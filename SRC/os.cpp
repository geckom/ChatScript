#include "common.h"

bool showDepth = false;
char serverLogfileName[200];				// file to log server to
char logFilename[MAX_WORD_SIZE];			// file to user log to
bool logUpdated = false;					// has logging happened
char* logmainbuffer = 0;					// where we build a log line
static bool pendingWarning = false;			// log entry we are building is a warning message
static bool pendingError = false;			// log entry we are building is an error message
struct tm* ptm;
int userLog = LOGGING_NOT_SET;				// do we log user
int serverLog = LOGGING_NOT_SET;			// do we log server
bool serverPreLog = true;					// show what server got BEFORE it works on it
bool serverctrlz = false;					// close communication with \0 and ctrlz
bool echo = false;							// show log output onto console as well
bool oob = false;							// show oob data
bool silent = false;						// dont display outputs of chat
bool logged = false;
bool showmem = false;
bool inLog = false;
char* testOutput = NULL;					// testing commands output reroute

// buffer information
#define MAX_BUFFER_COUNT 22
unsigned int maxBufferLimit = MAX_BUFFER_COUNT;		// default number of system buffers for AllocateBuffer
unsigned int maxBufferSize = MAX_BUFFER_SIZE;		// how big std system buffers from AllocateBuffer should be
unsigned int maxBufferUsed = 0;						// worst case buffer use - displayed with :variables
unsigned int bufferIndex = 0;				//   current allocated index into buffers[]  
unsigned baseBufferIndex = 0;				// preallocated buffers at start
char* buffers = 0;							//   collection of output buffers
#define MAX_OVERFLOW_BUFFERS 20
static char* overflowBuffers[MAX_OVERFLOW_BUFFERS];	// malloced extra buffers if base allotment is gone

unsigned char memDepth[512];				// memory usage at depth

static unsigned int overflowLimit = 0;
unsigned int overflowIndex = 0;


USERFILESYSTEM userFileSystem;
static char staticPath[MAX_WORD_SIZE]; // files that never change
static char readPath[MAX_WORD_SIZE];   // readonly files that might be overwritten from outside
static char writePath[MAX_WORD_SIZE];  // files written by app
unsigned int currentFileLine = 0;				// line number in file being read
char currentFilename[MAX_WORD_SIZE];	// name of file being read

// error recover 
jmp_buf scriptJump[5];
int jumpIndex = -1;

unsigned int randIndex = 0;
unsigned int oldRandIndex = 0;

#ifdef WIN32
#include <conio.h>
#include <direct.h>
#include <io.h>
#include <sys/types.h>
#include <sys/stat.h>

#endif

/////////////////////////////////////////////////////////
/// KEYBOARD
/////////////////////////////////////////////////////////

bool KeyReady()
{
	if (sourceFile) return true;
#ifdef WIN32
	return _kbhit() ? true : false;
#else
	bool ready = false;
	struct termios oldSettings, newSettings;
    if (tcgetattr( fileno( stdin ), &oldSettings ) == -1) return false; // could not get terminal attributes
    newSettings = oldSettings;
    newSettings.c_lflag &= (~ICANON & ~ECHO);
    tcsetattr( fileno( stdin ), TCSANOW, &newSettings );    
    fd_set set;
	struct timeval tv;
	tv.tv_sec = 0;
	tv.tv_usec = 0;
	FD_ZERO( &set );
    FD_SET( fileno( stdin ), &set );
    int res = select( fileno( stdin )+1, &set, NULL, NULL, &tv );
	ready = ( res > 0 );
    tcsetattr( fileno( stdin ), TCSANOW, &oldSettings );
	return ready;
#endif
}

/////////////////////////////////////////////////////////
/// EXCEPTION/ERROR
/////////////////////////////////////////////////////////

void JumpBack()
{
	if (jumpIndex < 0) return;	// not under handler control
	globalDepth = 0;
	longjmp(scriptJump[jumpIndex], 1);
}

void myexit(char* msg)
{	
	char name[MAX_WORD_SIZE];
	sprintf(name,"%s/exitlog.txt",logs);
	FILE* in = FopenUTF8WriteAppend(name);
	if (in) 
	{
		fprintf(in,"%s - called myexit\r\n",msg);
		fclose(in);
	}
	exit(0);
}

/////////////////////////////////////////////////////////
/// MEMORY SYSTEM
/////////////////////////////////////////////////////////

void ResetBuffers()
{
	globalDepth = 0;
	bufferIndex = baseBufferIndex;
	memset(memDepth,0,256); 
}

void CloseBuffers()
{
	while (overflowLimit > 0) 
	{
		free(overflowBuffers[--overflowLimit]);
		overflowBuffers[overflowLimit] = 0;
	}
	free(buffers);
	buffers = 0;
}

char* AllocateBuffer()
{// CANNOT USE LOG INSIDE HERE, AS LOG ALLOCATES A BUFFER
	char* buffer = buffers + (maxBufferSize * bufferIndex); 
	if (showmem) Log(STDUSERLOG,"BUff alloc %d\r\n",bufferIndex);
	if (++bufferIndex >= maxBufferLimit ) // want more than nominally allowed
	{
		if (bufferIndex > (maxBufferLimit+2) || overflowIndex > 20) 
		{
			char word[MAX_WORD_SIZE];
			sprintf(word,"Corrupt bufferIndex %d or overflowIndex %d\r\n",bufferIndex,overflowIndex);
			Log(STDUSERLOG,"%s\r\n",word);
			myexit(word);
		}
		--bufferIndex;

		// try to acquire more space, permanently
		if (overflowIndex >= overflowLimit) 
		{
			overflowBuffers[overflowLimit] = (char*) malloc(maxBufferSize);
			if (!overflowBuffers[overflowLimit]) 
			{
				Log(STDUSERLOG,"out of buffers\r\n");
				myexit("out of buffers");
			}
			overflowLimit++;
			if (overflowLimit >= MAX_OVERFLOW_BUFFERS) myexit("Out of overflow buffers\r\n");
			Log(STDUSERLOG,"Allocated extra buffer %d\r\n",overflowLimit);
		}
		buffer = overflowBuffers[overflowIndex++];
	}
	else if (bufferIndex > maxBufferUsed) maxBufferUsed = bufferIndex;
	*buffer++ = 0;	//   prior value
	*buffer = 0;	//   empty string
	return buffer;
}

char* AllocateAlignedBuffer()
{
	return AllocateBuffer() - 1;
}

void FreeBuffer()
{
	if (overflowIndex) --overflowIndex; // keep the dynamically allocated memory for now.
	else if (bufferIndex)  --bufferIndex; 
	else ReportBug("Buffer allocation underflow")
	if (showmem) Log(STDUSERLOG,"Buffer free %d\r\n",bufferIndex);
}

/////////////////////////////////////////////////////////
/// FILE SYSTEM
/////////////////////////////////////////////////////////

void InitUserFiles()
{ 
	// these are dynamically stored, so CS can be a DLL.
	userFileSystem.userCreate = FopenBinaryWrite;
	userFileSystem.userOpen = FopenReadWritten;
	userFileSystem.userClose = fclose;
	userFileSystem.userRead = fread;
	userFileSystem.userWrite = fwrite;
	userFileSystem.userSize = FileSize;
}

int MakeDirectory(char* directory)
{
	int result;

#ifdef WIN32
	char word[MAX_WORD_SIZE];
	char* path = _getcwd(word,MAX_WORD_SIZE);
	strcat(word,"/");
	strcat(word,directory);
    if( _access( path, 0 ) == 0 ){ // does directory exist, yes
        struct stat status;
        stat( path, &status );
        if ((status.st_mode & S_IFDIR) != 0) return -1;
    }
	result = _mkdir(directory);
#else 
	result = mkdir(directory, 0777); 
#endif
	return result;
}

void C_Directories(char* x)
{
	char word[MAX_WORD_SIZE];
	size_t len = MAX_WORD_SIZE;
	int bytes;
#ifdef WIN32
	bytes = GetModuleFileName(NULL, word, len);
#else
	char szTmp[32];
	sprintf(szTmp, "/proc/%d/exe", getpid());
	bytes = readlink(szTmp, word, len);
#endif
	if (bytes >= 0) 
	{
		word[bytes] = 0;
		Log(STDUSERLOG,"execution path: %s\r\n",word);
	}

#ifdef WIN32
    #include <direct.h>
    #define GetCurrentDir _getcwd
#else
    #include <unistd.h>
    #define GetCurrentDir getcwd
#endif
	if (GetCurrentDir(word, MAX_WORD_SIZE)) Log(STDUSERLOG,"current directory path: %s\r\n",word);

	Log(STDUSERLOG,"readPath: %s\r\n",readPath);
	Log(STDUSERLOG,"writeablePath: %s\r\n",writePath);
	Log(STDUSERLOG,"untouchedPath: %s\r\n",staticPath);
}

void InitFileSystem(char* untouchedPath,char* readablePath,char* writeablePath)
{
	if (readablePath) strcpy(readPath,readablePath);
	else *readPath = 0;
	if (writeablePath) strcpy(writePath,writeablePath);
	else *writePath = 0;
	if (untouchedPath) strcpy(staticPath,untouchedPath);
	else *staticPath = 0;

	InitUserFiles(); // default init all the io operations to file routines
}

void StartFile(const char* name)
{
	currentFileLine = 0;
	strcpy(currentFilename,name); // in case name is simple

	char* at = strrchr((char*) name,'/');	// last end of path
	if (at) strcpy(currentFilename,at+1);
	at = strrchr(currentFilename,'\\');		// windows last end of path
	if (at) strcpy(currentFilename,at+1);
}

FILE* FopenStaticReadOnly(const char* name) // static data file read path, never changed (DICT/LIVEDATA/src)
{
	StartFile(name);
	char path[MAX_WORD_SIZE];
	if (*readPath) sprintf(path,"%s/%s",staticPath,name);
	else strcpy(path,name);
	return fopen(path,"rb");
}

FILE* FopenReadOnly(const char* name) // read-only potentially changed data file read path (TOPIC)
{
	StartFile(name);
	char path[MAX_WORD_SIZE];
	if (*readPath) sprintf(path,"%s/%s",readPath,name);
	else strcpy(path,name);
	return fopen(path,"rb");
}

FILE* FopenReadNormal(char* name) // normal C read unrelated to special paths
{
	StartFile(name);
	return fopen(name,"rb");
}

size_t FileSize(FILE* in)
{
	fseek(in, 0, SEEK_END);
	unsigned int actualSize = (unsigned int) ftell(in);
	fseek(in, 0, SEEK_SET);
	return actualSize;
}

FILE* FopenBinaryWrite(const char* name) // writeable file path
{
	char path[MAX_WORD_SIZE];
	if (*writePath) sprintf(path,"%s/%s",writePath,name);
	else strcpy(path,name);
	FILE* out = fopen(path,"wb");
	if (out == NULL && !inLog) 
		ReportBug("Error opening binary write file %s: %s\n",path,strerror(errno));
	return out;
}

FILE* FopenReadWritten(const char* name) // read from files that have been written by us
{
	StartFile(name);
	char path[MAX_WORD_SIZE];
	if (*writePath) sprintf(path,"%s/%s",writePath,name);
	else strcpy(path,name);
	return fopen(path,"rb");
}

FILE* FopenUTF8Write(const char* filename) // insure file has BOM for UTF8
{
	char path[MAX_WORD_SIZE];
	if (*writePath) sprintf(path,"%s/%s",writePath,filename);
	else strcpy(path,filename);

	FILE* out = fopen(path,"wb");
	if (out) // mark file as UTF8 
	{
		unsigned char bom[3];
		bom[0] = 0xEF;
		bom[1] = 0xBB;
		bom[2] = 0xBF;
		fwrite(bom,1,3,out);
	}
	else ReportBug("Error opening utf8 write file %s: %s\n",path,strerror(errno));
	return out;
}

FILE* FopenUTF8WriteAppend(const char* filename,const char* flags) 
{
	char path[MAX_WORD_SIZE];
	if (*writePath) sprintf(path,"%s/%s",writePath,filename);
	else strcpy(path,filename);

	FILE* in = fopen(path,"rb"); // see if file already exists
	if (in) fclose(in);
	FILE* out = fopen(path,flags);
	if (out && !in) // mark file as UTF8 if new
	{
		unsigned char bom[3];
		bom[0] = 0xEF;
		bom[1] = 0xBB;
		bom[2] = 0xBF;
		fwrite(bom,1,3,out);
	}
	else if (!out && !inLog) 
		ReportBug("Error opening utf8writeappend file %s: %s\n",path,strerror(errno));
	return out;
}

#ifndef WIN32
int getdir (string dir, vector<string> &files)
{
    DIR *dp;
    struct dirent *dirp;
    if((dp  = opendir(dir.c_str())) == NULL) {
 		ReportBug("No such directory %s\n",strerror(errno));
		return errno;
    }
    while ((dirp = readdir(dp)) != NULL) files.push_back(string(dirp->d_name));
    closedir(dp);
    return 0;
}
#endif

void WalkDirectory(char* directory,FILEWALK function, uint64 flags) 
{
	char name[MAX_WORD_SIZE];
	char fulldir[MAX_WORD_SIZE];
	size_t len = strlen(directory);
	if (directory[len-1] == '/') directory[len-1] = 0;	// remove the / since we add it 
	if (*readPath) sprintf(fulldir,"%s/%s",staticPath,directory);
	else strcpy(fulldir,directory);

#ifdef WIN32 // do all files in src directory
	WIN32_FIND_DATA FindFileData;
	HANDLE hFind = INVALID_HANDLE_VALUE;
	DWORD dwError;
	LPSTR DirSpec;
	DirSpec = (LPSTR) malloc (MAX_PATH);
   
	  // Prepare string for use with FindFile functions.  First, 
	  // copy the string to a buffer, then append '\*' to the 
	  // directory name.
	strcpy(DirSpec,fulldir);
	strcat(DirSpec,"/*");
	// Find the first file in the directory.
	hFind = FindFirstFile(DirSpec, &FindFileData);

	if (hFind == INVALID_HANDLE_VALUE) 
	{
		ReportBug("No such directory %s: %s\n",DirSpec);
		return;
	} 
	else 
	{
		if (FindFileData.cFileName[0] != '.' && stricmp(FindFileData.cFileName,"bugs.txt"))
		{
			sprintf(name,"%s/%s",directory,FindFileData.cFileName);
			(*function)(name,flags);
		}
		while (FindNextFile(hFind, &FindFileData) != 0) 
		{
			if (FindFileData.cFileName[0] == '.' || !stricmp(FindFileData.cFileName,"bugs.txt")) continue;
			sprintf(name,"%s/%s",directory,FindFileData.cFileName);
			(*function)(name,flags);
		}
		dwError = GetLastError();
		FindClose(hFind);
		if (dwError != ERROR_NO_MORE_FILES) 
		{
			ReportBug("FindNextFile error. Error is %u.\n", dwError);
			return;
		}
	}
	free(DirSpec);
#else
    string dir = string(fulldir);
    vector<string> files = vector<string>();
    getdir(dir,files);
	for (unsigned int i = 0;i < files.size();i++) 
	{
		const char* file = files[i].c_str();
		if (*file != '.' && stricmp(file,"bugs.txt")) 
		{
			sprintf(name,"%s/%s",directory,file);
			(*function)(name,flags);
		}
     }
    return;
#endif
}

string GetUserPathString(const string &loginID)
{
    string userPath;
    if (loginID.length() == 0)  return userPath; // empty string
	size_t len = loginID.length();
	int counter = 0;
    for (size_t i = 0; i < len; i++) // use each character
	{
		if (loginID.c_str()[i] == '.' || loginID.c_str()[i] == '_') continue; // ignore IP . stuff
        userPath.append(1, loginID.c_str()[i]);
        userPath.append(1, '/');
		if (++counter >= 4) break;
    }
    return userPath;
}

#ifdef USERPATHPREFIX
static int MakePath(const string &rootDir, const string &path)
{
#ifndef WIN32
    struct stat st;
    if (stat((rootDir + "/" + path).c_str(), &st) == 0)  return 1;
#endif
    string pathToCreate(rootDir);
    size_t previous = 0;
    for (size_t next = path.find('/'); next != string::npos; previous = next + 1, next = path.find('/', next + 1)) 
	{
        pathToCreate.append("/");
        pathToCreate.append(path.substr(previous, next - previous));
#ifdef WIN32
        if (_mkdir(pathToCreate.c_str()) == -1 && errno != EEXIST) return 0;
#elif EVSERVER
  		if (mkdir(pathToCreate.c_str(), S_IRWXU | S_IRGRP | S_IXGRP | S_IROTH | S_IXOTH) == -1 && errno != EEXIST) return 0;
#else
  		if (mkdir(pathToCreate.c_str(), S_IRWXU | S_IRWXG) == -1 && errno != EEXIST) return 0;
#endif
    }
    return 1;
}
#endif

char* GetUserPath(char* login)
{
	static string userPath;
	char* path = "";
#ifdef USERPATHPREFIX
	if (server)
	{
#ifndef DISCARDDATABASE
		if (pguserdb) return path; // do not use this with postgres storage
#endif
		userPath = GetUserPathString(login);
		MakePath(users, userPath);
		path = (char*) userPath.c_str();
	}
#endif
	return path;
}

/////////////////////////////////////////////////////////
/// TIME FUNCTIONS
/////////////////////////////////////////////////////////

char* GetTimeInfo() //   Www Mmm dd hh:mm:ss yyyy Where Www is the weekday, Mmm the month in letters, dd the day of the month, hh:mm:ss the time, and yyyy the year. Sat May 20 15:21:51 2000
{
    time_t curr = time(0); // local machine time
    if (regression) curr = 44444444; 
	ptm = localtime (&curr);

	char* utcoffset = GetUserVariable("$cs_utcoffset");
	if (*utcoffset) // report relative time
	{
		ptm = gmtime (&curr); // UTC time reference structure

		// determine leap year status
		int year = ptm->tm_year + 1900;
		bool leap = false;
		if ((year / 400) == 0) leap = true;
		else if ((year / 100) != 0 && (year / 4) == 0) leap = true;

		// sign of offset
		int sign = 1;
		if (*utcoffset == '-') 
		{
			sign = -1;
			++utcoffset;
		}
		else if (*utcoffset == '+') ++utcoffset;

		// adjust hours, minutes, seconds
		int offset = atoi(utcoffset) * sign; // hours offset
		ptm->tm_hour += offset;
		char* colon = strchr(utcoffset,':'); // is there a minutes offset?
		if (colon)
		{
			offset = atoi(colon+1) * sign; // minutes offset
			ptm->tm_min += offset;
			colon = strchr(colon+1,':');
			if (colon) // seconds offset
			{
				offset = atoi(colon+1) * sign; // seconds offset
				ptm->tm_sec += offset;
			}
		}

		// correct for over and underflows
		if (ptm->tm_sec < 0) // sec underflow caused by timezone
		{ 
			ptm->tm_sec += 60;
			ptm->tm_min -= 1;
		}
		else if (ptm->tm_sec >= 60) // sec overflow caused by timezone
		{ 
			ptm->tm_sec -= 60;
			ptm->tm_min += 1;
		}

		if (ptm->tm_min < 0) // min underflow caused by timezone
		{ 
			ptm->tm_min += 60;
			ptm->tm_hour -= 1;
		}
		else if (ptm->tm_min >= 60) // min overflow caused by timezone
		{ 
			ptm->tm_min -= 60;
			ptm->tm_hour += 1;
		}

		if (ptm->tm_hour < 0) // hour underflow caused by timezone
		{ 
			ptm->tm_hour += 24;
			ptm->tm_yday -= 1;
			ptm->tm_mday -= 1;
			ptm->tm_wday -= 1;
		}
		else if (ptm->tm_hour >= 24) // hour overflow caused by timezone
		{ 
			ptm->tm_hour -= 24;
			ptm->tm_yday += 1;
			ptm->tm_mday += 1;
			ptm->tm_wday += 1;
		}
		
		if (ptm->tm_wday < 0) ptm->tm_wday += 7; // day of week underflow  0-6  
		else if (ptm->tm_wday >= 7) ptm->tm_wday -= 7; // day of week overflow  0-6  
		
		if (ptm->tm_yday < 0) ptm->tm_yday += 365; // day of year underflow  0-365  
		else if (ptm->tm_yday >= 365 && !leap ) ptm->tm_yday -= 365; // day of year overflow  0-365  
		else if (ptm->tm_yday >= 366) ptm->tm_yday -= 366; // day of year leap overflow  0-365  

		int daysInMonth = 30;
		if (ptm->tm_mday <= 0) // day of month underflow  1-31  
		{
			ptm->tm_mon -= 1;
			if (ptm->tm_mon == 1) // feb
			{
				if (leap) ptm->tm_mday = 29; 
				else ptm->tm_mday = 28; 
			}
			else if (ptm->tm_mon == 3) ptm->tm_mday = 30;  // apr
			else if (ptm->tm_mon == 5) ptm->tm_mday = 30;// june
			else if (ptm->tm_mon == 8) ptm->tm_mday = 30;// sept
			else if (ptm->tm_mon == 10) ptm->tm_mday = 30; // nov
			else ptm->tm_mday = 31;
		}
		else  // day of month overflow by 1?  1-31
		{
			if (ptm->tm_mon == 1 ) // feb
			{
				if (leap && ptm->tm_mday == 30) {ptm->tm_mon++; ptm->tm_mday = 1;}
				else if (ptm->tm_mday == 29) {ptm->tm_mon++; ptm->tm_mday = 1;}
			}
			else if (ptm->tm_mon == 3 && ptm->tm_mday == 31) {ptm->tm_mon++; ptm->tm_mday = 1;}  // apr
			else if (ptm->tm_mon == 5 && ptm->tm_mday == 31) {ptm->tm_mon++; ptm->tm_mday = 1;}// june
			else if (ptm->tm_mon == 8 && ptm->tm_mday == 31) {ptm->tm_mon++; ptm->tm_mday = 1;}// sept
			else if (ptm->tm_mon == 10 && ptm->tm_mday == 31) {ptm->tm_mon++; ptm->tm_mday = 1;} // nov
			else if (ptm->tm_mday == 32) {ptm->tm_mon++; ptm->tm_mday = 1;}
		}

		if (ptm->tm_mon < 0) // month underflow  0-11
		{ 
			ptm->tm_mon += 12; // back to december
			ptm->tm_year -= 1; // prior year
		}
		else if (ptm->tm_mon >= 12 ) // month overflow  0-11
		{ 
			ptm->tm_mon -= 12; //  january
			ptm->tm_year += 1; // on to next year
		}
	}
	char *mytime = asctime (ptm);
    mytime[strlen(mytime)-1] = 0; //   remove newline
    return mytime;
}

char* GetMyTime(time_t curr)
{
	char *mytime = ctime(&curr); //	Www Mmm dd hh:mm:ss yyyy
	static char when[40];
	strncpy(when,mytime+4,3); // mmm
	strncpy(when+3,mytime+8,2); // dd
	when[5] = '\'';
	strncpy(when+6,mytime+22,2); // yy
	when[8] = '-';
	strncpy(when+9,mytime+11,8); // hh:mm:ss
	when[17] = 0;
	return when;
}

#ifdef IOS
#elif __MACH__ 
void clock_get_mactime(struct timespec &ts)
{
	clock_serv_t cclock; 
	mach_timespec_t mts; 
	host_get_clock_service(mach_host_self(), CALENDAR_CLOCK, &cclock); 
	clock_get_time(cclock, &mts); 
	mach_port_deallocate(mach_task_self(), cclock); 
	ts.tv_sec = mts.tv_sec; 
	ts.tv_nsec = mts.tv_nsec; 
}
#endif

clock_t ElapsedMilliseconds()
{
	clock_t count;
#ifdef WIN32
	count = GetTickCount();
#elif IOS
	struct timeval x_time; 
	gettimeofday(&x_time, NULL); 
	count = x_time.tv_sec * 1000; 
	count += x_time.tv_usec / 1000; 
#elif __MACH__
	struct timespec abs_time; 
	clock_get_mactime( abs_time);
	count = abs_time.tv_sec * 1000; 
	count += abs_time.tv_nsec / 1000000; 
#else // LINUX
	struct timeval x_time;
	gettimeofday(&x_time, NULL);
	count = x_time.tv_sec * 1000; 
	count += x_time.tv_usec / 1000;
#endif
	return count;
}

#ifndef WIN32
unsigned int GetFutureSeconds(unsigned int seconds)
{
	struct timespec abs_time; 
#ifdef __MACH__
	clock_get_mactime(abs_time);
#else
	clock_gettime(CLOCK_REALTIME,&abs_time); 
#endif
	return abs_time.tv_sec + seconds; 
}
#endif

////////////////////////////////////////////////////////////////////////
/// RANDOM NUMBERS
////////////////////////////////////////////////////////////////////////



#define X64(n) (n##ULL)
uint64 X64_Table[256] = //   hash table randomizer
{
       X64(0x0000000000000000), X64(0x42f0e1eba9ea3693),       X64(0x85e1c3d753d46d26), X64(0xc711223cfa3e5bb5),
       X64(0x493366450e42ecdf), X64(0x0bc387aea7a8da4c),       X64(0xccd2a5925d9681f9), X64(0x8e224479f47cb76a),
       X64(0x9266cc8a1c85d9be), X64(0xd0962d61b56fef2d),       X64(0x17870f5d4f51b498), X64(0x5577eeb6e6bb820b),
       X64(0xdb55aacf12c73561), X64(0x99a54b24bb2d03f2),       X64(0x5eb4691841135847), X64(0x1c4488f3e8f96ed4),
       X64(0x663d78ff90e185ef), X64(0x24cd9914390bb37c),       X64(0xe3dcbb28c335e8c9), X64(0xa12c5ac36adfde5a),
       X64(0x2f0e1eba9ea36930), X64(0x6dfeff5137495fa3),       X64(0xaaefdd6dcd770416), X64(0xe81f3c86649d3285),
       X64(0xf45bb4758c645c51), X64(0xb6ab559e258e6ac2),       X64(0x71ba77a2dfb03177), X64(0x334a9649765a07e4),
       X64(0xbd68d2308226b08e), X64(0xff9833db2bcc861d),       X64(0x388911e7d1f2dda8), X64(0x7a79f00c7818eb3b),
       X64(0xcc7af1ff21c30bde), X64(0x8e8a101488293d4d),       X64(0x499b3228721766f8), X64(0x0b6bd3c3dbfd506b),
       X64(0x854997ba2f81e701), X64(0xc7b97651866bd192),       X64(0x00a8546d7c558a27), X64(0x4258b586d5bfbcb4),
       X64(0x5e1c3d753d46d260), X64(0x1cecdc9e94ace4f3),       X64(0xdbfdfea26e92bf46), X64(0x990d1f49c77889d5),
       X64(0x172f5b3033043ebf), X64(0x55dfbadb9aee082c),       X64(0x92ce98e760d05399), X64(0xd03e790cc93a650a),
       X64(0xaa478900b1228e31), X64(0xe8b768eb18c8b8a2),       X64(0x2fa64ad7e2f6e317), X64(0x6d56ab3c4b1cd584),
       X64(0xe374ef45bf6062ee), X64(0xa1840eae168a547d),       X64(0x66952c92ecb40fc8), X64(0x2465cd79455e395b),
       X64(0x3821458aada7578f), X64(0x7ad1a461044d611c),       X64(0xbdc0865dfe733aa9), X64(0xff3067b657990c3a),
       X64(0x711223cfa3e5bb50), X64(0x33e2c2240a0f8dc3),       X64(0xf4f3e018f031d676), X64(0xb60301f359dbe0e5),
       X64(0xda050215ea6c212f), X64(0x98f5e3fe438617bc),       X64(0x5fe4c1c2b9b84c09), X64(0x1d14202910527a9a),
       X64(0x93366450e42ecdf0), X64(0xd1c685bb4dc4fb63),       X64(0x16d7a787b7faa0d6), X64(0x5427466c1e109645),
       X64(0x4863ce9ff6e9f891), X64(0x0a932f745f03ce02),       X64(0xcd820d48a53d95b7), X64(0x8f72eca30cd7a324),
       X64(0x0150a8daf8ab144e), X64(0x43a04931514122dd),       X64(0x84b16b0dab7f7968), X64(0xc6418ae602954ffb),
       X64(0xbc387aea7a8da4c0), X64(0xfec89b01d3679253),       X64(0x39d9b93d2959c9e6), X64(0x7b2958d680b3ff75),
       X64(0xf50b1caf74cf481f), X64(0xb7fbfd44dd257e8c),       X64(0x70eadf78271b2539), X64(0x321a3e938ef113aa),
       X64(0x2e5eb66066087d7e), X64(0x6cae578bcfe24bed),       X64(0xabbf75b735dc1058), X64(0xe94f945c9c3626cb),
       X64(0x676dd025684a91a1), X64(0x259d31cec1a0a732),       X64(0xe28c13f23b9efc87), X64(0xa07cf2199274ca14),
       X64(0x167ff3eacbaf2af1), X64(0x548f120162451c62),       X64(0x939e303d987b47d7), X64(0xd16ed1d631917144),
       X64(0x5f4c95afc5edc62e), X64(0x1dbc74446c07f0bd),       X64(0xdaad56789639ab08), X64(0x985db7933fd39d9b),
       X64(0x84193f60d72af34f), X64(0xc6e9de8b7ec0c5dc),       X64(0x01f8fcb784fe9e69), X64(0x43081d5c2d14a8fa),
       X64(0xcd2a5925d9681f90), X64(0x8fdab8ce70822903),       X64(0x48cb9af28abc72b6), X64(0x0a3b7b1923564425),
       X64(0x70428b155b4eaf1e), X64(0x32b26afef2a4998d),       X64(0xf5a348c2089ac238), X64(0xb753a929a170f4ab),
       X64(0x3971ed50550c43c1), X64(0x7b810cbbfce67552),       X64(0xbc902e8706d82ee7), X64(0xfe60cf6caf321874),
       X64(0xe224479f47cb76a0), X64(0xa0d4a674ee214033),       X64(0x67c58448141f1b86), X64(0x253565a3bdf52d15),
       X64(0xab1721da49899a7f), X64(0xe9e7c031e063acec),       X64(0x2ef6e20d1a5df759), X64(0x6c0603e6b3b7c1ca),
       X64(0xf6fae5c07d3274cd), X64(0xb40a042bd4d8425e),       X64(0x731b26172ee619eb), X64(0x31ebc7fc870c2f78),
       X64(0xbfc9838573709812), X64(0xfd39626eda9aae81),       X64(0x3a28405220a4f534), X64(0x78d8a1b9894ec3a7),
       X64(0x649c294a61b7ad73), X64(0x266cc8a1c85d9be0),       X64(0xe17dea9d3263c055), X64(0xa38d0b769b89f6c6),
       X64(0x2daf4f0f6ff541ac), X64(0x6f5faee4c61f773f),       X64(0xa84e8cd83c212c8a), X64(0xeabe6d3395cb1a19),
       X64(0x90c79d3fedd3f122), X64(0xd2377cd44439c7b1),       X64(0x15265ee8be079c04), X64(0x57d6bf0317edaa97),
	   X64(0xd9f4fb7ae3911dfd), X64(0x9b041a914a7b2b6e),       X64(0x5c1538adb04570db), X64(0x1ee5d94619af4648),
       X64(0x02a151b5f156289c), X64(0x4051b05e58bc1e0f),       X64(0x87409262a28245ba), X64(0xc5b073890b687329),
       X64(0x4b9237f0ff14c443), X64(0x0962d61b56fef2d0),       X64(0xce73f427acc0a965), X64(0x8c8315cc052a9ff6),
       X64(0x3a80143f5cf17f13), X64(0x7870f5d4f51b4980),       X64(0xbf61d7e80f251235), X64(0xfd913603a6cf24a6),
       X64(0x73b3727a52b393cc), X64(0x31439391fb59a55f),       X64(0xf652b1ad0167feea), X64(0xb4a25046a88dc879),
       X64(0xa8e6d8b54074a6ad), X64(0xea16395ee99e903e),       X64(0x2d071b6213a0cb8b), X64(0x6ff7fa89ba4afd18),
       X64(0xe1d5bef04e364a72), X64(0xa3255f1be7dc7ce1),       X64(0x64347d271de22754), X64(0x26c49cccb40811c7),
       X64(0x5cbd6cc0cc10fafc), X64(0x1e4d8d2b65facc6f),       X64(0xd95caf179fc497da), X64(0x9bac4efc362ea149),
       X64(0x158e0a85c2521623), X64(0x577eeb6e6bb820b0),       X64(0x906fc95291867b05), X64(0xd29f28b9386c4d96),
       X64(0xcedba04ad0952342), X64(0x8c2b41a1797f15d1),       X64(0x4b3a639d83414e64), X64(0x09ca82762aab78f7),
       X64(0x87e8c60fded7cf9d), X64(0xc51827e4773df90e),       X64(0x020905d88d03a2bb), X64(0x40f9e43324e99428),
       X64(0x2cffe7d5975e55e2), X64(0x6e0f063e3eb46371),       X64(0xa91e2402c48a38c4), X64(0xebeec5e96d600e57),
       X64(0x65cc8190991cb93d), X64(0x273c607b30f68fae),       X64(0xe02d4247cac8d41b), X64(0xa2dda3ac6322e288),
       X64(0xbe992b5f8bdb8c5c), X64(0xfc69cab42231bacf),       X64(0x3b78e888d80fe17a), X64(0x7988096371e5d7e9),
       X64(0xf7aa4d1a85996083), X64(0xb55aacf12c735610),       X64(0x724b8ecdd64d0da5), X64(0x30bb6f267fa73b36),
       X64(0x4ac29f2a07bfd00d), X64(0x08327ec1ae55e69e),       X64(0xcf235cfd546bbd2b), X64(0x8dd3bd16fd818bb8),
       X64(0x03f1f96f09fd3cd2), X64(0x41011884a0170a41),       X64(0x86103ab85a2951f4), X64(0xc4e0db53f3c36767),
       X64(0xd8a453a01b3a09b3), X64(0x9a54b24bb2d03f20),       X64(0x5d45907748ee6495), X64(0x1fb5719ce1045206),
       X64(0x919735e51578e56c), X64(0xd367d40ebc92d3ff),       X64(0x1476f63246ac884a), X64(0x568617d9ef46bed9),
       X64(0xe085162ab69d5e3c), X64(0xa275f7c11f7768af),       X64(0x6564d5fde549331a), X64(0x279434164ca30589),
       X64(0xa9b6706fb8dfb2e3), X64(0xeb46918411358470),       X64(0x2c57b3b8eb0bdfc5), X64(0x6ea7525342e1e956),
       X64(0x72e3daa0aa188782), X64(0x30133b4b03f2b111),       X64(0xf7021977f9cceaa4), X64(0xb5f2f89c5026dc37),
       X64(0x3bd0bce5a45a6b5d), X64(0x79205d0e0db05dce),       X64(0xbe317f32f78e067b), X64(0xfcc19ed95e6430e8),
       X64(0x86b86ed5267cdbd3), X64(0xc4488f3e8f96ed40),       X64(0x0359ad0275a8b6f5), X64(0x41a94ce9dc428066),
       X64(0xcf8b0890283e370c), X64(0x8d7be97b81d4019f),       X64(0x4a6acb477bea5a2a), X64(0x089a2aacd2006cb9),
       X64(0x14dea25f3af9026d), X64(0x562e43b4931334fe),       X64(0x913f6188692d6f4b), X64(0xd3cf8063c0c759d8),
       X64(0x5dedc41a34bbeeb2), X64(0x1f1d25f19d51d821),       X64(0xd80c07cd676f8394), X64(0x9afce626ce85b507)
};

uint64 Hashit(unsigned char * data, int len,bool & hasUpperCharacters, bool & hasUTF8Characters)
{
	hasUpperCharacters = hasUTF8Characters = false;
	uint64 crc = 0;
	while (len-- > 0)
	{ 
		unsigned char c = *data++;
		if (!c) break;
		if (c & 0x80) hasUTF8Characters = true;
		else if (IsUpperCase(c)) 
		{
			c = GetLowercaseData(c);
			hasUpperCharacters = true;
		}
		crc = X64_Table[(crc >> 56) ^ c ] ^ (crc << 8 );
	}
	return crc;
} 

unsigned int random(unsigned int range)
{
	if (regression || range <= 1) return 0;
	unsigned int x = (unsigned int)X64_Table[randIndex++ % MAXRAND];
	return x % range;
}

/////////////////////////////////////////////////////////
/// LOGGING
/////////////////////////////////////////////////////////
uint64 logCount = 0;

void ChangeDepth(int value,char* where)
{
	if (value < 0)
	{
		if (memDepth[globalDepth] != bufferIndex)
		{
			ReportBug("depth %d not closing bufferindex correctly at %s\r\n",globalDepth,where);
			memDepth[globalDepth] = 0;
		}
		globalDepth += value;
		if (showDepth) Log(STDUSERLOG,"-depth after %s %d\r\n", where, globalDepth);
	}
	if (value > 0) 
	{
		if (showDepth) Log(STDUSERLOG,"+depth before %s %d\r\n", where, globalDepth);
		globalDepth += value;
		memDepth[globalDepth] = (unsigned char) bufferIndex;
	}
	if (globalDepth < 0) {ReportBug("bad global depth in %s",where); globalDepth = 0;}
	if (globalDepth >= 511)
	{
		ReportBug("globaldepth too deep at %s\r\n",where);
		myexit("global depth failure\r\n");
	}
}

unsigned int Log(unsigned int channel,const char * fmt, ...)
{
	static unsigned int id = 1000;
	if (quitting) return id;
	logged = true;
	bool localecho = false;
	if (channel == ECHOSTDUSERLOG)
	{
		localecho = true;
		channel = STDUSERLOG;
	}
	if (!userLog && (channel == STDUSERLOG || channel > 1000 || channel == id) && !testOutput) return id;
    if (!fmt || !logmainbuffer)  return id; // no format or no buffer to use
	if ((channel == BUGLOG || channel == SERVERLOG) && server && !serverLog)  return id; // not logging server data

	static char last = 0;
	static int priordepth = 0;
    char* at = logmainbuffer;
    *at = 0;
    va_list ap; 
    va_start(ap,fmt);
	++logCount;

    char* s;
    int i;
    const char *ptr = fmt - 1;

	//   when this channel matches the ID of the prior output of log,
	//   we dont force new line on it.
	if (channel == id) //   join result code onto intial description
	{
		channel = 1;
		strcpy(at,"    ");
		at += 4;
	}
	//   any channel above 1000 is same as 101
	else if (channel > 1000) channel = STDUSERTABLOG; //   force result code to indent new line

	//   channels above 100 will indent when prior line not ended
	if (channel >= STDUSERTABLOG && last != '\\') //   indented by call level and not merged
	{ //   STDUSERTABLOG 101 is std indending characters  201 = attention getting
		if (last == 1 && globalDepth == priordepth) {} // we indented already
		else if (last == 1 && globalDepth > priordepth) // we need to indent a bit more
		{
			for (int i = priordepth+1; i < globalDepth; i++)
			{
				*at++ = (i == 4 || i == 9) ? ',' : '.';
				*at++ = ' ';
			}
			priordepth = globalDepth;
		}
		else 
		{
			if (last != '\n') 
			{
				*at++ = '\r'; //   close out this prior thing
				*at++ = '\n';
			}
			while (ptr[1] == '\n' || ptr[1] == '\r') // we point BEFORE the format
			{
				*at++ = *++ptr;
			}

			int n = globalDepth;
			if (n < 0) n = 0; //   just in case
			for (int i = 0; i < n; i++)
			{
				if (channel == STDUSERATTNLOG) *at++ = (i == 1) ? '*' : ' ';
				else *at++ = (i == 4 || i == 9) ? ',' : '.';
				*at++ = ' ';
			}
			priordepth = globalDepth;
		}
 	}
	channel %= 100;
    while (*++ptr)
    {
        if (*ptr == '%')
        {
			++ptr;
            if (*ptr== 'c') sprintf(at,"%c",(char) va_arg(ap,int)); // char
            else if (*ptr== 'd') sprintf(at,"%d",va_arg(ap,int)); // int %d
            else if (*ptr== 'I') //   I64
            {
#ifdef WIN32
				sprintf(at,"%I64d",va_arg(ap,uint64));
#else
				sprintf(at,"%lld",va_arg(ap,uint64)); 
#endif
				ptr += 2; 
            }
            else if (*ptr== 'l' && ptr[1] == 'd') // ld
            {
                sprintf(at,"%ld",va_arg(ap,long int));
				++ptr; 
            }
            else if (*ptr== 'l' && ptr[1] == 'l') // lld
            {
#ifdef WIN32
				sprintf(at,"%I64d",va_arg(ap,long long int)); 
#else
				sprintf(at,"%lld",va_arg(ap,long long int)); 
#endif
				ptr += 2;
            }
            else if (*ptr == 'p') sprintf(at,"%p",va_arg(ap,char*)); // ptr
            else if (*ptr == 'f') 
			{
				float f = (float)va_arg(ap,double);
				sprintf(at,"%f",f); // float
			}
            else if (*ptr == 's') // string
            {
                s = va_arg(ap,char*);
				if (s) sprintf(at,"%s",s);
            }
            else if (*ptr == 'x') sprintf(at,"%x",(unsigned int)va_arg(ap,unsigned int)); // hex 
 			else if (IsDigit(*ptr)) // int %2d
            {
				i = va_arg(ap,int);
				unsigned int precision = atoi(ptr);
				while (*ptr && *ptr != 'd') ++ptr;
				if (precision == 2) sprintf(at,"%2d",i);
				else if (precision == 3) sprintf(at,"%3d",i);
				else if (precision == 4) sprintf(at,"%4d",i);
				else if (precision == 5) sprintf(at,"%5d",i);
				else if (precision == 6) sprintf(at,"%6d",i);
				else sprintf(at," Bad int precision %d ",precision);
            }
            else
            {
                sprintf(at,"unknown format ");
				ptr = 0;
            }
        }
        else  sprintf(at,"%c",*ptr);

        at += strlen(at);
		if (!ptr) break;
    }
    *at = 0;
    va_end(ap); 

	last = *(at-1); //   ends on NL?
	if (fmt && !*fmt) last = 1; // special marker 
	if (last == '\\') *--at = 0;	//   dont show it (we intend to merge lines)
	logUpdated = true; // in case someone wants to see if intervening output happened
	size_t bufLen = at - logmainbuffer;
 	logmainbuffer[bufLen] = 0;
	inLog = true;
	bool bugLog = false;
		
	if (pendingWarning)
	{
		AddWarning(logmainbuffer);
		pendingWarning = false;
	}
	else if (!strnicmp(logmainbuffer,"*** Warning",11)) 
		pendingWarning = true;// replicate for easy dump later
	
	if (pendingError)
	{
		AddError(logmainbuffer);
		pendingError= false;
	}
	else if (!strnicmp(logmainbuffer,"*** Error",9)) 
		pendingError = true;// replicate for easy dump later

#ifndef DISCARDSERVER
#ifndef EVSERVER
    if (server) GetLogLock();
#endif
#endif	

	if (channel == BADSCRIPTLOG || channel == BUGLOG) 
	{
		bugLog = true;
		char name[MAX_WORD_SIZE];
		sprintf(name,"%s/bugs.txt",logs);
		FILE* bug = FopenUTF8WriteAppend(name);
		char located[MAX_WORD_SIZE];
		*located = 0;
		if (currentTopicID && currentRule) sprintf(located,"%s.%d.%d",GetTopicName(currentTopicID),TOPLEVELID(currentRuleID),REJOINDERID(currentRuleID));
		if (bug) //   write to a bugs file
		{
			if (*currentFilename) fprintf(bug,"   in %s at %d: %s\r\n",currentFilename,currentFileLine,readBuffer);
			if (channel == BUGLOG && *currentInput) fprintf(bug,"input:%d %s %s caller:%s callee:%s in sentence: %s at %s\r\n",volleyCount,GetTimeInfo(),logmainbuffer,loginID,computerID,currentInput,located);
			fwrite(logmainbuffer,1,bufLen,bug);
			fclose(bug);

		}
		if ((echo||localecho) && !silent && !server)
		{
			if (*currentFilename) fprintf(stdout,"\r\n   in %s at %d: %s\r\n    ",currentFilename,currentFileLine,readBuffer);
			else if (*currentInput) fprintf(stdout,"\r\n%d %s in sentence: %s \r\n    ",volleyCount,GetTimeInfo(),currentInput);
		}
		strcat(logmainbuffer,"\r\n");	//   end it
		channel = STDUSERLOG;	//   use normal logging as well
	}

	if (server){} // dont echo  onto server console 
    else if (((echo||localecho) && channel == STDUSERLOG) || channel == STDDEBUGLOG  ) fwrite(logmainbuffer,1,bufLen,stdout);
	bool doserver = true;

    FILE* out = NULL;
	
	if (server && trace && !userLog) channel = SERVERLOG;	// force traced server to go to server log since no user log

#ifndef DISCARDDATABASE 
	if (pguserdb)
	{
		doserver = false;
		pguserLog(logmainbuffer,bufLen);
	}
	else
#endif
    if (logFilename[0] != 0 && channel != SERVERLOG)  
	{
		out =  FopenUTF8WriteAppend(logFilename); 
 		if (!out) // see if we can create the directory (assuming its missing)
		{
			char call[MAX_WORD_SIZE];
			sprintf(call,"mkdir %s",users);
			system(call);
			out = userFileSystem.userCreate(logFilename);
			if (!out && !inLog) ReportBug("unable to create user logfile %s",logFilename);
		}
	}
    else 
	{
		out = FopenUTF8WriteAppend(serverLogfileName); 
 		if (!out) // see if we can create the directory (assuming its missing)
		{
			char call[MAX_WORD_SIZE];
			sprintf(call,"mkdir %s",logs);
			system(call);
			out = userFileSystem.userCreate(serverLogfileName);
		}
	}

    if (out) 
    {
		if (doserver)
		{
			fwrite(logmainbuffer,1,bufLen,out);
			if (!bugLog);
 			else if (*currentFilename) fprintf(out,"   in %s at %d: %s\r\n    ",currentFilename,currentFileLine,readBuffer);
			else if (*currentInput) fprintf(out,"%d %s in sentence: %s \r\n    ",volleyCount,GetTimeInfo(),currentInput);
		}
		fclose(out);
		if (channel == SERVERLOG && echoServer)  printf("%s",logmainbuffer);
    }
	
#ifndef DISCARDSERVER
	if (testOutput && server) // command outputs
	{
		size_t len = strlen(testOutput);
		if ((len + bufLen) < (maxBufferSize - 10)) strcat(testOutput,logmainbuffer);
	}

#ifndef EVSERVER
    if (server) ReleaseLogLock();
#endif
#endif
	inLog = false;
	return ++id;
}

void Bug()
{
	int i = 0; // just a place to debug catch errors
	i = i - 1;
}
