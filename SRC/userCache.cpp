#include "common.h"

#define DEFAULT_USER_CACHE 50000
#define NO_CACHEID -1

static unsigned int cacheHead = 0;		// our marker for last allocated cache, used to find next free one
static unsigned int* cacheIndex = 0;	// data ring of the caches + timestamp/volley info
char* cacheBase = 0;					// start of contiguous cache block of caches
static int currentCache = NO_CACHEID;	// the current user file buffer
unsigned int userCacheCount = 1;		// holds 1 user by default
unsigned int userCacheSize = DEFAULT_USER_CACHE;
int volleyLimit =  -1;					// default save user records to file every n volley (use default 0 if this value is unchanged by user)
char* userDataBase = NULL;				// current write user record base
static char* overflowBuffer = NULL;		// if record is bigger than cache block size, here is emergency block
static unsigned int safespace = 0;		// size of emergency block allocated last

void OverflowRelease() // from either a read or a write
{
	if (overflowBuffer)
	{
		free(overflowBuffer);
		overflowBuffer = NULL;
		FreeUserCache();  // associated useless buffer released
	}
}
		
char* OverflowProtect(char* ptr)
{
	if (!overflowBuffer && (unsigned int) (ptr - userDataBase) >= (userCacheSize - OVERFLOW_SAFETY_MARGIN)) 
	{
		ReportBug("User File %s too big for buffer (actual:%ld  limit:%ld safety:%d)\r\n",userDataBase,(long int)(ptr-userDataBase),(long int)userCacheSize,OVERFLOW_SAFETY_MARGIN) // too big
		printf("User File %s too big for buffer (actual:%ld  limit:%ld safety:%d)\r\n",userDataBase,(long int)(ptr-userDataBase),(long int)userCacheSize,OVERFLOW_SAFETY_MARGIN); // too big
		safespace = userCacheSize * 2;
		if (safespace < 200000) safespace = 200000;
		if (trace & TRACE_USERCACHE) Log((server) ? SERVERLOG : STDUSERLOG,"Allocating overflow write for %s\r\n",userDataBase);
		overflowBuffer = (char*) malloc(safespace);
		if (!overflowBuffer) return NULL;	// cannot protect
		memmove(overflowBuffer,userDataBase,(ptr-userDataBase));
		ptr = overflowBuffer + (ptr-userDataBase);
		userDataBase = overflowBuffer; 
	}
	else if (overflowBuffer && (unsigned int) (ptr - userDataBase) >= (safespace  - OVERFLOW_SAFETY_MARGIN )) 
	{
		ReportBug("User File %s way too big for buffer (actual:%ld  limit:%ld safety:%d)\r\n",userDataBase,(long int)(ptr-userDataBase),(long int)safespace,OVERFLOW_SAFETY_MARGIN) // too big
		printf("User File %s way too big for buffer (actual:%ld  limit:%ld safety:%d)\r\n",userDataBase,(long int)(ptr-userDataBase),(long int)safespace,OVERFLOW_SAFETY_MARGIN); // too big
		return NULL; // just cannot write it
	}
	return ptr;
}

void InitCache(unsigned int dictStringSize)
{
	cacheBase = (char*) malloc(dictStringSize + userTopicStoreSize + userTableSize );
	if (!cacheBase)
	{
		printf("Out of  memory space for dictionary w user cache %d %d %d %d\r\n",dictStringSize,userTopicStoreSize,userTableSize,MAX_ENTRIES);
		ReportBug("Cannot allocate memory space for dictionary %ld\r\n",(long int)(dictStringSize + userTopicStoreSize))
		myexit("out of memory space for dictionary to allocate");
	}
	cacheIndex = (unsigned int*) (cacheBase + userTopicStoreSize); // linked list for caches - each entry is [3] wide 0=prior 1=next 2=TIMESTAMP
	char* ptr = cacheBase;
	for (unsigned int i = 0; i < userCacheCount; ++i) 
	{
		*ptr = 0; // item is empty
		cacheIndex[PRIOR(i)] = i - 1; // before ptr
		cacheIndex[NEXT(i)] = i + 1; // after ptr
		ptr += userCacheSize;
	}
	cacheIndex[PRIOR(0)] = userCacheCount-1; // last one as prior
	cacheIndex[NEXT(userCacheCount-1)] = 0;	// start as next one (circular list)
}

void CloseCache()
{
	free(cacheBase);
	cacheBase = NULL;
}

static void WriteCache(unsigned int which,size_t size)
{
	char* ptr = (overflowBuffer) ? overflowBuffer : GetCacheBuffer(which);
	if (!*ptr) return;	// nothing to write out

	unsigned int volleys = VOLLEYCOUNT(which);
	if (!volleys) return; // unchanged from prior write out

	if (size == 0) // request to compute size
	{
		size = strlen(ptr) + 1; // login string
		size += strlen(ptr+size);
	}
	FILE* out = userFileSystem.userCreate(ptr); // wb binary file (if external as db write should not fail)
	if (!out) // see if we can create the directory (assuming its missing)
	{
		char call[MAX_WORD_SIZE];
		sprintf(call,"mkdir %s",users);
		system(call);
		out = userFileSystem.userCreate(ptr);

		if (!out) 
		{
			ReportBug("cannot open user state file %s to write\r\n",ptr)
			return;
		}
	}

#ifdef LOCKUSERFILE
#ifdef LINUX
	if (server && userFileSystem.userCreate == FopenBinaryWrite)
	{
        int fd = fileno(out);
        if (fd < 0) 
		{
			fclose(out);
			return;
        }

        struct flock fl;
        fl.l_type   = F_WRLCK;  /* F_RDLCK, F_WRLCK, F_UNLCK	*/
        fl.l_whence = SEEK_SET; /* SEEK_SET, SEEK_CUR, SEEK_END */
        fl.l_start  = 0;	/* Offset from l_whence         */
        fl.l_len    = 0;	/* length, 0 = to EOF           */
        fl.l_pid    = getpid(); /* our PID                      */
        if (fcntl(fd, F_SETLKW, &fl) < 0) 
		{
             userFileSystem.userClose(out);
             return;
        }
	}
#endif
#endif

	userFileSystem.userWrite(ptr,1,size,out);
	userFileSystem.userClose(out);
	if (trace & TRACE_USERCACHE) Log((server) ? SERVERLOG : STDUSERLOG,"write out %s cache (%d)\r\n",ptr,which);

	cacheIndex[TIMESTAMP(which)] &= 0x00ffffff;	// clear volley count since last written but keep time info
	if ( overflowBuffer) OverflowRelease();
}

void FlushCache() // writes out the cache but does not invalidate it
{
	if (!userCacheCount) return;
	unsigned int start = cacheHead;
	while (ALWAYS) 
	{
		WriteCache(start,0);
		start = cacheIndex[NEXT(start)];
		if (start == cacheHead) break;	// end of loop when all are in use
	}
}

static char* GetFreeCache() // allocate backwards from current, so in use is always NEXT from current
{
	if (!userCacheCount) return NULL;
	unsigned int duration = (clock() / 	CLOCKS_PER_SEC) - startSystem; // how many seconds since start of program launch
	// need to find a cache that's free else flush oldest one
	unsigned int last = cacheIndex[PRIOR(cacheHead)];	// PRIOR ptr of list start
	char* ptr = GetCacheBuffer(last);
	if (*ptr) // this is in use
	{
		WriteCache(last,0);  
		*ptr = 0; // clear cache so it can be reused
	}
	cacheIndex[TIMESTAMP(last)] = duration; // includes 0 volley count and when this was allocated
	currentCache = cacheHead = last; // just rotate the ring - has more than one block
	return ptr;
}

void FreeUserCache()
{
	if (currentCache != NO_CACHEID ) // this is the current cache, disuse it
	{
		*GetCacheBuffer(currentCache) = 0;
		cacheHead = cacheIndex[NEXT(currentCache)];
		currentCache = NO_CACHEID;
	}
}

void FreeAllUserCaches()
{
	FlushCache();
	unsigned int start = cacheHead;
	while (userCacheCount) // kill all active caches
	{
		*GetCacheBuffer(start) = 0;
		start = cacheIndex[NEXT(start)];
		if (start == cacheHead) break;	// end of loop
	}
	currentCache = NO_CACHEID;
}

char* FindUserCache(char* word)
{
	// already in cache?
	unsigned int start = cacheHead;
	while (userCacheCount)
	{
		char* ptr = GetCacheBuffer(start);
		if (!stricmp(ptr,word)) // this is the user
		{
			if (start != cacheHead) // make him FIRST on the list
			{
				unsigned int prior = cacheIndex[PRIOR(start)];
				unsigned int next = cacheIndex[NEXT(start)];
				// decouple from where it is
				cacheIndex[NEXT(prior)] = next;
				cacheIndex[PRIOR(next)] = prior;

				// now insert in front
				prior = cacheIndex[PRIOR(cacheHead)];
				cacheIndex[PRIOR(cacheHead)] = start;

				cacheIndex[NEXT(prior)] = start;
				cacheIndex[PRIOR(start)] = prior;
				cacheIndex[NEXT(start)] = cacheHead;
			}
			currentCache = cacheHead = start;
			return ptr;
		}
		start = cacheIndex[NEXT(start)];
		if (start == cacheHead) break;	// end of loop
	}
	return NULL;
}


char* GetFileRead(char* user,char* computer)
{
	char word[MAX_WORD_SIZE];
	sprintf(word,"%s/%stopic_%s_%s.txt",users,GetUserPath(loginID),user,computer);
	char* buffer = FindUserCache(word); // sets currentCache and makes it first if non-zero return -  will either find but not assign if not found
	if (buffer) return buffer;

	// have to go read it
	buffer = GetFreeCache(); // get cache buffer 
    FILE* in = (!buffer) ? NULL : userFileSystem.userOpen(word); // user topic file

#ifdef LOCKUSERFILE
#ifdef LINUX
	if (server && in && userFileSystem.userOpen == FopenReadWritten)
	{
		int fd = fileno(in);
		if (fd < 0) 
		{
		    userFileSystem.userClose(in);
			in = 0;
		}
		else
		{
			struct flock fl;
			fl.l_type   = F_RDLCK;  /* F_RDLCK, F_WRLCK, F_UNLCK	*/
			fl.l_whence = SEEK_SET; /* SEEK_SET, SEEK_CUR, SEEK_END */
			fl.l_start  = 0;	/* Offset from l_whence		*/
			fl.l_len    = 0;	/* length, 0 = to EOF		*/
			fl.l_pid    = getpid(); /* our PID			*/
			if (fcntl(fd, F_SETLKW, &fl) < 0) 
			{
				userFileSystem.userClose(in);
				in = 0;
			}
		}
	}
#endif
#endif

	if (in) // read in data if file exists
	{
		unsigned int actualSize = userFileSystem.userSize(in);
		if ((int)actualSize != -1) 
		{
			if (actualSize >= userCacheSize) // emergency read issue
			{
				if (actualSize < safespace) {;} // prior write use is fine, avoid memory fragmentation
				else if (actualSize < 200000) safespace = 2000000;
				else 
				{
					ReportBug("Overflow read buffer unexpectedly huge\r\n");
					userFileSystem.userClose(in);
					return NULL;
				}
				if (trace & TRACE_USERCACHE) Log((server) ? SERVERLOG : STDUSERLOG,"Allocating overflow read for %s\r\n",word);
				overflowBuffer = buffer = (char*) malloc(safespace);
				if (!overflowBuffer) // couldnt malloc
				{
					ReportBug("Could not allocate overflow read buffer\r\n");
					userFileSystem.userClose(in);
					return NULL;
				}
			}


			size_t readit = userFileSystem.userRead(buffer,1,actualSize,in);	// read it all in, including BOM
			buffer[readit] = 0;
			if (readit != actualSize) *buffer = 0; // read failure
		}
		userFileSystem.userClose(in);
		if (trace & TRACE_USERCACHE) Log((server) ? SERVERLOG : STDUSERLOG,"read in %s cache (%d)\r\n",word,currentCache);
	}
	return buffer;
}

char* GetCacheBuffer(int which)
{
	return (which < 0) ? GetFreeCache() : (cacheBase+(which * userCacheSize)); // NOT from cache system, get a cache buffer
}

void Cache(char* buffer, size_t size) // save into cache
{
	if (!buffer) // ran out of room
	{
		OverflowRelease();
		return;
	}
	unsigned int duration = (clock() / 	CLOCKS_PER_SEC) - startSystem; // how many seconds since start of program launch

	// dont want to overflow 24bit second store... so reset system start if needed
	if ( duration > 0x000fffff) 
	{
		startSystem = clock() / CLOCKS_PER_SEC; 
		duration = 0; // how many seconds since start of program launch
		// allow all in cache to stay longer
		for (unsigned int i = 0; i < userCacheCount; ++i) cacheIndex[TIMESTAMP(i)] = duration; 
	}

	// write out users that haven't been saved recently
	unsigned int volleys = VOLLEYCOUNT(currentCache) + 1; 
	cacheIndex[TIMESTAMP(currentCache)] = duration | (volleys << 24); 
	if ( (int)volleys >= volleyLimit || overflowBuffer ) WriteCache(currentCache,size); // writecache clears the volley count - default 1 ALWAYS writes
	if (!volleyLimit) FreeUserCache(); // force reload each time, it will have already been written out immediately before

	currentCache = NO_CACHEID;
}
