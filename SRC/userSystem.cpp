#include "common.h"


#ifndef USERFACTS 
#define USERFACTS 100
#endif
unsigned int userFactCount = USERFACTS;			// how many facts user may save in topic file
bool serverRetryOK = false;
bool stopUserWrite = false;

static char* backupMessages = NULL;
static char* outdata; // global xfer for writetracedfunctions

//   replies we have tried already
char chatbotSaid[MAX_USED+1][SAID_LIMIT+3];  //   tracks last n messages sent to user
char humanSaid[MAX_USED+1][SAID_LIMIT+3]; //   tracks last n messages sent by user in parallel with userSaid
unsigned int humanSaidIndex;
unsigned int chatbotSaidIndex;

static char* saveVersion = "may1015";	// format of save file

int userFirstLine = 0;	// start volley of current conversation
uint64 setControl = 0;	// which sets should be saved with user

char ipAddress[50];
char computerID[ID_SIZE];
char computerIDwSpace[ID_SIZE];
char loginID[ID_SIZE];    //   user FILE name (lower case)
char loginName[ID_SIZE];    //   user typed name
char callerIP[ID_SIZE];

char timeturn15[100];
char timeturn0[20];
char timePrior[20];

void PartialLogin(char* caller,char* ip)
{
    //   make user name safe for file system
	char*  id = loginID;
	char* at = caller-1;
	char c;
	while ((c = *++at)) 
	{
		if (IsAlphaUTF8OrDigit(c) || c == '-' || c == '_' ) *id++ = c;
		else if (c == ' ') *id++ = '_';
	}
	*id = 0;

	sprintf(logFilename,"%s/%slog-%s.txt",users,GetUserPath(loginID),loginID); // user log goes here

	if (ip) strcpy(callerIP,ip);
	else *callerIP = 0;
}

void Login(char* caller,char* usee,char* ip) //   select the participants
{
	strcpy(ipAddress,(ip) ? ip : (char*)"");
	if (!stricmp(usee,"trace")) // enable tracing during login
	{
		trace = (unsigned int) -1;
		echo = true;
		*usee = 0;
	}
    if (*usee) MakeLowerCopy(computerID,usee);
	if (!*computerID) ReadComputerID(); //   we are defaulting the chatee
	if (!*computerID) ReportBug("No default bot?\r\n")

	//   for topic access validation
	*computerIDwSpace = ' ';
	MakeLowerCopy(computerIDwSpace+1,computerID);
	strcat(computerIDwSpace," ");

	if (ip && *ip) // maybe use ip in generating unique login
	{
		if (!stricmp(caller,"guest")) sprintf(caller,"guest%s",ip);
		else if (*caller == '.') sprintf(caller,"%s",ip);
	}
	char* ptr = caller-1;
	while (*++ptr) 
	{
		if (!IsAlphaUTF8OrDigit(*ptr) && *ptr != '-' ) *ptr = '_'; // require simple file names
	}

    //   prepare for chat
    PartialLogin(caller,ip);
 }

void ReadComputerID()
{
	strcpy(computerID,"anonymous");
	WORDP D = FindWord("defaultbot",0); // do we have a FACT with the default bot in it as verb
	if (D)
	{
		FACT* F = GetVerbNondeadHead(D);
		if (F) MakeLowerCopy(computerID,Meaning2Word(F->subject)->word);
	}
}

void ResetUserChat()
{
 	chatbotSaidIndex = humanSaidIndex = 0;
	setControl = 0;
	for (unsigned int i = 0; i <= MAX_FIND_SETS; ++i) SET_FACTSET_COUNT(i,0);
}

static char* SafeLine(char* line) // erase cr/nl to keep reads safe
{
	char* start = line;
	char c;
    while ((c = *++line))
    {
        if (c == '\r' && line[1]  == '\n')  // keep pair together
		{
			memmove(line+4,line+2,strlen(line+2)+1);
			line[0] = '\\';
			line[1] =  'r';
			line[2] = '\\';
			line[3] =  'n';
		}
		else if (c == '\r' || c == '\n')  // these are stand alones
		{
			memmove(line+1,line,strlen(line)+1);
			line[0] = '\\';
			line[1] = (c == '\r') ? 'r' : 'n';
		}
    }
	return start;
}

static char* WriteUserFacts(char* ptr,bool sharefile, int limit)
{
	if (!ptr) return NULL;

    //   write out fact sets first, before destroying any transient facts
	sprintf(ptr,"%x #set flags\r\n",(unsigned int) setControl);
	ptr += strlen(ptr);
	unsigned int i;
    unsigned int count;
	if (!shared || sharefile)  for (i = 0; i <= MAX_FIND_SETS; ++i) 
    {
		if (!(setControl & (uint64) (1 << i))) continue; // purely transient stuff

		//   remove dead references
		FACT** set = factSet[i];
        count = FACTSET_COUNT(i);
		unsigned int j;
        for (j = 1; j <= count; ++j)
		{
			FACT* F = set[j];
			if (F && F->flags & FACTDEAD)
			{
				memmove(&set[j],&set[j+1],sizeof(FACT*) * (count - j));
				--count;
				--j;
			}
		}
        if (!count) continue;

		// save this set
		sprintf(ptr,"#set %d\r\n",i); 
		ptr += strlen(ptr);
        for (j = 1; j <= count; ++j)
		{
			FACT* F = factSet[i][j];
			if (!F) strcpy(ptr,"0\r\n");
			else
			{
				WriteFact(F,false,ptr,false,true);
				if (F > factLocked) F->flags |= MARKED_FACT;	 // since we wrote this out here, DONT write out in general writeouts..
			}
			ptr += strlen(ptr);
			ptr =  OverflowProtect(ptr);
			if (!ptr) return NULL;
		}
		sprintf(ptr,"#end set\n"); 
		ptr += strlen(ptr);
     }
	strcpy(ptr,"#`end fact sets\r\n");
	ptr += strlen(ptr);

	// most recent facts, in order, but not those written out already as part of fact set (in case FACTDUPLICATE is on, dont want to recreate and not build2 layer facts)
	FACT* F = factFree+1;
	while (limit && --F > factLocked) // backwards down to base system facts
	{
		if (shared && !sharefile)  continue;
		if (!(F->flags & (FACTDEAD|FACTTRANSIENT|MARKED_FACT|FACTBUILD2))) --limit; // we will write this
	}

	--F;  
 	while (++F <= factFree)  
	{
		if (shared && !sharefile)  continue;
		if (!(F->flags & (FACTDEAD|FACTTRANSIENT|MARKED_FACT))) 
		{
			WriteFact(F,true,ptr,false,true);
			ptr += strlen(ptr);
			ptr =  OverflowProtect(ptr);
			if (!ptr) return NULL;
		}
	}
	//ClearUserFacts();
	strcpy(ptr,"#`end user facts\r\n");
	ptr += strlen(ptr);

	return ptr;
}

static bool ReadUserFacts()
{	
    //   read in fact sets
    char word[MAX_WORD_SIZE];
    *word = 0;
    ReadALine(readBuffer, 0); //   setControl
	ReadHex(readBuffer,setControl);
    while (ReadALine(readBuffer, 0)>= 0) 
    {
		if (*readBuffer == '#' && readBuffer[1] == ENDUNIT) break; // end of sets to read
		char* ptr = ReadCompiledWord(readBuffer,word);
        unsigned int setid;
        ptr = ReadInt(ptr,setid); 
		SET_FACTSET_COUNT(setid,0);
		if (trace & TRACE_USER) Log(STDUSERLOG,"Facts[%d]\r\n",setid);
	    while (ReadALine(readBuffer, 0)>= 0) 
		{
			if (*readBuffer == '#') break;
			char* ptr = readBuffer;
			FACT* F = ReadFact(ptr);
			AddFact(setid,F);
			if (trace & TRACE_USER) TraceFact(F);
        }
		if (*readBuffer == '#' && readBuffer[1] == ENDUNIT) break; // otherwise has #end set as the line
	}
	if (strcmp(readBuffer,"#`end fact sets")) 
	{
		ReportBug("Bad fact sets alignment\r\n")
		return false;
	}

	// read long-term user facts
	while (ReadALine(readBuffer, 0)>= 0) 
	{
		if (*readBuffer == '#' && readBuffer[1] == ENDUNIT) break;
		char* data = readBuffer;
		if (*data == '(' && strchr(data,')')) ReadFact(data);
		else 
		{
			ReportBug("Bad user fact %s\r\n",readBuffer)
			return false;
		}
		
	}	
    if (strcmp(readBuffer,"#`end user facts")) 
	{
		ReportBug("Bad user facts alignment\r\n")
		return false;
	}

	return true;
}

static char* WriteRecentMessages(char* ptr,bool sharefile)
{
	if (!ptr) return NULL; // buffer ran out long ago

    //   recent human inputs
	int start = humanSaidIndex - 20; 
	if (start < 0) start = 0;
	unsigned int i;
    if (!shared || sharefile) for (i = start; i < (unsigned int)humanSaidIndex; ++i)  
	{
		size_t len = strlen(humanSaid[i]);
		if (len == 0) continue;
		ptr =  OverflowProtect(ptr);
		if (!ptr) return NULL;
		sprintf(ptr,"%s\r\n",SafeLine(humanSaid[i]));
		ptr += strlen(ptr);
	}
	strcpy(ptr,"#`end user\r\n");
	ptr += strlen(ptr);
	
	// recent chatbot outputs
 	start = chatbotSaidIndex - 20;
	if (start < 0) start = 0;
    if (!shared || sharefile) for (i = start; i < (int)chatbotSaidIndex; ++i) 
	{
		size_t len = strlen(chatbotSaid[i]);
		if (len == 0) continue;
		ptr =  OverflowProtect(ptr);
		if (!ptr) return NULL;
		sprintf(ptr,"%s\r\n",SafeLine(chatbotSaid[i]));
		ptr += strlen(ptr);
	}
	strcpy(ptr,"#`end chatbot\r\n");
	ptr += strlen(ptr);

	return ptr;
}

static bool ReadRecentMessages()
{
	char* buffer = AllocateBuffer();
	char* original = buffer;
	*buffer = 0;
	buffer[1] = 0;
    for (humanSaidIndex = 0; humanSaidIndex <= MAX_USED; ++humanSaidIndex) 
    {
        ReadALine(humanSaid[humanSaidIndex], 0);
		if (*humanSaid[humanSaidIndex] == '#' && humanSaid[humanSaidIndex][1] == ENDUNIT) break; // #end
		strcpy(buffer,humanSaid[humanSaidIndex]);
		buffer += strlen(buffer) + 1;
    }
	if (humanSaidIndex > MAX_USED || strcmp(humanSaid[humanSaidIndex],"#`end user"))  // failure to end right
	{
		humanSaidIndex = 0;
		chatbotSaidIndex = 0;
		ReportBug("bad humansaid")
		return false;
	}
	else *humanSaid[humanSaidIndex] = 0;
	*buffer++ = 0;

	for (chatbotSaidIndex = 0; chatbotSaidIndex <= MAX_USED; ++chatbotSaidIndex) 
    {
        ReadALine(chatbotSaid[chatbotSaidIndex], 0);
		if (*chatbotSaid[chatbotSaidIndex] == '#' && chatbotSaid[chatbotSaidIndex][1] == ENDUNIT) break; // #end
		strcpy(buffer,chatbotSaid[chatbotSaidIndex]);
		buffer += strlen(buffer) + 1;
    }
	if (chatbotSaidIndex > MAX_USED || strcmp(chatbotSaid[chatbotSaidIndex],"#`end chatbot")) // failure to end right
	{
		chatbotSaidIndex = 0;
		ReportBug("Bad message alignment\r\n")
		return false;
	}
	else *chatbotSaid[chatbotSaidIndex] = 0;
	*buffer++ = 0;
	backupMessages = AllocateString(original,buffer-original); // create a backup copy
	FreeBuffer();
	return true;
}

void RecoverUser() // regain stuff we loaded from user
{
	chatbotSaidIndex = humanSaidIndex = 0;
	char* at = backupMessages;
	while (at && *at) // read human said messages
	{
		strcpy(humanSaid[humanSaidIndex++],at);
		at += strlen(at)+1;
	}
	*humanSaid[humanSaidIndex] = 0;

	if (at) ++at; // skip over null separator

	while (at && *at) // read human said messages
	{
		strcpy(chatbotSaid[chatbotSaidIndex++],at);
		at += strlen(at)+1;
	}
	*chatbotSaid[chatbotSaidIndex] = 0;

	randIndex =  oldRandIndex;

	// recover loaded topic info
	memcpy(pendingTopicList,originalPendingTopicList,sizeof(unsigned int) * (originalPendingTopicIndex + 1));
	pendingTopicIndex = originalPendingTopicIndex;
}

char* WriteUserVariables(char* ptr,bool sharefile, bool compiling)
{
	if (!ptr) return NULL;
	unsigned int index = userVariableIndex;
    while (index)
    {
        WORDP D = userVariableList[--index];
        if (!(D->internalBits & VAR_CHANGED) ) continue; 
		if (*D->word != '$') ReportBug("Bad user variable to save %s\r\n",D->word)
		else if (shared && !sharefile && !strnicmp(D->word,"$share_",7)) continue;
  		else if (shared && sharefile && strnicmp(D->word,"$share_",7)) continue;
        else if (D->word[1] !=  '$' && D->w.userValue) // transients not dumped, nor are NULL values
		{
			char* val = D->w.userValue;
			while ((val = strchr(val,'\n'))) *val = ' '; //  clean out newlines
			if (!stricmp(D->word,"$cs_trace")) 
			{
				sprintf(ptr,"%s=%d\r\n",D->word,trace);
				trace = 0;
				echo = false;
			}
			else sprintf(ptr,"%s=%s\r\n",D->word,SafeLine(D->w.userValue));
			ptr += strlen(ptr);
			if (!compiling)
			{
				ptr =  OverflowProtect(ptr);
				if (!ptr) return NULL;
			}
		}
        D->w.userValue = NULL;
		RemoveInternalFlag(D,VAR_CHANGED);
    }
	strcpy(ptr,"#`end variables\r\n");
	ptr += strlen(ptr);
	
	return ptr;
}

static bool ReadUserVariables()
{
	while (ReadALine(readBuffer, 0)>= 0) //   user variables
	{
		if (*readBuffer != '$') break; // end of variables
        char* ptr = strchr(readBuffer,'=');
        *ptr = 0; // isolate user var name from rest of buffer
        SetUserVariable(readBuffer,ptr+1);
		if (!stricmp(readBuffer,"$cs_trace")) 
		{
			trace = atoi(ptr+1);
			echo = true;
		}

		if (trace & TRACE_VARIABLE) Log(STDUSERLOG,"uservar: %s=%s\r\n",readBuffer,ptr+1);
    }

	if (strcmp(readBuffer,"#`end variables")) 
	{
		ReportBug("Bad variable alignment\r\n")
		return false;
	}
	return true;
}

static char* GatherUserData(char* ptr,time_t curr,bool sharefile)
{
	if (!timeturn15[1] && volleyCount >= 15 && responseIndex) sprintf(timeturn15,"%lu-%d%s",(unsigned long)curr,responseData[0].topic,responseData[0].id); // delimit time of turn 15 and location...
	sprintf(ptr,"%s %s %s %s |\n",saveVersion,timeturn0,timePrior,timeturn15); 
	ptr += strlen(ptr);
	ptr = WriteUserTopics(ptr,sharefile);
	
	int count = userFactCount;
	char* value = GetUserVariable("$cs_userfactlimit");
	if (value && *value) count = atoi(value);

	ptr = WriteUserVariables(ptr,sharefile,false);
	ptr = WriteUserFacts(ptr,sharefile,count);
	ptr = WriteUserContext(ptr,sharefile);
	ptr = WriteRecentMessages(ptr,sharefile);
	return ptr;
}

void WriteUserData(time_t curr)
{ 
	if (!numberOfTopics)  return; //   no topics ever loaded or we are not responding
	if (!userCacheCount) return;	// never save users - no history
	char name[MAX_WORD_SIZE];
	sprintf(name,"%s/%stopic_%s_%s.txt",users,GetUserPath(loginID),loginID,computerID);
	userDataBase = FindUserCache(name); // have a buffer dedicated to him? (cant be safe with what was read in, because share involves 2 files)
	if (!userDataBase)
	{
		userDataBase = GetCacheBuffer(-1); 
		if (!userDataBase) return;		// not saving anything
		strcpy(userDataBase,name);
	}

#ifndef DISCARDTESTING
	if ((!server || serverRetryOK) && !documentMode && !callback)  
	{
		char name[MAX_WORD_SIZE];
		sprintf(name,"TMP/backup-%s_%s.bin",loginID,computerID);
		CopyFile2File(name,userDataBase,false);	// backup for debugging BUT NOT if callback of some kind...
		if (redo) // multilevel backup enabled
		{
			sprintf(name,"TMP/backup%d-%s_%s.bin",volleyCount,loginID,computerID);
			CopyFile2File(name,userDataBase,false);	// backup for debugging BUT NOT if callback of some kind...
		}
	}
#endif

	char* ptr = GatherUserData(userDataBase+strlen(userDataBase)+1,curr,false);
	Cache(userDataBase,ptr-userDataBase);
	if (shared)
	{
		sprintf(name,"%s/%stopic_%s_%s.txt",users,GetUserPath(loginID),loginID,"share");
		userDataBase = FindUserCache(name); // have a buffer dedicated to him? (cant be safe with what was read in, because share involves 2 files)
		if (!userDataBase)
		{
			userDataBase = GetCacheBuffer(-1); // cannot fail if we got to here
			strcpy(userDataBase,name);
		}

#ifndef DISCARDTESTING
		if ((!server || serverRetryOK)  && !documentMode  && !callback)  
		{
			char name[MAX_WORD_SIZE];
			sprintf(name,"TMP/backup-share-%s_%s.bin",loginID,computerID);
			CopyFile2File(name,userDataBase,false);	// backup for debugging
			if (redo)
			{
				sprintf(name,"TMP/backup%d-share-%s_%s.bin",volleyCount,loginID,computerID);
				CopyFile2File(name,userDataBase,false);	// backup for debugging BUT NOT if callback of some kind...
			}
		}
#endif
		ptr = GatherUserData(userDataBase+strlen(userDataBase)+1,curr,true);
		Cache(userDataBase,ptr-userDataBase);
	}
	userVariableIndex = 0; // flush all modified variables
}

void ReadFileData(char* bot) // passed  buffer with file content (where feasible)
{	
	char* buffer = GetFileRead(loginID,bot);
	size_t len = 0;
	char junk[MAX_WORD_SIZE];
	*junk = 0;
	strcpy(timePrior,"0");
	strcpy(timeturn15,"0");
	strcpy(timeturn0,"0");

	// set bom
	currentFileLine = 1;
	BOM = 1; 

	if (buffer && *buffer != 0) // readable data
	{ 
		len = strlen(buffer);
		if (len > 100) // supposed to just be user filename info. compensate
		{
			char junk[MAX_WORD_SIZE];
			char* p = ReadCompiledWord(buffer,junk);
			len = p - buffer - 1; 
		}
		userRecordSourceBuffer = buffer + len + 1;
		ReadALine(readBuffer,0);
		char* x = ReadCompiledWord(readBuffer,junk);
		x = ReadCompiledWord(x,timeturn0); // the start stamp id if there
		x = ReadCompiledWord(x,timePrior); // the prior stamp id if there
		ReadCompiledWord(x,timeturn15); // the timeturn id if there
		if (stricmp(junk,saveVersion)) *buffer = 0;// obsolete format
	}
    if (!buffer || !*buffer) 
	{
		// if shared file exists, we dont have to kill it. If one does exist, we merely want to use it to add to existing bots
		ReadNewUser();
		strcpy(timeturn0,GetMyTime(time(0))); // startup time
	}
	else
	{
		if (!ReadUserTopics()) return;
		if (!ReadUserVariables()) return;
		if (!ReadUserFacts()) return;
		if (!ReadUserContext()) return;
		if (!ReadRecentMessages()) return;
		oldRandIndex = randIndex = atoi(GetUserVariable("$cs_randindex")) + (volleyCount % MAXRAND);	// rand base assigned to user
	}
	userRecordSourceBuffer = NULL;
	OverflowRelease();
}

void ReadUserData() // passed  buffer with file content (where feasible)
{	
	// std defaults
	tokenControl = (DO_SUBSTITUTE_SYSTEM | DO_INTERJECTION_SPLITTING | DO_PROPERNAME_MERGE | DO_NUMBER_MERGE | DO_SPELLCHECK | DO_PARSE );
	responseControl = ALL_RESPONSES;
	*wildcardSeparator = ' ';

	ResetUserChat();
	ReadFileData(computerID); // read user file, if any, or get it from cache
	if (shared) ReadFileData("share");  // read shared file, if any, or get it from cache
}

void KillShare()
{
	if (shared) 
	{
		char buffer[MAX_WORD_SIZE];
		sprintf(buffer,"%s/%stopic_%s_%s.txt",users,GetUserPath(loginID),loginID,"share");
		unlink(buffer); // remove all shared data of this user
	}
}

void ReadNewUser()
{
	if (trace & TRACE_USER) Log(STDUSERLOG,"New User\r\n");
	ResetUserChat();
	ClearUserVariables();
	ClearUserFacts();
	ResetTopicSystem(true);

	userFirstLine = 1;
	volleyCount = 0;
	// std defaults
	tokenControl = (DO_SUBSTITUTE_SYSTEM | DO_INTERJECTION_SPLITTING | DO_PROPERNAME_MERGE | DO_NUMBER_MERGE | DO_SPELLCHECK | DO_PARSE );
	responseControl = ALL_RESPONSES;
	*wildcardSeparator = ' ';

	//   set his random seed
	bool hasUpperCharacters;
	bool hasUTF8Characters;
	unsigned int rand = (unsigned int) Hashit((unsigned char *) loginID,strlen(loginID),hasUpperCharacters,hasUTF8Characters);
	char word[MAX_WORD_SIZE];
	oldRandIndex = randIndex = rand & 4095;
    sprintf(word,"%d",randIndex);
	SetUserVariable("$cs_randindex",word ); 
	strcpy(word,computerID);
	*word = GetUppercaseData(*word);
	SetUserVariable("$cs_bot",word ); 
	SetUserVariable("$cs_login",loginName);

	sprintf(readBuffer,"^%s",computerID);
	WORDP D = FindWord(readBuffer,0,LOWERCASE_LOOKUP);
	if (!D) // no such bot
	{
		*computerID = 0;
		return;
	}

	char* buffer = AllocateBuffer();
	*buffer = 0;
	PushOutputBuffers();
	currentRuleOutputBase = currentOutputBase = buffer;
	ChangeDepth(1,"ReadNewUser");
	FunctionResult result;
	DoFunction(D->word,"()",buffer,result);
	PopOutputBuffers();
	ChangeDepth(-1,"ReadNewUser");
	FreeBuffer();

	inputRejoinderTopic = inputRejoinderRuleID = NO_REJOINDER; 
}
