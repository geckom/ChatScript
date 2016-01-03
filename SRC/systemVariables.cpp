#include "common.h"

typedef char* (*SYSTEMVARPTR)(char* value); //   value is strictly overrride for testing

typedef struct SYSTEMVARIABLE
{
    const char* name;			// script name
    SYSTEMVARPTR address;		// function used to access it
	const char* comment;		// description
} SYSTEMVARIABLE;

extern SYSTEMVARIABLE sysvars[];

char* compileDate = __DATE__    " "  __TIME__;


static char systemValue[MAX_WORD_SIZE]; // common answer place

////////////////////////////////////////////////////
/// OVERVIEW CODE 
////////////////////////////////////////////////////

void DefineSystemVariables()
{
	unsigned int i = 0;
	while (sysvars[++i].name)
	{
		if (sysvars[i].name[0] == '%') 
		{
			StoreWord((char*) sysvars[i].name)->x.topicIndex = (unsigned short) i;  // not a header
			(*sysvars[i].address)("."); // force a reset-- testing calls this to reset after changes
		}
	}
}

char* SystemVariable(char* word,char* value)
{
	WORDP D = FindWord(word);
	unsigned int index = (D) ? D->x.topicIndex : 0;
	if (!index) 
	{
		ReportBug("No system variable %s",word)
		return "";
	}
	return (*sysvars[index].address)(value);
}

void DumpSystemVariables()
{
	unsigned int i = 0;
	while (sysvars[++i].name)
	{
		char* result = (sysvars[i].address) ? (*sysvars[i].address)(NULL) : (char*)""; // actual variable or header
		if (!*result) 
		{
			if (strstr(sysvars[i].comment,"Boolean")) result = "null";
			else if (strstr(sysvars[i].comment,"Numeric")) result = "0";
			else result = "null";
		}
		if (sysvars[i].address) Log(STDUSERLOG,"%s = %s - %s\r\n",sysvars[i].name, result,sysvars[i].comment);  // actual variable
		else Log(STDUSERLOG,"%s\r\n",sysvars[i].name);  // header
	}
}

static char* AssignValue(char* hold, char* value)
{
	if (value[0] == value[1] && value[1] == '"') *value = 0;	// null string
	else if (!stricmp(value,"NULL") ) *value = 0; 
	strcpy(hold,value);
	return hold;
}

////////////////////////////////////////////////////
/// TIME AND DATE 
////////////////////////////////////////////////////

static char* Sdate(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
 	char* x = GetTimeInfo() + 8;
    ReadCompiledWord(x,systemValue);
    if (regression) return "1";
    return (systemValue[0] != '0') ? systemValue : (systemValue+1); //   1 or 2 digit date
}

static char* SdayOfWeek(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
    if (regression) return "Monday";
    ReadCompiledWord(GetTimeInfo(),systemValue);
    switch(systemValue[1])
    {
        case 'o': return "Monday";
        case 'u': return (char*)((systemValue[0] == 'T') ? "Tuesday" : "Sunday");
        case 'e': return "Wednesday";
        case 'h': return "Thursday";
        case 'r': return "Friday";
        case 'a': return "Saturday";
    }
	return "";
}

static char* SdayNumberOfWeek(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	ReadCompiledWord(GetTimeInfo(),systemValue);
	int n;
    switch(systemValue[1])
    {
		case 'u': n = (systemValue[0] != 'T') ? 1 : 3; break;
		case 'o': n = 2; break;
		case 'e': n = 4; break;
		case 'h': n = 5; break;
		case 'r': n = 6; break;
		case 'a': n = 7; break;
		default: n = 0; break;
	}
	systemValue[0] = (char)(n + '0');
	systemValue[1] = 0;
	return systemValue;
}

static char* SFullTime(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	uint64 curr = (uint64) time(0);
    if (regression) curr = 44444444; 
#ifdef WIN32
   sprintf(systemValue,"%I64d",curr); 
#else
   sprintf(systemValue,"%lld",curr); 
#endif
    return systemValue;
}

static char* Shour(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	strncpy(systemValue,GetTimeInfo()+11,2);
	systemValue[2] = 0;
    return  systemValue;
}

static char* SleapYear(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	time_t rawtime;
	time (&rawtime );
	struct tm* timeinfo = localtime (&rawtime );
    int year = timeinfo->tm_year + 1900;
	bool leap = false;
	if ((year / 400) == 0) leap = true;
	else if ((year / 100) != 0 && (year / 4) == 0) leap = true;
    return leap ? (char*)"1" : (char*)"";
}  

static char* Sdaylightsavings(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	time_t rawtime;
	time (&rawtime );
	struct tm* timeinfo = localtime (&rawtime );
    int dst = timeinfo->tm_isdst;
    return dst ? (char*)"1" : (char*)"";
}  

static char* Sminute(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	ReadCompiledWord(GetTimeInfo()+14,systemValue);
	systemValue[2] = 0;
	return systemValue;
}

static char* Smonth(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	if (regression) return "6";
    ReadCompiledWord(GetTimeInfo()+SKIPWEEKDAY,systemValue);
	switch(systemValue[0])
	{
		case 'J':  //   january june july 
			if (systemValue[1] == 'a') return "1";
			else if (systemValue[2] == 'n') return "6";
			else if (systemValue[2] == 'l') return "7";
		case 'F': return "2";
		case 'M': return (systemValue[2] != 'y') ? (char*)"3" : (char*)"5"; 
  		case 'A': return (systemValue[1] == 'p') ? (char*)"4" : (char*)"8";
		case 'S': return "9";
		case 'O': return "10";
        case 'N': return "11";
        case 'D': return "12";
	}
	return "";
}

static char* SmonthName(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	if (regression) return "June";
    ReadCompiledWord(GetTimeInfo()+SKIPWEEKDAY,systemValue);
	switch(systemValue[0])
	{
		case 'J':  //   january june july 
			if (systemValue[1] == 'a') return "January";
			else if (systemValue[2] == 'n') return "June";
			else if (systemValue[2] == 'l') return "July";
		case 'F': return "February";
		case 'M': return (systemValue[2] != 'y') ? (char*)"March" : (char*)"May"; 
  		case 'A': return (systemValue[1] == 'p') ? (char*)"April" : (char*)"August";
		case 'S': return "September";
		case 'O': return "October";
        case 'N': return "November";
        case 'D': return "December";
	}
	return "";
}

static char* Ssecond(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
    ReadCompiledWord(GetTimeInfo()+17,systemValue);
    systemValue[2] = 0;
    return systemValue;
}

static char* Svolleytime(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	clock_t diff = ElapsedMilliseconds() - startTimeInfo;
    sprintf(systemValue,"%u",(unsigned int)diff);
    return systemValue;
}

static char* Stime(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
    strncpy(systemValue,GetTimeInfo()+11,5);
    systemValue[5] = 0;
    return systemValue;
}

static char* Stimenumbers(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
    GetTimeInfo();
	sprintf(systemValue,"%2.2d %2.2d %2.2d %d %d %d %d",ptm->tm_sec,ptm->tm_min, ptm->tm_hour, ptm->tm_wday, ptm->tm_mday, ptm->tm_mon, ptm->tm_year+1900); 
    return systemValue;
}
static char* SweekOfMonth(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
    if (regression) return "1";
	unsigned int n;
	char* x = GetTimeInfo() + 8;
	if (*x == ' ') ++x; // Mac uses space, pc uses 0 for 1 digit numbers 
    ReadInt(x,n);
	systemValue[0] = (char)('0' + (n/7) + 1);
	systemValue[1] = 0;
    return systemValue;
}

static char* Syear(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
    ReadCompiledWord(GetTimeInfo()+20,systemValue);
    return (regression) ? (char*)"1951" : systemValue;
}

static char* Srand(char* value) // 1 .. 100
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	sprintf(systemValue,"%d",random(100)+1);
	return systemValue;
}

////////////////////////////////////////////////////
/// SYSTEM 
////////////////////////////////////////////////////

static char* Sall(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	return (all != 0) ? (char*)"1" : (char*)"";
}

static char* Sscript(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	sprintf(systemValue,"Script1: %s Script0: %s",timeStamp1,timeStamp0);
    return systemValue;
}

static char* Sengine(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	sprintf(systemValue,"Engine: %s",compileDate);
    return systemValue;
}

static char* Sip(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	strcpy(systemValue,ipAddress);
    return systemValue;
}

static char* Sos(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
#ifdef WIN32
	strcpy(systemValue,"windows");
#elif  MACH
	strcpy(systemValue,"mac");
#elif IOS
	strcpy(systemValue,"ios");
#elif  ANDROID
	strcpy(systemValue,"android");
#else 
	strcpy(systemValue,"linux");
#endif

    return systemValue;
}

static char* Suser(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	strcpy(systemValue,loginID);
    return systemValue;
}

static char* Sbot(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	strcpy(systemValue,computerID);
	*systemValue = GetUppercaseData(*systemValue);
    return systemValue;
}

static char* Sdict(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	sprintf(systemValue,"Dictionary: %s",dictionaryTimeStamp);
    return systemValue;
}

static char* Sversion(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	sprintf(systemValue,"Version: %s",version);
    return systemValue;
}


static char* Sfact(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	sprintf(systemValue,"%d",Fact2Index(factFree));
    return systemValue;
}

static char* Sregression(char* value)
{
	static char hold[50] = ".";
	if (value) 
	{
		if (*value != '.') regression = *value != '0';
		return strcpy(hold,value);
	}
	if (*hold != '.') return hold;
	return (regression != 0) ? (char*)"1" : (char*)"";
}

static char* ShttpResponse(char* value)
{
	static char hold[50] = ".";
	if (value) 
	{
		if (*value != '.') regression = *value != '0';
		return strcpy(hold,value);
	}
	if (*hold != '.') return hold;
	sprintf(systemValue,"%d",(int)http_response);
    return systemValue;
}

static char* ScrossTalk(char* value)
{
	static char hold[4000];
	if (value) 
	{
		size_t len = strlen(value);
		if (len >= 4000) value[len-1] = 0;
		strcpy(hold,value); 
	}
	return (*hold != '.') ? hold :  (char*)"";
}

static char* Sdocument(char* value)
{
	static char hold[50] = ".";
	if (value) return strcpy(hold,value); // may not legall set on one's own
	if (*hold != '.') return hold;
	return (documentMode != 0) ? (char*)"1" : (char*)"";
}

static char* SfreeText(char* value)
{
	static char hold[50] = ".";
	if (value) return strcpy(hold,value); // may not legall set on one's own
	int nominalUsed = maxStringBytes - (stringBase - stringFree);
	sprintf(hold,"%d",nominalUsed / 1000);
	return hold;
}

static char* SfreeWord(char* value)
{
	static char hold[50] = ".";
	if (value) return strcpy(hold,value); // may not legall set on one's own
	sprintf(hold,"%ld",((unsigned int)maxDictEntries)-(dictionaryFree-dictionaryBase));
	return hold;
}

static char* SfreeFact(char* value)
{
	static char hold[50] = ".";
	if (value) return strcpy(hold,value); // may not legall set on one's own
	if (*hold != '.') return hold;
	sprintf(hold,"%ld",factEnd-factFree);
	return hold;
}

static char* Srule(char* value) 
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	if (currentTopicID == 0 || currentRuleID == -1) return "";
	sprintf(systemValue,"%s.%d.%d",GetTopicName(currentTopicID),TOPLEVELID(currentRuleID),REJOINDERID(currentRuleID));
    return systemValue;
}

static char* Sserver(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	if (!server) return "";

	sprintf(systemValue,"%d",port);
	return systemValue;
}

static char* Stopic(char* value) 
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	GetActiveTopicName(systemValue);
    return systemValue;
}

static char* SactualTopic(char* value) 
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	strcpy(systemValue,GetTopicName(currentTopicID,false)); 
    return systemValue;
}

static char* STrace(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	if (!trace) return "0";
	sprintf(systemValue,"%d",trace);
	return systemValue;
}

////////////////////////////////////////////////////
/// USER INPUT
////////////////////////////////////////////////////

static char* Sforeign(char* value)
{
	static char hold[50] = ".";
	if (value) 
	{
		if (*value == '.') strcpy(hold,value);
		else if (!stricmp(value,"1")) tokenFlags |= FOREIGN_TOKENS;
		else if (!stricmp(value,"0")) tokenFlags &= -1 ^ FOREIGN_TOKENS;
	}
	if (*hold != '.') return hold;
	return tokenFlags & FOREIGN_TOKENS ?  (char*)"1" : (char*)"";
}

static char* Sinput(char* value)
{
	static char hold[50] = ".";
	if (value)
	{  
		if (value[0] != '.') volleyCount = atoi(value); // actually changes it
		else strcpy(hold,value);
	}
	if (*hold != '.') return hold;
	sprintf(systemValue,"%d",volleyCount); 
	return systemValue;
}

static char* Slength(char* value) 
{
	static char hold[50] = ".";
	if (value)  return AssignValue(hold,value);
	if (*hold != '.') return hold;
 	sprintf(systemValue,"%d",wordCount); 
	return systemValue;
}

static char* Smore(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
    return moreToCome ? (char*)"1" : (char*)"";
}  

static char* SmoreQuestion(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
    return moreToComeQuestion ? (char*)"1" : (char*)"";
}   

static char* SoriginalInput(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
    return mainInputBuffer;
}   

static char* SoriginalSentence(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
    return inputCopy;
}   
static char* Sparsed(char* value) 
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
    return tokenFlags & FAULTY_PARSE ? (char*)"" : (char*)"1";
}  

static char* Ssentence(char* value) 
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
    return tokenFlags & NOT_SENTENCE ? (char*)"" : (char*)"1";
}  

static char* Squestion(char* value) 
{
	static char hold[50] = ".";
	if (value) 
	{
		if (*value == '.') strcpy(hold,value);
		else if (!stricmp(value,"1")) tokenFlags |= QUESTIONMARK;
		else if (!stricmp(value,"0")) tokenFlags &= -1 ^ QUESTIONMARK;
	}
	if (*hold != '.') return hold;
    return tokenFlags & QUESTIONMARK ? (char*)"1" : (char*)"";
}  

static char* Scommand(char* value) 
{
	static char hold[50] = ".";
	if (value) 
	{
		if (*value == '.') strcpy(hold,value);
		else if (!stricmp(value,"1")) tokenFlags |= COMMANDMARK;
		else if (!stricmp(value,"0")) tokenFlags &= -1 ^ COMMANDMARK;
	}
	if (*hold != '.') return hold;
    return tokenFlags & COMMANDMARK ? (char*)"1" : (char*)"";
}  

static char* Squotation(char* value) 
{
	static char hold[50] = ".";
	if (value) 
	{
		if (*value == '.') strcpy(hold,value);
		else if (!stricmp(value,"1")) tokenFlags |= QUOTATION;
		else if (!stricmp(value,"0")) tokenFlags &= -1 ^ QUOTATION;
	}
	if (*hold != '.') return hold;
    return tokenFlags & QUOTATION ? (char*)"1" : (char*)"";
}  

static char* Simpliedyou(char* value) 
{
	static char hold[50] = ".";
	if (value) 
	{
		if (*value == '.') strcpy(hold,value);
		else if (!stricmp(value,"1")) tokenFlags |= IMPLIED_YOU;
		else if (!stricmp(value,"0")) tokenFlags &= -1 ^ IMPLIED_YOU;
	}
	if (*hold != '.') return hold;
    else return tokenFlags & IMPLIED_YOU ? (char*)"1" : (char*)"";
}  

static char* Stense(char* value) 
{
	static char hold[50] = ".";
	if (value) 
	{
		if (*value == '.') strcpy(hold,value);
		else if (!stricmp(value,"past")) {tokenFlags &= -1 & (PRESENT|FUTURE); tokenFlags |= PAST;}
		else if (!stricmp(value,"future")) {tokenFlags &= -1 & (PRESENT|PAST); tokenFlags |= FUTURE;}
		else if (!stricmp(value,"present"))  {tokenFlags &= -1 & (FUTURE|PAST); tokenFlags |= PRESENT;}
	}
	if (*hold != '.') return hold;
	else if (tokenFlags & PAST) return "past";
	else if (tokenFlags & FUTURE) return "future";
	else return "present";
}

static char* StokenFlags(char* value) 
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
#ifdef WIN32
	sprintf(systemValue,"%I64d",(long long int) tokenFlags); 
#else
	sprintf(systemValue,"%lld",(long long int) tokenFlags); 
#endif	

	return systemValue;
}

static char* SuserFirstLine(char* value)
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	sprintf(systemValue,"%d",userFirstLine); 
	return systemValue;
}

static char* SuserInput(char* value) 
{
	static char hold[50] = ".";
	if (value) 
	{
		if (*value == '.') strcpy(hold,value);
		else if (!stricmp(value,"1")) tokenFlags |= USERINPUT;
		else if (!stricmp(value,"0")) tokenFlags &= -1 ^ USERINPUT;
	}
	if (*hold != '.') return hold;
	return tokenFlags & USERINPUT ? (char*)"1" : (char*)"";
}   

static char* SrevisedInput(char* value) 
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	return inputNest ? (char*)"1" : (char*)"";
}   

static char* Svoice(char* value) 
{
	static char hold[50] = ".";
	if (value) 
	{
		if (*value == '.') strcpy(hold,value);
		else if (!stricmp(value,"1")) tokenFlags |= PASSIVE;
		else if (!stricmp(value,"0")) tokenFlags &= -1 ^ PASSIVE;
	}
	if (*hold != '.') return hold;
	return (tokenFlags & PASSIVE) ? (char*)"passive" : (char*)"active";
}

////////////////////////////////////////////////////
/// OUTPUT VARIABLES
////////////////////////////////////////////////////

static char* SinputRejoinder(char* value)
{ 
	static char hold[50] = ".";
	if (value) 
	{
		if (*value == '.') return AssignValue(hold,value);
		char* dot = strchr(value,'.');
		if (dot)
		{
			*dot = 0;
			inputRejoinderTopic = FindTopicIDByName(value);
			inputRejoinderRuleID = atoi(dot+1);
			*dot = '.';
			dot = strchr(dot+1,'.');
			if (dot) inputRejoinderRuleID |= MAKE_REJOINDERID(atoi(dot+1));
		}
		return value;
	}
	if (*hold != '.') return hold;
	if (inputRejoinderTopic == NO_REJOINDER) return (char*)"";
	sprintf(systemValue,"%s.%d.%d",GetTopicName(inputRejoinderTopic),TOPLEVELID(inputRejoinderRuleID),REJOINDERID(inputRejoinderRuleID)); 
	return systemValue;
}

static char* SlastOutput(char* value) 
{
	static char hold[500];
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	return (responseIndex) ? responseData[responseOrder[responseIndex-1]].response : (char*)"";
}

static char* SlastQuestion(char* value) 
{
	static char hold[50] = ".";
 	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	if (!responseIndex) return "";
	char* sentence = responseData[responseOrder[responseIndex-1]].response;
	size_t len = strlen(sentence);
	return (sentence[len-1] == '?') ? (char*)"1" : (char*)"";
}

static char* SoutputRejoinder(char* value)
{
	static char hold[50] = ".";
	if (value) 
	{
		if (*value == '.') return AssignValue(hold,value);
		char* dot = strchr(value,'.');
		if (dot)
		{
			*dot = 0;
			outputRejoinderTopic = FindTopicIDByName(value);
			outputRejoinderRuleID = atoi(dot+1);
			*dot = '.';
			dot = strchr(dot+1,'.');
			if (dot) outputRejoinderRuleID |= MAKE_REJOINDERID(atoi(dot+1));
		}
		return value;
	}
	if (*hold != '.') return hold;
	if (outputRejoinderTopic == NO_REJOINDER) return (char*)"";
	sprintf(systemValue,"%s.%d.%d",GetTopicName(outputRejoinderTopic),TOPLEVELID(outputRejoinderRuleID),REJOINDERID(outputRejoinderRuleID)); 
	return systemValue;
}

static char* Sresponse(char* value) 
{
	static char hold[50] = ".";
	if (value) return AssignValue(hold,value);
	if (*hold != '.') return hold;
	sprintf(systemValue,"%d",responseIndex);
	return systemValue;
}   

SYSTEMVARIABLE sysvars[] =
{ 
	{"",0,""},

	{"\r\n---- Time, Date, Number variables",0,""},
	{"%date",Sdate,"Numeric day of the month"}, 
	{"%day",SdayOfWeek,"Named day of the week"}, 
	{"%daynumber",SdayNumberOfWeek,"Numeric day of week (0=sunday)"},  
	{"%fulltime",SFullTime,"Numeric full time/date in seconds"}, 
	{"%hour",Shour,"Numeric 2-digit current hour of day (00..23)"}, 
	{"%leapyear",SleapYear,"Boolean - is it a leap year"}, 
	{"%minute",Sminute,"Numeric 2-digit current minute"}, 
	{"%month",Smonth,"Numeric month number (1..12)"},
	{"%monthname",SmonthName,"Name of month"}, 
	{"%rand",Srand,"Numeric random number (1..100)"}, 
	{"%daylightsavings",Sdaylightsavings,"Boolean is daylight savings in effect"}, 
	{"%second",Ssecond,"Numeric 2-digit current second"}, 
	{"%time",Stime,"Current military time (e.g., 21:07)"}, 
	{"%timenumbers",Stimenumbers,"numbers, separated by blanks, of sec,min,hr,dayinweek,dayinmonth,year"}, 
	{"%week",SweekOfMonth,"Numeric week of month (1..5)"}, 
	{"%volleytime",Svolleytime,"Numeric milliseconds since volley start"}, 
	{"%year",Syear,"Numeric current 4-digit year"},
	
	{"\r\n---- System variables",0,""},
	{"%all",Sall,"Boolean - is all flag on"}, 
	{"%crosstalk",ScrossTalk,"cross bot/cross document variable storage"}, 
	{"%document",Sdocument,"Boolean - is :document flag on"}, 
	{"%fact",Sfact,"Most recent fact id"}, 
	{"%freetext",SfreeText,"bytes of available text space"}, 
	{"%freeword",SfreeWord,"number of available unused words"}, 
	{"%freefact",SfreeFact,"number of available unused facts"}, 
	{"%regression",Sregression,"Boolean - is regression flag on"}, 
	{"%http_response",ShttpResponse,"http response code from last call to JsonOpen"}, 
	{"%rule",Srule,"Get a tag to current executing rule or null"}, 
	{"%server",Sserver,"Port id of server or null if not server"}, 
	{"%actualtopic",SactualTopic,"Current  topic executing (including system or nostay)"}, 
	{"%topic",Stopic,"Current interesting topic executing (not system or nostay)"}, 
	{"%trace",STrace,"Numeric value of trace flag"}, 

	{"\r\n---- Build variables",0,""},
	{"%dict",Sdict,"String - when dictionary was built"}, 
	{"%engine",Sengine,"String - when engine was compiled (date/time)"}, 
	{"%os",Sos,"String - os involved: linux windows mac ios"}, 
	{"%script",Sscript,"String - when build1 and build0 were compiled)"}, 
	{"%version",Sversion,"String - engine version number"}, 

	{"\r\n---- Input variables",0,""},
	{"%bot",Sbot,"String - bot in use"}, 
	{"%command",Scommand,"Boolean - is the current input a command"},
	{"%foreign",Sforeign,"Boolean - is the bulk of current input foreign words"},
	{"%impliedyou",Simpliedyou,"Boolean - is the current input have you as an implied subject"},
	{"%input",Sinput,"Numeric volley id of the current input"}, 
	{"%ip",Sip,"String - ip address supplied"}, 
	{"%length",Slength,"Numeric count of words of current input"}, 
	{"%login",Suser,"String - user login name suppled - same as %user"}, 
	{"%more",Smore,"Boolean - is there more input pending"}, 
	{"%morequestion",SmoreQuestion,"Boolean - is there a ? in pending input"}, 
	{"%originalinput",SoriginalInput,"returns the raw content of what user sent in"}, 
	//{"%originalsentence",SoriginalSentence,"returns the raw content of the current sentence"}, 
	{"%parsed",Sparsed,"Boolean - was current input successfully parsed"}, 
	{"%question",Squestion,"Boolean - is the current input a question"},
	{"%quotation",Squotation,"Boolean - is the current input a quotation"},
	{"%sentence",Ssentence,"Boolean - does it seem like a sentence - has subject and verb or is command"}, 
	{"%tense",Stense,"Tense of current input (present, past, future)"}, 
	{"%tokenflags",StokenFlags,"Numeric value of all tokenflags"}, 
	{"%user",Suser,"String - user login name suppled"}, 
	{"%userfirstline",SuserFirstLine,"Numeric volley count at start of session"}, 
	{"%userinput",SuserInput,"Boolean - is input coming from user"}, 
	{"%revisedInput",SrevisedInput,"Boolean - is input coming from ^input"}, 
	{"%voice",Svoice,"Voice of current input (active,passive)"}, 

	{"\r\n---- Output variables",0,""},
	{"%inputrejoinder",SinputRejoinder,"if pending input rejoinder, this is the tag of it else null"},
	{"%lastoutput",SlastOutput,"Last line of currently generated output or null"},
	{"%lastquestion",SlastQuestion,"Boolean - did last output end in a ?"}, 
	{"%outputrejoinder",SoutputRejoinder,"tag of current output rejoinder or null"}, 
	{"%response",Sresponse,"Numeric count of responses generated for current volley"}, 
	
	{NULL,NULL,""},
};
