#include "common.h"
extern int ignoreRule;
#ifndef DISCARDTESTING

static unsigned int lineLimit = 0; // in abstract report lines that are longer than this...
static WORDP topLevel = 0;
static unsigned int err = 0;
static unsigned int filesSeen; 
static 	char directory[MAX_WORD_SIZE];
static int itemcount = 0;
static char* abstractBuffer;
static bool docstats = false;
static int longLines;
static uint64 verifyToken;

static WORDP dictUsedG;
static FACT* factUsedG;
static char* textUsedG;
static int trials;

#define ABSTRACT_SPELL 1
#define ABSTRACT_SET_MEMBER 2
#define ABSTRACT_CANONICAL 4
#define ABSTRACT_PRETTY 8
#define ABSTRACT_VP 16
#define ABSTRACT_NOCODE 32
#define ABSTRACT_STORY 64
#define ABSTRACT_RESPONDER 128
#define ABSTRACT_RESTRICTIONS (ABSTRACT_SPELL|ABSTRACT_SET_MEMBER|ABSTRACT_CANONICAL|ABSTRACT_PRETTY|ABSTRACT_VP )

static bool fromScript = false;

#define RECORD_SIZE 4000

static void ShowTrace(unsigned int bits, bool original);

// prototypes
static bool DumpOne(WORDP S,int all,int depth,bool shown);
static int CountDown(MEANING T,int all,int depth,unsigned int baseStamp);
static void C_Retry(char* input);

static MEANING* meaningList; // list of meanings from :concepts
static MEANING* meaningLimit; // end of meaninglistp

////////////////////////////////////////////////////////
/// UTILITY ROUTINES
////////////////////////////////////////////////////////

int CountSet(WORDP D,unsigned int baseStamp) //   full recursive referencing
{
	if (!D) return 0;

	int count = 0;
	FACT* F = GetObjectNondeadHead(D);
	FACT* G;
	while (F) //   do all atomic members of it
	{
		G = F;
		F = GetObjectNondeadNext(F);
		WORDP S = Meaning2Word(G->subject);
		if (!(G->verb == Mmember)  || G->flags & FACTDEAD) continue;
		if (*S->word == '~' ) continue;
		else if (Meaning2Index(G->subject)) count += CountDown(GetMaster(G->subject),-1,-2,baseStamp); //   word~2 reference is a synset header -- follow IS_A submembers
		else //   simple atomic member -- or POS specificiation
		{
			if (S->inferMark <= baseStamp) //   count once
			{
				S->inferMark = inferMark;
				++count;
			}
		}
	}
	F = GetObjectNondeadHead(D);
	while (F) //   do all set members of it
	{
		G = F;
		F = GetObjectNondeadNext(F);
		WORDP S = Meaning2Word(G->subject);
		if (!(G->verb == Mmember)  || G->flags & FACTDEAD) continue;
		if (*S->word == '~')  count += CountSet(S,baseStamp);
	}
	return count;
}

static int CountDown(MEANING T,int all,int depth,unsigned int baseStamp)
{ //  T is a synset header
	T &= -1 ^ SYNSET_MARKER;

	if (all == 5) return 0;
	int count = 0;

	//   show each word in synset
    WORDP D = Meaning2Word(T);
	WORDP baseWord = D;
	unsigned int index = Meaning2Index(T);
	unsigned int baseIndex = index;

	// walk the master list of synonyms at this level
	bool shown = false;
	while (ALWAYS) 
    {
		MEANING next = GetMeaning(D,index);
		if (D->inferMark != inferMark) 
		{
			if (D->inferMark <= baseStamp) ++count;
			D->inferMark = inferMark;	
			if (depth >= 0 ) shown |= DumpOne(D,all,depth,shown); //   display it
		}
		D = Meaning2Word(next);
		index = Meaning2Index(next);
		if (D == baseWord && index == baseIndex) break; // back at start of loop
    }

	//   down go down to next level synset from this one
	FACT* F = GetObjectNondeadHead(T); 
	while (F)
	{
		if (F->verb ==  Mis && F->object == T) count += CountDown(F->subject,all,(depth == -2) ? -2 : (depth+1),baseStamp);
		F = GetObjectNondeadNext(F);
	}
	return count;
}

static void Indent(int count,bool nonumber)
{
	if (!nonumber) Log(STDUSERLOG,"%d.",count);
	while (count--) Log(STDUSERLOG,"    ");
}

static bool DumpOne(WORDP S,int all,int depth,bool shown)
{
	bool did = false;
	if (all) 
	{
			if ( all == 3) return false;
			if (itemcount == 0 && all != 2) Indent(depth,shown);
			unsigned char* data = GetWhereInSentence(S);
			if (all == 1) 
			{
				if (!data)
				{
					AllocateWhereInSentence(S);
					data = GetWhereInSentence(S);
					if (!data) return false;
					*data = 0;
					data[1] = 0;
				}
				if (++data[1] == 0) ++data[0];
			}
			if (all == 1 && *data && (data[0] || data[1] > 1)) Log(STDUSERLOG,"+%s  ",S->word); //   multiple occurences
			else  //   first occurence of word
			{
				if (all == 1 && !(S->systemFlags & VERB_DIRECTOBJECT)) //   generate a list of intransitive verbs
				{
					FILE* out = FopenUTF8WriteAppend("intransitive.txt");
					fprintf(out,"%s 1\r\n",S->word);
					fclose(out);
				}
				if (all == 1 && (S->systemFlags & VERB_INDIRECTOBJECT)) //   generate a list of dual transitive verbs
				{
					FILE* out = FopenUTF8WriteAppend("intransitive.txt");
					fprintf(out,"%s 2\r\n",S->word);
					fclose(out);
				}
				Log(STDUSERLOG,"%s  ",S->word);
			}
			++itemcount;
			if (itemcount == 10 && all != 2)
			{
				Log(STDUSERLOG,"\r\n");
				itemcount = 0;
			}
			did = true;
	}
	return did;
}

static void MarkExclude(WORDP D)
{
	FACT* F = GetObjectNondeadHead(D);
	while (F)
	{
		if (F->verb == Mexclude) Meaning2Word(F->subject)->inferMark = inferMark;
		F = GetObjectNondeadNext(F);
	}
}

/////////////////////////////////////////////
/// TESTING
/////////////////////////////////////////////

static void C_AutoReply(char* input)
{
	regression = 1;
	strcpy(oktest,input);
	if (!*oktest)  regression =  false;
	if (*oktest) Log(STDUSERLOG,"Auto input set to %s\r\n",oktest);
}  

static void C_NoReact(char* input)
{
	noReact = !noReact;
	Log(STDUSERLOG,"Noreact = %d\r\n",noReact);
} 

static void C_POS(char* input)
{
	if (!*input) prepareMode = (prepareMode == POS_MODE) ? NO_MODE : POS_MODE;
	else 
	{
		unsigned int oldtrace = trace;
		uint64 oldTokenControl = tokenControl;

		char word[MAX_WORD_SIZE];
		char* at = ReadCompiledWord(input,word);
		if (!stricmp(word,"PENN"))
		{
			input = at;
			tokenControl = STRICT_CASING | DO_ESSENTIALS| DO_PARSE | DO_CONTRACTIONS| NO_HYPHEN_END | NO_COLON_END | NO_SEMICOLON_END | TOKEN_AS_IS;
		}
		else 
		{
			char* token = GetUserVariable("$cs_token");
			int64 f;
			ReadInt64(token,f);
			if (f == 0) f = DO_ESSENTIALS| DO_PARSE | DO_CONTRACTIONS| NO_HYPHEN_END | NO_COLON_END | NO_SEMICOLON_END | TOKEN_AS_IS;
			tokenControl = f;
		}
		trace = (unsigned int) -1;
		tmpPrepareMode = POS_MODE;
		quotationInProgress = 0;	
		PrepareSentence(input,true,true);	
		tmpPrepareMode = NO_MODE;
		tokenControl = oldTokenControl;
		trace = oldtrace;
	}
}

static void C_Prepare(char* input)
{
	uint64 oldToken = tokenControl;
	input = SkipWhitespace(input);
	static bool prepass = true;
	char word[MAX_WORD_SIZE];
	if (*input == '$') // set token control to this
	{
		char* ptr = ReadCompiledWord(input,word);
		char* value = GetUserVariable(word);
		if (value && *value)
		{
			input = ptr;
			int64 val64 = 0;
			ReadInt64(value,val64);
			tokenControl = val64;
		}
	}
	input = SkipWhitespace(input);
	if (!strnicmp(input,"NOPREPASS",9) || !strnicmp(input,"PREPASS",7))
	{
		prepass = strnicmp(input,"NOPREPASS",9) ? true : false;
		input = ReadCompiledWord(input,word);
	}

	if (!*input) prepareMode = (prepareMode == PREPARE_MODE) ? NO_MODE : PREPARE_MODE;
	else 
	{
		char prepassTopic[MAX_WORD_SIZE];
		strcpy(prepassTopic, GetUserVariable("$cs_prepass"));
		unsigned int oldtrace = trace;
		nextInput = input;
		while (*nextInput)
		{
			prepareMode = PREPARE_MODE;
			if (*prepassTopic) Log(STDUSERLOG,"Prepass: %s\r\n", prepass ? "ON" : "OFF");
			PrepareSentence(nextInput,true,true);	
			prepareMode = NO_MODE;
			if (!trace) trace = TRACE_OUTPUT | TRACE_MATCH | TRACE_PREPARE;
			if (prepass && PrepassSentence(prepassTopic)) continue;
		}
		trace = oldtrace;
	}
	tokenControl = oldToken;
}

static void MemorizeRegress(char* input)
{
	char word[MAX_WORD_SIZE];
	input = ReadCompiledWord(input,word);
	char outputfile[MAX_WORD_SIZE];
	ReadCompiledWord(input,outputfile);
	FILE* in = FopenReadNormal(word); // source full name given
	char file[MAX_WORD_SIZE];
	if (!in)
	{
		char* txt = strstr(word,".txt");
		if (txt) *txt = 0;
		sprintf(file,"%s/log-%s.txt",users,word); // presume only login given, go find full file
		in = FopenReadNormal(file); // source
	}
	if (!in) Log(STDUSERLOG,"Couldn't find %s\n",file);
	else  
	{
		FILE* out = FopenUTF8Write(outputfile);
		if (!out)
		{
			out = FopenUTF8Write("TMP/regress.txt");
			if (!out)
			{
				printf("cannot open %s\r\n",outputfile);
				return;
			}
		}
		char* at;
		bool start = true;
		while (ReadALine(readBuffer,in)  >= 0) // read log file
		{
			if (!*readBuffer) continue;
			size_t len;
			// Start: user:fa bot:patient1a ip: rand:247 (~introductions) 0 ==> Hello Doctor  When:Mar23'14-20:06:23 Version:4.2 Build0: Build1:Mar23'14-20:04:11 0:Mar23'14-20:06:18 F:0 P:0 Why:~introductions.0.0.~control.6.0 
			// Respond: user:fa bot:patient1a ip: (~introductions) 1  fa ==> I'm afraid I don't understand that question.  When:Mar23'14-20:06:30 Why:~control.10.0=MAINCONTROL 
			// fields are: type, user, bot, ip, {rand}, (resulting topic), current volley id, user input, ==> bot output, when: {version/build1/build0/f:/p:) followed by why: rule tags for each issued output.
		
			char kind[MAX_WORD_SIZE];
			ReadCompiledWord(readBuffer,kind);

			if (strcmp(kind,"Respond:") && strcmp(kind,"Start:") ) continue; // abnormal line? like a ^log entry.

			// normal volley
			char user[MAX_WORD_SIZE];
			char* ptr = strstr(readBuffer,"user:") + 5;
			ptr = ReadCompiledWord(ptr,user);

			unsigned int volley;
			char* endtopic = strchr(ptr,')');
			volley = atoi(endtopic+2);

			int rand = -1;
			char* randptr = strstr(ptr,"rand:");
			if (randptr) rand = atoi(randptr+5);
	
			// confirm legit startup
			if (start == true)
			{
				if (volley || *kind != 'S') 
				{
					Log(STDUSERLOG,"Log file must begin with Start at turn 0, not turn %d\r\n",volley);
					fclose(in);
					return;
				}
				start = false;
			}

			char bot[MAX_WORD_SIZE];
			ptr = strstr(readBuffer,"bot:") + 4;
			ptr = ReadCompiledWord(ptr,bot); 

			char topic[MAX_WORD_SIZE];
			at = strchr(ptr,'(') + 1;
			*endtopic = 0;
			at = ReadCompiledWord(at,topic);	
		
			char junk[MAX_WORD_SIZE];
			at = endtopic + 2;
			at = ReadCompiledWord(at,junk) - 1; // point at blank
			char* input = at; // now points to user input start

			char* output = strstr(at," ==> ");
			if (!output) continue;
			*output = 0;	// end of input
			input = SkipWhitespace(input);
			output += 5;
			output = SkipWhitespace(output);  // start of output

			char* why = strstr(output,"Why:");
			char* end = strstr(output," When:");
			if (end) *end = 0; // end of output
			if (rand != -1) fprintf(out,"%s user:%s bot:%s rand:%d (%s) %d ==> %s\r\n", kind, user, bot,rand,topic,volley,output);
			else fprintf(out,"%s user:%s bot:%s (%s) %d %s ==> %s\r\n", kind, user, bot,topic,volley,input,output);

			if (!why) continue;
			
			why += 4;
			end = strchr(why+1,'~'); // 2nd rule via if there is one
			if (end) *end = 0;
			unsigned int topicid;
			int id;
			char* verify = GetVerify(why,topicid,id);
			char* rule = GetRule(topicid,id);		// the rule we want to test
			char label[MAX_WORD_SIZE];
			char pattern[MAX_WORD_SIZE];
			char outputdata[MAX_WORD_SIZE];
			char* output1 = GetPattern(rule,label,pattern);
			len = strlen(output1);
			if (len > 50) len = 50;
			strncpy(outputdata,output1,len);
			while (outputdata[len-1] == ' ') --len;
			outputdata[len] = 0;
			pattern[50] = 0;	 // limit it
			fprintf(out,"  verify: %s rule:%s kind:%c label:%s pattern: %s output: %s \r\n",verify, why,*rule,label,pattern,outputdata);

			if (!end)
			{
				fprintf(out,"  verify2: \r\n");
				continue;
			}

			*end = '~';
			verify = GetVerify(end,topicid,id);
			rule = GetRule(topicid,id);		// the rule we want to test
			output1 = GetPattern(rule,label,pattern);
			len = strlen(output1);
			if (len > 50) len = 50;
			strncpy(outputdata,output1,len);
			outputdata[len] = 0;
			pattern[50] = 0;	 // limit it
			fprintf(out,"  verify2: %s rule:%s kind:%c label:%s pattern: %s output: %s \r\n",verify, end,*rule,label,pattern,outputdata);
		}
		fclose(out);
		fclose(in);
		Log(STDUSERLOG,"Regression file %s created\n",outputfile);
	}
}

static void VerifyRegress(char* file)
{
	char word[MAX_WORD_SIZE];
	char* at = ReadCompiledWord(file,word);
	bool silent = false;
	if (!stricmp(word,"terse")) 
	{
		file = at;
		silent = true;
	}
	FILE* in = FopenReadNormal(file); // source
	if (!in)
	{
		printf("No regression data found for %s\r\n",file);
		return;
	}
	sprintf(logFilename,"%s/tmpregresslog.txt",users); // user log goes here so we can regenerate a new regression file if we need one
	FILE* out = FopenUTF8Write(logFilename); // make a new log file to do this in.
	if (out) fclose(out);

	int olduserlog = userLog;
	userLog = LOGGING_SET;
	unsigned int changed = 0;
	bool modified = false;
	bool oldecho = echo;
	echo = false;
	unsigned int count = 0;
	prepareMode = REGRESS_MODE;
	size_t len;
	unsigned int minorchange = 0;
	char verifyinfo[MAX_BUFFER_SIZE];
	unsigned int volley = 0;
	char myBuffer[MAX_BUFFER_SIZE];
	regression = REGRESS_REGRESSION;
	while (ReadALine(myBuffer,in) >= 0 ) // read regression file
	{
		//Start: user:fd bot:rose rand:553 volley:0 topic:~hello input:  output: Good morning.  
		//	verify:  rule:~hello.1.0. kind:t label: pattern: ( !$olduser =8%input=0 =7%hour<12 )  output: $olduser = 1 Good morning. $begintime = %fulltime  
		//	verify2:  rule:~submain_control.5.0  kind:u label: pattern: ( =8%input<%userfirstline )  output: $repeatstart = %userfirstline + 10 ^gambit ( ~hell 
		//Respond: user:fd bot:rose volley:1 topic:~hello input: what is your name output: My name is Rose. What's yours?  
		//	verify:  rule:~hello.4.0=MYNAME. kind:t label:MYNAME pattern: ( )  output: My name is Rose. $begintime = %fulltime ^^if ( ! $ 
		//	verify2: what is your name?  rule:~physical_self.101.0=TELLNAME  kind:u label:TELLNAME pattern: ( ![ him my her them ] << what your [ name moniker output: ^reuse ( ~hello.myname ) `01b u: ( !my what * you  
		if (!*myBuffer) continue;
		char* ptr = SkipWhitespace(myBuffer);
		if (*ptr == '#' || !*ptr) continue;
		if (strstr(ptr,":quit")) break; // assume done
		if (strstr(ptr,":trace"))
		{
			trace = (trace == -1) ? 0 : -1;
			echo = (trace != 0);
			continue;
		}

		char user[MAX_WORD_SIZE];
		char* u = strstr(ptr,"user:") + 5;
		ptr = ReadCompiledWord(u,user);
		
		char bot[MAX_WORD_SIZE];
		u = strstr(myBuffer,"bot:") + 4;
		ptr = ReadCompiledWord(u,bot);	
		
		ptr = strchr(ptr,'(');
		char topic[MAX_WORD_SIZE];
		char* end = strchr(ptr,')');
		*end = 0;
		ptr = ReadCompiledWord(ptr + 1,topic);	// now points to volley
		*end = ')';

		char volleyid[MAX_WORD_SIZE];
		ptr = ReadCompiledWord(ptr+1,volleyid); // volley id
		char* vinput = ptr;
		char* oldsaid = strstr(vinput,"==> ");
		char actualOutput[MAX_WORD_SIZE];
		strcpy(actualOutput,oldsaid + 4);
		*oldsaid = 0;
		if (*(oldsaid-1) == ' ') *(oldsaid-1) = 0;
		if (*(oldsaid-2) == ' ') *(oldsaid-2) = 0;
		oldsaid += 4;
		oldsaid = TrimSpaces(oldsaid,true);

		// EXECUTE the input choice
		char buffer[MAX_BUFFER_SIZE];
		mainOutputBuffer = buffer;

		// bot login
		strcpy(computerID,bot);
		*computerIDwSpace = ' ';
		MakeLowerCopy(computerIDwSpace+1,computerID);
		strcat(computerIDwSpace," ");

		strcpy(loginID,user); // user login

		if (*myBuffer == 'S') // start it
		{
			int depth = globalDepth; // reset clears depth, but we are still in process so need to restore it
			int turn = atoi(volleyid);
			if (turn == 0) ResetUser(vinput); // force reset
			globalDepth = depth;
			*vinput = 0;
			userFirstLine = volleyCount+1;
			*readBuffer = 0;
			nextInput = vinput;
			FinishVolley(vinput,buffer,NULL);
			char* revised = Purify(buffer);
			if (revised != buffer) strcpy(buffer,revised);
			TrimSpaces(buffer,false);
			if (!responseIndex)
			{
				Log(ECHOSTDUSERLOG,"*** No response to startup\r\n");
			}
		}
		else if (*myBuffer == 'R')// respond
		{
			int depth = globalDepth; // reset clears depth, but we are still in process so need to restore it
			++volley;
			ReadUserData();
			char myinput[MAX_WORD_SIZE];
			strcpy(myinput,vinput);
			globalDepth = depth;
			ProcessInput(myinput);
			FinishVolley(myinput,buffer,NULL);
			char* revised = Purify(buffer);
			if (revised != buffer) strcpy(buffer,revised);
			TrimSpaces(buffer,false);
			if (!responseIndex)
			{
				Log(ECHOSTDUSERLOG,"*** No response to user input\r\n");
			}
		}
		else
		{
			Log(STDUSERLOG,"Bad regression file lineup %s\r\n",myBuffer);
			continue;
		}
		++count;

		// now get verification data
		ReadALine(readBuffer,in);
		strcpy(verifyinfo,readBuffer); // copy so we can debug seeing original data
		//	verify:  rule:~hello.1.0. kind:t label: pattern: ( !$olduser =8%input=0 =7%hour<12 )  output: $olduser = 1 Good morning. $begintime = %fulltime  
		char* vverify = strstr(verifyinfo,"verify: ") + 8;
		ptr = strstr(vverify,"rule:");
		*ptr = 0; // end of verification level
		ptr += 5;
		char vtag1[MAX_WORD_SIZE];
		ptr = ReadCompiledWord(ptr,vtag1);
		ptr = strstr(ptr,"kind:")+5;
		char vkind = *ptr;
		char* vlabel = strstr(ptr,"label:") + 6;
		char* vpattern = strstr(vlabel,"pattern: ");
		*--vpattern = 0;
		vpattern += 10;
		char* equal = strchr(vtag1,'=');
		if (equal) *equal = 0;	// remove label from tag

		char* voldoutputcode = strstr(vpattern,"output: "); // what it said then.
		*--voldoutputcode = 0;
		voldoutputcode += 9;
		len = strlen(voldoutputcode);
		while (voldoutputcode[len-1] == ' ') --len;
		voldoutputcode[len] = 0;
		char* at = strchr(voldoutputcode,'`');
		if (at) *at = 0;

		bool sametag = false;
		bool sameruletype  = false;
		bool samelabel = false;;
		bool samepattern = false;;
		bool sameoutput = false;; // used same rule
		char tag[MAX_WORD_SIZE];
		int id;
		unsigned int topicid;
		char label[MAX_WORD_SIZE];
		char pattern[MAX_WORD_SIZE];
		char outputdata[MAX_WORD_SIZE];
		for (unsigned int i = 0; i < responseIndex; ++i) // use last said as topicid (we usually prefix emotions and other things)
		{
			// get actual results
			unsigned int order = responseOrder[i];
			strcpy(tag,GetTopicName(responseData[order].topic));
			strcat(tag,responseData[order].id);
			GetVerify(tag,topicid,id);
			char* rule = GetRule(topicid,id);		// the rule we want to test
			char* newoutputcode = GetPattern(rule,label,pattern);
			size_t len = strlen(newoutputcode);
			if (len > 50) len = 50;
			strncpy(outputdata,newoutputcode,len);
			while (outputdata[len-1] == ' ') --len;
			outputdata[len] = 0;
			char* close = strchr(outputdata,'`');
			if (close) *close = 0;	// end rule

			pattern[50] = 0;	 // limit it
			if (!sametag) sametag = !strnicmp(tag,vtag1,strlen(vtag1));
			if (!sameruletype) sameruletype  = vkind == *rule;
			if (!samelabel) samelabel = *label && !stricmp(label,vlabel);
			if (!samepattern) samepattern = !stricmp(pattern,vpattern);
			if (!sameoutput) sameoutput = !stricmp(outputdata,voldoutputcode); // used same rule
		}

		bool samesaid = !stricmp(oldsaid,buffer);
		if (!samesaid && strstr(oldsaid,buffer)) samesaid = true; // see if we subsume what was said
		char changes[MAX_WORD_SIZE];
		*changes = 0;
		if (!sametag) strcat(changes,"Tag, ");
		if (!sameruletype) strcat(changes,"Rule type, ");
		if (!samelabel && (*label || *vlabel)) strcat(changes,"Label, ");
		if (!samepattern) strcat(changes,"Pattern, ");
		if (!sameoutput) strcat(changes,"Output, "); // we only care if outputdata changed, not what was said which might be random
				
		ReadALine(readBuffer,in); // verify2 info
		char verify2info[MAX_WORD_SIZE];
		strcpy(verify2info,readBuffer); // copy so we can debug seeing original data
		//	verify:  rule:~hello.1.0. kind:t label: pattern: ( !$olduser =8%input=0 =7%hour<12 )  output: $olduser = 1 Good morning. $begintime = %fulltime  
		char* vverify2 = strstr(verify2info,"verify2: ") + 8;
		ptr = strstr(vverify2,"rule:");
		if (ptr) *ptr = 0; // end of verification level

		if (sametag && sameruletype && samepattern && sameoutput){;} // matches rule id, output, kind, pattern - perfect match
		else if (sameoutput || samepattern || samelabel || samesaid)  
		{
			if (!sametag && samesaid) ++minorchange;
			else if (silent) {;}
			else if (!sametag) Log(ECHOSTDUSERLOG,"        Volley %d input %s changed tag. Was: %s  is: %s\r\n",volley,vinput,vtag1,tag);
			else Log(ECHOSTDUSERLOG,"    Volley %d input %s is intact. %s changed\r\n",volley,vinput,changes);
			if (!samesaid && !silent)
			{
				Log(ECHOSTDUSERLOG,"            Old said: %s\r\n",oldsaid);
				Log(ECHOSTDUSERLOG,"            Now says: %s\r\n\r\n",buffer);
			}
			modified = true;
		}
		else 
		{
			Log(ECHOSTDUSERLOG,"*** Volley %d input %s - changed radically. old:  %s now: %s\r\n",volley,vinput, vtag1, tag);
			if (!samesaid)
			{
				if (*SkipWhitespace(vverify) || *SkipWhitespace(vverify2)) Log(ECHOSTDUSERLOG,"            Old verify: %s  +  %s\r\n",vverify,vverify2);
				Log(ECHOSTDUSERLOG,"            Old said: %s  -  %s pattern: %s",oldsaid,vlabel,vpattern);
				unsigned int oldtopic;
				int oldid;
				GetVerify(vtag1,oldtopic,oldid);
				TraceSample(oldtopic,oldid,ECHOSTDUSERLOG);
				Log(ECHOSTDUSERLOG,"\r\n");
				Log(ECHOSTDUSERLOG,"            Now says: %s   - %s pattern: %s  ",buffer,label,pattern);
				TraceSample(topicid,id,ECHOSTDUSERLOG);
				Log(ECHOSTDUSERLOG,"\r\n\r\n");
			}			
			++changed;
		}
	}
	userLog = olduserlog;
	fclose(in);
	echo = oldecho;
	prepareMode = NO_MODE;
	regression = NO_REGRESSION;
	// shall we revise the regression file?
	if (changed) Log(ECHOSTDUSERLOG,"There were %d rules which changed radically of %d inputs.\r\n",changed,count);
	if (minorchange) Log(ECHOSTDUSERLOG,"There were %d rules which changed tag.\r\n",minorchange);
			
	if (changed || modified || minorchange)
	{
		printf("\nRegression has changed. Do you want to update regression to the current results? Only \"yes\" will do so: ");
		ReadALine(readBuffer,stdin);
		if (!stricmp(readBuffer,"yes"))
		{
			char fdo[MAX_WORD_SIZE];
			sprintf(fdo,"%s/tmpregresslog.txt %s",users,file);
			MemorizeRegress(fdo);
		}
	}
	else printf("Regression passed.\r\n");
}

static void C_Regress(char* input)
{
	char word[MAX_WORD_SIZE];
	char* xxptr = ReadCompiledWord(input,word);
	if (!strnicmp(input,"init ",5)) MemorizeRegress(input+5);
	else VerifyRegress(input);
}

static void C_Source(char* input)
{
	char word[MAX_WORD_SIZE];
	char* ptr = ReadCompiledWord(input,word);
	FILE* in = FopenReadNormal(word); // source
	if (in) sourceFile = in;
	else Log(STDUSERLOG,"No such source file: %s\r\n",word);
	SetUserVariable("$$document",word);
	ReadCompiledWord(ptr,word);
	echoSource = NO_SOURCE_ECHO;
	if (!stricmp(word,"echo")) echoSource = SOURCE_ECHO_USER;
	else if (!stricmp(word,"internal"))  echoSource = SOURCE_ECHO_LOG;
	
	sourceStart = ElapsedMilliseconds();
	sourceTokens = 0;
	sourceLines = 0;
} 

static void ReadNextDocument(char* name,uint64 value) // ReadDocument(inBuffer,sourceFile) called eventually to read document
{
	FILE* in = FopenReadNormal(name); // source
	if (in) sourceFile = in;
	else 
	{
		Log(STDUSERLOG,"No such document file: %s\r\n",name);
		return;
	}
	readingDocument = true;
	SetBaseMemory();
	inputSentenceCount = 0;
	docTime = ElapsedMilliseconds();
	tokenCount = 0;
	ShowStats(true);
	SetUserVariable("$$document",name);
	if (!trace) echo = false;
	*mainOutputBuffer = 0;
	documentMode = true;
	randIndex =  oldRandIndex;
	OnceCode("$cs_control_pre","~document_pre"); // just once per document
	randIndex =  oldRandIndex;
	
	// read the file
	ProcessInputFile();
	
	if (docstats) 
	{
		bool oldecho = echo;
		echo = true;

		unsigned int diff = (unsigned int) (ElapsedMilliseconds() - docTime);
		unsigned int mspl = diff/inputSentenceCount;
		float fract = (float)(diff/1000.0); // part of seccond
		float time = (float)(tokenCount/fract);
	
		unsigned int seconds = (diff/1000);
		diff -= (seconds * diff);
		if (diff >= 500) ++seconds;
		unsigned int minutes = seconds/60;
		seconds -= (minutes * 60);
		unsigned int hours = minutes/60;
		minutes -= (hours * 60);

		Log(STDUSERLOG,"\r\nRead: %d sentences (%d tokens) in %d hours %d minutes %d seconds  %d ms/l or %f token/s\r\n",inputSentenceCount,tokenCount, hours,minutes,seconds,mspl,time);
		
		unsigned int dictUsed = dictionaryFree - dictUsedG;
		unsigned int factUsed = factFree - factUsedG;
		unsigned int textUsed = (textUsedG - stringFree) / 1000;
		uint64 dictAvail =  maxDictEntries-(dictionaryFree-dictionaryBase);
		unsigned int factAvail = factEnd-factFree;
		unsigned int textAvail = (stringFree- (char*)dictionaryFree) / 1000;
		Log(STDUSERLOG,"\r\nUsed- dict:%d fact:%d text:%dkb   Free- dict:%d fact:%d  text:%dkb\r\n",dictUsed,factUsed,textUsed,(unsigned int)dictAvail,factAvail,textAvail);

		echo = oldecho;
	}
	// do post process on document
	postProcessing = AllocateBuffer();
	FinishVolley(" ",mainOutputBuffer,"~document_post"); // per document post process and will write out stuff  and reset user memory and ...
	ReadUserData();	// read user info back in so we can continue (a form of garbage collection)
	FreeBuffer();
	postProcessing = 0;
	if (*mainOutputBuffer) printf("%s\r\n",UTF2ExtendedAscii(mainOutputBuffer));
	documentMode = false;
	readingDocument = false;
}

static void C_Document(char* input)
{
	dictUsedG = dictionaryFree; // track memory use
	factUsedG = factFree;
	textUsedG = stringFree;

	documentBuffer = AllocateBuffer() + 1; // hide a char before edge for backward testing
	*documentBuffer = 0;
	++baseBufferIndex; // system will reset  buffers each sentence to include ours
	char name[MAX_WORD_SIZE];
	char* ptr = ReadCompiledWord(input,name);
	char attrib[MAX_WORD_SIZE];
	echoSource = NO_SOURCE_ECHO;
	docstats = false;
	bool docquit = false;
	while (ptr)
	{
		ptr = ReadCompiledWord(ptr,attrib);
		if (!*attrib) break;
		if (!stricmp(attrib,"single")) singleSource = true; // one line at a time, regardless of inability to find a complete sentence
		else if (!stricmp(attrib,"echo")) docOut = FopenUTF8Write("TMP/out.txt"); // clear it
		else if (!stricmp(attrib,"stats")) docstats = true;
		else if (!stricmp(attrib,"quit")) docquit = true;
	}
	
	MemoryMarkCode(NULL);
	
	size_t len = strlen(name);
	if (name[len-1] == '/') WalkDirectory(name,ReadNextDocument, 0);
	else ReadNextDocument(name,0);
	echo = false;
	
	postProcessing = documentBuffer; // dedicate buffer to alternate use
	documentBuffer = 0;
	FinishVolley(" ",mainOutputBuffer,NULL); // bots post processing step
	FreeBuffer(); // release document buffer
	--baseBufferIndex;
	postProcessing = 0;
	
	if (docOut) // end echoing
	{
		fclose(docOut);
		docOut = NULL;
	}

	if (docquit) exit(0);
} 

static void DoAssigns(char* ptr)  // find variable assignments
{
	char var[MAX_WORD_SIZE];
	char* dollar;
	char* percent;
	char* underscore;
	char* at;
	char* first = 0;
	while (ptr) // do all user variables
	{
		at = NULL;
		char* spot = ptr;
		char* d = ptr;
		dollar = NULL;
		while ( (d = strchr(d,'$'))) // find potential variable, not money
		{
			if (IsDigit(d[1])) ++d;
			else
			{
				dollar = d;
				break;
			}
		}
		percent = strchr(ptr,'%');
		underscore = strchr(ptr,'_');
		if (dollar) at = dollar;
		else if (percent) at = percent;
		else while ((underscore = strchr(spot,'_')))  // may not be real yet, might be like New_year's_eve 
		{
			if (IsDigit(underscore[1])) 
			{
				at = underscore;
				break;
			}
			else spot = underscore + 1;
		}
		if (!at) break;
	
		if (percent && percent < at) at = percent;
		if (underscore && underscore < at) at = underscore;
		
		// at is the soonest assignment
		char* eq = strchr(at,'='); // has an assignment
		if (!eq) break; // no assignment
		char c = *eq;
		*eq-- = 0; // break off lhs
		ReadCompiledWord(at,var);
		*eq = c;  // change  $current=1  into $current = 1 moving operator and giving space after

		if (eq[2] == '=') 
		{
			eq[1] = eq[2];
			eq[2] = ' '; // 2 char operator
		}
		else eq[1] = ' '; // single char operator

		if (!first) first = at; // start of all
		FunctionResult result;
		ptr = PerformAssignment(var,eq,result);
		if (ptr) memset(at,' ',ptr-at);
	}

	// do all word memberships
	char* mem = ptr;
	while ((mem = strchr(mem,'?'))) 
	{
		if (mem[1] == '~')
		{
			char* at = mem;
			while (*--at != ' ');
			char var[MAX_WORD_SIZE];
			*mem = 0;
			ReadCompiledWord(at+1,var);
			if (!first) first = at; // end with this test
			char set[MAX_WORD_SIZE];
			ReadCompiledWord(mem+1,set);
			MEANING memx = MakeMeaning(StoreWord("member"));
			CreateFact(MakeMeaning(StoreWord(var)),memx,MakeMeaning(StoreWord(set)),FACTTRANSIENT);
			*mem = '?';
		}
		++mem;
	}
	
	if (first)  *first = 0; // remove all assignments

}

static void C_TestPattern(char* input)
{ // pattern, input, optional var assigns  -  (drink)  Do you like drink? %date = 1
#ifndef DISCARDSCRIPTCOMPILER
	if (*input != '(' && *input != '~') 
	{
		Log(STDUSERLOG,"Bad test pattern");
		return;
	}

	char data[MAX_WORD_SIZE];
	char* pack = data;
	strcpy(readBuffer,input);

	char label[MAX_WORD_SIZE];
	char* ptr = ReadCompiledWord(readBuffer,label);
	unsigned int topic = currentTopicID;
	bool fulllabel = false;
	int id = 0;
	bool crosstopic = false;
	if (*label == '~') // named an existing rule
	{
		char* rule;
		char* dot = strchr(label,'.');
		if (!dot) 
		{
			Log(STDUSERLOG," %s rule lacks dot\r\n",label);
			return;
		}
		if (dot && IsDigit(dot[1])) rule = GetRuleTag(topic,id,label);
		else rule = GetLabelledRule(topic,label,"",fulllabel,crosstopic,id,currentTopicID);
		if (!rule) 
		{
			Log(STDUSERLOG," %s rule not found\r\n",label);
			return;
		}
		GetPattern(rule,NULL,data);
	}
	else
	{
		if (setjmp(scriptJump[++jumpIndex])) // return on script compiler error
		{
			--jumpIndex;
			return;
		}
		ReadNextSystemToken(NULL,NULL,data,false,false); // flush cache
		ptr = ReadPattern(readBuffer, NULL, pack,false); // swallows the pattern
	}

	//   var assign?
	DoAssigns(ptr);
	if (!*ptr) return; //   forget example sentence

	char prepassTopic[MAX_WORD_SIZE];
	strcpy(prepassTopic,GetUserVariable("$cs_prepass"));
	PrepareSentence(ptr,true,true);	
	
	unsigned int gap = 0;
	unsigned int wildcardSelector = 0;
	wildcardIndex = 0;
	unsigned int junk1;
	int oldtrace = trace;
	trace |= TRACE_PATTERN;
	bool uppercasem = false;
	int whenmatched = 0;
	SetContext(true);
	bool result =  Match(data+2,0,0,'(',true,gap,wildcardSelector,junk1,junk1,uppercasem,whenmatched);
	SetContext(false);
	trace = oldtrace;
	if (result) 
	{
		Log(STDUSERLOG," Matched\r\n");
		if (trace & (TRACE_PATTERN|TRACE_MATCH|TRACE_SAMPLE) ) //   display the entire matching responder and maybe wildcard bindings
		{
			if (wildcardIndex)
			{
				Log(STDUSERLOG," wildcards: ");
				for (unsigned int i = 0; i < wildcardIndex; ++i)
				{
					if (*wildcardOriginalText[i]) Log(STDUSERLOG,"_%d=%s / %s ",i,wildcardOriginalText[i],wildcardCanonicalText[i]);
					else Log(STDUSERLOG,"_%d=  ",i);
				}
			}
			Log(STDUSERLOG,"\r\n");
		}
	}
	else 
	{
		Log(STDUSERLOG," Failed\r\n    Adjusted Input: ");
		for (unsigned int i = 1; i <= wordCount; ++i) Log(STDUSERLOG,"%s ",wordStarts[i]);
		Log(STDUSERLOG,"\r\n    Canonical Input: ");
		for (unsigned int i = 1; i <= wordCount; ++i) Log(STDUSERLOG,"%s ",wordCanonical[i]);
		Log(STDUSERLOG,"\r\n");
	}
	--jumpIndex;
#endif
}

static void GambitTestTopic(char* topic)
{
	int topicID = FindTopicIDByName(topic);
	if (!topicID) 
	{
		Log(STDUSERLOG,"topic not found %s\r\n",topic);
		return;
	}
	if (GetTopicFlags(topicID) & TOPIC_NOGAMBITS) return;
	int  oldRegression = regression;
	regression = NORMAL_REGRESSION;

	char* data = GetTopicData(topicID);
	char* output = AllocateBuffer();
	int ruleID = -1;
	while (data)
	{
		char* rule = data;
		++ruleID;
		int id = 0;
		data = FindNextRule(NEXTTOPLEVEL,data,id);
		if (*rule != GAMBIT && *rule != RANDOM_GAMBIT) continue; // not a gambit

		// get the output
		rule  = GetPattern(rule,NULL,NULL);
		char* end = strchr(rule,ENDUNIT);  // will not be a useful output as blanks will become underscores, but can do ^reuse() to execute it
		*end = 0;
		strcpy(output,rule);
		*end = ENDUNIT;
		char* q = strchr(output,'?');
		if (!q) continue;	 // not a question
		q[1] = 0; // ignore any following.
		char* at = q;
		while (--at > output) // is there a question before this
		{
			if ((*at == '.' || *at == '!') && at[1] == ' ') break;// end of a sentence?
		}
		if (at != output) output = at+1;

		//  perform varible setup, do assigns, and prepare matching context
		ResetToPreUser();
		KillShare();
		ReadNewUser();   
		char prepassTopic[MAX_WORD_SIZE];
		strcpy(prepassTopic,GetUserVariable("$cs_prepass"));
		volleyCount = 1;
		strcpy(currentInput,output);	//   this is what we respond to, literally.
		nextInput = output;
		OnceCode("$cs_control_pre");
		while (ALWAYS)
		{
			PrepareSentence(output,true,true);
			if (!PrepassSentence(prepassTopic)) break;
		}
		AddPendingTopic(topicID); // ResetToPreUser clears pendingTopicIndex
		responseIndex = 0;
		Reply();
		if (pendingTopicIndex && pendingTopicList[pendingTopicIndex-1] == (unsigned int) topicID){;}
		else if (!responseIndex || responseData[0].topic != (unsigned int)topicID )
		{
			Log(STDUSERTABLOG,"Not answering own question in topic %d %s.%d.%d: %s => %s %s \r\n\r\n",++err,topic,TOPLEVELID(ruleID),REJOINDERID(ruleID),output,GetTopicName(responseData[0].topic),responseData[0].response);
		}
	}
	FreeBuffer();
	regression = oldRegression;
}

static void C_TestTopic(char* input)
{
	char word[MAX_WORD_SIZE];
	input = ReadCompiledWord(input,word);
	char prepassTopic[MAX_WORD_SIZE];
	strcpy(prepassTopic,GetUserVariable("$cs_prepass"));
	while (ALWAYS)
	{
		PrepareSentence(nextInput,true,true);	
		if (!PrepassSentence(prepassTopic)) break;
	}
	unsigned int topic = FindTopicIDByName(word);
	if (!topic)  return;
	int pushed =  PushTopic(topic); 
	if (pushed < 0) return;
	ClearUserVariableSetFlags();
	AllocateOutputBuffer();
	PerformTopic(0,currentOutputBase); //   ACTIVE handle - 0 is good result
	FreeOutputBuffer();
	for (unsigned int i = 0; i < responseIndex; ++i) Log(STDUSERLOG,"%s\r\n", responseData[responseOrder[i]].response);
	ShowChangedVariables();
}

static void VerifyAccess(char* topic,char kind,char* prepassTopic) // prove patterns match comment example, kind is o for outside, r for rule, t for topic, s for samples
{
	bool testKeyword = kind == 'k';
	bool testPattern = kind == 'p' ;
	bool testBlocking = kind == 'b';
	bool testSample = kind == 's' || kind == 'S' ;
	if (kind == 'a' || !kind) testKeyword = testPattern = testBlocking =  true;
 	unsigned int topicID = FindTopicIDByName(topic,true);
	if (!topicID) 
	{
		printf("%s not found\r\n",topic);
		return;
	}
	WORDP topicWord = FindWord(GetTopicName(topicID)); // must find it
	topic = topicWord->word;
	
	int flags = GetTopicFlags(topicID);
	if (flags & TOPIC_BLOCKED) return;

	if (testKeyword) 	// has no keyword into here so dont test keyword access
	{
		FACT* F = GetObjectNondeadHead(topicWord);
		while (F)
		{
			if (F->verb == Mmember) break; 
			F = GetObjectNondeadNext(F);
		}
		if (!F)  testKeyword = false;
	}

	if (GetTopicFlags(topicID) & (TOPIC_RANDOM|TOPIC_NOBLOCKING)) testBlocking = false;	
	if (GetTopicFlags(topicID) & (TOPIC_RANDOM|TOPIC_NOKEYS)) testKeyword = false;	
	if (GetTopicFlags(topicID) & TOPIC_NOPATTERNS) testPattern = false;	
	if (GetTopicFlags(topicID) & TOPIC_NOSAMPLES) testSample = false;	
	
	WORDP D = FindWord(topic);
	char c = (D->internalBits & BUILD0) ? '0' : '1'; 
	char name[100];
	char* tname = (*topic == '~') ? (topic + 1) : topic;
	if (duplicateCount) sprintf(name,"VERIFY/%s-b%c.%d.txt",tname,duplicateCount,c);
	else sprintf(name,"VERIFY/%s-b%c.txt",tname,c);
	FILE* in = FopenReadWritten(name);
	if (!in) 
	{
		printf("No %s verification data\r\n",name);
		return;
	}

	unsigned int oldtrace = trace;
	trace = 0;
	Log(STDUSERLOG,"VERIFYING %s ......\r\n",topic);
	char* copyBuffer = AllocateBuffer();
	char junk[MAX_WORD_SIZE];
	// process verification data
	while (ReadALine(readBuffer,in) >= 0)
	{
		if (bufferIndex > 6) return;

		if (!strnicmp(readBuffer,":trace",10))
		{
			trace = atoi(readBuffer+11);
			continue;
		}
		if (!strnicmp(readBuffer,":exit",5)) myexit(":exit requested");
		bool failTest = false;
	
		// read tag of rule to apply input to
		int verifyRuleID;
		char* dot = GetRuleIDFromText(readBuffer,verifyRuleID);
		if (!dot) return;
		char* rule = GetRule(topicID,verifyRuleID);					// the rule we want to test
		char* topLevelRule = GetRule(topicID,TOPLEVELID(verifyRuleID));	// the top level rule (if a rejoinder)
		char* rejoinderTop = NULL;
		int rejoinderTopID = 0;
		if (!rule) 
			break;
		if (rule && rule != topLevelRule) // its a rejoinder, find the start of the rejoinder area
		{
			rejoinderTop = topLevelRule;  // the limit of backward checking
			char* at = rule; // start at the given rejoinder
			rejoinderTopID = verifyRuleID;
			while (*at >= *rule && REJOINDERID(rejoinderTopID)) // stop if drop below our level or go to top level rule
			{
				at = RuleBefore(topicID,at);
				rejoinderTopID -= ONE_REJOINDER;
			}
			rejoinderTopID += ONE_REJOINDER; // now move back down to 1st of our level
			rejoinderTop = FindNextRule(NEXTRULE,at,rejoinderTopID);
		}

		// the comment headers are:
		// #!x  - description header for :abstract
		// #!!F  - expect to fail RULE
		// #!!T - expect to fail TOPIC (be masked by earlier rule)
		// #!!P - dont test patterns
		// #!!K - dont test keywords
		// #!!S - dont run sample
		*junk = junk[1] = junk[2] = 0;
		char* test = strchr(readBuffer,'!')+1;	// the input sentence (skipping offset and #! marker)
		if (*test != ' ') test = ReadCompiledWord(test,junk); // things to not test
		MakeLowerCase(junk);
		if (*junk == 'x') continue;  // only used for :abstract

		bool wantFailBlocking = false;
		bool wantFailKeyword = false;
		bool wantNoPattern = false;
		bool wantNoSample = false;
		bool wantFailMatch = false;
		// SUPPRESS testing this rule for this
		if (strchr(junk,'b') || strchr(junk,'B')) wantNoSample = wantFailBlocking = true;
		if (strchr(junk,'k') || strchr(junk,'K')) wantNoSample = wantFailKeyword = true;
		if (strchr(junk,'s') || strchr(junk,'S')) wantNoSample = true;
		if (strchr(junk,'p') || strchr(junk,'P')) wantNoPattern = true;

		if (strchr(junk,'f') || strchr(junk,'F')) wantFailMatch = true;

		//   test pattern on THIS rule

		//  perform varible setup, do assigns, and prepare matching context
		ResetToPreUser();
		KillShare();
		ReadNewUser();   
		if (verifyToken != 0) tokenControl = verifyToken;
		volleyCount = 1;
		if (testSample) OnceCode("$cs_control_pre");

		DefineSystemVariables(); // clear system variables to default
		DoAssigns(test); // kills test start where any defines are
		strcpy(copyBuffer,test);
		strcpy(currentInput,test);	//   this is what we respond to, literally.
		nextInput = test;
		while (ALWAYS)
		{
			PrepareSentence(nextInput,true,true);
			if (!PrepassSentence(prepassTopic)) break;
		}
		currentTopicID = topicID;
		strcpy(test,copyBuffer); // sentence prep may have altered test data and we might want to redo it
		AddPendingTopic(topicID); // ResetToPreUser clears pendingTopicIndex

		char label[MAX_WORD_SIZE];
		char pattern[MAX_WORD_SIZE];
		char* topLevelOutput = GetOutputCopy(topLevelRule); 
		GetPattern(rule,label,pattern);
		if (!*pattern) 
		{
			ReportBug("No pattern here? %s %s\r\n",topic,rule)
			continue;
		}

		bool result;
		if (testKeyword && !wantFailKeyword &&  !TopLevelGambit(rule) &&  TopLevelRule(rule) )  // perform keyword test on sample input sentence
		{
			unsigned int pStart = 0;
			unsigned int pEnd = 0;
			if (!GetNextSpot(topicWord,0,pStart,pEnd)) // not findable topic
			{
				Query("direct_v","?","idiom",topic,(unsigned int)-1,"?","?","?","?");  // get all idioms that can trigger this topic
				unsigned int i = FACTSET_COUNT(0);
				while (i > 0)
				{
					FACT* F = factSet[0][i];
					WORDP pattern = Meaning2Word(F->subject);
					strcpy(callArgumentList[callArgumentBase+1],pattern->word);
					*callArgumentList[callArgumentBase+2] = 0; // dumy argument 1
					if (MatchCode(junk) == 0) break;
					--i;
				}

				if ( i == 0) 
				{
					Log(STDUSERTABLOG,"%d Missing keyword %s.%d.%d <= %s\r\n",++err,topic,TOPLEVELID(verifyRuleID),REJOINDERID(verifyRuleID),test);
					failTest = true;
				}
			}
		}

		//   inside the pattern, test this rule
		if (testPattern && !wantNoPattern) // not blocking pattern testing
		{
			++trials;
			if (*rule == '?' && !(tokenFlags & QUESTIONMARK)) result = 0; // cannot match
			else if (*rule == 's' && tokenFlags & QUESTIONMARK) result = 0; // cannot match
			else 
			{
				SetContext(true); // force all contexts to be valid
				result = RuleTest(rule);
				SetContext(false);
			}
			bool unexpected = (!result && !wantFailMatch) || (result && wantFailMatch);
			if (unexpected )
			{
				char label[MAX_WORD_SIZE];
				GetLabel(rule, label);
				if (wantFailMatch) Log(STDUSERTABLOG,"Pattern matched inappropriately %d %s.%d.%d: %s => %c: %s %s\r\n    Adjusted Input: ",++err,topic,TOPLEVELID(verifyRuleID),REJOINDERID(verifyRuleID),test,*rule,label,pattern);
				else Log(STDUSERTABLOG,"Pattern failed to match %d %s.%d.%d: %s => %c: %s %s\r\n    Adjusted Input: ",++err,topic,TOPLEVELID(verifyRuleID),REJOINDERID(verifyRuleID),test,*rule,label,pattern);
				for (unsigned int i = 1; i <= wordCount; ++i) Log(STDUSERLOG,"%s ",wordStarts[i]);
				Log(STDUSERLOG,"\r\n    Canonical Input: ");
				for (unsigned int i = 1; i <= wordCount; ++i) Log(STDUSERLOG,"%s ",wordCanonical[i]);
				Log(STDUSERLOG,"\r\n\r\n");
				failTest = true;
	
				// redo with tracing on if selected so we can watch it fail
				if (oldtrace)
				{
					trace = oldtrace;
					nextInput = test;
					while (ALWAYS)
					{
						PrepareSentence(nextInput,true,true);	
						if (!PrepassSentence(prepassTopic)) break; // user input revise and resubmit?  -- COULD generate output and set rejoinders
					}
					strcpy(test,copyBuffer); // sentence prep may have altered test data and we might want to redo it
					SetContext(true);
					RuleTest(rule);
					SetContext(false);
					trace = 0;
					Log(STDUSERTABLOG, "\r\n:testpattern %s %s\r \n \r\n", pattern, test);				
				}
				continue;
			}
		}
		
		if (testBlocking && !wantFailBlocking  && !TopLevelGambit(rule)) // check for blocking
		{
			char* data;
			char* output = NULL;
			int id = 0;
			if (TopLevelRule(rule)) // test all top level rules in topic BEFORE this one
			{
				data = GetTopicData(topicID);
				char label[MAX_WORD_SIZE];
				char pattern[MAX_WORD_SIZE];
				while (data && data < rule)
				{
					if (*data == GAMBIT || *data == RANDOM_GAMBIT); // no data gambits
					else if (*rule == STATEMENT && *data == QUESTION); // no mismatch type
					else if (*rule == QUESTION && *data == STATEMENT); // no mismatch type
					else 
					{
						output = GetPattern(data,label,pattern);
						if (!*pattern) break; 
						bool result;
						uint64 oldflags = tokenFlags;
						SetContext(true);
						//if (*rule == STATEMENT) tokenFlags &= -1 ^ QUESTIONMARK; // cant be question
						//else if (*rule == QUESTION) tokenFlags |= -QUESTIONMARK; // can be question
						if (pattern[2] == ')' || pattern[2] == '*') result =  false; // universal match patterns are PRESUMED not to be blocking. they obviously obscure anything
						else result = RuleTest(data);// past the paren
						SetContext(false);
						if (result)	break; // he matched, blocking us
						tokenFlags = oldflags;
					}
					data = FindNextRule(NEXTTOPLEVEL,data,id);
				}
			}
			else  // rejoinder matching 
			{
				data = rejoinderTop;
				id = rejoinderTopID;
				while (data < rule)
				{
					if (*data == *rule)// all rules of this same level and before us
					{
						SetContext(true);
						bool result = RuleTest(data); // past the paren
						SetContext(false);
						if (result)	break; // he matched, blocking us
					}
					data = FindNextRule(NEXTRULE,data,id);
				}
			}

			if (data && data < rule && !strstr(data,"^incontext")) // earlier rule matches same pattern and is not context sensitive
			{
				// prove not a simple () (*) (!?)  (?) etc
				char* t = pattern+2; // start AFTER the ( 
				while (ALWAYS)
				{
					t = ReadCompiledWord(t,junk);
					if (!stricmp(junk,"!") || !stricmp(junk,"*") || !stricmp(junk,"?")) continue;
					break;
				}
				if (*junk == 0 || *junk == ')') continue;	// presumed end of pattern

				// prove it may output something - all matching rejoinders automatically mask if occur sooner
				if (!Rejoinder(data)) // top level units that dont generate output dont actually mask.
				{
					char word[MAX_WORD_SIZE];
					while (*output && *output != ENDUNIT)
					{
						output = ReadCompiledWord(output,word);
						if ((IsAlphaUTF8(*word) ) && FindWord(word)) 
							break; // possible problem
					}
				}
				if (!output || *output == ENDUNIT) continue;	// no text output found

				if (REJOINDERID(id)) Log(STDUSERTABLOG,"Blocking %d Rejoinder %d.%d ",++err,TOPLEVELID(id),REJOINDERID(id));
				else  Log(STDUSERTABLOG,"Blocking %d TopLevel %d.%d ",++err,TOPLEVELID(id),REJOINDERID(id));
				TraceSample(topicID,id,STDUSERTABLOG);
				Log(STDUSERLOG,"   %s\r\n",ShowRule(data));
				Log(STDUSERTABLOG,"    blocks %d.%d %s\r\n    given: %s\r\n\r\n",TOPLEVELID(verifyRuleID),REJOINDERID(verifyRuleID),ShowRule(rule),test);
				failTest = true;
			}
		}
		if (testSample && !wantNoSample && !failTest  && TopLevelRule(rule)) // check for sample
		{
			// force bot restriction match
			char oldcomputer[MAX_WORD_SIZE];
			strcpy(oldcomputer,computerIDwSpace);
			if (TI(topicID)->topicRestriction)
			{
				strcpy(computerIDwSpace,TI(topicID)->topicRestriction);
				char* space = strchr(computerIDwSpace+3,' ');
				space[1] = 0;
			}

			// prepare for contextfree start
			ClearPendingTopics();
			responseIndex = 0;
			currentTopicID = 0;
			topicIndex = 0;
			outputRejoinderTopic = NO_REJOINDER;
			if (oldtrace) trace = oldtrace;

			sampleTopic = topicID;
			sampleRule = verifyRuleID;
			Reply();
			bool foundSample = sampleTopic == 0;	// it was found and canceled.
			sampleTopic = sampleRule  = 0;
	
			trace = 0;		
			if (foundSample){;}
			else if (!responseIndex || responseData[0].topic != topicID)
			{
				bool bad = true;
				char* end = strchr(rule,ENDUNIT);
				if (end) *end = 0;
				if (strstr(rule,"^gambit")) // we dont expect it to answer in this topic unless '~' is argument
				{
					char * at = strstr(rule,"^gambit ( ") + 10;
					if (at[0] == '~' && at[1] == ' ') bad = false;
				} 
				else if (strstr(rule,"^respond") || strstr(rule,"^end") || strstr(rule,"^fail")) bad = false; // we dont expect it to answer here
				else if (strstr(rule,"^reuse"))
				{
					char * at = strstr(rule,"^reuse");
					char* paren = strchr(at,')');
					*paren = 0;
					if (strchr(at,'.')) bad = false; // we dont expect it to answer here
					*paren = ')';
				}
				if (bad) 
				{
					int gotid;
					char* junk = GetRuleIDFromText(responseData[0].id,gotid);
					unsigned int replytopic = responseData[0].topic;
					char gotrule[300];
					strcpy(gotrule,ShowRule(GetRule(replytopic,gotid)));

					// via info
					unsigned int replytopic2 = 0;
					int gotid2 = 0;
					char* gotrule2 = NULL;
					if (*junk)
					{
						replytopic2 = atoi(junk+1);
						GetRuleIDFromText(junk+1,gotid2);
						gotrule2 = ShowRule(GetRule(replytopic2,gotid2));
					}

					char wantrule[MAX_WORD_SIZE];
					strcpy(wantrule,ShowRule(rule));
					Log(STDUSERTABLOG,"Bad sample topic: %d  (%s.%d.%d)   %s  =>   %s  (%s) \r\n   want: : %s\r\n    got: %s%s\r\n",++err,topic,TOPLEVELID(verifyRuleID),REJOINDERID(verifyRuleID),test,responseData[0].response,GetTopicName(replytopic),wantrule,
						responseData[0].id,gotrule);
					if (gotrule2) Log(STDUSERTABLOG,"    via %s.%d.%d: %s" ,GetTopicName(replytopic2),TOPLEVELID(gotid2),REJOINDERID(gotid2),gotrule2);
					Log(STDUSERLOG,"\r\n\r\n");
				}
				if (end) *end = ENDUNIT;
			}
			else if (kind != 'S') // also check rule bad - topic was same but might be gambit or reuse
			{
				int id;
				char* after = GetRuleIDFromText(responseData[0].id,id);
				int reuseid = -1;
				if (*after == '.') // there is redirect rule leading to us
				{
					GetRuleIDFromText(after+1,reuseid);
				}
				if (id == verifyRuleID || (reuseid >= 0 && TOPLEVELID(reuseid) == (unsigned int) verifyRuleID)) {;} // we match
				else if (TOPLEVELID(id) == (unsigned int) verifyRuleID && !strstr(topLevelOutput,"refine")) {;} // we matched top level and are not looking for refinement
				else
				{
					char* gotrule = GetRule(topicID,id);
					char* end = strchr(rule,ENDUNIT);
					bool bad = true;
					*end = 0; // limit rule to this one only

					// via info
					unsigned int replytopic2 = 0;
					int gotid2 = 0;
					char gotrule2[300];
					*gotrule2 = 0;
					if (*after)
					{
						replytopic2 = atoi(after+1);
						GetRuleIDFromText(after+1,gotid2);
						strcpy(gotrule2,ShowRule(GetRule(replytopic2,gotid2)));
					}

					if (strstr(rule,"^gambit")) bad = false; // we dont expect it to answer here
					else if (strstr(rule,"^respond")) bad = false; // we dont expect it to answer here
					else if (strstr(rule,"^reuse")) // we dont expect it to answer here but we should have run label
					{
						char label[MAX_WORD_SIZE];
						GetLabel(gotrule,label);
						char want[MAX_WORD_SIZE];
						char* at = strstr(rule,"^reuse ( ")+9;
						ReadCompiledWord(at,want);
						if (!strcmp(want,label)) bad = false;
					} 
					else if (strstr(rule,"^fail") || strstr(rule,"^end")) bad = false; // we dont expect it to answer here
					if (bad)
					{
						char tmp[MAX_WORD_SIZE];
						strcpy(tmp,ShowRule(rule));
						Log(STDUSERTABLOG,"Bad sample rule %d %s  For: %s \r\n   want- %d.%d %s\n   got - %s => %s",++err,topic,test,
							TOPLEVELID(verifyRuleID),REJOINDERID(verifyRuleID),tmp,
							responseData[0].id+1,ShowRule(gotrule));
						if (*gotrule2) Log(STDUSERLOG,"\n   via %s.%d.%d: %s" ,GetTopicName(replytopic2),TOPLEVELID(gotid2),REJOINDERID(gotid2),gotrule2);
							Log(STDUSERLOG,"\r\n\r\n");
					}
					*end = ENDUNIT;
				}
			}
			strcpy(computerIDwSpace,oldcomputer);
		}
	}
	fclose(in);
	RemovePendingTopic(topicID);
	FreeBuffer(); // copyBuffer
	trace = oldtrace;
}

static void VerifyAllTopics(char kind,char* prepassTopic,char* topic)
{
	size_t len = 0;
	char* x = strchr(topic,'*');
	if (x) len = x - topic ;
	for (unsigned int i = 1; i <= numberOfTopics; ++i) 
	{
		if (!*GetTopicName(i)) continue;
		if (len && strnicmp(GetTopicName(i),topic,len)) continue;
		VerifyAccess(GetTopicName(i),kind,prepassTopic);
	}
}

static void AllGambitTests(char* topic)
{
	size_t len = 0;
	char* x = strchr(topic,'*');
	if (x) len = x - topic;
	for (unsigned int i = 1; i <= numberOfTopics; ++i) 
	{
		if (!*GetTopicName(i)) continue;
		if (len && strnicmp(GetTopicName(i),topic,len)) continue;
		GambitTestTopic(GetTopicName(i));
	}
}

static void C_Verify(char* input)
{
	char word[MAX_WORD_SIZE];
	char topic[MAX_WORD_SIZE];
	char tokens[MAX_WORD_SIZE];
	trials = 0;
	*topic = 0;
	err = 0;
	char* ptr = SkipWhitespace(input);
	// :verify    or    :verify blocking   or  :verify blocking ~family   or  :verify ~family or :verify sample
	if (*ptr == '$') // tokenize this way
	{
		ptr = ReadCompiledWord(ptr,tokens);
		char* value  = GetUserVariable(tokens);
		int64 flags = 0;
		ReadInt64(value,flags);
		verifyToken = flags;
	}
	else verifyToken = 0; // we dont believe this.
	if (*ptr == '~') ptr = ReadCompiledWord(ptr,topic);  // topic specifier given
	char type = 0;
	while (ptr && *ptr)
	{
		ptr = ReadCompiledWord(ptr,word);
		if (!strnicmp(word,"pattern",7)) type = 'p';
		else if (!stricmp(word,"all")) type = 'a';
		else if (!strnicmp(word,"gambit",6)) type = 'g';
		else if (!strnicmp(word,"block",5))  type = 'b';
		else if (!strnicmp(word,"keyword",7)) type = 'k';
		else if (!strnicmp(word,"sample",6))
		{
			if (!strnicmp(word,"sampletopic",11)) type = 'S'; // bad topic only
			else type = 's'; // bad topics and rules
		}
		else if (!*topic) // topic name given without ~
		{
			topic[0] = '~';
			strcpy(topic+1,word);
		}
	}
	
	if (type != 'g')
	{
		char prepassTopic[MAX_WORD_SIZE];
		strcpy(prepassTopic,GetUserVariable("$cs_prepass"));
		if (*topic == '~' && !strchr(topic,'*')) VerifyAccess(topic,type,prepassTopic);
		else VerifyAllTopics(type,prepassTopic,topic);
	}

	// now do gambit tests
	if (type == 'g' || type == 'a')
	{
		if (*topic == '~'  && !strchr(topic,'*')) GambitTestTopic(topic);
		else AllGambitTests(topic);
	}
	Log(STDUSERLOG,"%d verify findings of %d trials.\r\n",err,trials);
	ResetToPreUser();
}

bool stanfordParser = false;

static void PennWrite(char* name,uint64 flags)
{
	FILE* out = (FILE*)flags;
	FILE* in = fopen(name,"rb");
	if (!in) 
	{
		printf("missing %s\r\n",name);
		return;
	}
	bool content = false;
	char* buffer = AllocateBuffer();
	*buffer = 0;
	char* ptr = buffer;
	bool pendingDone = false;
	bool openQuote = false;
	while (ReadALine(readBuffer,in,maxBufferSize,true) >= 0) // read lines, returning empties as well
	{
		char word[MAX_WORD_SIZE];
		ReadCompiledWord(readBuffer,word);
		if (!*word && !stanfordParser) // empty line always separates sentences from Pennbank
		{
			if (content)
			{
				*ptr = 0;
				fprintf(out,"%s\r\n",buffer);
				ptr = buffer;
				*ptr = 0;
				content = false;
			}
			continue;
		}
		char* at = readBuffer;
		while (at && *at)
		{
			at = ReadCompiledWord(at,word);
			if (pendingDone) // saw a closing, aim to close it if not quote close
			{
				if (*word == '\'' && word[1] == '\'' && word[2] == '/' && openQuote) // close quote 
				{
					strcpy(word,"\"/\"");
					openQuote = false;
					strcat(ptr,word);
					ptr += strlen(ptr);
					strcat(ptr," ");
					++ptr;
					*word = 0;
				}	

				*ptr = 0;
				fprintf(out,"%s\r\n",buffer);
				ptr = buffer;
				*ptr = 0;
				content = false;
				pendingDone = false;
				if (!*word) continue; // closed quote around this
			}

			if (*word == '`' && word[1] == '`' && word[2] == '/') // open quote 
			{
				strcpy(word,"\"/\"");
				openQuote = true;
			}
			if (*word == '\'' && word[1] == '\'' && word[2] == '/') // close quote 
			{
				strcpy(word,"\"/\"");
				openQuote = false;
			}			
			if (*word == '[' || *word == ']') continue;	// ignore this
			if (*word == '=' && word[1] == '=') // ignore ======================================
			{
				if (content)
				{
					*ptr = 0;
					fprintf(out,"%s\r\n",buffer);
					ptr = buffer;
					*ptr = 0;
					content = false;
				}
				continue; 
			}
			strcat(ptr,word);
			ptr += strlen(ptr);
			strcat(ptr," ");
			++ptr;

			if (!content && !stanfordParser)
			{
				if (IsLowerCase(*word)) Log(STDUSERLOG,"LOWER START? %s in %s \r\n",readBuffer,name);
			}
			content = true;

			if (stanfordParser && (*word == '.' || *word == '?' || *word == '!')) // sentences using stanford parser will end with punctuation UNLESS have quote after that
			{
				pendingDone = true;
			}
		}
	}
	if (content)
	{
		*ptr = 0;
		fprintf(out,"%s\r\n",buffer);
	}
	fclose(in);
	FreeBuffer();
}

static void C_PennFormat(char* file)
{
	char indir[MAX_WORD_SIZE];
	file = ReadCompiledWord(file,indir); // where source is
	char word[MAX_WORD_SIZE];
	file = ReadCompiledWord(file,word); // where source is
	char outfile[MAX_WORD_SIZE];
	sprintf(outfile,"REGRESS/PENNTAGS/%s.txt",word); // where output is

	if (!strnicmp(file,"stanford",4)) stanfordParser = true; // sentences end with . or ! or ?
	FILE* out = FopenUTF8Write(outfile);
	if (!out) return;
	WalkDirectory(indir,PennWrite,(uint64)out);
	fclose(out);
}

static void ShowFailCount(WORDP D,uint64 junk)
{
	if (!(D->internalBits & DELETED_MARK)) return;
	Log(STDUSERLOG,"%s:%d  ",D->word,D->w.planArgCount);
	D->internalBits ^= DELETED_MARK;
	D->w.planArgCount = 0;
}

static void C_PennMatch(char* file)
{
	char word[MAX_WORD_SIZE];
	bool raw = false;
	bool ambig = false;
	bool showUsed = false;
	unsigned int ambigLocation = 0;
	char filename[MAX_WORD_SIZE];
	strcpy(filename,"REGRESS/PENNTAGS/penn.txt");
	clock_t startTime = ElapsedMilliseconds(); 
	int sentenceLengthLimit = 0;
	usedTrace = AllocateBuffer();
	unsigned int line = 0;
	bool reveal = false;

reloop:
	FILE* in = FopenReadOnly(filename); // REGRESS/PENNTAGS/
	if (!in) 
	{
		Log(STDUSERLOG,"No such file %s\r\n",filename);
		return;
	}
	while (*file) // " ambig 1"  or "raw -10" limit to 10 length  or "raw 15 to do sentence 15"
	{
		file = ReadCompiledWord(file,word);
		if (!stricmp(word,"raw")) raw = true; // original rule-based pos results not lost anything?
		else if (!stricmp(word,"ambig")) ambig = true; // show ambiguous sentences  - ambig 3
		else if (!stricmp(word,"show")) 
		{
			showUsed = true; // show sentences where rule matched badly
			echo = true;
			raw = true;
		}
		else if (!stricmp(word,"reveal")) 
		{
			reveal = true; // show sentences where rule matched
			echo = true;
			raw = true;
		}
		else if (!stricmp(word,"rule"))
		{
			raw = true;
			ignoreRule = 0;
		}
		else if (IsDigit(*word) || *word == '-') 
		{
			unsigned int x;
			ReadInt(word,x);
			if (ambig) ambigLocation = (int)x;
			else sentenceLengthLimit = (int) x;
			if (sentenceLengthLimit > 0)
			{
				line = sentenceLengthLimit;
				sentenceLengthLimit = 0;
				trace = (unsigned int)-1;
				echo = true;
			}
			else sentenceLengthLimit = - sentenceLengthLimit;
		}
		else sprintf(filename,"REGRESS/PENNTAGS/%s.txt",word);
	}

	char* buffer = AllocateBuffer();
	char tags[MAX_SENTENCE_LENGTH][20];
	char tokens[MAX_SENTENCE_LENGTH][100];
	char mytags[MAX_SENTENCE_LENGTH][200];
	char prior[MAX_WORD_SIZE];
	unsigned int len;
	unsigned int right = 0;
	unsigned int total = 0;
	unsigned int sentences = 0;
	quotationInProgress = 0;	
	prepareMode = PENN_MODE;
	unsigned int totalAmbigs = 0;
	unsigned int ambigItems = 0;
	unsigned int parseOK = 0;
	unsigned int parseBad = 0;
	unsigned int ambigSentences = 0;

	ReturnToFreeze();
	StoreWord("NN");
	StoreWord("NNS");
	StoreWord("NNP");
	StoreWord("NNPS");
	StoreWord("IN ",AS_IS);
	StoreWord("PDT");
	StoreWord("POS");
	StoreWord("CC");
	StoreWord("JJ");
	StoreWord("JJR");
	StoreWord("JJS");
	StoreWord("RB");
	StoreWord("RBR");
	StoreWord("RBS");
	StoreWord("MD");
	StoreWord("RP");
	StoreWord("DT");
	StoreWord("PRP$");
	StoreWord("PRP");
	StoreWord("VB");
	StoreWord("VBD");
	StoreWord("VBG");
	StoreWord("VBN");
	StoreWord("VBP");
	StoreWord("VBZ");
	StoreWord("WDT");
	StoreWord("WP");
	StoreWord("WP$");
	StoreWord("WRB");
	StoreWord("CD");
	StoreWord("EX");
	StoreWord("FW");

	FreezeBasicData();
	ambiguousWords = 0;

	FILE* oldin = NULL;

	while (ReadALine(readBuffer,in)  >= 0 || oldin)
	{
		if (!*readBuffer && !readBuffer[2]) // continue from nested call
		{
			fclose(in);
			in = oldin;
			oldin = NULL;
			continue;
		}
		if (line && currentFileLine != line) continue;
		*usedTrace = 0;
		usedWordIndex = 0;

		char* at = buffer;
		*at = 0;
		char word[MAX_WORD_SIZE];
		char* ptr = SkipWhitespace(readBuffer);
		if (!*ptr || *ptr == '#') continue;
		if (!strnicmp(ptr,":exit",5)) break;
		if (!strnicmp(ptr,":include ",8))
		{
			if (oldin) 
			{
				Log(STDUSERLOG,"Bad include");
				return;
			}
			oldin = in;
			in = FopenReadOnly(ptr+9);  // :include
			if (!in) 
			{
				Log(STDUSERLOG,"include failed %s\r\n",ptr+9);
				in = oldin;
				oldin = NULL;
			}
			continue;
		}
		if (*ptr == ':') 
		{
			char output[MAX_WORD_SIZE];
			DoCommand(ptr,output);
			continue;
		}
		len = 0;
		int matchedquote = 0;
		bool first = true;
		char* original = ptr;
		while (ptr && *ptr)
		{
			ptr = ReadCompiledWord(ptr,word);
			if (!*word) break;
			char* sep = strrchr(word,'/'); // find last one (there might be \/  when they actually want token
			if (!sep)
			{
				printf("Failed %s\r\n",readBuffer);
				break;
			}
			*sep = 0;
			++len;

			// recode \/ and its ilk
			char word1[MAX_WORD_SIZE];
			strcpy(word1,word);
			char* sep1;
			while ((sep1 = strchr(word1,'\\'))) memmove(sep1,sep1+1,strlen(sep1)+1);

			strcpy(tokens[len],word1);
			if (!stricmp(word1,"'s") && !stricmp("POS",sep+1) && *(at-1) == ' ') *--at = 0;// possessive vs 's as "is"
			
			if (!stricmp(word1,"-LRB-")) strcat(at,"(");
			else if (!stricmp(word1,"-RRB-")) strcat(at,")");
			else if (!stricmp(word1,"-LSB-")) strcat(at,"[");
			else if (!stricmp(word1,"-RSB-")) strcat(at,"]");
			else if (!stricmp(word1,"-LCB-")) strcat(at,"{");
			else if (!stricmp(word1,"-RCB-")) strcat(at,"}");
			else if (*word1 == '`' && word1[1] == '`') 
			{
				strcat(at,"\"");  // open quote
				matchedquote |= 1;
			}
			else if (*word1 == '\'' && word1[1] == '\'') 
			{
				if (first) 
					Log(STDUSERLOG,"Closing quote at start: %d %s \r\n",currentFileLine,original);
				strcat(at,"\""); // close quote
				matchedquote |= 2;
			}
			else strcat(at,word1);

			at += strlen(at);
			strcat(at++," ");
			strcpy(tags[len],sep+1); // what we expect
			first = false;
		}
		if (matchedquote == 1 && !showUsed)
		{
	//		Log(STDUSERLOG,"No closing quote: %d %s \r\n",currentFileLine,buffer);
		}
		if (matchedquote == 2 && !showUsed)
		{
		//	Log(STDUSERLOG,"No opening quote: %d %s \r\n",currentFileLine,buffer);
		}
		if (len == 0) continue; // on to next
		*at = 0;

		// test this sentence
		char* answer1;
		tokenControl = STRICT_CASING | DO_ESSENTIALS | DO_POSTAG | DO_CONTRACTIONS | NO_HYPHEN_END | NO_COLON_END | NO_SEMICOLON_END | TOKEN_AS_IS;
		if (!raw && !ambig && !showUsed) tokenControl |= DO_PARSE;
		ReturnToFreeze();
		PrepareSentence(buffer,true,true);	
		if (sentenceLengthLimit && wordCount != sentenceLengthLimit) continue; // looking for easy sentences to fix
		unsigned int actualLen = len;
		if (*tags[len] == '.' || *tags[len] == '?' || *tags[len] == '!') 
		{
			++right;  // end punctuation is always right
			--actualLen;
		}
		total += len;
		++sentences;
		answer1 = DumpAnalysis(1,wordCount,posValues,"Tagged POS",false,true); // to debug at
		bool bad;
		if (!showUsed) for (unsigned int i = 1; i <= wordCount; ++i) 
		{
			int loc = i;
			if (i == 1 && *wordStarts[i] == '"') ++loc; // ignore quote
			bad = false;
			if (bitCounts[i] != 1) 
			{
				bad = true;
				totalAmbigs += bitCounts[i]; // total ambiguity choices
				++ambigItems;
			}
			if (ambig && bad && (!ambigLocation || loc == ambigLocation) ) 
				Log(STDUSERLOG,"** AMBIG %d: line: %d %s\r\n",++ambigSentences,currentFileLine,answer1);
		}

		char* xxhold = answer1; // for debugging
		char* answer2 = strchr(answer1,':') + 1;
		unsigned int a = 0;
		while (answer2 && *answer2)
		{
			char* close = strstr(answer2,")  ");
			if (!close) break;
			close[1] = 0;
			strcpy(mytags[++a],answer2);
			close[1] =  ' ';
			answer2 = close+3;
		}
		if (answer1) strcpy(mytags[++a],answer2); // any remnant
		unsigned int oldRight = right;
		if ((a-1) != wordCount && !showUsed)
		{
			Log(STDUSERLOG,"Tag MisCount: %d instead of %d %s \r\n",a,wordCount,buffer);
			while (++a <= wordCount) *mytags[a] = 0;
		}

		if (actualLen != wordCount && !showUsed ) 
		{
			Log(STDUSERLOG,"MisCount: %d %s \r\n",currentFileLine,buffer);
		}
		strcpy(prior,buffer);
		int oldright = right;
		logged = false;
		if (!reveal) for (unsigned int i = 1; i <= wordCount; ++i) // match off the pos values we understand. all others are wrong by definition
		{
retry:
			unsigned int ok = right;
			char* sep = strchr(tags[i],'|');
			char* original = wordStarts[i];
			if (sep) *sep = 0;
			
			if (bitCounts[i] != 1 && (tokenControl & DO_PARSE) == DO_PARSE  ) // did not solve even when parsed
			{
				Log(STDUSERLOG,"Parse result- Ambiguous %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			} 
			
			else if (ignoreRule != -1 && !stricmp(wordStarts[i],"than")) ++right; // special against rule mode
			else if (posValues[i-1] & IDIOM) ++right; // we will PRESUME we are right - he did a lot of harm -- they say of is prep. we say the phrase is adjective
			else if (!stricmp(tags[i],"-LRB-"))
			{
				if (*wordStarts[i] == '(') ++right;
				else if (!showUsed || usedWordIndex == i) Log(STDUSERLOG,"** Bad left paren %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"-RRB-"))
			{
				if (*wordStarts[i] == ')') ++right;
				else if (!showUsed || usedWordIndex == i)  Log(STDUSERLOG,"** Bad right paren %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"-LSB-"))
			{
				if (*wordStarts[i] == '[') ++right;
				else if (!showUsed || usedWordIndex == i)  Log(STDUSERLOG,"** Bad left square bracket %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"-RSB-"))
			{
				if (*wordStarts[i] == ']') ++right;
				else if (!showUsed || usedWordIndex == i)  Log(STDUSERLOG,"** Bad right square bracket %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"-LCB-"))
			{
				if (*wordStarts[i] == '{') ++right;
				else if (!showUsed || usedWordIndex == i)  Log(STDUSERLOG,"** Bad left curly bracket %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"-RCB-"))
			{
				if (*wordStarts[i] == '}') ++right;
				else if (!showUsed || usedWordIndex == i)  Log(STDUSERLOG,"** Bad right curly bracket %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (posValues[i] & IDIOM) ++right;
			else if (!stricmp(tags[i],"TO")) ++right;	// always correct
			else if (!stricmp(tags[i],"NN")) 
			{
				if (posValues[i] & (NOUN_SINGULAR | ADJECTIVE_NOUN | NOUN_NUMBER)  && allOriginalWordBits[i] & (NOUN_SINGULAR|NOUN_NUMBER)) ++right;
				else if (posValues[i] & ADJECTIVE_PARTICIPLE && allOriginalWordBits[i] & NOUN_GERUND) ++right; // *drinking straws
				else if (posValues[i] & NOUN_SINGULAR) ++right; // they doubtless dont know it should be lower case
				else if (posValues[i] & ADJECTIVE_NORMAL && allOriginalWordBits[i] & NOUN_SINGULAR) ++right;  //"*expert aim"
				else if (posValues[i] & NOUN_PROPER_SINGULAR) ++right; // "*Pill bugs are good"
				else if (posValues[i] == PARTICLE) ++right; // "take *care of"
				else if (posValues[i-1] == IDIOM) ++right; // "by the *time I got here, she left"
				else if (posValues[i] & NOUN_GERUND && allOriginalWordBits[i] & NOUN_SINGULAR) ++right; // "*spitting is good"
				else if (posValues[i] & PRONOUN_BITS) ++right; // someone, anyone, etc
				else if (!showUsed || (usedWordIndex == i && usedType & (NOUN_SINGULAR|ADJECTIVE_NOUN)))  Log(STDUSERLOG,"** Bad NN (singular) %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"NNS")) 
			{
				if (posValues[i] & (NOUN_PLURAL| ADJECTIVE_NOUN)  && allOriginalWordBits[i] & NOUN_PLURAL) ++right;
				else if (posValues[i] & NOUN_NUMBER && canSysFlags[i] & MODEL_NUMBER) ++right; // model numbers
				else if (posValues[i] & NOUN_PROPER_PLURAL) ++right; // they get it wrong
				else if (posValues[i] & PRONOUN_BITS) ++right; // others
				else if (posValues[i] & NOUN_NUMBER) ++right; // 1920s
				else if (posValues[i] & NOUN_SINGULAR && ( allOriginalWordBits[i] &  NOUN_PLURAL || lcSysFlags[i] & NOUN_NODETERMINER)) ++right;
				else if (!showUsed || (usedWordIndex == i && usedType & (NOUN_PLURAL|ADJECTIVE_NOUN)))  Log(STDUSERLOG,"** Bad NNS (plural) %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"NNP")) // proper singular
			{
				uint64 val;
				if (posValues[i] & (NOUN_PROPER_SINGULAR | ADJECTIVE_NOUN) && allOriginalWordBits[i] & (NOUN_PROPER_SINGULAR | NOUN_SINGULAR)) ++right;
				else if (posValues[i] & NOUN_PROPER_PLURAL && allOriginalWordBits[i] & NOUN_PROPER_SINGULAR) ++right; // we just picked the other side
				else if (posValues[i] & NOUN_NUMBER && canSysFlags[i] & MODEL_NUMBER) ++right; // model numbers
				else if (posValues[i] & NOUN_NUMBER && IsRomanNumeral(wordStarts[i],val)) ++right; //  roman numerals
				else if (posValues[i] & ADJECTIVE_NORMAL && IsUpperCase(*wordStarts[i])) ++right; // things like French can be adjective or noun, we often call them adjectives instead of adjective_noun
				else if (posValues[i] & ADJECTIVE_NORMAL && allOriginalWordBits[i] & NOUN_PROPER_SINGULAR) ++right; // things like French can be adjective or noun, we often call them adjectives instead of adjective_noun
				else if (posValues[i] & NOUN_PROPER_PLURAL) ++right; // if it ended in s like Atomos.
				else if (posValues[i] & NOUN_SINGULAR) ++right; // "Bear had to eat a lot in raw mode
				else if (!showUsed || (usedWordIndex == i && usedType & (NOUN_PROPER_SINGULAR|ADJECTIVE_NOUN)))  Log(STDUSERLOG,"** Bad NNP (propersingular) %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"NNPS"))  // proper plural
			{
				if (posValues[i] & (NOUN_PROPER_PLURAL| ADJECTIVE_NOUN) && allOriginalWordBits[i] & NOUN_PROPER_PLURAL) ++right;
				else if (posValues[i] & NOUN_PROPER_SINGULAR && allOriginalWordBits[i] & NOUN_PROPER_PLURAL) ++right; // we just picked the other side
				else if (posValues[i] & NOUN_PROPER_SINGULAR) ++right; // confusion like Mercedes which is singualr
				else if (posValues[i] & NOUN_PLURAL) ++right;
				else if (!showUsed ||  (usedWordIndex == i && usedType & NOUN_PROPER_PLURAL))  Log(STDUSERLOG,"** Bad NNPS (properplural) %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"IN")) 
			{
				if (posValues[i] & (CONJUNCTION_SUBORDINATE|PREPOSITION)) ++right;
				else if (posValues[i] & IDIOM && allOriginalWordBits[i] & PREPOSITION) ++right; // "a couple *of days"
				else if (posValues[i] & PARTICLE && allOriginalWordBits[i] & PREPOSITION) ++right; 
				else if (!showUsed ||  (usedWordIndex == i && usedType & (CONJUNCTION_SUBORDINATE|PREPOSITION)))  Log(STDUSERLOG,"** Bad IN %s word %d(%s) line %d: %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"PDT")) 
			{
				if (posValues[i] & PREDETERMINER) ++right;
				else if (posValues[i] & DETERMINER) ++right; // close enough
				else if (!showUsed || (usedWordIndex == i && usedType & DETERMINER_BITS))  Log(STDUSERLOG,"** Bad PDT %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"POS")) 
			{
				if (posValues[i] & POSSESSIVE) ++right;
				else if (!showUsed || (usedWordIndex == i && usedType & POSSESSIVE))  Log(STDUSERLOG,"** Bad POS %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,mytags[i],buffer);
			}
			else if (!stricmp(tags[i],"LS")) // bullet point
			{
				if (posValues[i] & NOUN_NUMBER) ++right;
				else if (!showUsed || usedWordIndex == i)  Log(STDUSERLOG,"** Bad LS %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"CC")) 
			{
				if (posValues[i] & CONJUNCTION_COORDINATE) ++right;
				else if (!showUsed || (usedWordIndex == i && usedType & CONJUNCTION_COORDINATE))  Log(STDUSERLOG,"** Bad CC %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"JJ")) 
			{
				if (posValues[i] & (ADJECTIVE_NORMAL|NOUN_NUMBER)) ++right;
				else if (posValues[i] & ADJECTIVE_NUMBER && !(allOriginalWordBits[i] & (MORE_FORM|MOST_FORM))) ++right;
				else if (posValues[i] & NOUN_SINGULAR && allOriginalWordBits[i] & NOUN_GERUND  && allOriginalWordBits[i] & ADJECTIVE_NORMAL) ++right; // " *melting point" 
				else if (posValues[i] & NOUN_PROPER_SINGULAR) ++right; // " *Western boots" 
				else if (posValues[i] & VERB_PAST_PARTICIPLE) ++right;
				else if (posValues[i] & (ADJECTIVE_PARTICIPLE | ADJECTIVE_NOUN)) ++right; // "I am *tired"  "*pill bugs eat"
				else if (posValues[i] & NOUN_GERUND ) ++right; // "he got me *moving"
				else if (posValues[i] & NOUN_ADJECTIVE ) ++right; // "he got me *moving"
				else if (posValues[i] & NOUN_SINGULAR && posValues[i+1] & (ADJECTIVE_BITS|NOUN_BITS) && (tokenControl & DO_PARSE) != DO_PARSE ) ++right; // "the *bank teller" when using RAW mode or "*money_market mutual funds"
				else if (posValues[i] & (PREDETERMINER|DETERMINER)) ++right; // "*Other people"  "of *such stature"
				else if (posValues[i] & ADVERB && allOriginalWordBits[i] & ADJECTIVE_NORMAL && posValues[i+1] & ADJECTIVE_BITS) ++right; // we consider them adverbs
				else if (posValues[i] & PARTICLE) ++right; // "take it for *granted"
				else if (posValues[i] & VERB_PRESENT_PARTICIPLE && allOriginalWordBits[i] & ADJECTIVE_BITS) ++right;	// she is *willing to go"
				else if (!showUsed || (usedWordIndex == i && usedType & ADJECTIVE_BITS))  Log(STDUSERLOG,"** Bad JJ %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"JJR")) 
			{
				if (originalLower[i]  && posValues[i] & ADJECTIVE_NORMAL && allOriginalWordBits[i] & MORE_FORM) ++right;
				else if ( posValues[i] & DETERMINER && allOriginalWordBits[i] & MORE_FORM) ++right;
				else if (!showUsed || (usedWordIndex == i && usedType & ADJECTIVE_BITS))  Log(STDUSERLOG,"** Bad JJR %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"JJS")) 
			{
				if (originalLower[i] && posValues[i] & ADJECTIVE_NORMAL && allOriginalWordBits[i] & MOST_FORM) ++right;
				else if ( posValues[i] & DETERMINER && allOriginalWordBits[i] & MOST_FORM) ++right;
				else if (!showUsed || (usedWordIndex == i && usedType & ADJECTIVE_BITS))  Log(STDUSERLOG,"** Bad JJS %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"RB")) 
			{
				if (posValues[i] & ADVERB) ++right;
				else  if (posValues[i] & PARTICLE && allOriginalWordBits[i] & ADVERB)  ++right;
				else if (!showUsed || (usedWordIndex == i && usedType & ADVERB))  Log(STDUSERLOG,"** Bad RB %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"RBR")) 
			{
				if (posValues[i] & ADVERB && allOriginalWordBits[i] & MORE_FORM) ++right;
				else if (!showUsed ||  (usedWordIndex == i && usedType & ADVERB))  Log(STDUSERLOG,"** Bad RBR %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"RBS")) 
			{
				if (posValues[i] & ADVERB && allOriginalWordBits[i] & MOST_FORM) ++right;
				else if (!showUsed ||  (usedWordIndex == i && usedType & ADVERB))  Log(STDUSERLOG,"** Bad RBS %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
		    }
			else if (!stricmp(tags[i],"UH")) 
			{
				if (posValues[i] & INTERJECTION) ++right;
				else if (wordCount == 1) ++right;	// anything COULD be...
				else if (!showUsed || usedWordIndex == i)  Log(STDUSERLOG,"** Bad UH %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
		    }
			else if (!stricmp(tags[i],"MD")) 
			{
				if (posValues[i] & AUX_VERB) ++right;
				else if (!showUsed ||  (usedWordIndex == i && usedType & AUX_VERB_TENSES))  Log(STDUSERLOG,"** Bad MD %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"RP")) 
			{
				if (posValues[i] & PARTICLE) ++right;
				else if (posValues[i] & ADVERB) ++right; // who can say if ideomatic particle verb or adverb.... 
				else if (!showUsed || (usedWordIndex == i && usedType & PARTICLE))  Log(STDUSERLOG,"** Bad RP %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"DT")) 
			{
				if (posValues[i] & DETERMINER_BITS) ++right; // a an the // my her their our your
				else if (posValues[i] & ADJECTIVE_NUMBER) ++right;	// all numbers to us as adjectives might be considered determiners ?????
				else if (posValues[i] & ADJECTIVE_NORMAL && posValues[i-1] == IDIOM) ++right; // "none of *the honey"
				else if (!stricmp(wordStarts[i],"this") && posValues[i] & PRONOUN_BITS) ++right; 
				else if (!stricmp(wordStarts[i],"that") && posValues[i] & PRONOUN_BITS) ++right;
				else if (!stricmp(wordStarts[i],"those") && posValues[i] & PRONOUN_BITS) ++right;
				else if (posValues[i] & ADVERB && posValues[i+1] & PREPOSITION) ++right; // "he walked *all by himself"
				//else if (!stricmp(wordStarts[i],"every") || !stricmp(wordStarts[i],"no") || !stricmp(wordStarts[i],"another")
				//	 || !stricmp(wordStarts[i],"any") || !stricmp(wordStarts[i],"some")
				else if (!showUsed || (usedWordIndex == i && usedType & DETERMINER_BITS))   Log(STDUSERLOG,"** Bad DT %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"PRP$")) 
			{
				if (posValues[i] & PRONOUN_POSSESSIVE) ++right;
				else if (!showUsed ||  (usedWordIndex == i && usedType & PRONOUN_POSSESSIVE))  Log(STDUSERLOG,"** Bad PRP$ %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"PRP")) 
			{
				if (posValues[i] & (PRONOUN_BITS)) ++right;
				else if (!showUsed ||  (usedWordIndex == i && usedType & PRONOUN_BITS))  Log(STDUSERLOG,"** Bad PRP %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"VB")) // infinitive
			{
				if (posValues[i] & (NOUN_INFINITIVE|VERB_INFINITIVE)) ++right;  
				else if (posValues[i] & AUX_VERB && allOriginalWordBits[i] &  VERB_INFINITIVE) ++right;  // includes our modals 
				else if (!showUsed ||  (usedWordIndex == i && usedType & (NOUN_INFINITIVE|VERB_INFINITIVE)))  Log(STDUSERLOG,"** Bad VB (infinitive) %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"VBD")) // past
			{
				if (posValues[i] & VERB_PAST || (posValues[i] & AUX_VERB &&  allOriginalWordBits[i] &  VERB_PAST) ) ++right;  // includes our modals that can have this tense as verbs
				else if (posValues[i] & VERB_PAST_PARTICIPLE && allOriginalWordBits[i] & VERB_PAST) ++right; 
				else if (!showUsed || (usedWordIndex == i && usedType & VERB_PAST))  Log(STDUSERLOG,"** Bad VBD (past) %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"VBG"))  // gerund present participle
			{
				if (allOriginalWordBits[i] & (VERB_PRESENT_PARTICIPLE|NOUN_GERUND)) ++right;  // includes our modals that can have this tense as verbs
				else if (!showUsed || (usedWordIndex == i && usedType & (VERB_PRESENT_PARTICIPLE|NOUN_GERUND)))   Log(STDUSERLOG,"** Bad VBG (present participle) %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
		    }
			else if (!stricmp(tags[i],"VBN")) // past particple
			{
				if (posValues[i] & VERB_PAST_PARTICIPLE || ( posValues[i] & AUX_VERB && allOriginalWordBits[i] & VERB_PAST_PARTICIPLE)) ++right;  // includes our modals that can have this tense as verbs
				else if (posValues[i] & (ADJECTIVE_PARTICIPLE|ADJECTIVE_NORMAL|NOUN_ADJECTIVE) && allOriginalWordBits[i] & VERB_PAST_PARTICIPLE) ++right;
				else if (!showUsed || (usedWordIndex == i && usedType & VERB_PAST_PARTICIPLE))   Log(STDUSERLOG,"** Bad VBN (past participle) %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"VBP")) // present
			{
				if (posValues[i] & VERB_PRESENT || (posValues[i] & AUX_VERB && allOriginalWordBits[i]  &  VERB_PRESENT)) ++right;  // includes our modals that can have this tense as verbs
				else if (!showUsed || (usedWordIndex == i && usedType & VERB_PRESENT))  Log(STDUSERLOG,"** Bad VBP (present) %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"VBZ")) // 3ps
			{
				if (posValues[i] & VERB_PRESENT_3PS || (posValues[i] & AUX_VERB && allOriginalWordBits[i]  &  VERB_PRESENT_3PS)) ++right; // includes our modals that can have this tense as verbs
				else if (!showUsed || (usedWordIndex == i && usedType & VERB_PRESENT_3PS))  Log(STDUSERLOG,"** Bad VBZ (present_3ps) %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"WDT")) 
			{
				if (!stricmp(wordStarts[i],"that") || !stricmp(wordStarts[i],"what") ||!stricmp(wordStarts[i],"whatever") ||!stricmp(wordStarts[i],"which") ||!stricmp(wordStarts[i],"whichever"))
				{ 
					if (posValues[i] & (DETERMINER|PRONOUN_BITS|CONJUNCTION_SUBORDINATE)) ++right; // what dog is that
					else if (!showUsed || usedWordIndex == i)  Log(STDUSERLOG,"** Bad WDT %s word %d(%s) line %d: %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
				}
				else if (!showUsed || usedWordIndex == i)  Log(STDUSERLOG,"** Bad WDT %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"WP")) 
			{
				// that may be WDT
				if ( !stricmp(wordStarts[i],"what") || !stricmp(wordStarts[i],"who") || !stricmp(wordStarts[i],"whom"))
				{ // that whatever which WDT - whatsoever RB -  whosoever NN
					if (posValues[i] & (PRONOUN_BITS|CONJUNCTION_SUBORDINATE | DETERMINER | PREDETERMINER)) ++right; // what is that
					else if (!showUsed || usedWordIndex == i)  Log(STDUSERLOG,"** Bad WP %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
				}
				else if (!showUsed || usedWordIndex == i)  Log(STDUSERLOG,"** Bad WP %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"WP$")) 
			{
				if (!stricmp(wordStarts[i],"whose"))
				{
					if (posValues[i] & (PRONOUN_POSSESSIVE | DETERMINER)) ++right; // whose dog is that -- do we do both? or only one?
					else if (!showUsed || usedWordIndex == i)  Log(STDUSERLOG,"** Bad WP$ %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
				}
				else if (!showUsed || usedWordIndex == i)  Log(STDUSERLOG,"** Bad WP$ %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"WRB")) 
			{
				if (!stricmp(wordStarts[i],"how")  ||!stricmp(wordStarts[i],"whenever") ||!stricmp(wordStarts[i],"when") ||!stricmp(wordStarts[i],"where")
					||!stricmp(wordStarts[i],"whereby")||!stricmp(wordStarts[i],"wherein")||!stricmp(wordStarts[i],"why"))
				{
					// the ONLY exception is  "when" meaning "if" should be IN.  
					++right; 
					// however, whence, wherever, whereof are NOT wrb?
				}
				else if (!showUsed || usedWordIndex == i)  Log(STDUSERLOG,"** Bad WRB %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!IsAlphaUTF8(*tags[i]) || !stricmp(tags[i],"SYM") ) 
			{
				++right;	// all punctuation must be right
			}
			else if (!stricmp(tags[i],"CD")) 
			{
				if (posValues[i] & (NOUN_NUMBER | ADJECTIVE_NUMBER)) ++right;
				else if (posValues[i] & NOUN_PLURAL && IsDigit(*wordStarts[i])) ++right; // 1960s
				else if (posValues[i] & NOUN_PROPER_SINGULAR && FindWord(wordStarts[i],0,LOWERCASE_LOOKUP) && FindWord(wordStarts[i],0,LOWERCASE_LOOKUP)->properties & NOUN_NUMBER) ++right;
				else if (allOriginalWordBits[i] & NOUN_NUMBER) ++right;  // one as pronoun sometimes
				else if (!showUsed || usedWordIndex == i)  Log(STDUSERLOG,"** Bad CD %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"EX")) 
			{
				if (posValues[i]  &  THERE_EXISTENTIAL) ++right;
				else if (!showUsed ||  (usedWordIndex == i && usedType & THERE_EXISTENTIAL))  Log(STDUSERLOG,"** Bad EX %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!stricmp(tags[i],"FW")) 
			{
				if (strstr(mytags[i],"unknown-word") || allOriginalWordBits[i] & FOREIGN_WORD) ++right;
				else if (!showUsed || usedWordIndex == i)  Log(STDUSERLOG,"** Bad FW %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}
			else if (!sep) if (!showUsed || usedWordIndex == i)  Log(STDUSERLOG,"** Bad Unknown tag word %d(%s) line %d: %s %s\r\n",i,wordStarts[i],currentFileLine,tags[i],buffer);

			// composite choices
			if (sep && right == ok) // didn't match it yet
			{
				memmove(tags[i],sep+1,strlen(sep+1) + 1);
				goto retry;
			}

			if (stricmp(tags[i],"RP") && posValues[i] & PARTICLE && bitCounts[i] == 1 && right == ok) // things we thought were particles that werent counted as right
			{
				unsigned int at = i;
				while (--at >= 1 && !(posValues[at] & (VERB_BITS|NOUN_INFINITIVE|NOUN_GERUND|ADJECTIVE_PARTICIPLE))){;} // find verb linked across any sentence fragment
				if (!(posValues[at] & (VERB_BITS|NOUN_INFINITIVE|NOUN_GERUND|ADJECTIVE_PARTICIPLE))) // should NOT HAPPEN - we MUST find or particle option would have been removed
				{
					 if (!showUsed || usedWordIndex == i) Log(STDUSERLOG,"** Faulty RP Cannot find verb before particle %s word %d(%s) line %d:  %s\r\n",mytags[i],i,wordStarts[i],currentFileLine,buffer);
				}
				char word[MAX_WORD_SIZE];
				*word = 0;

				// FIRST, assume they are contiguous
				strcat(word,wordCanonical[at]);
				strcat(word,"_");
				while (++at <= i)
				{
					strcat(word,wordStarts[at]);
					if (at != i) strcat(word,"_");
				}
				WORDP X = FindWord(word);
				if (X) 
				{
					if (X->systemFlags & VERB_DIRECTOBJECT) strcat(word," directobj ");
					if (X->systemFlags & VERB_NOOBJECT) strcat(word," noobj ");
				}
				else // assume they are discontiguous
				{
					*word = 0;
					strcat(word,wordCanonical[at]);
					strcat(word,"_");
					strcat(word,wordStarts[i]);
				}
				 if (!showUsed || usedWordIndex == i) Log(STDUSERLOG,"** Faulty RP %s %s word %d(%s) line %d:  %s\r\n",word,mytags[i],i,wordStarts[i],currentFileLine,buffer);
			}		

			// it was considered wrong
			if (ok == right)
			{
				WORDP X = FindWord( stricmp(tags[i],"IN") ? tags[i] : "IN ");
				if (X)
				{
					X->w.planArgCount++;
					X->internalBits |= DELETED_MARK;
				}
			}
		}
		if (showUsed && *usedTrace && logged) {
			Log(STDUSERLOG,"** USED: line: %d %s\r\n",currentFileLine,answer1);
		}
		if (reveal && *usedTrace) {
			Log(STDUSERLOG,"** USED: line: %d %s\r\n",currentFileLine,answer1);
			continue;
		}
		if ((tokenControl & DO_PARSE) == DO_PARSE ) 
		{
			if ((right-oldRight) != wordCount){;} // pos is bad so parse is by definition bad
			else if (tokenFlags & FAULTY_PARSE && !(tokenFlags & NOT_SENTENCE)) 
			{
				Log(STDUSERLOG,"** Faulty parse %d words line %d: %s\r\n",wordCount,currentFileLine,buffer);
				++parseBad;
			}
			else ++parseOK;

			// verify plurality and determined
			unsigned int subject = 0;
			for (unsigned int i = startSentence; i <= endSentence; ++i)
			{
				if (roles[i] & (SUBJECT2|MAINSUBJECT)) subject = i;
				if (roles[i] & (VERB2|MAINVERB))
				{
					if (subject && posValues[subject] == NOUN_SINGULAR && posValues[i] == VERB_PRESENT && !(lcSysFlags[i] & NOUN_NODETERMINER)) Log(STDUSERLOG,"*** Warning singular noun %s to plural verb %s in %s\r\n",wordStarts[subject],wordStarts[i],buffer);
					if (subject && posValues[subject] == NOUN_PLURAL && posValues[i] == VERB_PRESENT_3PS) Log(STDUSERLOG,"*** Warning plural noun %s to singular verb %s in %s\r\n",wordStarts[subject],wordStarts[i],buffer);
					if (subject && posValues[subject] == PRONOUN_BITS && posValues[i] == VERB_PRESENT && !(lcSysFlags[i] & PRONOUN_SINGULAR)) Log(STDUSERLOG,"*** Warning singular pronoun %s to plural verb %s in %s\r\n",wordStarts[subject],wordStarts[i],buffer);
					if (subject && posValues[subject] == PRONOUN_BITS && posValues[i] == VERB_PRESENT_3PS && lcSysFlags[i] & PRONOUN_SINGULAR) Log(STDUSERLOG,"*** Warning plural pronoun %s to singular verb %s in %s\r\n",wordStarts[subject],wordStarts[i],buffer);
					subject = 0;
				}
				if (roles[i] & (SUBJECT2|MAINSUBJECT|OBJECT2|MAINOBJECT|INDIRECTOBJECT2|MAININDIRECTOBJECT) && posValues[i] & NOUN_SINGULAR && originalLower[i] && !(originalLower[i]->properties & PRONOUN_BITS) &&  !(lcSysFlags[i] & NOUN_NODETERMINER) )
				{
					unsigned int det;
					if (!IsDeterminedNoun(i,det)) Log(STDUSERLOG,"   *** Warning undetermined noun %s in %s\r\n",wordStarts[i],buffer);
				}
			}
		}
	}
	fclose(in);
	FreeBuffer();
	if (ignoreRule >= 0 && ignoreRule < (int) tagRuleCount) 
	{
		if (total-right)
		{
			Log(STDUSERLOG,"Rule fail: %s\r\n",comments[ignoreRule]);
		}
		++ignoreRule;
		goto reloop;
	}

	float percent = ((float)right * 100) /total;
	int val = (int)percent;
	percent = ((float)parseBad * 100) /sentences;
	int val1 = (int)percent;
	percent = ((float)ambigItems * 100) /ambiguousWords;
	int val2 = (int) percent;
	percent = ((float)ambiguousWords * 100) /total;
	int val3 = (int) percent;

	unsigned long timediff =  (unsigned long)( ElapsedMilliseconds() - startTime); 
	unsigned int tokensec = (timediff) ? ((total * 1000) / timediff) : 0; 
	FreeBuffer();

	Log(STDUSERLOG,"\r\nambigWords:%d  wrong:%d  notWrong:%d total:%d percent:%d sentences:%d parsed:%d parseBad:%d badSentencePercent:%d initialAmbiguousWords:%d percentambigLeft:%d initialAmbigpercent:%d\r\n\r\n",ambigItems,total-right,right,total,val,sentences,parseOK,parseBad,val1,ambiguousWords,val2,val3);
	if (!raw && !ambig) Log(STDUSERLOG,"parsed:%d parseBad:%d badSentenceRate:%d initialAmbiguousWords:%d percentambigLeft:%d initialAmbigpercent:%d\r\n\r\n",parseOK,parseBad,val1,ambiguousWords,val2,val3);
	WalkDictionary(ShowFailCount,0);
	Log(STDUSERLOG,"\r\n");
	ignoreRule = -1;
	if (line) 
	{ 
		trace = 0; 
		echo = false;
	}
}

static void C_PennNoun(char* file)
{
	char word[MAX_WORD_SIZE];
	file = ReadCompiledWord(file,word);
	char filename[MAX_WORD_SIZE];
	if (*word) sprintf(filename,"REGRESS/PENNTAGS/%s.txt",word);
	else strcpy(filename,"REGRESS/PENNTAGS/penn.txt");  // REGRESS/PENTAGS
	FILE* in = FopenReadOnly(filename);
	if (!in) return;
	char* buffer = AllocateBuffer();
	char tags[MAX_SENTENCE_LENGTH][20];
	char tokens[MAX_SENTENCE_LENGTH][100];
	unsigned int len;
	while (ReadALine(readBuffer,in) >= 0)
	{
		char* at = buffer;
		*at = 0;
		char word[MAX_WORD_SIZE];
		char* ptr = SkipWhitespace(readBuffer);
		if (!*ptr || *ptr == '#') continue;
		len = 0;
		while (ptr && *ptr)
		{
			ptr = ReadCompiledWord(ptr,word);
			if (!*word) break;
			char* sep = strrchr(word,'/'); // find last one (there might be \/  when they actually want token
			if (!sep)
			{
				printf("Failed %s\r\n",readBuffer);
				break;
			}
			*sep = 0;
			++len;

			// recode quotes (opening and closing)
			if (*word == '`' && word[1] == '`') strcpy(word,"\"");
			if (*word == '\'' && word[1] == '\'') strcpy(word,"\"");
			// recode \/ and its ilk
			char word1[MAX_WORD_SIZE];
			strcpy(word1,word);
			char* sep1;
			while ((sep1 = strchr(word1,'\\'))) memmove(sep1,sep1+1,strlen(sep1)+1);

			strcpy(tokens[len],word1);
			strcat(at,word1);
			at += strlen(at);
			strcat(at++," ");
			strcpy(tags[len],sep+1); // what we expect
		}
		if (len == 0) continue; // on to next

		*at = 0;
		for (unsigned int i = 1; i <= len; ++i) // match off the pos values we understand. all others are wrong by definition
		{
			char* sep = strchr(tags[i],'|');
			if (sep) *sep = 0;

			if (!stricmp(tags[i],"NN")) // found a noun, look backwards...
			{
				if (!strnicmp(tags[i+1],"NN",2)) continue;	 // noun follows us. he must be determined instead
				for (unsigned int x = i-1; x >= 1; --x)
				{
					if (!stricmp(tokens[x],",")) break;	 // immediately after comma may be appositive "Bob, dog of my dreams
					if (!stricmp(tokens[x],"of")) break;	 // can say of xxx always as in type of dog
					if (!stricmp(tags[x],"CC")) break;	// assume guy before is determeined
					if (!stricmp(tags[x],"DT")) break;	// it is determined
					if (!stricmp(tags[x],"POS")) break;	// is owned
					if (tags[x][0] == 'N') continue;	// it is joined noun.
					if (*tags[x] == 'J') continue; // adj
					if (!stricmp(tags[x],"PRP$")) break; // word after conjunct
					WORDP D = FindWord(tokens[i]);
					if (IsUpperCase(*tokens[i])) break; // actually not NN
					if (D && !IsAlphaUTF8(*D->word)) break;	 // not a normal word
					if (D && D->systemFlags & NOUN_NODETERMINER)
						break;
					Log(STDUSERLOG,"%s: %s %s  %s\r\n",tokens[i],tags[x],tokens[x], buffer); // unxpected
					break;
	
				}
			}
		}
	}
	fclose(in);
	FreeBuffer();
}

static void C_VerifyPos(char* file)
{
	if (!*file) file = "REGRESS/postest.txt";
	FILE* in = FopenReadOnly(file);  // REGRESS/postest
	if (!in) return;

	unsigned int start = ElapsedMilliseconds();
	
	prepareMode = POSVERIFY_MODE;
	uint64 oldtokencontrol = tokenControl;
	tokenControl =  DO_PARSE | DO_ESSENTIALS| DO_CONTRACTIONS | DO_BRITISH  | STRICT_CASING | DO_NUMBER_MERGE | DO_PROPERNAME_MERGE; 
	unsigned int tokens = 0;
	unsigned int count = 0;
	unsigned int fail = 0;
	char sentence[MAX_WORD_SIZE];
	while (ReadALine(readBuffer,in) >= 0)
	{
		char* ptr =  SkipWhitespace(readBuffer);
		if (!strnicmp(ptr,"#END",3)) break;
		if (!*ptr || *ptr == '#') continue;
		// debug command
		if (*ptr == ':' && IsAlphaUTF8(ptr[1]))
		{
			char output[MAX_WORD_SIZE];
			DoCommand(ptr,output);
			continue;
		}
		ReturnToFreeze(); // dont let dictionary tamper affect this. A problem with ANY multiple sentence input...
	
		++count;
		strcpy(sentence,ptr);
		PrepareSentence(sentence,true,true);
		tokens += wordCount;
		char parseForm[MAX_WORD_SIZE * 5];
		*parseForm = 0;
		char liveParse[MAX_WORD_SIZE * 5];
		*liveParse = 0;
		strcpy(liveParse,DumpAnalysis(1,wordCount,posValues,"Parsed POS",false,true));
		TrimSpaces(liveParse,false);
		while (ReadALine(readBuffer,in) >= 0)
		{
			char* start = SkipWhitespace(readBuffer);
			if (!*start || *start == '#') continue;
			if (!strnicmp(start,"Parsed",6)) 
			{
				strcpy(parseForm,TrimSpaces(start,false)); 
				break;
			}
		}

		if (strcmp(parseForm,liveParse))
		{
			size_t i;
			for (i = 0; i < strlen(parseForm); ++i)
			{
				if (parseForm[i] != liveParse[i]) break;
				if (!parseForm[i] || !liveParse[i]) break;
			}
			while (i && parseForm[--i] != '(');	// find start backwards
			if (i) --i;
			while (i && parseForm[--i] != ' ');	
			char hold[BIG_WORD_SIZE];
			strcpy(hold,parseForm+i);
			parseForm[i] = 0;
			strcat(parseForm,"\r\n--> ");
			strcat(parseForm,hold);
			char hold1[BIG_WORD_SIZE];
			*hold1 = 0;
			size_t len = strlen(liveParse);
			if ( len > i) strcpy(hold1,liveParse+i);
			liveParse[i] = 0;
			strcat(liveParse,"\r\n--> ");
			strcat(liveParse,hold1);
			Log(STDUSERLOG,"\r\nMismatch at %d: %s\r\n",count,sentence);
			Log(STDUSERLOG,"          got: %s\r\n",liveParse);
			Log(STDUSERLOG,"         want: %s\r\n",parseForm);
			int old = trace;
			trace |= TRACE_POS;
			PrepareSentence(sentence,true,true);
			trace = old;
			++fail;
		}
	}

	fclose(in);

	Log(STDUSERLOG,"%d sentences tested, %d failed doing %d tokens in %d ms\r\n",count,fail,tokens, ElapsedMilliseconds() - start);
	tokenControl = oldtokencontrol;
	prepareMode = NO_MODE; 
}

static void C_TimePos(char* file) // how many wps for pos tagging
{
	if (!*file) file = "RAWDICT/postiming.txt";
	FILE* in = fopen(file,"rb");
	if (!in) return;
	prepareMode = POSTIME_MODE;
	uint64 oldtokencontrol = tokenControl;
	tokenControl = DO_PARSE | DO_SUBSTITUTE_SYSTEM  | DO_NUMBER_MERGE | DO_PROPERNAME_MERGE ;
	posTiming = 0;
	unsigned int words = 0;
	while (ReadALine(readBuffer,in) >= 0)
	{
		char* ptr =  SkipWhitespace(readBuffer);
		if (!*ptr || *ptr == '#') continue;
		if (!strnicmp(ptr,"Tagged",6)) continue; 
		PrepareSentence(ptr,true,true);
		words += wordCount;
	}

	fclose(in);
	float wps = (float)words / ((float)posTiming/(float)1000.0);
	Log(STDUSERLOG,"%d words tagged in %d ms wps: %d.\r\n",words,posTiming, (unsigned int) wps);
	tokenControl = oldtokencontrol;
	prepareMode = NO_MODE; 
}

static void C_VerifySpell(char* file) // test spell checker against a file of entries  wrong-spell rightspell like livedata/spellfix.txt
{ 
	FILE* in = fopen(file,"rb");
	if (!in) return;
	unsigned int right = 0;
	unsigned int wrong = 0;
	while (ReadALine(readBuffer,in) >= 0)
	{
		// pull out the wrong and right words
		char wrongWord[MAX_WORD_SIZE];
		char rightWord[MAX_WORD_SIZE];
		char* ptr = SkipWhitespace(readBuffer);
		if (*ptr == 0 || *ptr == '#' || *ptr == '<' || *ptr == '\'' || IsDigit(*ptr)) continue; // unusual stuff
		ptr = ReadCompiledWord(ptr,wrongWord);
		if (strchr(wrongWord,'>') || strchr(wrongWord,'.') || strchr(wrongWord,',')) continue;  // unusual stuff
		ReadCompiledWord(ptr,rightWord);
		if (!*rightWord || strchr(rightWord,'+') || *rightWord == '~'  || *rightWord == '%') continue;  // unusual stuff
		
		WORDP D = FindWord(wrongWord);
		if (D && D->properties & (PART_OF_SPEECH|FOREIGN_WORD)) // already has a meaning
		{
			Log(STDUSERLOG,"%s already in dictionary\r\n",wrongWord);
			continue;
		}

		char* fix = SpellFix(wrongWord,1,PART_OF_SPEECH); 
		if (fix && !strcmp(fix,rightWord)) ++right;
		else
		{
			Log(STDUSERLOG,"%s wanted %s but got %s\r\n",wrongWord,rightWord,fix);
			++wrong;
		}
	}

	fclose(in);
	Log(STDUSERLOG,"Right:%d  Wrong:%d\r\n",right,wrong);
}

static void VerifySubstitutes1(WORDP D, uint64 unused)
{
	if (!(D->internalBits & HAS_SUBSTITUTE)) return;

	char expectedText[MAX_WORD_SIZE];
	char resultText[MAX_WORD_SIZE];
	*readBuffer = 0;
	unsigned int n;

	//   see if word has start or end markers. Remove them.
	bool start = false;
	if (*D->word == '<')
	{
		start = true;
		n = BurstWord(D->word+1);
	}
	else n = BurstWord(D->word);
	bool end = false;
	char* last = GetBurstWord(n-1);
	size_t len = strlen(last);
	if (last[len-1] == '>')
	{
		end = true;
		last[len-1] = 0;
	}

	//   now composite an example, taking into account start and end markers
	unsigned int i;
	if (!start) strcat(readBuffer,"x ");	//   so match is not at start
	for (i = 0; i < n; ++i)
	{
		strcat(readBuffer,GetBurstWord(i));
		strcat(readBuffer," ");
	}
	if (!end) strcat(readBuffer,"x "); //   so match is not at end

	//   generate what it results in
	PrepareSentence(readBuffer,true,true);

	*resultText = 0;
	if (!end) --wordCount;	//   remove the trailing x
	for (i = 1; i <= wordCount; ++i) //   recompose what tokenize got
	{
		if (!start && i == 1) continue;	//   remove the leading x
		strcat(resultText,wordStarts[i]);
		strcat(resultText," ");
	}

	WORDP S = GetSubstitute(D);
	if (!S && wordCount == 0) return;	//   erased just fine
	if (!S) Log(STDUSERLOG,"Substitute failed: %s didn't erase itself, got %s\r\n",D->word,resultText);
	else
	{
		strcpy(expectedText,S->word);
		strcat(expectedText," ");	//   add the trailing blank we get from concats above
		char* at;
		while ((at = strchr(expectedText,'+'))) *at = ' '; //   break up answer
		if (!stricmp(resultText,expectedText)) return;	//   got what was expected
		Log(STDUSERLOG,"Substitute failed: %s got %s not %s\r\n",D->word,resultText,expectedText);
	}
}

static void C_VerifySubstitutes(char* ptr) //   see if substitutes work...
{
	WalkDictionary(VerifySubstitutes1);
}

static bool StripEmbedded(char* word,char* &ptr,char* original,char* ref,char* notref,bool &control,bool keep)
{// strip embedded ref
	if (strstr(word,notref)) // contains an end
	{
		char* at = strstr(original,notref);
		if (at == original) // current token starts with it, end mode
		{
			ptr = original + strlen(notref); // skip over it to try again
			control = false;
		}
		else // separate old from new break
		{
			memmove(at+1,at,strlen(at)+1); // make room to separate off token
			*at = ' ';
			ptr = original; // try it again picking off old token then the ender
		}
		return true;
	}
	else if (control) return !keep; // continuing coverage
	else if (strstr(word,ref)) // starter coverage
	{
		char* at = strstr(original,ref); // find where it begins
		if (at == original) // start is it, ignoring or keeping hereafter til later close
		{
			control = !keep;
			ptr = original + strlen(ref);
			return true;
		}
		else // separate old from new break
		{
			memmove(at+1,at,strlen(at)+1); // make room to separate off token
			*at = ' ';
			ptr = original;
		}
		return true;
	}
	else return false;
}

static bool FlushEmbedded(char* & ptr,char* ref,char* notref,unsigned int &control)
{// strip embedded ref
	char* start;
	char* end;
	size_t endlen = strlen(notref);
	size_t startlen = strlen(ref);
	bool closedsqui = false;
	while ((end = strstr(ptr,notref))) // ending coverage exists on input?
	{
		*end = 0;	// trucate for a moment
		char* last = NULL;
		start = ptr - startlen;
		while ((start = strstr(start+startlen,ref)))  last = start; // find last before
		if (last) // here is the corresponding start
		{
			memmove(last,end+endlen,strlen(end+endlen-1)); // erase all content between
			if (*ref == '{' ) closedsqui = true;
			continue;
		}

		// we have an end from a prior one to close off
		if (control)
		{
			ptr = end + endlen; // skip over it to try again
			if (*ref == '{' ) closedsqui = true;
			--control;
		}
		else break; // unknown close
	}

	while ((start = strstr(ptr,ref))) // starter coverage exists in input but has no end for it
	{
		// has start not closed must wait but may have useful stuff before it! 
		++control; // pending
		if (ptr != start) // useful stuff before it?
		{
			*start = 0;
			return false;		// allow processing of this
		}
		return true; // line is garbage
	}
	if (closedsqui && *ptr == ';') // some {{}} have ; after them for no reason?   ayn rand article for example after her pronounciation
		++ptr;
	return (control != 0 || *ptr == 0); // line is ok as it stand or we must flush it
}

static void C_WikiText(char* ptr)
{ // fromfile directory, size
	char file[MAX_WORD_SIZE];
	char directoryout[MAX_WORD_SIZE];
	unsigned int size = 100000;
	bool split = false;
	ptr = ReadCompiledWord(ptr,file);
	ptr = ReadCompiledWord(ptr,directoryout);
	size_t len = strlen(directoryout);
	if (directoryout[len-1] == '/' || directoryout[len-1] == '\\') directoryout[len-1] = 0;	// remove ending /
	if (IsDigit(*ptr))
	{
		ptr = ReadInt(ptr,size);	 // 1kb chunks
		size *=  1000;
		if (!stricmp(ptr,"split")) split = true;
	}
	char bulletchar[5];
	bulletchar[0] = 0xe2; bulletchar[1] = 0x80; bulletchar[2] = 0xa2; bulletchar[3] = 0;  // � 

	unsigned int id = 0;
	char outfile[MAX_WORD_SIZE];
	sprintf(outfile,"%s/file%d.txt",directoryout,id); // the output file
	FILE* out = FopenUTF8Write(outfile);
	if (!out)
	{
		Log(STDUSERLOG,"Cannot open directory %s\r\n",directoryout);
		return;
	}
	else Log(STDUSERLOG,"Starting file: %s\r\n", outfile);

	FILE* in = NULL;
	unsigned int inputid = 0;
	bool inputdirectory = true;
	char word[MAX_WORD_SIZE];
	bool page = false;
	unsigned int countSquiggle = 0;
	bool text = false;
	bool title = false;
	char titlename[MAX_WORD_SIZE];
	char content[MAX_WORD_SIZE];
	char heading[MAX_WORD_SIZE];
	unsigned int lines = 0;
	bool pendingtextclose = false;
	int table = 0;
	bool header = true;
	bool superscript = false;
	bool subscript = false;
	bool italic = false;
	bool center = false;
	bool bold = false;
	bool bullet = false;
	bool killheading = false;
	unsigned int citex = 0;
	unsigned int includex = 0;
	unsigned int galleryx = 0;
	unsigned int mathx = 0;
	unsigned int prex = 0;
	unsigned int span = 0;
	unsigned int squ = 0;
	len = 0;
	while (inputdirectory)
	{
		size_t lent = strlen(file);
		if (file[lent-1] != '/') // read 1 file
		{
			in = FopenReadNormal(file); // WIKITEXT
			inputdirectory = false;
			if (!in) 
			{
				Log(STDUSERLOG,"No such file %s\r\n",file);
				break;
			}
		}
		else // read multiple files
		{
			char filex[MAX_WORD_SIZE];
			sprintf(filex,"%sfile%d.txt",file,inputid);
			in = FopenReadNormal(filex); // WIKITEXT
			if (!in) break; // end of files in directory
			Log(STDUSERLOG,"Reading %s\r\n",filex);
			++inputid;
		}

		bool paragraph = false;
		int len1;
	while ((len1 = ReadALine(readBuffer,in)) >= 0)
	{	
		if (!strncmp(readBuffer,"xxmarkxx",8)) // debug marker during testing
		{
			int xx = 0;
			continue;
		}
		++lines;
		if (split)
		{
			if (strstr(readBuffer,"<page")) // skip to start of a page
			{
				if (len > size) // start in new file, this file is getting too big
				{
					fclose(out);
					++id;
					sprintf(outfile,"%s/file%d.txt",directoryout,id); // the output file
					out = FopenUTF8Write(outfile);
					len = 0;
					Log(STDUSERLOG,"Starting file: %s\r\n", outfile);
				}
			}
			fprintf(out,"%s\r\n",readBuffer);
			len += strlen(readBuffer) + 2;
			continue;
		}
		if (len1 > 40000) // machine generated garbage
		{
			text = page = false;
			continue;
		}

		if (text && *content) 	// MAYBE NOT
		{
			fprintf(out,"%s\r\n",content);
			len += strlen(content) + 2;
			*content = 0;
		}
		
		char* at;
		char* ptr = SkipWhitespace(readBuffer);
		if (*ptr == 0) // NOTHING there-  paragraph boundary?
		{
			if (text) // during text
			{
				paragraph = true;
			}
			continue;
		}

		at = strstr(readBuffer,"See also");
		if (at && (at-readBuffer) < 10) continue;	 // ignore see also

		//
		// reformat special web characters
		//

		while ((at = strstr(ptr,"&lt;")))
		{
			memmove(at+1,at+4,strlen(at+3));
			at[0] = '<';
		}
		while ((at = strstr(ptr,"&gt;")))
		{
			memmove(at+1,at+4,strlen(at+3));
			at[0] = '>';
		}

		while ((at = strstr(ptr,"{{spaced ndash}}")))
		{
			memmove(at+3,at+16,strlen(at+15));
			at[0] = ' ';
			at[1] = '-';
			at[2] = ' ';
		}
			
		while ((at = strstr(ptr,"&lsquot;")))// convert '
		{
			memmove(at+1,at+7,strlen(at+6));
			*at = '"';
		}
				
		while ((at = strstr(ptr,"&rsquot;")))// convert '
		{
			memmove(at+1,at+7,strlen(at+6));
			*at = '"';
		}
	
		while ((at = strstr(ptr,"&quot;")))// convert quotes
		{
			memmove(at+1,at+6,strlen(at+5));
			*at = '"';
		}
		
		while ((at = strstr(ptr,"&ldquo;")))// convert left quotes
		{
			memmove(at+1,at+8,strlen(at+7));
			*at = '"';
		}
		
		while ((at = strstr(ptr,"&rdquo;")))// convert right quotes
		{
			memmove(at+1,at+8,strlen(at+7));
			*at = '"';
		}
	
		while ((at = strstr(ptr,"&laquo;")))// convert left foreign quotes
		{
			memmove(at+1,at+8,strlen(at+7));
			*at = '"';
		}
			
		while ((at = strstr(ptr,"&raquo;")))// convert right foreign quotes
		{
			memmove(at+1,at+8,strlen(at+7));
			*at = '"';
		}

		while ((at = strstr(ptr,"&amp;ndash;")))
		{
			memmove(at+3,at+11,strlen(at+10));
			*at = ' ';
			at[1] = '-';
			at[2] = ' ';
		}

		while ((at = strstr(ptr,"&amp;"))) // preserve &
		{
			memmove(at+1,at+5,strlen(at+4));
			*at = '&';
		}
		while ((at = strstr(ptr,"&nbsp;"))) // kill nonbreaking space
		{
			memmove(at+1,at+6,strlen(at+5));
			*at = ' ';
		}

		//
		// handle chunks
		//

		// any line with more than 2 bullets is some kind of index line, ignore it
		char* linker = readBuffer-1;
		unsigned int n = 0;
		while ((linker = strstr(linker+1,bulletchar))) ++n;
		if (n > 2) continue;


		while ((at = strstr(ptr,"<!--"))) // kill off private notes  <!-- Attention!  -->
		{
			char* end = strstr(at,"-->");
			if (end) memmove(at,end+3,strlen(end+2));
			else break;
		}

		// * [[aberation]] ([[aberration]])  ignore dictionary pretenses  - and really short lines
		if (*ptr == '*')
		{
			char* next = ReadCompiledWord(ptr,word);
			if (*word == '[')
			{
				char junk[MAX_WORD_SIZE];
				 next = ReadCompiledWord(next,junk);
				 if (*junk == '(') continue;	// just ignore this
				 next = ReadCompiledWord(next,junk);
				 next = ReadCompiledWord(next,junk);
				 if (!*junk) continue; 
			}
		}

		while (*ptr == ':') ++ptr; // skip over tab marks- BUG--  they may indicate stand alone lines in a line item. we'd want to use periods at end of line

		if (*ptr == '*') // denote a bullet item
		{
			if (text && *content) 	
			{
				fprintf(out,"%s\r\n",content);
				len += strlen(content) + 2;
				*content = 0;
			}
			bullet = true;
			while (*ptr == '*') ++ptr; 
		}

		// header lines
		if (*ptr == '=' && ptr[1] == '=')
		{
			killheading = false;
			span = citex = squ = prex = mathx = galleryx = includex = 0; // header closes anything we overlooked
			while (*ptr == '=') ++ptr; // skip to end of start
			char* end = strchr(ptr,'=');
			if (end) *end = 0; 
			size_t x = strlen(ptr);
			if (x > (MAX_WORD_SIZE-3)) x = MAX_WORD_SIZE-3;
			strncpy(heading,ptr,x);
			heading[x] = 0;

			if (*content) // close out old content
			{
				fprintf(out,"%s\r\n",content);
				*content = 0;
			}
			if (strstr(heading,"Sources") || strstr(heading,"sources") || strstr(heading,"urther reading") || strstr(heading,"ditions") || strstr(heading,"ebsites") || strstr(heading,"ibliography") || strstr(heading,"eferences") || strstr(heading,"xternal link"))// ignore sections listing other websites
			{
				killheading = true;
				*heading = 0;
			}
			continue;
		}

		if (strstr(ptr,"<page")) // skip to start of a page
		{
			ptr = strstr(ptr,"<page");
			
			if (len > size) // start in new file, this file is getting too big
			{
				char outfile[MAX_WORD_SIZE];
				fclose(out);
				++id;
				sprintf(outfile,"%s/file%d.txt",directoryout,id); // the output file
				out = FopenUTF8Write(outfile);
				len = 0;
				Log(STDUSERLOG,"Starting file: %s\r\n", outfile);
			}
			span = citex = includex = galleryx = mathx = prex = squ = 0;
			paragraph = false;
			*content = 0;
			*titlename = 0;
			*heading = 0;

			page = true;
			killheading = false;
			title = false;
			countSquiggle = 0;
			text = false;
			header = false;
			bullet = false;
			pendingtextclose = false;
			table = 0;
			superscript = false;
			subscript = false;
			italic = false;
			center = false;
			bold = false;
		}
		
		if (!span && !squ && !prex && !mathx && !galleryx && !includex && FlushEmbedded(ptr,"<ref","</ref>",citex)) continue;
		if (!span && !squ && !prex && !mathx && !galleryx && FlushEmbedded(ptr,"<includeonly","</includeonly>",includex)) continue;
		if (!span && !squ && !prex && !mathx && FlushEmbedded(ptr,"<gallery","</gallery>",galleryx)) continue;
		if (!span && !squ && !prex && FlushEmbedded(ptr,"<math","</math>",mathx)) continue; 
		if (!squ && !span && FlushEmbedded(ptr,"<pre","</pre>",prex)) continue;  // bug - what is this
		if (!squ && FlushEmbedded(ptr,"<span","</span>",span)) continue;  
		if (FlushEmbedded(ptr,"{{","}}",squ)) 
		{
			continue;  //  wikimedia templates
		}
		
		unsigned int oldlen = 0;
		char* oldoriginal = 0;

		while (ptr && *ptr)
		{
			ptr = SkipWhitespace(ptr);
			while (*ptr == '#' || *ptr == ':' || *ptr == ';' ) {++ptr;} // skip these

			char* original = ptr;	// before this iteration
			unsigned int lexn = strlen(ptr);
			if (oldoriginal == ptr && oldlen == lexn) // no progress
			{
				text = false;
				break;
			}
			oldoriginal = ptr;
			oldlen = lexn;
			ptr = ReadCompiledWord(ptr,word,true);

			// page end (article end)
			char* end = strstr(word,"</page>");
			if (end) 
			{
				page = false;
				title = false;
				text = false;
				*end = 0;
			}

			// titles
			end = strstr(word,"<title");
			if (end  && page) 
			{
				killheading = false;
				countSquiggle = 0;
				text = false;
				header = false;
				bullet = false;
				pendingtextclose = false;
				table = 0;
				text = false;
				superscript = false;
				subscript = false;
				italic = false;
				center = false;
				bold = false;
				title = true;
				paragraph = false;
				*titlename = 0;
				end = strchr(end,'>');
				if (end) memmove(word,end+1,strlen(end));
			}
			end = strstr(word,"</title>");
			if (end  && page) 
			{
				title = false;
				*end = 0;
				char* at = SkipWhitespace(word);
				if (*at)
				{
					size_t lenx = strlen(at) + 2;
					if ((strlen(titlename) + lenx) < (MAX_WORD_SIZE-3))
					{
						strcat(titlename," "); // any leading piece adds to title
						strcat(titlename,at);
					}
				}
				if (strchr(titlename,':') || strchr(titlename,'/')) // discard unusual articles, like: Wikipedia:AutoWikiBrowser/Typos
				{
					// Log(STDUSERLOG,"Discarding page about %s\r\n",titlename);
					*titlename = 0;
					page = false;
				}
				if (strstr(titlename,"disambiguation"))
				{
					// Log(STDUSERLOG,"Discarding disambiguation page about %s\r\n",titlename);
					*titlename = 0;
					page = false;
				}
			}
			// title substance
			if (title)
			{
				char* at = SkipWhitespace(word);
				if (*at)
				{
					size_t lenx = strlen(at) + 1;
					if ((strlen(titlename) + lenx) < (MAX_WORD_SIZE-3))
					{
						strcat(titlename," "); // any leading piece adds to title
						strcat(titlename,at);
					}
				}
				if (strlen(titlename) > 500) title = false;
				continue;
			}

			// text zones
			if (pendingtextclose)
			{
				char* e = strchr(original,'>');
				if (!e) continue;
				pendingtextclose = false;
				text = true;
				ptr = e + 1;
				continue;
			}
			end = strstr(word,"<text");
			if (end && page) // cant initiate text unless we saw a page and approved of any title.
			{
				paragraph = true;
				page = true;
				countSquiggle = 0;
				title = false;
				header = false;
				bullet = false;
				pendingtextclose = false;
				table = 0;
				superscript = false;
				subscript = false;
				italic = false;
				center = false;
				bold = false;

				*content = 0;
				end = strchr(end,'>');
				if (!end)
				{
					pendingtextclose = true;
					continue;
				}
				text = true; 
				memmove(word,end+1,strlen(end));
			}
			end = strstr(word,"</text>");
			if (!end && strstr(original,"-- interwiki --")) // cross language wiki links at end before close
			{
				text = false;
				*ptr = 0;
				end = SkipWhitespace(content);
				if (*end) 
				{
					fprintf(out,"%s\r\n",content);
					len += strlen(content) + 2;
				}
				*content = 0;	
				continue;
			}
			if (end  && text) 
			{
				if (end != word) // separate token from other stuff which might be kept
				{
					*end = 0;
					ptr = original;
					end =  strstr(ptr,"</text>");
					memmove(end+1,end,strlen(end)+1);
					*end = ' ';
					ptr = end + 1; // resume at end but accept stuff here

				}
				else // end at start
				{
					ptr = original;
					end = strstr(ptr,"</text>");
					ptr = end + 7;
					text = false;
					end = SkipWhitespace(content);
					if (*end) 
					{
						fprintf(out,"%s\r\n",content);
						len += strlen(content) + 2;
					}
					*content = 0;	
					continue;
				}
			}
			if (!text || killheading) continue; // either this heading's text is unacceptable or we aren't doing txt right now
			// process the text
			
			char* squiggle = strchr(word,'{');
			if (squiggle)
			{
				*squiggle = 0; // truncate word here
				char* endsquiggle = strchr(original,'{');
				ptr = endsquiggle + 1;
				if (squiggle == word) // is at start of token, absorb count and try again
				{
					countSquiggle += 1;
					continue;
				}
				else memmove(endsquiggle+1,endsquiggle,strlen(endsquiggle)+1); // is middle of token, separate it for later review
			}
			squiggle = strchr(word,'}');
			if (squiggle)
			{
				*squiggle = 0; // truncate word here
				char* endsquiggle = strchr(original,'}');
				ptr = endsquiggle + 1;
				if (squiggle == word) // is at start of token, absorb count and try again
				{
					countSquiggle -= 1;
					continue;
				}
				else memmove(endsquiggle+1,endsquiggle,strlen(endsquiggle)+1); // is middle of token, separate it for later review
			}
			if (countSquiggle) 
				continue;	 // ignore junk within squiggles
		
			char* start = word; 
			
			// handle anchors
			if (*start == '<' && start[1] == 'a' && start[2] == ' ') //<a href="/wiki/Month" title="Month">month</a>
			{
				char* end = strchr(start,'>');
				if (end) ptr = end + 1;
				else ptr = strchr(ptr,'>');

				continue;
			}
			char* at = strstr(start,"</");
			if (at) *at = 0;

			if (*start == '-' && start[1] == '-') continue; // line

			// strip embedded italic/bold format 
			char* format = strstr(word,"''");
			if (format)
			{
				format = strstr(original,"''");
				char* endstart = format;
				while (*++endstart == '\''){;}
				memmove(format,endstart,strlen(endstart)+1); 
				ptr = original;
				continue; // try again having removed the marker
			}
			if (StripEmbedded(word,ptr,original,"<sup","</sup>",superscript,true)) continue; 
			if (StripEmbedded(word,ptr,original,"<sub","</sub>",subscript,true)) continue; 
			if (StripEmbedded(word,ptr,original,"<i","</i>",italic,true)) continue; 
			if (StripEmbedded(word,ptr,original,"<center","</center>",center,true)) continue; 
			if (StripEmbedded(word,ptr,original,"<b","</b>",bold,true)) continue; 

			// strip embedded  links  [[ ]] and web link [http:...xxx ]
			char* link = strstr(word,"[[");
			if (!link) link = strstr(word,"[http");
			if (link)
			{
				if (link[1] == '[') link = strstr(original,"[[");
				else 
					link = strstr(original,"[http");

				// special category stuff
				// [[Category:English mathematicians|Turing, Alan]]
				if (!strnicmp(link,"[[category:",11))
				{
					char* end = strstr(link,"]]");
					if (end)
					{
						*end = 0;
						char* vert = strchr(link,'|');
						if (vert) *vert = 0;
						fprintf(out,"    [category]  %s \r\n",link+11);
						ptr = end+2;
						continue;
					}
				}

				// scan forward
				char* at = link + 1; // at the 2nd [
				// skip over http link
				char junk[MAX_WORD_SIZE];
				if (*at != '[') // http link
				{
					at = ReadCompiledWord(at,junk) - 1; // skip over http content
					if (strchr(junk,']')) at = strchr(link,']') - 1; // link is the only content and close was attached
				}
				unsigned int bracketCounter = 1; 
				char* endlink = 0;
				bool hadcolon = false;
				char hold[MAX_WORD_SIZE * 4];
				char* holdstart = hold;
				char* holdptr = hold;
				bool opensquiggle = false;
				bool image = !strnicmp(at+1,"image:",6);
				while (*++at)
				{
					if ((holdptr-hold) > ((MAX_WORD_SIZE * 4) - 2)) break; // something isnt right
					*holdptr++ = *at; // copy content
					if (*at == '{') opensquiggle = true;
					if (*at == '|') // discard all prior info
					{
						holdptr = holdstart;
						*holdptr = 0;
						hadcolon = false;
						continue;
					}
					if (*at == ':') 
					{
						hadcolon = true;
						continue;
					}
					if (!strnicmp(at,"<ref",4)) // internal ref
					{
						char* end = strstr(at,"</ref>");
						if (end)
						{
							--holdptr;
							at = end + 6;
							continue;
						}
					}
					
					if (*at == '}' && !opensquiggle && at[1] == '}') // revise as close ] as they made a typo
					{
						*at = ']';
						at[1] = ']';
					}
					if (*at == '[' && at[1] == '[')  // nested stuff to be displayed
					{
						--holdptr;	// remove hold on this
						*holdptr++ = ' '; // space it
						holdstart = holdptr;
						++bracketCounter;
						++at;
					}
					else if (*at == ']' ) // in case they dont close it correctly, accept a single close
					{
						--holdptr;	// remove hold on this
						--bracketCounter;
						endlink = at;
						if (at[1] == ']') ++at;  // points at last ]
						if (bracketCounter && (at-link) > 200 && !image) // image text can last a while
							bracketCounter = 0;	// wrong? force end
					}
					if (bracketCounter == 0) // true end of area found (may have nested brackets)
					{
						*endlink = 0;	// the close mark is done
						if (hadcolon) holdptr = hold; // drop all content
						break; // balanced out
					}
				}
				ptr =  (*at) ? (at+1) : at; // assume failure to close like: [[except [[kelsey grammar]]
				if (image) holdptr = hold;	// cancel all findings
				if (holdptr != hold)
				{
					if (*ptr == '\'' && ptr[1] == '\'') // closing italics
					{
						while (*++ptr == '\''){;}
					}
					else while (IsAlphaUTF8OrDigit(*ptr) || *ptr == '\'' ) *holdptr++ = *ptr++; // copy any leftover like [[hit]]s
					*holdptr++ = ' '; // close it off
					*holdptr = 0;
					if (strlen(hold) > (MAX_WORD_SIZE-3)) hold[MAX_WORD_SIZE-3] = 0;
					strcpy(word,hold);	 // declare all this to be displayed
				}
				else continue; // no text
			}

			if (*start == '&') // convert other special web character by removal
			{
				end = strchr(start,';');
				if (end) memmove(start,end+1,strlen(end));
			}
			if (!strnicmp(start,"ndash;",6) || !strnicmp(start,"mdash;",6)) // badly formed constant removal
			{
				end = strchr(start,';');
				if (end) memmove(start,end+1,strlen(end));
			}
			if (!*start) continue; // no text remaining

			if (!stricmp(start,"redirect")) // ignore a redirect body
			{
				text = false;
				continue;
			}

			if (*titlename) // drop title now
			{
				if (strstr(content,"may refer to")) // disambiguation
				{
					text = false;
					continue;
				}

				fprintf(out,"\r\n[title] %s\r\n  ",titlename);
				*titlename = 0;
			}

			// actual text now
			if (*heading) // only show heading if text materializes
			{
				fprintf(out,"  [heading] %s\r\n",heading);
				*heading = 0;
				paragraph = true;
			}
			if (bullet) // drop the bullet now that we found text
			{
				fprintf(out,"    [*] ");
				paragraph = false;
				bullet = false;
			}
			size_t lenx = strlen(start);
			if (lenx > (MAX_WORD_SIZE-3)) // limit
			{
				lenx = MAX_WORD_SIZE -3;
				start[lenx] = 0;
			}
			if (*content && (strlen(content) + lenx) > (MAX_WORD_SIZE - 100)) // dont accumulate, dump the old text, getting too big
			{
				fprintf(out,"%s\r\n",content);
				*content = 0;
			}
			if (paragraph)
			{
				paragraph = false;
				strcat(content,"[p] ");
			}
			strcat(content," ");
			strcat(content,start);
		}
	}
	fclose(in);

	} // end MAIN loop
	fclose(out);
}

/////////////////////////////////////////////////////
/// SYSTEM CONTROL COMMANDS
/////////////////////////////////////////////////////

static void C_Bot(char* name)
{
	char word[MAX_WORD_SIZE];
	name = ReadCompiledWord(name,word);
	MakeLowerCopy(computerID,word);
	strcpy(computerIDwSpace+1,computerID);
	strcat(computerIDwSpace," "); // trailing space
	if (shared) return; // pool doesnt require , just direct changeover since shared has the primary current context of all bots
	wasCommand = BEGINANEW;	// make system save revised user file
}



static void C_Build(char* input)
{
#ifndef DISCARDSCRIPTCOMPILER
	char oldlogin[MAX_WORD_SIZE];
	char oldbot[MAX_WORD_SIZE];
	char oldbotspace[MAX_WORD_SIZE];
	char oldloginname[MAX_WORD_SIZE];
	strcpy(oldlogin,loginID);
	strcpy(oldbot,computerID);
	strcpy(oldbotspace,computerIDwSpace);
	strcpy(oldloginname,loginName);
	char file[MAX_WORD_SIZE];
	char control[MAX_WORD_SIZE];
	input = ReadCompiledWord(input,file);
	input = SkipWhitespace(input);
	int spell = PATTERN_SPELL;
	bool reset = false;
	trace = 0;
	grade = 0;
	while (*input) 
	{
		input = ReadCompiledWord(input,control);
		if (!stricmp(control,"nospell")) spell = NO_SPELL;
		else if (!stricmp(control,"trace")) trace = TRACE_SCRIPT;
		else if (!stricmp(control,"nosubstitution")) spell = NO_SUBSTITUTE_WARNING;
		else if (!stricmp(control,"outputspell")) spell = OUTPUT_SPELL;
		else if (!stricmp(control,"gradek")) { grade = KINDERGARTEN; spell = OUTPUT_SPELL;}
		else if (!stricmp(control,"grade2")) { grade = (KINDERGARTEN|GRADE1_2); spell = OUTPUT_SPELL;}
		else if (!stricmp(control,"grade4")) { grade = (KINDERGARTEN|GRADE1_2|GRADE3_4); spell = OUTPUT_SPELL;}
		else if (!stricmp(control,"grade6")) { grade = (KINDERGARTEN|GRADE1_2|GRADE3_4|GRADE5_6); spell = OUTPUT_SPELL;}
		else if (!stricmp(control,"reset")) reset = true;
		else if (!stricmp(control,"keys"))
		{
			remove("TMP/keys.txt");
			spell = NOTE_KEYWORDS;
		}
	}
	size_t len = strlen(file);
	ClearTemps();
	if (!*file) Log(STDUSERLOG,"missing build label");
	else
	{
		sprintf(logFilename,"%s/build%s_log.txt",users,file); //   all data logged here by default
		FILE* in = FopenUTF8Write(logFilename);
		if (in) fclose(in);
		Log(STDUSERLOG,"ChatScript Version %s  compiled %s\r\n",version,compileDate);

		char word[MAX_WORD_SIZE];
		sprintf(word,"files%s.txt",file);
		buildId = (file[len-1] == '0') ? BUILD0 : BUILD1; // global so SaveCanon can work
		ReadTopicFiles(word,buildId,spell); 
		if (!stricmp(computerID,"anonymous")) *computerID = 0;	// use default
		CreateSystem();
		systemReset = (reset) ? 2 : 1;
	}
	// refresh current user data lost when we rebooted the system
	strcpy(loginID,oldlogin);
	strcpy(computerID,oldbot);
	strcpy(computerIDwSpace,oldbotspace);
	strcpy(loginName,oldloginname);
	trace &= -1 ^ TRACE_SCRIPT;
#endif
}  

static void C_Quit(char* input)
{
	Log(STDUSERLOG,"Exiting ChatScript via Quit\r\n");
	quitting = true;
}

static void C_Restart(char* input)
{
	char initialInput[MAX_WORD_SIZE];
	*initialInput = 0;
	trace = 0;
	ClearUserVariables();
	CloseSystem();
	CreateSystem();
	InitStandalone();
	if (!server)
	{
		printf("\r\nEnter user name: ");
		ReadALine(mainInputBuffer,stdin);
		printf("\r\n");
		if (*mainInputBuffer == '*') // let human go first
		{
			memmove(mainInputBuffer,mainInputBuffer+1,strlen(mainInputBuffer));
			printf("\r\nEnter starting input: ");
			ReadALine(initialInput,stdin);
			printf("\r\n");
		}
		echo = false;
		PerformChat(mainInputBuffer,computerID,initialInput,callerIP,mainOutputBuffer);
	}
	else Log(STDUSERLOG,"System restarted\r\n");
}

static void C_User(char* username)
{
	// fake a login of user
	strcpy(loginID,username);
	sprintf(logFilename,"%s/%slog-%s.txt",users,GetUserPath(loginID),loginID); // user log goes here
	wasCommand = BEGINANEW;	// make system save revised user file
}

///////////////////////////////////////////////
/// SERVER COMMANDS
///////////////////////////////////////////////

static void C_Flush(char* x)
{
	FlushCache();
}


///////////////////////////////////////////////////
/// WORD INFORMATION
///////////////////////////////////////////////////

static void DrawSynsets(MEANING M)
{
	unsigned int index = Meaning2Index(M);
	WORDP D = Meaning2Word(M);
	unsigned int limit =  GetMeaningCount(D);
	if (!limit)
	{
		MEANING T = MakeMeaning(D,0);
		Log(STDUSERLOG," %s",WriteMeaning(T,true)); // simple member
	}
	for (unsigned int i = 1; i <= limit; ++i)
	{
		if (index && i != index) continue;
		MEANING at = GetMeanings(D)[i];
		unsigned int n = 0;
		MEANING T = MakeMeaning(D,i);
		Log(STDUSERLOG,"%s ",WriteMeaning(T,true)); // simple member
		while ((at &= (INDEX_BITS|MEANING_BASE)) != (T & (INDEX_BITS|MEANING_BASE))) // find the correct ptr to return. The marked ptr means OUR dict entry is master, not that the ptr points to.
		{
			Log(STDUSERLOG,"%s ",WriteMeaning(at,true)); // simple member
			WORDP X = Meaning2Word(at);
			unsigned int ind = Meaning2Index(at);
			at = GetMeanings(X)[ind];
			if (++n >= 20) break; // force an end arbitrarily
		}
	}
	Log(STDUSERLOG,"\r\n "); 
}

static void DrawDownHierarchy(MEANING T,unsigned int depth,unsigned int limit,bool sets)
{
	if (sets) limit = 1000;
    if (depth >= limit || !T) return;
    WORDP D = Meaning2Word(T);
	if (D->inferMark == inferMark) return;	

	D->inferMark = inferMark;
    unsigned int index = Meaning2Index(T);
    unsigned int size = GetMeaningCount(D);
    if (!size) size = 1; 
	if (*D->word == '~') // show set members
	{
		if (D->internalBits & HAS_EXCLUDE) MarkExclude(D);

		FACT* F = GetObjectNondeadHead(D);
		unsigned int i = 0;
		while (F)
		{
			if (F->verb == Mmember)
			{
				if (trace == TRACE_HIERARCHY) TraceFact(F);
				MEANING M = F->subject;
				WORDP S = Meaning2Word(M);
				if (S->inferMark != inferMark)
				{
					if (*S->word == '~' && (depth + 1) < limit) // expand to lower level
					{
						Log(STDUSERLOG,"\r\n");
						for (unsigned int j = 0; j < (depth*2); ++j) Log(STDUSERLOG," "); // depth inclusive because tabbing for next level
						Log(STDUSERLOG,"%s ",WriteMeaning(M)); // simple member
						DrawDownHierarchy(M,depth+1,limit,sets);
						Log(STDUSERLOG,"\r\n");
						for (unsigned int j = 0; j < (depth*2); ++j) Log(STDUSERLOG," ");
					}
					else DrawSynsets(M);
					if ( ++i >= 10)
					{
						Log(STDUSERLOG,"\r\n");
						for (unsigned int j = 0; j < (depth*2); ++j) Log(STDUSERLOG," ");
						i = 0;
					}
				}
			}
			F = GetObjectNondeadNext(F);
		}
		return;
	}

    for (unsigned int k = 1; k <= size; ++k) //   for each meaning of this dictionary word
    {
        if (index)
		{
			if (k != index) continue; //   not all, just one specific meaning
			T = GetMaster(GetMeaning(D,k)); 
		}
		else 
		{
			if (GetMeaningCount(D)) T = GetMaster(GetMeaning(D,k));
			else T = MakeMeaning(D); //   did not request a specific meaning, look at each in turn
		}

        //   for the current T meaning
		char* gloss = GetGloss(Meaning2Word(T),Meaning2Index(T));
		if (!gloss) gloss = "";
        if (depth++ == 0 && size)  Log(STDUSERLOG,"\r\n<%s.%d => %s %s\r\n",D->word,k,WriteMeaning(T),gloss); //   header for this top level meaning is OUR entry and MASTER
        int l = 0;
        while (++l) //   find the children of the meaning of T
        {
			MEANING child = (limit >= 1) ? FindChild(T,l) : 0; //   only headers sought
            if (!child) break;
			if (sets) //   no normal words, just a set hierarchy
			{
				WORDP D = Meaning2Word(child);
				if (*D->word != '~') continue;
			}

			 //   child and all syn names of child
            for (unsigned int j = 0; j <= (depth*2); ++j) Log(STDUSERLOG," "); 
   			gloss = GetGloss(Meaning2Word(child),Meaning2Index(child));
			if (!gloss) gloss = "";
			Log(STDUSERLOG,"%d. (%s) ",depth,gloss);
			DrawSynsets(child);

			// below child master
			DrawDownHierarchy(child,depth,limit,sets);
        } //   end of children for this value
        --depth;
    }
}

static void DumpConceptPath(MEANING T) // once you are IN a set, the path can be this
{
	int k = 0;
	while (++k)
	{
		MEANING parent = FindSetParent(T,k); //   next set we are member of
		if (!parent)  break;

		WORDP D = Meaning2Word(parent);	// topic or concept
		if (D->internalBits & HAS_EXCLUDE) // prove no violation
		{
			FACT* F = GetObjectNondeadHead(D);
			while (F)
			{
				if (F->verb == Mexclude)
				{
					WORDP E = Meaning2Word(F->subject);
					if (E->inferMark == inferMark) break;
				}
				F = GetObjectNondeadNext(F);
			}
			if (F) continue;	// exclusion in effect
		}
		WORDP E = Meaning2Word(parent);
		if (E->inferMark != inferMark) 
		{
			E->inferMark = inferMark;
			*meaningLimit++ = parent;
		}
	}
}

static void ShowConcepts(MEANING T)
{
 	MEANING parent;
	unsigned int count;
	WORDP E = Meaning2Word(T);
	unsigned int index = Meaning2Index(T);
    if (*E->word != '~' && index == 0)  // at a base word
	{
		DumpConceptPath(T); // what is it a member of direclty

		//   then do concepts based on this word...
		unsigned int size = GetMeaningCount(E);
		if (!size) size = 1;	//   always at least 1, itself
		//   immediate sets of this base
		for  (unsigned int k = 1; k <= size; ++k)
		{
			if (index && k != index) continue; //   not all, just correct meaning

			//   get meaningptr spot facts are stored (synset head)
			if (!GetMeaningCount(E) ) T = MakeMeaning(E);	//   a generic since we have no meanings
			else 
			{
				if (GetMeaning(E,k) & SYNSET_MARKER) T = MakeMeaning(E,k); // we are master
				else T = GetMaster(GetMeaning(E,k)) | GETTYPERESTRICTION(GetMeaning(E,k)); 
			}
			DumpConceptPath(T); 
		}

		//   up one wordnet hierarchy based on each meaning
		for  (unsigned int k = 1; k <= size; ++k)
		{
			if (index && k != index) continue; //   not all, just correct meaning

			//   get meaningptr spot facts are stored (synset head)
			if (!GetMeaningCount(E) ) T = MakeMeaning(E);	//   a generic since we have no meanings
			else 
			{
				if (GetMeaning(E,k) & SYNSET_MARKER) T = MakeMeaning(E,k); // we are master
				else T = GetMaster(GetMeaning(E,k)) | GETTYPERESTRICTION(GetMeaning(E,k)); 
			}
			count = 0;
			while ((parent =  FindSynsetParent(T,count++))) ShowConcepts(parent); // immediate wordnet hierarchy
		}
	}
	else if (index != 0) //    always synset nodes above the base
	{
		count = 0;
		while ((parent =  FindSynsetParent(T,count++))) DumpConceptPath(parent); // sets of next parent level up
		count = 0;
		while ((parent =  FindSynsetParent(T,count++))) ShowConcepts(parent); // and follow next parent level up
	}
	else  DumpConceptPath(T); // track this synset to the next level
}

static void C_Concepts(char* input)
{
	char word[MAX_WORD_SIZE];
	ReadCompiledWord(input,word);
	MEANING M = ReadMeaning(word,false);
	if (!M) return;
	M = GetMaster(M);
	Log(STDUSERLOG,"%s: ",word);
	NextInferMark();

	meaningList = (MEANING*) AllocateBuffer();
	meaningLimit = meaningList;

	// check substitutes
	WORDP D = Meaning2Word(M);
	if (D->internalBits & HAS_SUBSTITUTE)
	{
		D = GetSubstitute(D);
		if (D && *D->word == '~')  *meaningLimit++ = MakeMeaning(D); 
	}

	char alter[MAX_WORD_SIZE];
	sprintf(alter,"<%s",word);
	D = FindWord(alter);
	if (D && D->internalBits & HAS_SUBSTITUTE)
	{
		D = GetSubstitute(D);
		if (D && *D->word == '~')   *meaningLimit++ = MakeMeaning(D); 
	}
	
	sprintf(alter,"<%s>",word);
	D = FindWord(alter);
	if (D && D->internalBits & HAS_SUBSTITUTE)
	{
		D = GetSubstitute(D);
		if (D &&*D->word == '~')   *meaningLimit++ = MakeMeaning(D); 
	}

	 *meaningLimit++ = M;

	// check concepts and topics
	while (meaningList < meaningLimit) 
	{
		WORDP E = Meaning2Word(*meaningList);
		if (*E->word == '~') Log(STDUSERLOG,(E->internalBits & TOPIC) ? (char*) "T%s " : (char*) "%s ",E->word);
		ShowConcepts(*meaningList++);
	}
	Log(STDUSERLOG,"\n");

	FreeBuffer();
}

static void C_Down(char* input)
{
	char word[MAX_WORD_SIZE];
	input = ReadCompiledWord(input,word);
	input = SkipWhitespace(input);
    int limit = atoi(input);
    if (!limit) limit = 1; //   top 2 level only (so we can see if it has a hierarchy)
	input = SkipWhitespace(input);
	NextInferMark();
	MEANING M = ReadMeaning(word,false);
	M = GetMaster(M);
    DrawDownHierarchy(M,1,limit+1,!stricmp(input,"sets"));
	Log(STDUSERLOG,"\r\n");
}

static void FindXWord(WORDP D, uint64 pattern)
{
	if (D->word && MatchesPattern(D->word,(char*) pattern)) Log(STDUSERLOG,"%s\r\n",D->word);
}

static void C_FindWords(char* input)
{
	WalkDictionary(FindXWord,(uint64) input);
}

static bool TestSetPath(MEANING T,unsigned int depth) // once you are IN a set, the path can be this
{
	WORDP D = Meaning2Word(T);
	if (D->inferMark == inferMark || depth > 100) return false;
	D->inferMark = inferMark;
	int k = 0;
	while (++k)
	{
		MEANING parent = FindSetParent(T,k); //   next set we are member of
		if (!parent)  break;
		WORDP D = Meaning2Word(parent);	// topic or concept
		if (trace) Log(STDUSERLOG,"%s\r\n",D->word);
		if (D == topLevel) return true;
		if (TestSetPath(parent,depth+1)) return true; // follow up depth first
	}
	return false;
}

static bool TestUpHierarchy(MEANING T,int depth)
{
    if (!T) return false;

    WORDP E = Meaning2Word(T);
	if (E == topLevel) return true;
	unsigned int index = Meaning2Index(T);
    if (depth == 0)  
	{
		if (TestSetPath(T,depth)) return true;	
		if (*E->word == '~') return false;	// not a word

		//   then do concepts based on this word...
		unsigned int size = GetMeaningCount(E);
		if (!size) size = 1;	//   always at least 1, itself

		//   draw wordnet hierarchy based on each meaning
		for  (unsigned int k = 1; k <= size; ++k)
		{
			if (index && k != index) continue; //   not all, just correct meaning

			//   get meaningptr spot facts are stored (synset head)
			if (!GetMeaningCount(E) ) T = MakeMeaning(E);	//   a generic since we have no meanings
			else 
			{
				if (GetMeaning(E,k) & SYNSET_MARKER) T = MakeMeaning(E,k); // we are master
				else T = GetMaster(GetMeaning(E,k)); 
			}
			if (TestSetPath(T,depth)) return true;
			unsigned int count = 0;
			MEANING parent;
			while ((parent = FindSynsetParent(T,count++)))
			{
				//   walk wordnet hierarchy
				if (TestSetPath(parent,depth)) return true;
				if (TestUpHierarchy(parent,depth+1)) return true; //   we find out what sets PARENT is in (will be none- bug)
			}
		}
	}
	else //    always synset nodes
	{
		E->inferMark = inferMark; // came this way
		unsigned int count = 0;
		MEANING parent;
		while ((parent = FindSynsetParent(T,count++)))
		{
			//   walk wordnet hierarchy
			if (TestSetPath(parent,depth)) return true;
			if (TestUpHierarchy(parent,depth+1)) return true; //   we find out what sets PARENT is in (will be none- bug)
		}
	}
	return false;
}

static void TestSet(WORDP D,uint64 flags)
{
	if (!(D->properties & flags) || !(D->systemFlags & AGE_LEARNED)) return; // only want simple words to be tested
	if (D->properties & NOUN_ABSTRACT) return; // not abstract
	MEANING M = MakeMeaning(D);
	NextInferMark();
	if (TestUpHierarchy(M,0)) return;
	Log(STDUSERLOG,"%s\r\n",D->word);
}

static void C_Nonset(char* buffer) // NOUN ~sizes
{
	char type[MAX_WORD_SIZE];
	buffer = ReadCompiledWord(buffer,type);
	uint64 kind  = FindValueByName(type);
	if (!kind) return;
	WORDP D = FindWord(buffer);
	topLevel = D;
	WalkDictionary(TestSet,kind);
}

static void C_HasFlag(char* buffer)
{
	bool notflag = false;
	char type[MAX_WORD_SIZE];
	buffer = ReadCompiledWord(buffer,type);
	WORDP D = FindWord(type); // name of set
	buffer = SkipWhitespace(buffer);
	if (*buffer == '!')
	{
		notflag = true;
		++buffer;
	}
	buffer = ReadCompiledWord(buffer,type);
	uint64 flag  = FindSystemValueByName(type); // flag to find or !find
	FACT* F = GetObjectNondeadHead(D);
	while (F)
	{
		if (F->verb == Mmember)
		{
			WORDP S = Meaning2Word(F->subject);
			if (S->systemFlags & flag)
			{
				if (!notflag) Log(STDUSERLOG,"%s has %s\r\n",S->word,type);
			}
			else
			{
				if (notflag) Log(STDUSERLOG,"%s lacks %s\r\n",S->word,type);
			}
		}
		F = GetObjectNondeadNext(F);
	}
}

static bool HitTest(WORDP D, WORDP set) // can we hit this
{
	if (D->inferMark == inferMark) return false;	// been here already
	D->inferMark = inferMark;
	FACT* F = GetSubjectNondeadHead(D);
	while (F)
	{
		if (F->verb == Mmember)
		{
			WORDP E = Meaning2Word(F->object);
			if (E == set) return true;
			if (*E->word == '~') 
			{
				if (HitTest(E,set)) return true;
			}
		}
		F = GetSubjectNondeadNext(F);
	}

	return false;
}

static void C_Overlap(char* buffer)
{
	char set1[MAX_WORD_SIZE];
	char set2[MAX_WORD_SIZE];
	buffer = ReadCompiledWord(buffer,set1);
	WORDP E = FindWord(set1);
	if (!E || E->word[0] != '~')
	{
		printf("no such set %s\r\n",set1);
		return;
	}
	buffer = ReadCompiledWord(buffer,set2);
	WORDP D = FindWord(set2);
	if (!E || E->word[0] != '~')
	{
		printf("no such set %s\r\n",set2);
		return;
	}
	Log(STDUSERLOG,"These members of %s are also in %s:\r\n",set1,set2);

	// walk members of set1, seeing if they intersect set2
	FACT* F = GetObjectNondeadHead(E);
	while (F)
	{
		E = Meaning2Word(F->subject);
		if (F->verb == Mmember && *E->word != '~') // see if word is member of set2
		{
			NextInferMark();
			if (HitTest(E,D)) Log(STDUSERLOG,"%s\r\n",E->word);
		}
		F = GetObjectNondeadNext(F);
	}

}

static bool DumpSetPath(MEANING T,unsigned int depth) // once you are IN a set, the path can be this
{
	int k = 0;
	if (depth > 20)
	{
		printf("Hierarchy too deep-- recursive?");
		return false;
	}	
	while (++k)
	{
 		MEANING parent = FindSetParent(T,k); //   next set we are member of
		if (!parent)  break;

		WORDP D = Meaning2Word(parent);	// topic or concept
		if (D->internalBits & HAS_EXCLUDE) // prove no violation
		{
			FACT* F = GetObjectNondeadHead(D);
			while (F)
			{
				if (F->verb == Mexclude)
				{
					WORDP E = Meaning2Word(F->subject);
					if (E->inferMark == inferMark) break;
				}
				F = GetObjectNondeadNext(F);
			}
			if (F) continue;	// exclusion in effect
		}

        Log(STDUSERLOG,"    ");
		for (unsigned int j = 0; j < depth; ++j) Log(STDUSERLOG,"   "); 
		WORDP E = Meaning2Word(parent);
		if (E->internalBits & TOPIC) Log(STDUSERLOG,"T%s \r\n",WriteMeaning(parent)); 
		else Log(STDUSERLOG,"%s \r\n",WriteMeaning(parent)); 
		if (!DumpSetPath(parent,depth+1)) return false; // follow up depth first
	}
	return true;
}

static bool DumpUpHierarchy(MEANING T,int depth)
{
    if (!T) return true;
	if (depth > 20)
	{
		printf("Hierarchy too deep-- recursive?");
		return false;
	}

    WORDP E = Meaning2Word(T);
	unsigned int restrict = GETTYPERESTRICTION(T);
	E->inferMark = inferMark; // came this way
	unsigned int index = Meaning2Index(T);
    if (depth == 0)  
	{
		Log(STDUSERLOG,"\r\nFor %s:\r\n",E->word); 
		Log(STDUSERLOG," Set hierarchy:\r\n"); 

		if (!DumpSetPath(T,depth)) return false;	
		if (*E->word == '~') return true;	// we are done, it is not a word

		//   then do concepts based on this word...
		unsigned int meaningCount = GetMeaningCount(E);
		unsigned int size = meaningCount;
		if (!size) size = 1;	//   always at least 1, itself
		Log(STDUSERLOG," Wordnet hierarchy:\r\n"); 

		//   draw wordnet hierarchy based on each meaning
		for  (unsigned int k = 1; k <= size; ++k)
		{
			if (index && k != index) continue; //   not all, just correct meaning
			MEANING M = (meaningCount) ? GetMeaning(E,k) : 0;
			if (restrict && !(GETTYPERESTRICTION(M) & restrict)) continue; // not valid meaning

			//   get meaningptr spot facts are stored (synset head)
			if (!GetMeaningCount(E) ) T = MakeMeaning(E);	//   a generic since we have no meanings
			else 
			{
				if (GetMeaning(E,k) & SYNSET_MARKER) T = MakeMeaning(E,k) | GETTYPERESTRICTION(GetMeaning(E,k)); // we are master
				else T = GetMaster(GetMeaning(E,k)) | GETTYPERESTRICTION(GetMeaning(E,k)); 
			}
			WORDP D1 = Meaning2Word(T);
			unsigned int restrict = GETTYPERESTRICTION(T);
			Log(STDUSERLOG,"  ");
			Log(STDUSERLOG,"%s~%d:",E->word,k);
			if (restrict & NOUN) Log(STDUSERLOG,"N   ");
			else if (restrict & VERB) Log(STDUSERLOG,"V   ");
			else if (restrict & ADJECTIVE) Log(STDUSERLOG,"Adj ");
			else if (restrict & ADVERB) Log(STDUSERLOG,"Adv ");
			else if (restrict & PREPOSITION) Log(STDUSERLOG,"Prep ");
			char* gloss = GetGloss(D1,Meaning2Index(T));
			if (gloss) Log(STDUSERLOG," %s ",gloss);
			Log(STDUSERLOG,"\r\n"); 
		
			if (!DumpSetPath(T,depth)) return false;
			unsigned int count = 0;
			MEANING parent;
			while ((parent =  FindSynsetParent(T,count++)))
			{
				//   walk wordnet hierarchy
				WORDP P = Meaning2Word(parent);
				Log(STDUSERLOG,"   ");
				for (int j = 0; j < depth; ++j) Log(STDUSERLOG,"   "); 
				Log(STDUSERLOG," is %s ",WriteMeaning(parent)); //   we show the immediate parent
				char* gloss = GetGloss(P,Meaning2Index(parent));
				if (gloss) Log(STDUSERLOG," %s ",gloss);
				Log(STDUSERLOG,"\r\n"); 
				if (!DumpSetPath(parent,depth)) return false;
				if (!DumpUpHierarchy(parent,depth+1)) return false; //   we find out what sets PARENT is in (will be none- bug)
			}
		}
	}
	else //    always synset nodes
	{
		unsigned int count = 0;
		MEANING parent;
		while ((parent =  FindSynsetParent(T,count++)))
		{
			//   walk wordnet hierarchy
			WORDP P = Meaning2Word(parent);
			unsigned int index = Meaning2Index(parent);
			Log(STDUSERLOG,"   ");
			for (int j = 0; j < depth; ++j) Log(STDUSERLOG,"   "); 
			Log(STDUSERLOG," is %s",WriteMeaning(parent)); //   we show the immediate parent
			char* gloss = GetGloss(P,index);
			if (gloss) Log(STDUSERLOG," %s ",gloss);
			Log(STDUSERLOG,"\r\n");
			if (!DumpSetPath(parent,depth)) return false;
			if (!DumpUpHierarchy(parent,depth+1)) return false; //   we find out what sets PARENT is in (will be none- bug)
		}
	}
	return true;
}

static void C_Up(char* input)
{
 	char word[MAX_WORD_SIZE];
	NextInferMark();
	ReadCompiledWord(input,word);
	MEANING M = ReadMeaning(word,false);
	M = GetMaster(M);
	DumpUpHierarchy(M,0);
}

static void C_Word(char* input)
{
	char word[MAX_WORD_SIZE];
	char junk[MAX_WORD_SIZE];
	while(ALWAYS)
	{
		input = ReadCompiledWord(input,word);
		if (!*word) break;
		input = SkipWhitespace(input);
		int limit= 0;
		if (IsDigit(*input))
		{
			input = ReadCompiledWord(input,word);
			limit = atoi(junk);
		}
		if (*word == '"')
		{
			size_t len = strlen(word);
			word[len-1] = 0;
			memmove(word,word+1,len);
		}
		DumpDictionaryEntry(word,limit);  
	}
} 	

static void WordDump(WORDP D,uint64 flags)
{
	if (!strstr(D->word,"_music")) return;
	Log(STDUSERLOG,"%s %d\r\n",D->word,GetMeaningCount(D));
}

static void C_WordDump(char* input)
{
	WalkDictionary(WordDump,0);

#ifdef JUNK
	WORDP D = FindWord(input);
	if (!D) 
	{
		Log(STDUSERLOG,"No such set %s\r\n",input);
		return;
	}
	FACT* F = GetObjectNondeadHead(D);
	while (F)
	{
		if (F->verb == Mmember)
		{
			if (D->systemFlags & VERB_TAKES_VERBINFINITIVE)
				Log(STDUSERLOG,"redundant %s\r\n",D->word);
		}
		F = GetObjectNondeadNext(F);
	}
#endif
} 	

//////////////////////////////////////////////////
/// SYSTEM INFO
/////////////////////////////////////////////////

static void FindConceptWord(WORDP D, uint64 pattern)
{
	char* prefix = (char*) pattern;
	if (D->internalBits & CONCEPT && !(D->internalBits & TOPIC))
	{
		if (!*prefix) Log(STDUSERLOG,"%s\r\n",D->word);
		else if ( MatchesPattern(D->word,prefix)) Log(STDUSERLOG,"%s\r\n",D->word);
	}
}

static void C_Context(char* input)
{
	int i = contextIndex;
	while (ALWAYS)
	{
		if (--i == -1) i = MAX_RECENT - 1;
		if ( i == (int)contextIndex) break;
		if (InContext(topicContext[i], labelContext[i])) Log(STDUSERLOG,"%s: %s %d\r\n",GetTopicName(topicContext[i]),labelContext[i],inputContext[i]);
	}
	Log(STDUSERLOG,"end of contexts");
}

static void C_ConceptList(char* input)
{
	WalkDictionary(FindConceptWord,(uint64) input);
}

static void C_Commands(char* x)
{
	int i = 0;
	CommandInfo *routine;
	while ((routine = &commandSet[++i]) && routine->word) Log(STDUSERLOG,"%s - %s\r\n",routine->word,routine->comment); // linear search
}

static void C_Definition(char* x)
{
	char name[MAX_WORD_SIZE];
	ReadCompiledWord(x,name);
	WORDP D = FindWord(name);
	if (!D || !(D->internalBits & FUNCTION_NAME)) Log(STDUSERLOG,"No such name\r\n");
	else if ((D->internalBits & FUNCTION_BITS) == IS_PLAN_MACRO) Log(STDUSERLOG,"Plan macro\r\n");
	else if (D->x.codeIndex && (D->internalBits & FUNCTION_BITS) != IS_TABLE_MACRO) Log(STDUSERLOG,"Engine API function\r\n");
	else if ((D->internalBits & FUNCTION_BITS) == IS_OUTPUT_MACRO) Log(STDUSERLOG,"output macro: %s\r\n",D->w.fndefinition+1); // skip arg count
	else Log(STDUSERLOG,"pattern macro: %s\r\n",D->w.fndefinition+1); // skip arg count
}

static void DumpMatchVariables()
{
	for (unsigned int i = 0; i <=  MAX_WILDCARDS; ++i)
	{
		Log(STDUSERLOG,"_%d (%d-%d) =  %s (%s)\r\n",i,WILDCARD_START(wildcardPosition[i]),WILDCARD_END(wildcardPosition[i]),wildcardOriginalText[i],wildcardCanonicalText[i]);  // spot wild cards can be stored
	}
}

static void C_Variables(char* input)
{
	if (!stricmp(input,"system")) DumpSystemVariables();
	else if (!stricmp(input,"user")) DumpUserVariables(); 
	else if (!stricmp(input,"match")) DumpMatchVariables(); 
	else // all
	{
		DumpUserVariables();
		DumpSystemVariables();
		DumpMatchVariables(); 
		Log(STDUSERLOG,"Max Buffers used %d\r\n",maxBufferUsed);
		Log(STDUSERLOG,"%s\r\n",ShowPendingTopics());
	}
} 	

static void C_Functions(char* input)
{
	DumpFunctions();
}

static void C_Identify(char* input)
{
	IdentifyCode(input);
	Log(STDUSERLOG,"%s",input);
}

static void ShowMacro(WORDP D,uint64 junk)
{
	if (!(D->internalBits & FUNCTION_NAME)) {;} // not a function or plan
	else if ((D->internalBits & FUNCTION_BITS) == IS_PLAN_MACRO) Log(STDUSERLOG,"plan: %s (%d)\r\n",D->word,D->w.planArgCount);
	else if (D->x.codeIndex) {;} //is system function (when not plan)
	else if (D->internalBits & IS_PATTERN_MACRO && D->internalBits & IS_OUTPUT_MACRO) Log(STDUSERLOG,"dualmacro: %s (%d)\r\n",D->word,MACRO_ARGUMENT_COUNT(D));
	else if (D->internalBits & IS_PATTERN_MACRO) Log(STDUSERLOG,"patternmacro: %s (%d)\r\n",D->word,MACRO_ARGUMENT_COUNT(D));
	else if (D->internalBits & IS_OUTPUT_MACRO) 	Log(STDUSERLOG,"outputmacro: %s (%d)\r\n",D->word,MACRO_ARGUMENT_COUNT(D));
	else if (D->internalBits & IS_PLAN_MACRO) Log(STDUSERLOG,"tablemacro: %s (%d)\r\n",D->word,MACRO_ARGUMENT_COUNT(D));
}

static void C_Macros(char* input)
{
	WalkDictionary(ShowMacro,0);
}

static void ShowQuery(WORDP D,uint64 junk)
{
	if (D->internalBits & QUERY_KIND) 
	{
		if (D->internalBits & BUILD0) Log(STDUSERLOG,"BUILD0 ");
		if (D->internalBits & BUILD1) Log(STDUSERLOG,"BUILD1 ");
		Log(STDUSERLOG,"Query: %s \"%s\"\n",D->word,D->w.userValue);
	}
}

static void C_Queries(char* input)
{
	WalkDictionary(ShowQuery,0);
}

static void TracedFunctions(WORDP D,uint64 junk)
{
	if (D->internalBits & MACRO_TRACE) Log(STDUSERLOG,"%s\r\n",D->word);
}

static void C_TracedFunctions(char* input) 
{
	WalkDictionary(TracedFunctions,0);
}

static void TracedTopics(WORDP D,uint64 junk)
{
	if (D->internalBits & TOPIC) 
	{
		unsigned int topic = FindTopicIDByName(D->word);
		topicBlock* block = TI(topic);
		if (block->topicDebug) Log(STDUSERLOG,"%s %d\r\n",D->word,block->topicDebug);
	}
}
static void C_TracedTopics(char* input)
{
	WalkDictionary(TracedTopics,0);
}

void C_MemStats(char* input)
{
	unsigned int factUsedMemKB = ( factFree-factBase) * sizeof(FACT) / 1000;
	unsigned int dictUsedMemKB = ( dictionaryFree-dictionaryBase) * sizeof(WORDENTRY) / 1000;
	// dictfree shares text space
	unsigned int textUsedMemKB = ( stringBase-stringFree)  / 1000;
	unsigned int bufferMemKB = (maxBufferLimit * maxBufferSize) / 1000;
	
	unsigned int used =  factUsedMemKB + dictUsedMemKB + textUsedMemKB + bufferMemKB;
	used +=  (userTopicStoreSize + userTableSize) /1000;

	char buf[MAX_WORD_SIZE];
	strcpy(buf,StdIntOutput(factFree-factBase));
	Log(STDUSERLOG,"Used: words %s (%dkb) facts %s (%dkb) text %dkb buffers %d overflowBuffers %d\r\n",
		StdIntOutput(dictionaryFree-dictionaryBase), 
		dictUsedMemKB,
		buf,
		factUsedMemKB,
		textUsedMemKB,
		bufferIndex,overflowIndex);

	unsigned int factFreeMemKB = ( factEnd-factFree) * sizeof(FACT) / 1000;
#ifndef SEPARATE_STRING_SPACE 
	char* endDict = (char*)(dictionaryBase + maxDictEntries);
	unsigned int textFreeMemKB = ( stringFree- endDict) / 1000;
#else
	unsigned int textFreeMemKB = ( stringFree- stringEnd) / 1000;
#endif

	Log(STDUSERLOG,"Free:  fact %dKb text %dKB\r\n\r\n",factFreeMemKB,textFreeMemKB);
}

static void C_Who(char*input)
{
	Log(STDUSERLOG,"%s talking to %s\r\n",loginID,computerID);
}

//////////////////////////////////////////////////////////
//// COMMAND SYSTEM
//////////////////////////////////////////////////////////

void InitCommandSystem() // set dictionary to match builtin functions
{
}

TestMode Command(char* input,char* output,bool scripted)
{
	char word[MAX_WORD_SIZE];
	fromScript = scripted;
	bool oldecho = echo;
	if (!scripted) echo = true;	// see outputs sent to log file on console also
	static bool commandsAllowed = true;		// local suppression
	
	if (!commandsAllowed && !stricmp(input,":commands on")) 
	{
		commandsAllowed =  true;
		if (!scripted) Log(STDUSERLOG,":commands enabled\r\n");
		echo = oldecho;
		return COMMANDED;
	}

	if (!stricmp(input,":commands off"))
	{
		commandsAllowed = false;
		if (!scripted) Log(STDUSERLOG,":commands disabled\r\n");
		echo = oldecho;
		return COMMANDED;
	}
	if (!commandsAllowed) 
	{
		echo = oldecho;
		return FAILCOMMAND;
	}

	int i = 0;
	CommandInfo *routine = NULL;
	input = SkipWhitespace(input);
	while ((routine = &commandSet[++i]) && routine->word) 
	{
		size_t len = strlen(routine->word);
		if (!strnicmp(routine->word,input,len) && !IsLegalNameCharacter(input[len])) break;
		if (input[1] == routine->word[1] && input[2] == routine->word[len-1] && !IsAlphaUTF8(input[3])) break; // 2 char abbrev, not unique
	}
	if (routine->word) 
	{
		CommandInfo* info;
		info = &commandSet[i];
		input = SkipWhitespace(input+strlen(info->word));
		char data[MAX_WORD_SIZE];
		if (strlen(input) > (MAX_WORD_SIZE-1)) 
		{
			ReportBug("Command data too large- %s %s\r\n",word,input)
			echo = oldecho;
			return COMMANDED; // ignore it
		}
		strcpy(data,input);
		TrimSpaces(data,false); // safe from change
		wasCommand = COMMANDED;
		testOutput = output;
		if (output) *output = 0;
		(*info->fn)(data);
		testOutput = NULL;
		if (strcmp(info->word,":trace")   && strcmp(info->word,":echo") && !prepareMode) echo = oldecho;
		if (scripted) echo = oldecho;
		return wasCommand;
	}
	echo = oldecho;
	return FAILCOMMAND; 
}

//////////////////////////////////////////////////////////
//// TOPIC INFO
//////////////////////////////////////////////////////////

void C_Gambits(char* buffer)
{
	buffer = SkipWhitespace(buffer);
	unsigned int topic = FindTopicIDByName(buffer);
	if (!topic) 
	{
		Log(STDUSERLOG,"No such topic %s\r\n",buffer);
		return;
	}
	
	char* base = GetTopicData(topic);  
	int ruleID = 0;
	topicBlock* block = TI(topic);
	unsigned int* map = block->gambitTag;
	ruleID = *map;
	unsigned int* indices =  block->ruleOffset;
	unsigned int n = 0;
	while (ruleID != NOMORERULES)
	{
		char* ptr = base + indices[ruleID]; // the gambit 
		char* end = strchr(ptr,ENDUNIT);
		*end = 0;
		++n;
		char label[MAX_WORD_SIZE];
		char pattern[MAX_WORD_SIZE];
		char* output = GetPattern( ptr,label,pattern);
		if (strlen(pattern) == 4) *pattern = 0;
		if (*label) strcat(label,":");
		if (!UsableRule(topic,ruleID)) Log(STDUSERLOG,"- %d %s %s    %s\r\n",n,label,output,pattern);
		else Log(STDUSERLOG,"%d  %s %s    %s\r\n",n,label,output,pattern);
		*end = ENDUNIT;
		ruleID = *++map;
	}
}

void C_Pending(char* buffer)
{
	Log(STDUSERLOG,"Pending topics: %s\r\n", ShowPendingTopics());
}

static void CountConcept(WORDP D, uint64 count)
{
	if (D->internalBits & CONCEPT && !(D->internalBits & TOPIC))
	{
		unsigned int* ctr = (unsigned int*) count;
		++*ctr;
	}
}

static bool EmptyReuse(char* output, unsigned int topic)
{
	if (!strnicmp(output,"^reuse (",8) && !strchr(output,'.')) // dont care about cross topic jumps
	{
		char label[MAX_WORD_SIZE];
		ReadCompiledWord(output+8,label);
		bool fulllabel = false;
		bool crosstopic = false;
		int id;
		char* rule = GetLabelledRule(topic,label,"1",fulllabel,crosstopic,id,topic);
		if (rule)
		{
			char pattern[MAX_WORD_SIZE];
			char* output1 = SkipWhitespace(GetPattern(rule,label,pattern));
			return (*output1 == '`');
		}
	}
	return false;
}

static void C_TopicStats(char* input)
{
	unsigned int totalgambits = 0;
	unsigned int totalresponders = 0;
	unsigned int totalrejoinders = 0;
	unsigned int totalquestions = 0;
	unsigned int totalstatements = 0;
	unsigned int totalempties = 0;
	unsigned int totaldual = 0;
	unsigned int conceptCount = 0;
	bool normal = false;
	if (!stricmp(input,"normal")) // show only normal topics
	{
		normal = true;
		*input = 0;
	}
	WalkDictionary(CountConcept,(uint64) &conceptCount);
	unsigned int topicCount = 0;

	size_t len = 0;
	char* x = strchr(input,'*');
	if (x) len = x - input;
	else if (*input == '~') len = strlen(input);

	for (unsigned int i = 1; i <= numberOfTopics; ++i) 
	{
		if (len && strnicmp(GetTopicName(i),input,len)) continue;
		char* name = GetTopicName(i);
		char* data = GetTopicData(i);
		unsigned int flags = GetTopicFlags(i);
		if (flags & TOPIC_SYSTEM && normal) continue;
		++topicCount;
		unsigned int gambits = 0;
		unsigned int responders = 0;
		unsigned int rejoinders = 0;
		unsigned int empties = 0;
		int id = 0;
		while (data && *data)
		{
			char label[MAX_WORD_SIZE];
			char pattern[MAX_WORD_SIZE];
			char* output = SkipWhitespace(GetPattern(data,label,pattern));
			bool norule = EmptyReuse(output,i);
			if (!*output || *output == '`' || norule) 
			{
				if (*data < 'a' ||*data > 'q') 
					++empties; // we dont care if rejoinder is empty.
				else  ++rejoinders;
			}
			else if (TopLevelGambit(data)) ++gambits;
			else if (TopLevelRule(data)) ++responders;
			else ++rejoinders;

			if (*data == QUESTION) ++totalquestions;
			else if (*data == STATEMENT) ++totalstatements;
			else if (*data == STATEMENT_QUESTION) ++totaldual;

			data = FindNextRule(NEXTRULE,data,id);
		}
		totalgambits += gambits;
		totalresponders += responders;
		totalrejoinders += rejoinders;
		totalempties += empties;
		Log(STDUSERLOG,"    %s     gambits %d responders %d rejoinders %d empties %d\r\n", name,gambits,responders,rejoinders,empties);
	}
	unsigned int totalrules = totalgambits + totalresponders + totalrejoinders;
	Log(STDUSERLOG,"Concepts %d Topics %d rules %d empties %d\r\n  gambits %d  responders %d (?: %d s: %d  u: %d) rejoinders %d  \r\n",conceptCount,topicCount,totalrules,totalempties,totalgambits,totalresponders,totalquestions,totalstatements,totaldual,totalrejoinders);
}

static void C_TopicDump(char* input)
{
	FILE* out = FopenUTF8Write("TMP/tmp.txt");
	size_t len = 0;
	char* x = strchr(input,'*');
	if (x) len = x - input;
	else if (*input == '~') len = strlen(input);

	for (unsigned int i = 1; i <= numberOfTopics; ++i) 
	{
		char* name = GetTopicName(i);
		if (!*name) continue;
		if (len && strnicmp(name,input,len)) continue;
		topicBlock* block = TI(i);
		fprintf(out,"topic: %s %s Bot: %s\r\n",name,DisplayTopicFlags(i),block->topicRestriction ? block->topicRestriction : (char*)"all ");
		// dump keywords
		WORDP D = FindWord(name);
		FACT* F = GetObjectNondeadHead(MakeMeaning(D));
		fprintf(out,"Keywords: ");
		while (F)
		{
			if (F->verb == Mmember) fprintf(out,"%s ",Meaning2Word(F->subject)->word);
			F = GetObjectNondeadNext(F);
		}
		fprintf(out," Rules: \r\n");
		// dump rules
		char* data = GetTopicData(i);
		int id = 0;
		while (data && *data)
		{
			char* end = strchr(data,'`');
			*end = 0;
			fprintf(out,"%s`\r\n",data-JUMP_OFFSET);
			*end = '`';
			data = FindNextRule(NEXTRULE,data,id);
		}
		fprintf(out,"000 x\r\n"); // end of topic
	}
	fclose(out);
	Log(STDUSERLOG,"Done.\r\n");
}

static bool shownItem;

static void TrackFactsUp(MEANING T,FACT* G,WORDP base) //   show what matches up in unmarked topics
{ 
    if (!T) return;
	WORDP D = Meaning2Word(T);
	unsigned int index = Meaning2Index(T);
	unsigned int flags = GETTYPERESTRICTION(T);
	if (!flags) flags = ESSENTIAL_FLAGS;
	if (D->internalBits & TOPIC) // is in some other topic
	{
		if (D->inferMark == inferMark) return;
		D->inferMark = inferMark;
		unsigned int flags = GetTopicFlags(FindTopicIDByName(D->word));
		if (flags & TOPIC_SYSTEM) return;	// dont report system intersects
		char word[MAX_WORD_SIZE];
		if (!shownItem)
		{
			shownItem = true;
			Log(STDUSERLOG,"  %s: ",base->word);
		}
		if (Meaning2Word(G->subject) == base) sprintf(word," %s ",D->word);
		else sprintf(word," %s(%s)",D->word,WriteMeaning(G->subject));
		Log(STDUSERLOG,"%s ",word);
		return;	
	}
	else if (D->internalBits & CONCEPT)
	{
		if (D->inferMark == inferMark) return;	// already marked
		D->inferMark = inferMark;
	}
	FACT* F = GetSubjectNondeadHead(D); 
	while (F) 
	{
		WORDP object = Meaning2Word(F->object);
		if ((F->verb == Mmember || F->verb == Mis) && object->inferMark != inferMark) 
		{
			unsigned int restrict = GETTYPERESTRICTION(F->subject);
			if (restrict) // type restricted member
			{
				if (!( restrict & flags ))
				{
					F = GetSubjectNondeadNext(F);
					continue;
				}
			}

			//  meaning restriction 
			if (index == Meaning2Index(F->subject)) // match generic or specific 
			{
				WORDP E = Meaning2Word(F->subject);
				if (*E->word == '~') TrackFactsUp(F->object,G,base);
				else TrackFactsUp(F->object,F,base);
			}
		}
		F = GetSubjectNondeadNext(F);
	}
}

static void TabInset(unsigned int depth,bool eol)
{
	if (eol) Log(STDUSERLOG,"\r\n");
	for (unsigned int i = 0; i < depth; ++i) Log(STDUSERLOG,"  ");
}

static void TrackFactsDown(MEANING M,FACT* F,unsigned int depth,size_t& length,bool display) // look at each keyword of this set
{
	WORDP D = Meaning2Word(M);
	if (D->inferMark == inferMark) return;	// already marked
	D->inferMark = inferMark;
	if (shownItem)
	{
		shownItem = false;
		Log(STDUSERLOG,"\r\n");
	}
	if (*D->word == '~')  // its a set or topic-- nest and do the set
	{
		if (display)
		{
			if ( length != depth)  TabInset(depth,true);
			// header
			Log(STDUSERLOG,"%s\r\n",D->word);
			// indent 
			TabInset(depth+2,true);
			length = depth + 2;
		}
		else TrackFactsUp(M,F,D); // what is it a member of
	    // concept keywords
		FACT* F = GetObjectNondeadHead(D);
		while (F)
		{
			if (F->verb == Mmember)	TrackFactsDown(F->subject,F,depth+2,length,display); // what is a member of this concept
			F = GetObjectNondeadNext(F);
		}
		if (display)
		{
			TabInset(depth,true); // end of concept keywords // restore indent 
			length = depth * 2;
		}
	}
	else // displaying a word of a set
	{
		unsigned int index = Meaning2Index(M);
		if (display)
		{
			char word[MAX_WORD_SIZE];
			if (!index)	sprintf(word,"%s ",D->word);
			else sprintf(word,"%s~%d ",D->word,index);
			Log(STDUSERLOG,"%s",word);
			size_t wlen = strlen(word)  + 1;
			length += wlen;
			while (wlen < 20) // force each word to be 20 wide
			{
				Log(STDUSERLOG," ");
				++wlen;
				++length;
			}
			if (length > 120) // avoid long lines
			{
				TabInset(depth,true);
				length = depth * 2;
			}
		}
		else if (index) // need to propogate down - but might be huge-- dont display
		{
			int l = 0;
			M = GetMaster(M); // master meaning
			while (++l) //   find the children of the meaning of T
			{
				MEANING child = FindChild(M,l);
				if (!child) break;
				TrackFactsDown(child,F,depth+2,length,false);
			} //   end of children for this value
		}
		else
		{
			FACT* F = GetSubjectNondeadHead(D); // who comes from this word
			while (F)
			{
				if (F->verb == Mmember)	TrackFactsUp(F->object,F,D); 
				F = GetSubjectNondeadNext(F);
			}
			unsigned int size = GetMeaningCount(D); // all meanings up
			for  (unsigned int k = 1; k <= size; ++k)
			{
				MEANING M = GetMeaning(D,k);
				TrackFactsUp(M,F,D); // anyone else refers to this meaning?
				MEANING parent = FindSetParent(M,0); //   next set we are member of
				TrackFactsUp(parent,F,D);
			}
		}
	}
}

static void C_Topics(char* input)
{
	PrepareSentence(input,true,true);	
	impliedSet = 0;
	KeywordTopicsCode(NULL);
	for (unsigned int i = 1; i <=  FACTSET_COUNT(0); ++i)
	{
		FACT* F = factSet[0][i];
		WORDP D = Meaning2Word(F->subject);
		WORDP N = Meaning2Word(F->object);
		unsigned int topic = FindTopicIDByName(D->word);
        char* name = GetTopicName(topic);
		Log(STDUSERLOG,"%s (%s) : ",name,N->word);
        //   look at references for this topic
        int start = -1;
		unsigned int startPosition = 0;
		unsigned int endPosition = 0;
        while (GetIthSpot(D,++start, startPosition,endPosition)) // find matches in sentence
        {
            // value of match of this topic in this sentence
            for (unsigned int k = startPosition; k <= endPosition; ++k) 
			{
				if (k != startPosition) Log(STDUSERLOG,"_");
				Log(STDUSERLOG,"%s",wordStarts[k]);
			}
			Log(STDUSERLOG," ");
		}
		Log(STDUSERLOG,"\r\n");
	}
	impliedSet = ALREADY_HANDLED;
	
}

static void C_TopicInfo(char* input)
{
	char word[MAX_WORD_SIZE];
	char* ptr = ReadCompiledWord(input,word);
	if (*word == '~' && word[1] == 0) 
	{
		if (inputRejoinderTopic == NO_REJOINDER) return;
		strcpy(word,GetTopicName(inputRejoinderTopic));
		input = ptr;
	}
	else if (*word == '~')  input = ptr;
	
	size_t len = 0;
	char* x = strchr(word,'*');
	if (x) len = x - word;
	else if (*word == '~') len = strlen(word);

	for (unsigned int topicid = 1; topicid <= numberOfTopics; ++topicid) 
	{
		if (!*GetTopicName(topicid)) continue;
		if (len && strnicmp(GetTopicName(topicid),word,len)) continue;
		topicBlock* block = TI(topicid);

		WORDP D = FindWord(GetTopicName(topicid));
		int rejoinderOffset = -1;
		if ((int)topicid == inputRejoinderTopic) rejoinderOffset = inputRejoinderRuleID;
		bool used = true;
		bool available = true;
		bool rejoinder = false;
		bool gambit = false;
		bool responder = false;
		bool keys = false;
		bool overlap = false;
		bool all = false;
		if (!*input) all = keys = overlap = gambit = responder = rejoinder = true; // show it all
		char* ptr = input;
		while (*ptr)
		{
			ptr = ReadCompiledWord(ptr,word); // restriction
			if (!*word) break;
			if (!stricmp(word,"used")) available = false;
			else if (!stricmp(word,"available")) used = false;

			else if (!stricmp(word,"rejoinder")) rejoinder = true;
			else if (!stricmp(word,"gambit")) gambit = true;
			else if (!stricmp(word,"responder")) responder = true;
			else if (!stricmp(word,"all")) rejoinder = gambit = responder = true;

			else if (!stricmp(word,"keys")) keys = true;
			else if (!stricmp(word,"overlap")) overlap = true;
		}
		if (!gambit && !responder && !rejoinder) used = available = false;
		if (all) 
		{
			Log(STDUSERLOG,"%s",DisplayTopicFlags(topicid));
			Log(STDUSERLOG,"Bot: %s\r\n",block->topicRestriction ? block->topicRestriction : (char*)"all");
			if (block->topicLastGambitted == 0 && block->topicLastRespondered == 0 && block->topicLastRejoindered == 0) Log(STDUSERLOG,"Seen: never visited");
			else Log(STDUSERLOG,"Seen: last gambit %d   last rejoinder %d  lastresponder\r\n", block->topicLastGambitted,block->topicLastRespondered,block->topicLastRejoindered);
		}

		if (keys) // display all keys (execpt recursive wordnet)
		{
			Log(STDUSERLOG,"\r\nTopic Keys: %s\r\n",D->word);
			NextInferMark();
			if (D->internalBits & HAS_EXCLUDE) MarkExclude(D);
			FACT* F = GetObjectNondeadHead(D);
			size_t length = 2;
			Log(STDUSERLOG,"  ");
			while (F)
			{
				shownItem = false;
				if (F->verb == Mmember) TrackFactsDown(F->subject,F,1,length,true); 
				F = GetObjectNondeadNext(F);
			}
			Log(STDUSERLOG,"\r\n");
		}
		shownItem = false;
		if (overlap)
		{
			FACT* F = GetObjectNondeadHead(D);
			NextInferMark();
			D->inferMark = inferMark;
			if (D->internalBits & HAS_EXCLUDE) MarkExclude(D);
			size_t length = 2;
			bool started = false;
			while (F)
			{
				if (F->verb == Mmember)
				{
					if (!started)
					{
						Log(STDUSERLOG,"\r\nTopic Key Overlap: %s\r\n",D->word);
						started = true;
					}
					if (shownItem) 
					{
						Log(STDUSERLOG,"\r\n");
						shownItem = false;
					}
					TrackFactsDown(F->subject,F,1,length,false); 
				}
				F = GetObjectNondeadNext(F);
			}
			Log(STDUSERLOG,"\r\n");
		}

		if ((used || available) && !gambit && !rejoinder && !responder) rejoinder = gambit = responder = true;

		unsigned int gambits = 0;
		unsigned int statements = 0;
		unsigned int questions = 0;
		unsigned int dual = 0;
		unsigned int rejoinders = 0;

		int id = 0;
		char* name = GetTopicName(topicid);
		char* data = GetTopicData(topicid);
		bool access = true;

		while (data && *data) // walk data
		{
			char* rule = ShowRule(data);
			if (*data == GAMBIT || *data == RANDOM_GAMBIT) ++gambits;
			else if (*data == QUESTION) ++questions;
			else if (*data == STATEMENT) ++statements;
			else if (*data == STATEMENT_QUESTION) ++dual;
			else  ++rejoinders;
			if (TopLevelRule(data))
			{
				access = UsableRule(topicid,id);
				if ((*data == GAMBIT || *data == RANDOM_GAMBIT) && !gambit) access = false;
				else if ((*data == QUESTION || *data == STATEMENT_QUESTION || *data == STATEMENT) && !responder) access = false;
				else if (!access) // no access exists
				{
					if (used) 
					{
						Log(STDUSERLOG,"  - %d(%d) %s\r\n",id,block->ruleOffset[id],rule);
						access = true;
					}
				}
				else // rule is accessible
				{
					if (available) Log(STDUSERLOG,"    %d(%d) %s\r\n",id,block->ruleOffset[id],rule);
					else access = false;
				}
			}
			else if (rejoinder) // inherits prior access
			{
				if (access)
				{
					unsigned int depth = *rule - 'a';
					while (depth--) Log(STDUSERLOG,"    "); // indent appropriately
					if (id == rejoinderOffset) Log(STDUSERLOG,"  ***  (%d) %s\r\n",REJOINDERID(id),rule); // current rejoinder
					else Log(STDUSERLOG,"       (%d) %s\r\n",REJOINDERID(id),rule);
				}
			}
			data = FindNextRule(NEXTRULE,data,id);
		}
		if (all) Log(STDUSERLOG,"%s(%d)  gambits: %d  responders: %d (?:%d s:%d u:%d)  rejoinders: %d\r\n", name,topicid,gambits,statements+questions+dual,statements, questions, dual,rejoinders);
	}
}

static void LoadDescriptions (char* file)
{
	FILE* in = FopenReadWritten(file);
	if (!in) return;
	char name[MAX_WORD_SIZE];
	char describe[MAX_WORD_SIZE];
	WORDP lock = dictionaryLocked;
	dictionaryLocked = 0; 

	while (ReadALine(readBuffer,in) >= 0 ) 
	{
		char *ptr = ReadCompiledWord(readBuffer,name);
		if (!*name) continue;
		ReadCompiledWord(ptr,describe);
		WORDP D = StoreWord(name);
		WORDP E = StoreWord(describe);
		AddInternalFlag(D,DEFINES);
		D->inferMark = MakeMeaning(E); 
	}
	dictionaryLocked = lock;
	fclose(in);
}

static void FreeDescriptions(WORDP D, uint64 junk)
{
	if (D->internalBits & DEFINES)
	{
		if (*D->word == '$'  || *D->word == '~' ) 
		{
			D->internalBits ^= DEFINES;
			D->inferMark = 0;
		}
	}
}

static void ListMacro(WORDP D, uint64 junk)
{
	if (*D->word == '^' ) 
	{
		unsigned int count = FACTSET_COUNT(3);
		factSet[3][++count] = CreateFact(MakeMeaning(D),MakeMeaning(StoreWord(":list")),MakeMeaning(StoreWord(":list")),FACTTRANSIENT|FACTDUPLICATE);
		if (count >= MAX_FIND) --count;
		SET_FACTSET_COUNT(3,count);  
	}
}

static void ListTopic(WORDP D, uint64 junk)
{
	if (*D->word == '~' && D->internalBits & TOPIC ) 
	{
		unsigned int count = FACTSET_COUNT(4);
		factSet[4][++count] = CreateFact(MakeMeaning(D),MakeMeaning(StoreWord(":list")),MakeMeaning(StoreWord(":list")),FACTTRANSIENT|FACTDUPLICATE);
		if (count >= MAX_FIND) --count;
		SET_FACTSET_COUNT(4,count);  
	}
}

static void C_List(char* input)
{
	bool all = false;
	bool sorted = true;
	char item[MAX_WORD_SIZE];
	char* ptr = ReadCompiledWord(input,item);
	if (!stricmp(item,"unsorted")) 
	{
		sorted = false;
		input = ptr;
	}
	else ptr = input;
	ptr = SkipWhitespace(ptr);	
	if (!*ptr) all = true;
	char word[MAX_WORD_SIZE];
	unsigned int count = 0;
	MEANING verb = MakeMeaning(StoreWord(":list"));
	if (all || strchr(input,'$')) // do permanent user variables
	{
		NextInferMark();
		for (unsigned int topicid = 1; topicid <= numberOfTopics; ++topicid) 
		{
			if (!*GetTopicName(topicid)) continue;
			int id = 0;
			char* data = GetTopicData(topicid);
			while (data && *data) // walk data
			{
				data = strstr(data,"$");
				if (!data) continue;
				data = ReadCompiledWord(data,word);
				if (!word[1] || (word[1] == '$' || IsDigit(word[1]))) continue; // ignore temp vars, $, and money
				char* at = word;
				while (*++at && (IsAlphaUTF8(*at) || IsDigit(*at) || *at == '-' || *at == '_'));
				*at = 0;
				WORDP D = StoreWord(word);
				if (D->inferMark == inferMark) continue;
				D->inferMark = inferMark;
				factSet[0][++count] = CreateFact(MakeMeaning(D),verb,verb,FACTTRANSIENT|FACTDUPLICATE);
				if (count >= MAX_FIND) --count;
			}
		}
		SET_FACTSET_COUNT(0,count);  
		if (sorted) SortFacts("@0subject",true);
	}
	if (all || strchr(input,'@'))
	{
		count = 0;
		for (unsigned int i = 0; i < MAX_FIND_SETS; ++i)
		{
			char word[MAX_WORD_SIZE];
			sprintf(word,"@%d",i);
			factSet[1][++count] = CreateFact(MakeMeaning(StoreWord(word)),verb,verb,FACTTRANSIENT|FACTDUPLICATE);
		}
		SET_FACTSET_COUNT(1,count);  
	}

	if (all || strchr(input,'_')) // match variables
	{
		count = 0;
		for (unsigned int i = 0; i <= MAX_WILDCARDS; ++i)
		{
			char word[MAX_WORD_SIZE];
			sprintf(word,"_%d",i);
			factSet[2][++count] = CreateFact(MakeMeaning(StoreWord(word)),verb,verb,FACTTRANSIENT|FACTDUPLICATE);
		}
		SET_FACTSET_COUNT(2,count);  
	}
	
	if (all || strchr(input,'^')) 
	{
		SET_FACTSET_COUNT(3,0);  
		WalkDictionary(ListMacro,0);
		if (sorted) SortFacts("@3subject",true);

	}
	if (all || strchr(input,'~')) 
	{
		SET_FACTSET_COUNT(4,0);  
		WalkDictionary(ListTopic,0);
		if (sorted) SortFacts("@4subject",true);
	}

	LoadDescriptions("TOPIC/describe0.txt");
	LoadDescriptions("TOPIC/describe1.txt");
	if (all || strchr(input,'$'))
	{
		count = FACTSET_COUNT(0);
		Log(STDUSERLOG,"User Variables:\r\n");
		for (unsigned int i = 1; i <= count; ++i)
		{
			WORDP D = Meaning2Word(factSet[0][i]->subject);
			if (D->internalBits & DEFINES) 
			{
				Log(STDUSERLOG,"    %s %s\r\n",D->word, Meaning2Word(D->inferMark)->word);
				D->internalBits ^= DEFINES;
			}
			else Log(STDUSERLOG,"    %s\r\n",D->word);
		}
	}

	if (all || strchr(input,'@'))
	{
		count = FACTSET_COUNT(1);
		Log(STDUSERLOG,"Fact Sets:\r\n");
		for (unsigned int i = 1; i <= count; ++i)
		{
			WORDP D = Meaning2Word(factSet[1][i]->subject);
			if (D->internalBits & DEFINES)
			{
				Log(STDUSERLOG,"    %s ",D->word);
				if ((setControl & (uint64) (1 << i))) Log(STDUSERLOG," SAVED ");
				Log(STDUSERLOG," %s\r\n",Meaning2Word(D->inferMark)->word);
				D->internalBits ^= DEFINES;
				D->inferMark = 0;
			}
		}
	}

	if (all || strchr(input,'_'))
	{
		count = FACTSET_COUNT(2);
		Log(STDUSERLOG,"Match Variables:\r\n");
		for (unsigned int i = 1; i <= count; ++i)
		{
			WORDP D = Meaning2Word(factSet[2][i]->subject);
			if (D->internalBits & DEFINES)
			{
				D->internalBits ^= DEFINES;
				Log(STDUSERLOG,"    %s %s\r\n",D->word, Meaning2Word(D->inferMark)->word);
				D->inferMark = 0;
			}
		}
	}

	if (all || strchr(input,'^')) 
	{
		count = FACTSET_COUNT(3);
		Log(STDUSERLOG,"User Macros:\r\n");
		for (unsigned int i = 1; i <= count; ++i)
		{
			WORDP D = Meaning2Word(factSet[3][i]->subject);
			if (D->internalBits & DEFINES) 
			{
				Log(STDUSERLOG,"    %s %s\r\n",D->word, Meaning2Word(D->inferMark)->word);
				D->internalBits ^= DEFINES;
				D->inferMark = 0;
			}
		}
	}

	if (all || strchr(input,'~')) 
	{
		count = FACTSET_COUNT(4);
		Log(STDUSERLOG,"Topics:\r\n");
		for (unsigned int i = 1; i <= count; ++i)
		{
			WORDP D = Meaning2Word(factSet[4][i]->subject);
			if (D->internalBits & DEFINES) 
			{
				Log(STDUSERLOG,"    %s %s\r\n",D->word, Meaning2Word(D->inferMark)->word);
				D->internalBits ^= DEFINES;
				D->inferMark = 0;
			}
		}
	}

	WalkDictionary(FreeDescriptions,0);
}

static void C_Where(char* input)
{
	unsigned int topic = FindTopicIDByName(input);
	if (topic)	Log(STDUSERLOG,"%s is from %s\r\n",input,GetTopicFile(topic));
}

//////////////////////////////////////////////////////////
//// FACT INFO
//////////////////////////////////////////////////////////

static void C_AllFacts(char* input)
{
	WriteFacts(FopenUTF8Write("TMP/facts.txt"),factBase);
}

static void C_Facts(char* input)
{
	char word[MAX_WORD_SIZE];
	char* ptr = ReadCompiledWord(input,word);
	FACT* G = NULL;
	WORDP D = NULL;
	unsigned int index = 0;
	FACT* F;
	if (*word == '(') // actual fact
	{
		char arg1[MAX_WORD_SIZE];
		char arg2[MAX_WORD_SIZE];
		char arg3[MAX_WORD_SIZE];
		ptr -= (strlen(word)-1) + 1;
		ptr = ReadCompiledWord(ptr,arg1);
		ptr = ReadCompiledWord(ptr,arg2);
		ptr = ReadCompiledWord(ptr,arg3);
		size_t len = strlen(arg3);
		if (arg3[len-1] == ')') arg3[len-1] = 0;	// remove trailing )
		G = FindFact(ReadMeaning(arg1,false),ReadMeaning(arg2,false),ReadMeaning(arg3,false),0); 
		if (!G) 
		{
			Log(STDUSERLOG,"No such facts\r\n");
			return;
		}
	}
	else if (*word == '@') // in a fact set
	{
		int set = GetSetID(word);
		if (set == ILLEGAL_FACTSET)
		{
			Log(STDUSERLOG,"Illegal fact set %s\r\n",word);
			return;
		}
		Log(STDUSERLOG,"Fact set %s: %d facts\r\n",word,FACTSET_COUNT(set));
		for (unsigned int i = 1; i <= FACTSET_COUNT(set); ++i)
		{
			TraceFact(factSet[set][i]);
		}
		return;
	}
	else
	{
		MEANING M = ReadMeaning(word,false);
		index = Meaning2Index(M);
		if (!M)
		{
			Log(STDUSERLOG,"No such meaning exists\r\n");
			return;
		}
		D = Meaning2Word(M);

	}
	F = (G) ? GetSubjectNondeadHead(G) :  GetSubjectNondeadHead(D);
	while (F)
	{
		if (index && F->subject != index) {;}
		else TraceFact(F);
		F = GetSubjectNondeadNext(F);
	}	
	F = (G) ? GetVerbNondeadHead(G) :  GetVerbNondeadHead(D);
	while (F)
	{
		if (index && F->verb != index)  {;}
		else TraceFact(F);
		F = GetVerbNondeadNext(F);
	}
	F = (G) ? GetObjectNondeadHead(G) :  GetObjectNondeadHead(D);
	while (F)
	{
		if (index && F->object != index)  {;}
		else TraceFact(F);
		F = GetObjectNondeadNext(F);
	}
}

static void C_UserFacts(char* input)
{
	if (!factLocked) return; // no user facts yet
	char* buffer = AllocateBuffer();
	for (unsigned int i = 1; i < MAX_FIND_SETS; ++i) 
    {
		if (!(setControl & (uint64) (1 << i))) continue; // purely transient stuff
		unsigned int count = FACTSET_COUNT(i);
		if (!count) continue;
		// save this set
		Log(STDUSERLOG,"Set %d[%d]\r\n",i,count); 
        for (unsigned int j = 1; j <= count; ++j)
		{
			char* fact = WriteFact(factSet[i][j],false,buffer,false,false);
			Log(STDUSERLOG, "%s  # %d\r\n",fact, Fact2Index(factSet[i][j]));
		}
    }
	FreeBuffer();
	FACT* F = factLocked;
	unsigned int count = 0;
	while (++F <= factFree)
	{
		char word[MAX_WORD_SIZE];
		++count;
		char* fact = WriteFact(F,false,word,false,false);
		Log(STDUSERLOG,"%s  # %d\r\n",fact,Fact2Index(F));
	}
	Log(STDUSERLOG,"user facts: %d\r\n",count);
}

//////////////////////////////////////////////////////////
//// DEBUGGING COMMANDS
//////////////////////////////////////////////////////////

static void C_Do(char* input)
{
	SAVEOLDCONTEXT()
	++volleyCount;
	responseIndex = 0;	// clear out data (having left time for :why to work)
	AddHumanUsed(":do");
	AddRepeatable(0);
	OnceCode("$cs_control_pre");
	currentRule = 0;
	currentRuleID = 0;
	currentRuleTopic =  currentTopicID = 0;
	char* data = AllocateBuffer();
	char* out = data;
	char* answer = AllocateBuffer();
#ifndef DISCARDSCRIPTCOMPILER
	hasErrors = 0;
	ReadOutput(input, NULL,out,NULL);
	if (hasErrors) Log(STDUSERLOG,"\r\nScript errors prevent execution.");
	else 
	{
		FunctionResult result;
		FreshOutput(data,answer,result);
		Log(STDUSERLOG,"   result: %s  output: %s\r\n",ResultCode(result),answer);
		AddResponse(answer);
	}
#else
	Log(STDUSERLOG,"Script compiler not installed.");
#endif
	FreeBuffer();
	FreeBuffer();
	RESTOREOLDCONTEXT()
	wasCommand = OUTPUTASGIVEN; // save results to user file
}

static void C_Silent(char* input)
{
	silent = !silent;
}

static void C_Retry(char* input)
{
	char file[MAX_WORD_SIZE];
	if (server && !serverRetryOK) return;

	char word[MAX_WORD_SIZE];
	ResetToPreUser();
	ResetSentence();
	char which[20];
	*which = 0;
	if (!strnicmp(SkipWhitespace(mainInputBuffer),":redo",5) && redo)
	{
		char* at = ReadCompiledWord(input,word); // input is after turn
		if (IsDigit(*word)) // retry depth
		{
			input = at;
			unsigned int n = atoi(word);
			sprintf(which,"%d",n);
			if (!*at) 
			{
				Log(STDUSERLOG,"You must supply input to go back. changing to :retry \r\n");
				*which = 0; // ordinary retry
			}
		}
	}
	input = SkipWhitespace(input);
	if (!*input) strcpy(mainInputBuffer,revertBuffer);
	else strcpy(mainInputBuffer,input);
	if (!server) printf("Retrying with: %s\r\n",mainInputBuffer);

	// get main user file
	sprintf(file,"%s/topic_%s_%s.txt",users,loginID,computerID);
	char name[MAX_WORD_SIZE];
	sprintf(name,"TMP/backup%s-%s_%s.bin",which,loginID,computerID);
	CopyFile2File(file,name,false);	
	char* buffer = FindUserCache(file); //  (does not trigger a read, assumes it has it in core)
	if (buffer) FreeUserCache(); // erase cache of user so it reads revised disk file

	// get shared file
	if (shared)
	{
		sprintf(file,"%s/topic_%s_%s.txt",users,loginID,"share");
		sprintf(name,"TMP/backup%s-share-%s_%s.bin",which,loginID,computerID);
		CopyFile2File(file,name,false);	
		buffer = FindUserCache(file); //  (does not trigger a read, assumes it has it in core)
		if (buffer) FreeUserCache(); // erase cache of user so it reads revised disk file
	}
	
	// load user from refreshed files
	char oldc;
	int oldCurrentLine;	
	int BOMvalue = -1; // get prior value
	BOMAccess(BOMvalue, oldc,oldCurrentLine); // copy out prior file access and reinit user file access
	ReadUserData();
	BOMAccess(BOMvalue, oldc,oldCurrentLine); 
}

static void C_Redo(char* input)
{
	C_Retry(input);
}

static void C_Log(char* input)
{
	Log(STDUSERLOG,"Log: %s\r\n",input);
}

static void C_Skip(char* buffer)
{
	unsigned int topic = GetPendingTopicUnchanged();
	if (!topic) 
	{
		Log(STDUSERLOG,"No pending topic\r\n");
		return;
	}
	topicBlock* block = TI(topic);
	unsigned int* offsets = block->ruleOffset;
	int n = atoi(SkipWhitespace(buffer));
	unsigned int* map = block->gambitTag;
	unsigned int ruleID = *map;
	char * rule = NULL;
	char* data = GetTopicData(topic);  
	while (ruleID != NOMORERULES)
	{
		rule = data + offsets[ruleID];
		if (TopLevelGambit(rule) && UsableRule(topic,ruleID) && --n == 0) SetRuleDisableMark(topic, ruleID);
		ruleID = *++map;
	}
	if (ruleID != NOMORERULES) Log(STDUSERLOG,"Next gambit of %s is: %s...\r\n",GetTopicName(topic),ShowRule(GetRule(topic,ruleID)));
	WriteUserData(0);
}

static void C_Show(char* input)
{
	char word[MAX_WORD_SIZE];
	input = ReadCompiledWord(input,word);
	char value[MAX_WORD_SIZE];
	*value = 0;
	bool set = atoi(value) ? true : false;
	if (*input) ReadCompiledWord(input,value);
	if (!stricmp(word,"all"))
	{
		if (*value) all = set;
		else all = !all;
		Log(STDUSERLOG,"All set to %d\n",all);
	}
	else if (!stricmp(word,"oob"))
	{
		if (*value) oob = set;
		else oob = !oob;
		Log(STDUSERLOG," oob set to %d\n",oob);
	}
	else if (!stricmp(word,"newline"))
	{
		if (*value) newline = set;
		else newline = !newline;
		Log(STDUSERLOG," newline set to %d\n",newline);
	}
	else if (!stricmp(word,"depth"))
	{
		if (*value) showDepth = set;
		else showDepth = !showDepth;
		Log(STDUSERLOG," showDepth set to %d\n",showDepth);
	}
	else if (!stricmp(word,"echo"))
	{
		if (*value) echo = set;
		else echo = !echo;
		Log(STDUSERLOG," echo set to %d\n",echo);
	}
	else if (!stricmp(word,"echoserver"))
	{
		if (*value) echoServer = set;
		else echoServer = !echoServer;
		Log(STDUSERLOG," echoServer set to %d\n",echoServer);
	}
	else if (!stricmp(word,"input"))
	{
		showInput = !showInput;
		Log(STDUSERLOG," input set to %d\n",showInput);
	}
	else if (!stricmp(word,"reject"))
	{
		showReject = !showReject;
		Log(STDUSERLOG," reject set to %d\n",showReject);
	}
	else if (!stricmp(word,"memory"))
	{
		showmem = !showmem;
		Log(STDUSERLOG," showmem set to %d\n",showmem);
	}	
	else if (!stricmp(word,"mark"))
	{
		showMark = !showMark;
		Log(STDUSERLOG," showMark set to %d\n",showMark);
	}
	else if (!stricmp(word,"number"))
	{
		if (*value) autonumber = set;
		else autonumber = !autonumber;
		Log(STDUSERLOG," autonumber set to %d\n",autonumber);
	}
	else if (!stricmp(word,"pos"))
	{
		if (*value) shortPos = set;
		else shortPos = !shortPos;
		Log(STDUSERLOG," Pos set to %d\n",shortPos);
	}
	else if (!stricmp(word,"serverLog"))
	{
		if (*value) serverLog = set;
		else serverLog = !serverLog;
		Log(STDUSERLOG," serverLog set to %d\n",serverLog);
	}
	else if (!stricmp(word,"stats"))
	{
		ruleCount = 0;
		if (*value) stats = set;
		else stats = !stats;
		Log(STDUSERLOG," stats set to %d\n",stats);
	}
	else if (!stricmp(word,"topic"))
	{
		if (*value) showTopic = set;
		else showTopic = !showTopic;
		Log(STDUSERLOG," topic set to %d\n",showTopic);
	}
	else if (!stricmp(word,"topics"))
	{
		if (*value) showTopics = set;
		else showTopics = !showTopics;
		Log(STDUSERLOG," topics set to %d\n",showTopics);
	}
	else if (!stricmp(word,"why"))
	{
		if (*value) showWhy = set;
		else showWhy = !showWhy;
		Log(STDUSERLOG," why set to %d\n",showWhy);
	}
} 

static void TraceTopicFunction(WORDP D, uint64 data)
{
	
	if (D->internalBits & TOPIC && D->word[0] ==  '~')
	{
		topicBlock* block = TI(D->x.topicIndex);
		if (block->topicDebug) 
		{
			Log(STDUSERLOG,"%s: \r\n",D->word);
			ShowTrace(block->topicDebug,false);
		}
	}
	else if (D->word[0] == '^' && (D->internalBits & (MACRO_TRACE|FN_NO_TRACE)))
	{
		if ((D->internalBits & FN_TRACE_BITS) == MACRO_TRACE) Log(STDUSERLOG,"%s: on\r\n",D->word);
		if ((D->internalBits & FN_TRACE_BITS) ==  (MACRO_TRACE|FN_NO_TRACE)) Log(STDUSERLOG,"%s: on off\r\n",D->word);
		if ((D->internalBits & FN_TRACE_BITS) ==  FN_NO_TRACE) Log(STDUSERLOG,"%s: off\r\n",D->word);
	}
}

static void ShowTrace(unsigned int bits, bool original)
{
	unsigned int general = (TRACE_VARIABLE|TRACE_MATCH);
	unsigned int mild = (TRACE_OUTPUT|TRACE_PREPARE|TRACE_PATTERN);
	unsigned int deep = (TRACE_JSON|TRACE_TOPIC|TRACE_FACT|TRACE_SAMPLE|TRACE_INFER|TRACE_HIERARCHY|TRACE_SUBSTITUTE|TRACE_VARIABLESET|TRACE_QUERY|TRACE_USER|TRACE_POS| TRACE_TCP|TRACE_USERFN|TRACE_USERCACHE|TRACE_SQL|TRACE_LABEL);

	// general
	if (bits & general) 
	{
		Log(STDUSERLOG,"Enabled simple: ");
		if (bits & TRACE_MATCH) Log(STDUSERLOG,"match ");
		if (bits & TRACE_VARIABLE) Log(STDUSERLOG,"variables ");
		Log(STDUSERLOG,"\r\n");
	}

	// mild detail
	if (bits & mild) 
	{
		Log(STDUSERLOG,"Enabled mild detail: ");
		if (bits & TRACE_OUTPUT) Log(STDUSERLOG,"output ");
		if (bits & TRACE_PREPARE) Log(STDUSERLOG,"prepare ");
		if (bits & TRACE_PATTERN) Log(STDUSERLOG,"pattern ");
		Log(STDUSERLOG,"\r\n");
	}
	// deep detail
	if (bits & deep) 
	{
		Log(STDUSERLOG,"Enabled deep detail: ");
		if (bits & TRACE_FACT) Log(STDUSERLOG,"fact ");
		if (bits & TRACE_INFER) Log(STDUSERLOG,"infer ");
		if (bits & TRACE_HIERARCHY) Log(STDUSERLOG,"hierarchy ");
		if (bits & TRACE_SUBSTITUTE) Log(STDUSERLOG,"substitute ");
		if (bits & TRACE_VARIABLESET) Log(STDUSERLOG,"varassign ");
		if (bits & TRACE_QUERY) Log(STDUSERLOG,"query ");
		if (bits & TRACE_USER) Log(STDUSERLOG,"user ");
		if (bits & TRACE_POS) Log(STDUSERLOG,"pos ");
		if (bits & TRACE_TCP) Log(STDUSERLOG,"tcp ");
		if (bits & TRACE_JSON) Log(STDUSERLOG,"json ");
		if (bits & TRACE_USERFN) Log(STDUSERLOG,"macro ");
		if (bits & TRACE_USERCACHE) Log(STDUSERLOG,"usercache ");
		if (bits & TRACE_SQL) Log(STDUSERLOG,"sql ");
		if (bits & TRACE_SAMPLE) Log(STDUSERLOG,"sample ");
		if (bits & TRACE_LABEL) Log(STDUSERLOG,"label ");
		if (bits & TRACE_TOPIC) Log(STDUSERLOG,"topic ");
		Log(STDUSERLOG,"\r\n");
	}

	// general
	if ((bits & general) != general) 
	{
		Log(STDUSERLOG,"Disabled simple: ");
		if (!(bits & TRACE_MATCH)) Log(STDUSERLOG,"match ");
		if (!(bits & TRACE_VARIABLE)) Log(STDUSERLOG,"variables ");
		Log(STDUSERLOG,"\r\n");
	}

	// mild detail
	if ((bits & mild) != mild) 
	{
		Log(STDUSERLOG,"Disabled mild detail: ");
		if (!(bits & TRACE_OUTPUT)) Log(STDUSERLOG,"output ");
		if (!(bits & TRACE_PREPARE)) Log(STDUSERLOG,"prepare ");
		if (!(bits & TRACE_PATTERN)) Log(STDUSERLOG,"pattern ");
		Log(STDUSERLOG,"\r\n");
	}

	// deep detail
	if ((bits & deep) != deep)
	{
		Log(STDUSERLOG,"Disabled deep detail: ");
		if (!(bits & TRACE_FACT)) Log(STDUSERLOG,"fact ");
		if (!(bits & TRACE_INFER)) Log(STDUSERLOG,"infer ");
		if (!(bits & TRACE_SAMPLE)) Log(STDUSERLOG,"sample ");
		if (!(bits & TRACE_HIERARCHY)) Log(STDUSERLOG,"hierarchy ");
		if (!(bits & TRACE_SUBSTITUTE)) Log(STDUSERLOG,"substitute ");
		if (!(bits & TRACE_VARIABLESET)) Log(STDUSERLOG,"varassign ");
		if (!(bits & TRACE_QUERY)) Log(STDUSERLOG,"query ");
		if (!(bits & TRACE_USER)) Log(STDUSERLOG,"user ");
		if (!(bits & TRACE_POS)) Log(STDUSERLOG,"pos ");
		if (!(bits & TRACE_TCP)) Log(STDUSERLOG,"tcp ");
		if (!(bits & TRACE_JSON)) Log(STDUSERLOG,"json ");
		if (!(bits & TRACE_USERFN)) Log(STDUSERLOG,"macro ");
		if (!(bits & TRACE_USERCACHE)) Log(STDUSERLOG,"usercache ");
		if (!(bits & TRACE_SQL)) Log(STDUSERLOG,"sql ");
		if (!(bits & TRACE_LABEL)) Log(STDUSERLOG,"label ");
		if (!(bits & TRACE_TOPIC)) Log(STDUSERLOG,"topic ");
		Log(STDUSERLOG,"\r\n");
	}
	if (original) WalkDictionary(TraceTopicFunction);
}

static void C_Say(char* input)
{
	AddResponse(input);
	wasCommand = OUTPUTASGIVEN;
}

static void C_NoTrace(char* input)
{
	char word[MAX_WORD_SIZE];
	unsigned int val = NOTRACE_TOPIC;
	while (input) 
	{
		input = ReadCompiledWord(input,word); // if using trace in a table, use closer "end" if you are using named flags
		if (!*word) break;
		input = SkipWhitespace(input);
		if (*word != '~') 
		{
			if (!stricmp(word,"on")) val = NOTRACE_TOPIC;
			else if (!stricmp(word,"off")) val = 0;
			else Log(STDUSERLOG,"Bad topic notrace request %s\r\n",word);
		}
		else
		{
			WORDP T = StoreWord(word);
			if (val) T->internalBits |= val;
			else T->internalBits &= -1 ^ NOTRACE_TOPIC;
		}
	}
}

static void C_Trace(char* input)
{
	char word[MAX_WORD_SIZE];
	unsigned int flags = trace;
	if (!*input) ShowTrace(trace,true);
	if (!*input) return;

	while (input) 
	{
		input = ReadCompiledWord(input,word); // if using trace in a table, use closer "end" if you are using named flags
		if (!*word) break;
		input = SkipWhitespace(input);
		if (*word == '+') // add this flag is the default
		{
			if (word[1]) memmove(word,word+1,strlen(word));
			else continue;
		}

		if (!stricmp(word,"all")) flags = (unsigned int)-1;
		else if (!stricmp(word,"none")) flags = 0;
		else if (*word == '-') // remove this flag
		{
			if (!word[1]) input = ReadCompiledWord(input,word);
			else memmove(word,word+1,strlen(word));
			if (!stricmp(word,"notthis")) flags &= -1 ^ TRACE_NOT_THIS_TOPIC;
			if (!stricmp(word,"match")) flags &= -1 ^ TRACE_MATCH;
			else if (!stricmp(word,"variables")) flags &= -1 ^ TRACE_VARIABLE; 
			else if (!stricmp(word,"simple")) flags &= -1 ^ (TRACE_MATCH|TRACE_VARIABLE); 
			else if (!stricmp(word,"input")) flags &= -1 ^ TRACE_INPUT;

			else if (!stricmp(word,"prepare")) flags &= -1 ^ TRACE_PREPARE; 
			else if (!stricmp(word,"output")) flags &= -1 ^ TRACE_OUTPUT;
			else if (!stricmp(word,"pattern")) flags &= -1 ^ TRACE_PATTERN;
			else if (!stricmp(word,"mild")) flags &= -1 ^ (TRACE_PREPARE|TRACE_OUTPUT|TRACE_PATTERN); 

			else if (!stricmp(word,"infer")) flags &= -1 ^ TRACE_INFER;
			else if (!stricmp(word,"sample")) flags &= -1 ^ TRACE_SAMPLE;
			else if (!stricmp(word,"substitute")) flags &= -1 ^ TRACE_SUBSTITUTE;
			else if (!stricmp(word,"hierarchy")) flags &= -1 ^ TRACE_HIERARCHY;
			else if (!stricmp(word,"fact")) flags &= -1 ^  TRACE_FACT;
			else if (!stricmp(word,"varassign")) flags &= -1 ^  TRACE_VARIABLESET;
			else if (!stricmp(word,"query")) flags &= -1 ^  TRACE_QUERY;
			else if (!stricmp(word,"user")) flags &= -1 ^  TRACE_USER;
			else if (!stricmp(word,"pos")) flags &= -1 ^  TRACE_POS;
			else if (!stricmp(word,"tcp")) flags &= -1 ^  TRACE_TCP;
			else if (!stricmp(word,"json")) flags &= -1 ^  TRACE_JSON;
			else if (!stricmp(word,"macro")) flags &= -1 ^  TRACE_USERFN;
			else if (!stricmp(word,"usercache")) flags &= -1 ^  TRACE_USERCACHE;
			else if (!stricmp(word,"sql")) flags &= -1 ^  TRACE_SQL;
			else if (!stricmp(word,"label")) flags &= -1 ^  TRACE_LABEL;
			else if (!stricmp(word,"topic")) flags &= -1 ^  TRACE_TOPIC;
			else if (!stricmp(word,"deep")) flags &= -1 ^ (TRACE_JSON|TRACE_TOPIC|TRACE_INPUT|TRACE_USERFN|TRACE_SAMPLE|TRACE_INFER|TRACE_SUBSTITUTE|TRACE_HIERARCHY| TRACE_FACT| TRACE_VARIABLESET| TRACE_QUERY| TRACE_USER|TRACE_POS|TRACE_TCP|TRACE_USERCACHE|TRACE_SQL|TRACE_LABEL); 
		}
		else if (IsNumberStarter(*word)) 
		{
			ReadInt(word,flags);
			break; // there wont be more flags -- want :trace -1 in a table to be safe from reading the rest
		}
		else if (!stricmp(word,"spell")) flags |= TRACE_SPELLING; // isolated
		else if (!stricmp(word,"match")) flags |= TRACE_MATCH;
		else if (!stricmp(word,"variables")) flags |= TRACE_VARIABLE; 
		else if (!stricmp(word,"simple")) flags |= (TRACE_MATCH|TRACE_VARIABLE); 
		else if (!stricmp(word,"input")) flags |= TRACE_INPUT;

		else if (!stricmp(word,"prepare")) flags |= TRACE_PREPARE; 
		else if (!stricmp(word,"output")) flags |= TRACE_OUTPUT;
		else if (!stricmp(word,"pattern")) flags |= TRACE_PATTERN;
		else if (!stricmp(word,"mild")) flags |= (TRACE_PREPARE|TRACE_OUTPUT|TRACE_PATTERN); 

		else if (!stricmp(word,"infer")) flags |= TRACE_INFER;
		else if (!stricmp(word,"sample")) flags |= TRACE_SAMPLE;
		else if (!stricmp(word,"substitute")) flags |= TRACE_SUBSTITUTE;
		else if (!stricmp(word,"hierarchy")) flags |= TRACE_HIERARCHY;
		else if (!stricmp(word,"fact")) flags |= TRACE_FACT;
		else if (!stricmp(word,"varassign")) flags |= TRACE_VARIABLESET;
		else if (!stricmp(word,"query")) flags |= TRACE_QUERY;
		else if (!stricmp(word,"user")) flags |= TRACE_USER;
		else if (!stricmp(word,"pos")) flags |= TRACE_POS;
		else if (!stricmp(word,"tcp")) flags |= TRACE_TCP;
		else if (!stricmp(word,"json")) flags |= TRACE_JSON;
		else if (!stricmp(word,"macro")) flags |= TRACE_USERFN;
		else if (!stricmp(word,"usercache")) flags |= TRACE_USERCACHE;
		else if (!stricmp(word,"sql")) flags |= TRACE_SQL;
		else if (!stricmp(word,"label")) flags |= TRACE_LABEL;
		else if (!stricmp(word,"topic")) flags |= TRACE_TOPIC;
		else if (!stricmp(word,"deep")) flags |= (TRACE_JSON|TRACE_TOPIC|TRACE_INPUT|TRACE_USERFN|TRACE_SAMPLE|TRACE_INFER|TRACE_SUBSTITUTE|TRACE_HIERARCHY| TRACE_FACT| TRACE_VARIABLESET| TRACE_QUERY| TRACE_USER|TRACE_POS|TRACE_TCP|TRACE_USERCACHE|TRACE_SQL|TRACE_LABEL); 

		else if (!stricmp(word,"0") || !stricmp(word,"clear")) trace = 0;
		else if (!stricmp(word,"end")) break; // safe end
		else if (*word == '!') // NOT tracing a topic 
		{
			if (word[1]) // ! jammed against topic, separate it
			{
				input -= strlen(word+1); 
				word[1] = 0;
			}
			input = ReadCompiledWord(input,word);
			SetTopicDebugMark(FindTopicIDByName(word),0);
			return;
		}
		else if (*word == '^')
		{
			WORDP FN = FindWord(word);
			if (FN) 
			{
				FN->internalBits ^= MACRO_TRACE;
				Log(STDUSERLOG,"Tracing function %s = %d\r\n",word, (FN->internalBits & MACRO_TRACE) ? 1 : 0);
			}
			else Log(STDUSERLOG,"No such function %s\r\n",word);
		}
		else if (*word == '~') // tracing a topic or rule by label
		{
			char* period = strchr(word,'.');
			if (period) *period = 0;
			unsigned int topic = FindTopicIDByName(word);
			if (topic == 0) Log(STDUSERLOG,"No such topic %s\r\n",word);
			else if (!period) 
			{
				if (!TI(topic)->topicDebug && !flags) SetTopicDebugMark(topic,(unsigned int)-1); // default all
				else if (flags) SetTopicDebugMark(topic,flags); // just those named previously
				else SetTopicDebugMark(topic,0); // disable
				flags = 0;
			}
			else if (IsAlphaUTF8(period[1])) // find ALL labelled statement and mark them
			{
				int id = 0;
				char* which = GetTopicData(topic);
				bool found = false;
				while (which && *which && (which = FindNextLabel(topic,period+1,which,id,true)))
				{
					SetDebugRuleMark(topic,id);
					found = true;
					which = FindNextRule(NEXTRULE,which,id);
				}
				if (!found)  Log(STDUSERLOG,"cannot find %s.%s\r\n",word,period+1);
			}
			else if (IsDigit(period[1]))// did he use number notation?
			{
				int id = 0;
				*period = '.';
				char* rule = GetRuleTag(topic,id,word);
				if (rule) SetDebugRuleMark(topic,id);
				else Log(STDUSERLOG,"cannot find %s.%s\r\n",word,period+1);
			}
			return;
		}
	}
	trace = flags;
	if (!fromScript)
	{
		echo = (trace) ? true : false;
		Log(STDUSERLOG," trace set to %d (0x%x)\n",trace,trace);
		if (trace) ShowTrace(trace,true);
	}
} 

void C_Why(char* buffer)
{
	for (unsigned int i = 0;  i < responseIndex; ++i)
	{
		unsigned int order = responseOrder[i];
		unsigned int topic = responseData[order].topic;
		int id;
		char* rest = GetRuleIDFromText(responseData[order].id,id);
		Log(STDUSERLOG,"%s%s  %s\r\n",GetTopicName(topic),responseData[order].id,ShowRule(GetRule(topic,id)));
		if (*rest) // format will be ~topic.3.0.5.3.3  where last 3 are the via rule info
		{
			topic = atoi(rest+1);
			GetRuleIDFromText(rest+1,id);
			Log(STDUSERLOG," via %s%s  %s\r\n",GetTopicName(topic),rest,ShowRule(GetRule(topic,id)));
		}
	}
}

//////////////////////////////////////////////////////////
//// MISC COMMANDS
//////////////////////////////////////////////////////////

static void CleanIt(char* word,uint64 junk) // remove cr from source lines for Linux
{
	FILE* in = fopen(word,"rb");
	if (!in) 
	{
		printf("missing %s\r\n",word);
		return;
	}
	fseek (in, 0, SEEK_END);
    size_t size = ftell(in);
	char* buf = (char*) malloc(size+2); // enough to hold the file

	fseek (in, 0, SEEK_SET);
	unsigned int val = (unsigned int) fread(buf,1,size,in);
	fclose(in);
	if ( val != size) return;
	buf[size] = 0;	// force an end

	// now overwrite file with proper trimming
	FILE* out = FopenUTF8Write(word);
	for (unsigned int i = 0; i < size; ++i)
	{
		if (buf[i] != '\r' && buf[i] != 26) fwrite(buf+i,1,1,out);	// remove cr and ^Z
	}
	if (buf[size-1] != '\n') fwrite("\n",1,1,out); // force ending line feed
	fclose(out);
	free(buf);
}

static void C_ExtraTopic(char* input) // topicdump will create a file in TMP/tmp.txt
{
	FILE* in = fopen("TMP/tmp.txt","rb");
	if (!in) 
	{
		printf("missing TMP/tmp.txt\r\n");
		return;
	}
	fseek (in, 0, SEEK_END);
    size_t size = ftell(in);
	fseek (in, 0, SEEK_SET);
 	extraTopicData = (char*)malloc(size+2); // enough to hold the file
	char* at = extraTopicData;
	currentFileLine = 0; // prepare for BOM
	while(ReadALine(at,in,size) >= 0) {at += strlen(at);} // join all lines
	// clearly end the topic data
	strcpy(at,"``");
	printf("Extra topic read\r\n");
}

static void C_Clean(char* word) // remove CR for LINUX
{
	WalkDirectory("src",CleanIt,0);
}

#ifndef DISCARDDATABASE
static void C_EndPGUser(char* word)
{
	PGUserFilesCloseCode();
}
#endif

static void BuildDummyConcept(WORDP D,uint64 junk)
{
	if ((D->internalBits & BUILD0) && *D->word == '~') 
		CreateFact(MakeMeaning(D),Mmember,MakeMeaning(StoreWord("~a_dummy")), FACTTRANSIENT);
}

static void SortConcept(WORDP D,uint64 junk)
{
	if ((D->internalBits & BUILD0) && *D->word == '~')
		Sortit(D->word,(int)junk); // will be 0 for no input, some char value otherwise
}

static void C_SortConcept(char* input)
{
#ifdef INFORMATION
To get concepts in a file sorted alphabetically (both by concept and within) , do 
    0. empty TOPICS
	0. :build concept0 
	1. :sortconcept x		-- builds one concept per line and sorts the file by concept name  outputs to concepts.top
	2. take the contents of concept.top and replace the original file in ONTOLOGY, erase TOPICS
	3. :build concept0
	4. :sortconcept			-- maps concepts neatly onto multiple lines
	5. take the contents of cset.txt and replace the original file
#endif
	WORDP D = StoreWord("~a_dummy",AS_IS);
	if (*input) 
	{
		WalkDictionary(BuildDummyConcept,0); // stores names of concepts on dummy concept, to lock position in dictionary. later not, will be read in
		AddInternalFlag(D,BUILD0|CONCEPT);
	}

	fclose(FopenUTF8Write("cset.txt"));
	if (!*input) // hide this on second pass
	{
		WORDP D = FindWord("~a_dummy");
		RemoveInternalFlag(D,BUILD0);
	}
	WalkDictionary(SortConcept,(uint64)input[0]);
	if (*input) system("sort /rec 63000 c:/chatscript/cset.txt >concepts.top");
	else system("copy c:/chatscript/cset.txt >concepts.top");
}

//////////////////////////////////////////////////////////
//// ANALYTICS
//////////////////////////////////////////////////////////

static void DisplayTables(char* topic)
{
	char args[MAX_WORD_SIZE];
	sprintf(args,"( %s )",topic);
	Callback(FindWord(GetUserVariable("$cs_abstract")),args);
}

static void DoHeader(int count,char* basic,FILE* in,int id,unsigned int spelling)
{
	if (*abstractBuffer == 0) 	// no more verification data for this topic
	{
		// display header
		if (!lineLimit)	
		{
			TabInset(count,false);
			Log(STDUSERLOG,"%s",basic); 
		}
		return;
	}

	// get verification matching input -- ~abortion.0.0 #! I am against abortion.
	static int readID = 0;
	static char* test = NULL;
	static char type = 0;
	if ((unsigned char)*abstractBuffer == 1) readID = -1; // read 1st line of topic data
retry:
	while (readID == -1 || TOPLEVELID(id) > TOPLEVELID(readID) ||  ( TOPLEVELID(id) == TOPLEVELID(readID) && REJOINDERID(id) > REJOINDERID(readID)  )) // flush reads until get 1st good one
	{
		if (ReadALine(abstractBuffer,in) < 0) break;	// no more verifcation data
		char* dot = strchr(abstractBuffer,'.');
		char* dot1 = strchr(dot+1,'.');
		readID = MAKE_REJOINDERID(atoi(dot1+1)) + atoi(dot+1); // the id pending
		test = strchr(abstractBuffer,'#');
		type = test[2];
		if (!(spelling & ABSTRACT_PRETTY)) test += 2;
		if ((type == 'x' || type == 'X') && *test != ' ' && ((TOPLEVELID(id) > TOPLEVELID(readID)) ||  (TOPLEVELID(id) == TOPLEVELID(readID) && REJOINDERID(id) > REJOINDERID(readID)) )) // global topic comment, dump it immediately and keep going
		{
			Log(STDUSERLOG,"\r\n%s\r\n",test+1); 
			readID = -1;
		}
	}

	if (test && (type == 'x' || type == 'X') && *test != ' ' && readID == id) // global topic comment for current match
	{
		Log(STDUSERLOG,"\r\n%s\r\n",test+1); 
		readID = -1;
		goto retry;
	}

	// since we have sample input, kill pattern
	if (id == readID && *basic != ' ' && !(spelling & ABSTRACT_PRETTY)) 
	{
		unsigned int offset = 2;
		while (basic[offset] && basic[offset] != '(') ++offset; // find end of blank space before pattern.
		if (basic[offset]) basic[--offset] = 0;  
	}

	// display header
	if (spelling & ABSTRACT_PRETTY && id == readID)  
	{
		TabInset(count,false);
		Log(STDUSERLOG,"%s\r\n",test);
	}
	if (!lineLimit)	
	{
		TabInset(count,false);
		Log(STDUSERLOG,"%s",basic); 
	}

	// display verify as pattern
	if (id == readID && !lineLimit && !(spelling & ABSTRACT_PRETTY)) 
	{
		Log(STDUSERLOG," %s =>   ",test);
	}
}

static void DisplayTopic(char* name,int spelling)
{
	int topicID = FindTopicIDByName(name,true);
	if (!topicID) return;
	char* rule = GetTopicData(topicID); 
	if (!rule) return;
	if (spelling & ABSTRACT_STORY && !GAMBIT_MAX(TI(topicID)->topicMaxRule)) return; // has no gambits
	
	*abstractBuffer = 1;	// buffer started for new topic
	if (spelling & ABSTRACT_PRETTY)
	{
		unsigned int lineSize = 0;
		Log(STDUSERLOG,"\r\nTOPIC: %s",name);
		unsigned int flags = GetTopicFlags(topicID);
		if (flags & TOPIC_SYSTEM) Log(STDUSERLOG," SYSTEM");
		if (flags & TOPIC_KEEP) Log(STDUSERLOG," KEEP");
		if (flags & TOPIC_REPEAT) Log(STDUSERLOG," REPEAT");
		if (flags & TOPIC_RANDOM) Log(STDUSERLOG," RANDOM");
		if (flags & TOPIC_NOSTAY) Log(STDUSERLOG," NOSTAY");
		if (flags & TOPIC_PRIORITY) Log(STDUSERLOG," PRIORITY");
		if (flags & TOPIC_LOWPRIORITY) Log(STDUSERLOG," DEPRIORITIZE");
		if (flags & TOPIC_NOBLOCKING) Log(STDUSERLOG," NOBLOCKING");
		if (flags & TOPIC_NOPATTERNS) Log(STDUSERLOG," NOPATTERNS");
		if (flags & TOPIC_NOGAMBITS) Log(STDUSERLOG," NOGAMBITS");
		if (flags & TOPIC_NOSAMPLES) Log(STDUSERLOG," NOSAMPLES");
		if (flags & TOPIC_NOKEYS) Log(STDUSERLOG," NOKEYS");
		if (flags & TOPIC_SAFE) Log(STDUSERLOG," SAFE");
		if (flags & TOPIC_SHARE) Log(STDUSERLOG," SHARE");
		Log(STDUSERLOG," (");
		WORDP D = FindWord(name);
		FACT* F = GetObjectNondeadHead(D);
		while (F) 
		{
			if (F->verb == Mmember|| F->verb == Mexclude)
			{
				char word[MAX_WORD_SIZE];
				if (F->flags & ORIGINAL_ONLY) sprintf(word,"'%s ",WriteMeaning(F->subject));
				else sprintf(word,"%s ",WriteMeaning(F->subject));
				if (F->verb == Mexclude) Log(STDUSERLOG,"!");
				size_t wlen = strlen(word);
				lineSize += wlen;
				Log(STDUSERLOG,"%s",word);
				if (lineSize > 500) // avoid long lines
				{
					Log(STDUSERLOG,"\r\n     ");
					lineSize = 0;
				}
			}
			F = GetObjectNondeadNext(F);
		}
		Log(STDUSERLOG,")\r\n\r\n");
	}
	else 
	{
		Log(STDUSERLOG,"\r\n****** TOPIC: %s",name);
		topicBlock* block = TI(topicID);
		if (block->topicRestriction) Log(STDUSERLOG,"  restricted to: %s\r\n",block->topicRestriction);
		Log(STDUSERLOG,"\r\n");
	}

	WORDP D = FindWord(name);
	char word[MAX_WORD_SIZE];
	char fname[MAX_WORD_SIZE];
	sprintf(fname,"VERIFY/%s-b%c.txt",name+1,(D->internalBits & BUILD0) ? '0' : '1');
	FILE* in = FopenReadWritten(fname);

	bool preprint;
	char* old = NULL;
	char* buffer = AllocateBuffer();
	char* tmpBuffer = AllocateBuffer();
	char label[MAX_WORD_SIZE];
	char pattern[MAX_BUFFER_SIZE];
	char basic[MAX_BUFFER_SIZE];
	int id = 0;
	char bodyKind[100];

	while (rule && *rule) // for each rule
	{
		preprint = false;
		char* output = GetPattern(rule,label,pattern);
		char* end = strchr(output,'`');
		bool norule = EmptyReuse(output,topicID);
		if (!*output || *output == '`' || norule) 
		{
			rule = FindNextRule(NEXTRULE,rule,id);
			continue;
		}
		if (spelling & ABSTRACT_STORY)
		{
			char* topLevelRule = GetRule(topicID,TOPLEVELID(id));	// the top level rule (if a rejoinder)
			if (TopLevelQuestion (topLevelRule) || TopLevelStatement(topLevelRule)) 
			{
				rule = FindNextRule(NEXTRULE,rule,id);
				continue;
			}
		}
		if (spelling & ABSTRACT_RESPONDER)
		{
			char* topLevelRule = GetRule(topicID,TOPLEVELID(id));	// the top level rule (if a rejoinder)
			if (!TopLevelQuestion (topLevelRule) && !TopLevelStatement(topLevelRule)) 
			{
				rule = FindNextRule(NEXTRULE,rule,id);
				continue;
			}
		}

		if (spelling & ABSTRACT_VP)
		{
			char* end = strchr(output,ENDUNIT);
			*end = 0;
			if (*rule == QUESTION || *rule == STATEMENT_QUESTION)
			{
				if (!*label && strstr(output,"factanswer")) Log(STDUSERLOG,"No label for: %s %s\r\n",pattern,output);
			}
			*end = ENDUNIT;
			rule = FindNextRule(NEXTRULE,rule,id);
			continue;
		}
		if (spelling & ABSTRACT_PRETTY) // revise pattern for cannonical
		{
			*tmpBuffer = 0;
			char word[MAX_WORD_SIZE];
			char* pbase = pattern;
			if (*label) 
			{
				strcat(tmpBuffer,label);
				strcat(tmpBuffer," ");
			}
			while (pbase && *pbase)
			{
				pbase = ReadCompiledWord(pbase,word);
				if (IsAlphaUTF8(word[0]) && strchr(word,'_') && spelling & ABSTRACT_PRETTY ) // is it a word or a phrase
				{
					WORDP X = FindWord(word);
					if (X && X->properties & PART_OF_SPEECH) {;} // known word
					else // make it a phrase
					{
						Convert2Blanks(word);
						strcat(word,"\"");	// closing quote
						memmove(word+1,word,strlen(word)+1);
						*word = '"';
					}
				}
				if (IsAlphaUTF8(word[0]) && spelling & ABSTRACT_CANONICAL) // could be made canonical
				{
					WORDP entry, canonical;
					uint64 sysflags = 0;
					uint64 cansysflags = 0;
					GetPosData(2,word,entry,canonical,sysflags,cansysflags);
					if (canonical)
					{
						// if canonical is upper and entry is lower, dont show canonical
						if (entry && canonical && IsUpperCase(*canonical->word) && !IsUpperCase(*entry->word)) {;}
						else if (!stricmp(canonical->word,"unknown-word")) {;}
						else strcpy(word,canonical->word);
					}
				}
				strcat(tmpBuffer,word);
				strcat(tmpBuffer," ");
			}
			strcpy(pattern,tmpBuffer);
		}

		// std rule header
		unsigned int kind = *rule;
		basic[0] = (unsigned char)kind;
		basic[1] = ':';
		basic[2] = ' ';
		basic[3] = 0;
		if (*label)
		{
			strcat(basic,label);
			strcat(basic,"  ");
		}
		int choiceNest = 0;
		char* choiceStart = NULL;
		unsigned int choiceCharacters = 0;

		// revise comparison patterns
		if (*pattern)
		{
			char* compare = pattern;
			while (ALWAYS)
			{
				char* compare1 = strstr(compare," !="); // hunt for comparison operators
				compare = strstr(compare," =");
				if (compare1)
				{
					if (compare1 < compare || !compare) compare = compare1;
				}
				if (!compare) break;
				if (*++compare != '=') ++compare; // negated compare
				if (compare[1] != ' ') memmove(compare,compare+2,strlen(compare+1));// remove header and accelerator of comparison
			}
			if ((kind == 't' || kind == 'r') && *pattern == '(' && pattern[1] == ' ' && pattern[2] == ')') *pattern = 0;	// there is no pattern really for this gambit
			else
			{
				strcat(basic,pattern);
				if (!(spelling & ABSTRACT_PRETTY)) strcat(basic," => ");
			}
		}
		
		// now determine the output
		unsigned int indent = Rejoinder(rule) ? ((*rule - 'a' + 1) * 2) : 0; 
		char* outputPtr = buffer;
		*outputPtr = 0;
		bool badspell = false;
		int hasBody = 0;
		end = strchr(output,ENDUNIT);
		*end = 0;
		bool badWord = false;
		bool multipleOutput = false;
		int level = 0;
		char levelMark[1000];
		levelMark[0] = 0;
		char* prior = "";
		char* prior2 = "";
		while (output && *output && *output != ' ') // read output until end of rule
		{
			if (spelling & ABSTRACT_PRETTY) // line by line neatened output
			{
				prior2 = prior;
				prior = output;
				output = ReadDisplayOutput(output,word);
				if (!*word) break;	// nothing left
				if (*word == '}') 
				{
					--level;
					if (level < 0) 
						level = 0;
				}
				// for ^if testing zone, remove accelerator
				if (word[3] == '{' && word[4] == ' ' && !word[5]) strcpy(word,"{ ");
				if (word[0] && word[1] && word[2] && word[3] == ' ' && !word[4]) // possible accelerator
				{
					if (!strnicmp(prior2,"^^if",4)) continue;	// ignore accelerator after iftest to skip to next test
					if (!strnicmp(prior2,"^^loop",6)) continue;	// ignore accelerator at start of loop to skip
					if (!strnicmp(prior2,"} ",2) && levelMark[level+1] == 'i') continue;	 // ignore jump after if branch to end of whole if
				}
				
				if (multipleOutput) for (unsigned int j = 0; j < (indent + (level * 2) + 4); ++j) 
				{
					sprintf(outputPtr,"  ");
					outputPtr += 2;
				}
				if (*word == '^' && word[1] == '^') memmove(word,word+1,strlen(word));	// ^^if and ^^loop make normal user written
				sprintf(outputPtr,"%s\r\n",word); // abstract puts lf after EACH item
				outputPtr += strlen(outputPtr);
				multipleOutput = true;
				if (*word == '{' ) 
				{
					++level;
					levelMark[level] = 0;
					if (!strnicmp(prior2,"^^if",4)) levelMark[level] = 'i'; // is an if level
				}
				continue;
			}

			output = ReadCompiledWord(output,word);
			if (!*word) break; 
			if (*word == '+') break;	// skip assignment
			next:
			switch(*word)
			{
			case '[': // choice area, with optional label
				++choiceNest;
				choiceStart = outputPtr;
				sprintf(outputPtr,"%s ",word);
				outputPtr += strlen(outputPtr);
				output = ReadCompiledWord(output,word);
				if (word[1] == ':' && !word[2]) // jump label
				{
					sprintf(outputPtr,"%s ",word); 
					outputPtr += strlen(outputPtr);
					output = ReadCompiledWord(output,word);
				}
				goto next;
			case ']':
				if (--choiceNest == 0)
				{ 
					unsigned int len =  outputPtr - choiceStart; // size of [] 
					strcpy(outputPtr++,"]");
					if (!spelling && len >= lineLimit && len && lineLimit) Log(STDUSERLOG,"(%d) %s\r\n",len,choiceStart);
					choiceCharacters += len; 
				}
				break;
			case ')':
				if (preprint) //   closing preprint call
				{
					preprint = false;
					continue;
				}
				break;
			case '}':
				if (hasBody)
				{
					if (bodyKind[hasBody] == 'i') // if
					{
						output = strchr(output,' ');
						if (output) ++output; // skip end sizing jump rule
					}
					--hasBody;
					continue;
				}
				break;
			case '$':
				if (IsDigit(word[1])) break; // money $
				// flow into these other variables
			case '%': case '_': case '@': // match variable or set variable
				if (*output == '=' || output[1] == '=') // assignment
				{
					output = ReadCompiledWord(output,word); // assign op
					output = ReadCompiledWord(output,word); // rhs item
					if (*word == '^' && *output == '(') output = BalanceParen(output+1); // rhs function call
					while (IsArithmeticOperator(output)) // arithmetic with assignment
					{
						output = ReadCompiledWord(output,word); // op
						output = ReadCompiledWord(output,word);  // next rhs item
						if (*word == '^' && *output == '(') output = BalanceParen(output+1); // rhs function call
					}
					continue;
				}
				break;
			case '^': // function call or argument
				if (!stricmp(word,"^preprint") || !stricmp(word,"^print") || !stricmp(word,"^insertprint") || !stricmp(word,"^postprint")) // show content
				{
					output = ReadCompiledWord(output,word);
					preprint = true;
					continue;
				}
				else if (!stricmp(word,"^reuse") || !stricmp(word,"^gambit") || !stricmp(word,"^respond")|| !stricmp(word,"^refine"))
				{
					output -= strlen(word) + 1;
					char* end = strchr(output,')');
					char c = end[1];
					end[1] = 0;
					strncpy(outputPtr,output,strlen(output));
					outputPtr += end - output + 1;
					*outputPtr = 0;
					end[1] = c;
					output = end + 1;
				}
				else if ((!stricmp(word,"^^if") || !stricmp(word,"^^loop")) && *output == '(') 
				{
					++hasBody;
					bodyKind[hasBody] = word[2]; // i or l
					output = strchr(output,'{') + 2;
					continue;
				}
				else if (*output == '(') output = BalanceParen(output+1); //  end call
				break;
			case ':':  // shouldnt be label inside []
				break;
			case '=': // assignment
				old = outputPtr;
				while (*old && *--old && *old != ' '); // find LHS of assignment
				if (*old == ' ') // erase left hand of assignment
				{
					outputPtr = old + 1;
					if (*outputPtr == '$' || *outputPtr == '_' || *outputPtr == '@' || *outputPtr == '%') *outputPtr = 0;
				}
				if (*output != '^') output = ReadCompiledWord(output,word);	// swallow next when not a function call
				break;
			case '~': 
				break;
			case '\\':
				if (word[1] == '"')
				{
					sprintf(outputPtr,"%s ",word+1);
					outputPtr += strlen(outputPtr);
				}
				else 
				{
					sprintf(outputPtr,"%s ",word);
					outputPtr += strlen(outputPtr);
				}
				break;
			default: // ordinary words usually
				if (!stricmp(word,"else") && (*output == '(' || *output =='{')) //  else {}  OR else if () {}
				{
					++hasBody;
					bodyKind[hasBody] = 'i'; // if
					if (*output != '{') output = strchr(output,'{');
					output += 2;
					continue;
				}
				else 
				{
					bool wrong = false;
					if (spelling == ABSTRACT_SET_MEMBER && word[1])
					{
						WORDP D = FindWord(word,0,LOWERCASE_LOOKUP);
						if (!D || D->inferMark != inferMark) D = FindWord(word,0,UPPERCASE_LOOKUP);
						if (D && D->inferMark == inferMark) badWord = true;
					}
					char copy[MAX_WORD_SIZE];
					MakeLowerCopy(copy,(*word == '\'') ? (word+1) : word);
					if (spelling & ABSTRACT_SPELL && word[1]) // ignore punctuation
					{
						if (*word == '*' || IsDigit(*word)) continue;	 // ignore wildcards, numbers, or jump zones
						size_t len = strlen(copy);
						if (copy[len-1] == '{') continue;  // an IF jump zone
						while (len-- && IsPunctuation(copy[len])) copy[len] = word[len] = 0;  // remove trailing punctuation.
						char* apostrophe = strchr(copy,'\'');
						WORDP D = FindWord(copy);
						if (!D || !(D->properties & PART_OF_SPEECH)) 
						{
							if (!D || !(D->internalBits & HAS_SUBSTITUTE)) // not known, try for sentence head one
							{
								char word[MAX_WORD_SIZE];
								sprintf(word,"<%s",copy);
								D = FindWord(word);
							}
							if (!D) D = FindWord(copy,0,UPPERCASE_LOOKUP);
						}
						if (D && (D->properties & PART_OF_SPEECH || D->internalBits & HAS_SUBSTITUTE)){;} //  we know this word
						else if (D && D->internalBits & QUERY_KIND) {;} // a query
						else if (IsUrl(copy,0) || apostrophe || copy[0] == '_' || copy[0] == '$' || copy[0] == '%' || copy[0] == '@' || copy[0] == '"') {;} 
						else if (!FindCanonical( copy, 1,true)) wrong = badspell = true;
					}
					if (wrong) 
						Log(STDUSERLOG,"%s\r\n",word);
					else sprintf(outputPtr,"%s ",word);
					outputPtr += strlen(outputPtr);
				}
			}
		} 
		
		*end = ENDUNIT; // restore data
		char* finish = buffer + strlen(buffer) - 1;
		if (*finish == ' ') *finish = 0;

		// we have the output, what to do with it

		if (spelling & ABSTRACT_SET_MEMBER && !badWord) *buffer = 0; // only do lines with censored words, showing context
		if (spelling & ABSTRACT_SPELL) *buffer = 0; // only do lines with bad spelling
		bool headit = false;
		size_t len = strlen(buffer);
		if (lineLimit) // check for sections between \n that are too long.
		{
			char* esc;
			char* at = buffer;
			while ((esc = strchr(at,'\\')))
			{
				if (esc[1] != 'n') at = esc+2;
				else
				{
					len = at - esc - 1;
					char word[MAX_WORD_SIZE];
					ReadCompiledWord(at,word);
					size_t wsize = strlen(word);
					if (word[wsize-1] == ':') len -= wsize + 1;		// remove speaker flag
					if (len > lineLimit) headit = true;
					at = esc+2;
				}
			}
			len = strlen(at);
			if (choiceCharacters) len -= choiceCharacters - 1; // dont zero out len
			char word[MAX_WORD_SIZE];
			ReadCompiledWord(at,word);
			size_t wsize = strlen(word);
			if (word[wsize-1] == ':') len -= wsize + 1;		// remove speaker flag
			if (len > lineLimit) 
			{
				headit = true;
				longLines++;
			}
		}
		else if (!*buffer && !lineLimit && !(spelling & ABSTRACT_SET_MEMBER) && !(spelling & ABSTRACT_SPELL) && !(spelling & ABSTRACT_PRETTY)) // nothing to show but we want to see anything
		{
			if (!(spelling & ABSTRACT_NOCODE) )
			{
				strcpy(buffer," { code }");
				headit = true;
			}
		}
		else headit = true;

		if (headit && !(spelling & ABSTRACT_RESTRICTIONS)) 
		{
			DoHeader(indent,basic,in,id,spelling); 
			if (lineLimit) // check for sections between \n that are too long.
			{
				char* esc;
				char* at = buffer;
				char* start = at;
				while ((esc = strchr(at,'\\')))
				{
					if (esc[1] != 'n') at = esc+1;
					else
					{
						*esc = 0;
						len = strlen(start);
						char word[MAX_WORD_SIZE];
						ReadCompiledWord(at,word);
						size_t wsize = strlen(word);
						if (word[wsize-1] == ':') 
						{
							len -= wsize + 1;		// remove speaker flag and space
							start += wsize + 1;
						}
						if (choiceCharacters) len -= choiceCharacters - 1; // dont zero out len
						if (len > lineLimit) 
							Log(STDUSERLOG,"(%d) %s\r\n",len,start);
						choiceCharacters = 0;
						*esc = '\\';
						start = at = esc + 3; // skip \n and space
					}
				}
				len = strlen(at);
				char word[MAX_WORD_SIZE];
				ReadCompiledWord(at,word);
				size_t wsize = strlen(word);
				if (word[wsize-1] == ':') len -= wsize + 1;		// remove speaker flag
				if (choiceCharacters) len -= choiceCharacters - 1; // dont zero out len
				if (len > lineLimit) 
					Log(STDUSERLOG,"(%d) %s\r\n",len,at);
				choiceCharacters = 0;
			}
			else 
			{
				// convert \n to linefeeds
				char* lf;
				unsigned int gap = 2;
				if (*basic == 'a') gap = 6;
				while ((lf = strstr(buffer,"\\n")))
				{
					*lf = '\r';
					lf[1] = '\n';
					memmove(lf+2 + gap,lf+2,strlen(lf+2)+1);
					for (unsigned int i = 0; i < gap; ++i) lf[2+i] = ' ';
				}
				Log(STDUSERLOG,"%s\r\n",buffer);
			}
		}
		*end = ENDUNIT;
		rule = FindNextRule(NEXTRULE,rule,id);
	}
	if (in) fclose(in);
	FreeBuffer();
	FreeBuffer();
}

static void MarkDownHierarchy(MEANING T)
{
    if (!T) return;
    WORDP D = Meaning2Word(T);
	if (D->inferMark == inferMark) return;	
	D->inferMark = inferMark;

	if (*D->word == '~') // follow members of set
	{
		FACT* F = GetObjectNondeadHead(D);
		while (F)
		{
			if (F->verb == Mmember)
			{
				MEANING M = F->subject;
				WORDP S = Meaning2Word(M);
				if (S->inferMark != inferMark) MarkDownHierarchy(M);
			}
			F = GetObjectNondeadNext(F);
		}
	}
}

void CopyFile2File(const char* newname,const char* oldname, bool automaticNumber)
{
	char name[MAX_WORD_SIZE];
	FILE* out;
	if (automaticNumber) // get next number
	{
		const char* at = strchr(newname,'.');	//   get suffix
		int len = at - newname;
		strncpy(name,newname,len);
		strcpy(name,newname); //   base part
		char* endbase = name + len;
		int j = 0;
		while (++j)
		{
			sprintf(endbase,"%d.%s",j,at+1);
			out = FopenReadWritten(name);
			if (out) fclose(out);
			else break;
		}
	}
	else strcpy(name,newname);

	FILE* in = FopenReadWritten(oldname);
	if (!in) 
	{
		unlink(name); // kill any old one
		return;	
	}
	out = FopenUTF8Write(name);
	if (!out) // cannot create 
	{
		return;
	}
	fseek (in, 0, SEEK_END);
	unsigned long size = ftell(in);
	fseek (in, 0, SEEK_SET);

	char buffer[RECORD_SIZE];
	while (size >= RECORD_SIZE)
	{
		fread(buffer,1,RECORD_SIZE,in);
		fwrite(buffer,1,RECORD_SIZE,out);
		size -= RECORD_SIZE;
	}
	if (size > 0)
	{
		fread(buffer,1,size,in);
		fwrite(buffer,1,size,out);
	}

	fclose(out);
	fclose(in);
}

static void C_Abstract(char* input)
{
	int spelling = 0;
	lineLimit = 0;
	longLines = 0;
	if (IsDigit(*input)) input = ReadInt(input,lineLimit); // line length limit
	char word[MAX_WORD_SIZE];
	input = SkipWhitespace(input);
	while (input && *input)
	{
		if (*input == '~') break;
		input = ReadCompiledWord(input,word);
		if (!stricmp(word,"spell")) spelling |= ABSTRACT_SPELL;
		else if (!stricmp(word,"censor"))
		{
			spelling |= ABSTRACT_SET_MEMBER;
			input = ReadCompiledWord(input,word);
			NextInferMark();
			MarkDownHierarchy(MakeMeaning(StoreWord(word)));
		}
		else if (!stricmp(word,"canon")) spelling |= ABSTRACT_CANONICAL | ABSTRACT_PRETTY;
		else if (!stricmp(word,"pretty")) spelling |= ABSTRACT_PRETTY;
		else if (!stricmp(word,"vp")) spelling |= ABSTRACT_VP;
		else if (!stricmp(word,"story")) spelling |= ABSTRACT_STORY;
		else if (!stricmp(word,"responder")) spelling |= ABSTRACT_RESPONDER;
		else if (!stricmp(input,"nocode")) spelling |= ABSTRACT_NOCODE;
		else if (!stricmp(input,"story")) spelling |= ABSTRACT_STORY;
		input = SkipWhitespace(input);
	}
	input = SkipWhitespace(input);

	abstractBuffer = AllocateBuffer();

	size_t len = 0;
	char* x = strchr(input,'*');
	if (x) len = x - input;
	else if (*input == '~') len = strlen(input);

	// get topic if given
	if (*input == '~' && !x)
	{
		char word[MAX_WORD_SIZE];
		while (input && *input)
		{
			input = ReadCompiledWord(input,word);
			DisplayTopic(word,spelling);
			DisplayTables(word);
		}
	}
	else if (*input && *input != '~') // from topic file
	{
		char filename[MAX_WORD_SIZE];
		ReadCompiledWord(input,filename);
		for (unsigned int i = 1; i <= numberOfTopics; ++i) 
		{
			if (!stricmp(GetTopicFile(i),filename)) DisplayTopic(GetTopicName(i),spelling);
		}
	}
	// otherwise do all
	else
	{
		for (unsigned int i = 1; i <= numberOfTopics; ++i) 
		{
			if (!*GetTopicName(i)) continue;
			if (len && strnicmp(GetTopicName(i),input,len)) continue;
			DisplayTopic(GetTopicName(i),spelling);
		}
		DisplayTables("*");
	}
	FreeBuffer();
	if (lineLimit) Log(STDUSERLOG,"%d lines were over length %d\r\n",longLines,lineLimit);
}



static void C_Diff(char* input)
{
	char file1[MAX_WORD_SIZE];
	char file2[MAX_WORD_SIZE];
	input = ReadCompiledWord(input,file1);
	input = ReadCompiledWord(input,file2);
	input = SkipWhitespace(input);
	char separator = *input;
	FILE* in1 = FopenReadWritten(file1);
	if (!in1) 
	{
		Log(STDUSERLOG,"%s does not exist\r\n",file1);
		return;
	}
	FILE* in2 = FopenReadWritten(file2);
	if (!in2) 
	{
		Log(STDUSERLOG,"%s does not exist\r\n",file2);
		fclose(in1);
		return;
	}
	char name[MAX_WORD_SIZE];
	sprintf(name,"%s/diff.txt",logs);
	FILE* out = FopenUTF8Write(name);
	char* buf1 = AllocateBuffer();
	char* buf2 = AllocateBuffer();
	unsigned int n = 0;
	unsigned int err = 0;
	while (ALWAYS)
	{
		++n;
		if (!fgets(buf1,maxBufferSize,in1)) 
		{
			if (fgets(buf2,maxBufferSize,in2)) 
			{
				Log(STDUSERLOG,"2nd file has more at line %d: %s\r\n",n,buf2);
				fprintf(out,"2nd file has more at line %d: %s\r\n",n,buf2);
				++err;
			}
			break;
		}
		if (!fgets(buf2,maxBufferSize,in2)) 
		{
			++err;
			Log(STDUSERLOG,"1st file has more at line %d: %s\r\n",n,buf1);
			fprintf(out,"1st file has more at line %d: %s\r\n",n,buf1);
			break;
		}
		// dont show the input after this
		char* sep1 = strchr(buf1,separator);
		if (sep1) *sep1 = 0;
		char* sep2 = strchr(buf2,separator);
		if (sep2) *sep2 = 0;

		// clean up white space
		char* start1 = buf1;
		while (*start1 == '\r' || *start1 == '\n' || *start1 == ' ' || *start1 == '\t') ++start1;
		size_t len1 = strlen(start1);
		while (len1 && (start1[len1-1] == '\r' || start1[len1-1] == '\n' || start1[len1-1] == ' ' || start1[len1-1] == '\t')) --len1;

		char* start2 = buf2;
		while (*start2 == '\r' || *start2 == '\n' || *start2 == ' ' || *start2 == '\t') ++start2;
		size_t len2 = strlen(start2);
		while (len2 && (start2[len2-1] == '\r' || start2[len2-1] == '\n' || start2[len2-1] == ' ' || start2[len2-1] == '\t')) --len2;
	
		if (len1 != len2 || strncmp(start1,start2,len1)) 
		{
			if (sep1) *sep1 = ':';
			if (sep2) *sep2 = ':';
			Log(STDUSERLOG,"%5d<<    %s\r\n",n,start1);
			Log(STDUSERLOG,"     >>    %s\r\n",start2);
			fprintf(out,"%5d<<    %s\r\n",n,start1);
			fprintf(out,"     >>    %s\r\n",start2);
		++err;
		}
	}
	FreeBuffer();
	FreeBuffer();
	fclose(in2);
	fclose(in1);
	fprintf(out,"For %s vs %s -  %d lines differ.\r\n",file1,file2,err);
	Log(STDUSERLOG,"For %s vs %s - %d lines differ.\r\n",file1,file2,err);
	fclose(out);
}

static void IndentDisplay(char* one, char* two,char* display)
{
	char* original = display;
	bool start = true;
	size_t len = strlen(one);
	while (len)
	{
		if (!start) 
		{
			strcpy(display,"\r\n");
			display += 2;
		}
		else start = false;
		if (len < 120) 
		{
			strcpy(display,one);
			break;
		}
		unsigned int i = 120;
		while (one[i] && one[i] != ' ') ++i;
		if (one[i]) ++i;
		memmove(display,one,i);
		len -= i;
		display += i;
		*display = 0;
		one += i;
	}

	display += strlen(display);
	len = strlen(two);
	while (len)
	{
		if (len == 1 && two[0] == ' ') break;	 // dont bother
		strcpy(display,"\r\n    ");
		display += 6;
		if (len < 120) 
		{
			strcpy(display,two);
			break;
		}
		unsigned int i = 120;
		while (two[i] && two[i] != ' ') ++i;
		if (two[i]) ++i;
		memmove(display,two,i);
		len -= i;
		display += i;
		*display = 0;
		two += i;
	}
	strcat(display,"\r\n\r\n");
}

static void TrimIt(char* name,uint64 flag) 
{
	//  0 = user->bot
	//  1 = bot->user
	//  2 = topic user-bot
	//  3 = topic bot->user last sentence
	//  4 = indent human
	//  5 = indent bot
	//  6 = user only
	//  7 = tags verify user-bot
	//  8 = topic indent bot
	//  9 = generate user log files from system log
	
	char prior[MAX_BUFFER_SIZE];
	FILE* in = FopenReadWritten(name);
	if (!in) return;
	if ((++filesSeen % 1000) == 0) printf( ((filesSeen % 100000) == 0) ? (char*)"+\r\n" : (char*) "."); // mark progress thru files

	bool header = false;
	FILE* out = FopenUTF8WriteAppend("TMP/tmp.txt");
	char file[MAX_WORD_SIZE];
	*file = 0;
	*prior = 0;
	char* at;
	while (ReadALine(readBuffer,in) >= 0 ) 
	{
		size_t len = strlen(readBuffer);
   		if (!len) continue;
		char copy[MAX_BUFFER_SIZE];
		strcpy(copy,readBuffer);

		// fields in log file are: type, user, bot, ip, resulting topic, (current volley id),  input,  output, dateinfo, possible f:,  followed by rule tags for each issued output.
		
		// fields in regress file are: Start: user:test bot:rose rand:3089 (resulting topic), volleyid,  input:  output: Good morning. 
		// Respond: user:test bot:rose (resulting topic), volleyid input output 

		if (strncmp(readBuffer,"Respond:",8) && strncmp(readBuffer,"Start:",6)) continue; // not a normal line?

		// normal volley

		char user[MAX_WORD_SIZE];
		char* ptr = strstr(readBuffer,"user:") + 5;
		ptr = ReadCompiledWord(ptr,user);

		char bot[MAX_WORD_SIZE];
		ptr = ReadCompiledWord(ptr+4,bot); // skip "bot:"

		if (!strncmp(readBuffer,"Start:",6)) 
		{
			if (flag == 9)
			{
				char file[MAX_WORD_SIZE];
				sprintf(file,"%s/log-%s.txt",users,user);
				FILE* out1 = FopenUTF8WriteAppend(file);
				fprintf(out1,"%s\r\n",copy);
				fclose(out1);
			}
			// other things you could do with start line here
			continue;
		}

		char ip[MAX_WORD_SIZE];
		*ip = 0;
		at = strchr(ptr,'(');
		if (!at) continue;
		*at++ = 0;
		char* end = strchr(at,')');
		if (!end) continue;
		*end = 0;
		char* ipp = strstr(ptr,"ip:");
		if (ipp) ptr = ReadCompiledWord(ipp+3,ipp);

		char topic[MAX_WORD_SIZE];
		at = ReadCompiledWord(at,topic);	
		
		char volley[MAX_WORD_SIZE];
		at = ReadCompiledWord(end+1,volley); 
		char* input = SkipWhitespace(at); // now points to user input start

		char* output = strstr(at," ==> ");
		if (!output) continue;
		*output = 0;	// end of input
		output += 5;
		output = SkipWhitespace(output);  // start of output

		char* when = strstr(output,"When:");
		char* why = "";
		if (when) 
		{
			*when = 0;	// end of output
			when += 5; // start of datestamp

			why = strstr(when,"Why:");
			if (why) // why may not exist (like postprocess output and gesture output)
			{
				*why = 0;	// end of datestamp
				why += 4;  // beginnings of whys
			}
			else why = "";
		}

		// remove our internal reply markers
		char* x = output;
		while ((x = strchr(x,ENDUNIT))) *x++ = ' ';

		// now show the data
		char display[MAX_BUFFER_SIZE];
		display[0] = 0;

		if (flag == 0) sprintf(display,"\r\n%s   =>   %s\r\n",input,output); //  showing both as pair, user first
		else if (flag == 1)  sprintf(display,"\r\n%s   =>   %s\r\n",prior,input);  // pair, bot first
		else if ( flag == 2) sprintf(display,"\r\n%s %s   =>   %s\r\n",topic,input,output); //  showing both as pair, user first, with topic of response
		else if ( flag == 3) sprintf(display,"%s %s   =>   %s\r\n",topic,prior,input); // topic bot user
 		else if ( flag == 4) IndentDisplay(output,input,display);
		else if ( flag == 5) IndentDisplay(input,output,display);
 		else if ( flag == 6) sprintf(display,"%s\r\n",input); // user input only
		else if ( flag == 7) // figure out matching verify
		{
			char tag[MAX_WORD_SIZE];
			char* whyTag = why;
			bool start = true;
			char* atOutput = output;
			if (*whyTag != '~') // had no main motivation
			{
				fprintf(out,"?-?   %s => %s\r\n",input,atOutput); //  showing both as pair, user first, with tag of response and verify input reference
			}
			while (*whyTag == '~') // do each tag
			{
				whyTag = ReadCompiledWord(whyTag,tag); // get tag  which is topic.x.y=name or topic.x.y<topic.a.b (reuse) and optional label which is whytag
				char* separation = strchr(atOutput,'|');
				char* rule;
				if (separation) *separation = 0; // block out rest of output for a moment
				char* dot;
				dot = strchr(tag,'.'); // split of primary topic from rest of tag
				unsigned int topicidx = 0;
				*dot = 0;
				strcpy(topic,tag); // get the primary topic of the tag
				topicidx = FindTopicIDByName(topic,true);
				*dot = '.';
				int id;
				char* rest = GetRuleIDFromText(dot,id); // will point to null, or label, or tag topic
				char verify[MAX_WORD_SIZE];
				strcpy(verify,GetVerify(tag,topicidx, id));
				
				// impacts of indirection
				char* reuseRule = NULL;
				rest = strchr(rest,'~'); // topic start
				if (rest) // look at indirection rule
				{
					char* dot = strchr(rest,'.');
					*dot = 0;
					unsigned int reusetopicid = FindTopicIDByName(rest);
					*dot = '.';
					int reuseid = -1;
					GetRuleIDFromText(dot,reuseid);
					bool updatedVerify = false;
					if (!*verify) 
					{
						strcpy(verify,GetVerify(rest,reusetopicid, reuseid));
						updatedVerify = true;
					}
					reuseRule = GetRule(reusetopicid,reuseid); // the reused rule
					if (!reuseRule || !strstr(reuseRule,"^reuse")) 
					{
						if (updatedVerify) *verify = 0;  // CANCEL not a reuse - have NO verify at all
						reuseRule = 0;
					}
					else rule = GetRule(topicidx,id);	// THIS RULE GETS SHOWN
				}

				rule =  (reuseRule) ?  reuseRule : GetRule(topicidx,id); // show the rule whose pattern matched
				char pattern[MAX_WORD_SIZE];
				*pattern = 0;
				if (rule) GetPattern(rule,NULL,pattern);
				else rule = "-";
				if (!*pattern) strcpy(pattern,"()"); // gambits for example
				if (start) start = false;
				else fprintf(out,"    ");
				fprintf(out,"%s|\"%s\"|%c: %s|%s|%s\r\n",tag,verify,*rule,pattern,input,atOutput); //  showing both as pair, user first, with tag of response and verify input reference
				if (separation) atOutput = separation + 1; // next output
			}
			*display = 0;
		}
		else if ( flag == 8) sprintf(display,"%s\r\n\t(%s) %s\r\n",input,topic,output); // 2liner, indented computer   + topic
		else if ( flag == 9) // build user logs
		{
			char file[MAX_WORD_SIZE];
			sprintf(file,"%s/log-%s.txt",users,user);
			FILE* out1 = FopenUTF8WriteAppend(file);
			fprintf(out1,"%s\r\n",copy);
			fclose(out1);
			continue;
		}
		if (*display) 
		{
			if (!header) 
			{
				header = true;
				char* type = " ";
				if ( flag == 0) type = "user->bot";
				else if (flag == 1) type = "bot->user";
				else if ( flag == 2) type = "topic user->bot";
				else if ( flag == 3) type = "topic bot->user";
				else if ( flag == 4) type = "indent bot";
				else if ( flag == 5) type = "indent human";
				else if ( flag == 6) type = "user only";
				else if ( flag == 7) type = "tags verify user->bot";
				else if ( flag == 8) type = "indent bot + topic";
				char* last = strrchr(name,'/');
				if (last) name = last;
				fprintf(out,"\r\n# ----------------- %s   %s\r\n",name,type);
			}
			fprintf(out,"%s",display);
		}

		strcpy(prior,output); // what bot said previously
	}
    fclose(in);
    if (out) fclose(out);
	Log(STDUSERLOG,"Trim %s complete\r\n",name);
}

static void C_Trim(char* input) // create simple file of user chat from directory
{   
 	char word[MAX_WORD_SIZE];
	char file[MAX_WORD_SIZE];
	char* original = input;
	*file = 0;
	input = ReadCompiledWord(input,word);
	filesSeen = 0;
	if (!strnicmp("log-",word,4)) // is just a user file name
	{
		*directory = 0;	
		if (strstr(word,"txt")) sprintf(file,"%s/%s",users,word);
		else sprintf(file,"%s/%s.txt",users,word);
		input = ReadCompiledWord(input,word);
	}
	else if (strstr(word,".txt")) 
	{
		*directory = 0;	
		strcpy(file,word);
		input = ReadCompiledWord(input,word);
	}
	else if (IsAlphaUTF8(*word)) // directory name or simple user name
	{
		*directory = 0;	
		sprintf(file,"%s/log-%s.txt",users,word);
		FILE* x = FopenReadWritten(file);
		if (x) fclose(x); // see if file exists. if not, then its a directory name
		else 
		{
			strcpy(directory,word);
			*file = 0;
		}
		input = ReadCompiledWord(input,word);

	}
	else strcpy(directory,logs);

	unsigned int flag;
	if (!stricmp(word,"bot2user")) flag = 1;
	else if (!stricmp(word,"useronly") || !stricmp(word,"humanonly")) flag = 6;
	else if (!stricmp(word,"indenthuman")) flag = 4;
	else if (!stricmp(word,"indentbot")) flag = 5;
	else if (!stricmp(word,"usersfromsystem")) flag = 9;
	else flag = atoi(word); 
	
	FILE* out = FopenUTF8Write("TMP/tmp.txt");
	fprintf(out,"# %s\r\n",original);
	Log(STDUSERLOG,"# %s\r\n",input);
	fclose(out);

	if (!*file) WalkDirectory(directory,TrimIt,flag);
	else TrimIt(file,flag);
	printf("\r\n");
}

CommandInfo commandSet[] = // NEW
{//  actual command names must be lower case 
	{"",0,""},
	
	{"\r\n---- Debugging commands",0,""}, 
	{":do",C_Do,"Execute the arguments as an output stream, e.g., invoke a function, set variables, etc"},  
	{":silent",C_Silent,"toggle silent - dont show outputs"}, 
	{":log",C_Log,"dump message into log file"}, 
	{":noreact",C_NoReact,"Disable replying to input"}, 
	{":notrace",C_NoTrace,"Toggle notracing during this topic"},
	{":redo",C_Redo,"Back up to turn n and try replacement user input"}, 
	{":retry",C_Retry,"Back up and try replacement user input or just redo last sentence"}, 
	{":say",C_Say,"Make chatbot say this line"}, 
	{":skip",C_Skip,"Erase next n gambits"}, 
	{":show",C_Show,"All, Input, Mark, Number, Pos, Stats, Topic, Topics, Why, Reject, Newlines"},
	{":trace",C_Trace,"Set trace variable (all none basic prepare match output pattern infer query substitute hierarchy fact control topic pos)"},
	{":why",C_Why,"Show rules causing most recent output"}, 
	
	{"\r\n---- Fact info",0,""}, 
	{":allfacts",C_AllFacts,"Write all facts to TMP/facts.tmp"}, 
	{":facts",C_Facts,"Display all facts with given word or meaning or fact set"}, 
	{":userfacts",C_UserFacts,"Display current user facts"}, 

	{"\r\n---- Topic info",0,""}, 
	{":gambits",C_Gambits,"Show gambit sequence of topic"}, 
	{":pending",C_Pending,"Show current pending topics list"}, 
	{":topicstats",C_TopicStats,"Show stats on all topics or named topic or NORMAL for non-system topics"},
	{":topicinfo",C_TopicInfo,"Show information on a topic"}, 
	{":topics",C_Topics,"Show topics that given input resonates with"}, 
	{":where",C_Where,"What file is the given topic in"}, 
	
	{"\r\n---- System info",0,""},  
	{":commands",C_Commands,"Show all :commands"}, 
	{":context",C_Context,"Display current context labels"}, 
	{":conceptlist",C_ConceptList,"Show all concepts- or with argument show concepts starting with argument"}, 
	{":definition",C_Definition,"Show code of macro named"},
	{":directories",C_Directories,"Show current directories"},
	{":functions",C_Functions,"List all defined system ^functions"},
	{":identify",C_Identify,"Give version data on this CS"},
	{":macros",C_Macros,"List all user-defined ^macros and plans"},
	{":memstats",C_MemStats,"Show memory allocations"},
	{":list",C_List,"v (variables) @ _ m (macros) t (topics)"}, 
	{":queries",C_Queries,"List all defined queries"},
	{":tracedfunctions",C_TracedFunctions,"List all user defined macros currently being traced"},
	{":tracedtopics",C_TracedTopics,"List all topics currently being traced"},
	{":variables",C_Variables,"Display current user/sysytem/match/all variables"}, 
	{":who",C_Who,"show current login/computer pair"}, 
		
	{"\r\n---- Word information",0,""}, 
	{":down",C_Down,"Show wordnet items inheriting from here or concept members"},  
	{":concepts",C_Concepts,"Show concepts triggered by this word"},  
	{":findwords",C_FindWords,"show words matching pattern of letters and *"},
	{":hasflag",C_HasFlag,"List words of given set having or !having some system flag"}, 
	{":nonset",C_Nonset,"List words of POS type not encompassed by given set"}, 
	{":overlap",C_Overlap,"Direct members of set x that are also in set y somehow"}, 
	{":up",C_Up,"Display concept structure above a word"}, 
	{":word",C_Word,"Display information about given word"}, 

	{"\r\n---- System Control commands",0,""}, 
	{":build",C_Build,"Compile a script - filename {nospell,outputspell,reset}"}, 
	{":bot",C_Bot,"Change to this bot"},  
	{":crash",0,"Simulate a server crash"}, 
	{":flush",C_Flush,"Flush server cached user data to files"}, 
	{":quit",C_Quit,"Exit ChatScript"}, 
	{":reset",ResetUser,"Start user all over again, flushing his history"}, 
	{":restart",C_Restart,"Restart Chatscript"}, 
	{":user",C_User,"Change to named user, not new conversation"}, 

	{"\r\n---- Script Testing",0,""},  
	{":autoreply",C_AutoReply,"[OK,Why] use one of those as all input."}, 
	{":prepare",C_Prepare,"Show results of tokenization, tagging, and marking on a sentence"},  
	{":regress",C_Regress,"create or test a regression file"}, 
	{":source",C_Source,"Switch input to named file"}, 
	{":testpattern",C_TestPattern,"See if a pattern works with an input."}, 
	{":testtopic",C_TestTopic,"Try named topic responders on input"}, 
	{":verify",C_Verify,"Given test type & topic, test that rules are accessible. Tests: pattern (default), blocking(default), keyword(default), sample, gambit, all."},  

	{"\r\n---- Document Processing",0,""},  
	{":document",C_Document,"Switch input to named file/directory as a document {single, echo}"}, 
	{":wikitext",C_WikiText,"read wiki xml and write plaintext"},

	{"\r\n---- Analytics",0,""}, 
	{":abstract",C_Abstract,"Display overview of ChatScript topics"}, 
	{":diff",C_Diff,"match 2 files and report lines that differ"}, 
	{":trim",C_Trim,"Strip excess off chatlog file to make simple file TMP/tmp.txt"}, 
	
	{"\r\n---- internal support",0,""}, 
	{":topicdump",C_TopicDump,"Dump topic data suitable for inclusion as extra topics into TMP/tmp.txt (:extratopic or PerformChatGivenTopic)"},
	{":builddict",BuildDictionary," short, short init, or wordnet are options instead of default full"}, 
	{":clean",C_Clean,"Convert source files to NL instead of CR/LF for unix"},
#ifndef DISCARDDATABASE
	{":endpguser",C_EndPGUser,"Switch from postgres user topic to file system"},
#endif
	{":extratopic",C_ExtraTopic,"given topic name and file as output from :topicdump, build in core topic and use it thereafter"},
	{":pennformat",C_PennFormat,"rewrite penn tagfile (eg as output from stanford) as one liners"}, 
	{":pennmatch",C_PennMatch,"FILE {raw ambig} compare penn file against internal result"}, 
	{":pennnoun",C_PennNoun,"locate mass nouns in pennbank"}, 
	{":pos",C_POS,"Show results of tokenization and tagging"},  
	{":sortconcept",C_SortConcept,"Prepare concept file alphabetically"}, 
	{":timepos",C_TimePos,"compute wps average to prepare inputs"},
	{":verifypos",C_VerifyPos,"Regress pos-tagging using default REGRESS/postest.txt file or named file"},
	{":verifyspell",C_VerifySpell,"Regress spell checker against file"}, 
	{":verifysubstitutes",C_VerifySubstitutes,"Regress test substitutes of all kinds"}, 
	{":worddump",C_WordDump,"show words via hardcoded test"}, 

	{0,0,""},	
};

bool VerifyAuthorization(FILE* in) //   is he allowed to use :commands
{
	char buffer[MAX_WORD_SIZE];
	if ( authorizations == (char*)1) // command line does not authorize
	{
		if (in) fclose(in);
		return false;
	}

	//  check command line params
	char* at = authorizations;
	if (at) // command line given
	{
		if (*at == '"') ++at;
		while (*at)
		{
			at = ReadCompiledWord(at,buffer);
			size_t len = strlen(buffer);
			if (at[len-1] == '"') at[len-1] = 0;
			if (!stricmp(buffer,"all") || !stricmp(buffer,callerIP) || (*buffer == 'L' && buffer[1] == '_' && !stricmp(buffer+2,loginID))) //   allowed by IP or L_loginname
			{
				if (in) fclose(in);
				return true;
			}
		}
	}

	if (!in) return (authorizations) ? false : true;			//   no restriction file

	bool result = false;
	while (ReadALine(buffer,in) >= 0 )
    {
		if (!stricmp(buffer,"all") || !stricmp(buffer,callerIP) || (*buffer == 'L' && buffer[1] == '_' && !stricmp(buffer+2,loginID))) //   allowed by IP or L_loginname
		{ 
			result = true;
			break;
		}
	}
	fclose(in);
	return result;
}

void SortTopic(WORDP D,uint64* junk)
{
	if (!(D->internalBits & (BUILD0|BUILD1))) return; // ignore internal system topics (of which there are none)
	if (D->internalBits & TOPIC) Sortit(D->word,(int)(long long)junk);
}

void SortTopic0(WORDP D,uint64 junk)
{
	if (!(D->internalBits & (BUILD0|BUILD1))) return; // ignore internal system concepts
	if (!(D->internalBits & TOPIC)) return;
	CreateFact(MakeMeaning(D),Mmember,MakeMeaning(StoreWord("~_dummy",AS_IS)));
}

typedef std::vector<char*>::const_iterator  citer;

static bool myFunction (char* i,char* j) 
{ 
	if (*i == '~' && *j != '~') return true; // all concepts come first
	if (*i != '~' && *j == '~') return false;
	return stricmp(i,j) < 0; 
}

static bool myInverseFunction (char* i,char* j) 
{ 
	if (*i == '~' && *j != '~') return true; // all concepts come first
	if (*i != '~' && *j == '~') return false;
	return stricmp(i,j) > 0; 
}

void Sortit(char* name,int oneline)   
{
	WORDP D = FindWord(name,0);
	if (!D) return;
	FILE* out = FopenUTF8WriteAppend("cset.txt");

	char word[MAX_WORD_SIZE];
	MakeUpperCopy(word,name);
	int cat = FindTopicIDByName(name); // note if its a category, need to dump its flags also

	// get the concept members 
	std::vector<char*> mylist;
	FACT* F = GetObjectNondeadHead(D);
	bool duplicate = false;
	while (F)
	{
        if (F->verb == Mmember || F->verb == Mexclude)
		{
			strcpy(word,WriteMeaning(F->subject));
			if (*word == '~') MakeUpperCase(word); // cap all concepts and topics
			WORDP E = StoreWord(word);
			if (F->verb == Mexclude) AddInternalFlag(E,BEEN_HERE); // exclude notation
			mylist.push_back(E->word);
			if (F->flags & FACTDUPLICATE) duplicate = true;	// we allow duplicate facts, DONT SORT THIS
		}
		F = GetObjectNondeadNext(F);
	}

	// sort the member list, but do special concept reversed so comes in proper to flood dictionary in correct order
	if (!duplicate) std::sort(mylist.begin(), mylist.end(),!stricmp(name,"~a_dummy") ? myInverseFunction : myFunction);

	// dump the concept lists
	bool drop = false;
	bool close = false;
	char* buffer = AllocateBuffer();
	*buffer = 0;
	for (citer it = mylist.begin(), end = mylist.end(); it < end; ++it)   
	{	  
		if (close) 
		{
			fprintf(out,"%s\r\n",buffer);
			*buffer = 0;
			close = false;
			for (unsigned int j = 1; j <= 10; ++j) strcat(buffer," ");
		}
		if (!drop) // put out the header
		{
			sprintf(buffer, (D->internalBits & TOPIC) ? (char*) "topic: %s " : (char*) "concept: %s ",name);
			drop = true;
			if (cat)
			{
				int flags = GetTopicFlags(cat);
                if (flags & TOPIC_LOWPRIORITY) strcat(buffer,"deprioritize ");
                if (flags & TOPIC_NOBLOCKING) strcat(buffer,"noblocking ");
				if (flags & TOPIC_NOKEYS) strcat(buffer,"nokeys ");
				if (flags & TOPIC_NOPATTERNS) strcat(buffer,"nopatterns ");
				if (flags & TOPIC_NOSAMPLES) strcat(buffer,"nosamples ");
				if (flags & TOPIC_NOGAMBITS) strcat(buffer,"nogambits ");
	            if (flags & TOPIC_KEEP) strcat(buffer,"keep ");
                if (flags & TOPIC_NOSTAY) strcat(buffer,"nostay ");
                if (flags & TOPIC_PRIORITY) strcat(buffer,"priority ");
                if (flags & TOPIC_RANDOM) strcat(buffer,"random ");
                if (flags & TOPIC_REPEAT) strcat(buffer,"repeat ");
				if (flags & TOPIC_SAFE) strcat(buffer,"safe ");
 				if (flags & TOPIC_SHARE) strcat(buffer," share");
                if (flags & TOPIC_SYSTEM) strcat(buffer,"system ");
			}
			else
			{
				uint64 properties = D->properties;
				uint64 bit = START_BIT;	
				while (bit)
				{
					if (properties & bit ) sprintf(buffer + strlen(buffer),"%s ",FindNameByValue(bit));
					bit >>= 1;
				}
				properties = D->systemFlags;
				bit = START_BIT;
				while (bit)
				{
					if (properties & bit) sprintf(buffer + strlen(buffer),"%s ",FindSystemNameByValue(bit));
					bit >>= 1;
				}
			}
			strcat(buffer,"(");
		}
		char* b = buffer + strlen(buffer);
		WORDP G = FindWord(*it);
		if (G->internalBits & BEEN_HERE) // marked for exclude
		{
			G->internalBits ^= BEEN_HERE;
			sprintf(b,"!%s ",*it ); 
		}
		else sprintf(b,"%s ",*it ); 
		if (strlen(buffer) > 180 && !oneline) close = true;
	}
	if (drop) fprintf(out,"%s)\r\n",buffer);
	FreeBuffer();
	fclose(out);
}

#endif

///// ALWAYS AVAILABLE

TestMode DoCommand(char* input,char* output,bool authorize)
{
#ifndef DISCARDTESTING
	if (server && authorize && !VerifyAuthorization(FopenReadOnly("authorizedIP.txt")))  // authorizedIP
	{
		Log(SERVERLOG,"Command %s issued but not authorized\r\n",input);
		return FAILCOMMAND;
	}
	if (authorize) Log(STDUSERLOG,"Command: %s\r\n",input);
	*currentFilename = 0;
	char* ptr = NULL;
	ReadNextSystemToken(NULL,ptr,NULL,false,false);		// flush any pending data in input cache
	if (strnicmp(input,":why",4)) responseIndex = 0;
	return Command(input,output,!authorize); 
#else
	if (server) Log(SERVERLOG,"Command %s issued but testing is discarded\r\n",input);
	return COMMANDED;
#endif
}
