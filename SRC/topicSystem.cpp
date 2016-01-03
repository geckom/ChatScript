#include "common.h"

#define MAX_NO_ERASE 300
#define MAX_REPEATABLE 300
#define TOPIC_LIMIT 10000								// max toplevel rules in a RANDOM topic
topicBlock* topicBlockPtr;
unsigned int numberOfTopics = 0;

// current operating data
bool shared = false;
bool loading = false;

#define MAX_OVERLAPS 1000
static WORDP overlaps[MAX_OVERLAPS];
static  int overlapCount  = 0;
static bool cstopicsystem = false;

static unsigned int oldNumberOfTopics;					// for creating/restoring dynamic topics

unsigned int currentTopicID = 0;						// current topic id
char* currentRule = 0;									// current rule being procesed
int currentRuleID = -1;									// current rule id
int currentReuseID = -1;								// local invoking reuse
int currentReuseTopic = -1;								// topic invoking reuse
int currentRuleTopic = -1;

unsigned short topicContext[MAX_RECENT + 1];
char labelContext[100][MAX_RECENT+ 1];
int inputContext[MAX_RECENT+ 1];
unsigned int contextIndex = 0;
static bool contextResult = false;

bool ruleErased = false;

#define MAX_DISABLE_TRACK 100
static char disableList[MAX_DISABLE_TRACK][200];
static unsigned int disableIndex = 0;

int sampleRule = 0;
unsigned int sampleTopic = 0;

char timeStamp0[20];	// when build0 was compiled
char timeStamp1[20];	// when build1 was compiled
char numberTimeStamp0[20];	// when build0 was compiled
char numberTimeStamp1[20];	// when build1 was compiled
char buildStamp0[150];	// compile command
char buildStamp1[150];	// compile command

// rejoinder info
int outputRejoinderRuleID  = NO_REJOINDER;
int outputRejoinderTopic = NO_REJOINDER;
int inputRejoinderTopic = NO_REJOINDER;					// what topic were we in, that we should check for update
int inputRejoinderRuleID = NO_REJOINDER;

// block erasing with this
static char* keepSet[MAX_NO_ERASE];					// rules not authorized to erase themselves
static unsigned int keepIndex;

// allow repeats with this
static char* repeatableSet[MAX_REPEATABLE];				// rules allowed to repeat output
static unsigned int repeatableIndex;

//   current flow of topic control stack
unsigned int topicIndex = 0;
unsigned int topicStack[MAX_TOPIC_STACK+1];

//   pending topics
unsigned int pendingTopicIndex = 0;
unsigned int pendingTopicList[MAX_TOPIC_STACK+1];
unsigned int originalPendingTopicList[MAX_TOPIC_STACK+1];
unsigned int originalPendingTopicIndex = 0;

// debug information
bool stats = false;				// show how many rules were executed
unsigned int ruleCount = 0;			// how many rules were executed
unsigned int xrefCount = 0;			// how many xrefs were created
unsigned int duplicateCount = 0;	// detecting multiple topics with same name

static unsigned char code[] = {//   value to letter  0-78 (do not use - since topic system cares about it) see uncode
    '0','1','2','3','4','5','6','7','8','9',
    'a','b','c','d','e','f','g','h','i','j',
    'k','l','m','n','o','p','q','r','s','t',
    'u','v','w','x','y','z','A','B','C','D',
    'E','F','G','H','I','J','K','L','M','N',
    'O','P','Q','R','S','T','U','V','W','X',
	'Y','Z','~','!','@','#','$','%','^','&',
	'*','?','/','+','=', '<','>',',','.',
};

static unsigned char uncode[] = {//   letter to value - see code[]
    0,0,0,0,0,0,0,0,0,0,				// 0
    0,0,0,0,0,0,0,0,0,0,				// 10
    0,0,0,0,0,0,0,0,0,0,				// 20
    0,0,0,63,0,65,66,67,69,0,			// 30  33=! (63)  35=# (65)  36=$ (66) 37=% (67) 38=& (69)
    0,0,70,73,77,0,78,72,0,1,			// 40  42=* (70) 43=+ (73) 44=, (77)  46=. (78) 47=/ (72) 0-9 = 0-9
    2,3,4,5,6,7,8,9,0,0,				// 50
    75,74,76,71,64,36,37,38,39,40,		// 60  60=< (75)  61== (74)  62=> (76) 63=? (71) 64=@ 65=A-Z  (36-61)
    41,42,43,44,45,46,47,48,49,50,		// 70
    51,52,53,54,55,56,57,58,59,60,		// 80
    61,0,0,0,68,0,0,10,11,12,			// 90  90=Z  94=^ (68) 97=a-z (10-35)
    13,14,15,16,17,18,19,20,21,22,		// 100
    23,24,25,26,27,28,29,30,31,32,		// 110
    33,34,35,0,0,0,62,0,0,0,			// 120  122=z 126=~ (62)
};

void CleanOutput(char* word)
{
	char* ptr = word-1;
	while (*++ptr)
	{
		if (ptr == word && *ptr == '=' && ptr[1] != ' ') memmove(ptr,ptr+2,strlen(ptr+1)); // comparison operator - remove header
		else if (ptr == word  && *ptr == '*' && IsAlphaUTF8(ptr[1])) memmove(ptr,ptr+1,strlen(ptr)); // * partial word match- remove header
		else if ((*ptr == ' ' || *ptr == '!') && ptr[1] == '=' && ptr[2] != ' ') memmove(ptr+1,ptr+3,strlen(ptr+2)); // comparison operator - remove header
		else if (*ptr == ' ' && ptr[1] == '*' && IsAlphaUTF8(ptr[2])) memmove(ptr+1,ptr+2,strlen(ptr+1)); // * partial word match- remove header
	}
}

char* GetRuleIDFromText(char* ptr, int & id) // passed ptr to or before dot, returns ptr  after dot on rejoinder
{
	if (!ptr) return NULL;
	id = -1;
	char* dot = strchr(ptr,'.'); // align to dot before top level id
	if (!dot) return NULL;
	id = atoi(dot+1); // top level id
	dot = strchr(dot+2,'.');
	if (dot)
	{
		id |= MAKE_REJOINDERID(atoi(dot+1)); // rejoinder id
		while (*++dot && IsDigit(*dot)){;} // point after it to next dot or nothing  - will be =label or .tag
	}
	return dot;
}
///////////////////////////////////////////
/// ENCODE/DECODE
///////////////////////////////////////////

void DummyEncode(char* &data) // script compiler users to reserve space for encode
{
	*data++ = 'a'; 
	*data++ = 'a';
	*data++ = 'a';
}

void Encode(unsigned int val,char* &ptr,bool single)
{ // digits are base 75
	if (single)
	{
		*ptr = code[val % USED_CODES];	
		return;
	}

	if (val > (USED_CODES*USED_CODES*USED_CODES)) ReportBug("Encode val too big")
	int digit1 = val / (USED_CODES*USED_CODES);
    ptr[0] = code[digit1];
	val -= (digit1 * USED_CODES * USED_CODES);
    ptr[1] = code[val / USED_CODES];
    ptr[2] = code[val % USED_CODES];
}

unsigned int Decode(char* data,bool single)
{
	if (single) return uncode[*data];

    unsigned int val = uncode[*data++] * (USED_CODES*USED_CODES);
    val += uncode[*data++] * USED_CODES;
    val += uncode[*data++];

	return val;
}

char* FullEncode(uint64 val,char* ptr) // writes least significant digits first
{ //   digits are base 75
	int digit1 = val % USED_CODES; 
	*ptr++ = code[digit1];
	val = val - digit1; 
	val /= USED_CODES;
	while (val)
	{
		digit1 = val % USED_CODES; 
		*ptr++ = code[digit1];
		val = val - digit1; 
		val /= USED_CODES;
	}
	*ptr++ = ' ';
	*ptr = 0;
	return ptr;
}

uint64 FullDecode(char* data) // read end to front
{
	char* ptr = data + strlen(data);
    uint64 val = uncode[*--ptr];
	while (ptr != data) val = (val * USED_CODES) + uncode[*--ptr];
	return val;
}

void TraceSample(unsigned int topic, unsigned int ruleID,unsigned int how)
{
	FILE* in;
	WORDP D = FindWord(GetTopicName(topic,true));
	if (D)
	{
		char file[MAX_WORD_SIZE];
		sprintf(file,"VERIFY/%s-b%c.txt",D->word+1, (D->internalBits & BUILD0) ? '0' : '1'); 
		in = FopenReadOnly(file); // VERIFY folder
		if (in) // we found the file, now find any verfiy if we can
		{
			char tag[MAX_WORD_SIZE];
			sprintf(tag,"%s.%d.%d",GetTopicName(topic),TOPLEVELID(ruleID),REJOINDERID(ruleID));
			char verify[MAX_WORD_SIZE];
			while (ReadALine(verify,in) >= 0) // find matching verify
			{
				char word[MAX_WORD_SIZE];
				char* ptr = ReadCompiledWord(verify,word); // topic + rule info
				if (!stricmp(word,tag)) // if output  rule has a tag use that
				{
					char junk[MAX_WORD_SIZE];
					ptr = ReadCompiledWord(ptr,junk); // skip the marker
					Log(how,"#! %s",ptr);
					break;
				}
			}
			fclose(in);
		}
	}
}

///////////////////////////////////////////////////////
///// TOPIC DATA ACCESSORS
///////////////////////////////////////////////////////

char* GetTopicFile(unsigned int topic)
{
	topicBlock* block = TI(topic);
	return block->topicSourceFileName;
}

char* RuleBefore(unsigned int topic,char* rule)
{
	char* start = GetTopicData(topic);
	if (rule == start) return NULL;
	rule -= 7; // jump before end marker of prior rule
	while (--rule > start && *rule != ENDUNIT); // back up past start of prior rule
	return (rule == start) ? rule : (rule + 5);
}

static unsigned int ByteCount (unsigned char n)  
{  
	unsigned char count = 0;  
    while (n)  
	{  
       count++;  
       n &= n - 1;  
    }  
    return count;  
 } 

unsigned int TopicUsedCount(unsigned int topic)
{
	topicBlock* block = TI(topic);
 	int size = block->topicBytesRules;
   	unsigned char* bits = block->topicUsed;
	int test = 0;
	unsigned int count = 0;
	while (++test < size) count += ByteCount(*bits++);
	return count;
}

char*  DisplayTopicFlags(unsigned int topic)
{
	static char buffer[MAX_WORD_SIZE];
	*buffer = 0;
	unsigned int flags = GetTopicFlags(topic);
	if (flags) strcat(buffer,"Flags: ");
	if (flags & TOPIC_SYSTEM) strcat(buffer,"SYSTEM ");
	if (flags & TOPIC_KEEP) strcat(buffer,"KEEP ");
	if (flags & TOPIC_REPEAT) strcat(buffer,"REPEAT ");
	if (flags & TOPIC_RANDOM) strcat(buffer,"RANDOM ");
	if (flags & TOPIC_NOSTAY) strcat(buffer,"NOSTAY ");
	if (flags & TOPIC_PRIORITY) strcat(buffer,"PRIORITY ");
	if (flags & TOPIC_LOWPRIORITY) strcat(buffer,"LOWPRIORITY ");
	if (flags & TOPIC_NOBLOCKING) strcat(buffer,"NOBLOCKING ");
	if (flags & TOPIC_NOSAMPLES) strcat(buffer,"NOSAMPLES ");
	if (flags & TOPIC_NOPATTERNS) strcat(buffer,"NOPATTERNS ");
	if (flags & TOPIC_NOGAMBITS) strcat(buffer,"NOGAMBITS ");
	if (flags & TOPIC_NOKEYS) strcat(buffer,"NOKEYS ");
	if (flags & TOPIC_BLOCKED) strcat(buffer,"BLOCKED ");
	if (flags & TOPIC_SHARE) strcat(buffer,"SHARE ");
	return buffer;
}

bool BlockedBotAccess(unsigned int topic)
{
	if (!topic || topic > numberOfTopics) return true;
	topicBlock* block = TI(topic);
	if (block->topicFlags & TOPIC_BLOCKED) return true;
	return (block->topicRestriction && !strstr(block->topicRestriction,computerIDwSpace));
}

char* GetRuleTag(unsigned int& topic,int& id,char* tag)
{
	// tag is topic.number.number or mearerly topic.number
	char* dot = strchr(tag,'.');
	topic = id = 0;
	if (!dot) return NULL;
	*dot = 0;
	topic = FindTopicIDByName(tag);
	*dot = '.';
	if (!topic || !IsDigit(dot[1])) return NULL; 
	id = atoi(dot+1);
	dot = strchr(dot+1,'.');
	if (dot && IsDigit(dot[1]))  id |= MAKE_REJOINDERID(atoi(dot+1));
	return GetRule(topic,id);
}

char* GetLabelledRule(unsigned int& topic, char* label,char* notdisabled,bool &fulllabel, bool& crosstopic,int& id, unsigned int baseTopic)
{
	// ~ means current rule
	// 0 means current top rule (a would be current a rule above us)
	// name means current topic and named rule
	// ~xxx.name means specified topic and named rule
	id = 0;
	fulllabel = false;
	crosstopic = false;
	topic = baseTopic;
	if (*label == '~' && !label[1])  // ~ means current rule
	{
		id = currentRuleID;
		return currentRule;
	}
	else if (*label == '0' && label[1] == 0  )  // 0 means current TOP rule
	{
		id = TOPLEVELID(currentRuleID);
		return  GetRule(topic,id);
	}
	else if (!*label) return NULL;

	char* dot = strchr(label,'.');
	if (dot) // topicname.label format 
	{
		fulllabel = true;
		*dot = 0;
		topic = FindTopicIDByName(label);
		if (!topic) topic = currentTopicID;
		else crosstopic = true;
		label = dot+1; // the label 
	}

	return FindNextLabel(topic,label, GetTopicData(topic),id,!*notdisabled);
}

char* GetVerify(char* tag,unsigned int &topicid, int &id) //  ~topic.#.#=LABEL<~topic.#.#  is a maximally complete why
{
	topicid = 0;
	id = -1;
	if (!*tag)  return "";
	char* verify = AllocateBuffer();
	char topicname[MAX_WORD_SIZE];
	strcpy(topicname,tag);
	char* dot;
	dot = strchr(topicname,'.'); // split of primary topic from rest of tag
	*dot = 0;
	if (IsDigit(*tag)) strcpy(topicname,GetTopicName(atoi(tag)));
	char file[MAX_WORD_SIZE];
	WORDP D = FindWord(topicname);
	if (!D) return "";

	sprintf(file,"VERIFY/%s-b%c.txt",topicname+1, (D->internalBits & BUILD0) ? '0' : '1'); 
	topicid = FindTopicIDByName(topicname,true);
	
	*dot = '.';
	char* rest = GetRuleIDFromText(tag,id);  // rest is tag or label or end
	char c = *rest;
	*rest = 0;	// tag is now pure

	// get verify file of main topic if will have preference over caller
	char display[MAX_WORD_SIZE];
	FILE* in = FopenReadOnly(file); // VERIFY folder
	if (in)
	{
		while (ReadALine(display,in) >= 0) // find matching verify
		{
			char word[MAX_WORD_SIZE];
			char* ptr = ReadCompiledWord(display,word); // topic + rule info
			if (!stricmp(word,tag) && ptr[2] != 'x') // if output  rule has a tag use that - ignore comment rules
			{
				char junk[MAX_WORD_SIZE];
				ptr = ReadCompiledWord(ptr,junk); // skip the marker
				strcpy(verify,ptr);
				break;
			}
		}
		fclose(in);
	}
	*rest = c;
	FreeBuffer();
	return verify;
}


char* GetRule(unsigned int topic, int id)
{
    if (!topic || topic > numberOfTopics || id < 0) return NULL;
	topicBlock* block = TI(topic);

	int ruleID = TOPLEVELID(id);
	int maxrules = RULE_MAX(block->topicMaxRule); 
	if (ruleID >= maxrules) return NULL;

	char* rule = GetTopicData(topic);
	if (!rule) return NULL;

	int rejoinderID = REJOINDERID(id);
	rule += block->ruleOffset[ruleID];	// address of top level rule 
	while (rejoinderID--) 
	{
		rule = FindNextRule(NEXTRULE,rule,ruleID);
		if (!Rejoinder(rule)) return NULL; // ran out of rejoinders
	}
	return rule;
}

void AddTopicFlag(unsigned int topic,unsigned int flag)
{
    if (topic > numberOfTopics || !topic) 
		ReportBug("AddTopicFlag flags topic id %d out of range\r\n",topic)
    else TI(topic)->topicFlags |= flag;
}

void RemoveTopicFlag(unsigned int topic,unsigned int flag)
{
    if (topic > numberOfTopics || !topic) ReportBug("RemoveTopicFlag flags topic %d out of range\r\n",topic)
    else 
	{
		TI(topic)->topicFlags &= -1 ^ flag;
		AddTopicFlag(topic,TOPIC_USED); 
	}
}

char* GetTopicName(unsigned int topic,bool actual)
{
	topicBlock* block = TI(topic);
	if (!topic || !block->topicName) return "";
	if (actual) return block->topicName; // full topic name (if duplicate use number)

	static char name[MAX_WORD_SIZE];
	strcpy(name,block->topicName);
	char* dot = strchr(name,'.'); // if this is duplicate topic name, use generic base name
	if (dot) *dot = 0;
	return name;
}

static char* RuleTypeName(char type)
{
	char* name;
	if (type == GAMBIT) name = "Gambits";
	else if (type == QUESTION) name = "Questions";
	else if (type == STATEMENT) name = "Statements";
	else if (type == STATEMENT_QUESTION) name = "Responders";
	else name = "unknown";
	return name;
}

void SetTopicData(unsigned int topic,char* data)
{
    if (topic > numberOfTopics) ReportBug("SetTopicData id %d out of range\r\n",topic)
	else TI(topic)->topicScript= data; 
}

char* GetTopicData(unsigned int topic)
{
	topicBlock* block = TI(topic);
    if (!topic || !block->topicScript) return NULL;
    if (topic > numberOfTopics)
    {
        ReportBug("GetTopicData flags id %d out of range",topic)
        return 0;
    }
    char* data = block->topicScript; //   predefined topic or user private topic
    return (!data || !*data) ? NULL : (data+JUMP_OFFSET); //   point past accellerator to the t:
}

unsigned int FindTopicIDByName(char* name,bool exact)
{
	if (!name || !*name)  return 0;
    
	char word[MAX_WORD_SIZE];
	*word = '~';
	if (*name == '~' && !name[1]) 
	{
		MakeLowerCopy(word,GetTopicName(currentTopicID,false)); // ~ means current topic always
	}
	else MakeLowerCopy((*name == '~') ? word : (word+1),name);

	WORDP D = FindWord(word);
	duplicateCount = 0;
	while (D && D->internalBits & TOPIC) 
	{
		unsigned int topic = D->x.topicIndex;
		if (!topic) 
		{
			if (!compiling) ReportBug("Missing topic index for %s\r\n",D->word)
			break;
		}
		topicBlock* block = TI(topic);
		if (exact || !block->topicRestriction|| strstr(block->topicRestriction,computerIDwSpace)) return topic; // legal to this bot

		// replicant topics for different bots
		++duplicateCount;
		sprintf(tmpWord,"%s%c%d",word,DUPLICATETOPICSEPARATOR,duplicateCount);
		D = FindWord(tmpWord);
	}
	return 0;
}

void UndoErase(char* ptr,unsigned int topic,unsigned int id)
{
    if (trace & TRACE_TOPIC && CheckTopicTrace())  Log(STDUSERLOG,"Undoing erase %s\r\n",ShowRule(ptr));
	ClearRuleDisableMark(topic,id);
}

char* FindNextRule(signed char level, char* ptr, int& id)
{ // level is NEXTRULE or NEXTTOPLEVEL
	if (!ptr || !*ptr) return NULL;
	char* start = ptr;
	unsigned int offset = Decode(ptr-JUMP_OFFSET);
	if (offset == 0) return NULL; // end of the line
    if (ptr[1] != ':') 
	{
		if (buildID)  BADSCRIPT("TOPIC-10 In topic %s missing colon for responder %s - look at prior responder for bug",GetTopicName(currentTopicID) ,ShowRule(ptr))
		ReportBug("not ptr start of responder %d %s %s - killing data",currentTopicID, GetTopicName(currentTopicID) ,tmpWord)
		TI(currentTopicID)->topicScript = 0; // kill off data
		return NULL;
	}
	ptr +=  offset;	//   now pointing to next responder
	if (Rejoinder(ptr)) id += ONE_REJOINDER;
	else id = TOPLEVELID(id) + 1;
	if (level == NEXTRULE || !*ptr) return (*ptr) ? ptr : NULL; //   find ANY next responder- we skip over + x x space to point ptr t: or whatever - or we are out of them now

    while (*ptr) // wants next top level
    {
		if (ptr[1] != ':')
		{
			char word[MAX_WORD_SIZE];
			strncpy(word,ptr,50);
			word[50] = 0;
			if (buildID) BADSCRIPT("TOPIC-11 Bad layout starting %s %c %s",word,level,start)
			ReportBug("Bad layout bug1 %c The rule just before here may be faulty %s",level,start)
			return NULL;
		}
        if (TopLevelRule(ptr)) break; // found next top level
		offset = Decode(ptr-JUMP_OFFSET);
		if (!offset) return NULL;
		ptr += offset;	// now pointing to next responder
 		if (Rejoinder(ptr)) id += ONE_REJOINDER;
		else id = TOPLEVELID(id) + 1;
   }
	return (*ptr) ? ptr : NULL;
}

bool TopLevelQuestion(char* word)
{
	if (!word || !*word) return false; 
	if (word[1] != ':') return false;
	if (*word != QUESTION && *word != STATEMENT_QUESTION) return false;
	if (word[2] && word[2] != ' ') return false;
	return true;
}

bool TopLevelStatement(char* word)
{
	if (!word || !*word) return false; 
	if (word[1] != ':') return false;
	if (*word != STATEMENT && *word != STATEMENT_QUESTION) return false;
	if (word[2] && word[2] != ' ') return false;
	return true;
}

bool TopLevelGambit(char* word)
{
	if (!word || !*word) return false; 
	if (word[1] != ':') return false;
	if (*word != RANDOM_GAMBIT && *word != GAMBIT) return false;
	if (word[2] && word[2] != ' ') return false;
	return true;
}

bool TopLevelRule(char* word)
{
	if (!word || !*word) return true; //   END is treated as top level
	if (TopLevelGambit(word)) return true;
	if (TopLevelStatement(word)) return true;
	return TopLevelQuestion(word);
}

bool Rejoinder(char* word)
{
	if (!word || !*word) return false; 
	if ((word[2] != 0 && word[2] != ' ') || word[1] != ':' || !IsAlphaUTF8(*word)) return false;
	return (*word >= 'a' && *word <= 'q') ? true : false;
}

int HasGambits(unsigned int topic) // check each gambit to find a usable one (may or may not match by pattern)
{
	if (BlockedBotAccess(topic) || GetTopicFlags(topic) & TOPIC_SYSTEM) return -1; 
	
	unsigned int* map = TI(topic)->gambitTag;
	if (!map) return false; // not even a gambit map
	unsigned int gambitID = *map;
	while (gambitID != NOMORERULES)
	{
		if (UsableRule(topic,gambitID)) return 1;
		gambitID = *++map;
	}
	return 0;
}

char* ShowRule(char* rule,bool concise)
{
	if (rule == NULL) return "?";

	static char result[300];
	result[0] = rule[0];
	result[1] = rule[1];
	result[2] = ' ';
	result[3] = 0;

	// get printable fragment
	char word[MAX_WORD_SIZE];
	char label[MAX_WORD_SIZE];
	char* ruleAfterLabel = GetLabel(rule,label);
	strncpy(word,ruleAfterLabel,(concise) ? 40 : 90);
	word[(concise) ? 40 : 90] = 0;
	if ((int)strlen(word) >= ((concise) ? 40 : 90)) strcat(word,"...   ");
	char* at = strchr(word,ENDUNIT);
	if (at) *at = 0; // truncate at end

	CleanOutput(word);

	strcat(result,label);
	strcat(result," ");
	strcat(result,word);
	return result;
}

char* GetPattern(char* ptr,char* label,char* pattern)
{
	if (label) *label = 0;
	if (!ptr || !*ptr) return NULL;
	if (ptr[1] == ':') ptr = GetLabel(ptr,label);
	else ptr += 3; // why ever true?
	char* patternStart = ptr;
	// acquire the pattern data of this rule
	if (*patternStart == '(') ptr = BalanceParen(patternStart+1); // go past pattern to new token
	int patternlen = ptr - patternStart;
	if (pattern)
	{
		strncpy(pattern,patternStart,patternlen);
		pattern[patternlen] = 0;
	}
	return ptr; // start of output ptr
}

char* GetOutputCopy(char* ptr)
{
	static char buffer[MAX_WORD_SIZE];
	if (!ptr || !*ptr) return NULL;
	if (ptr[1] == ':') ptr = GetLabel(ptr,NULL);
	else ptr += 3; // why ever true?
	char* patternStart = ptr;
	// acquire the pattern data of this rule
	if (*patternStart == '(') ptr = BalanceParen(patternStart+1); // go past pattern to new token
	char* end = strchr(ptr,ENDUNIT);
	if (end)
	{
		size_t len = end-ptr;
		strncpy(buffer,ptr,len);
		buffer[len] = 0;
	}
	else strcpy(buffer,ptr);
	return buffer; // start of output ptr
}

char* GetLabel(char* rule,char* label)
{
	if (label) *label = 0;
	if (!rule || !*rule) return NULL;
    rule += 3; // skip kind and space
 	char c = *rule;
	if (c == '('){;}	// has pattern and no label
	else if (c == ' ')  ++rule; // has no pattern and no label
	else // there is a label
	{
		unsigned int len = c - '0'; // length to jump over label
		if (label)
		{
			strncpy(label,rule+1,len-2);
			label[len-2] = 0;
		}
		rule += len;			// start of pattern (
	}
	return rule;
}

char* FindNextLabel(unsigned int topic,char* label, char* ptr, int &id,bool alwaysAllowed)
{ // id starts at 0 or a given id to resume hunting from
	// Alwaysallowed (0=false, 1= true, 2 = rejoinder) would be true coming from enable or disable, for example, because we want to find the
	// label in order to tamper with its availablbilty. 
	bool available = true;
	while (ptr && *ptr) 
	{
		bool topLevel = !Rejoinder(ptr);
		if (topLevel) available = (alwaysAllowed) ? true : UsableRule(topic,id); 
		// rule is available if a top level available rule OR if it comes under the current rule
		if ((available || TOPLEVELID(id) == (unsigned int) currentRuleID) )
		{
			char ruleLabel[MAX_WORD_SIZE];
			GetLabel(ptr,ruleLabel);
			if  (!stricmp(label,ruleLabel)) return ptr;// is it the desired label?
		}
		ptr = FindNextRule(NEXTRULE,ptr,id); // go to end of this one and try again at next responder (top level or not)
	}
	id = -1;
	return NULL;
}

int GetTopicFlags(unsigned int topic)
{
	return (!topic || topic > numberOfTopics) ? 0 : TI(topic)->topicFlags;
}

void SetTopicDebugMark(unsigned int topic,unsigned int value)
{
	if (!topic || topic > numberOfTopics) return;
	topicBlock* block = TI(topic);
	block->topicDebug = value;
	Log(STDUSERLOG," topictrace %s = %d\r\n",GetTopicName(topic),block->topicDebug);
}

void SetDebugRuleMark(unsigned int topic,unsigned int id)
{
	if (!topic || topic > numberOfTopics) return;
	topicBlock* block = TI(topic);
	id = TOPLEVELID(id);
	unsigned int byteOffset = id / 8; 
	if (byteOffset >= block->topicBytesRules) return; // bad index

	unsigned int bitOffset = id % 8;
	unsigned char* testByte = block->topicDebugRule + byteOffset;
	*testByte ^= (unsigned char) (0x80 >> bitOffset);
}

static bool GetDebugRuleMark(unsigned int topic,unsigned int id) //   has this top level responder been marked for debug
{
	if (!topic || topic > numberOfTopics) return false;
	topicBlock* block = TI(topic);
	id = TOPLEVELID(id);
	unsigned int byteOffset = id / 8; 
	if (byteOffset >= block->topicBytesRules) return false; // bad index

	unsigned int bitOffset = id % 8;
	unsigned char* testByte = block->topicDebugRule + byteOffset;
	unsigned char value = (*testByte & (unsigned char) (0x80 >> bitOffset));
	return value != 0;
}

void FlushDisabled()
{
	for (unsigned int i = 1; i <= disableIndex; ++i) 
	{
		char* at = strchr(disableList[i],'.');
		*at = 0;
		unsigned int topic = FindTopicIDByName(disableList[i],true);
		unsigned int id = atoi(at+1);
		at = strchr(at+1,'.');
		id |= MAKE_REJOINDERID(atoi(at+1));
		ClearRuleDisableMark(topic,id);
	}
	disableIndex = 0;
	ruleErased = false;
}

bool SetRuleDisableMark(unsigned int topic, unsigned int id)
{
	if (!topic || topic > numberOfTopics) return false;
	topicBlock* block = TI(topic);
	id = TOPLEVELID(id);
	unsigned int byteOffset = id / 8; 
	if (byteOffset >= block->topicBytesRules) return false; // bad index

	unsigned int bitOffset = id % 8;
	unsigned char* testByte = block->topicUsed + byteOffset;
	unsigned char value = (*testByte & (unsigned char) (0x80 >> bitOffset));
	if (!value) 
	{
		*testByte |= (unsigned char) (0x80 >> bitOffset);
		AddTopicFlag(topic,TOPIC_USED); 
		if (++disableIndex == MAX_DISABLE_TRACK)
		{
			--disableIndex;
			ReportBug("Exceeding disableIndex");
		}
		sprintf(disableList[disableIndex],"%s.%d.%d",GetTopicName(topic),TOPLEVELID(id),REJOINDERID(id));
		return true;
	}
	else return false;	// was already set
}

void ClearRuleDisableMark(unsigned int topic,unsigned int id)
{
	if (!topic || topic > numberOfTopics) return;
	topicBlock* block = TI(topic);
	id = TOPLEVELID(id);
	unsigned int byteOffset = id / 8; 
	if (byteOffset >= block->topicBytesRules) return; // bad index

	unsigned int bitOffset = id % 8;
	unsigned char* testByte = block->topicUsed + byteOffset;
	*testByte &= -1 ^ (unsigned char) (0x80 >> bitOffset);
	AddTopicFlag(topic,TOPIC_USED); 
}

bool UsableRule(unsigned int topic,unsigned int id) // is this rule used up
{
	if (!topic || topic > numberOfTopics) return false;
	topicBlock* block = TI(topic);
	if (id == (unsigned int) currentRuleID && topic == (unsigned int) currentRuleTopic) return false;	// cannot use the current rule from the current rule
	id = TOPLEVELID(id);
	unsigned int byteOffset = id / 8; 
	if (byteOffset >= block->topicBytesRules) return false; // bad index

	unsigned int bitOffset = id % 8;
	unsigned char* testByte = block->topicUsed + byteOffset;
	unsigned char value = (*testByte & (unsigned char) (0x80 >> bitOffset));
	return !value;
}


///////////////////////////////////////////////////////
///// TOPIC EXECUTION
///////////////////////////////////////////////////////

void ResetTopicReply()
{
	ruleErased = false;		// someone can become liable for erase
    keepIndex = 0;			// for list of rules we won't erase
	repeatableIndex = 0;
}

void AddKeep(char* rule)
{
	for (unsigned int i = 0; i < keepIndex; ++i) 
	{
		if (keepSet[i] == rule) return;
	}
    keepSet[keepIndex++] = rule;
    if (keepIndex >= MAX_NO_ERASE) keepIndex = MAX_NO_ERASE - 1;
}

bool Eraseable(char* rule)
{
	for (unsigned int i = 0; i < keepIndex; ++i)
    {
        if (keepSet[i] == rule) return false; 
	}
	return true;
}

void AddRepeatable(char* rule)
{
    repeatableSet[repeatableIndex++] = rule;
    if (repeatableIndex == MAX_REPEATABLE) --repeatableIndex;
}

bool Repeatable(char* rule)
{
	if (!rule) return true;	//  allowed from :say
	for (unsigned int i = 0; i < repeatableIndex; ++i)
    {
        if (repeatableSet[i] == rule || !repeatableSet[i]) return true; // a 0 value means allow anything to repeat
	}
	return false;
}

void SetErase(bool force)
{ 
	if (planning || !currentRule || !TopLevelRule(currentRule)) return; // rejoinders cant erase anything nor can plans
	if (ruleErased && !force) return;	// done 
	if (!TopLevelGambit(currentRule) && (GetTopicFlags(currentTopicID) & TOPIC_KEEP)) return; // default no erase does not affect gambits
	if (GetTopicFlags(currentTopicID) & TOPIC_SYSTEM || !Eraseable(currentRule)) return; // rule explicitly said keep or was in system topic
	
 	if (SetRuleDisableMark(currentTopicID,currentRuleID))
	{
		ruleErased = true;
		if (trace & TRACE_OUTPUT && CheckTopicTrace()) Log(STDUSERTABLOG,"**erasing %s  %s\r\n",GetTopicName(currentTopicID),ShowRule(currentRule));
	}
}

void SetRejoinder(char* rule)
{
 	if (outputRejoinderRuleID == BLOCKED_REJOINDER) // ^refine set this because rejoinders on that rule are not for rejoinding, they are for refining.
	{
		outputRejoinderRuleID = NO_REJOINDER;
		return;
	}
	if (currentRuleID < 0 || outputRejoinderRuleID != NO_REJOINDER) 
	{
		return; //   not markable OR already set 
	}
	if (GetTopicFlags(currentTopicID) & TOPIC_BLOCKED) 
	{
		return; //   not allowed to be here (must have been set along the way)
	}
 
	char level = TopLevelRule(rule)   ? 'a' :  (*rule+1); // default rejoinder level
	int rejoinderID = currentRuleID;
	char* ptr = FindNextRule(NEXTRULE,rule,rejoinderID);
    if (respondLevel) level = respondLevel; //   random selector wants a specific level to match. so hunt for that level to align at start.
    
    //   now align ptr to desired level. If not found, force to next top level unit
    bool startcont = true;
    while (ptr && *ptr && !TopLevelRule(ptr)) //  walk units til find level matching
    {
        if (startcont && *ptr == level) break;     //   found desired starter
        if (!respondLevel && *ptr < level) return; // only doing sequentials and we are exhausted

        unsigned int priorlevel = *ptr;  //   we are here now
        ptr = FindNextRule(NEXTRULE,ptr,rejoinderID); //   spot next unit is -- if ptr is start of a unit, considers there. if within, considers next and on
		startcont = (ptr && *ptr) ? (*ptr != (int)(priorlevel+1)) : false; //   we are in a subtree if false, rising, since  subtrees in turn are sequential, 
    }

    if (ptr && *ptr == level) //   will be on the level we want
    {
        if (trace & TRACE_OUTPUT && CheckTopicTrace()) Log(STDUSERTABLOG,"  **set rejoinder at %s\r\n",ShowRule(ptr));
        outputRejoinderRuleID = rejoinderID; 
 	    outputRejoinderTopic = currentTopicID;
    }
}

FunctionResult ProcessRuleOutput(char* rule, unsigned int id,char* buffer)
{
	unsigned int oldtrace = trace;
	bool traceChanged = false;
	if ( GetDebugRuleMark(currentTopicID,id))  
	{
		trace = (unsigned int) -1;
		traceChanged = true;
	}

	char* ptr = GetPattern(rule,NULL,NULL);  // go to output

   //   now process response
    FunctionResult result;

	// was this a pending topic before?
	bool old = IsCurrentTopic(currentTopicID);
	AddPendingTopic(currentTopicID); // make it pending for now...more code will be thinking they are in this topic

	unsigned int startingIndex = responseIndex;
	bool oldErase = ruleErased; // allow underling gambits to erase themselves. If they do, we dont have to.
	ruleErased = false;
	Output(ptr,buffer,result);

	if (!ruleErased) ruleErased = oldErase;

	bool responseHappened = startingIndex != responseIndex;
	bool madeResponse = false;
	if (result & FAILCODES) *buffer = 0; // erase any partial output on failures. stuff sent out already remains sent.
	else if (!planning)
	{
		result = (FunctionResult) (result & (-1 ^ ENDRULE_BIT));
		//   we will fail to add a response if:  we repeat  OR  we are doing a gambit or topic passthru
		 madeResponse = (*buffer != 0);
		if (*currentOutputBase) // dont look at "buffer" because it might have been reset
		{
			//   the topic may have changed but OUR topic matched and generated the buffer, so we get credit. change topics to us for a moment.
			//   How might this happen? We generate output and then call poptopic to remove us as current topic.
			//   since we added to the buffer and are a completed pattern, we push the entire message built so far.
			//   OTHERWISE we'd leave the earlier buffer content (if any) for higher level to push
			if (!AddResponse(currentOutputBase,responseControl))
			{
				result = (FunctionResult) (result | FAILRULE_BIT);
 				madeResponse = false;
			}
			else 
			{
				if (TopLevelGambit(rule)) AddTopicFlag(currentTopicID,TOPIC_GAMBITTED); // generated text answer from gambit
				else if (TopLevelRule(rule)) AddTopicFlag(currentTopicID,TOPIC_RESPONDED); // generated text answer from responder
				else AddTopicFlag(currentTopicID,TOPIC_REJOINDERED); 
			}
	   }
	}

	char label[MAX_WORD_SIZE];
	GetLabel(rule,label); // now at pattern if there is one
	if ((madeResponse && *label) || (*label == 'C' && label[1] == 'X' && label[2] == '_')) AddContext(currentTopicID,label);

	// gambits that dont fail try to erase themselves - gambits and responders that generated output directly will have already erased themselves
	if (planning) {;}
	else if (TopLevelGambit(currentRule))
	{
		if (!(result & FAILCODES)) SetErase();
	}
	else if (TopLevelStatement(currentRule) || TopLevelQuestion(currentRule)) // responders that caused output will try to erase, will fail if lower did already
	{
		if (responseHappened) SetErase();	
	}
	
	// set rejoinder if we didnt fail 
	if (!(result & FAILCODES) && (madeResponse || responseHappened) && !planning) SetRejoinder(rule); // a response got made
	if (outputRejoinderRuleID == BLOCKED_REJOINDER) outputRejoinderRuleID = NO_REJOINDER; // we called ^refine. He blocked us from rejoindering. We can clear it now.

	if (planning) {;}
	else if (startingIndex != responseIndex && !(result & (FAILTOPIC_BIT | ENDTOPIC_BIT)));
	else if (!old) RemovePendingTopic(currentTopicID); // if it wasnt pending before, it isn't now
	respondLevel = 0; 
	
	if (traceChanged) trace = oldtrace;
    return result;
}

FunctionResult DoOutput(char* buffer,char* rule, unsigned int id)
{
	FunctionResult result;
	// do output of rule
	PushOutputBuffers();
	currentRuleOutputBase = buffer;
	ChangeDepth(1,"testRule");
	result = ProcessRuleOutput(rule,currentRuleID,buffer);
	ChangeDepth(-1,"testRule");
	PopOutputBuffers();
	return result;
}

FunctionResult TestRule(int ruleID,char* rule,char* buffer)
{
	SAVEOLDCONTEXT()
	unsigned int oldIterator = currentIterator;
	currentIterator = 0;
	currentRule = rule;
	currentRuleID = ruleID;
	currentRuleTopic = currentTopicID;

	unsigned int oldtrace = trace;
	bool traceChanged = false;
	if (GetDebugRuleMark(currentTopicID,currentRuleID)) 
	{
		trace = (unsigned int) -1 ;
		traceChanged = true;
	}
	++ruleCount;
	unsigned int start = 0;
	unsigned int end = 0;
	unsigned int limit = 100; 

retry:
	FunctionResult result = NOPROBLEM_BIT;

	char label[MAX_WORD_SIZE];
    char* ptr = GetLabel(rule,label); // now at pattern if there is one
	if (*label)
	{
		int xx = 0; // debug hook
	}
	if (trace & (TRACE_PATTERN | TRACE_SAMPLE )  && CheckTopicTrace())
	{
		if (*label) Log(STDUSERTABLOG, "try %d.%d %s: \\",TOPLEVELID(ruleID),REJOINDERID(ruleID),label); //  \\  blocks linefeed on next Log call
		else  Log(STDUSERTABLOG, "try %d.%d: \\",TOPLEVELID(ruleID),REJOINDERID(ruleID)); //  \\  blocks linefeed on next Log call
		if (trace & TRACE_SAMPLE && *ptr == '(') TraceSample(currentTopicID,ruleID);// show the sample as well as the pattern
		if (*ptr == '(')
		{
			char pattern[MAX_WORD_SIZE];
			GetPattern(rule,NULL,pattern);
			CleanOutput(pattern);
			Log(STDUSERLOG," %s",pattern);
		}
		Log(STDUSERLOG,"\r\n");
	}
	int whenmatched;
	if (*ptr == '(') // pattern requirement
	{
		unsigned int wildcardSelector = 0;
		unsigned int gap = 0;
		wildcardIndex = 0;
		bool uppercasem = false;
		unsigned int positionStart, positionEnd;
		whenmatched = 0;
		++globalDepth; // indent pattern
 		if (start > wordCount || !Match(ptr+2,0,start,'(',true,gap,wildcardSelector,start,end,uppercasem,whenmatched,positionStart,positionEnd)) result = FAIL_MATCH;  // skip paren and blank, returns start as the location for retry if appropriate
		--globalDepth;
		if (clearUnmarks) // remove transient global disables.
		{
			clearUnmarks = false;
			for (unsigned int i = 1; i <= wordCount; ++i) unmarked[i] = 1;
		}
	}
	
	if (trace & TRACE_LABEL && *label && !(trace & TRACE_PATTERN)  && CheckTopicTrace())
	{
		if (result == NOPROBLEM_BIT) Log(STDUSERTABLOG,"  **Match: %s\r\n",ShowRule(rule));
		else Log(STDUSERTABLOG,"  **fail: %s\r\n",ShowRule(rule));
	}
	if (result == NOPROBLEM_BIT) // generate output
	{
		if (trace & (TRACE_PATTERN|TRACE_MATCH|TRACE_SAMPLE)  && CheckTopicTrace() ) //   display the entire matching responder and maybe wildcard bindings
		{
			if (!(trace & (TRACE_PATTERN|TRACE_SAMPLE))) Log(STDUSERTABLOG, "Try %s",ShowRule(rule)); 
			Log(STDUSERTABLOG,"  **Match: %s",ShowRule(rule)); //   show abstract result we will apply
			if (wildcardIndex)
			{
				Log(STDUSERTABLOG,"  Wildcards: ");
				for (unsigned int i = 0; i < wildcardIndex; ++i)
				{
					if (*wildcardOriginalText[i]) Log(STDUSERLOG,"_%d=%s  /  %s ",i,wildcardOriginalText[i],wildcardCanonicalText[i]);
					else Log(STDUSERLOG,"_%d=  ",i);
				}
			}
			Log(STDUSERLOG,"\r\n");
		}
		if (sampleTopic && sampleTopic == currentTopicID && sampleRule == ruleID) // sample testing wants to find this rule got hit
		{
			result = FAILINPUT_BIT;
			sampleTopic = 0;
		}
		else 
		{
			result = DoOutput(buffer,currentRule,currentRuleID);
		}
		if (result & RETRYRULE_BIT || (result & RETRYTOPRULE_BIT && TopLevelRule(rule)) ) 
		{
			if (--limit == 0)
			{
				result = FAILRULE_BIT;
				ReportBug("Exceeeded retry rule limit");
				goto exit;
			}
			if (whenmatched == NORETRY) {}
			else if (end > start) start = end;	// continue from last match location
			else if (start > MAX_SENTENCE_LENGTH) start = 0; // never matched internal words - is at infinite start
			if (end != NORETRY) goto retry;
		}
	}
exit:
	RESTOREOLDCONTEXT()
	currentIterator = oldIterator;
	
	if (traceChanged) trace = oldtrace;
	return result; 
}

static FunctionResult FindLinearRule(char type, char* buffer, unsigned int& id,unsigned int topic,char* rule) 
{
	if (trace & (TRACE_MATCH|TRACE_PATTERN|TRACE_SAMPLE)  && CheckTopicTrace()) 
		id = Log(STDUSERTABLOG,"\r\n\r\nTopic: %s linear %s: \r\n",GetTopicName(currentTopicID),RuleTypeName(type));
	char* base = GetTopicData(currentTopicID);  
	int ruleID = 0;
	topicBlock* block = TI(currentTopicID);
	unsigned int* map = (type == STATEMENT || type == QUESTION || type == STATEMENT_QUESTION) ? block->responderTag : block->gambitTag;
	ruleID = *map;
    FunctionResult result = NOPROBLEM_BIT;
	unsigned int oldResponseIndex = responseIndex;
	unsigned int* indices =  TI(currentTopicID)->ruleOffset;
	while (ruleID != NOMORERULES) //   find all choices-- layout is like "t: xxx () yyy"  or   "u: () yyy"  or   "t: this is text" -- there is only 1 space before useful label or data
	{
		if (indices[ruleID] == 0xffffffff) break; // end of the line
		char* ptr = base + indices[ruleID]; // the gambit or responder
		if (!UsableRule(currentTopicID,ruleID))
		{
			if (trace & (TRACE_PATTERN|TRACE_SAMPLE) && CheckTopicTrace()) 
			{
				Log(STDUSERTABLOG,"try %d.%d: linear used up  ",TOPLEVELID(ruleID),REJOINDERID(ruleID));
				if (trace & TRACE_SAMPLE && !TopLevelGambit(ptr) && CheckTopicTrace()) TraceSample(currentTopicID,ruleID);// show the sample as well as the pattern
				Log(STDUSERLOG,"\r\n");
			}
		}
		else if (rule && ptr < rule) {;} // ignore rule until zone hit
		else if (type == GAMBIT || (*ptr == type || *ptr == STATEMENT_QUESTION)) // is this the next unit we want to consider?
		{
			result = TestRule(ruleID,ptr,buffer);
			if (result == FAIL_MATCH) result = FAILRULE_BIT;
			if (result & (FAILRULE_BIT | ENDRULE_BIT)) oldResponseIndex = responseIndex; // update in case he issued answer AND claimed failure
 			else if (result & ENDCODES || responseIndex > oldResponseIndex) break; // wants to end or got answer
		}
		ruleID = *++map;
		result = NOPROBLEM_BIT;
	}
	if (result & (ENDINPUT_BIT|FAILINPUT_BIT|FAILSENTENCE_BIT|ENDSENTENCE_BIT|RETRYSENTENCE_BIT|RETRYTOPIC_BIT|RETRYINPUT_BIT)) return result; // stop beyond mere topic
	return (result & (ENDCODES-ENDTOPIC_BIT)) ? FAILTOPIC_BIT : NOPROBLEM_BIT; 
}

static FunctionResult FindRandomRule(char type, char* buffer, unsigned int& id)
{
	if (trace & (TRACE_MATCH|TRACE_PATTERN|TRACE_SAMPLE) && CheckTopicTrace()) id = Log(STDUSERTABLOG,"\r\n\r\nTopic: %s random %s: \r\n",GetTopicName(currentTopicID),RuleTypeName(type));
	char* base = GetTopicData(currentTopicID);  
	topicBlock* block = TI(currentTopicID);
	unsigned int ruleID = 0;
	unsigned  int* rulemap;
	rulemap = (type == STATEMENT || type == QUESTION || type == STATEMENT_QUESTION) ? block->responderTag : block->gambitTag;
	ruleID = *rulemap;

	//   gather the choices
    unsigned int index = 0;
  	unsigned int idResponder[TOPIC_LIMIT];
	while (ruleID != NOMORERULES)
    {
		char* ptr = base + block->ruleOffset[ruleID];
		if (!UsableRule(currentTopicID,ruleID))
		{
			if (trace & (TRACE_PATTERN|TRACE_SAMPLE)  && CheckTopicTrace()) 
			{
				Log(STDUSERTABLOG,"try %d.%d: random used up   ",TOPLEVELID(ruleID),REJOINDERID(ruleID));
				if (trace & TRACE_SAMPLE && !TopLevelGambit(ptr) && CheckTopicTrace()) TraceSample(currentTopicID,ruleID);// show the sample as well as the pattern
				Log(STDUSERLOG,"\r\n");
			}
		}
		else if (type == GAMBIT || (*ptr == type || *ptr == STATEMENT_QUESTION))
		{
			idResponder[index] = ruleID;
			if (++index > TOPIC_LIMIT-1)
			{
               ReportBug("Too many random choices for topic")
               break; 
			}
        }
		ruleID = *++rulemap;
   }

 	FunctionResult result = NOPROBLEM_BIT;
	unsigned int oldResponseIndex = responseIndex;
	//   we need to preserve the ACTUAL ordering information so we have access to the responseID.
    while (index)
    {
        int n = random(index);
		int rule = idResponder[n];
        result = TestRule(rule,block->ruleOffset[rule]+base,buffer);
		if (result == FAIL_MATCH) result = FAILRULE_BIT;
		if (result & (FAILRULE_BIT | ENDRULE_BIT)) oldResponseIndex = responseIndex; // update in case added response AND declared failure
 		else if (result & ENDCODES || responseIndex > oldResponseIndex) break;
        idResponder[n] =  idResponder[--index] ; // erase choice and reset loop index
		result = NOPROBLEM_BIT;
    }
	
	if (result & (FAILSENTENCE_BIT | ENDSENTENCE_BIT | RETRYSENTENCE_BIT | ENDINPUT_BIT|RETRYINPUT_BIT )) return result;
	return (result & (ENDCODES-ENDTOPIC_BIT)) ? FAILTOPIC_BIT : NOPROBLEM_BIT; 
}

static FunctionResult FindRandomGambitContinuation(char type, char* buffer, unsigned int& id)
{
	if (trace & (TRACE_MATCH|TRACE_PATTERN|TRACE_SAMPLE) && CheckTopicTrace()) id = Log(STDUSERTABLOG,"\r\n\r\nTopic: %s random %s: \r\n",GetTopicName(currentTopicID),RuleTypeName(type));
	char* base = GetTopicData(currentTopicID);  
	topicBlock* block = TI(currentTopicID);
	unsigned  int* rulemap = block->gambitTag;	// looking for gambits
	int gambitID = *rulemap;

	FunctionResult result = NOPROBLEM_BIT;
	unsigned int oldResponseIndex = responseIndex;
	bool available = false;
	bool tried = false;
 	while (gambitID != NOMORERULES)
    {
		char* ptr = base + block->ruleOffset[gambitID];
		if (!UsableRule(currentTopicID,gambitID))
		{
			if (trace & (TRACE_PATTERN|TRACE_SAMPLE)  && CheckTopicTrace()) Log(STDUSERTABLOG,"try %d.%d: randomcontinuation used up\r\n",TOPLEVELID(gambitID),REJOINDERID(gambitID));
			if (*ptr == RANDOM_GAMBIT) available = true; //   we are allowed to use gambits part of this subtopic
		}
		else if (*ptr == GAMBIT) 
		{
			if (available) //   we can try it
			{
				result = TestRule(gambitID,ptr,buffer);
				tried = true;
				if (result == FAIL_MATCH) result = FAILRULE_BIT;
				if (result & (FAILRULE_BIT | ENDRULE_BIT)) oldResponseIndex = responseIndex; // update in case he added response AND claimed failure
 				else if (result & ENDCODES || responseIndex > oldResponseIndex) break;
			}
		}
		else if (*ptr == RANDOM_GAMBIT) available = false; //   this random gambit not yet taken
        else break; //   gambits are first, if we didn match we must be exhausted
		result = NOPROBLEM_BIT;
		gambitID = *++rulemap;
	}
	if (result & (FAILSENTENCE_BIT | ENDSENTENCE_BIT | RETRYSENTENCE_BIT| ENDINPUT_BIT|RETRYINPUT_BIT )) return result;
	if (!tried) return FAILRULE_BIT;
	return (result & (ENDCODES-ENDTOPIC_BIT)) ? FAILTOPIC_BIT : NOPROBLEM_BIT; 
}

static FunctionResult FindTypedResponse(char type,char* buffer,unsigned int& id,char* rule)
{
   char* ptr = GetTopicData(currentTopicID);  
    if (!ptr || !*ptr || GetTopicFlags(currentTopicID) & TOPIC_BLOCKED) return FAILTOPIC_BIT;
	topicBlock* block = TI(currentTopicID);
	FunctionResult result;
	SAVEOLDCONTEXT()
	if (rule) result = FindLinearRule(type,buffer,id,currentTopicID,rule);
	else if (type == GAMBIT &&  block->topicFlags & TOPIC_RANDOM_GAMBIT)
	{
		result = FindRandomGambitContinuation(type,buffer,id);
		if (result & FAILRULE_BIT) result = FindRandomRule(type,buffer,id);
	}
	else if (GetTopicFlags(currentTopicID) & TOPIC_RANDOM) result = FindRandomRule(type,buffer,id);
	else result = FindLinearRule(type,buffer,id,currentTopicID,0);
	RESTOREOLDCONTEXT()
    return result;
}

bool CheckTopicTrace() // have not disabled this topic for tracing
{
	WORDP D = FindWord(GetTopicName(currentTopicID));
	return !D || !(D->internalBits & NOTRACE_TOPIC);
}

unsigned int EstablishTopicTrace()
{
	topicBlock* block = TI(currentTopicID);
	unsigned int oldtrace = trace;
	if (block->topicDebug & TRACE_NOT_THIS_TOPIC) 
		trace = 0; // dont trace while  in here
	if (block->topicDebug & (-1 ^ TRACE_NOT_THIS_TOPIC)) 
		trace = block->topicDebug; // use tracing flags of topic
	return oldtrace;
}

FunctionResult PerformTopic(int active,char* buffer,char* rule, unsigned int id)//   MANAGE current topic full reaction to input (including rejoinders and generics)
{//   returns 0 if the system believes some output was generated. Otherwise returns a failure code
//   if failed, then topic stack is spot it was 
	unsigned int tindex = topicIndex;
	topicBlock* block = TI(currentTopicID);
	if (currentTopicID == 0 || !block->topicScript) return FAILTOPIC_BIT;
	if (!active) active = (tokenFlags & QUESTIONMARK)  ? QUESTION : STATEMENT;
    FunctionResult result = RETRYTOPIC_BIT;
	unsigned oldTopic = currentTopicID;
	ChangeDepth(1,"PerformTopic");
	char* topicName = GetTopicName(currentTopicID);
	unsigned int limit = 30;
	unsigned int oldtrace = EstablishTopicTrace();
	char value[100];
	WORDP D = FindWord("^cs_topic_enter");
	if (D && !cstopicsystem)  
	{
		sprintf(value,"( %s %c )",topicName,active);
		cstopicsystem = true;
		Callback(D,value); 
		cstopicsystem = false;
	}
	while (result == RETRYTOPIC_BIT && --limit > 0)
	{
		if (BlockedBotAccess(currentTopicID)) result = FAILTOPIC_BIT;	//   not allowed this bot
		else result = FindTypedResponse((active == QUESTION || active == STATEMENT || active == STATEMENT_QUESTION ) ? (char)active : GAMBIT,buffer,id,rule);

		//   flush any deeper stack back to spot we started
		if (result & (FAILRULE_BIT | FAILTOPIC_BIT | FAILSENTENCE_BIT | RETRYSENTENCE_BIT | RETRYTOPIC_BIT|RETRYINPUT_BIT)) topicIndex = tindex; 
		//   or remove topics we matched on so we become the new master path
	}
	if (!limit) ReportBug("Exceeeded retry topic limit");
	result = (FunctionResult)(result & (-1 ^ ENDTOPIC_BIT)); // dont propogate 
	if (result & FAILTOPIC_BIT) result = FAILRULE_BIT; // downgrade
	if (trace & (TRACE_MATCH|TRACE_PATTERN|TRACE_SAMPLE) && CheckTopicTrace()) 
		id = Log(STDUSERTABLOG,"Result: %s Topic: %s \r\n",ResultCode(result),topicName);
	
	ChangeDepth(-1,"PerformTopic");
	WORDP E = FindWord("^cs_topic_exit");
	if (E && !cstopicsystem) 
	{
		sprintf(value,"( %s %s )",topicName, ResultCode(result));
		cstopicsystem = true;
		Callback(E,value); 
		cstopicsystem = false;
	}
	trace = oldtrace;
	currentTopicID = oldTopic;
	return (result & (ENDSENTENCE_BIT|FAILSENTENCE_BIT|RETRYINPUT_BIT|RETRYSENTENCE_BIT|ENDINPUT_BIT|FAILINPUT_BIT|FAILRULE_BIT)) ? result : NOPROBLEM_BIT;
}

///////////////////////////////////////////////////////
///// TOPIC SAVING FOR USER
///////////////////////////////////////////////////////

char* WriteUserTopics(char* ptr,bool sharefile)
{ 
    char word[MAX_WORD_SIZE];
    //   dump current topics list and current rejoinder
    unsigned int id;

     //   current location in topic system -- written by NAME, so topic data can be added (if change existing topics, must kill off lastquestion)
    *word = 0;
	if (outputRejoinderTopic == NO_REJOINDER) sprintf(ptr,"%d %d 0 # flags, start, input#, no rejoinder\r\n",userFirstLine,volleyCount);
	else 
	{
		sprintf(ptr,"%d %d %s ",userFirstLine,volleyCount,GetTopicName(outputRejoinderTopic));
		ptr += strlen(ptr);
		ptr = FullEncode(outputRejoinderRuleID,ptr); 
		ptr = FullEncode(TI(outputRejoinderTopic)->topicChecksum,ptr);
		sprintf(ptr," # flags, start, input#, rejoindertopic,rejoinderid (%s),checksum\r\n",ShowRule(GetRule(outputRejoinderTopic,outputRejoinderRuleID)));
	}
	ptr += strlen(ptr);
    if (topicIndex)  ReportBug("topic system failed to clear out topic stack\r\n")
   
	for (id = 0; id < pendingTopicIndex; ++id) 
	{
		sprintf(ptr,"%s ",GetTopicName(pendingTopicList[id])); 
		ptr += strlen(ptr);
	}
	sprintf(ptr,"#pending\r\n");
	ptr += strlen(ptr);
 
    //   write out dirty topics
    for (id = 1; id <= numberOfTopics; ++id) 
    {
		topicBlock* block = TI(id);
        char* name = block->topicName;// actual name, not common name
		if (!*name) continue;
        unsigned int flags = block->topicFlags;
		block->topicFlags &= -1 ^ ACCESS_FLAGS;
		if (!(flags & TRANSIENT_FLAGS) || flags & TOPIC_SYSTEM) continue; // no change or not allowed to change
		if (shared && flags & TOPIC_SHARE && !sharefile) continue;
		if (shared && !(flags & TOPIC_SHARE) && sharefile) continue;

		// if this is a topic with a bot restriction and we are not that bot, we dont care about it.
		if (block->topicRestriction && !strstr(block->topicRestriction,computerIDwSpace)) continue; // not our topic

		// see if topic is all virgin still. if so we wont care about its checksum and rule count or used bits
		int size = block->topicBytesRules;
   		unsigned char* bits = block->topicUsed;
		int test = 0;
		if (size) while (!*bits++ && ++test < size); // any rules used? need to track their status if so
		if (test != size || flags & TOPIC_BLOCKED) // has used bits or blocked status, write out erased status info
		{
			//   now write out data- if topic is not eraseable, it wont change, but used flags MIGHT (allowing access to topic)
 			char c = (flags & TOPIC_BLOCKED) ? '-' : '+';
			sprintf(ptr,"%s %c",name,c);
			ptr += strlen(ptr);
			sprintf(ptr," %d ",(test == size) ? 0 : size);
			ptr += strlen(ptr);
			if (test != size) // some used bits exist
			{
				ptr = FullEncode(block->topicChecksum,ptr);
				bits = block->topicUsed; 
				while (size > 0)
				{
					--size;
					unsigned char value = *bits++;
					sprintf(ptr,"%c%c",((value >> 4) & 0x0f) + 'a',(value & 0x0f) + 'a');
					ptr += strlen(ptr);
				}
				*ptr++ = ' ';
			}
			if (flags & TOPIC_GAMBITTED) block->topicLastGambitted = volleyCount; // note when we used a gambit from topic 
			if (flags & TOPIC_RESPONDED) block->topicLastGambitted = volleyCount; // note when we used a responder from topic 
			if (flags & TOPIC_REJOINDERED) block->topicLastGambitted = volleyCount; // note when we used a responder from topic 
			ptr = FullEncode(block->topicLastGambitted,ptr);
			ptr = FullEncode(block->topicLastRespondered,ptr);
			ptr = FullEncode(block->topicLastRejoindered,ptr);
			strcpy(ptr,"\r\n");
			ptr += 2;
			ptr =  OverflowProtect(ptr);
			if (!ptr) return NULL;
		}
    }
	strcpy(ptr,"#`end topics\r\n"); 
	ptr += strlen(ptr);
	return ptr;
}

bool ReadUserTopics()
{
    char word[MAX_WORD_SIZE];
	//   flags, status, rejoinder
	ReadALine(readBuffer, 0);
	char* ptr = ReadCompiledWord(readBuffer,word); 
    userFirstLine = atoi(word); // share has priority (read last)
    ptr = ReadCompiledWord(ptr,word); 
    volleyCount = atoi(word);

    ptr = ReadCompiledWord(ptr,word);  //   rejoinder topic name
	if (*word == '0')  inputRejoinderTopic = inputRejoinderRuleID = NO_REJOINDER; 
    else
	{
		inputRejoinderTopic  = FindTopicIDByName(word,true);
		ptr = ReadCompiledWord(ptr,word); //  rejoinder location
		inputRejoinderRuleID = ((int)FullDecode(word)); 
		// prove topic didnt change (in case of system topic or one we didnt write out)
		unsigned int checksum;
		ptr = ReadCompiledWord(ptr,word); 
		checksum = (unsigned int) FullDecode(word); // topic checksum
		if (!inputRejoinderTopic) inputRejoinderTopic = inputRejoinderRuleID = NO_REJOINDER;  // topic changed
		if (checksum != TI(inputRejoinderTopic)->topicChecksum && TI(inputRejoinderTopic)->topicChecksum && !(GetTopicFlags(inputRejoinderTopic) & TOPIC_SAFE)) inputRejoinderTopic = inputRejoinderRuleID = NO_REJOINDER;  // topic changed
	}

    //   pending stack
    ReadALine(readBuffer,0);
    ptr = readBuffer;
    originalPendingTopicIndex = pendingTopicIndex = 0;
    while (ptr && *ptr) //   read each topic name
    {
        ptr = ReadCompiledWord(ptr,word); //   topic name
		if (*word == '#') break; //   comment ends it
        unsigned int id = FindTopicIDByName(word,true); 
        if (id) 
		{
			originalPendingTopicList[originalPendingTopicIndex++] = id;
			pendingTopicList[pendingTopicIndex++] = id;
		}
    }

    //   read in used topics
    char topicName[MAX_WORD_SIZE];
    while (ReadALine(readBuffer, 0) >= 0) 
    {
        size_t len = strlen(readBuffer); 
        if (len < 3) continue;
		if (*readBuffer == '#') break;
        char* at = readBuffer;
        at = ReadCompiledWord(at,topicName);
		WORDP D = FindWord(topicName);			
		if (!D || !(D->internalBits & TOPIC)) continue; // should never fail unless topic disappears from a refresh
		unsigned int id = D->x.topicIndex;
		if (!id) continue;	//   no longer exists

		topicBlock* block = TI(id);
		at = ReadCompiledWord(at,word); //   blocked status (+ ok - blocked) and maybe safe topic status
		if (*word == '-') block->topicFlags |= TOPIC_BLOCKED|TOPIC_USED; // want to keep writing it out as blocked
		bool safe = (block->topicFlags & TOPIC_SAFE) ? true : false; // implies safe checksum
		unsigned int bytes;
		at = ReadInt(at,bytes); // 0 means use default values otherwise we have used bits to read in
		if (bytes)
		{
			char sum[MAX_WORD_SIZE];
			at = ReadCompiledWord(at,sum);
			unsigned int checksum = (unsigned int)FullDecode(sum);
			if (safe) checksum = 0;	// this is a safe update
			// a topic checksum of 0 implies it was changed manually, and set to 0 because  it was a minor edit.
			block->topicFlags |= TOPIC_USED; 
			unsigned int size = block->topicBytesRules; // how many bytes of data in memory
			bool ignore = false;
			if ((block->topicChecksum && checksum != block->topicChecksum) || size < bytes) ignore = true; // topic changed or has shrunk = discard our data
			unsigned char* bits = block->topicUsed;
			unsigned char* startbits = bits;
			while (*at != ' ') // til byte marks used up
			{
				if (!ignore) *bits++ = ((*at -'a') << 4) + (at[1] - 'a'); 
				at += 2;
			}
			if (!ignore && (unsigned int)((bits - startbits)) != size) ReportBug("Bad updating on topic %s %d %d actual vs %d wanted  %s\r\n",GetTopicName(id), id,(unsigned int)((bits - startbits)),size,readBuffer)
			char val[MAX_WORD_SIZE];
			at = ReadCompiledWord(at+1,val); // skip over the blank that ended the prior loop
			block->topicLastGambitted = (unsigned int)FullDecode(val); // gambits
			at = ReadCompiledWord(at,val);
			block->topicLastRespondered = (unsigned int)FullDecode(val); // responders
			at = ReadCompiledWord(at,val);
			block->topicLastRejoindered = (unsigned int)FullDecode(val); // rejoinders
		}
    }
	if (strcmp(readBuffer,"#`end topics")) 
	{
		ReportBug("Bad file layout")
		return false;
	}

	return true;
 }

//////////////////////////////////////////////////////
/// TOPIC INITIALIZATION
//////////////////////////////////////////////////////
 
void ResetTopicSystem()
{
    ResetTopics();
	topicIndex = 0;
	disableIndex = 0;
	pendingTopicIndex = 0;
	ruleErased = false;	
	for (unsigned int i = 1; i <= numberOfTopics; ++i) 
	{
		if (!*GetTopicName(i)) continue;
		topicBlock* block = TI(i);
		block->topicLastGambitted = 0; 
		block->topicLastRespondered = 0; 
		block->topicLastRejoindered = 0; 
	}
	currentTopicID = 0;
	unusedRejoinder = true; 
	outputRejoinderTopic = outputRejoinderRuleID = NO_REJOINDER; 
	inputRejoinderTopic = inputRejoinderRuleID = NO_REJOINDER; 
 }

void ResetTopics()
{
	for (unsigned int i = 1; i <= numberOfTopics; ++i) ResetTopic(i);
}

 void ResetTopic(unsigned int topic)
{
	if (!topic || topic > numberOfTopics) return;
	if (!*GetTopicName(topic)) return;
	topicBlock* block = TI(topic);
	if (*block->topicName) // normal fully functional topic
	{
		memset(block->topicUsed,0,block->topicBytesRules);
		block->topicFlags &= -1 ^ TRANSIENT_FLAGS;
		block->topicLastGambitted = block->topicLastRespondered = block->topicLastRejoindered = 0;
		AddTopicFlag(topic,TOPIC_USED);
	}
}
 
static void AllocateGlobalTopicMemory(unsigned int total)
{
	numberOfTopics = total;
	total += 2; // reserve the null 0 topic and 1 extra at end for dynamic use
	topicBlockPtr = (topicBlock*) AllocateString(NULL,total,sizeof(topicBlock),true); // reserved space for each topic to have its data
	for (unsigned int i = 0; i <= numberOfTopics; ++i) TI(i)->topicName = "";
}

static WORDP AllocateTopicMemory( unsigned int topic, char* name, uint64 flags, unsigned int topLevelRules, unsigned int gambitCount)
{
	topicBlock* block = TI(topic);
	block->ruleOffset =  (unsigned int*)AllocateString(NULL,(1+topLevelRules), sizeof(int));		// how to find rule n
	block->gambitTag =  (unsigned int*)AllocateString(NULL,( 1 + gambitCount),sizeof(int));     // how to find each gambit
	block->responderTag =  (unsigned int*)AllocateString(NULL,(topLevelRules - gambitCount + 1),sizeof(int)); // how to find each responder
	block->topicMaxRule = topLevelRules | MAKE_GAMBIT_MAX(gambitCount); // count of rules and gambits (and implicitly responders)
	
	unsigned int bytes = (topLevelRules + 7) / 8;	// bytes needed to bit mask the responders and gambits
	if (!bytes) bytes = 1;

	block->topicUsed =  (unsigned char*)AllocateString(NULL,bytes,1,true); // bits representing used up rules
	block->topicDebugRule = (unsigned char*)AllocateString(NULL,bytes,1,true); // bits representing debug this rule
	block->topicBytesRules = (unsigned short)bytes; // size of topic
		
	WORDP D = StoreWord(name); 
	AddInternalFlag(D,(unsigned int)flags);
	D->x.topicIndex = (unsigned short) topic;
	block->topicName = D->word;
		
	//   topic data
	unsigned int i = 0;
	char* ptr = GetTopicData(topic);
	char* base = GetTopicData(topic);
	unsigned int gambitIndex = 0;
	unsigned int responderIndex = 0;
	int id = 0;
	while (ptr && *ptr) // walk all rules
	{
		if (*ptr == GAMBIT || *ptr == RANDOM_GAMBIT) block->gambitTag[gambitIndex++] = i; // tag
		else block->responderTag[responderIndex++] = i;
		if (*ptr == RANDOM_GAMBIT)  block->topicFlags |= TOPIC_RANDOM_GAMBIT;
		block->ruleOffset[i++] = ptr - base; // store direct offset of rule
		if (i == topLevelRules) break;
		ptr = FindNextRule(NEXTTOPLEVEL,ptr,id);
	}
	if (gambitIndex != gambitCount)		ReportBug("Gambits in  %s don't match count. maybe T: instead of t: ?\r\n",name)
	block->gambitTag[gambitIndex] = NOMORERULES;
	block->responderTag[responderIndex] = NOMORERULES;
	block->ruleOffset[i] = NOMORERULES; 
	return D;
}

unsigned int ReadTopicFlags(char* ptr)
{
	unsigned int flags = 0;
	while (*ptr)
	{
		char word[MAX_WORD_SIZE];
		ptr = ReadCompiledWord(ptr,word);
		if (!strnicmp(word,"bot=",4)) // bot restriction on the topic
		{
		}
		else if (!stricmp(word,"deprioritize")) flags |= TOPIC_LOWPRIORITY; 
		else if (!stricmp(word,"noblocking")) flags |= TOPIC_NOBLOCKING; 
 		else if (!stricmp(word,"nopatterns")) flags |= TOPIC_NOPATTERNS; 
 		else if (!stricmp(word,"nogambits")) flags |= TOPIC_NOGAMBITS; 
 		else if (!stricmp(word,"nosamples")) flags |= TOPIC_NOSAMPLES; 
 		else if (!stricmp(word,"nokeys") || !stricmp(word,"nokeywords")  )  flags |= TOPIC_NOKEYS; 
        else if (!stricmp(word,"keep")) flags |= TOPIC_KEEP; 
 		else if (!stricmp(word,"norandom")) flags &= -1 ^TOPIC_RANDOM;
		else if (!stricmp(word,"normal")) flags &= -1 ^TOPIC_PRIORITY;
		else if (!stricmp(word,"norepeat")) flags &= -1 ^TOPIC_REPEAT;
		else if (!stricmp(word,"nostay")) flags |= TOPIC_NOSTAY;
		else if (!stricmp(word,"priority"))  flags |= TOPIC_PRIORITY; 
		else if (!stricmp(word,"random")) flags |= TOPIC_RANDOM;
		else if (!stricmp(word,"repeat")) flags |= TOPIC_REPEAT; 
		else if (!stricmp(word,"safe")) flags |= -1 ^TOPIC_SAFE;
		else if (!stricmp(word,"share")) flags |= TOPIC_SHARE;
		else if (!stricmp(word,"stay")) flags &= -1 ^TOPIC_NOSTAY;
		else if (!stricmp(word,"erase")) flags &= -1 ^TOPIC_KEEP;
		else if (!stricmp(word,"system")) flags |= TOPIC_SYSTEM | TOPIC_KEEP | TOPIC_NOSTAY;
		else if (!stricmp(word,"user")){;}
	}
	return flags;
}

void ReleaseFakeTopics()
{
	// restore hidden topics
	numberOfTopics = oldNumberOfTopics;
	while (--overlapCount >= 0) // restore names on topics hidden
	{
		WORDP D = overlaps[overlapCount];
		TI(D->x.topicIndex)->topicName= D->word;
	}
}

void CreateFakeTopics(char* data) // ExtraTopic can be used to test this, naming file built by topicdump
{
	char word[MAX_WORD_SIZE];
	oldNumberOfTopics = numberOfTopics;
	data = ReadCompiledWord(data,word);
	overlapCount = 0;
	MEANING MtopicName = 0;
	while (ALWAYS)
	{
		if (stricmp(word,"topic:")) return;	// bad information or end of system, ignore it
		data = ReadCompiledWord(data,word); // topic name
		WORDP D = FindWord(word);

		// format of data is:
		// 1. topic: topic_name list_of_flags 
		/// Bot: restriction\r\n
		// keywords: keyword keyword keyword rules:\r\n
		// rule'\r\n
		// rule'\r\n
		// rule'\r\n
		//` OR  topic:

		// disable native topic if there
		if (D) 
		{
			TI(D->x.topicIndex)->topicName = ""; // make prebuilt topic unfindable
			overlaps[overlapCount++] = D;
		}
		MtopicName = MakeMeaning(StoreWord(word));
	
		data = ReadCompiledWord(data,word); // flags
		if (stricmp(word,"flags:")) return;

		char* bot = strstr(data,"Bot:");
		if (!bot) return;
		unsigned int flags = ReadTopicFlags(data);

		/// bot + 4 thru to end is bot description
		char restriction[MAX_WORD_SIZE];
		char* keywords = strstr(bot,"Keywords:");
		*keywords = 0;
		data = bot + 4;
		strcpy(restriction,data);
		data = keywords+9;
		while (ALWAYS)
		{
			data = ReadCompiledWord(data,word);
			if (!stricmp(word,"rules:")) break; // end of keywords
			CreateFact(MakeMeaning(StoreWord(word)),Mmember,MtopicName,FACTTRANSIENT);
		}
		*keywords = 'K';

		char* topicData = SkipWhitespace(data);		
		if (!*topicData) return;

		// tally info
		int id;
		char* ruledata = topicData + JUMP_OFFSET;
		unsigned int gambitCount = 0;
		unsigned int topLevelRules = 0;
		char* endrules = strstr(ruledata,"`000 x");
		if (!endrules) return;

		endrules[5] = 0;
		while (ruledata && *ruledata)
		{
			char type = *ruledata;
			if (type == GAMBIT || type== RANDOM_GAMBIT)
			{
				++gambitCount;
				++topLevelRules;
			}
			else if (type == QUESTION || type == STATEMENT || type == STATEMENT_QUESTION) ++topLevelRules;
			ruledata =  FindNextRule(NEXTTOPLEVEL,ruledata,id);
		}
		unsigned int bytes = (topLevelRules + 7) / 8;	// bytes needed to bit mask the responders and gambits
		if (!bytes) bytes = 1;
		endrules[5] = 'x';
		SetTopicData(++numberOfTopics,topicData);
		AllocateTopicMemory(numberOfTopics, word,  BUILD1|CONCEPT|TOPIC, topLevelRules,gambitCount);
		TI(numberOfTopics)->topicFlags = flags; // carry over flags from topic of same name
		data = ReadCompiledWord(endrules+6,word);
	}
}

static void LoadTopicData(const char* name,uint64 build,bool plan)
{
	FILE* in = FopenReadOnly(name); // TOPIC folder
	if (!in) return;

	char count[MAX_WORD_SIZE];
	char* ptr = count;
	ReadALine(count,in);
	ptr = ReadCompiledWord(ptr,tmpWord);	// skip the number of topics
	if (plan){}
	else if (build & BUILD0) 
	{
		ptr = ReadCompiledWord(ptr,timeStamp0); // Jan04'15
		ptr = ReadCompiledWord(ptr,buildStamp0);

	}
	else if (build & BUILD1) 
	{
		ptr = ReadCompiledWord(ptr,timeStamp1);
		ptr = ReadCompiledWord(ptr,buildStamp1);
	}

	// plan takes 2 lines:
	// 1- PLAN: name:^travel arguments:0  top level rules:14  bytes of data:1453 name of source file: xxx
	// 2- restriction and actual topic data sized by last number of 1st line e/g/ " all "00! ?: ( south * what color be *~2 bear ) White.

	// topic takes 2 lines:
	// 1- TOPIC: name:~happiness flags:0 checksum:11371305158409071022 top level rules:14  gambits:10 reserved:0 bytes of data:1453 name of source file: xxx
	// 2- restriction and actual topic data sized by last number of 1st line e/g/ " all "00! ?: ( south * what color be *~2 bear ) White.
	while (ReadALine(readBuffer,in) >= 0)  
	{
		char* ptr;	
		char name[MAX_WORD_SIZE];
		ptr = ReadCompiledWord(readBuffer,name); // eat TOPIC: 
		if (!*name) break;
		if (!plan && stricmp(name,"topic:"))
		{
			ReportBug("bad topic alignment %s\r\n",name)
			myexit("bad topic alignment");
		}
		if (plan && stricmp(name,"plan:"))
		{
			ReportBug("bad plan alignment %s\r\n",name)
			myexit("bad plan alignment");
		}
		ptr = ReadCompiledWord(ptr,name);
		if (!topicBlockPtr || !TI(0)->topicName)
		{
			if (build == BUILD0) 
			{
				EraseTopicFiles(BUILD0);
				printf("\r\n>>>  TOPICS directory bad. Contents erased. :build 0 again.\r\n\r\n");
			}
			else 
			{
				printf("\r\n>>> TOPICS directory bad. Build1 Contents erased. :build 1 again.\r\n\r\n");
				EraseTopicFiles(BUILD1);
			}
			return;
		}
		compiling = true;
		unsigned int topic = FindTopicIDByName(name); // may preexist
		compiling = false;
		if (!topic) topic = ++currentTopicID;
		else if (plan) myexit("duplicate plan name");
		
		topicBlock* block = TI(topic);
		unsigned int topLevelRules = 0;
		unsigned int gambitCount = 0;
		char argCount[MAX_WORD_SIZE];

		if (plan)
		{
			ptr = ReadCompiledWord(ptr,argCount);
 			ptr = ReadInt(ptr,topLevelRules);
		}
		else
		{
			ptr = ReadInt(ptr,block->topicFlags);
			if (block->topicFlags & TOPIC_SHARE) shared = true; // need more data written into USER zone
			ptr = ReadInt(ptr,block->topicChecksum);
 			ptr = ReadInt(ptr,topLevelRules);
			ptr = ReadInt(ptr,gambitCount); 
		}
		unsigned int datalen;
		ptr = ReadInt(ptr,datalen);

		char* space = AllocateString(0,datalen); // no closing null, just \r\n
		char* copy = space;
		unsigned int didread = fread(copy,1,datalen-2,in); // not yet read \r\n 
		copy[datalen-2] = 0;
		if (didread != (datalen - 2))
		{
			ReportBug("failed to read all of topic/plan %s read: %d wanted: %d \r\n",name,didread,datalen)
			break;
		}
		// read \r\n or \n carefully, since windows and linux do things differently
		char c = 0;
		didread = fread(&c,1,1,in); // \n or \r\n
		if (c != '\r' && c != '\n') 
		{
			ReportBug("failed to end topic/plan %s properly\r\n",name)
			myexit("failed to end topic/plan properly");
		}
		block->topicSourceFileName = AllocateString(ptr); // name of file topic came from

		//   bot restriction if any
		char* start = copy;
		ptr = strchr(start+1,'"') + 2;	// end of bot restriction, start of topic data
		*start = ' '; //  kill start "
		*(ptr-2) = ' '; // kill close "
		*(ptr-1) = 0;	//   end bot restriction - double space after botname
		block->topicRestriction = ( strstr(start," all ")) ? NULL : start;

		SetTopicData(topic,ptr);
		if (!plan) AllocateTopicMemory(topic, name, build|CONCEPT|TOPIC, topLevelRules,gambitCount);
		else
		{
			WORDP P = AllocateTopicMemory(topic, name, FUNCTION_NAME|build|IS_PLAN_MACRO, topLevelRules,0);
			P->w.planArgCount = *argCount - '0'; // up to 9 arguments
		}
	}
	fclose(in);
}

static void ReadPatternData(const char* name)
{
    FILE* in = FopenReadOnly(name); // TOPIC folder
    char word[MAX_WORD_SIZE];
	if (!in) return;
	currentFileLine = 0;
	while (ReadALine(readBuffer,in) >= 0) 
	{
		ReadCompiledWord(readBuffer,word); //   skip over double quote or QUOTE
		if (!*word) continue;
        if (*word == '"') StoreWord(JoinWords(BurstWord(word),false),0,PATTERN_WORD); 
		else if (*word == '\'')   StoreWord(word+1,0,PATTERN_WORD); 
        else  StoreWord(word,0,PATTERN_WORD);
    }
    fclose(in);
}

static void AddRecursiveProperty(WORDP D,uint64 type,bool buildingDictionary)
{
	if (D->internalBits & DELETED_MARK  && !(D->internalBits & TOPIC)) RemoveInternalFlag(D,DELETED_MARK);
	AddProperty(D,type);
	if (buildingDictionary) AddSystemFlag(D,MARKED_WORD);
	if (*D->word != '~')
	{
		if (type & NOUN && !(D->properties & (NOUN_PROPER_SINGULAR|NOUN_SINGULAR|NOUN_PLURAL|NOUN_PROPER_PLURAL))) // infer case 
		{
			if (IsUpperCase(*D->word || IsUpperCase(D->word[1]) || IsUpperCase(D->word[2]))) AddProperty(D,NOUN_PROPER_SINGULAR);
			else AddProperty(D,NOUN_SINGULAR);
		}
		return;
	}
	if (D->inferMark == inferMark) return;
	D->inferMark = inferMark;
	FACT* F = GetObjectNondeadHead(D);
	while (F)
	{
		AddRecursiveProperty(Meaning2Word(F->subject),type,buildingDictionary);
		F = GetObjectNondeadNext(F);
	}
}

static void AddRecursiveRequired(WORDP D,WORDP set,uint64 type,bool buildingDictionary)
{
	if (*D->word != '~')  
	{
		FACT* F = GetSubjectNondeadHead(D);
		while (F)
		{
			if (Meaning2Word(F->object) == set) 
			{
				F->subject |= type;	// must be of this type
				break;
			}
			F = GetObjectNondeadNext(F);
		}

		return; // alter required behavior
	}
	if (D->inferMark == inferMark) return;
	D->inferMark = inferMark;
	if (D->systemFlags & ONLY_NONE) 
		return;	 // DONT PROPOGATE ANYTHING DOWN THRU HERE
	// everybody who is a member of this set
	FACT* F = GetObjectNondeadHead(D);
	while (F)
	{
		AddRecursiveRequired(Meaning2Word(F->subject),D,type,buildingDictionary);
		F = GetObjectNondeadNext(F);
	}
}
static void AddRecursiveFlag(WORDP D,uint64 type,bool buildingDictionary)
{
	AddSystemFlag(D,type);
	if (buildingDictionary) AddSystemFlag(D,MARKED_WORD);
	if (*D->word != '~') return;
	if (D->inferMark == inferMark) return;
	D->inferMark = inferMark;
	FACT* F = GetObjectNondeadHead(D);
	while (F)
	{
		AddRecursiveFlag(Meaning2Word(F->subject),type,buildingDictionary); // but may NOT have been defined yet!!!
		F = GetObjectNondeadNext(F);
	}
}

void InitKeywords(const char* name,uint64 build,bool buildDictionary,bool concept)
{ 
	FILE* in = FopenReadOnly(name); //  TOPICS keywords files
	if (!in) return;

	WORDP holdset[10000];
	uint64 holdprop[10000];
	uint64 holdsys[10000];
	unsigned int holdparse[10000];
	unsigned int holdrequired[10000];
	unsigned int holdindex = 0;
	uint64 type = 0;
	uint64 sys = 0;
	unsigned int parse= 0;
	unsigned int required = 0;
	StartFile(name);
	bool endseen = true;
	MEANING T = 0;
	WORDP set = NULL;
	while (ReadALine(readBuffer, in)>= 0) //~hate (~dislikeverb )
	{
		parse = 0;
		required = 0;
		type = 0;
		sys = 0;
		unsigned int parse= 0;
		char word[MAX_WORD_SIZE];
		char name[MAX_WORD_SIZE];
		char* ptr = readBuffer;
		if (*readBuffer == '~' || endseen || *readBuffer == 'T') // concept, not-a-keyword, topic
		{
			// get the main concept name
			ptr = ReadCompiledWord(ptr,word); //   leaves ptr on next good word
			if (*word == 'T') memmove(word,word+1,strlen(word));
			strcpy(name,word);
			T = ReadMeaning(word,true,true);
			set = Meaning2Word(T);
			AddInternalFlag(set,(unsigned int) (CONCEPT|build));// sets and concepts are both sets. Topics get extra labelled on script load
			if (buildDictionary) AddSystemFlag(set,MARKED_WORD);
			if (set->internalBits & DELETED_MARK && !(set->internalBits & TOPIC)) RemoveInternalFlag(set,DELETED_MARK); // restore concepts but not topics

			// read any properties to mark on the members
			while (*ptr != '(' && *ptr != '"')
			{
				ptr = ReadCompiledWord(ptr,word);
				if (!stricmp(word,"UPPERCASE_MATCH"))
				{
					AddInternalFlag(set,UPPERCASE_MATCH);
					continue;
				}
				uint64 val = FindValueByName(word);
				if ( val) type |= val;
				else 
				{
					val = FindSystemValueByName(word);
					if ( val) sys |= val;
					else 
					{
						val = FindParseValueByName(word);
						if (val) parse |= val;
						else break; // unknown
					}
				}
			}
			AddProperty(set,type);
			AddSystemFlag(set,sys); 
			AddParseBits(set,parse); 
			if (sys & DELAYED_RECURSIVE_DIRECT_MEMBER) sys ^= DELAYED_RECURSIVE_DIRECT_MEMBER; // only mark top set for this recursive membership
			char* dot = strchr(word,'.');
			if (dot) // convert the topic family to the root name --- BUG breaks with amazon data...
			{
				*dot = 0;
				T = ReadMeaning(word,true,true);
			}
			ptr += 2;	//   skip the ( and space
			endseen = false;
		}

		required = set->systemFlags & (PROBABLE_NOUN|PROBABLE_VERB|PROBABLE_ADJECTIVE|PROBABLE_ADVERB); // aka ONLY_NOUN ONLY_VERB etc
		if (set->systemFlags & ONLY_NONE) 

			sys &= -1 ^ ONLY_NONE; // dont pass this on to anyone

		// now read the keywords
		while (ALWAYS)
		{
			ptr = ReadCompiledWord(ptr,word);
			if (*word == ')' ||  !*word  ) break; // til end of keywords or end of line
			MEANING U;
			char* p1 = word;
			if (*word == '!') 
			{
				++p1;
				AddInternalFlag(set,HAS_EXCLUDE);
			}
			bool original = false;
			if (*p1 == '\'') 
			{
				++p1;
				original = true;
			}
			U = ReadMeaning(p1,true,true);

			if (Meaning2Index(U)) U = GetMaster(U); // use master if given specific meaning
				
			WORDP D = Meaning2Word(U);
			if (D->internalBits & DELETED_MARK  && !(D->internalBits & TOPIC)) RemoveInternalFlag(D,DELETED_MARK); 
			if (buildDictionary) AddSystemFlag(D,MARKED_WORD);
			if (type && !strchr(p1+1,'~')) // not dictionary entry
			{
				AddSystemFlag(D,sys);
				AddParseBits(D,parse); 
				AddProperty(D,type); // require type doesnt set the type, merely requires it be that
				if (type & NOUN && *p1 != '~' && !(D->properties & (NOUN_SINGULAR|NOUN_PLURAL|NOUN_PROPER_SINGULAR|NOUN_PROPER_PLURAL|NOUN_NUMBER)))
				{
					if (D->internalBits & UPPERCASE_HASH) AddProperty(D,NOUN_PROPER_SINGULAR);
					else if (IsNumber(word)) AddProperty(D,NOUN_NUMBER);
					else AddProperty(D,NOUN_SINGULAR);
				}
			}
			else if (IsAlphaUTF8(p1[0])) AddSystemFlag(D,PATTERN_WORD); // blocks spell checking to something else
			
			unsigned int index = Meaning2Index(U);
			if (index) U = GetMaster(U); // if not currently the master, switch to master

			 // recursively do all members of an included set. When we see the set here and its defined, we will scan it
			// if we are DEFINING it now, we scan and mark. Eventually it will propogate
			if (*D->word != '~') // do simple word properties
			{
				AddProperty(D,type);
				AddSystemFlag(D,sys);
				AddParseBits(D,parse); 
				U |= (type | required)  & (NOUN|VERB|ADJECTIVE|ADVERB); // add any pos restriction as well

				// if word is proper name, allow it to be substituted
				if (IsUpperCase(*D->word))
				{
					AddProperty(D,NOUN|NOUN_PROPER_SINGULAR); // could have been plural for all we know
					char* underscore = strchr(D->word,'_');
					if (underscore) 
					{
						unsigned int n = 1;
						char* at = underscore-1;
						while ((at = strchr(at+1,'_'))) ++n;
						if (n > 1 && n > GETMULTIWORDHEADER(D)) 
						{
							*underscore = 0;
							WORDP E = StoreWord(D->word);
							*underscore = '_';
							SETMULTIWORDHEADER(E,n);
						}
					}
				}
			}
			else // recurse on concept
			{
				if (type || sys || parse || required)
				{
					holdset[holdindex] = D;
					holdprop[holdindex] = type;
					holdsys[holdindex] = sys;
					holdparse[holdindex] = parse;
					holdrequired[holdindex] = required;
					++holdindex;
					if (holdindex >= 10000) myexit("Too much concept recursion in keywordinit");
				}
			}
	
			MEANING verb = (*word == '!') ? Mexclude : Mmember;
			if (U & ONLY_NONE)
			{
				int xx = 0;
			}
			CreateFact(U,verb,T,(original) ? (FACTDUPLICATE|ORIGINAL_ONLY) : FACTDUPLICATE ); // script compiler will have removed duplicates if that was desired
		}
		if (*word == ')') endseen = true; // end of keywords found. OTHERWISE we continue on next line
	}
	while (holdindex--) // now all local set defines shall have happened- wont work CROSS build zones
	{
		WORDP D = holdset[holdindex];
		type = holdprop[holdindex];
		sys = holdsys[holdindex];
		if (sys & ONLY_NONE)
		{
			int xx = 0;
		}
		parse = holdparse[holdindex];
		required = holdrequired[holdindex];
		if (type) 
		{
			NextInferMark();
			AddRecursiveProperty(D,type,buildDictionary);
		}
		if (sys) 
		{
			NextInferMark();
			AddRecursiveFlag(D,sys,buildDictionary);
		}
		if (parse) 
		{
			NextInferMark();
			AddParseBits(D,parse);
		}
		if (required)
		{
			NextInferMark();
			AddRecursiveRequired(D,D,required,buildDictionary);
		}
	}
	fclose(in);
}

static void InitMacros(const char* name,uint64 build)
{
	FILE* in = FopenReadOnly(name); // TOPICS macros
	if (!in) return;
	currentFileLine = 0;
	while (ReadALine(readBuffer, in)>= 0) //   ^showfavorite O 2 _0 = ^0 _1 = ^1 ^reuse (~xfave FAVE ) 
	{
		if (!*readBuffer) continue;
		char* ptr = ReadCompiledWord(readBuffer,tmpWord); //   the name
		if (!*tmpWord) continue;
		WORDP D = StoreWord(tmpWord,0); 
		AddInternalFlag(D,(unsigned int)(FUNCTION_NAME|build));
		D->x.codeIndex = 0;	//   if one redefines a system macro, that macro is lost.
		ptr = ReadCompiledWord(ptr,tmpWord);
		if (*tmpWord == 'T') AddInternalFlag(D,IS_TABLE_MACRO);  // table macro
		else if (*tmpWord == 'O') AddInternalFlag(D,IS_OUTPUT_MACRO); 
		else if (*tmpWord == 'P') AddInternalFlag(D,IS_PATTERN_MACRO); 
		else if (*tmpWord == 'D') AddInternalFlag(D,IS_PATTERN_MACRO|IS_OUTPUT_MACRO);
		unsigned int val;
		ptr = ReadInt(ptr,val); 
		D->x.macroFlags = (unsigned short) val; // controls on text string as KEEP_QUOTE or not 
		ptr = ReadCompiledWord(ptr,tmpWord); // skip over readable arg count, has arg count embedded also
		D->w.fndefinition = (unsigned char*) AllocateString(ptr);
	}
	fclose(in);
}

void AddContext(unsigned int topic, char* label)
{
	strcpy(labelContext[contextIndex],label);
	topicContext[contextIndex] = (unsigned short) topic;
	inputContext[contextIndex] = (int)volleyCount;
	++contextIndex;
	if (contextIndex == MAX_RECENT) contextIndex = 0; // ring buffer
}

void SetContext(bool val)
{
	contextResult = val;
}

unsigned int InContext(unsigned int topic, char* label)
{
	if (contextResult) return true; // testing override
	int i = contextIndex;
	while (--i != (int)contextIndex)
	{
		if (i < 0) i = MAX_RECENT;
		if (topicContext[i] == 0) break;	// has no context
		if ((int)inputContext[i] <= ((int)volleyCount - 5)) break; //  not close ( last volley == -1 -2 -3 -4 
		if (topic == topicContext[i] && !stricmp(labelContext[i],label)) return inputContext[i];
	}
	return 0;
}

char* WriteUserContext(char* ptr,bool sharefile )
{
	if (!ptr) return NULL;

	// write out recent context
	int i = contextIndex;
	sprintf(ptr,"#context ");
	ptr += strlen(ptr);
	while (--i != (int)contextIndex)
	{
		if (i < 0) i = MAX_RECENT;
		if (topicContext[i] == 0) break;
		if ((int)inputContext[i] <= ((int)volleyCount - 5)) break; //  not close 
		sprintf(ptr,"%s %d %s ", GetTopicName(topicContext[i]),inputContext[i],labelContext[i]);
		ptr += strlen(ptr);
	}
	strcpy(ptr,"\r\n");
	memset(topicContext,0,sizeof(topicContext));
	contextIndex = 0;
	return ptr + strlen(ptr);
}

bool ReadUserContext()
{
	char word[MAX_WORD_SIZE];
    ReadALine(readBuffer, 0); 
	char* ptr = readBuffer;
	ptr = ReadCompiledWord(ptr,word);
	if (stricmp(word,"#context")) return false; // cant handle it
	memset(topicContext,0,sizeof(topicContext));
	contextIndex = 0;
	while (ptr && *ptr)
	{
		ptr = ReadCompiledWord(ptr,word);
		if (!*word) break;
		topicContext[contextIndex] = (unsigned short) FindTopicIDByName(word);
		if (!topicContext[contextIndex]) return false;
		ptr = ReadCompiledWord(ptr,word);
		inputContext[contextIndex] = atoi(word);
		ptr = ReadCompiledWord(ptr,(char*) &labelContext[contextIndex]);
		++contextIndex;
	}
	return true;
}

static void InitTopicMemory()
{
	memset(topicContext,0,sizeof(topicContext));
	
	unsigned int total;
	topicStack[0] = 0;
	numberOfTopics = 0;
	FILE* in = FopenReadOnly("TOPIC/script0.txt"); // TOPICS
	if (in)
	{
		ReadALine(readBuffer,in);
		ReadInt(readBuffer,total);
		fclose(in);
		numberOfTopics += total;
	}
	in = FopenReadOnly("TOPIC/script1.txt"); // TOPICS
	if (in)
	{
		ReadALine(readBuffer,in);
		ReadInt(readBuffer,total);
		fclose(in);
		numberOfTopics += total;
	}
	in = FopenReadOnly("TOPIC/plans0.txt"); // TOPICS
	if (in)
	{
		ReadALine(readBuffer,in);
		ReadInt(readBuffer,total);
		fclose(in);
		numberOfTopics += total;
	}
	in = FopenReadOnly("TOPIC/plans1.txt"); // TOPICS
	if (in)
	{
		ReadALine(readBuffer,in);
		ReadInt(readBuffer,total);
		fclose(in);
		numberOfTopics += total;
	}
	if (numberOfTopics) AllocateGlobalTopicMemory(numberOfTopics);
}

static void AddRecursiveMember(WORDP D, WORDP set)
{
	if (*D->word != '~')
	{
		CreateFact(MakeMeaning(D),Mmember,MakeMeaning(set));
		return;
	}
	if (D->inferMark == inferMark) return; // concept already seen
	D->inferMark = inferMark;
	FACT* F = GetObjectNondeadHead(D);
	while (F)
	{
		AddRecursiveMember(Meaning2Word(F->subject),set);
		F = GetObjectNondeadNext(F);
	}
}

static void IndirectMembers(WORDP D, uint64 pattern)
{ // we want to recursively get members of this concept, but waited til now for any subset concepts to have been defined
	if (D->systemFlags & DELAYED_RECURSIVE_DIRECT_MEMBER) // this set should acquire all its indirect members now
	{
		NextInferMark();
		D->inferMark = inferMark;
		FACT* F = GetObjectNondeadHead(D);
		while (F)
		{
			if (F->verb == Mmember) AddRecursiveMember(Meaning2Word(F->subject),D);
			F = GetObjectNondeadNext(F);
		}
	}
}

void LoadTopicSystem() // reload all topic data
{
	//   purge any prior topic system - except any patternword marks made on basic dictionary will remain (doesnt matter if we have too many marked)
	ReturnDictionaryToWordNet(); // return dictionary and string space to pretopic conditions
	*timeStamp0 = *timeStamp1 = 0;

	printf("WordNet: dict=%ld  fact=%ld  stext=%ld %s\r\n",(long int)(dictionaryFree-dictionaryBase),(long int)(factFree-factBase),(long int)(stringBase-stringFree),dictionaryTimeStamp);

	InitTopicMemory();
	ClearBotVariables();
	WORDP wordnetBase = dictionaryFree;
	char* preallocate = stringFree;

	InitKeywords("TOPIC/keywords0.txt",BUILD0); 
	ReadFacts("TOPIC/facts0.txt",BUILD0);
	InitMacros("TOPIC/macros0.txt",BUILD0);
	ReadFacts("TOPIC/dict0.txt",BUILD0); //   FROM topic system build of topics
	ReadPatternData("TOPIC/patternWords0.txt");
	char* prescript = stringFree;
	currentTopicID = 0;
	LoadTopicData("TOPIC/script0.txt",BUILD0,false);
	LoadTopicData("TOPIC/plans0.txt",BUILD0,true);
	ReadSubstitutes("TOPIC/private0.txt",DO_PRIVATE,true);
	ReadCanonicals("TOPIC/canon0.txt");
	char data[MAX_WORD_SIZE];
	sprintf(data,"Build0:  dict=%ld  fact=%ld  dtext=%ld stext=%ld %s %s\r\n",(long int)(dictionaryFree-wordnetBase),(long int)(factFree-wordnetFacts),(long int)(preallocate-prescript),(long int)(prescript-stringFree),timeStamp0,buildStamp0);
	if (server)  Log(SERVERLOG, "%s",data);
	else printf("%s",data);

	Build0LockDictionary();
	preallocate = stringFree;
	ReadPatternData("TOPIC/patternWords1.txt");
	wordnetBase = dictionaryFree;
	InitKeywords("TOPIC/keywords1.txt",BUILD1);
	InitMacros("TOPIC/macros1.txt",BUILD1);
	ReadFacts("TOPIC/dict1.txt",BUILD1);
	ReadFacts("TOPIC/facts1.txt",BUILD1);
	prescript = stringFree;
	LoadTopicData("TOPIC/script1.txt",BUILD1,false);
	LoadTopicData("TOPIC/plans1.txt",BUILD1,true);
	ReadSubstitutes("TOPIC/private1.txt",DO_PRIVATE,true);
	ReadCanonicals("TOPIC/canon1.txt");
	
	WalkDictionary(IndirectMembers,0); // having read in all concepts, handled delayed word marks
	sprintf(data,"Build1:  dict=%ld  fact=%ld  dtext=%ld stext=%ld %s %s\r\n",(long int)(dictionaryFree-wordnetBase),(long int)(factFree-build0Facts),(long int)(preallocate-prescript),(long int)(prescript-stringFree),timeStamp1,buildStamp1);
	if (server)  Log(SERVERLOG, "%s",data);
	else printf("%s",data);
	ReadLivePosData(); // any needed concepts must have been defined by now.

	Callback(FindWord("^csboot"),"()"); // do before world is locked
	
	NoteBotVariables();
	preallocate = stringFree;
	// StoreWord("$cs_randindex",0);	// so it is before the freeze WHY!!  cant write on it then
    FreezeBasicData();
}


///////////////////////////////////////////////////////////
/// PENDING TOPICS
///////////////////////////////////////////////////////////

char* ShowPendingTopics()
{
	static char word[MAX_WORD_SIZE];
	*word = 0;
	char* ptr = word;
	for (int i = pendingTopicIndex-1; i >= 0; --i)
	{
		sprintf(ptr,"%s ",GetTopicName(pendingTopicList[i])); 
		ptr += strlen(ptr);
	}
	return word;
}

void GetActiveTopicName(char* buffer)
{
	unsigned int topic = currentTopicID;
	*buffer = 0;

	// the real current topic might be the control topic or a user topic
	// when we are in a user topic, return that or something from the nested depths. Otherwise return most pending topic.
	if (currentTopicID && !(GetTopicFlags(currentTopicID) & (TOPIC_SYSTEM|TOPIC_BLOCKED|TOPIC_NOSTAY))) strcpy(buffer,GetTopicName(currentTopicID,false)); // current topic is valid
	else if (topicIndex) // is one of these topics a valid one
	{
		for (unsigned int i = topicIndex; i > 1; --i) // 0 is always the null topic
		{
			if (!(GetTopicFlags(topicStack[i]) & (TOPIC_SYSTEM|TOPIC_BLOCKED|TOPIC_NOSTAY)))
			{
				strcpy(buffer,GetTopicName(topicStack[i],false));
				break;
			}
		}
	}
	if (!*buffer) // requests current pending topic
	{
		topic = GetPendingTopicUnchanged();
		if (topic) strcpy(buffer,GetTopicName(topic,false));
	}
}

void AddPendingTopic(unsigned int topic)
{	//   these are topics we want to return to
	//   topics added THIS turn are most pending in first stored order
	//   topics added previously should retain their old order 
	// - a topic is pending if user says it is OR we execute the output side of one of its rules (not just the pattern side)
	if (!topic || planning) return;
	if (GetTopicFlags(topic) & (TOPIC_SYSTEM|TOPIC_NOSTAY|TOPIC_BLOCKED)) 	//   cant add this but try its caller
	{
		// may not recurse in topics
		for (unsigned int i = topicIndex; i >= 1; --i) // #1 will always be 0, the prior nontopic
		{
			topic = topicStack[i];
			if (i == 1)  return; // no one to add
			if (GetTopicFlags(topic) & (TOPIC_SYSTEM|TOPIC_NOSTAY|TOPIC_BLOCKED)) continue;	//   cant 
			break;
		}
	}

	bool removed = RemovePendingTopic(topic);	//   remove any old reference
	pendingTopicList[pendingTopicIndex++] = topic;
	if (pendingTopicIndex >= MAX_TOPIC_STACK) memmove(&pendingTopicList[0],&pendingTopicList[1],sizeof(int) * --pendingTopicIndex);
	if (trace & TRACE_OUTPUT && !removed && CheckTopicTrace()) Log(STDUSERLOG,"Adding pending topic %s\r\n",GetTopicName(topic));
}

void PendingTopics(int set)
{
	SET_FACTSET_COUNT(set,0);
	for (unsigned int i = 0; i < pendingTopicIndex; ++i) AddFact(set,CreateFact(MakeMeaning(FindWord(GetTopicName(pendingTopicList[i]))),Mpending,MakeMeaning(StoreWord(i)),FACTTRANSIENT));  // (~topic pending 3) 
}

bool IsCurrentTopic(unsigned int topic) // see if topic is an already pending one, not current
{
	for (unsigned int i = 0; i < pendingTopicIndex; ++i) 
	{
		if (pendingTopicList[i] == topic) 
			return true;
	}
	return false;
}

void ClearPendingTopics()
{
	 pendingTopicIndex = 0;
}

bool RemovePendingTopic(unsigned int topic)
{
	for (unsigned int i = 0; i < pendingTopicIndex; ++i)
	{
		if (pendingTopicList[i] == topic)
		{
			memmove(&pendingTopicList[i],&pendingTopicList[i+1],sizeof(int) * (--pendingTopicIndex - i));
			return true;
		}
	}
	return false;
}

unsigned int GetPendingTopicUnchanged()
{
	if (!pendingTopicIndex) return 0;	//   nothing there
	return pendingTopicList[pendingTopicIndex-1];
}


///////////////////////////////////////////////////////////
/// EXECUTING CODE TOPICS
///////////////////////////////////////////////////////////

int TopicInUse(unsigned int topic)
{
	if (topic == currentTopicID) return -1;
	
	// insure topic not already in progress
	for (unsigned int i = 1; i <= topicIndex; ++i) 
	{
		if (topicStack[i] == topic) return -1; // already here
	}

	return 0;
}

int PushTopic(unsigned int topic) // -1 = failed  0 = unneeded  1 = pushed 
{
	if (topic == currentTopicID) 
	{
		if (trace & TRACE_TOPIC && CheckTopicTrace()) Log(STDUSERLOG,"Topic is already current\r\n");
		return 0;  // current topic
	}
	else if (!topic)
	{
		ReportBug("PushTopic topic missing")
		return -1;
	}

	// insure topic not already in progress
	if (TopicInUse(topic) == -1)
	{
		if (trace & TRACE_TOPIC && CheckTopicTrace()) Log(STDUSERLOG,"Topic is already pending\r\n");
		return -1; // already here
	}
    topicStack[++topicIndex] = currentTopicID; // [1] will be 0 
    if (topicIndex >= MAX_TOPIC_STACK) 
    {
		--topicIndex;
        ReportBug("PusTopic overflow")
        return -1;
    }
	currentTopicID = topic; 
    return 1;
}

void PopTopic()
{
	if (topicIndex) currentTopicID = topicStack[topicIndex--];
	else currentTopicID = 0;	// no topic now
}
