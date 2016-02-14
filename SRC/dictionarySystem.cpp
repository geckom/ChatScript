#include "common.h"

#ifdef INFORMATION

This file covers routines that create and access a "dictionary entry" (WORDP) and the "meaning" of words (MEANING).

The dictionary acts as the central hash mechanism for accessing various kinds of data.

The dictionary consists of data imported from WORDNET 3.0 (copyright notice at end of file) + augmentations + system and script pseudo-words.

A word also gets the WordNet meaning ontology (->meanings & ->meaningCount). The definition of meaning in WordNet 
is words that are synonyms in some particular context. Such a collection in WordNet is called a synset. 

Since words can have multiple meanings (and be multiple parts of speech), the flags of a word are a summary
of all of the properties it might have and it has a list of entries called "meanings". Each entry is a MEANING 
and points to the circular list, one of which marks the word you land at as the synset head. 
 This is referred to as the "master" meaning and has the gloss (definition) of the meaning. The meaning list of a master node points back to 
all the real words which comprise it.

Since WordNet has an ontology, its synsets are hooked to other synsets in various relations, particular that
of parent and child. ChatScript represents these as facts. The hierarchy relation uses the verb "is" and
has the child as subject and the parent as object. Such a fact runs from the master entries, not any of the actual 
word entries. So to see if "dog" is an "animal", you could walk every meaning list of the word animal and
mark the master nodes they point at. Then you would search every meaning of dog, jumping to the master nodes,
then look at facts with the master node as subject and the verb "is" and walk up to the object. If the object is 
marked, you are there. Otherwise you take that object node as subject and continue walking up. Eventually you arrive at
a marked node or run out at the top of the tree.

Some words DO NOT have a master node. Their meaning is defined to be themselves (things like pronouns or determiners), so
their meaning value for a meaning merely points to themselves.
The meaning system is established by building the dictionary and NEVER changes thereafter by chatbot execution.
New words can transiently enter the dictionary for various purposes, but they will not have "meanings".

A MEANING is a reference to a specific meaning of a specific word. It is an index into the dictionary 
(identifying the word) and an index into that words meaning list (identifying the specific meaning).
An meaning list index of 0 refers to all meanings of the word. A meaning index of 0 can also be type restricted
so that it only refers to noun, verb, adjective, or adverb meanings of the word.

Since there are only two words in WordNet with more than 63 meanings (break and cut) we limit all words to having no
more than 63 meanings by discarding the excess meanings. Since meanings are stored most important first,
these are no big loss. This leaves room for the 5 essential type flags used for restricting a generic meaning.

Space for dictionary words, strings, and the meanings of words come from a common pool. Dictionary words are
allocated linearly forward in the pool, while strings and meanings are allocated linearly backwards. Thus
all dictionary entries are indexable as a giant array.

The dictionary separately stores uppercase and lowercase forms of the same words (since they have different meanings).
There is only one uppercase form stored, so United and UnItED would be saved as one entry. The system will have
to decide which case a user intended, since they may not have bothered to capitalize a proper noun, or they 
may have shouted a lowercase noun, and a noun at the start of the sentence could be either proper or not.

Dictionary words are hashed as lower case, but if the word has an upper case letter it will be stored
in the adjacent higher bucket. Words of the basic system are stored in their appropriate hash bucket.
After the basic system is read in, the dictionary is frozen. This means it remembers the spots the allocation
pointers are at for the dictionary and string space and is using mark-release memory management.

Words created on the fly (after a freeze) by interacting with a user are always stored in bucket 0. 
This allows the system to instantly discard them when the interaction has been processed merey by 
zeroing bucket 0. The string space and dictionary space allocated to those on-the-fly words are merely 
"released" back to the values at the time of dictionary freeze.

We mark sysnet entries with the word & meaning number & POS of word in the dictionary entry. The POS not used explicitly by lots of the system
but is needed when seeing the dictionary definitions (:word) and if one wants to use pos-restricted meanings in a match or in keywords.

#endif

#define HASH_EXTRA		2					// +1 for being 1-based and +1 for having uppercase bump

static unsigned int propertyRedefines = 0;	// property changes on locked dictionary entries
static unsigned int flagsRedefines = 0;		// systemflags changes on locked dictionary entries

bool buildDictionary = false;				// indicate when building a dictionary
char dictionaryTimeStamp[20];		// indicate when dictionary was built
char language[40];							// indicate current language used
char* mini = "";

static unsigned int rawWords = 0;	

static unsigned char* writePtr;				// used for binary dictionary writes

// memory data
#define MAX_STRING_SPACE 35000000  // transient string space 35MB
unsigned long maxHashBuckets = MAX_HASH_BUCKETS;
bool setMaxHashBuckets = false;
uint64 maxDictEntries = MAX_ENTRIES;
unsigned long maxStringBytes = MAX_STRING_SPACE;
unsigned int userTopicStoreSize,userTableSize; // memory used which we will display
char livedata[500];		// where is the livedata folder
char englishFolder[500];		// where is the livedata english folder
char systemFolder[500];		// where is the livedata system folder

MEANING posMeanings[64];				// concept associated with propertyFlags of WORDs
MEANING sysMeanings[64];				// concept associated with systemFlags of WORDs

bool fullDictionary = true;				// we have a big master dictionary, not a mini dictionary

#ifndef DISCARDDICTIONARYBUILD
void LoadRawDictionary(int mini);
#endif

char* Index2String(unsigned int offset) 
{ 
	if (!offset) return NULL;
	char* ptr = stringBase - offset;
	if (ptr < stringFree)  
	{
		ReportBug("String offset into free space\r\n");
		return NULL;
	}
	if (ptr > stringBase)  
	{
		ReportBug("String offset before string space\r\n");
		return NULL;
	}
	return ptr;
}

void SetPlural(WORDP D,MEANING M) 
{
	PrepareConjugates(D); 
	AccessPlural(D) = M; 
}

void PrepareConjugates(WORDP D) 
{
	if (!D->extensions) 
	{
		if (dictionaryLocked)
		{
			ReportBug("Attempt to set extension during chat\r\n");
			return;
		}

		D->extensions = String2Index(AllocateString(NULL,4, sizeof(MEANING),true));
	}
}


void SetWordValue(WORDP D, int x)
{
	MEANING* set = GetTemps(D);
	if (set) set[WORDVALUE] = x;
}

int GetWordValue(WORDP D)
{
	if (!D->temps) return 0;
	MEANING* set = GetTemps(D);
	return set[WORDVALUE];
}

// start and ends of space allocations
WORDP dictionaryBase = 0;			// base of allocated space that encompasses dictionary, string space, and meanings
WORDP dictionaryFree;				// current next dict space available going forward (not a valid entry)
char* stringBase;					// start of string space (runs backward)
char* stringFree;					// current free string ptr
char* stringEnd;

// return-to values for layers
WORDP dictionaryPreBuild[NUMBER_OF_LAYERS+1];
char* stringsPreBuild[NUMBER_OF_LAYERS+1];
// build0Facts 
	
// return-to values after build1 loaded, before user is loaded
WORDP dictionaryLocked;
FACT* factLocked = 0;
char* stringLocked;

// format of word looked up
uint64 verbFormat;
uint64 nounFormat;
uint64 adjectiveFormat;
uint64 adverbFormat;

// dictionary ptrs for these words
WORDP Dplacenumber;
WORDP Dpropername;
MEANING Mphrase;
MEANING MabsolutePhrase;
MEANING MtimePhrase;
WORDP Dclause;
WORDP Dverbal;
WORDP Dmalename,Dfemalename,Dhumanname;
WORDP Dtime;
WORDP Dunknown;
WORDP Dchild,Dadult;
WORDP Dtopic;
MEANING Mchatoutput;
MEANING Mburst;
MEANING Mpending;
MEANING Mkeywordtopics;
MEANING Mconceptlist;
MEANING Mmoney,Musd,Meur,Mgbp,Myen,Mcny,Minr;
MEANING Mintersect;
MEANING MgambitTopics;
MEANING MadjectiveNoun;
MEANING Mnumber;
WORDP Dpronoun;
WORDP Dadjective;
WORDP Dauxverb;
WORDP DunknownWord;

static char* predefinedSets[] = //  some internally mapped concepts not including emotions from LIVEDATA/interjections
{
	 "~repeatme","~repeatinput1","~repeatinput2","~repeatinput3","~repeatinput4","~repeatinput5","~repeatinput6","~uppercase","~utf8","~sentenceend",
	"~pos","~sys","~grammar_role","~daynumber","~yearnumber","~dateinfo","~email_url","~fahrenheit","~celsius","~kelvin",
	"~KINDERGARTEN","~GRADE1_2","~GRADE3_4","~GRADE5_6",

    NULL
};

void DictionaryRelease(WORDP until,char* stringUsed) 
{
	WORDP D;
	while (propertyRedefines) // must release these
	{
		unsigned int * at = (unsigned int *) Index2String(propertyRedefines); // 1st is index of next, 2nd is index of dict, 3/4 is properties to replace
		if (!at) // bug - its been killed
		{
			propertyRedefines = 0;
			break;
		}
		if ((char*)at >= stringUsed) break;	// not part of this freeing
		propertyRedefines = *at;
		D = Index2Word(at[1]);
		D->properties = *((uint64*) (at+2));
	}
	while (flagsRedefines) // must release these
	{
		unsigned int * at = (unsigned int*) Index2String(flagsRedefines); // 1st is index of next, 2nd is index of dict, 3/4 is properties to replace
		if (!at) // bug - its been killed
		{
			flagsRedefines = 0;
			break;
		}
		if ((char*)at >= stringUsed) break;	// not part of this freeing
		flagsRedefines = *at;
		D = Index2Word(at[1]);
		D->systemFlags = *((uint64*) (at+2));
	}
	while (dictionaryFree > until) DeleteDictionaryEntry(--dictionaryFree); //   remove entry from buckets
    stringFree = stringUsed; 
}

char* UseDictionaryFile(char* name)
{
	static char junk[100];
	if (*mini) sprintf(junk,"DICT/%s",mini);
	else if (!*language) sprintf(junk,"DICT");
	else if (!name) sprintf(junk,"DICT/%s",language);
	else sprintf(junk,"DICT/%s",language);
	if (name && *name) 
	{
		strcat(junk,"/");
		strcat(junk,name);
	}
	else MakeDirectory(junk); // if it doesnt exist
	return junk;
}

MEANING FindChild(MEANING who,int n)
{ // GIVEN SYNSET
    FACT* F = GetObjectNondeadHead(who);
	unsigned int index = Meaning2Index(who);
    while (F)
    {
        FACT* at = F;
        F = GetObjectNondeadNext(F);
        if (at->verb != Mis) continue;
		if (index && at->object  != who) continue;	// not us
        if (--n == 0)   return at->subject;
    }
    return 0;
} 

unsigned char BitCount(uint64 n)  
{  
	unsigned char count = 0;  
    while (n)  
	{  
       count++;  
       n &= (n - 1);  
    }  
    return count;  
 } 

WORDP GetSubstitute(WORDP D)
{
	return (D && D->internalBits & HAS_SUBSTITUTE)  ?  D->w.substitutes : 0;
}

void BuildShortDictionaryBase();

static void EraseFile(char* file)
{
	FILE* out = FopenUTF8Write(UseDictionaryFile(file));
	if (out) fclose(out);
}

static void ClearDictionaryFiles()
{
	char buffer[MAX_BUFFER_SIZE];
	EraseFile("other.txt"); //   create but empty file
    unsigned int i;
	for (i = 'a'; i <= 'z'; ++i)
	{
		sprintf(buffer,"%c.txt",i);
		EraseFile(buffer); //   create but empty file
	}
	for (i = '0'; i <= '9'; ++i)
	{
		sprintf(buffer,"%c.txt",i);
		EraseFile(buffer); //   create but empty file
	}
}

void BuildDictionary(char* label)
{
	buildDictionary = true;
	int miniDict = 0;
	char word[MAX_WORD_SIZE];
	char lang[MAX_WORD_SIZE];
	mini = "ENGLISH";
	char* ptr = ReadCompiledWord(label,word);
	bool makeBaseList = false;
	if (!stricmp(word,"wordnet")) // the FULL wordnet dictionary w/o synset removal
	{
		miniDict = -1;
		ReadCompiledWord(ptr,word);
		mini = "WORDNET";
	}
	else if (!stricmp(word,"basic"))
	{
		miniDict = 1;
		makeBaseList = true;
		fclose(FopenUTF8Write("RAWDICT/basicwordlist.txt"));
		maxHashBuckets = 10000;
		setMaxHashBuckets = true;
		mini = "BASIC";
	}
	else if (!stricmp(word,"layer0") || !stricmp(word,"layer1")) // a mini dictionary
	{
		miniDict = !stricmp(word,"layer0") ? 2 : 3;
		mini = (miniDict == 2) ? (char*)"LAYER0" : (char*)"LAYER1";
		maxHashBuckets = 10000;
		setMaxHashBuckets = true;
	}
	strcpy(lang,mini);
	// insure language subdirectory exists
	MakeUpperCopy(language,lang); // localized version of dict. otherwise its of the current language
	UseDictionaryFile(NULL); 

	InitFacts(); 
	InitDictionary();
#ifndef DISCARDDICTIONARYBUILD
	LoadRawDictionary(miniDict); 
#endif
	if (miniDict) StoreWord("minidict"); // mark it as a mini dictionary

	// dictionary has been built now
	printf("Dumping dictionary\r\n");
	ClearDictionaryFiles();
	WalkDictionary(WriteDictionary);
#ifndef DISCARDDICTIONARYBUILD
	if (makeBaseList) BuildShortDictionaryBase(); // write out the basic dictionary
#endif

 	remove(UseDictionaryFile("dict.bin")); // invalidate cache of dictionary, forcing binary rebuild later
    WriteFacts(FopenUTF8Write(UseDictionaryFile("facts.txt")),factBase); 
	sprintf(logFilename,"%s/build_log.txt",users); // all data logged here by default
	FILE* out = FopenUTF8Write(logFilename);
	if (out) fclose(out);
	printf("dictionary dump complete %d\r\n",miniDict);

    echo = true;
	buildDictionary = false;
	CreateSystem();
}

void InitDictionary()
{
	// read what the default dictionary wants as hash if parameter didnt set it
	if (!setMaxHashBuckets)
	{
		FILE* in = FopenStaticReadOnly(UseDictionaryFile("dict.bin"));  // DICT
		if (in) 
		{
			maxHashBuckets = Read32(in); // bucket size used by dictionary file
			fclose(in);
		}
	}

	dictionaryLocked = 0;
	userTopicStoreSize = userCacheCount * userCacheSize; //  minimum cache spot
	userTopicStoreSize /= 64;
	userTopicStoreSize = (userTopicStoreSize * 64) + 64;
	
	//   dictionary and meanings and strings share space, running from opposite ends of a common pool
	size_t size = (size_t)(sizeof(WORDENTRY) * maxDictEntries);
#ifdef WIN32
	size += maxStringBytes;
#endif
	size /= sizeof(WORDENTRY);
	size = (size * sizeof(WORDENTRY)) + sizeof(WORDENTRY);
	size /= 64;
	size = (size * 64) + 64; // 64 bit align both ends
	// on FUTURE startups (not 1st) the userCacheCount has been preserved while the rest of the system is reloaded
	if ( dictionaryBase == 0) // 1st startup allocation -- not needed on a reload
	{
		userTableSize = userCacheCount * 3 * sizeof(unsigned int);
		userTableSize /= 64;
		userTableSize = (userTableSize * 64) + 64; // 64 bit align both ends
		InitCache((unsigned int)size);
		dictionaryBase = (WORDP) (cacheBase + userTopicStoreSize + userTableSize);
	}
	memset(dictionaryBase,0,size);
	dictionaryFree =  dictionaryBase + maxHashBuckets + HASH_EXTRA ;		//   prededicate hash space within the dictionary itself
#ifndef SEPARATE_STRING_SPACE 	
	stringBase = stringFree = ((char*)dictionaryBase) + size;				//   the end of the allocated space
#else
	size = maxStringBytes / 64;
	size = (size * 64) + 64; // 64 bit align both ends
	stringEnd = ((char*) malloc(size));	// point to end
	if (!stringEnd)
	{
		printf("Out of  memory space for text space %d\r\n",(int)size);
		ReportBug("Cannot allocate memory space for text %d\r\n",(int)size)
		myexit("out of memory space for text space to allocate");
	}
	stringFree = stringBase = stringEnd + size; // allocate backwards
#endif
	//   The bucket list is threaded thru WORDP nodes, and consists of indexes, not addresses.

	dictionaryPreBuild[0] = dictionaryPreBuild[1] = dictionaryPreBuild[2] = 0;	// in initial dictionary
	factsPreBuild[0] = factsPreBuild[1] = factsPreBuild[2] = factFree;	// last fact in dictionary 
	propertyRedefines = flagsRedefines = 0;
}

char* reuseAllocation(char* old, char* word)
{
	return reuseAllocation(old,word, strlen(word));
}

char* reuseAllocation(char* old, char* word,int size)
{
	size_t len = 0;
	if (old && !planning  && !compiling && !loading) 
	{
		char* at = old - ALLOCATESTRING_SIZE_PREFIX;	
		char* prior = old - ALLOCATESTRING_SIZE_PREFIX - ALLOCATESTRING_SIZE_SAFEMARKER;
		if (word) {;} // BLOCK REUSE DATA FOR NOW... DEBUG FURTHER
		else if (old && (*prior != ALLOCATESTRING_MARKER || prior[1] != ALLOCATESTRING_MARKER)) // lacks the marker block- not allocated correctly?
		{
			ReportBug("reuseallocation failed1 on input %s",mainInputBuffer);
		}
		else if (at[0] == ALLOCATESTRING_MARKER) // lacks a mark of length
		{
			ReportBug("reuseallocation failed2 on input %s",mainInputBuffer);
		}
		else
		{
			if (ALLOCATESTRING_SIZE_PREFIX == 3) len +=  ((unsigned char) *(at++)) << 16;
			len +=  (unsigned char)*(at++) << 8;
			len +=  (unsigned char)*(at++);
		}
	}
	if (size < (int) len)
	{
		strncpy(old,word,size); // reuse the space 
		old[size] = 0;
	}
	else old = AllocateString(word,size,1); 
	return old;
}

char* expandAllocation(char* old, char* word,int size)
{
	size_t len = 0;
	if (old && !planning  && !compiling && !loading) 
	{
		char* at = old - ALLOCATESTRING_SIZE_PREFIX;	
		char* prior = old - ALLOCATESTRING_SIZE_PREFIX - ALLOCATESTRING_SIZE_SAFEMARKER;
		if (word) {;} // BLOCK REUSE DATA FOR NOW... DEBUG FURTHER
		else if (old && (*prior != ALLOCATESTRING_MARKER || prior[1] != ALLOCATESTRING_MARKER)) // lacks the marker block- not allocated correctly?
		{
			ReportBug("reuseallocation failed1 on input %s",mainInputBuffer);
		}
		else if (at[0] == ALLOCATESTRING_MARKER) // lacks a mark of length
		{
			ReportBug("reuseallocation failed2 on input %s",mainInputBuffer);
		}
		else
		{
			if (ALLOCATESTRING_SIZE_PREFIX == 3) len +=  ((unsigned char) *(at++)) << 16;
			len +=  (unsigned char)*(at++) << 8;
			len +=  (unsigned char)*(at++);
		}
	}
	if (size >= (int)len)
	{
		word = AllocateString(NULL,size,1,false);
		*word = 0;
		if (old) strcpy(word,old);
		old = word; // otherwise leave buffer with original content alone
	}
	return old;
}

char* AllocateString(char* word,size_t len,int bytes,bool clear) // BYTES means size of unit
{ //   string allocation moves BACKWARDS from end of dictionary space (as do meanings)
/* Allocations during setup as :
2 when setting up cs using current dictionary and livedata for extensions (plurals, comparatives, tenses, canonicals) 
3 preserving flags or properties when removing them or adding them while  the dictionary is unlocked - only during builds 
4 reading strings during dictionary setup
5 assigning meanings or glosses or posconditionsfor the dictionary
6 reading in postag information
---
Allocations happen during volley processing as
1 adding a new dictionary word - all the time on user input
2. saving plan backtrack data
3 altering concepts[] and topics[] lists as a result of a mark operation or normal behavior
4. temps information
5 spellcheck adjusted word in sentence list
6 tokenizing words and quoted stuff adjustments
7. assignment onto user variables
8. JSON reading
*/
	len *= bytes; // this many units of this size
	if (len == 0) len = strlen(word);
	if (word) ++len;	// null terminate string
	size_t allocationSize = len;
	if (bytes == 1 && dictionaryLocked && !compiling && !loading) 
	{
		allocationSize += ALLOCATESTRING_SIZE_PREFIX + ALLOCATESTRING_SIZE_SAFEMARKER; 
		// reserve space at front for allocation sizing not in dict items though (variables not in plannning mode can reuse space if prior is big enough)
		// initial 2 test area
	}

	//   always allocate in word units
	unsigned int allocate = ((allocationSize + 3) / 4) * 4;
	stringFree -= allocate;
 	if (bytes > 4) // force 64bit alignment alignment
	{
		uint64 base = (uint64) stringFree;
		base &= 0xFFFFFFFFFFFFFFC0ULL;
		stringFree = (char*) base;
	}
 	else if (bytes == 4) // force 32bit alignment alignment
	{
		uint64 base = (uint64) stringFree;
		base &= 0xFFFFFFFFFFFFFFF0ULL;
		stringFree = (char*) base;
	}
 	else if (bytes == 2) // force 16bit alignment alignment
	{
		uint64 base = (uint64) stringFree;
		base &= 0xFFFFFFFFFFFFFFF8ULL;
		stringFree = (char*) base;
	}
	else if (bytes != 1) 
		ReportBug("Allocation of bytes is not std unit %d", bytes);

	// create marker
	if (bytes == 1  && dictionaryLocked && !compiling && !loading) 
	{
		stringFree[0] = ALLOCATESTRING_MARKER; // we put ff ff  just before the sizing data
		stringFree[1] = ALLOCATESTRING_MARKER;
	}

	char* newword =  stringFree;
	if (bytes == 1 && dictionaryLocked && !compiling && !loading) // store size of allocation to enable potential reuse by $var assign and by wordStarts tokenize
	{
		newword += ALLOCATESTRING_SIZE_SAFEMARKER;
		allocationSize -= ALLOCATESTRING_SIZE_PREFIX + ALLOCATESTRING_SIZE_SAFEMARKER; // includes the end of string marker
		if (ALLOCATESTRING_SIZE_PREFIX == 3)		*newword++ = (unsigned char)(allocationSize >> 16); 
		*newword++ = (unsigned char)(allocationSize >> 8) && 0x000000ff;  
		*newword++ = (unsigned char) (allocationSize & 0x000000ff);
	}
	
	int nominalLeft = maxStringBytes - (stringBase - stringFree);

#ifndef SEPARATE_STRING_SPACE 
    if (stringFree <= (char*) dictionaryFree) 
#else
	 if (stringFree < (char*) stringEnd) 
#endif
    {
		ReportBug("Out of transient string space\r\n")
		myexit("no more transient string space");
    }
    if (word) 
	{
		memcpy(newword,word,--len);
		newword[len] = 0;
	}
	else if (clear) memset(newword,0,len);
    return newword;
}

void AddInternalFlag(WORDP D, unsigned int flag)
{
	if (flag && flag !=  D->internalBits) // prove there is a change - dont use & because if some bits are set is not enough
	{
		if (D < dictionaryLocked)
			return;
		D->internalBits |= (unsigned int) flag;
	}
}

void RemoveInternalFlag(WORDP D,unsigned int flag)
{
	D->internalBits &= -1 ^ flag;
}

static void PreserveFlags(WORDP D)
{			
	unsigned int* at = (unsigned int*) AllocateString (NULL,2, sizeof(uint64),false); // PreserveFlags
	*at = flagsRedefines;
	at[1] = Word2Index(D);
	flagsRedefines = String2Index((char*)at);
	*((uint64*)(at+2)) = D->systemFlags;
}

void AddSystemFlag(WORDP D, uint64 flag)
{
	if (flag & NOCONCEPTLIST && *D->word != '~') flag ^= NOCONCEPTLIST; // not allowed to mark anything but concepts with this
	if (flag && flag != D->systemFlags) // prove there is a change - dont use & because if some bits are set is not enough
	{
		if (D < dictionaryLocked) PreserveFlags(D);
		D->systemFlags |= flag;
	}
}

void AddParseBits(WORDP D, unsigned int flag)
{
	if (flag && flag != D->parseBits) // prove there is a change - dont use & because if some bits are set is not enough
	{
		if (D < dictionaryLocked)
			return;
		D->parseBits |= (unsigned int) flag;
	}
}

void RemoveSystemFlag(WORDP D, uint64 flags)
{
	if (D->systemFlags & flags)
	{
		if (D < dictionaryLocked) PreserveFlags(D);
		D->systemFlags &= -1LL ^ flags;
	}
}

static void PreserveProperty(WORDP D)
{
	unsigned int* at = (unsigned int*) AllocateString (NULL,2, sizeof(uint64),false); //  PreserveProperty
	*at = propertyRedefines;
	at[1] = Word2Index(D);
	propertyRedefines = String2Index((char*)at);
	*((uint64*)(at+2)) = D->properties;
}

void AddProperty(WORDP D, uint64 flag)
{
	if (flag && flag != (D->properties & flag))
	{
		if (D < dictionaryLocked) PreserveProperty(D);
		if (!(D->properties & PART_OF_SPEECH) && flag & PART_OF_SPEECH && *D->word != '~'  && *D->word != '^' && *D->word != '$')  // not topic,concept,function
		{
			//   internal use, do not allow idioms on words from #defines or user variables or  sets.. but allow substitutes to do it?
			unsigned int n = BurstWord(D->word);
			if (n != 1) 
			{
				WORDP E = StoreWord(JoinWords(1));		// create the 1-word header
				if (n > GETMULTIWORDHEADER(E)) SETMULTIWORDHEADER(E,n);	//   mark it can go this far for an idiom
			}
		}
		D->properties |= flag;
	}
}

void RemoveProperty(WORDP D, uint64 flags)
{
	if (D->properties & flags)
	{
		if (D < dictionaryLocked)  PreserveProperty(D);
		D->properties &= -1LL ^ flags;
	}
}

char* GetCanonical(WORDP D)
{
	if (!D->extensions) return NULL;
	unsigned int x = AccessCanonical(D);
	if (!x) return NULL;
	WORDP X = Meaning2Word(x);
	return  X->word;
}

WORDP FindWord(const char* word, int len,uint64 caseAllowed) 
{
	if (word == NULL || *word == 0) return NULL;
	if (len >= PRIMARY_CASE_ALLOWED) // in case argument omitted accidently
	{
		caseAllowed = len;
		len = 0;
	}
	if (len == 0) len = strlen(word);
	bool hasUpperCharacters;
	bool hasUTF8Characters;
	uint64 fullhash = Hashit((unsigned char*) word,len,hasUpperCharacters,hasUTF8Characters); //   sets hasUpperCharacters and hasUTF8Characters 
	unsigned int hash  = (fullhash % maxHashBuckets) + 1; // mod by the size of the table
	if (caseAllowed & LOWERCASE_LOOKUP){;}
	else if (*word == '%' || *word == '$' || *word == '~'  || *word == '^') 
	{
		if (caseAllowed == UPPERCASE_LOOKUP) return NULL; // not allowed to find
		caseAllowed = LOWERCASE_LOOKUP; // these are always lower case
	}
	else if (hasUpperCharacters || (caseAllowed & UPPERCASE_LOOKUP)) ++hash;

	// you can search on upper or lower specifically (not both) or primary or secondary or both

	//   normal or fixed case bucket
	WORDP D;
	if (caseAllowed & (PRIMARY_CASE_ALLOWED|LOWERCASE_LOOKUP|UPPERCASE_LOOKUP))
	{
		D = dictionaryBase + hash;
		while (D != dictionaryBase)
		{
			if (fullhash == D->hash && D->length == len)
			{
				if (!strnicmp(D->word,word,len)) return D;
			}
			D = dictionaryBase + GETNEXTNODE(D);
		}
	}

    //    alternate case bucket
	if (caseAllowed & SECONDARY_CASE_ALLOWED) 
	{
		D = dictionaryBase + hash + ((hasUpperCharacters) ? -1 : 1);
		while (D != dictionaryBase)
		{
			if (fullhash == D->hash && D->length == len)
			{
				if (!strnicmp(D->word,word,len)) return D;
			}
			D = dictionaryBase + GETNEXTNODE(D);
		}
	}

    return NULL;
}

static WORDP AllocateEntry()
{
	WORDP  D = dictionaryFree++;
#ifdef WIN32
	if (Word2Index(D) >= maxDictEntries || ((char*)D + sizeof(WORDENTRY)) >= stringFree)// we allow string space to use up dict space if it needs it
#else
	if (Word2Index(D) >= maxDictEntries)
#endif
	{
		ReportBug("used up all dict nodes\r\n")
		myexit("used up all dict nodes");
	}
    memset(D,0,sizeof(WORDENTRY));
	return D;
}

WORDP StoreWord(int val) // create a number word
{
	char value[MAX_WORD_SIZE];
	sprintf(value,"%d",val);
	return StoreWord(value);
}

WORDP StoreWord(char* word, uint64 properties, uint64 flags)
{
	WORDP D = StoreWord(word,properties);
	AddSystemFlag(D,flags);
	return D;
}

WORDP StoreWord(char* word, uint64 properties)
{
	if (!*word) // servers dont want long lists of bugs from strange inputs //   we require something 
	{
		if (!server) ReportBug("entering null word to dictionary in sentence")
		return StoreWord("badword"); //   we require something
	}
	unsigned int n = 0;
	bool lowercase = false;
	//   make all words normalized with no blanks in them.
	if (*word == '"' || *word == '_' || *word == '`') {;} // dont change any quoted things or things beginning with _ (we use them in facts for a "missing" value) or user var names
	else if (*word == '%' || *word == '$' || *word == '~'  || *word == '^') lowercase = true; // these are always lower case
	else if (!(properties & (AS_IS|PUNCTUATION_BITS))) 
	{
		n = BurstWord(word,0);
		word = JoinWords(n); //   when reading in the dictionary, BurstWord depends on it already being in, so just use the literal text here
	}
	properties &= -1 ^ AS_IS;
	size_t len = strlen(word);
	bool hasUpperCharacters;
	bool hasUTF8Characters;
	uint64 fullhash = Hashit((unsigned char*) word,len,hasUpperCharacters,hasUTF8Characters); //   sets hasUpperCharacters and hasUTF8Characters 
	unsigned int hash = (fullhash % maxHashBuckets) + 1; //   mod the size of the table (saving 0 to mean no pointer and reserving an end upper case bucket)
	if (hasUpperCharacters)
	{
		if (lowercase) hasUpperCharacters = false;
		else if (!lowercase)  ++hash;
	}
	WORDP base = dictionaryBase + hash;

	//   locate spot existing entry goes
    WORDP D = base; 
	while (D != dictionaryBase)
    {
 		if (fullhash == D->hash && D->length == len)
		{
			if (!strnicmp(D->word,word,len))
			{
				AddProperty(D,properties);
				return D;
			}
		}
		D = dictionaryBase + GETNEXTNODE(D);
    }  

    //   not found, add entry 
	char* wordx = AllocateString(word,len); // storeword
    if (!wordx) return StoreWord("x.x",properties|AS_IS); // fake it
	if (base->word == 0 && !dictionaryPreBuild[0]) D = base; // add into hash zone initial dictionary entries (nothing allocated here yet) if and only if loading the base system
	else  
	{
		D = AllocateEntry();
		D->nextNode = GETNEXTNODE(base);
		base->nextNode &= MULTIHEADERBITS;
		base->nextNode |= D - dictionaryBase;
	}
	// fill in data on word
    D->word = wordx; 
	if (hasUTF8Characters) AddInternalFlag(D,UTF8);
	if (hasUpperCharacters) AddInternalFlag(D,UPPERCASE_HASH);
	D->hash = fullhash;
	D->length = (unsigned short) len;
    AddProperty(D,properties);
    return D;
}

//   insert entry into a circular list, initializing if need be
void AddCircularEntry(WORDP base, unsigned int field,WORDP entry)
{
	if (!base) return;
	PrepareConjugates(base);
	PrepareConjugates(entry);

	//   verify item to be added not already in circular list of this kind - dont add if it is
	char* con = Index2String(entry->extensions);
	MEANING* mean = (MEANING*) con;
	if (!mean[field]) 
	{
		char* conb = Index2String(base->extensions);
		MEANING* meanb = (MEANING*) conb;
		if (!meanb[field]) meanb[field] = MakeMeaning(base); // if set base not initialized, make it loop to self
		mean[field] = meanb[field];
		meanb[field] = MakeMeaning(entry);
	}
	else printf("%s already on circular list of %s\r\n",entry->word, base->word);
}

void WalkDictionary(DICTIONARY_FUNCTION func,uint64 data)
{
    for (WORDP D = dictionaryBase+1; D < dictionaryFree; ++D) 
	{
		if (D->word) (func)(D,data); 
	}
}

void DeleteDictionaryEntry(WORDP D)
{
	// Newly added dictionary entries will be after some marker (provided we are not loading the base dictionary).
	unsigned int hash = (D->hash % maxHashBuckets) + 1; 
	if (D->internalBits & UPPERCASE_HASH) ++hash;
	WORDP base = dictionaryBase + hash;  // the bucket at the base
	if (D == base) base->word = 0; // the base is free// is the bucket itself, was assigned into it first and all the rest come after -- should never happen because only basic words go as base, and are never released
	else
	{
		WORDP X = dictionaryBase + GETNEXTNODE(base);
		if (X != D) // this SHOULD have been pointing to here
		{
			ReportBug("Bad dictionary delete %s\r\n",D->word);
			return;
		}
	}

	base->nextNode &= MULTIHEADERBITS;
	base->nextNode |= GETNEXTNODE(D); //   move entry over to next in list

	D->nextNode = 0;
	D->hash = 0;
}

void ShowStats(bool reset)
{
	static unsigned int maxRules = 0;
	static unsigned int maxDict = 0;
	static unsigned int maxText = 0;
	static unsigned int maxFact = 0;
	if (reset) maxRules = maxDict = maxText = maxFact = ruleCount = 0;
	if (stats && !reset) 
	{
		unsigned int dictUsed = dictionaryFree - dictionaryLocked;
		if (dictUsed > maxDict) maxDict = dictUsed;
		unsigned int factUsed = factFree - factLocked;
		if (factUsed > maxFact) maxFact = factUsed;
		unsigned int textUsed = stringLocked - stringFree;
		if (textUsed > maxText) maxText = textUsed;
		if (ruleCount > maxRules) maxRules = ruleCount;

		unsigned int diff = (unsigned int) (ElapsedMilliseconds() - volleyStartTime);
		unsigned int mspl = (inputSentenceCount) ? (diff/inputSentenceCount) : 0;
		float fract = (float)(diff/1000.0); // part of seccond
		float time = (float)(tokenCount/fract);
		Log(ECHOSTDUSERLOG,"\r\nRead: %d sentences (%d tokens) in %d ms = %d ms/l or %f token/s\r\n",inputSentenceCount,tokenCount, diff,mspl,time);

		Log(ECHOSTDUSERLOG,"used: rules=%d dict=%d fact=%d text=%d mark=%d\r\n",ruleCount,dictUsed,factUsed,textUsed,xrefCount);
		Log(ECHOSTDUSERLOG,"      maxrules=%d  maxdict=%d maxfact=%d  maxtext=%d\r\n",maxRules,maxDict,maxFact,maxText);
		ruleCount = 0;
		xrefCount = 0;
	}		

}

#ifndef DISCARDSCRIPTCOMPILER
static void WriteDictDetailsBeforeLayer(int layer)
{
	char word[MAX_WORD_SIZE];
	sprintf(word,"TMP/prebuild%d.bin",layer);
	FILE* out = FopenBinaryWrite(word); // binary file, no BOM
	if (out)
	{
		char x = 0;
		for (WORDP D = dictionaryBase+1; D < dictionaryPreBuild[layer]; ++D) 
		{
			unsigned int offset = D - dictionaryBase;
			fwrite(&offset,1,4,out);
			fwrite(&D->properties,1,8,out); 
			fwrite(&D->systemFlags,1,8,out); 
			fwrite(&D->internalBits,1,4,out); 
			unsigned char head = GETMULTIWORDHEADER(D);
			fwrite(&head,1,1,out);
			fwrite(&x,1,1,out);
		}
		fclose(out);
	}
}

static void ReadDictDetailsBeforeLayer(int layer)
{
	char word[MAX_WORD_SIZE];
	sprintf(word,"TMP/prebuild%d.bin",layer);
	FILE* in = FopenReadWritten(word); // binary file, no BOM
	if (in)
	{
		unsigned int xoffset;
		for (WORDP D = dictionaryBase+1; D < dictionaryPreBuild[layer]; ++D) 
		{
			fread(&xoffset,1,4,in); 
			unsigned int offset = D - dictionaryBase;
			if (xoffset != offset) ReportBug("Bad return to build\r\n");
			fread(&D->properties,1,8,in);
			fread(&D->systemFlags,1,8,in);
			fread(&D->internalBits,1,4,in);
			unsigned char c;
			fread(&c,1,1,in);
			SETMULTIWORDHEADER(D,c);
			fread(&c,1,1,in);
			if (c != 0) myexit("bad return to build");
		}
		fclose(in);
	}
}
#endif

void WordnetLockDictionary() // dictionary and facts before build0 layer 
{
    dictionaryPreBuild[0] = dictionaryPreBuild[1] = dictionaryPreBuild[2] = dictionaryFree;		// end of wordnet data
	stringsPreBuild[0] = stringsPreBuild[1] = stringsPreBuild[2] = stringFree;		// mark point for mark release
	factsPreBuild[0] = factsPreBuild[1] = factsPreBuild[2] = factFree;

#ifndef DISCARDSCRIPTCOMPILER
	// memorize dictionary values for backup to pre build locations :build0 operations (reseting word to dictionary state)
	WriteDictDetailsBeforeLayer(0);
#endif
}

void ReturnDictionaryToWordNet() // drop all memory allocated after the wordnet freeze
{
	ClearTemps();
	while (factFree > factsPreBuild[0]) FreeFact(factFree--); // restore to end of dictionary load
	DictionaryRelease(dictionaryPreBuild[0],stringsPreBuild[0]);
#ifndef DISCARDSCRIPTCOMPILER
	ReadDictDetailsBeforeLayer(0);
#endif
	dictionaryLocked = 0;
	numberOfTopics = 0;
	// all layer data
	factsPreBuild[2] = factsPreBuild[1] = factsPreBuild[0];
	dictionaryPreBuild[2] = dictionaryPreBuild[1] = dictionaryPreBuild[0];
	stringsPreBuild[2] = stringsPreBuild[1] = stringsPreBuild[0];
	numberOfTopicsInLayer[0] = numberOfTopicsInLayer[1] = numberOfTopicsInLayer[2] = 0;
	topicBlockPtrs[0] = topicBlockPtrs[1] = topicBlockPtrs[2] = NULL;
}

void LockLevel()
{
	dictionaryLocked = dictionaryFree;		
	stringLocked = stringFree;		
	factLocked = factFree; 
}

void UnlockLevel()
{
	dictionaryLocked = 0;		
	stringLocked = 0;		
	factLocked = 0; 
}

void LockLayer(int layer)
{
	// stores the results of the layer as the starting point of the next layers (hence size of arrays are +1)
	for (int i = layer+1; i < NUMBER_OF_LAYERS; ++i)
	{
		numberOfTopicsInLayer[i] = numberOfTopicsInLayer[layer];
		dictionaryPreBuild[i] = dictionaryFree;		
		stringsPreBuild[i] = stringFree;	
		factsPreBuild[i] = factFree; 
		topicBlockPtrs[i] = NULL;
		buildStamp[i][0] = 0;
	}
	
	if (layer < 2) // permanent layers
	{
	#ifndef DISCARDSCRIPTCOMPILER
		WriteDictDetailsBeforeLayer(layer+1);
	#endif

		// lock dictionary system  at layer 2 or earlier
		LockLevel();
	}
}

void ReturnToLayer(int layer, bool unlocked) 
{
	if (layer == 1)
	{
		ClearUserVariables();
		ClearTemps();
	}
	while (factFree > factsPreBuild[layer+1]) FreeFact(factFree--); //   restore back to facts alone
	DictionaryRelease(dictionaryPreBuild[layer+1],stringsPreBuild[layer+1]);

#ifndef DISCARDSCRIPTCOMPILER
	if (!server) ReadDictDetailsBeforeLayer(layer+1);// on server we assume scripts will not damage level0 or earlier data of dictionary but user doing :trace might
#endif

	// canonical map in layer 1 is now garbage- 
	if (unlocked)
	{
		dictionaryLocked = NULL;
		stringLocked = NULL;
		factLocked = NULL; // unlock
	}
	numberOfTopics = numberOfTopicsInLayer[layer];
	for (int i = layer+1; i < NUMBER_OF_LAYERS; ++i)
	{
		numberOfTopicsInLayer[i] = numberOfTopicsInLayer[layer];
		topicBlockPtrs[i] = NULL;
		factsPreBuild[i] = factsPreBuild[layer+1]; // start of next layer is set for all
		dictionaryPreBuild[i] = dictionaryPreBuild[layer+1];  // start of next layer is set for all
		stringsPreBuild[i] = stringsPreBuild[layer+1];  // start of next layer is set for all
		buildStamp[i][0] = 0;
	}
}

void CloseDictionary()
{
	CloseTextUtilities();
	dictionaryBase = NULL;
	CloseCache(); // actual memory space of the dictionary
}

static void Write8(unsigned int val, FILE* out)
{
	unsigned char x[1];
	x[0] = val & 0x000000ff;
	if (out) fwrite(x,1,1,out);
	else *writePtr++ = *x;
}

static void Write16(unsigned int val, FILE* out)
{
	unsigned char x[2];
	x[0] = val & 0x000000ff;
	x[1] = (val >> 8) & 0x000000ff;
	if (out) fwrite(x,1,2,out);
	else 
	{
		memcpy(writePtr,(unsigned char*)x,2);
		writePtr += 2;
	}
}

void Write24(unsigned int val, FILE* out)
{
	unsigned char x[3];
	x[0] = val & 0x000000ff;
	x[1] = (val >> 8) & 0x000000ff;
	x[2] = (val >> 16) & 0x000000ff;
	if (out) fwrite(x,1,3,out);
	else 
	{
		memcpy(writePtr,(unsigned char*)x,3);
		writePtr += 3;
	}
}

void Write32(unsigned int val, FILE* out)
{
	unsigned char x[4];
	x[0] = val & 0x000000ff;
	x[1] = (val >> 8) & 0x000000ff;
	x[2] = (val >> 16) & 0x000000ff;
	x[3] = (val >> 24) & 0x000000ff;
	if (out) fwrite(x,1,4,out);
	else 
	{
		memcpy(writePtr,(unsigned char*)x,4);
		writePtr += 4;
	}
}

void Write64(uint64 val, FILE* out)
{
	unsigned char x[8];
	x[0] = val & 0x000000ff;
	x[1] = (val >> 8) & 0x000000ff;
	x[2] = (val >> 16) & 0x000000ff;
	x[3] = (val >> 24) & 0x000000ff;
	x[4] = (val >> 32) & 0x000000ff;
	x[5] = (val >> 40) & 0x000000ff;
	x[6] = (val >> 48) & 0x000000ff;
	x[7] = (val >> 56) & 0x000000ff;
	if (out) fwrite(x,1,8,out);
	else 
	{
		memcpy(writePtr,(unsigned char*)x,8);
		writePtr += 8;
	}
}

void WriteDWord(WORDP ptr, FILE* out)
{
	unsigned int val = (ptr) ? Word2Index(ptr) : 0;
	unsigned char x[3];
	x[0] = val & 0x000000ff;
	x[1] = (val >> 8) & 0x000000ff;
	x[2] = (val >> 16) & 0x000000ff;
	if (out) fwrite(x,1,3,out);
	else 
	{
		memcpy(writePtr,(unsigned char*)x,3);
		writePtr += 3;
	}
}

static void WriteString(char* str, FILE* out)
{
	if (!str || !*str) Write16(0,out);
	else
	{
		size_t len = strlen(str);
		Write16(len,out);
		if (out) fwrite(str,1,len+1,out);
		else
		{
			memcpy(writePtr,(unsigned char*)str,len+1);
			writePtr += len+1;
		}
	}
}

static void WriteBinaryEntry(WORDP D, FILE* out)
{
	unsigned char c;
	writePtr = (unsigned char*)(readBuffer+2); // reserve size space
	if (!D->word) // empty entry
	{
		c = 0;
		WriteString((char*)&c,0);
		unsigned int len = writePtr-(unsigned char*)readBuffer;
		*readBuffer = (unsigned char)(len >> 8);
		readBuffer[1] = (unsigned char)(len & 0x00ff);
		fwrite(readBuffer,1,len,out);
		return;
	}

	WriteString(D->word,0);
	unsigned int bits = 0;
	if (GETMULTIWORDHEADER(D)) bits |= 1 << 0;
	if (GetTense(D)) bits |= 1 << 1;
	if (GetPlural(D)) bits |= 1 << 2;
	if (GetComparison(D)) bits |= 1 << 3;
	if (GetMeaningCount(D)) bits |= 1 << 4;
	if (GetGlossCount(D)) bits |= 1 << 5;
	if (D->systemFlags || D->properties || D->parseBits) bits |= 1 << 6;
	if (D->internalBits) bits |= 1 << 7;
	Write8(bits,0);

	if (bits & ( 1 << 6))
	{
		Write64(D->properties,0);
		Write64(D->systemFlags,0);
		Write32(D->parseBits,0);
	}
	if (D->internalBits) Write32(D->internalBits,0);
	if (D->internalBits & DEFINES) Write32(D->inferMark,0); // store invert value for some things
	Write24(D->nextNode,0); 
	if (D->systemFlags & CONDITIONAL_IDIOM) WriteString(D->w.conditionalIdiom,0);

	if (GETMULTIWORDHEADER(D))
	{
		c = (unsigned char)GETMULTIWORDHEADER(D);
		Write8(c,0); //   limit 255 no problem
	}
	if (GetTense(D)) Write32(MakeMeaning(GetTense(D)),0);
	if (GetPlural(D)) Write32(MakeMeaning(GetPlural(D)),0);
	if (GetComparison(D)) Write32(MakeMeaning(GetComparison(D)),0);
	if (GetMeaningCount(D)) 
	{
		unsigned char c = (unsigned char)GetMeaningCount(D);
		Write8(c,0);  //   limit 255 no problem
		for (unsigned int i = 1; i <= GetMeaningCount(D); ++i) Write32(GetMeaning(D,i),0);
	}
	if (GetGlossCount(D)) 
	{
		unsigned char c = (unsigned char)GetGlossCount(D);
		Write8(c,0); //   limit 255 no problem
		for (unsigned int i = 1; i <= GetGlossCount(D); ++i) 
		{
			Write8(D->w.glosses[i] >> 24,0);
			WriteString(Index2String(D->w.glosses[i] & 0x00ffffff),0);
		}
	}
	Write8('0',0);
	unsigned int len = writePtr - (unsigned char*) readBuffer;
	*readBuffer = (unsigned char)(len >> 8);
	readBuffer[1] = (unsigned char)(len & 0x00ff);
	fwrite(readBuffer,1,len,out);
}

void WriteBinaryDictionary()
{
	FILE* out = FopenBinaryWrite(UseDictionaryFile("dict.bin")); // binary file, no BOM
	if (!out) return;
	Write32(maxHashBuckets,out); // bucket size used
	WORDP D = dictionaryBase;
	while (++D < dictionaryFree) WriteBinaryEntry(D,out);
	char x[2];
	x[0] = x[1] = 0;
	fwrite(x,1,2,out); //   end marker for synchronization
	// add datestamp
	strcpy(dictionaryTimeStamp, GetMyTime(time(0)));
	fwrite(dictionaryTimeStamp,1,20,out);
	fclose(out);
	printf("binary dictionary %ld written\r\n",(long int)(dictionaryFree - dictionaryBase));
}

static unsigned char Read8(FILE* in) 
{
	if (in)
	{
		unsigned char x[1];
		return (fread(x,1,1,in) != 1) ? 0 : (*x);
	}
	else return *writePtr++;
}

static unsigned short Read16(FILE* in) 
{
	if (in)
	{
		unsigned char x[2];
		return (fread(x,1,2,in) != 2) ? 0 : ((*x) | (x[1]<<8));
	}
	else 
	{
		unsigned int n = *writePtr++;
		return (unsigned short)(n | (*writePtr++ << 8));
	}
}

static unsigned int Read24(FILE* in)
{
	if (in)
	{
		unsigned char x[3];
		if (fread(x,1,3,in) != 3) return 0;
		return (*x) | ((x[1]<<8) | (x[2]<<16));
	}
	else
	{
		unsigned int n = *writePtr++;
		n |= (*writePtr++ << 8);
		return n | (*writePtr++ << 16);
	}
}
  
unsigned int Read32(FILE* in)
{
	if (in)
	{
		unsigned char x[4];
		if (fread(x,1,4,in) != 4) return 0;
		unsigned int x3 = x[3];
		x3 <<= 24;
		return (*x) | (x[1]<<8) | (x[2]<<16) | x3 ;
	}
	else
	{
		unsigned int n = *writePtr++;
		n |= (*writePtr++ << 8);
		n |= (*writePtr++ << 16);
		return n | (*writePtr++ << 24);
	}
}

uint64 Read64(FILE* in)
{
	if (in)
	{
		unsigned char x[8];
		if (fread(x,1,8,in) != 8) return 0;
		unsigned int x1,x2,x3,x4,x5,x6,x7,x8;
		x1 = x[0]; 
		x2 = x[1];
		x3 = x[2];
		x4 = x[3];
		x5 = x[4];
		x6 = x[5];
		x7 = x[6];
		x8 = x[7];
		uint64 a = x1 | (x2<<8) | (x3<<16) | (x4<<24);
		uint64 b = x5 | (x6<<8) | (x7<<16) | (x8<<24);
		b <<= 16;
		b <<= 16;
		a |= b;
		return a;
	}
	else
	{
		unsigned int n = *writePtr++;
		n |= (*writePtr++ << 8);
		n |= (*writePtr++ << 16);
		n |= (*writePtr++ << 24);

		unsigned int n1 = *writePtr++;
		n1 |= (*writePtr++ << 8);
		n1 |= (*writePtr++ << 16);
		n1 |= (*writePtr++ << 24);

		uint64 ans = n1;
		ans <<= 16;
		ans <<= 16;
		return n | ans ;
	}
}

WORDP ReadDWord(FILE* in)
{
	if (in)
	{
		unsigned char x[3];
		if (fread(x,1,3,in) != 3) return 0;
		return Index2Word((x[0]) + (x[1]<<8) + (x[2]<<16));
	}
	else
	{
		unsigned int n = *writePtr++;
		n |= (*writePtr++ << 8);
		n |= (*writePtr++ << 16);
		return Index2Word(n);
	}
}

static char* ReadString(FILE* in)
{
	unsigned int len = Read16(in);
	if (!len) return NULL;
	char* str;
	if (in)
	{
		char* buffer = AllocateBuffer();
		if (fread(buffer,1,len+1,in) != len+1) return NULL;
		str = AllocateString(buffer,len); // readstring
		FreeBuffer();
	}
	else 
	{
		str = AllocateString((char*)writePtr,len); // readstring
		writePtr += len + 1;
	}
	return str;
}

static WORDP ReadBinaryEntry(FILE* in)
{
	writePtr = (unsigned char*) readBuffer;
	unsigned int len = fread(writePtr,1,2,in);
	if (writePtr[0] == 0 && writePtr[1] == 0) return NULL;	//   normal ending in synch
	len = (writePtr[0] << 8 ) | writePtr[1];
	writePtr += 2;
	if (fread(writePtr,1,len-2,in) != len-2) myexit("bad binary dict entry"); // swallow entry

	unsigned int nameLen = *writePtr | (writePtr[1] << 8); // peek ahead
	WORDP D = AllocateEntry();
	char* name = ReadString(0);
	if (!name)  return D;
	D->word = name;
	D->length = (unsigned short)nameLen;
	echo = true;
	unsigned int bits = Read8(0);

    if (bits & ( 1 << 6)) 
	{
		D->properties = Read64(0);
		D->systemFlags = Read64(0);
		D->parseBits = Read32(0);
	}
	if (bits & ( 1 << 7)) D->internalBits = Read32(0);
	if (D->internalBits & DEFINES) D->inferMark =  Read32(0); // xref 
	bool hasUpperCharacters;
	bool hasUTF8Characters;
	D->hash = Hashit((unsigned char*)name,nameLen,hasUpperCharacters,hasUTF8Characters);
	D->nextNode = Read24(0); 
	if (D->systemFlags & CONDITIONAL_IDIOM)  
		D->w.conditionalIdiom = ReadString(0);

	if (bits & (1 << 0)) 
	{
		unsigned char c = Read8(0);
		SETMULTIWORDHEADER(D,c);
	}
	if (bits & (1 << 1)) SetTense(D,Read32(0));
	if (bits & (1 << 2)) SetPlural(D,Read32(0));
	if (bits & (1 << 3)) SetComparison(D,Read32(0));
	if (bits & (1 << 4)) 
	{
		unsigned char c = Read8(0);
		MEANING* meanings = (MEANING*) AllocateString(NULL,(c+1),sizeof(MEANING)); 
		memset(meanings,0,(c+1) * sizeof(MEANING)); 
		D->meanings =  String2Index((char*)meanings);
		GetMeaning(D,0) = c;
		for (unsigned int i = 1; i <= c; ++i)  
		{
			GetMeaning(D,i) = Read32(0);
			if (GetMeaning(D,i) == 0)
			{
				ReportBug("binary entry meaning is null %s",name)
				myexit("null meaning for binary dict entry");
			}
		}
	}
	if (bits & (1 << 5)) // glosses
	{
		unsigned char c = Read8(0);
		MEANING* glosses = (MEANING*) AllocateString(NULL,(c+1), sizeof(MEANING)); 
		memset(glosses,0,(c+1) * sizeof(MEANING)); 
		glosses[0] = c;
		D->w.glosses =  glosses;
		for (unsigned int i = 1; i <= c; ++i)  
		{
			unsigned int index = Read8(0);
			char* string = ReadString(0);
			D->w.glosses[i] = String2Index(string) | (index << 24);
		}
		AddInternalFlag(D,HAS_GLOSS);
	}
	if (Read8(0) != '0')
	{
		printf("Bad Binary Dictionary entry, rebuild the binary dictionary %s\r\n",name);
		myexit("bad binary entry rebuilding");
	}
	return D;
}

bool ReadBinaryDictionary() 
{
	FILE* in = FopenStaticReadOnly(UseDictionaryFile("dict.bin"));  // DICT
	if (!in) return false;
	unsigned int size = Read32(in); // bucket size used
	if (size != maxHashBuckets) // if size has changed, rewrite binary dictionary
	{
		ReportBug("Binary dictionary uses hash=%d but system is using %d -- rebuilding binary dictionary\r\n",size,maxHashBuckets)
		return false;
	}
	dictionaryFree = dictionaryBase + 1;
	while (ReadBinaryEntry(in));
	fread(dictionaryTimeStamp,1,20,in);
	fclose(in);
	return true;
}

void WriteDictionaryFlags(WORDP D, FILE* out)
{
	if (D->internalBits & DEFINES) return; // they dont need explaining, loaded before us
	uint64 properties = D->properties;
	uint64 bit = START_BIT;	
	while (properties)
	{
		if (properties & bit)
		{
			properties ^= bit;
			char* label = FindNameByValue(bit);
			if (label) fprintf(out,"%s ",label);
		}
		bit >>= 1;
	}

	properties = D->systemFlags;
	bit = START_BIT;
	bool posdefault = false;
	bool agedefault = false;
	while (properties)
	{
		if (properties & bit)
		{
			char* label = NULL;
			if (bit & ESSENTIAL_FLAGS) 
			{
				if (!posdefault)
				{
					if (D->systemFlags & NOUN) fprintf(out,"posdefault:NOUN ");
					if (D->systemFlags & VERB) fprintf(out,"posdefault:VERB "); 
					if (D->systemFlags & ADJECTIVE) fprintf(out,"posdefault:ADJECTIVE "); 
					if (D->systemFlags & ADVERB) fprintf(out,"posdefault:ADVERB "); 
					if (D->systemFlags & PREPOSITION) fprintf(out,"posdefault:PREPOSITION ");
					posdefault = true;
				}
			}
			else if (bit & AGE_LEARNED) 
			{
				if (!agedefault)
				{
					agedefault = true;
					uint64 age = D->systemFlags & AGE_LEARNED;
					if (age == KINDERGARTEN) fprintf(out,"KINDERGARTEN ");
					else if (age == GRADE1_2) fprintf(out,"GRADE1_2 ");
					else if (age == GRADE3_4) fprintf(out,"GRADE3_4 ");
					else if (age == GRADE5_6) fprintf(out,"GRADE5_6 ");
				}
			}
			else label = FindSystemNameByValue(bit);
			properties ^= bit;
			if (label) fprintf(out,"%s ",label);
		}
		bit >>= 1;
	}
	
	properties = D->parseBits;
	bit = START_BIT;	
	while (properties)
	{
		if (properties & bit)
		{
			properties ^= bit;
			char* label = FindParseNameByValue(bit);
			if (label) fprintf(out,"%s ",label);
		}
		bit >>= 1;
	}
}

char* GetGloss(WORDP D,unsigned int index)
{
	index = GetGlossIndex(D,index);
	return (!index) ? 0 : (char*) Index2String(D->w.glosses[index] & 0x00ffffff);
}

unsigned int GetGlossIndex(WORDP D,unsigned int index)
{
	unsigned int count = GetGlossCount(D);
	if (!count) return 0;
	MEANING* glosses = D->w.glosses;
	for (unsigned int i = 1; i <= count; ++i)
	{
		if (GlossIndex(glosses[i]) == index) return i;
	}
	return 0;
}

static void WriteDictionaryReference(char* label,WORDP D,FILE* out)
{
    if (!D) return; 
	if (D->internalBits & DELETED_MARK) return;	// ignore bad links
    fprintf(out,"%s=%s ",label,D->word);
}

void WriteDictionary(WORDP D,uint64 data)
{
	if (D->internalBits & DELETED_MARK) return;
	if (*D->word == '$' && D->word[1]) return;	// var never and money never, but let $ punctuation through
	RemoveInternalFlag(D,(unsigned int)(-1 ^ (UTF8|UPPERCASE_HASH|DEFINES|HAS_GLOSS)));  // keep only these

	// choose appropriate subfile
	char c = GetLowercaseData(*D->word); 
	char name[40];
	if (IsDigit(c)) sprintf(name,"%c.txt",c); //   main real dictionary
    else if (!IsLowerCase(c)) sprintf(name,"other.txt"); //   main real dictionary
    else sprintf(name,"%c.txt",c);//   main real dictionary
    FILE* out = FopenUTF8WriteAppend(UseDictionaryFile(name));
	if (!out) 
		myexit("Dict write failed");

	//   write out the basics (name meaningcount idiomcount)
	fprintf(out," %s ( ",D->word);
	unsigned int count = GetMeaningCount(D);
	if (count) fprintf(out,"meanings=%d ",count);

	// check valid glosses (sometimes we have troubles that SHOULD have been found earlier)
	unsigned int ngloss = 0;
	for (unsigned int i = 1; i <= count; ++i)
	{
		if (GetGloss(D,i)) ++ngloss;
	}
	if (ngloss) fprintf(out,"glosses=%d ",ngloss);
	if (ngloss != GetGlossCount(D))
	{
		ReportBug("Bad gloss count for %s\r\n",D->word);
	}

	//   now do the dictionary bits into english
	WriteDictionaryFlags(D,out);
	if (D->systemFlags & CONDITIONAL_IDIOM) 
		fprintf(out," poscondition=%s ",D->w.conditionalIdiom);
 	fprintf(out,") ");

	//   these must have valuable ->properties on them
	WriteDictionaryReference("conjugate",GetTense(D),out);
	WriteDictionaryReference("plural",GetPlural(D),out);
	WriteDictionaryReference("comparative",GetComparison(D),out);

	//   show the meanings, with illustrative gloss
		
	fprintf(out,"\r\n");
	//   now dump the meanings and their glosses
	for (unsigned int i = 1; i <= count; ++i)
	{
		MEANING M = GetMeaning(D,i);
		fprintf(out,"    %s ", WriteMeaning(M,true)); 
		if (M & SYNSET_MARKER) //   facts for this will be OUR facts
		{
			M = MakeMeaning(D,i); // our meaning id
			FACT* F = GetSubjectNondeadHead(D);
			while (F)
			{
				if ( M == F->subject && F->verb == Mis) // show up path as information only
				{
					fprintf(out,"(^%s) ",WriteMeaning(F->object));  // shows an object that we link to up (parent)
					break;
				}
				F = GetSubjectNondeadNext(F);
			}
		}
		char* gloss =  GetGloss(D,i);
		if (gloss == NULL) gloss = "";
		fprintf(out,"%s\r\n",gloss);
	}
 
    fclose(out);
}

char* ReadDictionaryFlags(WORDP D, char* ptr,unsigned int* meaningcount, unsigned int * glosscount)
{
	char junk[MAX_WORD_SIZE];
	ptr = ReadCompiledWord(ptr,junk);
	uint64 properties = D->properties;
	uint64 flags = D->systemFlags;
	uint64 parsebits = D->parseBits;
	while (*junk && *junk != ')' )		//   read until closing paren
	{
		if (!strncmp(junk,"meanings=",9)) 
		{
			if (meaningcount) *meaningcount = atoi(junk+9);
		}
		else if (!strncmp(junk,"glosses=",8)) 
		{
			if (glosscount) *glosscount = atoi(junk+8);
		}
		else if (!strncmp(junk,"poscondition=",13)) 
		{
			ptr = ReadCompiledWord(junk+13,junk);
			D->w.conditionalIdiom = AllocateString(junk);
		}
		else if (!strncmp(junk,"#=",2));
		else if (!strcmp(junk,"posdefault:NOUN")) flags |= NOUN;
		else if (!strcmp(junk,"posdefault:VERB")) flags |= VERB;
		else if (!strcmp(junk,"posdefault:ADJECTIVE")) flags |= ADJECTIVE;
		else if (!strcmp(junk,"posdefault:ADVERB")) flags |= ADVERB;
		else if (!strcmp(junk,"posdefault:PREPOSITION")) flags |= PREPOSITION;
		else if (!strcmp(junk,"CONCEPT")) AddInternalFlag(D,CONCEPT); // only from a fact dictionary entry
		else if (!strcmp(junk,"TOPIC")) AddInternalFlag(D,TOPIC); // only from a fact dictionary entry
		else 
		{
			uint64 val = FindValueByName(junk);
			if (val) properties |= val;
			else
			{
				val = FindSystemValueByName(junk);
				if (val) flags |= val;
				else
				{
					val = FindParseValueByName(junk);
					if (val) parsebits |= val;
				}
			}
		}
		ptr = ReadCompiledWord(ptr,junk);
	}
	if (!(D->internalBits & DEFINES)) 
	{
		AddProperty(D,properties); // dont override existing define value
		AddSystemFlag(D,flags);
		AddParseBits(D,(unsigned int)parsebits);
	}
	return ptr;
}

void AddGloss(WORDP D,char* glossy,unsigned int index) // only a synset head can have a gloss
{ 
	//   cannot add gloss to entries before the freeze (space will free up when transient space chopped back but pointers will be bad).
	//   If some dictionary words cannot add after the fact, none should
	if (dictionaryLocked) return;
	if (D->systemFlags & CONDITIONAL_IDIOM) return;	// shared ptr with gloss, not allowed gloss any more
#ifndef NOGLOSS
	MEANING gloss = String2Index(glossy) | (index << 24);
	MEANING* glosses = D->w.glosses;
	//   if we run out of room, reallocate gloss space double in size (ignore the hole in memory)
	unsigned int oldCount = GetGlossCount(D);

	//prove we dont already have this here
	for (unsigned int i = 1; i <= oldCount; ++i) if (glosses[i] == gloss) return;

	unsigned int count = oldCount + 1;  
	if (!(count & oldCount)) //   new count has no bits in common with old count, is a new power of 2
	{
		glosses = (MEANING*) AllocateString(NULL,(count<<1),sizeof(MEANING)); 
		memset(glosses,0,(count<<1) * sizeof(MEANING)); //   just to be purist
		memcpy(glosses+1,D->w.glosses+1,oldCount * sizeof(MEANING));
		D->w.glosses =  glosses;
		AddInternalFlag(D,HAS_GLOSS);
	}
	*glosses = count;
	glosses[count] = gloss;
#endif
}

MEANING AddTypedMeaning(WORDP D,unsigned int type)
{
	unsigned int count = 1 + GetMeaningCount(D);
	MEANING M =  MakeTypedMeaning(D,count, SYNSET_MARKER | type);
	return AddMeaning(D,M);
}

MEANING AddMeaning(WORDP D,MEANING M)
{ //   worst case wordnet meaning count = 75 (break)
	//   meaning is 1-based (0 means generic)
	//   cannot add meaning to entries before the freeze (space will free up when transient space chopped back but pointers will be bad).
	//   If some dictionary words cannot add after the fact, none should
	//   Meanings disambiguate multiple POS per word. User not likely to be able to add words that have
	//   multiple parts of speech.
	if (dictionaryLocked) return 0;

	//   no meaning given, use self with meaning one
	if (!(((ulong_t)M) & MAX_DICTIONARY)) M |= MakeMeaning(D,(1 + GetMeaningCount(D))) | SYNSET_MARKER;
	//   meanings[0] is always the count of existing meanings
	//   Actual space available is always a power of 2.
	MEANING* meanings = GetMeanings(D);
	//   if we run out of room, reallocate meaning space double in size (ignore the hole in memory)
	unsigned int oldCount = GetMeaningCount(D);
	if (oldCount == MAX_MEANING) return 0; // refuse more -- (break and cut)

	//prove we dont already have this here
	for (unsigned int i = 1; i <= oldCount; ++i) 
	{
		if (meanings[i] == M) return M;
		if (GETTYPERESTRICTION(M) & PREPOSITION && GETTYPERESTRICTION(meanings[i]) & PREPOSITION) return meanings[i]; // ignore any duplicate prep entries
	}

	unsigned int count = oldCount + 1;  
	if (!(count & oldCount)) //   new count has no bits in common with old count, is a new power of 2
	{
		meanings = (MEANING*) AllocateString(NULL,(count<<1),sizeof(MEANING)); 
		memset(meanings,0,(count<<1) * sizeof(MEANING)); //   just to be purist
		memcpy(meanings+1,&GetMeaning(D,1),oldCount * sizeof(MEANING));
		D->meanings =  String2Index((char*)meanings);
	}
	meanings[0] = count;
	return meanings[count] = M;
}

MEANING GetMaster(MEANING T)
{ //   for a specific meaning return node that is master or return general node if all fails.
	if (!T) return 0;
    WORDP D = Meaning2Word(T);
    unsigned int index = Meaning2Index(T);
	if (!GetMeaningCount(D)) return MakeMeaning(D,index); // has none, all erased
	if (index > GetMeaningCount(D))
	{
		ReportBug("Bad meaning index %s %d",D->word,index)
		return MakeMeaning(D,0);
	}
	if (index == 0) return T;
	MEANING old = T;
	MEANING at = GetMeanings(D)[index];
	unsigned int n = 0;
	while (!(at & SYNSET_MARKER)) // find the correct ptr to return. The marked ptr means OUR dict entry is master, not that the ptr points to.
	{
		old = at;
		WORDP X = Meaning2Word(at);
		unsigned int ind = Meaning2Index(at);
		if (ind > GetMeaningCount(X)) 
		{
			ReportBug("syset master failure %s",X->word)
			return old;
		}
		at = GetMeanings(X)[ind];
		if (++n >= 20) break; // force an end arbitrarily
	}
    return old & SIMPLEMEANING; // never return the type flags or synset marker -- FindChild loop wont want them nor will fact creation.
}

void RemoveMeaning(MEANING M, MEANING M1)
{
	M1 &= STDMEANING; 
	
	//   remove meaning and keep only valid main POS values (may not have a synset ptr when its irregular conjugation or such)
	WORDP D = Meaning2Word(M);
	for (unsigned int i = 1; i <= GetMeaningCount(D); ++i)
	{
		if ((GetMeaning(D,i) & STDMEANING) == M1) // he points to ourself
		{
			GetMeaning(D,i) = 0;
			unsigned int g = GetGlossIndex(D,i);
			if (g) D->w.glosses[g] = 0; // kill the gloss also if any
		}
	}
}

MEANING ReadMeaning(char* word,bool create,bool precreated)
{// be wary of multiple deletes of same word in low-to-high-order
	char hold[MAX_WORD_SIZE];
	if (*word == '\\' && word[1] && !word[2])  strcpy(hold,word+1);	//   special single made safe, like \[  or \*
	else strcpy(hold,word);
	word = hold;

	unsigned int flags = 0;
	unsigned int index = 0;

	char* at = (*word != '~') ? strchr(word,'~') : NULL; 
	if (at && *word != '"' ) // beware of topics or other things, dont lose them. we want xxx~n (one character) or  xxx~digits  or xxx~23n
	{
		if (IsDigit(at[1]))  // number starter  at~3  or   at~3n
		{
			index = atoi(at+1);
			char* p = at;
			while (IsDigit(*++p)); // find end
			if (*p == 'n') flags = NOUN;
			else if (*p == 'v') flags = VERB;
			else if (*p == 'a') flags = ADJECTIVE;
			else if (*p == 'b') flags = ADVERB;
			if (*p == 'z' ||  (*p && p[1] == 'z')) flags |= SYNSET_MARKER; 
			*at = 0; // drop the tail
		}
		if (index == 0) //   at~nz
		{
			if (at[2] && at[2] != ' ' && at[2] != 'z'){;} // insure flag only the last character - write meaning can write multiple types, but only for internal display. externally only 1 type at a time is allowed to be input
			else if (at[1] == 'n') flags = NOUN;
			else if (at[1] == 'v') flags = VERB;
			else if (at[1] == 'a') flags = ADJECTIVE;
			else if (at[1] == 'b') flags = ADVERB;
			if (at[1] == 'z' || at[2] == 'z') flags |= SYNSET_MARKER;
			if (flags) *at = 0;
		}
	}
	if (*word == '"') 
	{
		if (!precreated) 
		{
			strcpy(hold,JoinWords(BurstWord(word,CONTRACTIONS)));
			word = hold;
		}
		else if (word[1] == FUNCTIONSTRING) {;} // compiled script string
		//else // some other quoted thing, strip off the quotes, becomes raw text
		//{
		//	if (!word[1]) return (MEANING)0;	 // just a " is bad
		//	memmove(hold,word+1,strlen(word)); // the system should already have this correct if reading a file. dont burst and rejoin
		//	size_t len = strlen(hold);
		//	hold[len-1] = 0;	// remove ending dq
		//	word = hold; // hereinafter, this fact will be written out as `xxxx` instead
		//}
	}
	if (!*word) return 0;
	WORDP D = (create) ? StoreWord(word,AS_IS) : FindWord(word,0,PRIMARY_CASE_ALLOWED);
    return (!D)  ? (MEANING)0 :  (MakeMeaning(D,index) | flags);
}

bool ReadDictionary(char* file)
{
	char junk[MAX_WORD_SIZE];
	char word[MAX_WORD_SIZE];
	char* ptr;
    char* equal;
	FILE* in = FopenReadOnly(file); // DICT text dictionary file
	if (!in) return false;
	while (ReadALine(readBuffer,in) >= 0)
	{
		ptr = ReadCompiledWord(readBuffer,word); // word
		if (!*word) continue;
		ptr = ReadCompiledWord(ptr,junk);	//   read open paren
		if (*junk != '(') 
			ReportBug("bad dictionary alignment")
		WORDP D = StoreWord(word,AS_IS);
		++rawWords;
		if (stricmp(D->word,word)) ReportBug("Dictionary read does not match original %s %s\r\n",D->word,word)
		unsigned int meaningCount = 0;
		unsigned int glossCount = 0;
		ptr = ReadDictionaryFlags(D,ptr,&meaningCount,&glossCount);

		//   precreate meanings...

		//   read cross-reference attribute ptrs
		while (*ptr)		//   read until closing paren
		{
			ptr = ReadCompiledWord(ptr,word);
			if (!*word) break;
			equal = strchr(word,'=');
			*equal++ = 0;
			if (!strcmp(word,"conjugate")) { SetTense(D,MakeMeaning(StoreWord(equal)));}
			else if (!strcmp(word,"plural")) {SetPlural(D,MakeMeaning(StoreWord(equal)));}
			else if (!strcmp(word,"comparative")) { SetComparison(D,MakeMeaning(StoreWord(equal)));}
		}

		//   directly create meanings, since we know the size-- no meanings may be added after this
		if (meaningCount)
		{
			MEANING* meanings = (MEANING*) AllocateString(NULL,(meaningCount+1),sizeof(MEANING),true); 
			meanings[0]= meaningCount;
			D->meanings =  String2Index((char*)meanings);

			unsigned int glossIndex = 0;
			//   directly create gloss space, since we know the size-- no glosses may be added after this
			if (glossCount) // reserve space for this many glosses
			{
				MEANING* glosses = (MEANING*) AllocateString(NULL,(glossCount+1), sizeof(MEANING),true); 
				glosses[0] = glossCount;
				D->w.glosses =  glosses;
				AddInternalFlag(D,HAS_GLOSS);
			}
			for (unsigned int i = 1; i <= meaningCount; ++i) //   read each meaning
			{
				ReadALine(readBuffer,in);
				char* ptr = ReadCompiledWord(readBuffer,junk);
				GetMeaning(D,i) = ReadMeaning(junk,true,true);
				if (*ptr == '(') ptr = strchr(ptr,')') + 2; // point after the )
				if (glossCount && *ptr && GetMeaning(D,i) & SYNSET_MARKER) 
					D->w.glosses[++glossIndex] =  String2Index(AllocateString(ptr)) + (i << 24);
			}
			if (glossIndex != glossCount)
			{
				ReportBug("Actual gloss index of %s %d not matching count of expected %d ",D->word,glossIndex,glossCount);
			}
		}
	}
	fclose(in);
	return true;
}

MEANING MakeTypedMeaning(WORDP x, unsigned int y, unsigned int flags)
{
	return (!x) ? 0 : (((MEANING)(Word2Index(x) + (((uint64)y) << INDEX_OFFSET))) | (flags << TYPE_RESTRICTION_SHIFT));
}

MEANING MakeMeaning(WORDP x, unsigned int y) //   compose a meaning
{
    return (!x) ? 0 : (((MEANING)(Word2Index(x) + (((uint64)y) << INDEX_OFFSET))));
}

WORDP Meaning2Word(MEANING x) //   convert meaning to its dictionary entry
{
    WORDP D = (!x) ? NULL : Index2Word((((uint64)x) & MAX_DICTIONARY)); 
	return D;
}

unsigned int GetMeaningType(MEANING T)
{
    if (T == 0) return 0;
	WORDP D = Meaning2Word(T);
    unsigned int index = Meaning2Index(T);
	if (index) T = GetMeaning(D,index); //   change to synset head for specific meaning
	else if (GETTYPERESTRICTION(T)) return GETTYPERESTRICTION(T); //   generic word type it must be
	D = Meaning2Word(T);
	return (unsigned int) (D->properties & PART_OF_SPEECH);
}

MEANING FindSynsetParent(MEANING T,unsigned int which) //  presume we are at the master, next wordnet
{
    WORDP D = Meaning2Word(T);
    unsigned int index = Meaning2Index(T);
    FACT* F = GetSubjectNondeadHead(D); //   facts involving word 
	unsigned int count = 0;
    while (F)
    {
        FACT* at = F;
        F = GetSubjectNondeadNext(F);
        if (at->verb == Mis) // wordnet meaning
		{
			//   prove indexes mate up
			if (index && index != Meaning2Index(at->subject)) continue; // must match generic or specific precisely
			if (count++ == which) return at->object; //   next set/class in line
		}
    }
    return 0;
}

MEANING FindSetParent(MEANING T,int n) //   next set parent
{
    WORDP D = Meaning2Word(T);
    unsigned int index = Meaning2Index(T);
	uint64 restrict = GETTYPERESTRICTION(T);
	if (!restrict && index) restrict = GETTYPERESTRICTION(GetMeaning(D,index));
    FACT* F = GetSubjectNondeadHead(D); //   facts involving word 
    while (F)
    {
        FACT* at = F;
		F = GetSubjectNondeadNext(F);
        if (!(at->verb == Mmember)) continue;
     
		//   prove indexes mate up
		unsigned int localIndex = Meaning2Index(at->subject); //   what fact says
        if (index != localIndex && localIndex) continue; //   must match generic or specific precisely
		if (restrict && GETTYPERESTRICTION(at->subject)  && !(GETTYPERESTRICTION(at->subject) & restrict)) continue; // not match type restriction 

        if (--n == 0) 
		{
   			if (trace == TRACE_HIERARCHY) TraceFact(F);
			return at->object; // next set/class in line
		}
    }
    return 0;
}

char* WriteMeaning(MEANING T,bool withPos)
{
	if (!T) return "";
    WORDP D = Meaning2Word(T);

	if ((T & MEANING_BASE) == T) return D->word; 

	//   need to annotate the value
    static char mybuffer[150];
	strcpy(mybuffer,D->word); 
	char* at = mybuffer + strlen(mybuffer);
   
	//   index 
	unsigned int index = Meaning2Index(T);
	if (index > 9) 
	{
		*at++ = '~';
		*at++ = (char)((index / 10) + '0');
		*at++ = (char)((index % 10) + '0');
	}
	else if (index)
	{
		*at++ = '~';
		*at++ = (char)(index + '0');
	}

	if (withPos)
	{
		if (GETTYPERESTRICTION(T) && !index) *at++ = '~';	// pos marker needed on generic
		if (GETTYPERESTRICTION(T) & NOUN) *at++ = 'n'; 
		else if (GETTYPERESTRICTION(T) & VERB) *at++ = 'v'; 
		else if (GETTYPERESTRICTION(T) & ADJECTIVE) *at++ = 'a';
		else if (GETTYPERESTRICTION(T) & ADVERB) *at++ = 'b';
	}
	if (T & SYNSET_MARKER) *at++ = 'z';
	*at = 0;
    return mybuffer;
}

void NoteLanguage()
{
	FILE* out = FopenUTF8Write("language.txt"); 
	fprintf(out,"%s\r\n",language); // current default language
	fclose(out);
}

void ReadSubstitutes(char* name,unsigned int fileFlag, bool filegiven)
{
	char file[MAX_WORD_SIZE];
	if (filegiven) strcpy(file,name);
	else sprintf(file,"%s/%s",livedata,name);
    char original[MAX_WORD_SIZE];
    char replacement[MAX_WORD_SIZE];
    FILE* in = FopenStaticReadOnly(file); // LIVEDATA substitutes
    if (!in) return;
    while (ReadALine(readBuffer,in)  >= 0) 
    {
        if (*readBuffer == '#' || *readBuffer == 0) continue;
        char* ptr = ReadCompiledWord(readBuffer,original); //   original phrase
		
        if (*original == 0 || *original == '#') continue;
		//   replacement can be multiple words joined by + and treated as a single entry.  
		ptr = ReadCompiledWord(ptr,replacement);    //   replacement phrase
		WORDP D = FindWord(original,0,PRIMARY_CASE_ALLOWED);	//   do we know original already?
		if (D && D->internalBits & HAS_SUBSTITUTE)
		{
			if (!compiling) Log(STDUSERLOG,"Currently have a substitute for %s in %s\r\n",original,readBuffer);
			continue;
		}
		D = StoreWord(original,AS_IS); //   original word
		AddInternalFlag(D,fileFlag|HAS_SUBSTITUTE);
		RemoveInternalFlag(D,HAS_GLOSS); // no longer usable as that
		if (!(D->systemFlags & CONDITIONAL_IDIOM)) D->w.substitutes = NULL;
		else printf("BAD Substitute conflicts with conditional idiom %s\r\n",D->word);
		if (GetPlural(D))  SetPlural(D,0);
		if (GetComparison(D))  SetComparison(D,0);
		if (GetTense(D)) SetTense(D,0);

		unsigned int n = BurstWord(D->word);
		char wd[MAX_WORD_SIZE];
		strcpy(wd,JoinWords(1));
		// now determine the multiword headerness...
		char* word = wd;
		if (*word == '<') ++word;		// do not show the < starter for lookup
		size_t len = strlen(word);
		if (len > 1 && word[len-1] == '>')  word[len-1] = 0;	// do not show the > on the starter for lookup
		WORDP E = StoreWord(word);		// create the 1-word header
		if (n > GETMULTIWORDHEADER(E)) SETMULTIWORDHEADER(E,n);	//   mark it can go this far for an idiom

		WORDP S = NULL;
		if (replacement[0] != 0 && replacement[0] != '#') 	//   with no substitute, it will just erase itself
		{
			if (strchr(replacement,'_'))
				printf("Warning-- substitution replacement %s of %s in %s at line %d has _ in it\r\n",replacement,original,name,currentFileLine);
			D->w.substitutes = S = StoreWord(replacement,AS_IS);  //   the valid word
			AddSystemFlag(S,SUBSTITUTE_RECIPIENT);
			// for the emotions (like ~emoyes) we want to be able to reverse access, so make them a member of the set
			if (*S->word == '~') CreateFact(MakeMeaning(D),Mmember,MakeMeaning(S));
		}

        //   if original has hyphens, replace as single words also. Note burst form for initial marking will be the same
        bool hadHyphen = false;
		char copy[MAX_WORD_SIZE];
		strcpy(copy,original);
        ptr = copy;
        while (*++ptr) // replace all alphabetic hypens using _
        {
            if (*ptr == '-' && IsAlphaUTF8(ptr[1])) 
            {
                *ptr = '_';
                hadHyphen = true;
            }
        }
        if (hadHyphen) 
        {
			D = FindWord(copy);	//   do we know original already?
			if (D && D->internalBits & HAS_SUBSTITUTE)
			{
				ReportBug("Already have a substitute for %s of %s",original,readBuffer)
				continue;
			}
	
			D = StoreWord(copy,0);
			AddInternalFlag(D,fileFlag|HAS_SUBSTITUTE);
 			D->w.substitutes = S;
 			RemoveInternalFlag(D,HAS_GLOSS); // no longer usable as that
			if (GetPlural(D)) SetPlural(D,0);
			if (GetComparison(D)) SetComparison(D,0);
			if (GetTense(D)) SetTense(D,0);
       }
	}
    fclose(in);
}

void ReadWordsOf(char* name,uint64 mark)
{
	char file[MAX_WORD_SIZE];
	sprintf(file,"%s/%s",livedata,name);
    char word[MAX_WORD_SIZE];
    FILE* in = FopenStaticReadOnly(file); // LOWERCASE TITLES LIVEDATA scriptcompile nonwords allowed OR lowercase title words
    if (!in) return;
    while (ReadALine(readBuffer,in)  >= 0) 
    {
        char* ptr = ReadCompiledWord(readBuffer,word); 
        if (*word != 0 && *word != '#') 
		{
			WORDP D = StoreWord(word,mark); 
			ReadCompiledWord(ptr,word);
			if (!stricmp(word,"FOREIGN_WORD")) AddProperty(D,FOREIGN_WORD);
		}

	}
    fclose(in);
}

void ReadCanonicals(char* file)
{
    char original[MAX_WORD_SIZE];
    char replacement[MAX_WORD_SIZE];
    FILE* in = FopenStaticReadOnly(file); // LIVEDATA canonicals
    if (!in) return;
    while (ReadALine(readBuffer,in)  >= 0) 
    {
        if (*readBuffer == '#' || *readBuffer == 0) continue;

        char* ptr = ReadCompiledWord(readBuffer,original); //   original phrase
        if (*original == 0 || *original == '#') continue;
        ptr = ReadCompiledWord(ptr,replacement);    //   replacement word
		WORDP D = StoreWord(original);
		WORDP R = StoreWord(replacement);
		SetCanonical(D,MakeMeaning(R));
	}
    fclose(in);
}

void ReadAbbreviations(char* name)
{
	char file[MAX_WORD_SIZE];
	sprintf(file,"%s/%s",livedata,name);
    char word[MAX_WORD_SIZE];
    FILE* in = FopenStaticReadOnly(file); // LIVEDATA abbreviations
    if (!in) return;
    while (ReadALine(readBuffer,in)  >= 0) 
    {
		ReadCompiledWord(readBuffer,word); 
		if (*word != 0 && *word != '#')  
		{
			WORDP D = StoreWord(word,0,KINDERGARTEN);
			RemoveInternalFlag(D,DELETED_MARK);
		}
	}
    fclose(in);
}

void ReadQueryLabels(char* name)
{
    char word[MAX_WORD_SIZE];
    FILE* in = FopenStaticReadOnly(name); // LIVEDATA queries.txt
    if (!in) return;
    while (ReadALine(readBuffer,in)  >= 0) 
    {
        if (*readBuffer == '#' ||  *readBuffer == 0) continue;
        char* ptr = ReadCompiledWord(readBuffer,word);    // the name or query: name
        if (*word == 0) continue;
		if (!stricmp(word,"query:")) ptr = ReadCompiledWord(ptr,word); 

		ptr = SkipWhitespace(ptr); // in case excess blanks before control string
        WORDP D = StoreWord(word);
		AddInternalFlag(D, QUERY_KIND);
		if (*ptr == '"') // allowed quoted string
		{
			ReadCompiledWord(ptr,word);
			ptr = word+1;
			char* at = strchr(ptr,'"');
			*at = 0;
		}
		else // ordinary chars
		{
			char* at = strchr(ptr,' '); // in case has blanks after control string
			if (at) *at = 0;
		}
 	    D->w.userValue = AllocateString(ptr);    // read query labels
    }
    fclose(in);
}

void ReadLivePosData()
{
	// read pos rules of english langauge
	uint64 xdata[MAX_POS_RULES * MAX_TAG_FIELDS];
	char*  xcommentsData[MAX_POS_RULES];
	data = xdata;
	commentsData = xcommentsData;
	tagRuleCount = 0;
	char word[MAX_WORD_SIZE];
	sprintf(word,"%s",englishFolder);
	WalkDirectory(word,ReadPosPatterns,0);
	tags = (uint64*)AllocateString((char*) xdata,tagRuleCount * MAX_TAG_FIELDS, sizeof(uint64),false);
	comments = 0;
	bool haveComments = true;
#ifdef IOS // applications dont want comments
	haveComments = false;
#endif
#ifdef NOMAIN
	haveComments = false;
#endif
	if (haveComments) comments = (char**)AllocateString((char*) xcommentsData,tagRuleCount,sizeof(char*),true);
}

void ReadLiveData()
{
	// system livedata
	char word[MAX_WORD_SIZE];
	sprintf(word,"%s/systemessentials.txt",systemFolder);
	ReadSubstitutes(word,DO_ESSENTIALS,true);
	sprintf(word,"%s/canonical.txt",systemFolder);
	ReadCanonicals(word);
	sprintf(word,"%s/queries.txt",systemFolder);
	ReadQueryLabels(word);

	ReadSubstitutes("substitutes.txt",DO_SUBSTITUTES);
	ReadSubstitutes("contractions.txt",DO_CONTRACTIONS);
	ReadSubstitutes("interjections.txt",DO_INTERJECTIONS);
	ReadSubstitutes("british.txt",DO_BRITISH);
	ReadSubstitutes("spellfix.txt",DO_SPELLING);
	ReadSubstitutes("texting.txt",DO_TEXTING);
	ReadSubstitutes("noise.txt",DO_NOISE);
	ReadWordsOf("lowercaseTitles.txt",LOWERCASE_TITLE);
}

static bool ReadAsciiDictionary()
{
    char buffer[50];
	unsigned int n = 0;
	bool found = false;
	rawWords = 0;
	for (char i = '0'; i <= '9'; ++i)
	{
		sprintf(buffer,"%c.txt",i);
		if (!ReadDictionary(UseDictionaryFile(buffer))) ++n;
		else found = true;
	}
	for (char i = 'a'; i <= 'z'; ++i)
	{
		sprintf(buffer,"%c.txt",i);
		if (!ReadDictionary(UseDictionaryFile(buffer))) ++n;
		else found = true;
	}
	if (!ReadDictionary(UseDictionaryFile("other.txt"))) ++n;
	else found = true;
	if (n) printf("Missing %d word files\r\n",n);
	printf("read %d raw words\r\n",rawWords);
	return found;
}

void VerifyEntries(WORDP D,uint64 junk) // prove meanings have synset heads and major kinds have subkinds
{
	if (D->internalBits & (DELETED_MARK|WORDNET_ID) || D->internalBits & DEFINES) return;

	if (D->properties & VERB && !(D->properties & VERB_BITS)) ReportBug("Verb %s lacks tenses\r\n",D->word);
	if (D->properties & NOUN && !(D->properties & NOUN_BITS)) ReportBug("Noun %s lacks subkind\r\n",D->word);
	if (D->properties & ADVERB && !(D->properties & ADVERB)) ReportBug("Adverb %s lacks subkind\r\n",D->word);
	if (D->properties & ADJECTIVE && !(D->properties & ADJECTIVE_BITS)) ReportBug("Adjective %s lacks subkind\r\n",D->word);

	unsigned int count = GetMeaningCount(D);
	for(unsigned int i = 1; i <= count; ++i)
	{
		MEANING M = GetMeanings(D)[i]; // what we point to in synset land
		if (!M)
		{
			ReportBug("Has no meaning %s %d\r\n",D->word,i)
			return;
		}
		WORDP X = Meaning2Word(M);
		unsigned int index = Meaning2Index(M);
		if (index > GetMeaningCount(X)) 
			ReportBug("Has meaning index too high %s.%d points to %s.%d but limit is %d\r\n",D->word,i,X->word,index, GetMeaningCount(X))
			
		// can we find the master meaning for this meaning?
		MEANING at = M;
		unsigned int n = 0;
		while (!(at & SYNSET_MARKER)) // find the correct ptr to return as master
		{
			WORDP X = Meaning2Word(at);
			if (X->internalBits & DELETED_MARK) ReportBug("Synset goes to dead word %s",X->word)
			unsigned int ind = Meaning2Index(at);
			if (ind > GetMeaningCount(X)) 
			{
				ReportBug("syset master failure %s",X->word)
				return;
			}
			if (!ind ) 
			{
				ReportBug("syset master failure %s refers to no meaning index",X->word)
				return;
			}			
			at = GetMeanings(X)[ind];
			if (++n >= MAX_SYNLOOP) 
			{
				ReportBug("syset master loop overflow %s",X->word)
				return;
			}
		}
	}

	// verify glosses match up legal
	unsigned int glossCount = GetGlossCount(D);
	for (unsigned int x = 1; x <= glossCount; ++x)
	{
		if (GlossIndex(D->w.glosses[x]) > count)
		{
			ReportBug("Gloss out of range for gloss %d   %s~%d with count only  %d\r\n",x,D->word,GlossIndex(D->w.glosses[x]),count);
			D->w.glosses[x] = 0;	// bad ref
		}
	}

	count = GetMeaningCount(D);
	unsigned int synsetHeads;
	for (unsigned int i = 1; i <= count; ++i)
	{
		synsetHeads = 0;
		unsigned int counter = 0;
		MEANING M = GetMeaning(D,i);
		WORDP X = Meaning2Word(M);
		unsigned int index = Meaning2Index(M);
		if (M & SYNSET_MARKER);
		else while (X != D) // run til we loop once back to this entry, counting synset heads we see
		{
			if (X->internalBits & DELETED_MARK)
			{
				ReportBug("Synset references dead entry %s word: %s meaning: %d\r\n",X->word,D->word,i)
				break;
			}
			if (M & SYNSET_MARKER) ++synsetHeads; // prior was a synset head
			index = Meaning2Index(M);
			if (index == 0) break; // generic pointer
			if (!GetMeanings(X))
			{
				M = 0;
				ReportBug("Missing synsets for %s word: %s meaning: %d\r\n",X->word,D->word,i)
				break;
			}
			if (GetMeaningCount(X) < index)
			{
				ReportBug("Missing synset index %s %s\r\n",X->word,D->word)
				break;
			}
			M = GetMeaning(X,index);
			X = Meaning2Word(M);
			if (++counter > MAX_SYNLOOP) break; // in case of trouble
		}
		if (M & SYNSET_MARKER) ++synsetHeads; // prior was a synset head
		if (synsetHeads != 1 || counter > MAX_SYNLOOP) 
			ReportBug("Bad synset list %s heads: %d count: %d\r\n",D->word,synsetHeads,counter)
	}
	if (GetTense(D)) 
	{
		WORDP E = GetTense(D);
		while (E != D)
		{
			if (!E)
			{
				ReportBug("Missing conjugation %s \r\n",D->word)
				break;
			}
			if (E->internalBits & DELETED_MARK)
			{
				ReportBug("Deleted conjucation %s %s \r\n",D->word,E->word)
				break;
			}
			E = GetTense(E);
		}
	}
	if (GetPlural(D)) 
	{
		WORDP E = GetPlural(D);
		while (E != D)
		{
			if (!E)
			{
				ReportBug("Missing plurality %s \r\n",D->word)
				break;
			}
			if (E->internalBits & DELETED_MARK)
			{
				ReportBug("Deleted plurality %s %s \r\n",D->word,E->word)
				break;
			}
			E = GetPlural(E);
		}
	}
	if (GetComparison(D)) 
	{
		WORDP E = GetComparison(D);
		while (E != D)
		{
			if (!E)
			{
				ReportBug("Missing comparison %s \r\n",D->word)
				break;
			}
			if (E->internalBits & DELETED_MARK)
			{
				ReportBug("Deleted comparison %s %s \r\n",D->word,E->word)
				break;
			}
			E = GetComparison(E);
		}
	}

	// anything with a singular noun meaning should have an uplink
	if (D->properties & NOUN_SINGULAR && GetMeanings(D) && buildDictionary)
	{
		unsigned int count = GetMeaningCount(D);
		for (unsigned int i = 1; i <= count; ++i)
		{
			if (! (GETTYPERESTRICTION(GetMeaning(D,i)) & NOUN)) continue;

			// might be just a "more noun" word
			WORDP X = Meaning2Word(GetMeaning(D,i));
			if (X == D) continue; // points to self is good enough

			MEANING M = GetMaster(GetMeaning(D,i));
			X = Meaning2Word(M);
			FACT* F = GetSubjectNondeadHead(X);
			while (F)
			{
				if (F->subject == M && F->verb == Mis && !(F->flags & FACTDEAD)) break;
				F = GetSubjectNondeadNext(F);
			}

			if (!F && !(D->internalBits & UPPERCASE_HASH)) 
				Log(STDUSERLOG,"Meaning %d of %s with master %s missing uplink IS\r\n",i,D->word,WriteMeaning(M));
		}
	}
}

void LoadDictionary()
{
	if (!ReadBinaryDictionary()) //   if binary form not there or wrong hash, use text form (slower)
	{
		InitFactWords(); 
		AcquireDefines("SRC/dictionarySystem.h"); //   get dictionary defines (must occur before loop that decodes properties into sets (below)
		if (ReadAsciiDictionary())
		{
			*currentFilename = 0;
			WalkDictionary(VerifyEntries); // prove good before writeout
			remove(UseDictionaryFile("facts.bin")); // insure no erroneous binary of facts
			remove(UseDictionaryFile("dict.bin")); 
			WriteBinaryDictionary(); //   store the faster read form of dictionary
		}
	}
	else
	{
		InitFactWords(); 
		AcquireDefines("SRC/dictionarySystem.h"); //   get dictionary defines (must occur before loop that decodes properties into sets (below)
	}

	AcquirePosMeanings();
	ReadAbbreviations("abbreviations.txt"); // needed for burst/tokenizing
	*currentFilename = 0;
	fullDictionary = (!stricmp(language,"ENGLISH")) || (dictionaryFree-dictionaryBase) > 170000; // a lot of words are defined, must be a full dictionary.
}

WORDP BUILDCONCEPT(char* word) 
{
	WORDP name = StoreWord(word); 
	AddInternalFlag(name,CONCEPT);
	return name;
}

void ExtendDictionary()
{
	Dtopic = BUILDCONCEPT("~topic");
	Mburst = MakeMeaning(StoreWord("^burst"));
	Mchatoutput = MakeMeaning(StoreWord("chatoutput"));
	MgambitTopics = MakeMeaning(StoreWord("^gambittopics"));
	Mintersect = MakeMeaning(StoreWord("^intersect"));
	Mkeywordtopics = MakeMeaning(StoreWord("^keywordtopics"));
	Mconceptlist = MakeMeaning(StoreWord("^conceptlist"));
 	Mmoney = MakeMeaning(BUILDCONCEPT("~moneynumber"));
	Musd = MakeMeaning(BUILDCONCEPT("~usd"));
	Myen = MakeMeaning(BUILDCONCEPT("~yen"));
	Mcny = MakeMeaning(BUILDCONCEPT("~cny"));
	Meur = MakeMeaning(BUILDCONCEPT("~eur"));
	Minr = MakeMeaning(BUILDCONCEPT("~inr"));
	Mgbp = MakeMeaning(BUILDCONCEPT("~gbp"));
	Mnumber = MakeMeaning(BUILDCONCEPT("~number"));
	MadjectiveNoun  = MakeMeaning(BUILDCONCEPT("~adjective_noun"));
	Mpending = MakeMeaning(StoreWord("^pending"));
	DunknownWord  = StoreWord("unknown-word");

	// generic concepts the engine marks automatically
	Dadult = BUILDCONCEPT("~adultword");
	Dchild = BUILDCONCEPT("~childword");
	Dfemalename = BUILDCONCEPT("~femalename"); 
	Dhumanname = BUILDCONCEPT("~humanname"); 
	Dmalename = BUILDCONCEPT("~malename"); 
    Dplacenumber = BUILDCONCEPT("~placenumber"); 
	Dpronoun = BUILDCONCEPT("~pronoun");
	Dadjective= BUILDCONCEPT("~adjective");
	Dauxverb = BUILDCONCEPT("~aux_verb");
	Dpropername = BUILDCONCEPT("~propername"); 
	Mphrase = MakeMeaning( BUILDCONCEPT("~phrase"));
	MabsolutePhrase = MakeMeaning( BUILDCONCEPT("~absolutephrase"));
	MtimePhrase = MakeMeaning( BUILDCONCEPT("~timeephrase"));
	Dclause = BUILDCONCEPT("~clause"); 
	Dverbal = BUILDCONCEPT("~verbal"); 
	Dtime = BUILDCONCEPT("~timeword"); 
	Dunknown = BUILDCONCEPT("~unknownword"); 
	// predefine builtin sets with no engine variables
	unsigned int i = 0;
	char* ptr;
	while ((ptr = predefinedSets[i++]) != 0) BUILDCONCEPT(ptr);
}

char* FindCanonical(char* word, unsigned int i,bool notNew)
{
	uint64 controls = PRIMARY_CASE_ALLOWED;
    WORDP D = FindWord(word,0,PRIMARY_CASE_ALLOWED);
	if (i == startSentence || i == 1)
	{
		WORDP S = FindWord(word,0,SECONDARY_CASE_ALLOWED);
		if (S && IsLowerCase(*S->word))  D = S;
	}
    if (D && !buildDictionary) 
	{
		char* answer = GetCanonical(D);
		if (answer) return answer; //   special canonical form (various pronouns typically)
	}

    //    numbers - use digit form
	char* number;
    if (IsNumber(word))
    {
        char word1[MAX_WORD_SIZE];
        if (strchr(word,'.') || strlen(word) > 9)  //   big numbers need float
        {
            float y;
			if (*word == '$') y = (float)atof(word+1);
			else y = (float)atof(word);
            int x = (int)y;
            if (((float) x) == y) sprintf(word1,"%d",x); //   use int where you can
            else sprintf(word1,"%1.2f",atof(word)); 
        }
		else if (GetCurrency(word,number)) sprintf(word1,"%d",atoi(number));
#ifdef WIN32
        else sprintf(word1,"%I64d",Convert2Integer(word)); // integer
#else
        else sprintf(word1,"%lld",Convert2Integer(word)); // integer
#endif
        WORDP N = StoreWord(word1,ADJECTIVE|NOUN|ADJECTIVE_NUMBER|NOUN_NUMBER); // digit format cannot be ordinal
		return N->word;
    }
 
	// before seeing if canoncial can come from verb, see if it is from a known noun.  "cavities" shouldnt create cavity as a verb
	char* noun = NULL;
	size_t len = strlen(word);
	if (word[len-1] == 's') noun = English_GetSingularNoun(word,true,true); // do we already KNOW this as a an extension of a noun

    //   VERB
    char* verb = English_GetInfinitive(word,(noun) ? true : notNew);
    if (verb) 
    {
        WORDP V = FindWord(verb,0,controls);
        verb = (V) ? V->word : NULL;
    }
	if (verb) return verb; //   we prefer verb base-- gerunds are nouns and verbs for which we want the verb

    //   NOUN
    noun = English_GetSingularNoun(word,true,notNew);
    if (noun) 
    {
        WORDP  N = FindWord(noun,0,controls);
        noun = (N) ? N->word : NULL;
    }
	if (noun) return noun;
    
	//   ADJECTIVE
    char* adjective = English_GetAdjectiveBase(word,(noun) ? false : notNew);
    if (adjective) 
    {
        WORDP A = FindWord(adjective,0,controls);
        adjective = (A) ? A->word : NULL;
    }
	if (adjective) return adjective;
 
	//   ADVERB
    char* adverb = English_GetAdverbBase(word,(noun) ? false : notNew);
    if (adverb) 
    {
        WORDP A = FindWord(adverb,0,controls);
        adverb = (A) ? A->word : NULL;
    }
	if (adverb) return adverb;

	return (D && D->properties & PART_OF_SPEECH) ? D->word : NULL;
}

bool IsHelper(char* word)
{
    WORDP D = FindWord(word,0,tokenControl & STRICT_CASING ? PRIMARY_CASE_ALLOWED : 0);
    return (D && D->properties & AUX_VERB);
}

bool IsFutureHelper(char* word)
{
	WORDP D = FindWord(word,0,tokenControl & STRICT_CASING ? PRIMARY_CASE_ALLOWED : 0);
    return (D &&  D->properties & AUX_VERB_FUTURE);
}    
	
bool IsPresentHelper(char* word)
{
	WORDP D = FindWord(word,0,tokenControl & STRICT_CASING ? PRIMARY_CASE_ALLOWED : 0);
	return (D && D->properties & AUX_VERB && D->properties & (VERB_PRESENT | VERB_PRESENT_3PS | AUX_VERB_PRESENT));
}

bool IsPastHelper(char* word)
{
	WORDP D = FindWord(word,0,tokenControl & STRICT_CASING ? PRIMARY_CASE_ALLOWED : 0);
    return (D && D->properties & AUX_VERB && D->properties & (AUX_VERB_PAST | VERB_PAST));
}

void DumpDictionaryEntry(char* word,unsigned int limit)
{
	char name[MAX_WORD_SIZE];
	strcpy(name,word);
	MEANING M = ReadMeaning(word,false,true);
	unsigned int index = Meaning2Index(M);
	uint64 oldtoken = tokenControl;
	tokenControl |= STRICT_CASING;
	WORDP D = Meaning2Word(M);
	if (D && IS_NEW_WORD(D) && (*D->word != '~' && *D->word == '$'   && *D->word == '^')) D = 0;	// debugging may have forced this to store, its not in base system
	if (limit == 0) limit = 5; // default
	if (D) 	Log(STDUSERLOG,"\r\n%s (%d):\r\n  Properties: ",name,Word2Index(D));
	else Log(STDUSERLOG,"\r\n%s (unknown word):\r\n  Properties: ",name);
	uint64 properties = (D) ? D->properties : 0;
	uint64 sysflags = (D) ? D->systemFlags : 0;
	uint64 cansysflags =  0;
	uint64 bit = START_BIT;	
	while (bit)
	{
		if (properties & bit) Log(STDUSERLOG,"%s ",FindNameByValue(bit));
		bit >>= 1;
	}

	WORDP entry = NULL;
	WORDP canonical = NULL;
	char* tilde = strchr(name+1,'~');
	wordStarts[0] = reuseAllocation(wordStarts[0],"");
	posValues[0] = 0;
	posValues[1] = 0;
	wordStarts[1] = reuseAllocation(wordStarts[1],"");
	posValues[2] = 0;
	wordStarts[2] = reuseAllocation(wordStarts[2],word);
	posValues[3] = 0;
	wordStarts[3] = reuseAllocation(wordStarts[3],"");
	if (tilde && IsDigit(tilde[1])) *tilde = 0;	// turn off specificity
	uint64 xflags = 0;
	uint64 inferredProperties = (name[0] != '~' && name[0] != '^') ? GetPosData(2,name,entry,canonical,xflags,cansysflags) : 0; 
	sysflags |= xflags;
	if (entry) D = entry;
	bit = START_BIT;
	bool extended = false;
	while (bit)
	{
		if (inferredProperties & bit)
		{
			if (!(properties & bit)) // bits beyond what was directly known in dictionary before
			{
				if (!extended) Log(STDUSERLOG," Implied: ");
				extended = true;
				char* label = FindNameByValue(bit);
				Log(STDUSERLOG,"%s ",label);
			}
		}
		bit >>= 1;
	}
	Log(STDUSERLOG,"\r\n  SystemFlags: ");

	bit = START_BIT;
	while (bit)
	{
		if (sysflags & bit)
		{
			char word[MAX_WORD_SIZE];
			if (!(bit & ESSENTIAL_FLAGS)) Log(STDUSERLOG,"%s ",MakeLowerCopy(word,FindSystemNameByValue(bit)));
		}
		bit >>= 1;
	}
	if (sysflags & ESSENTIAL_FLAGS)
	{
		Log(STDUSERLOG," POS-tiebreak: ");
		if (sysflags & NOUN) Log(STDUSERLOG,"NOUN ");
		if (sysflags & VERB) Log(STDUSERLOG,"VERB ");
		if (sysflags & ADJECTIVE) Log(STDUSERLOG,"ADJECTIVE ");
		if (sysflags & ADVERB) Log(STDUSERLOG,"ADVERB ");
		if (sysflags & PREPOSITION) Log(STDUSERLOG,"PREPOSITION ");
	}
	if (!D) return;

	if (D->systemFlags & CONDITIONAL_IDIOM)  Log(STDUSERLOG,"poscondition=%s\r\n",D->w.conditionalIdiom);
	
	Log(STDUSERLOG,"\r\n  ParseBits: ");
	bit = START_BIT;
	while (bit)
	{
		if (D->parseBits & bit)
		{
			char word[MAX_WORD_SIZE];
			Log(STDUSERLOG,"%s ",MakeLowerCopy(word,FindParseNameByValue(bit)));
		}
		bit >>= 1;
	}

	Log(STDUSERLOG,"  \r\n  InternalBits: ");
#ifndef DISCARDTESTING
	unsigned int basestamp = inferMark;
#endif
	NextInferMark();  

#ifndef DISCARDTESTING 
	if (D->internalBits & CONCEPT  && !(D->internalBits & TOPIC)) Log(STDUSERLOG,"concept (%d members) ",CountSet(D,basestamp));
#endif

	if (D->internalBits & QUERY_KIND) Log(STDUSERLOG,"query ");
	if (D->internalBits & MACRO_TRACE ) Log(STDUSERLOG,"being-traced ");
	if (D->internalBits & CONCEPT  && !(D->internalBits & TOPIC)) Log(STDUSERLOG,"concept ");
	if (D->internalBits & TOPIC) Log(STDUSERLOG,"topic ");
	if (D->internalBits & BUILD0) Log(STDUSERLOG,"build0 ");
	if (D->internalBits & BUILD1) Log(STDUSERLOG,"build1 ");
	if (D->internalBits & BUILD2) Log(STDUSERLOG,"build2 ");
	if (D->internalBits & HAS_EXCLUDE) Log(STDUSERLOG,"has_exclude ");
	if (D->systemFlags & SUBSTITUTE_RECIPIENT) Log(STDUSERLOG,"substituteRecipient ");
	if (D->internalBits & HAS_SUBSTITUTE) 
	{
		Log(STDUSERLOG,"substitute=");
		if (GetSubstitute(D)) Log(STDUSERLOG,"%s ",GetSubstitute(D)->word); 
		else Log(STDUSERLOG,"  ");
	}
	if (D->internalBits & FUNCTION_NAME) 
	{
		char* kind = "";

		SystemFunctionInfo* info = NULL;
		if (D->x.codeIndex)	info = &systemFunctionSet[D->x.codeIndex];	//   system function

		if ((D->internalBits & FUNCTION_BITS) ==  IS_PLAN_MACRO) kind = (char*) "plan";
		else if ((D->internalBits & FUNCTION_BITS) == IS_OUTPUT_MACRO) kind = (char*)"output";
		else if ((D->internalBits & FUNCTION_BITS) ==  IS_TABLE_MACRO) kind = (char*) "table";
		else if ((D->internalBits & FUNCTION_BITS) ==  IS_PATTERN_MACRO) kind = (char*)"pattern";
		else if ((D->internalBits & FUNCTION_BITS) ==  (IS_PATTERN_MACRO | IS_OUTPUT_MACRO)) kind = (char*) "dual";
		if (D->x.codeIndex && (D->internalBits & FUNCTION_BITS) !=  IS_PLAN_MACRO) Log(STDUSERLOG,"systemfunction %d (%d arguments) ", D->x.codeIndex,info->argumentCount);
		else if (D->x.codeIndex && (D->internalBits & FUNCTION_BITS) ==  IS_PLAN_MACRO) Log(STDUSERLOG,"plan (%d arguments)", D->w.planArgCount);
		else Log(STDUSERLOG,"user %s macro (%d arguments)\r\n  %s \r\n",kind,MACRO_ARGUMENT_COUNT(D),D->w.fndefinition+1); // 1st byte is argument count
		if (D->internalBits & VARIABLE_ARGS_TABLE) Log(STDUSERLOG,"variableArgs");
	}
	Log(STDUSERLOG,"\r\n  Other:   ");
	if (*D->word == '%') Log(STDUSERLOG,"systemvar ");
	if (*D->word == '$')
	{
		char* val = GetUserVariable(D->word);
		Log(STDUSERLOG,"VariableValue= \"%s\" ",val);
	}
	if (canonical) Log(STDUSERLOG,"  canonical: %s ",canonical->word);
	Log(STDUSERLOG,"\r\n");
	tokenControl = oldtoken;
	if (GetTense(D)) 
	{
		Log(STDUSERLOG,"  ConjugationLoop= ");
		WORDP E = GetTense(D);
		while (E != D)
		{
			Log(STDUSERLOG,"-> %s ",E->word);
			E = GetTense(E);
		}
		Log(STDUSERLOG,"\r\n");
	}
	if (GetPlural(D)) 
	{
		Log(STDUSERLOG,"  PluralLoop= ");
		WORDP E = GetPlural(D);
		while (E != D)
		{
			Log(STDUSERLOG,"-> %s ",E->word);
			E = GetPlural(E);
		}
		Log(STDUSERLOG,"\r\n");
	}
	if (GetComparison(D)) 
	{
		Log(STDUSERLOG,"  comparativeLoop= ");
		WORDP E = GetComparison(D);
		while (E != D)
		{
			Log(STDUSERLOG,"-> %s ",E->word);
			E = GetComparison(E);
		}
		Log(STDUSERLOG,"\r\n");
	}
	
	//   now dump the meanings
	unsigned int count = GetMeaningCount(D);
	if (count) Log(STDUSERLOG,"  Meanings:");
	uint64 kind = 0;
	for (unsigned int i = 1; i <= count; ++i)
	{
		if (index && i != index) continue;
		MEANING M = GetMeaning(D,i);
		uint64 k1 = GETTYPERESTRICTION(M);
		if (kind != k1)
		{
			kind = k1;
			if (GETTYPERESTRICTION(M) & NOUN) Log(STDUSERLOG,"\r\n    noun\r\n");
			else if (GETTYPERESTRICTION(M) & VERB) Log(STDUSERLOG,"\r\n    verb\r\n");
			else if (GETTYPERESTRICTION(M) & ADJECTIVE) Log(STDUSERLOG,"\r\n    adjective\r\n");
			else if (GETTYPERESTRICTION(M) & ADVERB) Log(STDUSERLOG,"\r\n    adverb\r\n");
			else Log(STDUSERLOG,"\r\n    misc\r\n");
		}
		char* gloss;
		MEANING master = GetMaster(M);
		gloss = GetGloss(Meaning2Word(master),Meaning2Index(master));
		if (!gloss) gloss = "";
		Log(STDUSERLOG,"    %d: %s %s\r\n",i,WriteMeaning(master & STDMEANING,true),gloss);

		M = GetMeaning(D,i) & STDMEANING;
		bool did = false;
		while (Meaning2Word(M) != D) // if it points to base word, the loop is over.
		{
			MEANING next = GetMeaning(Meaning2Word(M),Meaning2Index(M));
			if ((next & STDMEANING) == M) break;	 // only to itself
			if (!did) 
			{
				did = true;
				Log(STDUSERLOG,"      synonyms: ");
			}
			if (next & SYNSET_MARKER) Log(STDUSERLOG," *%s ",WriteMeaning(M));	// mark us as master for display
			else Log(STDUSERLOG," %s ",WriteMeaning(M)); 
			M = next & STDMEANING;
		}
		if (did) // need to display closure in for seeing MASTER marker, even though closure is us
		{
 			if (GetMeaning(D,i) & SYNSET_MARKER) Log(STDUSERLOG," *%s ",WriteMeaning(M)); 
			else Log(STDUSERLOG," %s ",WriteMeaning(M)); 
			Log(STDUSERLOG,"\r\n"); //   header for this list
		}
	}

	if (D->inferMark) Log(STDUSERLOG,"  Istamp- %d\r\n",D->inferMark);
	if (GETMULTIWORDHEADER(D)) Log(STDUSERLOG,"  MultiWordHeader length: %d\r\n",GETMULTIWORDHEADER(D));

	// show concept/topic members
	FACT* F = GetSubjectNondeadHead(D);
	Log(STDUSERLOG,"  Direct Sets: ");
	while (F)
	{
		if (index && Meaning2Index(F->subject) && Meaning2Index(F->subject) != index ){;} // wrong path member
		if (F->verb == Mmember) Log(STDUSERLOG,"%s ",Meaning2Word(F->object)->word);
		F = GetSubjectNondeadNext(F);
	}
	Log(STDUSERLOG,"\r\n");

	char* buffer = AllocateBuffer();
	Log(STDUSERLOG,"  Facts:\r\n");

	count = 0;
	F = GetSubjectNondeadHead(D);
	while (F)
	{
		Log(STDUSERLOG,"    %s",WriteFact(F,false,buffer,false,true));
		if (++count >= limit) break;
		F = GetSubjectNondeadNext(F);
	}

	F = GetVerbNondeadHead(D);
	count = limit;
	while (F)
	{
		Log(STDUSERLOG,"    %s",WriteFact(F,false,buffer,false,true));
		if (++count >= limit) break;
		F = GetVerbNondeadNext(F);
	}
	
	F = GetObjectNondeadHead(D);
	count = 0;
	while (F)
	{
		Log(STDUSERLOG,"    %s",WriteFact(F,false,buffer,false,true));
		if (++count >= limit) break;
		F = GetObjectNondeadNext(F);
	}

	FreeBuffer();
}

#ifndef DISCARDDICTIONARYBUILD
#include "../extraSrc/readrawdata.cpp"
#endif

#ifdef COPYRIGHT

Per use of the WordNet dictionary data....

 This software and database is being provided to you, the LICENSEE, by  
  2 Princeton University under the following license.  By obtaining, using  
  3 and/or copying this software and database, you agree that you have  
  4 read, understood, and will comply with these terms and conditions.:  
  5   
  6 Permission to use, copy, modify and distribute this software and  
  7 database and its documentation for any purpose and without fee or  
  8 royalty is hereby granted, provided that you agree to comply with  
  9 the following copyright notice and statements, including the disclaimer,  
  10 and that the same appear on ALL copies of the software, database and  
  11 documentation, including modifications that you make for internal  
  12 use or for distribution.  
  13   
  14 WordNet 3.0 Copyright 2006 by Princeton University.  All rights reserved.  
  15   
  16 THIS SOFTWARE AND DATABASE IS PROVIDED "AS IS" AND PRINCETON  
  17 UNIVERSITY MAKES NO REPRESENTATIONS OR WARRANTIES, EXPRESS OR  
  18 IMPLIED.  BY WAY OF EXAMPLE, BUT NOT LIMITATION, PRINCETON  
  19 UNIVERSITY MAKES NO REPRESENTATIONS OR WARRANTIES OF MERCHANT-  
  20 ABILITY OR FITNESS FOR ANY PARTICULAR PURPOSE OR THAT THE USE  
  21 OF THE LICENSED SOFTWARE, DATABASE OR DOCUMENTATION WILL NOT  
  22 INFRINGE ANY THIRD PARTY PATENTS, COPYRIGHTS, TRADEMARKS OR  
  23 OTHER RIGHTS.  
  24   
  25 The name of Princeton University or Princeton may not be used in  
  26 advertising or publicity pertaining to distribution of the software  
  27 and/or database.  Title to copyright in this software, database and  
  28 any associated documentation shall at all times remain with  
  29 Princeton University and LICENSEE agrees to preserve same.  
#endif
