
#define MAX_SYNLOOP	60

#define MAX_HASH_BUCKETS 50000 
#ifdef WIN32
#define MAX_ENTRIES      0x000fffff 
#else
#define MAX_ENTRIES      (0x000affff)
#endif

#define ALLOCATESTRING_SIZE_PREFIX 3
#define ALLOCATESTRING_SIZE_SAFEMARKER 2
#define ALLOCATESTRING_MARKER 0xff

#define GETNEXTNODE(D) (D->nextNode & NODEBITS)		// top byte is the length of joined phrases of which this is header
#define GETMULTIWORDHEADER(D)  (D->nextNode >> MULTIWORDHEADER_SHIFT)
#define SETMULTIWORDHEADER(D,n) (  D->nextNode &= NODEBITS, D->nextNode |= n << MULTIWORDHEADER_SHIFT )

#define IS_NEW_WORD(x) (!x || !(x->internalBits & BASE_DEFINED)) // created by user volley

#define ALL_OBJECTS ( MAINOBJECT | MAININDIRECTOBJECT | OBJECT2 | INDIRECTOBJECT2 )

// system internal bits on dictionary entries internalBits

// these values of word->internalBits are NOT stored in the dictionary text files but are generated while reading in data

// various sources of livedata substitions 
//	used 	0x00000001 
//	used	0x00000002
//	used	0x00000004
//	used	0x00000008
//	used	0x00000010 
//	used	0x00000020 
//	used	0x00000040 
//	used	0x00000080 
//	used	0x00000100 thru PRIVATE

#define QUERY_KIND				0x00000200		// is a query item (from LIVEDATA or query:)
#define LABEL					QUERY_KIND		// transient scriptcompiler use
#define RENAMED					QUERY_KIND		// _alpha name renames _number or @name renames @n
#define HAS_GLOSS				0x00000400		// has gloss ptr (all normal words)	
#define FN_NO_TRACE				0x00000800		// dont trace this function (on functions only)

#define UTF8					0x00001000		// word has utf8 char in it (all normal words)
#define UPPERCASE_HASH			0x00002000		// word has upper case English character in it
#define VAR_CHANGED				0x00004000		// $variable has changed value this volley
#define NOTRACE_TOPIC			VAR_CHANGED		// dont trace this topic (topic names)
#define WORDNET_ID				0x00008000		// a wordnet synset header node (MASTER w gloss ) only used when building a dictionary -- or transient flag for unduplicate
#define MACRO_TRACE				WORDNET_ID		// turn on tracing for this function (only used when live running)
#define INTERNAL_MARK			0x00010000		// transient marker for Intersect coding and Country testing in :trim
#define FROM_FILE				INTERNAL_MARK	//  for scriptcompiler to tell stuff comes from FILE not DIRECTORY
#define BEEN_HERE				0x00020000		// used in internal word searches that might recurse
#define BASE_DEFINED			0x00040000		// word had part of speech bits when dictionary was locked (enables you to tell new properties filled in on old dict entries)
#define FAKE_NOCONCEPTLIST		BASE_DEFINED	// used on concepts declared NOCONCEPTLIST
#define DELETED_MARK			0x00080000		// transient marker for  deleted words in dictionary build - they dont get written out - includes script table macros that are transient
#define BUILD0					0x00100000		// comes from build0 data (marker on functions, concepts, topics)
#define BUILD1					0x00200000		// comes from build1 data
#define HAS_EXCLUDE				0x00400000		// concept/topic has keywords to exclude
#define BUILD2					0x00800000		// comes from dynamic build2 data
#define FUNCTION_NAME			0x01000000 	//   name of a ^function  (has non-zero ->x.codeIndex if system, else is user but can be patternmacro,outputmacro, or plan) only applicable to ^ words
#define CONCEPT					0x02000000	// topic or concept has been read via a definition
#define TOPIC					0x04000000	//  this is a ~xxxx topic name in the system - only applicable to ~ words
#define VARIABLE_ARGS_TABLE		0x08000000		// only for table macros
#define UPPERCASE_MATCH			VARIABLE_ARGS_TABLE	// match on this concept should store canonical as upper case
#define DEFINES					0x10000000		// word is a define, starts with `, uses ->properties and ->infermark as back and forth links

#define IS_OUTPUT_MACRO			0x20000000	// function is an output macro
#define IS_TABLE_MACRO			0x40000000	// function is a table macro - transient executable output function
#define IS_PLAN_MACRO			( IS_TABLE_MACRO | IS_OUTPUT_MACRO )	// function is a plan macro (specialized form of IS_OUTPUT_MACRO has a codeindex which is the topicindex)
#define IS_PATTERN_MACRO		0x80000000 
#define FUNCTION_BITS ( IS_PATTERN_MACRO | IS_OUTPUT_MACRO | IS_TABLE_MACRO | IS_PLAN_MACRO )

#define FN_TRACE_BITS ( MACRO_TRACE | FN_NO_TRACE )

///   DEFINITION OF A MEANING 
#define GETTYPERESTRICTION(x) ( ((x)>>TYPE_RESTRICTION_SHIFT) & TYPE_RESTRICTION)
#define STDMEANING ( INDEX_BITS | MEANING_BASE | TYPE_RESTRICTION ) // no synset marker
#define SIMPLEMEANING ( INDEX_BITS | MEANING_BASE ) // simple meaning, no type

//   codes for BurstWord argument
#define SIMPLE 0
#define STDBURST 0		// normal burst behavior
#define POSSESSIVES 1
#define CONTRACTIONS 2
#define HYPHENS 4
#define COMPILEDBURST 8  // prepare argument as though it were output script		
#define NOBURST 16		// dont burst (like for a quoted text string)

#define FUNCTIONSTRING '^'


#define MACRO_ARGUMENT_COUNT(D) ((unsigned char)(*D->w.fndefinition - 'A')) // for user macros not plans

#define KINDS_OF_PHRASES ( CLAUSE | PHRASE | VERBAL | OMITTED_TIME_PREP | OMITTED_OF_PREP | QUOTATION_UTTERANCE )

// pos tagger ZONE roles for a comma zone
#define ZONE_SUBJECT			0x000001	// noun before any verb
#define ZONE_VERB				0x000002
#define ZONE_OBJECT				0x000004	// noun AFTER a verb
#define ZONE_CONJUNCT			0x000008	// coord or subord conjunction
#define ZONE_FULLVERB			0x000010	// has normal verb tense or has aux
#define ZONE_AUX				0x000020	// there is aux in the zone
#define ZONE_PCV				0x000040	// zone is entirely phrases, clauses, and verbals
#define ZONE_ADDRESS			0x000080	// zone is an addressing name start. "Bob, you are amazing."
#define ZONE_ABSOLUTE			0x000100	// absolute zone has subject and partial participle verb, used to describe noun in another zone
#define ZONE_AMBIGUOUS			0x000200	// type of zone is not yet known

//   values for FindWord lookup
#define PRIMARY_CASE_ALLOWED 1024
#define SECONDARY_CASE_ALLOWED 2048
#define STANDARD_LOOKUP (PRIMARY_CASE_ALLOWED |  SECONDARY_CASE_ALLOWED )
#define LOWERCASE_LOOKUP 4096
#define UPPERCASE_LOOKUP 8192

#define NO_EXTENDED_WRITE_FLAGS ( PATTERN_WORD  )
#define MARK_FLAGS (  TIMEWORD | ACTUAL_TIME | WEB_URL | LOCATIONWORD )

// postag composites 
#define PUNCTUATION_BITS	( COMMA | PAREN | PUNCTUATION | QUOTE | CURRENCY )

#define NORMAL_WORD		( PARTICLE | ESSENTIAL_FLAGS | FOREIGN_WORD | INTERJECTION | THERE_EXISTENTIAL | TO_INFINITIVE | QWORD | DETERMINER_BITS | POSSESSIVE_BITS | CONJUNCTION | AUX_VERB | PRONOUN_BITS )
#define PART_OF_SPEECH		( PUNCTUATION_BITS  | NORMAL_WORD   ) 

#define VERB_CONJUGATION_PROPERTIES ( VERB_CONJUGATE1 | VERB_CONJUGATE2 | VERB_CONJUGATE3 ) 
#define VERB_PHRASAL_PROPERTIES ( INSEPARABLE_PHRASAL_VERB | MUST_BE_SEPARATE_PHRASAL_VERB | SEPARABLE_PHRASAL_VERB | PHRASAL_VERB )
#define VERB_OBJECTS ( VERB_NOOBJECT | VERB_INDIRECTOBJECT | VERB_DIRECTOBJECT | VERB_TAKES_GERUND | VERB_TAKES_ADJECTIVE | VERB_TAKES_INDIRECT_THEN_TOINFINITIVE | VERB_TAKES_INDIRECT_THEN_VERBINFINITIVE | VERB_TAKES_TOINFINITIVE | VERB_TAKES_VERBINFINITIVE )
#define VERB_SYSTEM_PROPERTIES ( PRESENTATION_VERB | COMMON_PARTICIPLE_VERB | VERB_CONJUGATION_PROPERTIES | VERB_PHRASAL_PROPERTIES | VERB_OBJECTS ) 

#define NOUN_PROPERTIES ( NOUN_HE | NOUN_THEY | NOUN_SINGULAR | NOUN_PLURAL | NOUN_PROPER_SINGULAR | NOUN_PROPER_PLURAL | NOUN_ABSTRACT | NOUN_HUMAN | NOUN_FIRSTNAME | NOUN_SHE | NOUN_TITLE_OF_ADDRESS | NOUN_TITLE_OF_WORK  )
#define SIGNS_OF_NOUN_BITS ( NOUN_DESCRIPTION_BITS | PRONOUN_SUBJECT | PRONOUN_OBJECT )

#define NUMBER_BITS ( NOUN_NUMBER | ADJECTIVE_NUMBER )

#define VERB_PROPERTIES (  VERB_BITS )

#define Index2Word(n) (dictionaryBase+n)
#define Word2Index(D) ((uint64) (D-dictionaryBase))
#define GetMeanings(D) ((MEANING*) Index2String(D->meanings))
#define GetMeaning(D,k) GetMeanings(D)[k]
#define GetMeaningsFromMeaning(T) (GetMeanings(Meaning2Word(T)))
#define Meaning2Index(x) ((unsigned int)((x & INDEX_BITS) >> INDEX_OFFSET)) //   which dict entry meaning

#define GetFactBack(D) ((D->temps) ? GetTemps(D)[FACTBACK] : 0) // transient per search
unsigned char* GetWhereInSentence(WORDP D); // always skips the linking field at front
#define USEDTEMPSLIST 3
#define TRIEDBITS 2
#define WORDVALUE 1
#define FACTBACK 0

#define OOB_START '['
#define OOB_END ']'
void LockLevel();
void UnlockLevel();

void PrepareConjugates(WORDP D);
#define PLURALFIELD 0
#define AccessPlural(D) ((MEANING*)Index2String(D->extensions))[PLURALFIELD]
#define GetPlural(D) ((D->extensions) ? Meaning2Word(AccessPlural(D)) : 0)
void SetPlural(WORDP D,MEANING M);
#define COMPARISONFIELD 1
#define AccessComparison(D) ((MEANING*)Index2String(D->extensions))[COMPARISONFIELD]
#define GetComparison(D) ((D->extensions) ? Meaning2Word(AccessComparison(D)) : 0)
#define SetComparison(D,M) { PrepareConjugates(D); AccessComparison(D) = M; }
#define TENSEFIELD 2
#define AccessTense(D) ((MEANING*)Index2String(D->extensions))[TENSEFIELD]
#define GetTense(D) ((D->extensions) ? Meaning2Word(AccessTense(D)) : 0)
#define SetTense(D,M) {PrepareConjugates(D); AccessTense(D) = M; }
#define CANONICALFIELD 3
#define AccessCanonical(D) ((MEANING*)Index2String(D->extensions))[CANONICALFIELD]
#define SetCanonical(D,M) {PrepareConjugates(D); AccessCanonical(D) = M; }
char* GetCanonical(WORDP D);
void ReadSubstitutes(char* name,unsigned int fileFlag,bool filegiven = false);

// memory data
extern WORDP dictionaryBase;
extern char* stringBase;
extern char* stringFree;
extern char* stringEnd;
extern uint64 maxDictEntries;
extern unsigned long maxStringBytes;
extern unsigned int userTopicStoreSize;
extern unsigned int userTableSize;
extern unsigned long maxHashBuckets;
extern bool setMaxHashBuckets;
extern WORDP dictionaryLocked;
extern bool fullDictionary;
extern uint64 verbFormat;
extern uint64 nounFormat;
extern uint64 adjectiveFormat;
extern uint64 adverbFormat;
extern MEANING posMeanings[64];
extern MEANING sysMeanings[64];
extern bool buildDictionary;
extern char language[40];
extern FACT* factLocked;
extern char* stringLocked;

extern WORDP dictionaryPreBuild[NUMBER_OF_LAYERS+1];
extern char* stringsPreBuild[NUMBER_OF_LAYERS+1];
extern WORDP dictionaryFree;
extern char dictionaryTimeStamp[20];

// internal references to defined words
extern WORDP Dplacenumber;
extern WORDP Dpropername;
extern MEANING Mphrase;
extern MEANING MabsolutePhrase;
extern MEANING MtimePhrase;
extern WORDP Dclause;
extern WORDP Dverbal;
extern WORDP Dmalename,Dfemalename,Dhumanname;
extern WORDP Dtime;
extern WORDP Dunknown;
extern WORDP DunknownWord;
extern WORDP Dpronoun;
extern WORDP Dadjective;
extern WORDP Dauxverb;
extern WORDP Dchild,Dadult;
extern WORDP Dtopic;
extern MEANING Mmoney;
extern MEANING Musd;
extern MEANING Meur;
extern MEANING Mgbp;
extern MEANING Myen;
extern MEANING Mcny;
extern MEANING Mchatoutput;
extern MEANING Mburst;
extern MEANING Mpending;
extern MEANING Mkeywordtopics;
extern MEANING Mconceptlist;
extern MEANING Mintersect;
extern MEANING MgambitTopics;
extern MEANING MadjectiveNoun;
extern MEANING Mnumber;
extern char livedata[500];
extern char englishFolder[500];
extern char systemFolder[500];
char* expandAllocation(char* old, char* word,int size);
char* AllocateString(char* word,size_t len = 0,int bytes= 1,bool clear = false);
WORDP StoreWord(int);
WORDP StoreWord(char* word, uint64 properties = 0);
WORDP StoreWord(char* word, uint64 properties, uint64 flags);
WORDP FindWord(const char* word, int len = 0,uint64 caseAllowed = STANDARD_LOOKUP);
WORDP FullStore(char* word, uint64 properties, uint64 flags);
unsigned char BitCount(uint64 n);
void ReadQueryLabels(char* file);
char* reuseAllocation(char* old, char* word);
char* reuseAllocation(char* old, char* word,int len);
char* UseDictionaryFile(char* name);
char* Index2String(unsigned int offset);
inline unsigned int String2Index(char* str) {return (!str) ? 0 : (stringBase - str);}
inline unsigned int GlossIndex(MEANING M) { return M >> 24;}
void ReadAbbreviations(char* file);
void ReadLiveData();
void ReadLivePosData();
WORDP GetSubstitute(WORDP D);
void ShowStats(bool reset);
MEANING FindChild(MEANING who,int n);
void ReadCanonicals(char* file);

// adjust data on a dictionary entry
void AddProperty(WORDP D, uint64 flag);
void RemoveProperty(WORDP D, uint64 flag);
void RemoveSystemFlag(WORDP D, uint64 flag);
void AddSystemFlag(WORDP D, uint64 flag);
void AddInternalFlag(WORDP DP, unsigned int flag);
void AddParseBits(WORDP D, unsigned int flag);
void RemoveInternalFlag(WORDP D,unsigned int flag);
void WriteDWord(WORDP ptr, FILE* out);
WORDP ReadDWord(FILE* in);
void AddCircularEntry(WORDP base, unsigned int field,WORDP entry);
void SetWordValue(WORDP D, int x);
int GetWordValue(WORDP D);

inline unsigned int GetMeaningCount(WORDP D) { return (D->meanings) ? GetMeaning(D,0) : 0;}
inline unsigned int GetGlossCount(WORDP D) 
{
	if (D->internalBits & HAS_GLOSS)  return D->w.glosses[0];
	return 0;
}
char* GetGloss(WORDP D, unsigned int index);
unsigned int GetGlossIndex(WORDP D,unsigned int index);
void DictionaryRelease(WORDP until,char* stringUsed);

// startup and shutdown routines
void InitDictionary();
void CloseDictionary();
void LoadDictionary();
void ExtendDictionary();
void WordnetLockDictionary();
void ReturnDictionaryToWordNet();
void LockLayer(int layer);
void ReturnToLayer(int layer,bool unlocked);
void DeleteDictionaryEntry(WORDP D);
void BuildDictionary(char* junk);

// read and write dictionary or its entries
void WriteDictionary(WORDP D, uint64 data);
void DumpDictionaryEntry(char* word,unsigned int limit);
bool ReadDictionary(char* file);
char* ReadDictionaryFlags(WORDP D, char* ptr,unsigned int *meaningcount = NULL, unsigned int *glosscount = NULL);
void WriteDictionaryFlags(WORDP D, FILE* out);
void WriteBinaryDictionary();
bool ReadBinaryDictionary();
void Write32(unsigned int val, FILE* out);
unsigned int Read32(FILE* in);
void Write64(uint64 val, FILE* out);
uint64 Read64(FILE* in);
void Write24(unsigned int val, FILE* out);

// utilities
void ReadWordsOf(char* file,uint64 mark);
void WalkDictionary(DICTIONARY_FUNCTION func,uint64 data = 0);
char* FindCanonical(char* word, unsigned int i, bool nonew = false);
void VerifyEntries(WORDP D,uint64 junk);
void NoteLanguage();

bool IsHelper(char* word);
bool IsFutureHelper(char* word);
bool IsPresentHelper(char* word);
bool IsPastHelper(char* word);

///   code to manipulate MEANINGs
MEANING MakeTypedMeaning(WORDP x, unsigned int y, unsigned int flags);
MEANING MakeMeaning(WORDP x, unsigned int y = 0);
WORDP Meaning2Word(MEANING x);
MEANING AddMeaning(WORDP D,MEANING M);
MEANING AddTypedMeaning(WORDP D,unsigned int type);
void AddGloss(WORDP D,char* gloss,unsigned int index);
void RemoveMeaning(MEANING M, MEANING M1);
MEANING ReadMeaning(char* word,bool create=true,bool precreated = false);
char* WriteMeaning(MEANING T,bool withPOS = false);
MEANING GetMaster(MEANING T);
unsigned int GetMeaningType(MEANING T);
MEANING FindSynsetParent(MEANING T,unsigned int which = 0);
MEANING FindSetParent(MEANING T,int n);

