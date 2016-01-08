#include "common.h"

#ifdef INFORMATION

Facts are added as layers. You remove facts by unpeeling a layer. You can "delete" a fact merely by
marking it dead.

Layer1:  facts resulting from wordnet dictionary  (wordnetFacts)
Layer2:	 facts resulting from topic system build0
Layer3:	 facts resulting from topic system build1
Layer4:	 facts created by user

Layer 4 is always unpeeled after an interchange with the chatbot, in preparation for a new user who may chat with a different persona.
Layers 2 and 3 are unpeeled if you want to restart the topic system to read in new topic data on the fly or rebuild 0.
Layer 3 is unpeeled for a new build 1.

Layer 1 is never unpeeled. If you want to modify the dictionary, you either restart the chatbot entirely
or patch in data piggy backing on facts (like from the topic system).

Unpeeling a layer implies you will also reset dictionary/stringspace pointers back to levels at the
start of the layer since facts may have allocated dictionary and string items. 
This is ReturnToDictionaryFreeze for unpeeling 3/4 and ReturnDictionaryToWordNet for unpeeling layer 2.

#endif

size_t maxFacts = MAX_FACT_NODES;	// how many facts we can create at max

FACT* factBase = NULL;			// start of all facts
FACT* factEnd = NULL;			// end of all facts
FACT* wordnetFacts = NULL;		// end of facts after dictionary load
FACT* build0Facts = NULL;		// end of build0 facts, start of build1 facts
FACT* factFree = NULL;			// currently next fact we can reuse for allocation
FACT* currentFact = NULL;		// current fact

//   values of verbs to compare against
MEANING Mmember;				// represents concept sets
MEANING Mis;					// represents wordnet hierarchy
MEANING Mexclude;				// represents restriction of word not allowed in set (blocking inheritance)

FACT* Index2Fact(FACTOID e)
{ 
	FACT* F = NULL;
	if (e)
	{
		F =  e + factBase;
		if (F > factFree)
		{
			ReportBug("Illegal fact index")
			F = NULL;
		}
	}
	return F;
}

FACT* GetSubjectNext(FACT* F) { return Index2Fact(F->subjectNext);}
FACT* GetVerbNext(FACT* F) {return Index2Fact(F->verbNext);}
FACT* GetObjectNext(FACT* F) {return Index2Fact(F->objectNext);}

FACT* GetSubjectNondeadNext(FACT* F) 
{ 
	while (F) 
	{
		F =  Index2Fact(F->subjectNext);
		if (F && ! (F->flags & FACTDEAD)) break;
	}
	return F;
}

FACT* GetVerbNondeadNext(FACT* F) 
{
	while (F) 
	{
		F =  Index2Fact(F->verbNext);
		if (F && ! (F->flags & FACTDEAD)) break;
	}
	return F;
}

FACT* GetObjectNondeadNext(FACT* F) 
{
	while (F) 
	{
		F =  Index2Fact(F->objectNext);
		if (F && ! (F->flags & FACTDEAD)) break;
	}
	return F;
}

FACT* GetSubjectNondeadHead(FACT* F) 
{
	F = Index2Fact(F->subjectHead);
	while (F && F->flags & FACTDEAD) 
	{
		F =  Index2Fact(F->subjectNext);
	}
	return F;
}

FACT* GetVerbNondeadHead(FACT* F) 
{
	F = Index2Fact(F->verbHead);
	while (F && F->flags & FACTDEAD) 
	{
		F =  Index2Fact(F->verbNext);
	}
	return F;
}

FACT* GetObjectNondeadHead(FACT* F) 
{
	F = Index2Fact(F->objectHead);
	while (F && F->flags & FACTDEAD) 
	{
		F =  Index2Fact(F->objectNext);
	}
	return F;
}

FACT* GetSubjectNondeadHead(WORDP D) 
{
	FACT* F = Index2Fact(D->subjectHead);
	while (F && F->flags & FACTDEAD) 
	{
		F =  Index2Fact(F->subjectNext);
	}

	return F;
}

FACT* GetVerbNondeadHead(WORDP D) 
{
	FACT* F = Index2Fact(D->verbHead);
	while (F && F->flags & FACTDEAD) 
	{
		F =  Index2Fact(F->verbNext);
	}
	return F;
}

FACT* GetObjectNondeadHead(WORDP D)  
{
	FACT* F = Index2Fact(D->objectHead);
	while (F && F->flags & FACTDEAD) 
	{
		F =  Index2Fact(F->objectNext);
	}
	return F;
}


void SetSubjectNext(FACT* F, FACT* value){ F->subjectNext = Fact2Index(value);}
void SetVerbNext(FACT* F, FACT* value) {F->verbNext = Fact2Index(value);}
void SetObjectNext(FACT* F, FACT* value){ F->objectNext = Fact2Index(value);}

FACTOID Fact2Index(FACT* F) 
{ 
	return  (F) ? ((FACTOID)(F - factBase)) : 0;
}

FACT* FactTextIndex2Fact(char* id) // given number word, get corresponding fact
{
	char word[MAX_WORD_SIZE];
	strcpy(word,id);
	char* comma = word;
	while ((comma = strchr(comma,','))) memmove(comma,comma+1,strlen(comma));  // maybe number has commas, like 100,000,300 . remove them
	unsigned int n = atoi(word);
	if (n <= 0) return NULL;
	return (n <= (unsigned int)(factFree-factBase)) ? Index2Fact(n) : NULL;
}

int GetSetID(char* x)
{
	if (*x != '@') return ILLEGAL_FACTSET;
	if (!IsDigit(*++x)) return ILLEGAL_FACTSET; 
	unsigned int n = *x - '0';
	if (IsDigit(*++x)) n = (n * 10) + *x - '0';
	// allow additional characters naming a field
	return (n >= MAX_FIND_SETS) ? ILLEGAL_FACTSET : n;
}

bool GetSetMod(char* x)
{
	if (!IsDigit(*++x)) return false; // illegal set
	if (IsDigit(*++x)) ++x;
	if ((*x == 's' || *x == 'S' ) && strnicmp(x,"subject",7)) return false;
	if ((*x == 'v' || *x == 'V' )&& strnicmp(x,"verb",4)) return false;
	if ((*x == 'o' || *x == 'O' )&& strnicmp(x,"object",6)) return false;
	if ((*x == 'a' || *x == 'A' )&& strnicmp(x,"all",4)) return false;
	if ((*x == 'f'|| *x == 'F' ) && strnicmp(x,"fact",4)) return false;
	return true;
}

char* GetSetType(char* x)
{ // @13subject returns subject
	x += 2;
	if (IsDigit(*x)) ++x;
	return x;
}

char* GetSetEnd(char* x)
{ // @adagsubject returns subject
	char* start = x;
	while (IsAlphaUTF8(*++x)){;} // find natural end.
	size_t len = x - start;	 // this long
	if (len >= 9 && !strnicmp(x-7,"subject",7)) x -= 7;
	else if (len >= 6 && !strnicmp(x-4,"verb",4)) x -= 4;
	else if (len >= 8 && !strnicmp(x-6,"object",6)) x -= 6;
	else if (len >= 6 && !strnicmp(x-4,"fact",4)) x -= 4;
	else if (len >= 5 && !strnicmp(x-3,"all",3)) x -= 3;

	if (IsDigit(*x)) ++x;
	return x; 
}

void TraceFact(FACT* F,bool ignoreDead)
{
	char* word = AllocateBuffer();
	Log(STDUSERLOG,"%d: %s\r\n",Fact2Index(F),WriteFact(F,false,word,ignoreDead,false));
	Log(STDUSERTABLOG,"");
	FreeBuffer();
}

void ClearUserFacts()
{
	while (factFree > factLocked)  FreeFact(factFree--); //   erase new facts
}

void InitFacts()
{
	if ( factBase == 0) 
	{
		factBase = (FACT*) malloc(maxFacts * sizeof(FACT)); // only on 1st startup, not on reload
		if ( factBase == 0)
		{
			printf("failed to allocate fact space\r\n");
			myexit("failed to get fact space");
		}
	}
	memset(factBase,0,sizeof(FACT) *  maxFacts); // not strictly necessary
    factFree = factBase;
	factEnd = factBase + maxFacts;
}

void InitFactWords()
{
	//   special internal fact markers
	Mmember = MakeMeaning(StoreWord("member"));
	Mexclude = MakeMeaning(StoreWord("exclude"));
	Mis = MakeMeaning(StoreWord("is"));
}

void CloseFacts()
{
    free(factBase);
	factBase = 0;
}

void FreeFact(FACT* F)
{ //   most recent facts are always at the top of any xref list. Can only free facts sequentially backwards.
	if (!F->subject) // unindexed fact recording a fact delete that must be undeleted
	{
		if (!F->object) // death of fact fact (verb but no object)
		{
			F = Index2Fact(F->verb);
			F->flags &= -1 ^ FACTDEAD;
		}
		else if (F->flags & ITERATOR_FACT) {;} // holds iterator backtrack
		else // undo a variable assignment fact (verb and object)
		{
			WORDP D = Meaning2Word(F->verb); // the variable
			unsigned int offset = (unsigned int) F->object;
			D->w.userValue =  (offset == 1) ? NULL : (stringBase + offset);
		}
	}
    else // normal indexed fact
	{
		if (!(F->flags & FACTSUBJECT)) SetSubjectHead(F->subject,GetSubjectNext(F)); // dont use nondead
		else SetSubjectHead(Index2Fact(F->subject),GetSubjectNext(F)); // dont use nondead

		if (!(F->flags & FACTVERB)) SetVerbHead(F->verb,GetVerbNext(F)); // dont use nondead
		else  SetVerbHead(Index2Fact(F->verb),GetVerbNext(F)); // dont use nondead

		if (!(F->flags & FACTOBJECT)) SetObjectHead(F->object,GetObjectNext(F)); // dont use nondead
		else SetObjectHead(Index2Fact(F->object),GetObjectNext(F)); // dont use nondead
	}
 }

unsigned int AddFact(unsigned int set, FACT* F) // fact added to factset
{
	unsigned int count = FACTSET_COUNT(set);
	if (++count > MAX_FIND) --count; 
	factSet[set][count] = F;
	SET_FACTSET_COUNT(set,count);
	return count;
}

FACT* SpecialFact(MEANING verb, MEANING object,unsigned int flags)
{
	//   allocate a fact
	if (++factFree == factEnd) 
	{
		--factFree;
		ReportBug("out of fact space at %d",Fact2Index(factFree))
		printf("out of fact space");
		return factFree; // dont return null because we dont want to crash anywhere
	}
	//   init the basics
	memset(factFree,0,sizeof(FACT));
	factFree->verb = verb;
	factFree->object = object;
	factFree->flags = FACTTRANSIENT | FACTDEAD | flags;	// cannot be written or kept
	return factFree;
}

void KillFact(FACT* F)
{
	if (!F || F->flags & FACTDEAD) return; // already dead

	if (trace & TRACE_FACT && CheckTopicTrace()) 
	{
		Log(STDUSERLOG,"Kill: ");
		TraceFact(F);
	}
	F->flags |= FACTDEAD;
	if (planning) SpecialFact(Fact2Index(F),0,0); // save to restore

	// if this fact has facts depending on it, they too must die
	FACT* G = GetSubjectNondeadHead(F);
	while (G)
	{
		KillFact(G);
		G = GetSubjectNondeadNext(G);
	}
	G = GetVerbNondeadHead(F);
	while (G)
	{
		KillFact(G);
		G = GetVerbNondeadNext(G);
	}
	G = GetObjectNondeadHead(F);
	while (G)
	{
		KillFact(G);
		G = GetObjectNondeadNext(G);
	}
}

void ResetFactSystem(FACT* locked)
{
	while (factFree > locked) FreeFact(factFree--); // restore to end of basic facts
	for (unsigned int i = 1; i < MAX_FIND_SETS; ++i)  // clear any factset with contaminated data
	{
		unsigned int limit = FACTSET_COUNT(i);
		for (unsigned int k = 1; k <= limit; ++k)
		{
			if (factSet[i][k] > locked) 
			{
				SET_FACTSET_COUNT(i, 0); // empty all facts sets
				break;
			}
		}
	}
}

FACT* FindFact(MEANING subject, MEANING verb, MEANING object, unsigned int properties)
{
    FACT* F;
	FACT* G;
	if (!subject || !verb || !object) return NULL;
	if (properties & FACTDUPLICATE) 
		return NULL;	// can never find this since we are allowed to duplicate and we do NOT want to share any existing fact

    //   see if  fact already exists. if so, just return it 
	if (properties & FACTSUBJECT)
	{
		F  = Index2Fact(subject);
		G = GetSubjectNondeadHead(F);
		while (G)
		{
			if (G->verb == verb &&  G->object == object && G->flags == properties) return G;
			G  = GetSubjectNondeadNext(G);
		}
		return NULL;
	}
	else if (properties & FACTVERB)
	{
		F  = Index2Fact(verb);
		G = GetVerbNondeadHead(F);
		while (G)
		{
			if (G->subject == subject && G->object == object &&  G->flags == properties) return G;
			G  = GetVerbNondeadNext(G);
		}
		return NULL;
	}   
 	else if (properties & FACTOBJECT)
	{
		F  = Index2Fact(object);
		G = GetObjectNondeadHead(F);
		while (G)
		{
			if (G->subject == subject && G->verb == verb &&  G->flags == properties) return G;
			G  = GetObjectNondeadNext(G);
		}
		return NULL;
	}
  	//   simple FACT* based on dictionary entries
	F = GetSubjectNondeadHead(Meaning2Word(subject));
    while (F)
    {
		if ( F->subject == subject &&  F->verb ==  verb && F->object == object && properties == F->flags)  return F;
		F = GetSubjectNondeadNext(F);
    }
    return NULL;
}

FACT* CreateFact(MEANING subject, MEANING verb, MEANING object, unsigned int properties)
{
	currentFact = NULL; 
	if (!subject || !object || !verb)
	{
		ReportBug("Missing field in fact create at line %d of %s",currentFileLine,currentFilename)
		return NULL;
	}

	//   get correct field values
    WORDP s = (properties & FACTSUBJECT) ? NULL : Meaning2Word(subject);
    WORDP v = (properties & FACTVERB) ? NULL : Meaning2Word(verb);
	WORDP o = (properties & FACTOBJECT) ? NULL : Meaning2Word(object);
	if (s && *s->word == 0)
	{
		ReportBug("bad choice in fact subject")
		return NULL;
	}
	if (v && *v->word == 0)
	{
		ReportBug("bad choice in fact verb")
		return NULL;
	}
	if (o && *o->word == 0)
	{
		ReportBug("bad choice in fact object")
		return NULL;
	}
	// convert any restricted meaning
	MEANING other;
	char* word;
	if (s && (word = s->word) && *word != '"' && strchr(word+1,'~')) // has number or word after it? convert notation
	{
		other = ReadMeaning(word,true,true);
		if (Meaning2Index(other) || GETTYPERESTRICTION(other)) subject = other;
	}
	if (v && (word = v->word) && strchr(word+1,'~')) // has number or word after it? convert notation
	{
		other = ReadMeaning(word,true,true);
		if (Meaning2Index(other) || GETTYPERESTRICTION(other)) verb = other;
	}
	if (o && (word = o->word) &&  strchr(word+1,'~')) // has number or word after it? convert notation
	{
		other = ReadMeaning(word,true,true);
		if (Meaning2Index(other) || GETTYPERESTRICTION(other)) object = other;
	}

	//   insure fact is unique if requested
	currentFact =  (properties & FACTDUPLICATE) ? NULL : FindFact(subject,verb,object,properties); 
	if (trace & TRACE_FACT && currentFact && CheckTopicTrace())  Log(STDUSERLOG," Found %d ", Fact2Index(currentFact));
	if (currentFact) return currentFact;
	currentFact = CreateFastFact(subject,verb,object,properties);
	if (trace & TRACE_FACT && currentFact && CheckTopicTrace())  
	{
		Log(STDUSERLOG," Created %d\r\n", Fact2Index(currentFact));
		Log(STDUSERTABLOG,"");
	}

	return  currentFact;
}

bool ExportFacts(char* name, int set,char* append)
{
	if (set < 0 || set >= MAX_FIND_SETS) return false;
	if ( *name == '"')
	{
		++name;
		size_t len = strlen(name);
		if (name[len-1] == '"') name[len-1] = 0;
	}
	FILE* out = (append && !stricmp(append,"append")) ? FopenUTF8WriteAppend(name) : FopenUTF8Write(name);
	if (!out) return false;

	char word[MAX_WORD_SIZE];
	unsigned int count = FACTSET_COUNT(set);
	for (unsigned int i = 1; i <= count; ++i)
	{
		FACT* F = factSet[set][i];
		if (!F) fprintf(out,"null ");
		else if ( !(F->flags & FACTDEAD))
		{
			unsigned int original = F->flags;
			F->flags &= -1 & FACTTRANSIENT;	// dont pass transient flag out
			fprintf(out,"%s",WriteFact(F,false,word,false,true));
			F->flags = original;
		}
	}

	fclose(out);
	return true;
}

char* EatFact(char* ptr,unsigned int flags,bool attribute)
{
	char word[MAX_WORD_SIZE];
	char word1[MAX_WORD_SIZE];
	char word2[MAX_WORD_SIZE];
	ptr = SkipWhitespace(ptr); // could be user-formateed, dont trust
	FunctionResult result = NOPROBLEM_BIT;
	//   subject
	if (*ptr == '(') //   nested fact
	{
		ptr = EatFact(ptr+1); //   returns after the closing paren
		flags |= FACTSUBJECT;
		sprintf(word,"%d",currentFactIndex() ); //   created OR e found instead of created
	}
	else  ptr = ReadShortCommandArg(ptr,word,result,OUTPUT_FACTREAD); //   subject
	ptr = SkipWhitespace(ptr); // could be user-formateed, dont trust
	if (!ptr) return NULL;
	if (result & ENDCODES) return ptr;
	if (!*word) 
	{
		if (!ptr) return NULL;
		if (compiling) BADSCRIPT("FACT-1 Missing subject for fact create")
		char* end = strchr(ptr,')');
		return (end) ? (end + 2) : ptr; 
	}

	//verb
	if (*ptr == '(') //   nested fact
	{
		ptr = EatFact(ptr+1);
		flags |= FACTVERB;
		sprintf(word1,"%d",currentFactIndex() );
	}
	else  ptr = ReadShortCommandArg(ptr,word1,result,OUTPUT_FACTREAD); //verb
	if (!ptr) return NULL;
	ptr = SkipWhitespace(ptr); // could be user-formateed, dont trust
	if (result & ENDCODES) return ptr;
	if (!*word1) 
	{
		if (!ptr) return NULL;
		if (compiling) BADSCRIPT("FACT-2 Missing verb for fact create")
		char* end = strchr(ptr,')');
		return (end) ? (end + 2) : ptr; 
	}

	//   object
	if (*ptr == '(') //   nested fact
	{
		ptr = EatFact(ptr+1);
		flags |= FACTOBJECT;
		sprintf(word2,"%d",currentFactIndex() );
	}
	else  ptr = ReadShortCommandArg(ptr,word2,result,OUTPUT_FACTREAD); 
	ptr = SkipWhitespace(ptr); // could be user-formateed, dont trust
	if (result & ENDCODES) return ptr;
	if (!*word2) 
	{
		if (compiling) BADSCRIPT("FACT-3 Missing object for fact create - %s",readBuffer)
		if (!ptr) return NULL;
		char* end = strchr(ptr,')');
		return (end) ? (end + 2) : ptr; 
	}
	uint64 fullflags;
	bool bad = false;
	bool response = false;
	char strip[MAX_WORD_SIZE];
	char* at = ReadCompiledWord(ptr,strip);
	bool stripquote = false;
	if (!strnicmp(strip,"STRIP_QUOTE",11)) 
	{
		stripquote = true;
		ptr = at;
	}
	ptr = ReadFlags(ptr,fullflags,bad,response);
	flags |= (unsigned int) fullflags;
	//if (bad) 
	//	return (*ptr) ? (ptr + 2) : ptr; //   returns after the closing ) if there is one - creates no fact

	MEANING subject;
	if ( flags & FACTSUBJECT)
	{
		subject = atoi(word);
		if (!subject) subject = 1; // make a phony fact
	}
	else if (stripquote)
	{
		size_t len = strlen(word);
		if (*word == '"' && word[len-1] == '"') 
		{
			word[len-1] = 0;
			memmove(word,word+1,strlen(word));
		}
		subject =  MakeMeaning(StoreWord(word,AS_IS),0);
	}
	else subject =  MakeMeaning(StoreWord(word,AS_IS),0);
	MEANING verb;
	if ( flags & FACTVERB)
	{
		verb = atoi(word1);
		if (!verb) verb = 1; // make a phony fact
	}
	else if (stripquote)
	{
		size_t len = strlen(word1);
		if (*word1 == '"' && word1[len-1] == '"') 
		{
			word1[len-1] = 0;
			memmove(word1,word1+1,strlen(word1));
		}
		verb =  MakeMeaning(StoreWord(word1,AS_IS),0);
	}
	else verb =  MakeMeaning(StoreWord(word1,AS_IS),0);
	MEANING object;
	if ( flags & FACTOBJECT)
	{
		object = atoi(word2);
		if (!object) object = 1; // make a phony fact
	}
	else if (stripquote)
	{
		size_t len = strlen(word2);
		if (*word2 == '"' && word2[len-1] == '"') 
		{
			word2[len-1] = 0;
			memmove(word2,word2+1,strlen(word2));
		}
		object =  MakeMeaning(StoreWord(word2,AS_IS),0);
	}
	else object =  MakeMeaning(StoreWord(word2,AS_IS),0);

	if (trace & TRACE_OUTPUT && CheckTopicTrace()) Log(STDUSERLOG,"%s %s %s %x) = ",word,word1,word2,flags);

	FACT* F = FindFact(subject,verb,object,flags);
	if (!attribute || (F && object == F->object)) {;}  // not making an attribute or already made
	else // remove any facts with same subject and verb, UNlESS part of some other fact
	{
		if (flags & FACTSUBJECT) F = GetSubjectNondeadHead(Index2Fact(subject));
		else F = GetSubjectNondeadHead(subject);
		while (F)
		{
			if (F->subject == subject && F->verb == verb) 
			{
				if (!(F->flags & FACTATTRIBUTE)) // this is a script failure. Should ONLY be an attribute
				{
					char word[MAX_WORD_SIZE];
					WriteFact(F,false,word,false,true);
					Log(STDUSERLOG,"Fact created is not an attribute. There already exists %s",word); 
					printf("Fact created is not an attribute. There already exists %s",word); 
					currentFact = F;
					return (*ptr) ? (ptr + 2) : ptr; 
				}
				KillFact(F); 
			}
			F = GetSubjectNondeadNext(F);
		}
	}

	F = CreateFact(subject,verb,object,flags);
	if (attribute) 	F->flags |= FACTATTRIBUTE;
	return (*ptr) ? (ptr + 2) : ptr; //   returns after the closing ) if there is one
}

bool ImportFacts(char* name, char* set, char* erase, char* transient)
{
	int store = GetSetID(set);
	if (store == ILLEGAL_FACTSET) return false;
	SET_FACTSET_COUNT(store,0);
	if ( *name == '"')
	{
		++name;
		size_t len = strlen(name);
		if (name[len-1] == '"') name[len-1] = 0;
	}
	FILE* in = FopenReadWritten(name);
	if (!in) return false;
	unsigned int flags = 0;
	if (!stricmp(erase,"transient") || !stricmp(transient,"transient")) flags |= FACTTRANSIENT; // make facts transient
	while (ReadALine(readBuffer, in) >= 0)
    {
        if (*readBuffer == 0 || *readBuffer == '#') continue; //   empty or comment
		char word[MAX_WORD_SIZE];
		char* ptr = ReadCompiledWord(readBuffer,word);
		if (!stricmp(word,"null")) AddFact(store,NULL);
		else if (*word == '(')
		{
			EatFact(ptr,flags);
			AddFact(store,currentFact);
		}
	}
	fclose(in);
	if (!stricmp(erase,"erase") || !stricmp(transient,"erase")) remove(name); // erase file after reading
	if (trace & TRACE_OUTPUT && CheckTopicTrace()) Log(STDUSERLOG,"[%d] => ",FACTSET_COUNT(store));
	return true;
}

void WriteFacts(FILE* out,FACT* F) //   write out from here to end
{ 
	char word[MAX_WORD_SIZE];
	if (!out) return;
    while (++F <= factFree) 
	{
		if (!(F->flags & (FACTTRANSIENT|FACTDEAD))) fprintf(out,"%s",WriteFact(F,true,word,false,true));
	}
    fclose(out);
}

void WriteBinaryFacts(FILE* out,FACT* F) //   write out from here to end
{ 
	if (!out) return;
    while (++F <= factFree) 
	{
		unsigned int index = Fact2Index(F);
		if (F->flags & FACTSUBJECT && F->subject >= index) ReportBug("subject fact index too high")
		if (F->flags & FACTVERB && F->verb >= index) ReportBug("verb fact index too high")
		if (F->flags & FACTOBJECT && F->object >= index) ReportBug("object fact index too high")
		Write32(F->subject,out);
		Write32(F->verb,out);
		Write32(F->object,out);
		Write32(F->flags,out);
	}
    fclose(out);
}
	
FACT* CreateFastFact(MEANING subject, MEANING verb, MEANING object, unsigned int properties)
{
	//   get correct field values
	WORDP s = (properties & FACTSUBJECT) ? NULL : Meaning2Word(subject);
	WORDP v = (properties & FACTVERB) ? NULL : Meaning2Word(verb);
	WORDP o = (properties & FACTOBJECT) ? NULL : Meaning2Word(object);
	if (properties & FACTDEAD) // except for special internal system facts, this shouldnt happen - unless user intends it
	{
		int xx = 0;
	}
	// DICTIONARY should never be build with any but simple meanings and Mis
	// No fact meaning should ever have a synset marker on it. And member facts may have type restrictions on them
	if (s && ((subject & (-1 ^ SIMPLEMEANING) && verb == Mis) || subject&SYNSET_MARKER))
	{
		int xx = 0;
	}
	if (o && ((object & (-1 ^ SIMPLEMEANING) && verb == Mis)|| subject&SYNSET_MARKER))
	{
		int xx = 0;
	}

	//   allocate a fact
	FACT* F;
	if (++factFree == factEnd) 
	{
		--factFree;
		ReportBug("out of fact space at %d",Fact2Index(factFree))
		printf("out of fact space");
		return NULL;
	}
	currentFact = factFree;

	//   init the basics
	memset(currentFact,0,sizeof(FACT));
	currentFact->subject = subject;
	currentFact->verb = verb; 
	currentFact->object = object;
	currentFact->flags = properties;

	//   crossreference
	if (s) 
	{
		SetSubjectNext(currentFact,GetSubjectHead(subject)); // dont use nondead
		SetSubjectHead(subject,currentFact);
	}
	else 
	{
		F = Index2Fact(currentFact->subject);
		if (F)
		{	
			SetSubjectNext(currentFact,GetSubjectHead(F));   // dont use nondead
			SetSubjectHead(F,currentFact);
		}
		else
		{
			--factFree;
			return NULL;
		}
	}
	if (v) 
	{
		SetVerbNext(currentFact, GetVerbHead(verb));  // dont use nondead
		SetVerbHead(verb,currentFact);
	}
	else 
	{
		F = Index2Fact(currentFact->verb);
		if (F)
		{
			SetVerbNext(currentFact,GetVerbHead(F));  // dont use nondead
			SetVerbHead(F,currentFact);
		}
		else
		{
			--factFree;
			return NULL;
		}
	}
	if (o) 
	{
		SetObjectNext(currentFact, GetObjectHead(object));  // dont use nondead
		SetObjectHead(object,currentFact);
	}
	else
	{
		F = Index2Fact(currentFact->object);
		if (F)
		{
			SetObjectNext(currentFact,GetObjectNext(F));   // dont use nondead
			SetObjectHead(F,currentFact);
		}
		else
		{
			--factFree;
			return NULL;
		}
	}

	if (planning) currentFact->flags |= FACTTRANSIENT;

	if (trace & TRACE_FACT && CheckTopicTrace())
	{
		char* buffer = AllocateBuffer(); // fact might be big, cant use mere WORD_SIZE
		buffer = WriteFact(currentFact,false,buffer,true,false);
		Log(STDUSERLOG,"create %s",buffer);
		FreeBuffer();
	}	
	return currentFact;
}

bool ReadBinaryFacts(FILE* in) //   read binary facts
{ 
	if (!in) return false;
	while (ALWAYS)
	{
		MEANING subject = Read32(in);
		if (!subject) break;
 		MEANING verb = Read32(in);
 		MEANING object = Read32(in);
  		unsigned int properties = Read32(in);
		CreateFastFact(subject,verb,object,properties);
	}
    fclose(in);
	return true;
}

static char* WriteField(MEANING T, uint64 flags,char* buffer,bool ignoreDead)
{
	// a field is either a contiguous mass of non-blank tokens, or a user string "xxx" or an internal string `xxx`  (internal removes its ends, user doesnt)
    if (flags ) //   fact reference
    {
		FACT* G = Index2Fact(T);
		if (!*WriteFact(G,false,buffer,ignoreDead)) 
		{
			*buffer = 0;
			return buffer;
		}
		buffer += strlen(buffer);
    }
	else if (!T) 
	{
		ReportBug("Missing fact field")
		*buffer++ = '?';
	}
    else 
	{
		WORDP D = Meaning2Word(T);
		if (D->internalBits & (INTERNAL_MARK|DELETED_MARK) && !ignoreDead) // a deleted field
		{
			*buffer = 0;
			return buffer; //   cancels print
		}
		char* answer = WriteMeaning(T,true);
		bool embedded = *answer != '"' && (strchr(answer,' ') != NULL || strchr(answer,'(') != NULL) ; // does this need protection? blanks or function call maybe
		if (embedded) sprintf(buffer,"`%s`",answer); // has blanks, use internal string notation
		else strcpy(buffer,answer); // use normal notation

		buffer += strlen(buffer);
	}
	*buffer++ = ' ';
	*buffer = 0;
	return buffer;
}

char* WriteFact(FACT* F,bool comments,char* buffer,bool ignoreDead,bool eol)
{ //   if fact is junk, return the null string
	char* start = buffer;
	*buffer = 0;
	if (!F || !F->subject) return start; // never write special facts out
	if (F->flags & FACTDEAD) // except for user display THIS shouldnt happen to real fact writes
	{
		if (ignoreDead)
		{
			strcpy(buffer,"DEAD ");
			buffer += strlen(buffer);
		}
		else 
			return ""; // illegal - only happens with facts (nondead) that refer to dead facts?
	}

	//   fact opener
	*buffer++ = '(';
	*buffer++ = ' ';

	//   do subject
	char* base = buffer;
 	buffer = WriteField(F->subject,F->flags & FACTSUBJECT,buffer,ignoreDead);
	if (base == buffer ) 
	{
		*start = 0;
		return start; //    word itself was removed from dictionary
	}
	base = buffer;
	buffer = WriteField(F->verb,F->flags & FACTVERB,buffer,ignoreDead);
	if (base == buffer ) 
	{
		*start = 0;
		return start; //    word itself was removed from dictionary
	}

	base = buffer;
	buffer = WriteField(F->object,F->flags & FACTOBJECT,buffer,ignoreDead);
	if (base == buffer ) 
	{
		*start = 0;
		return start; //    word itself was removed from dictionary
	}

	//   add properties
    if (F->flags)  
	{
		sprintf(buffer,"0x%x ",F->flags & (-1 ^ (MARKED_FACT|MARKED_FACT2) ));  // dont show markers
		buffer += strlen(buffer);
	}

	//   close fact
	*buffer++ = ')';
	*buffer = 0;
	if (eol) strcat(buffer,"\r\n");
	return start;
}

char* ReadField(char* ptr,char* field,char fieldkind, unsigned int& flags)
{
	if (*ptr == '(')
	{
		FACT* G = ReadFact(ptr);
		if (fieldkind == 's') flags |= FACTSUBJECT;
		else if (fieldkind == 'v') flags |= FACTVERB;
		else if (fieldkind == 'o') flags |= FACTOBJECT;
		if (!G)
		{
			ReportBug("Missing fact field")
			return NULL;
		}
		sprintf(field,"%d",Fact2Index(G)); 
	}
	else if (*ptr == ENDUNIT) // internal string token (fact read)
	{
		char* end = strchr(ptr+1,ENDUNIT); // find corresponding end
		*end = 0;
		strcpy(field,ptr+1);
		return end+2; // point AFTER the space after the `
	}
    else 
	{
		ptr = ReadCompiledWord(ptr,field); 
	}
	if (field[0] == '~') MakeLowerCase(field);	// all concepts/topics are lower case
	return ptr; //   return at new token
}

FACT* ReadFact(char* &ptr)
{
	char word[MAX_WORD_SIZE];
    MEANING subject = 0;
	MEANING verb = 0;
    MEANING object = 0;
 	//   fact may start indented.  Will start with (or be 0 for a null fact
    ptr = ReadCompiledWord(ptr,word);
    if (*word == '0') return 0; 
	unsigned int flags = 0;

	char subjectname[MAX_WORD_SIZE];
	ptr = ReadField(ptr,subjectname,'s',flags);
    char verbname[MAX_WORD_SIZE];
	ptr = ReadField(ptr,verbname,'v',flags);
    char objectname[MAX_WORD_SIZE];
	ptr = ReadField(ptr,objectname,'o',flags);

	if (!ptr) return NULL;
	
    //   handle the flags on the fact
    uint64 properties = 0;
	bool bad = false;
	bool response = false;
    if (!*ptr || *ptr == ')' ); // end of fact
	else ptr = ReadFlags(ptr,properties,bad,response);
	flags |= (unsigned int) properties;

    if (flags & FACTSUBJECT) subject = (MEANING) atoi(subjectname);
    else  subject = ReadMeaning(subjectname,true,true);
	if (flags & FACTVERB) verb = (MEANING) atoi(verbname);
	else  verb = ReadMeaning(verbname,true,true);
	if (flags & FACTOBJECT) object = (MEANING) atoi(objectname);
	else  object = ReadMeaning(objectname,true,true);

    FACT* F = FindFact(subject, verb,object,flags);
    if (!F)   F = CreateFact(subject,verb,object,flags); 
	if (*ptr == ')') ++ptr;	// skip over ending )
	ptr = SkipWhitespace(ptr);
    return F;
}

void ReadFacts(const char* name,uint64 build,bool user) //   a facts file may have dictionary augmentations and variable also
{
    FILE* in = (user) ? FopenReadWritten(name) : FopenReadOnly(name); //  TOPIC fact/DICT files
    if (!in) return;
	StartFile(name);
	char word[MAX_WORD_SIZE];
    while (ReadALine(readBuffer, in) >= 0)
    {
		char* ptr = ReadCompiledWord(readBuffer,word);
        if (*word == 0 || *word == '#'); //   empty or comment
		else if (*word == '+') //   dictionary entry
		{
			if (!stricmp(word,"+query")) // defining a private query
			{
				ptr = ReadCompiledWord(ptr,word); // name
				WORDP D = StoreWord(word);
				AddInternalFlag(D,(unsigned int)(QUERY_KIND|build));
				ReadCompiledWord(ptr,word);
				ptr = strchr(word+1,'"');
				*ptr = 0;
				D->w.userValue = AllocateString(word+1);
				continue;
			}

			char word[MAX_WORD_SIZE];
			char* at = ReadCompiledWord(readBuffer+2,word); //   start at valid token past space
			WORDP D = FindWord(word,0,PRIMARY_CASE_ALLOWED);
			if (!D)
			{
				D = StoreWord(word);
				AddInternalFlag(D,(unsigned int)build);
			}
			bool sign = false;
			if (*at == '-' && IsDigit(at[1])) 
			{
				sign = true;
				++at;
			}
			if (IsDigit(*at)) 
			{
				int64 n;
				ReadInt64(at,n);
				AddProperty(D,(uint64) n);// rename value
				AddInternalFlag(D,RENAMED);
				if (sign) AddSystemFlag(D,CONSTANT_IS_NEGATIVE);
			}
			else ReadDictionaryFlags(D,at);
		}
		else if (*word == '$') // variable
		{
			ReportBug("Bad fact file user var assignment")
		}
        else 
		{
			char* ptr = readBuffer;
			ReadFact(ptr); // will write on top of ptr... must not be readBuffer variable
		}
    }
   fclose(in);
}

void SortFacts(char* set, int alpha) //   sort low to high ^sort(@1subject) which field we sort on (subject or verb or object)
{
    int n = GetSetID(set);
	if (n == ILLEGAL_FACTSET) return;
	char kind = GetLowercaseData(*GetSetType(set));
	if (!kind) kind = 's';
    int i;
	int size = FACTSET_COUNT(n);
	float floatValues[MAX_FIND+1];
	char* wordValues[MAX_FIND+1];

	// load the actual array to compare
    for (i = 1; i <= size; ++i)
    {
        FACT* F =  factSet[n][i];
		char* word;
		if (kind == 's') word = Meaning2Word(F->subject)->word; 
		else if (kind == 'v') word = Meaning2Word(F->verb)->word; 
		else word = Meaning2Word(F->object)->word;
		if (alpha == 1) wordValues[i] = word;
		else if (alpha == 0) floatValues[i] = (float) atof(word);
    }

	// do bubble sort 
    bool swap = true;
    while (swap)
    {
        swap = false;
        for (i = 1; i <= size-1; ++i) 
        {
			char* word = wordValues[i];
            float tmp = floatValues[i];
			if (alpha == 1 && strcmp(word,wordValues[i+1]) > 0) {;}
			else if (alpha == 2 && (char*)factSet[n] > (char*)factSet[n+1]) {;}
			else if (alpha == 0 && tmp > floatValues[i+1]) {;}
			else continue;
	        wordValues[i] = wordValues[i+1];
            wordValues[i+1] = word;
            floatValues[i] = floatValues[i+1];
            floatValues[i+1] = tmp;
            FACT* F = factSet[n][i];
			factSet[n][i] = factSet[n][i+1];
			factSet[n][i+1] = F;
			swap = true;
		}
        --size;
    }
}
