// markSystem.cpp - annotates the dictionary with what words/concepts are active in the current sentence

#include "common.h"

#ifdef INFORMATION

For every word in a sentence, the word knows it can be found somewhere in the sentence, and there is a 64-bit field of where it can be found in that sentence.
The field is in a hashmap and NOT in the dictionary word, where it would take up excessive memory.

Adjectives occur before nouns EXCEPT:
	1. object complement (with some special verbs)
	2. adjective participle (sometimes before and sometimes after)

In a pattern, an author can request:
	1. a simple word like bottle
	2. a form of a simple word non-canonicalized like bottled or apostrophe bottle
	3. a WordNet concept like bottle~1 
	4. a set like ~dead or :dead

For #1 "bottle", the system should chase all upward all sets of the word itself, and all
WordNet parents of the synset it belongs to and all sets those are in. 

Marking should be done for the original and canonical forms of the word.

For #2 "bottled", the system should only chase the original form.

For #3 "bottle~1", this means all words BELOW this in the wordnet hierarchy not including the word
"bottle" itself. This, in turn, means all words below the particular synset head it corresponds to
and so instead becomes a reference to the synset head: "0173335n" or some such.

For #4 "~dead", this means all words encompassed by the set ~dead, not including the word ~dead.

So each word in an input sentence is scanned for marking. 
the actual word gets to see what sets it is in directly. 
Thereafter the system chases up the synset hierarchy fanning out to sets marked from synset nodes.

#endif
static MEANING tempList = 0;
static MEANING freeMark = 0;
unsigned int maxRefSentence = MAX_XREF_SENTENCE  * 2;

// mark debug tracing
bool showMark = false;
static unsigned int markLength = 0; // prevent long lines in mark listing trace
#define MARK_LINE_LIMIT 80

char unmarked[MAX_SENTENCE_LENGTH]; // can completely disable a word from mark recognition
unsigned int tempc = 0;
#ifdef JUNK
Temps (D->temps) are extra data slots attached to words that only last during the volley. The 4 temps are:
	FACTBACK,  USEDTEMPSLIST,  TRIEDBITS, WORDVALUE 
TRIEDBITS is cleared and reallocated every sentence, not every volley.

Tallying - ^tally() - uses WORDVALUE to add a counter to words. Only happens from scripting.
USEDTEMPSLIST is a threaded list ptr for all allocated temps. It allows clearing of the triedbits while leaving the temps intact
TRIEDBITS is 64 bits defining meaning used after which  is used for marking words in current prepared input.
	Its a string of 32 entries (each entry a start and end index) where the word can be found.

#endif

unsigned int concepts[MAX_SENTENCE_LENGTH];  // concept chains per word
unsigned int topics[MAX_SENTENCE_LENGTH];  // topics chains per word

MEANING* GetTemps(WORDP D)
{
	if (D->temps) return (MEANING*) Index2String(D->temps); // we have an active temp (valid for duration of VOLLEY)

	MEANING* temps = (MEANING*) AllocateString(NULL,4, sizeof(MEANING),true);  
	if (!temps) return NULL;
	D->temps = String2Index((char*)temps);
	temps[USEDTEMPSLIST] = tempList;		// link back - we have a list threaded thru the temps triples (clearable at end of volley)
	tempList = MakeMeaning(D);  
	++tempc; // tally of allocated temps
	return temps;
}
	
static void ClearTemps(WORDP D, uint64 junk)
{
	D->temps = 0;
}

void AllocateWhereInSentence(WORDP D)
{
	MEANING* set = GetTemps(D); // allocates if need be
	if (!set) return;

	uint64* data;
	if (freeMark) // reuse free list
	{
		data = (uint64*) Index2String(freeMark);
		freeMark = *(MEANING*)data;
	}
	else // get where chunk
	{
		data  = (uint64*) AllocateString(NULL, sizeof(uint64) + maxRefSentence,1,false); // 64 bytes (16 words) + 64 bits (2 words) = 18 words  BUG?
		if (!data) return;
	}
	*data = 0;
	memset(data+1,0xff,maxRefSentence);
	// store where in the temps data
	int index = String2Index((char*) data);
	set[TRIEDBITS] = index; // 64 bits to enable
}

unsigned char* GetWhereInSentence(WORDP D) 
{
	MEANING* set =  (MEANING*)Index2String(D->temps); // 438707  ~about_you
	if (!set) return NULL;
	unsigned int index =  set[TRIEDBITS]; // string index of where information, skip over 4 byte tried field
	if (!index) return NULL;
	return ((unsigned char*) Index2String(index)) + 8; 
}

void ClearTemps() // release temps that may exist on base dictionary words 
{
	memset(concepts,0, sizeof(unsigned int) * MAX_SENTENCE_LENGTH); // precautionary, not required in theory
	memset(topics,0, sizeof(unsigned int) * MAX_SENTENCE_LENGTH); // precautionary, not required in theory
	while (tempList && tempc--) // list of words that have templist attached (some have where info and some may have factback info) allowing us to clear triedbits
	{
		WORDP D = Meaning2Word(tempList);
		MEANING* tempset = (MEANING*) Index2String(D->temps); // the temp set
		D->temps = 0;
		if (!tempset) break; // bug not expected
		tempList = tempset[USEDTEMPSLIST]; // next one in list to consider
	}

	if (tempList) // we failed to properly release the tried bits, instead release all temps as an emergency
	{
		ReportBug("ClearTemps didnt finish\r\n");
		WalkDictionary(ClearTemps,0); // drop all transient data completely
		tempList = tempc =  0;
	}
	freeMark = 0;
}

void ClearWhereInSentence() // erases  the WHEREINSENTENCE and the TRIEDBITS 
{
	memset(concepts,0, sizeof(unsigned int) * MAX_SENTENCE_LENGTH);
	memset(topics,0, sizeof(unsigned int) * MAX_SENTENCE_LENGTH);
	
	MEANING xlist = tempList;
	unsigned int x = tempc; // safety limit in case of bugs
	while (xlist && x--) // list of words that have templist attached (some have where info and some may have factback info) allowing us to clear triedbits
	{
		WORDP D = Meaning2Word(xlist);
		MEANING* tempset = (MEANING*) Index2String(D->temps); // the temp set 
		if (!tempset) break; // bug

		xlist = tempset[USEDTEMPSLIST]; // next one in list to consider

		unsigned int datum = tempset[TRIEDBITS];
		MEANING* data = (MEANING*)Index2String(datum);
		if (data) // save them for reuse
		{
			*data = freeMark;
			freeMark = datum;
		}
		tempset[TRIEDBITS] = 0; 
	}

	if (xlist) // we failed to properly release the tried bits, instead release all temps as an emergency
	{
		ReportBug("ClearWhere didnt finish\r\n");
		WalkDictionary(ClearTemps,0); // drop all transient data completely
		tempList = tempc =  0;
		freeMark = 0;
	}
}

void SetTried(WORDP D,uint64 bits)
{
	MEANING* list = GetTemps(D); // allocate if needed
	if (!list) return;
	uint64*  data = (uint64*) Index2String(list[TRIEDBITS]);
	if (!data) // allocate a new one both where and bits
	{
		AllocateWhereInSentence(D);
		data = (uint64*) Index2String(list[TRIEDBITS]);
		if (!data) return;
	}
	*data = bits;
}

uint64 GetTried(WORDP D)
{
	MEANING* set =  (MEANING*)Index2String(D->temps);
	if (!set) return 0;
	uint64* data = (uint64*) Index2String(set[TRIEDBITS]); 
	return (!data) ? 0 : *data;
}

void RemoveMatchValue(WORDP D, unsigned int position)
{
	unsigned char* data = GetWhereInSentence(D);
	if (!data) return;
	for (unsigned int i = 0; i < maxRefSentence; i += 2)
	{
		if (data[i] == position) 
		{
			if (trace) Log(STDUSERLOG,"unmark %s @word %d  ",D->word,position);
			memmove(data+i,data+i+2,(maxRefSentence - i - 2)); 
			break;
		}
	}
}

void MarkWordHit(WORDP D, unsigned int start,unsigned int end)
{	//   keep closest to start at bottom, when run out, drop later ones 
    if (!D || !D->word) return;
	if (end > wordCount) end = wordCount;   
	if (start > wordCount) 
	{
		ReportBug("save position is too big")
		return;
	}
	// track the actual sets done matching start word location (good for verbs, not so good for nouns)
	if (*D->word == '~')
	{
		if (!(D->internalBits & TOPIC))
		{
			unsigned int* entry = (unsigned int*) AllocateString(NULL,2, sizeof(MEANING),false); // ref and link
			entry[1] = concepts[start];
			concepts[start] = String2Index((char*) entry);
			entry[0] = MakeMeaning(D);
		}
		else {
			unsigned int* entry = (unsigned int*) AllocateString(NULL,2,sizeof(MEANING),false); // ref and link
			entry[1] = topics[start];
			topics[start] = String2Index((char*) entry);
			entry[0] = MakeMeaning(D);
		}
	}
	// diff < 0 means peering INSIDE a multiword token before last word
	// we label END as the word before it (so we can still see next word) and START as the actual multiword token
 	unsigned char* data = GetWhereInSentence(D);
    if (!data) 
	{
		AllocateWhereInSentence(D);
		data = GetWhereInSentence(D);
	}
	if (!data) return;

	bool added = false;
	for (unsigned int i = 0; i < maxRefSentence; i += 2)
	{
		if (data[i] == 0 || (data[i] > wordCount && data[i] != 0xff)) // CANNOT BE TRUE
		{
			static bool did = false;
			if (!did) ReportBug("illegal whereref for %s at %d\r\n",D->word,volleyCount);
			did = true;
			return;
		}
		if (data[i] == start) 
		{
			if (end > data[i+1])
			{
				data[i+1] = (unsigned char)end; 
				added = true;
			}
			break; // we are already here
		}
		else if (data[i] > start) 
		{
			memmove(data+i+2,data+i,maxRefSentence - i - 2);
			data[i] = (unsigned char)start;
			data[i+1] = (unsigned char)end;
			added = true;
			break; // data inserted here
		}
	}

	if ( ( trace & (TRACE_PREPARE|TRACE_HIERARCHY)  || prepareMode == PREPARE_MODE || showMark) && added)  
	{
		markLength += D->length;
		if (markLength > MARK_LINE_LIMIT)
		{
			markLength = 0;
			Log(STDUSERLOG,"\r\n");
			Log(STDUSERTABLOG,"");
		}
		Log((showMark) ? ECHOSTDUSERLOG : STDUSERLOG,(D->internalBits & TOPIC) ? " +T%s " : " +%s",D->word);
		if (start != end) Log((showMark) ? ECHOSTDUSERLOG : STDUSERLOG,"(%d-%d)",start,end);
	}
}

unsigned int GetIthSpot(WORDP D,unsigned int i, unsigned int& start, unsigned int& end)
{
    if (!D) return 0; //   not in sentence
	unsigned char* data = GetWhereInSentence(D);
	if (!data) return 0;
	i *= 2;
	if (i >= maxRefSentence) return 0; // at end
	start = data[i];
	if (start == 0xff) return 0;
	end = data[i+1];
	if (end > wordCount)
	{
		static bool did = false;
		if (!did) ReportBug("Getith out of range %s at %d\r\n",D->word,volleyCount);
		did = true;
	}
    return start;
}

unsigned int GetNextSpot(WORDP D,int start,unsigned int &startPosition,unsigned int& endPosition, bool reverse)
{//   spot can be 1-31,  range can be 0-7 -- 7 means its a string, set last marker back before start so can rescan
	//   BUG - we should note if match is literal or canonical, so can handle that easily during match eg
	//   '~shapes matches square but not squares (whereas currently literal fails because it is not ~shapes
    if (!D) return 0; //   not in sentence
	unsigned char* data = GetWhereInSentence(D);
	if (!data) return 0;
	
	unsigned int i;
	startPosition = 0;
	for (i = 0; i < maxRefSentence; i += 2)
	{
		unsigned char at = data[i];
		unsigned char end = data[i+1];
		if ((at > wordCount && at != 0xff) || (end > wordCount && end != 0xff))
		{
			static bool did = false;
			if (!did) ReportBug("Getith out of range %s at %d\r\n",D->word,volleyCount);
			did = true;
			return 0;	// CANNOT BE TRUE
		}
		if (unmarked[at]){;}
		else if (reverse)
		{
			if (at < start) 
			{
				startPosition = at;
				endPosition = end;
			}
			else return startPosition;
		}
		else if (at > start)
		{
			if (at == 0xff) return 0; // end of data going forward
			startPosition = at;
			endPosition = end;
			return startPosition;
		}
	}
    return 0;
}

static int MarkSetPath(MEANING M, unsigned int start, unsigned  int end, unsigned int depth, bool canonical) //   walks set hierarchy
{//   travels up concept/class sets only, though might start out on a synset node or a regular word
	unsigned int flags = GETTYPERESTRICTION(M);
	if (!flags) flags = ESSENTIAL_FLAGS; // what POS we allow from Meaning
	WORDP D = Meaning2Word(M);
	unsigned int index = Meaning2Index(M); // always 0 for a synset or set
	// check for any repeated accesses of this synset or set or word
	uint64 offset = 1 << index;
	uint64 tried = GetTried(D);
 	if (D->inferMark == inferMark) // been thru this word recently
	{
		if (*D->word == '~') return -1;	// branch is marked
		if (tried & offset)	return -1;	// word synset done this branch already
	}
	else //   first time accessing, note recency and clear tried bits
	{
		D->inferMark = inferMark;
		if (*D->word != '~') 
		{
			SetTried(D,0);
			tried = 0;
		}
	}
 	if (*D->word != '~') SetTried(D,tried |offset);
	int result = NOPROBLEM_BIT;
	FACT* F = GetSubjectNondeadHead(D); 
	while (F)
	{
		if (F->verb == Mmember) // ~concept members and word equivalent
		{
			char word[MAX_WORD_SIZE];
			char* fact;
			if (trace == TRACE_HIERARCHY)  
			{
				int factx = Fact2Index(F);
				fact = WriteFact(F,false,word); // just so we can see it
				unsigned int hold = globalDepth;
				globalDepth = depth;
				Log(STDUSERTABLOG,"%s   ",fact); // \r\n
				globalDepth = hold;
			}
			// if subject has type restriction, it must pass
			unsigned int restrict = GETTYPERESTRICTION(F->subject );
			if (!restrict && index) restrict = GETTYPERESTRICTION(GetMeaning(D,index)); // new (may be unneeded)
 
			if (restrict && !(restrict & flags)) {;} // type restriction in effect for this concept member
			else if (canonical && F->flags & ORIGINAL_ONLY) {;} // incoming is not original words and must be

			//   index meaning restriction (0 means all)
			else if (index == Meaning2Index(F->subject)) // match generic or exact subject 
			{
				bool mark = true;
				// test for word not included in set
				WORDP E = Meaning2Word(F->object); // this is a topic or concept
				if (index)
				{
					WORDP D = Meaning2Word(F->subject);
					MEANING M = GetMeaning(D,index);
					unsigned int pos = GETTYPERESTRICTION(M);
					if (!(flags & pos)) 
						mark = false; // we cannot be that meaning because type is wrong
				}

				if (!mark){;}
				else if (E->inferMark == inferMark && *E->word == '~') mark = false; // already marked this set
				else if (E->internalBits & HAS_EXCLUDE) // set has some members it does not want
				{
					FACT* G = GetObjectNondeadHead(E);
					while (G)
					{
						if (G->verb == Mexclude) // see if this is marked for this position, if so, DONT trigger topic
						{
							WORDP S = Meaning2Word(G->subject);
							unsigned int startPosition,endPosition;
							if (GetNextSpot(S,start-1,startPosition,endPosition) && startPosition == start && endPosition == end)
							{
								mark = false;
								break;
							}
						}
						G = GetObjectNondeadNext(G);
					}
				}

				if (mark)
				{
					MarkWordHit(E,start,end);
					if (MarkSetPath(F->object,start,end,depth+1,canonical) != -1) result = 1; // someone marked
				}
			}
			else if (!index && Meaning2Index(F->subject)) // we are all meanings (limited by pos use) and he is a specific meaning
			{
				unsigned int which = Meaning2Index(F->subject);
				WORDP H = Meaning2Word(F->subject);
				MEANING M = GetMeaning(H,which);
				unsigned int pos = GETTYPERESTRICTION(M);
				if (flags & pos) //  && start == end   wont work if spanning multiple words revised due to "to fish" noun infinitive
				{
					MarkWordHit(Meaning2Word(F->object),start,end);
					if (MarkSetPath(F->object,start,end,depth+1,canonical) != -1) result = 1; // someone marked
				}
			}
		}
		F = GetSubjectNondeadNext(F);
	}
	return result;
}

static void RiseUp(MEANING M,unsigned int start, unsigned int end,unsigned int depth,bool canonical) //   walk wordnet hierarchy above a synset node
{	// M is always a synset head 
	M &= -1 ^ SYNSET_MARKER;
	unsigned int index = Meaning2Index(M);
	WORDP D = Meaning2Word(M);
	WORDP X;
	char word[MAX_WORD_SIZE];
	sprintf(word,"%s~%d",D->word,index);
	X = FindWord(word,0,PRIMARY_CASE_ALLOWED);
	if (X) 	MarkWordHit(X,start,end); // direct reference in a pattern

	// now spread and rise up
	if (MarkSetPath(M,start,end,depth,canonical) == -1) return; // did the path
	FACT* F = GetSubjectNondeadHead(D); 
	while (F)
	{
		if (F->verb == Mis && (index == 0 || F->subject == M)) RiseUp(F->object,start,end,depth+1,canonical); // allowed up
		F = GetSubjectNondeadNext(F);
	}
}

static void MarkSequenceTitleFacts(MEANING M, unsigned int start, unsigned int end,bool canonical) // title phrases in sentence
{
    if (!M) return;
	WORDP D = Meaning2Word(M);
	if (D->properties & NOUN_TITLE_OF_WORK && canonical) return; // accidental canonical match. not intended

	if (D->properties & PART_OF_SPEECH) // mark pos data
	{
		uint64 bit = START_BIT;
		for (int j = 63; j >= 0; --j)
		{
			if (D->properties & bit) MarkFacts(posMeanings[j],start,end,canonical,(D->properties & NOUN_TITLE_OF_WORK && !canonical) ? false : true); // treat original title as a full normal word
			bit >>= 1;
		}
	}

	MarkFacts(M,start,end,canonical,true);
}

void MarkFacts(MEANING M,unsigned int start, unsigned int end,bool canonical,bool sequence) 
{ // M is always a word or sequence from a sentence

    if (!M) return;
	WORDP D = Meaning2Word(M);
	if (!sequence || D->properties & (PART_OF_SPEECH|NOUN_TITLE_OF_WORK|NOUN_HUMAN) || D->systemFlags & PATTERN_WORD || D->internalBits &  CONCEPT) MarkWordHit(D,start,end); // if we want the synset marked, RiseUp will do it.
	int result = MarkSetPath(M,start,end,0,canonical); // generic membership of this word all the way to top
	if (sequence && result == 1) MarkWordHit(D,start,end); // if we want the synset marked, RiseUp will do it.
	WORDP X;
	char word[MAX_WORD_SIZE];
	bool test = true;
	if (*D->word == '~') test = false;// not a word
	unsigned int restrict = GETTYPERESTRICTION(M);
	if (test && (restrict & NOUN) && !(posValues[start] & NOUN_INFINITIVE) ) // BUG- this wont work up the ontology, only at the root of what the script requests - doesnt accept "I like to *fish" as a noun, so wont refer to the animal
	{
		sprintf(word,"%s~n",D->word);
		X = FindWord(word,0,PRIMARY_CASE_ALLOWED);
		if (X) 	MarkWordHit(X,start,end); // direct reference in a pattern
	}
	if (test && ((restrict & VERB) || posValues[start] & NOUN_INFINITIVE))// accepts "I like to *swim as not a verb meaning" 
	{
		sprintf(word,"%s~v",D->word);
		X = FindWord(word,0,PRIMARY_CASE_ALLOWED);
		if (X) 	MarkWordHit(X,start,end); // direct reference in a pattern
	}
	if (test && (restrict & ADJECTIVE))
	{
		sprintf(word,"%s~a",D->word);
		X = FindWord(word,0,PRIMARY_CASE_ALLOWED);
		if (X) 	MarkWordHit(X,start,end); // direct reference in a pattern
	}
	if (test && restrict & ADVERB)
	{
		sprintf(word,"%s~b",D->word);
		X = FindWord(word,0,PRIMARY_CASE_ALLOWED);
		if (X) 	MarkWordHit(X,start,end); // direct reference in a pattern
	}
	if (test && restrict & PREPOSITION)
	{
		sprintf(word,"%s~p",D->word);
		X = FindWord(word,0,PRIMARY_CASE_ALLOWED);
		if (X) 	MarkWordHit(X,start,end); // direct reference in a pattern
	}

	//   now follow out the allowed synset hierarchies 
	unsigned int index = Meaning2Index(M);
	unsigned int size = GetMeaningCount(D);
	unsigned int flags = GETTYPERESTRICTION(M); // typed ptr?
	if (!flags) flags = ESSENTIAL_FLAGS & finalPosValues[end]; // unmarked ptrs can rise all branches compatible with final values - end of a multiword (idiom or to-infintiive) is always the posvalued one
	for  (unsigned int k = 1; k <= size; ++k) 
	{
		M = GetMeaning(D,k); // it is a flagged meaning unless it self points
		if (!(GETTYPERESTRICTION(M) & flags)) continue;	// cannot match type

		// walk the synset words and see if any want vague concept matching like dog~~
		MEANING T = M; // starts with basic meaning
		unsigned int n = (index && k != index) ? 80 : 0;	// only on this meaning or all synset meanings 
		while (n < 50) // insure not infinite loop
		{
			WORDP X = Meaning2Word(T);
			unsigned int ind = Meaning2Index(T);
			sprintf(word,"%s~~",X->word);
			WORDP V = FindWord(word,0,PRIMARY_CASE_ALLOWED);
			if (V) 	MarkWordHit(V,start,end); // direct reference in a pattern
			if (!ind) break;	// has no meaning index
			T = GetMeanings(X)[ind];
			if (!T)
				break;
			if ((T & MEANING_BASE) == (M & MEANING_BASE)) break; // end of loop
			++n;
		}

		M = (M & SYNSET_MARKER) ? MakeMeaning(D,k) : GetMaster(M); // we are the master itself or we go get the master
		RiseUp(M,start,end,0,canonical); // allowed meaning pos (self ptrs need not rise up)
	}
}

static void SetSequenceStamp() //   mark words in sequence, original and canonical (but not mixed) - detects proper name potential up to 5 words  - and does discontiguous phrasal verbs
{
	char* rawbuffer = AllocateBuffer();
	char* canonbuffer1 = AllocateBuffer();
	char* raw_buffer = AllocateBuffer();
	char* canon_buffer1 = AllocateBuffer();
	unsigned int oldtrace = trace;
	unsigned int usetrace = trace;
	char* buffer2 = AllocateBuffer();
	if (trace & TRACE_PREPARE || prepareMode == PREPARE_MODE) 
	{
		Log(STDUSERLOG,"\r\nSequences:\r\n");
		usetrace = (unsigned int) -1;
	}

	//   consider all sets of up to 3-in-a-row 
	for (int i = startSentence; i < (int)endSentence; ++i)
	{
		if (!IsAlphaUTF8OrDigit(*wordStarts[i]) ) continue; // we only composite words, not punctuation or quoted stuff

		// check for dates
		int start,end;
		if (DateZone(i,start,end))
		{
			int at = start - 1;
			*rawbuffer = 0;
			while (++at <= end)
			{
				if (!stricmp(wordStarts[at],"of")) continue;	 // skip of
				strcat(rawbuffer,wordStarts[at]);
				if (at != end) strcat(rawbuffer,"_");
			}
			StoreWord(rawbuffer,NOUN|NOUN_PROPER_SINGULAR);
			NextInferMark();
			MarkFacts(MakeMeaning(FindWord("~dateinfo")),start,end,false,true); 
			i = end;
			continue;
		}

		//   set base phrase
		*rawbuffer = 0;
		canonbuffer1[0] = 0;
		*raw_buffer = 0;
		canon_buffer1[0] = 0;
		strcat(rawbuffer,wordStarts[i]);
		strcat(canonbuffer1,wordCanonical[i]);
  		strcat(raw_buffer,wordStarts[i]);
		strcat(canon_buffer1,wordCanonical[i]);
      
		//   fan out for addon pieces
		unsigned int k = 0;
		int index = 0;
		uint64 logbase = logCount; // see if we logged anything
		while ((++k + i) <= endSentence)
		{
			strcat(raw_buffer,"_");
			strcat(canon_buffer1,"_");
			strcat(rawbuffer," ");
			strcat(canonbuffer1," ");

			strcat(rawbuffer,wordStarts[i+k]);
			strcat(canonbuffer1,wordCanonical[i+k]);
			strcat(raw_buffer,wordStarts[i+k]);
			strcat(canon_buffer1,wordCanonical[i+k]);

			// we  composite anything, not just words, in case they made a typo
			NextInferMark();

			// for now, accept upper and lower case forms of the decomposed words for matching
			// storeword instead of findword because we normally dont store keyword phrases in dictionary
			WORDP D;
			if (tokenControl & STRICT_CASING) 
			{
				D = FindWord(rawbuffer,0,PRIMARY_CASE_ALLOWED); 
				if (D)
				{
					trace = (D->subjectHead || D->systemFlags & PATTERN_WORD || D->properties & PART_OF_SPEECH)  ? usetrace : 0; // being a subject head means belongs to some set. being a marked word means used as a keyword
					MarkFacts(MakeMeaning(D),i,i+k,false,true); 
				}
			}
			else
			{
				MakeLowerCopy(buffer2,rawbuffer);
				WORDP D = FindWord(buffer2,0,LOWERCASE_LOOKUP); 
				if (D)
				{
					trace = (D->subjectHead || D->systemFlags & PATTERN_WORD || D->properties & PART_OF_SPEECH)  ? usetrace : 0; // being a subject head means belongs to some set. being a marked word means used as a keyword
					MarkFacts(MakeMeaning(D),i,i+k,false,true); 
				}
				MakeUpperCopy(buffer2,rawbuffer);
				D = FindWord(buffer2,0,UPPERCASE_LOOKUP);
				if (D)
				{
					trace = (D->subjectHead || D->systemFlags & PATTERN_WORD || D->properties & PART_OF_SPEECH)  ? usetrace : 0;
					MarkSequenceTitleFacts(MakeMeaning(D),i,i+k,false);
				}
			}
			if (tokenControl & STRICT_CASING) 
			{
				D = FindWord(raw_buffer,0,PRIMARY_CASE_ALLOWED); 
				if (D)
				{
					trace = (D->subjectHead || D->systemFlags & PATTERN_WORD || D->properties & PART_OF_SPEECH)  ? usetrace : 0; // being a subject head means belongs to some set. being a marked word means used as a keyword
					MarkFacts(MakeMeaning(D),i,i+k,false,true); 
				}
			}
			else
			{
				MakeLowerCopy(buffer2,raw_buffer);
				WORDP D = FindWord(buffer2,0,LOWERCASE_LOOKUP); 
				if (D)
				{
					trace = (D->subjectHead || D->systemFlags & PATTERN_WORD || D->properties & PART_OF_SPEECH)  ? usetrace : 0; // being a subject head means belongs to some set. being a marked word means used as a keyword
					MarkFacts(MakeMeaning(D),i,i+k,false,true); 
				}
				MakeUpperCopy(buffer2,raw_buffer);
				D = FindWord(buffer2,0,UPPERCASE_LOOKUP);
				if (D)
				{
					trace = (D->subjectHead || D->systemFlags & PATTERN_WORD || D->properties & PART_OF_SPEECH)  ? usetrace : 0;
					MarkSequenceTitleFacts(MakeMeaning(D),i,i+k,false);
				}
			}
			
			if (tokenControl & STRICT_CASING) 
			{
				D = FindWord(canonbuffer1,0,PRIMARY_CASE_ALLOWED); 
				if (D && !(D->properties & (NOUN_PROPER_SINGULAR|NOUN_PROPER_PLURAL))) // proper nouns MUST be exact match to raw, not canonical
				{
					trace = (D->subjectHead || D->systemFlags & PATTERN_WORD || D->properties & PART_OF_SPEECH)  ? usetrace : 0; // being a subject head means belongs to some set. being a marked word means used as a keyword
					MarkFacts(MakeMeaning(D),i,i+k,false,true); 
				}
			}
			else
			{
				MakeLowerCopy(buffer2,canonbuffer1);
				D = FindWord(buffer2,0,LOWERCASE_LOOKUP);
				if (D) 
				{
					trace = (D->subjectHead  || D->systemFlags & PATTERN_WORD || D->properties & PART_OF_SPEECH)  ? usetrace : 0;
					MarkFacts(MakeMeaning(D),i,i+k,true,true); 
				}
				// dont do uppercase, that should have come from raw - EXCEPT "I say" given "I said"
				MakeUpperCopy(buffer2,canonbuffer1);
				D = FindWord(buffer2,0,UPPERCASE_LOOKUP);
				if (D)
				{
					trace = (D->subjectHead || D->systemFlags & PATTERN_WORD || D->properties & PART_OF_SPEECH)  ? usetrace : 0;
					MarkSequenceTitleFacts(MakeMeaning(D),i,i+k,false);
				}
		}
			if (tokenControl & STRICT_CASING) 
			{
				D = FindWord(canon_buffer1,0,PRIMARY_CASE_ALLOWED); 
				if (D && !(D->properties & (NOUN_PROPER_SINGULAR|NOUN_PROPER_PLURAL))) // proper nouns MUST be exact match to raw, not canonical
				{
					trace = (D->subjectHead || D->systemFlags & PATTERN_WORD || D->properties & PART_OF_SPEECH)  ? usetrace : 0; // being a subject head means belongs to some set. being a marked word means used as a keyword
					MarkFacts(MakeMeaning(D),i,i+k,false,true); 
				}
			}
			else
			{
				MakeLowerCopy(buffer2,canon_buffer1);
				D = FindWord(buffer2,0,LOWERCASE_LOOKUP);
				if (D) 
				{
					trace = (D->subjectHead  || D->systemFlags & PATTERN_WORD || D->properties & PART_OF_SPEECH)  ? usetrace : 0;
					MarkFacts(MakeMeaning(D),i,i+k,true,true); 
				}
				// dont do uppercase, that should have come from raw - EXCEPT "I say" given "I said"
				MakeUpperCopy(buffer2,canon_buffer1);
				D = FindWord(buffer2,0,UPPERCASE_LOOKUP);
				if (D)
				{
					trace = (D->subjectHead || D->systemFlags & PATTERN_WORD || D->properties & PART_OF_SPEECH)  ? usetrace : 0;
					MarkSequenceTitleFacts(MakeMeaning(D),i,i+k,false);
				}
			}
	

			if (logCount != logbase && usetrace)  Log(STDUSERLOG,"\r\n"); // if we logged something, separate
			
			if (++index >= SEQUENCE_LIMIT) break; //   up thru 5 words in a phrase
		}
	}
	
	// mark disjoint particles
	for (int i = wordCount; i >= 1; --i)
	{
		if (!(posValues[i] & PARTICLE)) continue;
		// find the particle
		unsigned int at = i;
		while (posValues[--at] & PARTICLE){;}	// back up thru contiguous particles
		if (posValues[at] & (VERB_BITS|NOUN_INFINITIVE|NOUN_GERUND|ADJECTIVE_PARTICIPLE)) continue;	// its all contiguous

		char canonical[MAX_WORD_SIZE];
		char original[MAX_WORD_SIZE];
		*canonical = 0;
		*original = 0;
		while (at && !(posValues[--at] & (VERB_BITS|NOUN_INFINITIVE|NOUN_GERUND|ADJECTIVE_PARTICIPLE))){;} // find the verb
		if (!at) continue; // failed to find match  "in his early work *on von neuman...

		unsigned int end = i;
		i = at; // resume later from here
		while (++at <= end)
		{
			if (posValues[at] & (VERB_BITS|PARTICLE|NOUN_INFINITIVE|NOUN_GERUND|ADJECTIVE_PARTICIPLE))
			{
				if (*original) 
				{
					strcat(original,"_");
					strcat(canonical,"_");
				}
				strcat(original,wordStarts[at]);
				strcat(canonical, wordCanonical[at]);
			}
		}
		NextInferMark();

		// storeword instead of findword because we normally dont store keyword phrases in dictionary
		WORDP D = FindWord(original,0,LOWERCASE_LOOKUP); 
		if (D)
		{
			trace = usetrace; // being a subject head means belongs to some set. being a marked word means used as a keyword
			MarkFacts(MakeMeaning(D),i,i,false,false); 
		}
		if (stricmp(original,canonical))
		{
			D = FindWord(canonical,0,LOWERCASE_LOOKUP);
			if (D) 
			{
				trace = usetrace;
				MarkFacts(MakeMeaning(D),i,i,true,false); 
			}
		}
	}


	trace = oldtrace;
	FreeBuffer();
	FreeBuffer();
	FreeBuffer();
	FreeBuffer();
	FreeBuffer();
}

static void StdMark(MEANING M, unsigned int start, unsigned int end, bool canonical) 
{
	if (!M) return;
	MarkFacts(M,start,end,canonical);		//   the basic word
	WORDP D = Meaning2Word(M);
	if (D->systemFlags & TIMEWORD && !(D->properties & PREPOSITION)) MarkFacts(MakeMeaning(Dtime),start,end);
}


void MarkAllImpliedWords()
{
	ChangeDepth(1,"MarkAllImpliedWords");
	memset(concepts,0, sizeof(unsigned int) * MAX_SENTENCE_LENGTH); // precautionary, not required in theory
	memset(topics,0, sizeof(unsigned int) * MAX_SENTENCE_LENGTH); // precautionary, not required in theory

	unsigned int i;
 	for (i = 1; i <= wordCount; ++i)  capState[i] = IsUpperCase(*wordStarts[i]); // note cap state
	TagIt(); // pos tag and maybe parse
	if ( prepareMode == POS_MODE || tmpPrepareMode == POS_MODE || prepareMode == PENN_MODE || prepareMode == POSVERIFY_MODE  || prepareMode == POSTIME_MODE ) 
	{
		ChangeDepth(-1,"MarkAllImpliedWords");
		return;
	}
	WORDP pos = FindWord("~pos");
	WORDP sys = FindWord("~sys");
	WORDP role = FindWord("~grammar_role");

    if (trace & TRACE_PREPARE || prepareMode == PREPARE_MODE) Log(STDUSERLOG,"\r\nConcepts: \r\n");
 	if (showMark)  Log(ECHOSTDUSERLOG,"----------------\r\n");
	markLength = 0;
	//   now mark every word in sentence
    for (i = startSentence; i <= endSentence; ++i) //   mark that we have found this word, either in original or canonical form
    {
		char* original =  wordStarts[i];
		if (!wordCanonical[i]) wordCanonical[i] = original; // in case failure below

		if (showMark) Log(ECHOSTDUSERLOG,"\r\n");
		NextInferMark(); // blocks circular fact marking.
		pos->inferMark = inferMark; // dont mark these supersets of pos-tagging stuff
		sys->inferMark = inferMark; // dont mark these supersets of pos-tagging stuff
		role->inferMark = inferMark; // dont mark these supersets of pos-tagging stuff

 		if (trace  & (TRACE_HIERARCHY | TRACE_PREPARE) || prepareMode == PREPARE_MODE) Log(STDUSERLOG,"\r\n%d: %s (raw): ",i,original);
	
		uint64 flags = posValues[i];
		//if (flags & ADJECTIVE_NOUN) // transcribe back to adjective
		//{
			//MarkFacts(MadjectiveNoun,i,i); 
			//flags |= ADJECTIVE;
	//		if (originalLower[i]) flags |= originalLower[i]->properties & (NOUN_SINGULAR|NOUN_PLURAL|NOUN_PROPER_SINGULAR|NOUN_PROPER_PLURAL);
		//}
		WORDP D = originalLower[i] ? originalLower[i] : originalUpper[i]; // one of them MUST have been set
		if (!D) {
			int xx = 0;
		}
		// put back non-tagger generalized forms of bits
		if (flags & NOUN_BITS) flags |= NOUN;
		if (flags & (VERB_BITS | NOUN_INFINITIVE| NOUN_GERUND)) flags |= VERB;
		if (flags & ADJECTIVE_BITS) flags |= ADJECTIVE  | (allOriginalWordBits[i] & (MORE_FORM|MOST_FORM));
		if (flags & NOUN_ADJECTIVE) flags |=  (allOriginalWordBits[i] & (MORE_FORM|MOST_FORM)) | ADJECTIVE_NORMAL | ADJECTIVE; // what actress is the *prettiest  -- be NOUN OR ADJECTIVE
		if (flags & ADVERB) flags |= ADVERB |  (allOriginalWordBits[i] & (MORE_FORM|MOST_FORM));
		if (D && D->systemFlags & ORDINAL) 
		{
			flags |= PLACE_NUMBER;
			AddParseBits(D,QUANTITY_NOUN);
		}
		if (!stricmp(wordCanonical[i],"be"))
		{
			if (!stricmp(original,"am") || !stricmp(original,"was")) flags |= SINGULAR_PERSON;
		}
		if (flags & NOUN_INFINITIVE && !(flags & NOUN_SINGULAR)) // transcribe back to verb only, leaving noun_infinitive status and not verb tense status
		{
			flags &= -1 ^ NOUN; // but still a noun_infinitive
			flags |= VERB;
		}
		finalPosValues[i] = flags; // these are what we finally decided were correct pos flags from tagger
		
		if (wordStarts[i][1] && (wordStarts[i][1] == ':' || wordStarts[i][2] == ':')) // time info 1:30 or 11:30
		{
			if (originalLower[i] && IsDigit(wordStarts[i][0]) && IsDigit(wordStarts[i][3])) 
			{
				AddSystemFlag(D,ACTUAL_TIME);
			}
		}

		MarkTags(i);
#ifndef DISCARDPARSER
		MarkRoles(i);
#endif
	
		// mark general number property
		if (D->properties & ( NOUN_NUMBER | ADJECTIVE_NUMBER))   // a date can become an idiom, marking it as a proper noun and not a number
		{
			if (IsDigit(*wordStarts[i]) && IsDigit(wordStarts[i][1])  && IsDigit(wordStarts[i][2]) && IsDigit(wordStarts[i][3])  && !wordStarts[i][4]) MarkFacts(MakeMeaning(FindWord("~yearnumber")),i,i);
			if (!wordCanonical[i][1] || !wordCanonical[i][2]) // 2 digit or 1 digit
			{
				int n = atoi(wordCanonical[i]);
				if (n > 0 && n < 32 && *wordStarts[i] != '$') MarkFacts(MakeMeaning(FindWord("~daynumber")),i,i);
			}

			MarkFacts(Mnumber,i,i); 
			//   handle finding fractions as 3 token sequence  mark as placenumber 
			if (i < wordCount && *wordStarts[i+1] == '/' && wordStarts[i+1][1] == 0 && finalPosValues[i+2] & (NOUN_NUMBER | ADJECTIVE_NUMBER))
			{
				MarkFacts(MakeMeaning(Dplacenumber),i,i);  
				if (trace & TRACE_PREPARE || prepareMode == PREPARE_MODE) Log(STDUSERLOG,"=%s/%s \r\n",wordStarts[i],wordStarts[i+2]);
			}
			else if (IsDigit(*wordStarts[i]) && IsPlaceNumber(wordStarts[i])) // finalPosValues[i] & (NOUN_NUMBER | ADJECTIVE_NUMBER) 
			{
				MarkFacts(MakeMeaning(Dplacenumber),i,i);  
			}
			// special temperature property
			char c = GetTemperatureLetter(original);
			if (c)
			{
				if (c == 'F') MarkFacts(MakeMeaning(StoreWord("~fahrenheit")),i,i);
				else if (c == 'C') MarkFacts(MakeMeaning(StoreWord("~celsius")),i,i);
				else if (c == 'K')  MarkFacts(MakeMeaning(StoreWord("~kelvin")),i,i);
				MarkFacts(Mnumber,i,i);
				char number[MAX_WORD_SIZE];
				sprintf(number,"%d",atoi(original));
				WORDP canon =  StoreWord(number,(NOUN_NUMBER | ADJECTIVE_NUMBER));
				if (canon) wordCanonical[i] = canon->word;
			}

			// special currency property
			char* number;
			char* currency = GetCurrency(wordStarts[i],number); 
			if (currency) 
			{
				char tmp[MAX_WORD_SIZE];
				strcpy(tmp,currency);
				MarkFacts(Mmoney,i,i); 
				if (*currency == '$') tmp[1] = 0;
				else if (*currency == 0xe2 && currency[1] == 0x82 && currency[2] == 0xac) tmp[3] = 0;
				else if (*currency == 0xc2 && currency[1] == 0xa5 ) tmp[2] = 0;
				else if (*currency == 0xc2 && currency[1] == 0xa3 ) tmp[2] = 0;
				MarkFacts(MakeMeaning(StoreWord(tmp)),i,i);
			}
		}
	
		if (FindTopicIDByName(wordStarts[i])) MarkFacts(MakeMeaning(Dtopic),i,i);

        WORDP OL = originalLower[i];
		WORDP CL = canonicalLower[i];
 		WORDP OU = originalUpper[i]; 
        WORDP CU = canonicalUpper[i]; 
		
		if (!CU && original[1]) // dont convert single letters to upper case "a" if it hasnt already decided its not a determiner
		{
			CU = FindWord(original,0,UPPERCASE_LOOKUP);	// try to find an upper to go with it, in case we can use that, but not as a human name
			if (OU){;} // it was originally uppercase or there is no lower case meaning
			else if (CU && CU->properties & (NOUN_FIRSTNAME|NOUN_HUMAN)) CU = NULL;	// remove accidental names 
		}
	
		if (CL && CL == DunknownWord) // allow unknown proper names to be marked unknown
		{
			MarkFacts(MakeMeaning(Dunknown),i,i); // unknown word
			MarkFacts(MakeMeaning(StoreWord(original)),i,i);		// allowed word
		}

		// note "bank teller" we want bank to have recognizion of its noun meaning in concepts - must do FIRST as noun, since adjective value is abnormal
		unsigned int restriction = (unsigned int)(finalPosValues[i] & BASIC_POS);
		if (finalPosValues[i] & ADJECTIVE_NOUN) StdMark(MakeTypedMeaning(OL,0,NOUN), i, i,false); //  mark word as a noun
		else StdMark(MakeTypedMeaning(OL,0,restriction), i, i,false);
        if (trace & TRACE_PREPARE || prepareMode == PREPARE_MODE) Log(STDUSERLOG," // "); //   close original meanings lowercase

		markLength = 0;
		if (IS_NEW_WORD(OU) && (OL || CL)) {;}
		else 
		{
			if (finalPosValues[i] & ADJECTIVE_NOUN) StdMark(MakeTypedMeaning(OU,0,NOUN), i, i,false); //  mark word as a noun first, adjective is not normal
			else StdMark(MakeTypedMeaning(OU,0,restriction), i, i,false);
       	}
		
		if (trace & TRACE_PREPARE || prepareMode == PREPARE_MODE) 
		{
			if (CL) Log(STDUSERLOG,"\r\n%d: %s (canonical): ", i,CL->word ); //    original meanings lowercase
			else Log(STDUSERLOG,"\r\n%d: %s (canonical): ", i,(CU) ? CU->word : "" ); //    original meanings uppercase
		}

		//   canonical word
		if (finalPosValues[i] & ADJECTIVE_BITS && allOriginalWordBits[i] & (VERB_PRESENT_PARTICIPLE|VERB_PAST_PARTICIPLE)) // see if adj is verb as canonical base - "ing and ed" forms
		{
			StdMark(MakeTypedMeaning(CL,0,VERB), i, i,true);
		}
		else if (finalPosValues[i] & (NOUN_GERUND|NOUN_INFINITIVE))
		{
			StdMark(MakeTypedMeaning(CL,0,VERB), i, i,true);
		}
 		else if (finalPosValues[i] & ADJECTIVE_NOUN)
		{
			StdMark(MakeTypedMeaning(CL,0,NOUN), i, i,true);
		}
		else StdMark(MakeTypedMeaning(CL,0, (unsigned int)(finalPosValues[i] & BASIC_POS)), i, i,true);

 		markLength = 0;
	    if (trace & TRACE_PREPARE || prepareMode == PREPARE_MODE) Log(STDUSERLOG," // "); //   close canonical form lowercase
 		
		// mark upper case canonical ONLY if existed (someone wants it) - March in lower case is always a problem
		if (!IS_NEW_WORD(CU)) StdMark(MakeTypedMeaning(CU,0, (unsigned int)(finalPosValues[i] & BASIC_POS)), i, i,true);

		// canonical word is a number (maybe we didn't register original right) eg. "how much is 24 and *seven"
		if (IsDigit(*wordCanonical[i]) && IsNumber(wordCanonical[i])) MarkFacts(Mnumber,i,i,true);  

		if (trace & TRACE_PREPARE || prepareMode == PREPARE_MODE) Log(STDUSERLOG," "); //   close canonical form uppercase
		markLength = 0;
	
        //   peer into multiword expressions  (noncanonical), in case user is emphasizing something so we dont lose the basic match on words
        //   accept both upper and lower case forms . 
		// But DONT peer into something proper like "Moby Dick"
		unsigned int  n = BurstWord(wordStarts[i]); // peering INSIDE a single token....
		WORDP E;
		if (tokenControl & NO_WITHIN);  // dont peek within hypenated words
        else if (finalPosValues[i] & (NOUN_PROPER_SINGULAR|NOUN_PROPER_PLURAL)) // mark first and last word, if they are recognized words
		{
			char* w = GetBurstWord(0);
			WORDP D1 = FindWord(w);
			w = GetBurstWord(n-1);
			WORDP D2 = FindWord(w);
			if (D1 && allOriginalWordBits[i] & NOUN_HUMAN ) MarkFacts(MakeMeaning(D1),i,i); // allow first name recognition with human names
			if (D1) MarkFacts(MakeMeaning(D2),i,i); // allow final word as in "Bill Gates" "United States of America" , 
			n = 1;
		}
        else if (n >= 2 && n <= 4) //   longer than 4 is not emphasis, its a sentence - we do not peer into titles
        {
			static char words[5][MAX_WORD_SIZE];
			unsigned int k;
			for (k = 0; k < n; ++k) strcpy(words[k],GetBurstWord(k)); // need local copy since burstwords might be called again..

            for (unsigned int k = 0; k < n; ++k)
            {
  				unsigned int prior = (k == (n-1)) ? i : (i-1); //   -1  marks its word match INSIDE a string before the last word, allow it to see last word still
                E = FindWord(words[k],0,PRIMARY_CASE_ALLOWED); 
                if (E)
				{
					if (!(E->properties & (NOUN_PROPER_SINGULAR|NOUN_PROPER_PLURAL))) StdMark(MakeMeaning(E),i,prior,false);
					else MarkFacts(MakeMeaning(E),i,prior);
				}
                E = FindWord(words[k],0,SECONDARY_CASE_ALLOWED); 
				if (E)
				{
					if (!(E->properties & (NOUN_PROPER_SINGULAR|NOUN_PROPER_PLURAL))) StdMark(MakeMeaning(E),i,prior,false);
					else MarkFacts(MakeMeaning(E),i,prior);
				}
           }
        }

		// now look on either side of a hypenated word
		char* hypen = strchr(wordStarts[i],'-');
		if (hypen) 
		{
			MarkFacts(MakeMeaning(StoreWord(hypen)),i,i); // post form -colored
			char word[MAX_WORD_SIZE];
			strcpy(word,wordStarts[i]);
			word[hypen+1-wordStarts[i]] = 0;
			MarkFacts(MakeMeaning(StoreWord(word)),i,i); // pre form  light-
		}
		
		D = (CL) ? CL : CU; //   best recognition
		char* last;
		if (D && D->properties & NOUN && !(D->internalBits & UPPERCASE_HASH) && (last = strrchr(D->word,'_')) && finalPosValues[i] & NOUN) StdMark(MakeMeaning(FindWord(last+1,0)), i, i,true); //   composite noun, store last word as referenced also

		// ALL Foreign words detectable by utf8 char
		D = (OL) ? OL : OU;
		if (D && D->internalBits & UTF8) MarkFacts(MakeMeaning(StoreWord("~utf8")),i,i);
		if (D && D->internalBits & UPPERCASE_HASH && D->length > 1)  MarkFacts(MakeMeaning(Dpropername),i,i);  // historical - internal is uppercase

        if (trace & TRACE_PREPARE || prepareMode == PREPARE_MODE) Log(STDUSERLOG,"\r\n");
    }
 
	//   check for repeat input by user - but only if more than 2 words or are unknown (we dont mind yes, ok, etc repeated)
	//   track how many repeats, for escalating response
	unsigned int sentenceLength = endSentence - startSentence + 1;
	bool notbrief = (sentenceLength > 2);
	if (sentenceLength == 1 && !FindWord(wordStarts[startSentence])) notbrief = true;
    unsigned int counter = 0;
    if (notbrief && humanSaidIndex) for (int j = 0; j < (int)(humanSaidIndex-1); ++j)
    {
        if (strlen(humanSaid[j]) > 5 && !stricmp(humanSaid[humanSaidIndex-1],humanSaid[j])) //   he repeats himself
        {
            ++counter;
            char buf[100];
			strcpy(buf,"~repeatinput");
			buf[12] = (char)('0' + counter);
			buf[13] = 0;
 			MarkFacts(MakeMeaning(FindWord(buf,0,PRIMARY_CASE_ALLOWED)),1,1); //   you can see how many times
        }
    }

	//   now see if he is repeating stuff I said
	counter = 0;
    if (sentenceLength > 2) for (int j = 0; j < (int)chatbotSaidIndex; ++j)
    {
        if (humanSaidIndex && strlen(chatbotSaid[j]) > 5 && !stricmp(humanSaid[humanSaidIndex-1],chatbotSaid[j])) //   he repeats me
        {
			if (counter < sentenceLength) ++counter;
			MarkFacts(MakeMeaning(FindWord("~repeatme",0,PRIMARY_CASE_ALLOWED)),counter,counter); //   you can see how many times
        }
    }

    //   handle phrases now
	markLength = 0;
    SetSequenceStamp(); //   sequences of words

	ChangeDepth(-1,"MarkAllImpliedWords");
}
