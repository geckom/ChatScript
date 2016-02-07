#include "common.h"

#define LETTERMAX 40

static unsigned char letterIndexData[256] = 
{
	0,0,0,0,0,0,0,0,0,0,	0,0,0,0,0,0,0,0,0,0,
	0,0,0,0,0,0,0,0,0,0,	0,0,0,0,0,0,0,0,0,0,
	0,0,0,0,0,37,38,0,27,28,	29,30,31,32,33,34,35,36,0,0,  //37=- 38 = .  
	0,0,0,0,0,0,0,0,0,0,	0,0,0,0,0,0,0,0,0,0,
	0,0,0,0,0,0,0,0,0,0, 	0,0,0,0,0,39,0,1,2,3, // 39 is _
	4,5,6,7,8,9,10,11,12,13, 	14,15,16,17,18,19,20,21,22,23,
	24,25,26,0,0,0,0,0,0,0,
	0,0,0,0,0,0,0,0,0,0,	0,0,0,0,0,0,0,0,0,0,
	0,0,0,0,0,0,0,0,0,0,	0,0,0,0,0,0,0,0,0,0,
	0,0,0,0,0,0,0,0,0,0,	0,0,0,0,0,0,0,0,0,0,
	0,0,0,0,0,0,0,0,0,0,	0,0,0,0,0,0,0,0,0,0,
	0,0,0,0,0,0,0,0,0,0,	0,0,0,0,0,0,0,0,0,0,
	0,0,0,0,0,0,0,0,0,0,	0,0,0,0,0,0,0,0,0,0,
	0,0,0,0,0,0
};

static MEANING lengthLists[100];		// lists of valid words by length

typedef struct SUFFIX
{
    char* word;
	uint64 flags;
} SUFFIX;

static SUFFIX stems[] = 
{
	{"less",NOUN},
	{"ness",ADJECTIVE|NOUN},
	{"est",ADJECTIVE},
	{"en",ADJECTIVE},
	{"er",ADJECTIVE},
	{"ly",ADJECTIVE},
	{0},
};

void InitSpellCheck()
{
	memset(lengthLists,0,sizeof(MEANING) * 100);
	WORDP D = dictionaryBase - 1;
	while (++D <= dictionaryFree)
	{
		if (!D->word || !IsAlphaUTF8(*D->word) || D->length >= 100 || strchr(D->word,'~') || strchr(D->word,'$') || strchr(D->word,'^')) continue; 
		if (D->properties & PART_OF_SPEECH || D->systemFlags & PATTERN_WORD)
		{
			D->spellNode = lengthLists[D->length];
			lengthLists[D->length] = MakeMeaning(D);
		}
	}
}

static int SplitWord(char* word)
{
	WORDP D2;
	bool good;
	int breakAt = 0;
	if (IsDigit(*word))
    {
		while (IsDigit(word[++breakAt]) || word[breakAt] == '.'){;} //   find end of number
        if (word[breakAt]) // found end of number
		{
			D2 = FindWord(word+breakAt,0,PRIMARY_CASE_ALLOWED);
			if (D2)
			{
				good = (D2->properties & (PART_OF_SPEECH|FOREIGN_WORD)) != 0 || (D2->internalBits & HAS_SUBSTITUTE) != 0; 
				if (good && (D2->systemFlags & AGE_LEARNED))// must be common words we find
				{
					char number[MAX_WORD_SIZE];
					strncpy(number,word,breakAt);
					number[breakAt] = 0;
					StoreWord(number,ADJECTIVE|NOUN|ADJECTIVE_NUMBER|NOUN_NUMBER); 
					return breakAt; // split here
				}
			}
		}
    }

	//  try all combinations of breaking the word into two known words
	breakAt = 0;
	size_t len = strlen(word);
    for (unsigned int k = 1; k < len-1; ++k)
    {
        if (k == 1 &&*word != 'a' &&*word != 'A' &&*word != 'i' &&*word != 'I') continue; //   only a and i are allowed single-letter words
		WORDP D1 = FindWord(word,k,PRIMARY_CASE_ALLOWED);
        if (!D1) continue;
		good = (D1->properties & (PART_OF_SPEECH|FOREIGN_WORD)) != 0 || (D1->internalBits & HAS_SUBSTITUTE) != 0; 
		if (!good || !(D1->systemFlags & AGE_LEARNED)) continue; // must be normal common words we find

        D2 = FindWord(word+k,len-k,PRIMARY_CASE_ALLOWED);
        if (!D2) continue;
        good = (D2->properties & (PART_OF_SPEECH|FOREIGN_WORD)) != 0 || (D2->internalBits & HAS_SUBSTITUTE) != 0;
		if (!good || !(D2->systemFlags & AGE_LEARNED) ) continue; // must be normal common words we find

        if (!breakAt) breakAt = k; // found a split
		else // found multiple places to split... dont know what to do
        {
           breakAt = -1; 
           break;
		}
    }
	return breakAt;
}

static char* SpellCheck(unsigned int i)
{
    //   on entry we will have passed over words which are KnownWord (including bases) or isInitialWord (all initials)
    //   wordstarts from 1 ... wordCount is the incoming sentence words (original). We are processing the ith word here.
    char* word = wordStarts[i];
	if (!*word) return NULL;
	if (!stricmp(word,loginID) || !stricmp(word,computerID)) return word; //   dont change his/our name ever

	size_t len = strlen(word);
	if (len > 2 && word[len-2] == '\'') return word;	// dont do anything with ' words

    //   test for run togetherness like "talkabout fingers"
    int breakAt = SplitWord(word);
    if (breakAt > 0)//   we found a split, insert 2nd word into word stream
    {
        ++wordCount;
		memmove(wordStarts+i+1,wordStarts+i,sizeof(char*) * (wordCount-i)); // open up a slot for a new word
        wordStarts[i+1] = reuseAllocation(wordStarts[i+1],wordStarts[i]+breakAt); // set this to the second word (shared from within 1st word)
        return FindWord(wordStarts[i],breakAt,PRIMARY_CASE_ALLOWED)->word; //   1st word gets replaced, we added valid word after
    }

	// now imagine partial runtogetherness, like "talkab out fingers"
	if (i < wordCount)
	{
		char tmp[MAX_WORD_SIZE];
		strcpy(tmp,word);
		strcat(tmp,wordStarts[i+1]);
		breakAt = SplitWord(tmp);
		if (breakAt > 0) // replace words with the dual pair
		{
			wordStarts[i+1] = reuseAllocation(wordStarts[i+1],StoreWord(tmp+breakAt)->word); // set this to the second word (shared from within 1st word)
			return FindWord(tmp,breakAt,PRIMARY_CASE_ALLOWED)->word; // 1st word gets replaced, we added valid word after
		}
	}

    //   remove any nondigit characters repeated more than once. Dont do this earlier, we want substitutions to have a chance at it first.  ammmmmmazing
	static char word1[MAX_WORD_SIZE];
    char* ptr = word-1; 
	char* ptr1 = word1;
    while (*++ptr)
    {
	   *ptr1 = *ptr;
	   while (ptr[1] == *ptr1 && ptr[2] == *ptr1 && (*ptr1 < '0' || *ptr1 > '9')) ++ptr; // skip double repeats
	   ++ptr1;
    }
	*ptr1 = 0;
	if (FindCanonical(word1,0,true) && !IsUpperCase(*word1)) return word1; // this is a different form of a canonical word so its ok

	//   now use word spell checker 
    char* d = SpellFix(word,i,PART_OF_SPEECH); 
    return (d) ? d : NULL;
}

char* ProbableKnownWord(char* word)
{
	if (strchr(word,' ') || strchr(word,'_')) return word; // not user input, is synthesized
	size_t len = strlen(word);

	// do we know the word as is?
	WORDP D = FindWord(word,0,PRIMARY_CASE_ALLOWED);
	if (D) 
	{
		if (D->properties & FOREIGN_WORD || *D->word == '~' || D->systemFlags & PATTERN_WORD) return D->word;	// we know this word clearly or its a concept set ref emotion
		if (D->properties & PART_OF_SPEECH && !IS_NEW_WORD(D)) return D->word; // old word we know
		// are there facts using this word?
		if (GetSubjectNondeadHead(D) || GetObjectNondeadHead(D) || GetVerbNondeadHead(D)) return D->word;
	}
	
	char lower[MAX_WORD_SIZE];
	MakeLowerCopy(lower,word);

	// do we know the word in lower case?
	D = FindWord(word,0,LOWERCASE_LOOKUP);
	if (D) // direct recognition
	{
		if (D->properties & FOREIGN_WORD || *D->word == '~' || D->systemFlags & PATTERN_WORD) return D->word;	// we know this word clearly or its a concept set ref emotion
		if (D->properties & PART_OF_SPEECH && !IS_NEW_WORD(D)) return D->word; // old word we know
		// are there facts using this word?
		if (GetSubjectNondeadHead(D) || GetObjectNondeadHead(D) || GetVerbNondeadHead(D)) return D->word;
	}

	// do we know the word in upper case?
	char upper[MAX_WORD_SIZE];
	MakeLowerCopy(upper,word);
	upper[0] = GetUppercaseData(upper[0]);
	D = FindWord(upper,0,UPPERCASE_LOOKUP);
	if (D) // direct recognition
	{
		if (D->properties & FOREIGN_WORD || *D->word == '~' || D->systemFlags & PATTERN_WORD) return D->word;	// we know this word clearly or its a concept set ref emotion
		if (D->properties & PART_OF_SPEECH && !IS_NEW_WORD(D)) return D->word; // old word we know
		// are there facts using this word?
		if (GetSubjectNondeadHead(D) || GetObjectNondeadHead(D) || GetVerbNondeadHead(D)) return D->word;
	}

	// interpolate to lower case words 
	uint64 expectedBase = 0;
	if (ProbableAdjective(word,len,expectedBase) && expectedBase) return word;
	expectedBase = 0;
	if (ProbableAdverb(word,len,expectedBase) && expectedBase) return word;
	// is it a verb form
	char* verb = English_GetInfinitive(lower,false);
	if (verb) 
	{
		WORDP D =  StoreWord(lower,0); // verb form recognized
		return D->word;
	}
	
	// is it simple plural of a noun?
	if (word[len-1] == 's') 
	{
		WORDP E = FindWord(lower,len-1,LOWERCASE_LOOKUP);
		if (E && E->properties & NOUN) 
		{
			return word;	
		}
		E = FindWord(lower,len-1,UPPERCASE_LOOKUP);
		if (E && E->properties & NOUN) 
		{
			*word = toUppercaseData[*word];
			return word;	
		}
	}

	return NULL;
}

bool SpellCheckSentence()
{
	WORDP D,E;
	bool fixedSpell = false;
	bool lowercase = false;
	// check for all uppercase
	for (unsigned int i = FindOOBEnd(1) + 1; i <= wordCount; ++i) // skip start of sentence
	{
		char* word = wordStarts[i];
		size_t len = strlen(word);
		for (unsigned int j = 0; j < len; ++j) 
		{
			if (IsLowerCase(word[j])) 
			{
				lowercase = true;
				i = j = 1000;
			}
		}
	}
	if (!lowercase && wordCount > 2) // must have several words in uppercase
	{
		for (unsigned int i = FindOOBEnd(1); i <= wordCount; ++i)
		{
			char* word = wordStarts[i];
			MakeLowerCase(word);
		}
	}

	unsigned int startWord = FindOOBEnd(1);
	for (unsigned int i = startWord; i <= wordCount; ++i)
	{
		char* word = wordStarts[i];
		if (!word || !word[1] || *word == '"' ) continue; // illegal or single char or quoted thingy 
		size_t len = strlen(word);

		// dont spell check uppercase not at start or joined word
		if (IsUpperCase(word[0]) && (i != startWord || strchr(word,'_')) && tokenControl & NO_PROPER_SPELLCHECK) continue; 
		//  dont  spell check email or other things with @ or . in them
		if (strchr(word,'@') || strchr(word,'.') || strchr(word,'$')) continue;

		char* known = ProbableKnownWord(word);
		if (known) 
		{
			if (strcmp(known,word)) // revised the word to lower case
			{
				wordStarts[i] = reuseAllocation(wordStarts[i],known);
				fixedSpell = true;
			}
			continue;
		}

		char* p = word -1;
		unsigned char c;
		char* hyphen = 0;
		char* under = 0;
		while ((c = *++p) != 0)
		{ 
			++len;
			if (c == '-') hyphen = p; // note is hyphenated - use trailing
			else if (c == '_') under = p; // note is underscored - use trailing
		}
		if (len == 0 || GetTemperatureLetter(word)) continue;	// bad ignore utf word or llegal length - also no composite words
		if (c && c != '@' && c != '.') // illegal word character
		{
			if (IsDigit(word[0]) || len == 1){;} // probable numeric?
			// accidental junk on end of word we do know immedately?
			else if (i > 1 && !IsAlphaUTF8OrDigit(wordStarts[i][len-1]) )
			{
				WORDP entry,canonical;
				char word[MAX_WORD_SIZE];
				strcpy(word,wordStarts[i]);
				word[len-1] = 0;
				uint64 sysflags = 0;
				uint64 cansysflags = 0;
				GetPosData(i,word,entry,canonical,sysflags,cansysflags,true,true); // dont create a non-existent word
				if (entry && entry->properties & PART_OF_SPEECH)
				{
					wordStarts[i] = reuseAllocation(wordStarts[i],entry->word);
					fixedSpell = true;
					continue;	// not a legal word character, leave it alone
				}
			}
		}

		// see if we know the other case
		if (!(tokenControl & (ONLY_LOWERCASE|STRICT_CASING)) || (i == startSentence && !(tokenControl & ONLY_LOWERCASE)))
		{
			WORDP E = FindWord(word,0,SECONDARY_CASE_ALLOWED);
			bool useAlternateCase = false;
			if (E && E->systemFlags & PATTERN_WORD) useAlternateCase = true;
			if (E && E->properties & (PART_OF_SPEECH|FOREIGN_WORD))
			{
				// if the word we find is UPPER case, and this might be a lower case noun plural, don't change case.
				size_t len = strlen(word);
				if (word[len-1] == 's' ) 
				{
					WORDP F = FindWord(word,len-1);
					if (!F || !(F->properties & (PART_OF_SPEECH|FOREIGN_WORD))) useAlternateCase = true;
					else continue;
				}
				else useAlternateCase = true;
			}
			if (useAlternateCase)
			{
				wordStarts[i] = reuseAllocation(wordStarts[i],E->word);
				fixedSpell = true;
				continue;	
			}
		}
		
		// merge with next token?
		char join[MAX_WORD_SIZE];
		if (i != wordCount && *wordStarts[i+1] != '"' )
		{
			// direct merge as a single word
			strcpy(join,word);
			strcat(join,wordStarts[i+1]);
			WORDP D = FindWord(join,0,(tokenControl & ONLY_LOWERCASE) ?  PRIMARY_CASE_ALLOWED : STANDARD_LOOKUP);

			strcpy(join,word);
			if (!D || !(D->properties & PART_OF_SPEECH) ) // merge these two, except "going to" or wordnet composites of normal words  // merge as a compound word
			{
				strcat(join,"_");
				strcat(join,wordStarts[i+1]);
				D = FindWord(join,0,(tokenControl & ONLY_LOWERCASE) ?  PRIMARY_CASE_ALLOWED : STANDARD_LOOKUP);
			}

			if (D && D->properties & PART_OF_SPEECH && !(D->properties & AUX_VERB)) // merge these two, except "going to" or wordnet composites of normal words
			{
				WORDP P1 = FindWord(word,0,LOWERCASE_LOOKUP);
				WORDP P2 = FindWord(wordStarts[i+1],0,LOWERCASE_LOOKUP);
				if (!P1 || !P2 || !(P1->properties & PART_OF_SPEECH) || !(P2->properties & PART_OF_SPEECH)) 
				{
					memmove(wordStarts+i+1,wordStarts+i+2,sizeof(char*) * (wordCount - i - 1));
					wordStarts[i] = reuseAllocation(wordStarts[i],D->word);
					--wordCount;
					continue;
				}
			}
		}   

		// break apart slashed pair like eat/feed
		char* slash = strchr(word,'/');
		if (slash && slash != word && slash[1]) //   break apart word/word
		{
			*slash = 0;
			if ((wordCount + 2 ) >= REAL_SENTENCE_LIMIT) continue;	// no room
			wordCount += 2;
			memmove(wordStarts+i+3,wordStarts+i+1,(wordCount-i)*sizeof(char*)); 
			D = StoreWord(word);
			E = StoreWord(slash+1);
			wordStarts[i] = reuseAllocation(wordStarts[i],D->word);
			wordStarts[i+1] = reuseAllocation(wordStarts[i+1],"/");
			wordStarts[i+2] = reuseAllocation(wordStarts[i+1],E->word);
			--i;
			continue;
		}

		// see if hypenated word should be separate or joined (ignore obvious adjective suffix)
		if (hyphen &&  !stricmp(hyphen,"-like"))
		{
			StoreWord(word,ADJECTIVE_NORMAL|ADJECTIVE); // accept it as a word
			continue;
		}
		else if (hyphen && (hyphen-word) > 1)
		{
			char test[MAX_WORD_SIZE];
			*hyphen = 0;

			// test for split
			strcpy(test,hyphen+1);
			WORDP E = FindWord(test,0,LOWERCASE_LOOKUP);
			WORDP D = FindWord(word,0,LOWERCASE_LOOKUP);
			if (*word == 0) wordStarts[i] = AllocateString(wordStarts[i] + 1); // -pieces  want to lose the leading hypen  (2-pieces)
			else if (D && E) //   1st word gets replaced, we added another word after
			{
				if ((wordCount + 1 ) >= REAL_SENTENCE_LIMIT) continue;	// no room
				++wordCount;
				memmove(wordStarts+i+2,wordStarts+i+1,(wordCount-i)*sizeof(char*)); // make room for new word
				wordStarts[i] = reuseAllocation(wordStarts[i],D->word);
				wordStarts[i+1] = reuseAllocation(wordStarts[i+1],E->word);
				--i;
			}
			else if (!stricmp(test,"old") || !stricmp(test,"olds")) //   break apart 5-year-old
			{
				if ((wordCount + 1 ) >= REAL_SENTENCE_LIMIT) continue;	// no room
				++wordCount;
				memmove(wordStarts+i+2,wordStarts+i+1,(wordCount-i)*sizeof(char*)); 
				D = StoreWord(word);
				E = StoreWord(test);
				wordStarts[i] = reuseAllocation(wordStarts[i],D->word);
				wordStarts[i+1] = reuseAllocation(wordStarts[i+1],E->word);
				--i;
			}
			else // remove hyphen entirely?
			{
				strcpy(test,word);
				strcat(test,hyphen+1);
				D = FindWord(test,0,(tokenControl & ONLY_LOWERCASE) ?  PRIMARY_CASE_ALLOWED : STANDARD_LOOKUP);
				*hyphen = '-';
				if (D) 
				{
					wordStarts[i] = reuseAllocation(wordStarts[i],D->word);
					--i;
				}
			}
			fixedSpell = true;
			continue; // ignore hypenated errors that we couldnt solve, because no one mistypes a hypen
		}
		
		// leave uppercase in first position if not adjusted yet
		if (IsUpperCase(word[0])  && tokenControl & NO_PROPER_SPELLCHECK) 
			continue; 

		if (*word != '\'' && (!FindCanonical(word, i,true) || IsUpperCase(word[0]))) // dont check quoted or findable words unless they are capitalized
		{
			word = SpellCheck(i);

			// dont spell check proper names to improper, if word before or after is lower case originally
			if (word && i != 1 && originalCapState[i] && !IsUpperCase(*word))
			{
				if (!originalCapState[i-1]) return false;
				else if (i != wordCount && !originalCapState[i+1]) return false;
			}

			if (word && !*word) // performed substitution on prior word, restart this one
			{
				fixedSpell = true;
				--i;
				continue;
			}
			if (word) 
			{
				wordStarts[i] = reuseAllocation(wordStarts[i],word);
				fixedSpell = true;
				continue;
			}
		}
    }
	return fixedSpell;
}

unsigned int EditDistance(WORDP D, unsigned int size, unsigned int inputLen, char* inputSet, unsigned int min,unsigned char realWordLetterCounts[LETTERMAX])
{//   dictword has no underscores, inputSet is already lower case
    char dictw[MAX_WORD_SIZE];
    MakeLowerCopy(dictw,D->word);
    char* dictinfo = dictw;
    char* dictstart = dictinfo;
    unsigned int val = 0; //   a difference in length will manifest as a difference in letter count
    //   how many changes  (change a letter, transpose adj letters, insert letter, drop letter)
    if (size != inputLen) 
	{
		val += (size < inputLen) ? 5 : 2;	// real word is shorter than what they typed, not so likely as longer
		if (size < 7) val += 3;	
	}
    //   first and last letter errors are rare, more likely to get them right
    if (*dictinfo != *inputSet) val += 6; // costs a lot  to change first letter, odds are he types that right 
    if (dictinfo[size-1] != inputSet[inputLen-1]) val += 6; // costs more to change last letter, odds are he types that right or sees its wrong
    if (val > min) return 60;	// fast abort
	
	// match off how many letter counts are correct between the two, need to be close enough to bother with
	unsigned char dictWordLetterSet[LETTERMAX];
 	memset(dictWordLetterSet,0,LETTERMAX); 
	for (unsigned int  i = 0; i < size; ++i) 
	{
		int index = letterIndexData[(unsigned char)dictinfo[i]];
		++dictWordLetterSet[index]; // computer number of each kind of letter
	}
	unsigned int count = 0;
	for (unsigned int  i = 0; i < LETTERMAX; ++i) // count how many letters are the same in both words
	{
		if (dictWordLetterSet[i]) // revised word has these many
		{
			int diff = dictWordLetterSet[i] - realWordLetterCounts[i]; // how many of ours does real have?
			if (diff < 0) count += dictWordLetterSet[i]; // he has more than we have, he gets credit for ours he does have
			else count += dictWordLetterSet[i] - diff; // he has <= what we have, count them
		}
	}
	unsigned int countVariation = size - ((size > 7) ? 3 : 2); // since size >= 2, this is always >= 0
	if (count < countVariation)  return 60;	// need most letters be in common
	if (count == size)  // same letters (though he may have excess) --  how many transposes
	{
		unsigned int bad = 0;
		for (unsigned int i = 0; i < size; ++i) if (dictinfo[i] != inputSet[i]) ++bad;
		if (size != inputLen){;}
		else if (bad <= 2) return val + 3; // 1 transpose
		else if (bad <= 4) return val + 9; // 2 transpose
		else return val + 38; // many transpose
    }
	
	// now look at specific letter errors
    char* dictend = dictinfo+size;
    char* inputend = inputSet+inputLen;
	count = 0;
    while (ALWAYS)
    {
		++count;
        if (*dictinfo == *inputSet) // match
        {
            if (inputSet == inputend && dictinfo == dictend) break;    // ended
            ++inputSet;
            ++dictinfo;
            continue;
        }
        if (inputSet == inputend || dictinfo == dictend) // one ending, other has to catch up by adding a letter
        {
            if (inputSet == inputend) ++dictinfo;
            else ++inputSet;
            val += 6;
            continue;
        }

        //   letter match failed

        //   try to resynch series and reduce cost of a transposition of adj letters  
        if (*dictinfo == inputSet[1] && dictinfo[1] == *inputSet) // transpose 
        {
			if (dictinfo[2] == inputSet[2]) // they match after, so transpose is pretty likely
			{
				val += 4;  
				if (dictinfo[2]) // not at end, skip the letter in synch for speed
				{
					++dictinfo;
					++inputSet;
				}
			}
			else val += 8;  // transposed maybe good, assume it is
   			dictinfo += 2;
			inputSet += 2;
		}
        else if (*dictinfo == inputSet[1]) // current dict letter matches matches his next input letter, so maybe his input inserted a char here and need to delete it 
        {
            char* prior = inputSet-1; // potential extraneous letter
            if (*prior == *inputSet) val += 5; // low cost for dropping an excess repeated letter - start of word is prepadded with 0 for prior char
            else if (*inputSet == '-') val += 3; //   very low cost for removing a hypen 
            else if (inputSet+1 == inputend && *inputSet == 's') val += 30;    // losing a trailing s is almost not acceptable
            else val += 9; //  high cost removing an extra letter, but not as much as having to change it
            ++inputSet;
		}
        else if (dictinfo[1] == *inputSet) // next dict leter matches current input letter, so maybe his input deleted a char here and needs to insert  it
        {
            char* prior = (dictinfo == dictstart) ? (char*)" " : (dictinfo-1);
            if (*dictinfo == *prior  && !IsVowel(*dictinfo )) val += 5; 
            else if (IsVowel(*dictinfo ))  val += 1; //  low cost for missing a vowel ( already charged for short input), might be a texting abbreviation
            else val += 9; // high cost for deleting a character, but not as much as changing it
            ++dictinfo;
       }
       else //   this has no valid neighbors.  alter it to be the correct, but charge for multiple occurences
       {
			if (count == 1 && *dictinfo != *inputSet) val += 30; //costs a lot to change the first letter, odds are he types that right or sees its wrong
			//  2 in a row are bad, check for a substituted vowel sound
			bool swap = false;
			unsigned int oldval = val;
			if (dictinfo[1] != inputSet[1])
			{
				if (*inputSet == 't' && !strncmp(dictinfo,"ght",3)) 
				{
                    dictinfo += 3;
                    inputSet += 1;
                    val += 5;  
				}
				else if (!strncmp(inputSet,"ci",2) && !strncmp(dictinfo,"cki",3)) 
				{
                    dictinfo += 3;
                    inputSet += 2;
                    val += 5;
				}
				else if (*(dictinfo-1) == 'a' && !strcmp(dictinfo,"ir") && !strcmp(inputSet,"re")) // prepair prepare as terminal sound
				{
                    dictinfo += 2;
                    inputSet += 2;
                    val += 3;
				}
				else if (!strncmp(inputSet,"ous",3) && !strncmp(dictinfo,"eous",4)) 
				{
                    dictinfo += 4;
                    inputSet += 3;
                    val += 5; 
               }
              else if (!strncmp(inputSet,"of",2) && !strncmp(dictinfo,"oph",3)) 
               {
                    dictinfo += 3;
                    inputSet += 2;
                    val += 5; 
               }
             else if (*dictinfo == 'x' && !strncmp(inputSet,"cks",3)) 
               {
                    dictinfo += 1;
                    inputSet += 3;
                    val += 5; 
               }
               else if (*inputSet == 'k' && !strncmp(dictinfo,"qu",2)) 
               {
                    dictinfo += 2;
                    inputSet += 1;
                    val += 5;  
               }
			   if (oldval != val){;} // swallowed a multiple letter sound change
               else if (!strncmp(dictinfo,"able",4) && !strncmp(inputSet,"ible",4)) swap = true;
               else if (!strncmp(dictinfo,"ible",4) && !strncmp(inputSet,"able",4)) swap = true;
               else if (*dictinfo == 'a' && dictinfo[1] == 'y'     && *inputSet == 'e' && inputSet[1] == 'i') swap = true;
               else if (*dictinfo == 'e' && dictinfo[1] == 'a'     && *inputSet == 'e' && inputSet[1] == 'e') swap = true;
               else if (*dictinfo == 'e' && dictinfo[1] == 'e'     && *inputSet == 'e' && inputSet[1] == 'a') swap = true;
               else if (*dictinfo == 'e' && dictinfo[1] == 'e'     && *inputSet == 'i' && inputSet[1] == 'e') swap = true;
               else if (*dictinfo == 'e' && dictinfo[1] == 'i'     && *inputSet == 'a' && inputSet[1] == 'y') swap = true;
               else if (*dictinfo == 'e' && dictinfo[1] == 'u'     && *inputSet == 'o' && inputSet[1] == 'o') swap = true;
               else if (*dictinfo == 'e' && dictinfo[1] == 'u'     && *inputSet == 'o' && inputSet[1] == 'u') swap = true;
               else if (*dictinfo == 'i' && dictinfo[1] == 'e'     && *inputSet == 'e' && inputSet[1] == 'e') swap = true;
               else if (*dictinfo == 'o' && dictinfo[1] == 'o'     && *inputSet == 'e' && inputSet[1] == 'u') swap = true;
               else if (*dictinfo == 'o' && dictinfo[1] == 'o'     && *inputSet == 'o' && inputSet[1] == 'u') swap = true;
               else if (*dictinfo == 'o' && dictinfo[1] == 'o'     && *inputSet == 'u' && inputSet[1] == 'i') swap = true;
               else if (*dictinfo == 'o' && dictinfo[1] == 'u'     && *inputSet == 'e' && inputSet[1] == 'u') swap = true;
               else if (*dictinfo == 'o' && dictinfo[1] == 'u'     && *inputSet == 'o' && inputSet[1] == 'o') swap = true;
               else if (*dictinfo == 'u' && dictinfo[1] == 'i'     && *inputSet == 'o' && inputSet[1] == 'o') swap = true;
               if (swap)
               {
                    dictinfo += 2;
                    inputSet += 2;
                    val += 5; 
               }
            } 

            // can we change a letter to another similar letter
            if (oldval == val) 
            {
				bool convert = false;
                if (*dictinfo == 'i' && *inputSet== 'y' && count > 1) convert = true;//   but not as first letter
                else if ((*dictinfo == 's' && *inputSet == 'z') || (*dictinfo == 'z' && *inputSet == 's')) convert = true;
                else if (*dictinfo == 'y' && *inputSet == 'i' && count > 1) convert = true; //   but not as first letter
                else if (*dictinfo == '/' && *inputSet == '-') convert = true;
                else if (inputSet+1 == inputend && *inputSet == 's') val += 30;    //   changing a trailing s is almost not acceptable
                if (convert) val += 5;	// low cost for exchange of similar letter, but dont do it often
                else val += 12;			// changing a letter is expensive, since it destroys the visual image
                ++dictinfo;
                ++inputSet;
            }
       } 
       if (val > min) return val; // too costly, ignore it
    }
    return val;
}

static char* StemSpell(char* word,unsigned int i)
{
    static char word1[MAX_WORD_SIZE];
    strcpy(word1,word);
    size_t len = strlen(word);

	char* ending = NULL;
    char* best = NULL;
    
	//   suffixes
	if (len < 5){;} // too small to have a suffix we care about (suffix == 2 at min)
    else if (!strnicmp(word+len-3,"ing",3))
    {
        word1[len-3] = 0;
        best = SpellFix(word1,0,VERB); 
        if (best && FindWord(best,0,LOWERCASE_LOOKUP)) return English_GetPresentParticiple(best);
	}
    else if (!strnicmp(word+len-2,"ed",2))
    {
        word1[len-2] = 0;
        best = SpellFix(word1,0,VERB); 
        if (best)
        {
			char* past = English_GetPastTense(best);
			if (!past) return NULL;
			size_t len = strlen(past);
			if (past[len-1] == 'd') return past;
			ending = "ed";
        }
    }
	else
	{
		unsigned int i = 0;
		char* suffix;
		while ((suffix = stems[i].word))
		{
			uint64 kind = stems[i++].flags;
			size_t len = strlen(suffix);
			if (!strnicmp(word+len-len,suffix,len))
			{
				word1[len-len] = 0;
				best = SpellFix(word1,0,kind); 
				if (best) 
				{
					ending = suffix;
					break;
				}
			}
		}
	}
	if (!ending && word[len-1] == 's')
    {
        word1[len-1] = 0;
        best = SpellFix(word1,0,VERB|NOUN); 
        if (best)
        {
			WORDP F = FindWord(best,0,(tokenControl & ONLY_LOWERCASE) ?  PRIMARY_CASE_ALLOWED : STANDARD_LOOKUP);
			if (F && F->properties & NOUN) return English_GetPluralNoun(F);
			ending = "s";
        }
   }
   if (ending)
   {
		strcpy(word1,best);
		strcat(word1,ending);
		return word1;
   }
   return NULL;
}

char* SpellFix(char* originalWord,unsigned int start,uint64 posflags)
{
    size_t len = strlen(originalWord);
	if (len >= 100 || len == 0) return NULL;
	if (IsDigit(*originalWord)) return NULL; // number-based words and numbers must be treated elsewhere
	char letterLow = GetLowercaseData(*originalWord);
	char letterHigh = GetUppercaseData(*originalWord);
	bool hasUnderscore = (strchr(originalWord,'_')) ? true : false;
	bool isUpper = IsUpperCase(originalWord[0]);
	if (IsUpperCase(originalWord[1])) isUpper = false;	// not if all caps
	if (trace == TRACE_SPELLING) Log(STDUSERLOG,"Spell: %s\r\n",originalWord);

	char word[MAX_WORD_SIZE];
	MakeLowerCopy(word,originalWord);

	// mark positions of the letters and make lower case
    char base[257];
    memset(base,0,257);
    char* ptr = word - 1;
    char c;
    int position = 0;
    while ((c = *++ptr) && position < 255)
    {
        base[position++ + 1] = GetLowercaseData(c);
   }

	//   Priority is to a word that looks like what the user typed, because the user probably would have noticed if it didnt and changed it. So add/delete  has priority over tranform
    WORDP choices[4000];
    WORDP bestGuess[4000];
    unsigned int index = 0;
    unsigned int bestGuessindex = 0;
    unsigned int min = 30;
	unsigned char realWordLetterCounts[LETTERMAX];
	memset(realWordLetterCounts,0,LETTERMAX); 
	for (unsigned int  i = 0; i < len; ++i)  ++realWordLetterCounts[(unsigned char)letterIndexData[(unsigned char)word[i]]]; // compute number of each kind of character
	
	uint64  pos = PART_OF_SPEECH;  // all pos allowed
    WORDP D;
    if (posflags == PART_OF_SPEECH && start < wordCount) // see if we can restrict word based on next word
    {
        D = FindWord(wordStarts[start+1],0,PRIMARY_CASE_ALLOWED);
        uint64 flags = (D) ? D->properties : (-1); //   if we dont know the word, it could be anything
        if (flags & PREPOSITION) pos &= -1 ^ (PREPOSITION|NOUN);   //   prep cannot be preceeded by noun or prep
        if (!(flags & (PREPOSITION|VERB|CONJUNCTION|ADVERB)) && flags & DETERMINER) pos &= -1 ^ (DETERMINER|ADJECTIVE|NOUN|ADJECTIVE_NUMBER|NOUN_NUMBER); //   determiner cannot be preceeded by noun determiner adjective
        if (!(flags & (PREPOSITION|VERB|CONJUNCTION|DETERMINER|ADVERB)) && flags & ADJECTIVE) pos &= -1 ^ (NOUN); 
        if (!(flags & (PREPOSITION|NOUN|CONJUNCTION|DETERMINER|ADVERB|ADJECTIVE)) && flags & VERB) pos &= -1 ^ (VERB); //   we know all helper verbs we might be
        if (D && *D->word == '\'' && D->word[1] == 's' ) pos &= NOUN;    //   we can only be a noun if possessive - contracted 's should already be removed by now
    }
    if (posflags == PART_OF_SPEECH && start > 1)
    {
        D = FindWord(wordStarts[start-1],0,PRIMARY_CASE_ALLOWED);
        uint64 flags = (D) ? D->properties : (-1); // if we dont know the word, it could be anything
        if (flags & DETERMINER) pos &= -1 ^ (VERB|CONJUNCTION|PREPOSITION|DETERMINER);  
    }
    posflags &= pos; //   if pos types are known and restricted and dont match
	static int range[] = {0,-1,1};
	for (unsigned int i = 0; i < 3; ++i)
	{
		MEANING offset = lengthLists[len + range[i]];
		if (trace == TRACE_SPELLING) Log(STDUSERLOG,"\r\n  Begin offset %d\r\n",i);
		while (offset)
		{
			D = Meaning2Word(offset);
			offset = D->spellNode;
			if (!(D->properties & posflags)) continue; // wrong kind of word
			if (*D->word != letterLow && *D->word != letterHigh) continue;	// we assume no one misspells starting letter
			char* under = strchr(D->word,'_');
			if (hasUnderscore && !under) continue;	 // require keep any underscore
			if (!hasUnderscore && under) continue;	 // require not have any underscore
			if (isUpper && !(D->internalBits & UPPERCASE_HASH) && start != 1) continue;	// dont spell check to lower a word in upper
			unsigned int val = EditDistance(D, D->length, len, base+1,min,realWordLetterCounts);
			if (val <= min) // as good or better
			{
				if (val < min)
				{
					if (trace == TRACE_SPELLING) Log(STDUSERLOG,"    Better: %s against %s value: %d\r\n",D->word,originalWord,val);
					index = 0;
					min = val;
				}
				else if ( val == min && trace == TRACE_SPELLING) Log(STDUSERLOG,"    Equal: %s against %s value: %d\r\n",D->word,originalWord,val);

				if (!(D->internalBits & BEEN_HERE)) 
				{
					choices[index++] = D;
					if (index > 3998) break; 
					AddInternalFlag(D,BEEN_HERE);
				}
			}
		}
	}
	// try endings ing, s, etc
	if (start) // no stem spell if COMING from a stem spell attempt (start == 0)
	{
		char* stem = StemSpell(word,start);
		if (stem) 
		{
			WORDP D = FindWord(stem,0,(tokenControl & ONLY_LOWERCASE) ?  PRIMARY_CASE_ALLOWED : STANDARD_LOOKUP);
			if (D) 
			{
				for (unsigned int j = 0; j < index; ++j) 
				{
					if (choices[j] == D) // already in our list
					{
						D = NULL; 
						break;
					}
				}
			}
			if (D) choices[index++] = D;
		}
	}

    if (!index)  return NULL; 

	// take our guesses, and pick the most common (earliest learned or most frequently used) word
    uint64 commonmin = 0;
    bestGuess[0] = NULL;
	for (unsigned int j = 0; j < index; ++j) RemoveInternalFlag(choices[j],BEEN_HERE);
    if (index == 1) 
	{
		if (trace == TRACE_SPELLING) Log(STDUSERLOG,"    Single best spell: %s\r\n",choices[0]->word);
		return choices[0]->word;	// pick the one
	}
    for (unsigned int j = 0; j < index; ++j) 
    {
        uint64 common = choices[j]->systemFlags & COMMONNESS;
        if (common < commonmin) continue;
		if (choices[j]->internalBits & UPPERCASE_HASH && index > 1) continue;	// ignore proper names for spell better when some other choice exists
        if (common > commonmin)
        {
            commonmin = common;
            bestGuessindex = 0;
        }
        bestGuess[bestGuessindex++] = choices[j];
    }
	if (bestGuessindex) 
	{
		if (trace == TRACE_SPELLING) Log(STDUSERLOG,"    Pick spell: %s\r\n",bestGuess[0]->word);
		return bestGuess[0]->word; 
	}
	return NULL;
}

