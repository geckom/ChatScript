#include "common.h"

#ifdef INFORMATION
SPACES		 space \t \r \n 
PUNCTUATIONS  , | -  (see also ENDERS)
ENDERS		 . ; : ? ! -
BRACKETS 	 () [ ] { } < >
ARITHMETICS	  % * + - ^ = / .  
SYMBOLS 	  $ # @ ~  
CONVERTERS	  & `
//NORMALS 	  A-Z a-z 0-9 _  and sometimes / 
#endif

int inputNest = 0;

#define MAX_BURST 400
static char burstWords[MAX_BURST][MAX_WORD_SIZE];	// each token burst from a text string
static unsigned int burstLimit = 0;					// index of burst  words
char* joinBuffer;									// buffer for joinwords function		

uint64 tokenFlags;										// what tokenization saw
char* wordStarts[MAX_SENTENCE_LENGTH];				// current sentence tokenization (always points to D->word values or allocated values)
unsigned int wordCount;								// how many words/tokens in sentence
bool capState[MAX_SENTENCE_LENGTH];					
bool originalCapState[MAX_SENTENCE_LENGTH];			// was input word capitalized by user
char* tokenPool[MAX_SENTENCE_LENGTH];				// reuse token allocation space when possible

void ResetTokenSystem()
{
	tokenFlags = 0;
	wordStarts[0] = reuseAllocation(0,"");    
    wordCount = 0;
}

void DumpResponseControls(uint64 val)
{
	if (val & RESPONSE_UPPERSTART) Log(STDUSERLOG,"RESPONSE_UPPERSTART ");
	if (val & RESPONSE_REMOVESPACEBEFORECOMMA) Log(STDUSERLOG,"RESPONSE_REMOVESPACEBEFORECOMMA ");
	if (val & RESPONSE_ALTERUNDERSCORES) Log(STDUSERLOG,"RESPONSE_ALTERUNDERSCORES ");
}

void DumpTokenControls(uint64 val)
{
	if ((val & DO_SUBSTITUTE_SYSTEM) == DO_SUBSTITUTE_SYSTEM) Log(STDUSERLOG,"DO_SUBSTITUTE_SYSTEM ");
	else // partials
	{
		if (val & DO_ESSENTIALS) Log(STDUSERLOG,"DO_ESSENTIALS ");
		if (val & DO_SUBSTITUTES) Log(STDUSERLOG,"DO_SUBSTITUTES ");
		if (val & DO_CONTRACTIONS) Log(STDUSERLOG,"DO_CONTRACTIONS ");
		if (val & DO_INTERJECTIONS) Log(STDUSERLOG,"DO_INTERJECTIONS ");
		if (val & DO_BRITISH) Log(STDUSERLOG,"DO_BRITISH ");
		if (val & DO_SPELLING) Log(STDUSERLOG,"DO_SPELLING ");
		if (val & DO_TEXTING) Log(STDUSERLOG,"DO_TEXTING ");
		if (val & DO_NOISE) Log(STDUSERLOG,"DO_NOISE ");
	}
	if (val & DO_PRIVATE) Log(STDUSERLOG,"DO_PRIVATE ");
	// reserved
	if (val & DO_NUMBER_MERGE) Log(STDUSERLOG,"DO_NUMBER_MERGE ");
	if (val & DO_PROPERNAME_MERGE) Log(STDUSERLOG,"DO_PROPERNAME_MERGE ");
	if (val & DO_DATE_MERGE) Log(STDUSERLOG,"DO_DATE_MERGE ");
	if (val & NO_PROPER_SPELLCHECK) Log(STDUSERLOG,"NO_PROPER_SPELLCHECK ");
	if (val & DO_SPELLCHECK) Log(STDUSERLOG,"DO_SPELLCHECK ");
	if (val & DO_INTERJECTION_SPLITTING) Log(STDUSERLOG,"DO_INTERJECTION_SPLITTING ");

	if ((val & DO_PARSE) == DO_PARSE) Log(STDUSERLOG,"DO_PARSE ");
	else if (val & DO_POSTAG) Log(STDUSERLOG,"DO_POSTAG ");
	
	if (val & NO_IMPERATIVE) Log(STDUSERLOG,"NO_IMPERATIVE ");
	if (val & NO_WITHIN) Log(STDUSERLOG,"NO_WITHIN ");
	if (val & NO_SENTENCE_END) Log(STDUSERLOG,"NO_SENTENCE_END ");
	if (val & NO_HYPHEN_END) Log(STDUSERLOG,"NO_HYPHEN_END ");
	if (val & NO_COLON_END) Log(STDUSERLOG,"NO_COLON_END ");
	if (val & NO_SEMICOLON_END) Log(STDUSERLOG,"NO_SEMICOLON_END ");
	if (val & STRICT_CASING) Log(STDUSERLOG,"STRICT_CASING ");
	if (val & ONLY_LOWERCASE) Log(STDUSERLOG,"ONLY_LOWERCASE ");
	if (val & TOKEN_AS_IS) Log(STDUSERLOG,"TOKEN_AS_IS ");
	if (val & SPLIT_QUOTE) Log(STDUSERLOG,"SPLIT_QUOTE ");
	if (val & UNTOUCHED_INPUT) Log(STDUSERLOG,"UNTOUCHED_INPUT ");
}

void DumpTokenFlags(char* msg)
{
	Log(STDUSERLOG,"%s TokenFlags: ",msg);
	// DID THESE
	if (tokenFlags & DO_ESSENTIALS) Log(STDUSERLOG,"DO_ESSENTIALS ");
	if (tokenFlags & DO_SUBSTITUTES) Log(STDUSERLOG,"DO_SUBSTITUTES ");
	if (tokenFlags & DO_CONTRACTIONS) Log(STDUSERLOG,"DO_CONTRACTIONS ");
	if (tokenFlags & DO_INTERJECTIONS) Log(STDUSERLOG,"DO_INTERJECTIONS ");
	if (tokenFlags & DO_BRITISH) Log(STDUSERLOG,"DO_BRITISH ");
	if (tokenFlags & DO_SPELLING) Log(STDUSERLOG,"DO_SPELLING ");
	if (tokenFlags & DO_TEXTING) Log(STDUSERLOG,"DO_TEXTING ");
	if (tokenFlags & DO_PRIVATE) Log(STDUSERLOG,"DO_PRIVATE ");
	// reserved
	if (tokenFlags & DO_NUMBER_MERGE) Log(STDUSERLOG,"NUMBER_MERGE ");
	if (tokenFlags & DO_PROPERNAME_MERGE) Log(STDUSERLOG,"PROPERNAME_MERGE ");
	if (tokenFlags & DO_DATE_MERGE) Log(STDUSERLOG,"DATE_MERGE ");
	if (tokenFlags & DO_SPELLCHECK) Log(STDUSERLOG,"SPELLCHECK ");
	// FOUND THESE
	if (tokenFlags & NO_HYPHEN_END) Log(STDUSERLOG,"HYPHEN_END ");
	if (tokenFlags & NO_COLON_END) Log(STDUSERLOG,"COLON_END ");
	if (tokenFlags & PRESENT) Log(STDUSERLOG,"PRESENT ");
	if (tokenFlags & PAST) Log(STDUSERLOG,"PAST ");
	if (tokenFlags & FUTURE) Log(STDUSERLOG,"FUTURE ");
	if (tokenFlags & PERFECT) Log(STDUSERLOG,"PERFECT ");
	if (tokenFlags & PRESENT_PERFECT) Log(STDUSERLOG,"PRESENT_PERFECT ");
	if (tokenFlags & CONTINUOUS) Log(STDUSERLOG,"CONTINUOUS ");
	if (tokenFlags & PASSIVE) Log(STDUSERLOG,"PASSIVE ");

	if (tokenFlags & QUESTIONMARK) Log(STDUSERLOG,"QUESTIONMARK ");
	if (tokenFlags & EXCLAMATIONMARK) Log(STDUSERLOG,"EXCLAMATIONMARK ");
	if (tokenFlags & PERIODMARK) Log(STDUSERLOG,"PERIODMARK ");
	if (tokenFlags & USERINPUT) Log(STDUSERLOG,"USERINPUT ");
	if (tokenFlags & FAULTY_PARSE) Log(STDUSERLOG,"FAULTY_PARSE ");
	if (tokenFlags & COMMANDMARK) Log(STDUSERLOG,"COMMANDMARK ");
	if (tokenFlags & QUOTATION) Log(STDUSERLOG,"QUOTATION ");
	if (tokenFlags & IMPLIED_YOU) Log(STDUSERLOG,"IMPLIED_YOU ");
	if (tokenFlags & NOT_SENTENCE) Log(STDUSERLOG,"NOT_SENTENCE ");
	if (inputNest) Log(STDUSERLOG," ^input ");
	Log(STDUSERLOG,"\r\n");
}

// BUG see if . allowed in word 

int ValidPeriodToken(char* start, char* end, char next,char next2) // token with period in it - classify it
{ //  TOKEN_INCLUSIVE means completes word   TOKEN_EXCLUSIVE not part of word.    TOKEN_INCOMPLETE  means embedded in word but word not yet done
	size_t len = end - start;
	if (IsAlphaUTF8(next) && tokenControl & TOKEN_AS_IS) return TOKEN_INCOMPLETE;
	if (IsDigit(next)) return TOKEN_INCOMPLETE;
	if (len > 100) return TOKEN_EXCLUSIVE; // makes no sense
	if (len == 2) // letter period combo like H.
	{
		char* next = SkipWhitespace(start + 2);
		if (IsUpperCase(*next) || !*next) return TOKEN_INCLUSIVE;	// Letter period like E. before a name
	}
	if (IsWhiteSpace(next) && IsDigit(*start)) return TOKEN_EXCLUSIVE;	// assume no one uses float period without a digit after it.
	if (FindWord(start,len)) return TOKEN_INCLUSIVE;	// nov.  recognized by system for later use
	if (IsMadeOfInitials(start,end) == ABBREVIATION) return TOKEN_INCLUSIVE; //   word of initials is ok
	if (IsUrl(start,end)) 
	{
		if (*(end-1) == ']' || *(end-1) == ')') return TOKEN_INCOMPLETE; // bruce@job.net]
		return TOKEN_INCLUSIVE; //   swallow URL as a whole
	}
	if (!strnicmp("no.",start,3) && IsDigit(next)) return TOKEN_INCLUSIVE; //   no.8  
	if (!strnicmp("no.",start,3)) return TOKEN_INCLUSIVE; //   sentence: No.
	if (!IsDigit(*start) && len > 3 && *(end-3) == '.') return TOKEN_INCLUSIVE; // p.a._system
	if (FindWord(start,len-1)) return TOKEN_EXCLUSIVE; // word exists independent of it

	// is part of a word but word not yet done
    if (IsFloat(start,end) && IsDigit(next)) return TOKEN_INCOMPLETE; //   decimal number9
	if (*start == '$' && IsFloat(start+1,end) && IsDigit(next)) return TOKEN_INCOMPLETE; //   decimal number9 or money
	if (IsNumericDate(start,end)) return TOKEN_INCOMPLETE;	//   swallow period date as a whole - bug . after it?
	if ( next == '-') return TOKEN_INCOMPLETE;	// like N.J.-based

	//  not part of word, will be stand alone token.
	return TOKEN_EXCLUSIVE;
}


////////////////////////////////////////////////////////////////////////
// BURSTING CODE
////////////////////////////////////////////////////////////////////////

int BurstWord(char* word, int contractionStyle) 
{
#ifdef INFORMATION
	BurstWord, at a minimum, separates the argument into words based on internal whitespace and internal sentence punctuation.
	This is done for storing "sentences" as fact callArgumentList.
	Movie titles extend this to split off possessive endings of nouns. Bob's becomes Bob_'s. 
	Movie titles may contain contractions. These are not split, but two forms of the title have to be stored, the 
	original and one spot contractions have be expanded, which refines to the original.
	And in full burst mode it splits off contractions as well (why- who uses it).

#endif
	//   concept and class names do not burst, regular or quoted, nor do we waste time if word is 1-2 characters, or if quoted string and NOBURST requested
	if (!word[1] || !word[2] || *word == '~' || (*word == '\'' && word[1] == '~' ) || (contractionStyle & NOBURST && *word == '"')) 
	{
		strcpy(burstWords[0],word);
		return 1;
	}

	//   make it safe to write on the data while separating things
	char* copy = AllocateBuffer();
	strcpy(copy,word);
	word = copy;
	unsigned int base = 0;

	//   eliminate quote kind of things around it
    if (*word == '"' || *word == '\'' || *word == '*' || *word == '.')
    {
       size_t len = strlen(word);
       if (len > 2 &&  word[len-1] == *word) // start and end same and has something between
       {
           word[len-1] = 0;  // remove trailing quote
           ++word;
       }
   }

	bool underscoreSeen = false;
	char* start = word;
	while (*++word) // locate spaces of words, and 's 'd 'll 
	{
        if (*word == ' ' || *word == '_' || (*word == '-' && contractionStyle == HYPHENS)) //   these bound words for sure
        {
			if (*word == '_') underscoreSeen = true;
            if (!word[1]) break;  // end of coming up.

			char* end = word;  
			int len = end-start;
			char* prior = (end-1); // ptr to last char of word
			char priorchar = *prior;

			// separate punctuation from token except if it is initials or abbrev of some kind
			if (priorchar == ',' || IsPunctuation(priorchar) & ENDERS) //   - : ; ? !     ,
			{
				char next = *end;
				char next2 = (next) ? *SkipWhitespace(end+1) : 0;
				if (len <= 1){;}
				else if (priorchar == '.' && ValidPeriodToken(start,end,next,next2) != TOKEN_EXCLUSIVE){;} //   dont want to burst titles or abbreviations period from them
				else  // punctuation not a part of token
				{
					*prior = 0; // not a singleton character, remove it
					--len; // better not be here with -fore  (len = 0)
				}
			}

			// copy off the word we burst
            strncpy(burstWords[base],start,len);
			burstWords[base++][len] = 0;
			if (base > (MAX_BURST - 5)) break; //   protect excess

			//   add trailing punctuation if any was removed
			if (!*prior)
			{
				 *burstWords[base] = priorchar;
				 burstWords[base++][1] = 0;
			}

			//   now resume after
            start = word + 1;
            while (*start == ' ' || *start == '_') ++start;  // skip any excess blanks of either kind
            word = start - 1;
        }
		else if (*word == '\'' && contractionStyle & (POSSESSIVES|CONTRACTIONS)) //  possible word boundary by split of contraction or possession
        {
            int split = 0;
            if (word[1] == 0 || word[1] == ' '  || word[1] == '_') split = 1;  //   ' at end of word
            else if (word[1] == 's' && (word[2] == 0 || word[2] == ' ' || word[2] == '_')) split = 2;  //   's at end of word
			else if (!(contractionStyle & CONTRACTIONS)) {;} // only accepting possessives
            else if (word[1] == 'm' && (word[2] == 0 || word[2] == ' '  || word[2] == '_')) split = 2;  //   'm at end of word
            else if (word[1] == 't' && (word[2] == 0 || word[2] == ' '  || word[2] == '_')) split = 2;  //   't at end of word
            else if ((word[1] == 'r' || word[2] == 'v') && word[2] == 'e' && (word[3] == 0 || word[3] == ' '  || word[3] == '_')) split = 3; //    're 've
            else if (word[1] == 'l'  && word[2] == 'l' && (word[3] == 0 || word[3] == ' '  || word[3] == '_')) split = 3; //    'll
            if (split) 
            {
				//  swallow any word before
				if (*start != '\'')
				{
					int len = word - start;
					strncpy(burstWords[base],start,len);
					burstWords[base++][len] = 0;
					start = word;
				}
	
				// swallow apostrophe chunk as unique word, aim at the blank after it
				word += split;
				int len = word - start;
				strncpy(burstWords[base],start,len);
				burstWords[base++][len] = 0;

				start = word;
				if (!*word) break;	//   we are done, show we are at end of line
				if (base > MAX_BURST - 5) break; //   protect excess
                ++start; // set start to go for next word+
            }
       }
    }

	// now handle end of last piece
    if (start && *start && *start != ' ' && *start != '_') strcpy(burstWords[base++],start); // a trailing 's or '  won't have any followup word left
	if (!base && underscoreSeen) strcpy(burstWords[base++],"_");
	else if (!base) strcpy(burstWords[base++],start);

	FreeBuffer();
	burstLimit = base;	// note legality of burst word accessor GetBurstWord
    return base;
}

char* GetBurstWord(unsigned int n) //   0-based
{
	if (n >= burstLimit) 
	{
		ReportBug("Bad burst n %d",n)
		return "";
	}
	return burstWords[n];
}

char* JoinWords(unsigned int n,bool output)
{
    *joinBuffer = 0;
	char* at = joinBuffer;
    for (unsigned int i = 0; i < n; ++i)
    {
		char* hold = burstWords[i];
		if (!hold) break;
        if (!output && (*hold == ',' || *hold == '?' || *hold == '!' || *hold == ':')) // for output, dont space before punctuation
        {
            if (joinBuffer != at) *--at = 0; //   remove the understore before it
        } 
		size_t len = strlen(hold);
		if ((len + 4 + (at - joinBuffer)) >= maxBufferSize) break;	 // avoid overflow
        strcpy(at,hold);
		at += len;
        if (i != (n-1)) strcpy(at++,"_");
    }
    return joinBuffer;
}

////////////////////////////////////////////////////////////////////////
// BASIC TOKENIZING CODE
////////////////////////////////////////////////////////////////////////

static void TokenizeQuoteToUnderscore(char* start, char* end, char* buffer)
{//   start and end are the marker characters
	*end = 0;	//   remove trailing quote
	char* tmp = AllocateBuffer();
	strcpy(tmp,start);
	start = tmp;
	char* wordlist[MAX_SENTENCE_LENGTH];
	memset(wordlist,0,sizeof(char*)*MAX_SENTENCE_LENGTH); // empty it
	++start; // past the " start
	unsigned int loops = 0;
	while (start && *start)
	{
		unsigned int index;
		char* rest = Tokenize(start,index,wordlist,true);
		for (unsigned int i = 1; i <= index; ++i)
		{
			strcpy(buffer,wordlist[i]);
			buffer += strlen(buffer);
			if (i != index) *buffer++ = '_'; 
		}
		start = rest;
		++loops;
	}
	FreeBuffer();
}

static char* HandleQuoter(char* ptr,char** words, int& count)
{
	char c = *ptr; // kind of quoter
	char* end = strchr(ptr+1,c); // find matching end?
	if (!end) return NULL; 
	char pastEnd = IsPunctuation(end[1]); // what comes AFTER quote
	if (!(pastEnd & (SPACES|PUNCTUATIONS|ENDERS))) return NULL;	// doesnt end cleanly

	// if quote has a tailing comma or period, move it outside of the end - "Pirates of the Caribbean,"  -- violates NOMODIFY clause if any
	char priorc = *(end-1);
	if (priorc == ',' || priorc == '.')
	{
		*(end-1) = *end;
		*end-- = priorc;
	}

	if (c == '*') // stage direction notation, erase it and return to normal processing
	{
		*ptr = ' ';
		*end = ' ';		// erase the closing * of a stage direction -- but violates a nomodify clause
		return ptr;		// skip opening *
	}
	
	// strip off the quotes if quoted words are only alphanumeric single words (emphasis quoting)
	char* at = ptr;
	while (++at < end)
	{
		if (!IsAlphaUTF8OrDigit(*at) ) // worth quoting, unless it is final char and an ender
		{
			if (at == (end-1) && IsPunctuation(*at) & ENDERS);
			else // store string as properly tokenized, NOT as a string.
			{
				char* buf = AllocateBuffer();
				char word[MAX_WORD_SIZE];
				++end; // subsume the closing marker
				strncpy(word,ptr,end-ptr);
				word[end-ptr] = 0;
				TokenizeQuoteToUnderscore(word,end-ptr-1+word,buf);
				++count;
				words[count] = reuseAllocation(words[count],buf); 
				if (!words[count]) words[count] = reuseAllocation(words[count],"a"); // safe replacement
				FreeBuffer();
				return end;
			}
		}
	}
	++count;
	words[count] = reuseAllocation(words[count],ptr+1,end-ptr-1); // stripped quotes off simple word
	if (!words[count]) words[count] = reuseAllocation(words[count],"a"); // safe replacement
	return  end + 1;
}

static char* FindWordEnd(char* ptr,char* priorToken,char** words,int &count,bool nomodify, bool oobStart)
{
	char c = *ptr; 
	unsigned char kind = IsPunctuation(c);
	char* end  = NULL;
	static bool quotepending = false;
	if (kind & QUOTERS) // quoted strings 
	{
		if (c == '\'' && ptr[1] == 's' && !IsAlphaUTF8(ptr[2])) return ptr+2;	// 's directly
		if (c == '"' ) 
		{
			if (tokenControl & SPLIT_QUOTE) return ptr + 1; // split up quote marks
			else // see if merely highlighting a word
			{
				char word[MAX_WORD_SIZE];
				char* tail = ReadCompiledWord(ptr,word);
				char* close = strchr(word+1,'"');
				if (close && !strchr(word,' ')) // we dont need quotes
				{
					if (tokenControl & LEAVE_QUOTE) return tail;
					*ptr = ' ';			// kill off starting dq
					ptr[close-word] = ' ';	// kill off closing dq
					return ptr;
				}
			}
		}
		if (c == '\'' && tokenControl & SPLIT_QUOTE ) // 'enemies of the state'
		{
			if (quotepending) quotepending = false;
			else if (strchr(ptr+1,'\'')) quotepending = true;
			return ptr + 1;
		}
		if (c == '\'' && !(tokenControl & TOKEN_AS_IS) && !IsAlphaUTF8(ptr[1])  && !IsDigit(ptr[1])) 	return ptr + 1; // is this quote or apostrophe - for penntag dont touch it - for 've  leave it alone also leave '82 alone
		else if (c == '\''  && tokenControl & TOKEN_AS_IS) {;} // for penntag dont touch it - for 've  leave it alone also leave '82 alone
		else if ( c == '"' && tokenControl & TOKEN_AS_IS) return ptr + 1;
		else
		{
			char* end = HandleQuoter(ptr,words,count);
			if (end)  return end;
		}
	}

	// OOB only separates ( [ { ) ] }   - the rest remain joined as given
	if (oobStart) // support JSON parsing
	{
		if (*ptr == '(' || *ptr == ')' || *ptr == '[' || *ptr == ']' || *ptr == '{' || *ptr == '}'  || *ptr == ',' ) return ptr + 1;
		while (*++ptr != ' ' &&  *ptr != '(' && *ptr != ')' && *ptr != '[' && *ptr != ']'  && *ptr != '{' && *ptr != '}');
		return ptr;
	}

	// single letter abbreviaion period like H.
	if (IsAlphaUTF8(*ptr) && ptr[1] == '.' && ptr[2] == ' ' && IsUpperCase(*ptr)) return ptr+2;
	if (*ptr == '.' && ptr[1] == '.' && ptr[2] == '.' && ptr[3] != '.') return ptr+3;
	if (*ptr == '-' && ptr[1] == '-' && ptr[2] == '-') ptr[2] = ' ';	// change excess to space
	if (*ptr == '-' && ptr[1] == '-' && (ptr[2] == ' ' || IsAlphaUTF8(ptr[2]) )) return ptr + 2; // the -- break
	if (*ptr == ';' && ptr[1] != ')' && ptr[1] == '(') return ptr + 1; // semicolon not emoticon
	if (*ptr == ',' && ptr[1] != ':') return ptr + 1; // comma not emoticon

	// Things that are normally separated as single character tokens
	char next = ptr[1];
	if (kind & BRACKETS && ( (c != '>' && c != '<') || next != '=') ) 
	{
		if (c == '<' && next == '/') return ptr + 2; // keep html together  </
		if (c == '[' && next == '[') return ptr + 2; // keep html together  [[
		if (c == ']' && next == ']') return ptr + 2; // keep html together  ]]
		if (c == '{' && next == '{') return ptr + 2; // keep html together  {{
		if (c == '}' && next == '}') return ptr + 2; // keep html together  }}
		return ptr+1; // keep all brackets () [] {} <> separate but  <= and >= are operations
	}
	else if (c == '=' && next == '=') // swallow headers == ==== ===== etc
	{
		while (*++ptr == '='){;}
		return ptr;
	}
	else if (c == '\'' && next == '\'' && ptr[2] == '\'' && ptr[3] == '\'') return ptr + 4;	// '''' marker
	else if (c == '\'' && next == '\'' && ptr[2] == '\'') return ptr + 3;	// ''' marker
	else if (c == '\'' && next == '\'') return ptr + 2;	// '' marker
	else if (c == '\'' && next == '\'') return ptr + 2;	// '' marker
	else if (c == '&' && !(tokenControl & TOKEN_AS_IS))  //  we need to change this to "and"
	{
		++count;
		words[count] = reuseAllocation(words[count],"and"); 
		return ptr + 1;
	}
	//   arithmetic operator between numbers -  . won't be seen because would have been swallowed already if part of a float, 
	else if ((kind & ARITHMETICS || c == 'x' || c == 'X') && IsDigit(*priorToken) && IsDigit(next)) 
	{
		return ptr+1;  // separate operators from number
	}
	//   normal punctuation separation
	else if (c == '.' && IsDigit(ptr[1]));	// float start like .24
	else if (c == '.' && (ptr[1] == '"' || ptr[1] == '\'')) return ptr + 1;	// let it end after closing quote
	if (c == '.' && ptr[1] == '.' && ptr[2] == '.')  // stop at .. or ...   stand alone punctuation 
	{
		if (tokenControl & TOKEN_AS_IS) 
			return ptr + 3;
		return ptr+1;
	}
	else if (*ptr == ',') return ptr+1; 
 	else if (kind & (ENDERS|PUNCTUATIONS) && ((unsigned char)IsPunctuation(ptr[1]) == SPACES || ptr[1] == 0)) return ptr+1; 

	//   find "normal" word end, including all touching nonwhitespace, keeping periods (since can be part of word) but not ? or ! which cant
 	end = ptr;
	char* stopper = NULL;
	char* fullstopper = NULL;
	if (*ptr != ':' && *ptr != ';') while (*++end && !IsWhiteSpace(*end) && *end != '!' && *end != '?')
	{
		if (*end == ',') 
		{
			if (!IsDigit(end[1]) || !IsDigit(* (end-1))) // not comma within a number
			{
				if (!fullstopper) fullstopper = end;
				if (!stopper) stopper = end;
			}
			continue;
		}
		if (*end == ';' && !stopper) stopper = end;
		if (*end == '-' && !(tokenControl & TOKEN_AS_IS) && !stopper) stopper = end; // alternate possible end  (e.g. 8.4-ounce)
		if (*end == ';' && !fullstopper) fullstopper = end; // alternate possible end  (e.g. 8.4-ounce)
		if (end[0] == '.' && end[1] == '.' && end[2] == '.') break; // ...
	}
	if (end == ptr) ++end;	// must shift at least 1
	WORDP X = FindWord(ptr,end-ptr);
	if (X && (X->properties & PART_OF_SPEECH || X->systemFlags & PATTERN_WORD || X->internalBits & HAS_SUBSTITUTE)) // we know this word (with exceptions)
	{
		// if ' follows a number, make it feet
		if (*ptr == '\'' && (end-ptr) == 1)
		{
			if (IsDigit(*priorToken))
			{
				++count;
				words[count] = reuseAllocation(words[count],"foot"); 
				return end;
			}
		}

		// but No. must not be recognized unless followed by a digit
		else if (!strnicmp(ptr,"no.",end-ptr))
		{
			char* at = end;
			if (*at) while (*++at && *at == ' ');
			if (IsDigit(*at)) return end;
		}

		else return end;
	}

	// possessive ending? swallow whole token like "K-9's"
	if (*(end-1) == 's' && (end-ptr) > 2 && *(end-2) == '\'') return end - 2;

	//  e-mail, needs to not see - as a stopper.
	WORDP W = (fullstopper) ? FindWord(ptr,fullstopper-ptr) : NULL;
	if (*end && IsDigit(end[1]) && IsDigit(*(end-1))) W = NULL; // if , separating digits, DONT break at it  4,000 even though we recognize subpiece
	if (W && (W->properties & PART_OF_SPEECH || W->systemFlags & PATTERN_WORD))  return fullstopper; // recognize word at more splits

	// recognize subword? now in case - is a stopper
	W = (stopper && (stopper-ptr) > 1 && ((*stopper != '-' && *stopper != '/') || !IsAlphaUTF8(stopper[1]))) ? FindWord(ptr,stopper-ptr) : NULL;
	if (*end == '-' && IsAlphaUTF8(end[1])) W = NULL; // but don't split -  in a name or word 
	else if (*end && IsDigit(end[1]) && IsDigit(*(end-1))) W = NULL; // if , separating digits, DONT break at it  4,000 even though we recognize subpiece
	if (W && (W->properties & PART_OF_SPEECH || W->systemFlags & PATTERN_WORD))  return stopper; // recognize word at more splits

	char* start = ptr;
	char next2;
	while (++ptr && !IsWordTerminator(*ptr)) // now scan to find end of token one by one, stopping where appropriate
    {
		unsigned int len = end - ptr;
		c = *ptr;
		kind = IsPunctuation(c);
		next = ptr[1];
		if (c == '\'' && next == '\'') break;	// '' marker or ''' or ''''
		else if (c == '=' && next == '=') break; // swallow headers == ==== ===== etc
		next2 = (next) ? *SkipWhitespace(ptr+2) : 0; // start of next token
		if (c == '-' && next == '-') break; // -- in middle is a break regardless
		if (tokenControl & TOKEN_AS_IS) {;}
		else
		{
			if (c == '\'') //   possessive ' or 's  - we separate ' or 's into own word
			{
				if (next == ',' || IsWhiteSpace(next) || next == ';' || next == '.' || next == '!' || next == '?') // trailing plural?
				{
					break; 
				}
				if (!IsAlphaUTF8OrDigit(next)) break;					//   ' not within a word, ending it
				if (((next == 's') || ( next == 'S')) && !IsAlphaUTF8OrDigit(ptr[2]))  //   's becomes separate - can be WRONG when used as contraction like speaker's but we cant know
				{
					ptr[1] = 's'; // in case uppercase flaw
					break;	
				}
				// ' as particle ellision
				if ((ptr-start) == 1 && (*start == 'd' || *start == 'j' || *start == 'l' || *start == 's'  || *start == 't')) return ptr + 1;  // break off d' argent and other foreign particles
			
				//   12'6" or 12'. or 12' 
				if (IsDigit(*start) && !IsAlphaUTF8(next)) return ptr + 1;  //   12' swallow ' into number word
			}
			else if (ptr != start && c == ':' && IsDigit(next) && IsDigit(*(ptr-1)) && len > 1) //   time 10:30 or odds 1:3
			{
				if (!strnicmp(end-2,"am",2)) return end-2;
				else if (!strnicmp(end-2,"pm",2)) return end-2;
				else if (len > 2 && !strnicmp(end-3,"a.m",3)) return end-3;
				else if (len > 2 && !strnicmp(end-3,"p.m",3)) return end-3;
				else if (len > 3 && !strnicmp(end-4,"a.m.",4)) return end-4;
				else if (len > 3 && !strnicmp(end-4,"p.m.",4)) return end-4;
			} 
			else if (c == '-') // - used as measure separator or arithmetic
			{
				if (IsDigit(*start) && IsDigit(next)) break; // minus
				if ((next == 'x' || next == 'X') && ptr[2] == '-') // measure like 2ft-x-5ft
				{
					ptr[2] = ' ';
					*ptr = ' ';
					break;
				}
				else if ((IsDigit(*start) || (*start == '.' && IsDigit(start[1]))) && IsAlphaUTF8(next) && !(tokenControl & TOKEN_AS_IS)) // break apart measures like 4-ft except when penntag strict casing
				{
					*ptr = ' ';
					break;	//   treat as space
				}
				else if (next == '-' ) 
					break; // the anyways-- break 
			}
			if (( c == ']' || c == ')')) 
				break; //closers
			if (c == '&') break; // must represent "and" 
			if (ptr != start && IsDigit(*(ptr-1)) && IsWordTerminator(ptr[1]) && (c == '"' || c == '\'' || c == '%')) break; // special markers on trailing end of numbers get broken off. 50' and 50" and 50%
			if ((c == 'x' || c== 'X') && IsDigit(*start) && IsDigit(next)) break; // break  4x4
			if (kind & ARITHMETICS && IsDigit(next) && c != '/' && c != '.' && IsDigit(*start) && !(tokenControl & TOKEN_AS_IS)) break;  // split numeric operator like  60*2 => 60 * 2  but 60 1/2 stays // 1+1=
		}

		if (kind & BRACKETS) break; // separate brackets

		if (kind & (PUNCTUATIONS|ENDERS) && IsWordTerminator(next)) 
		{
			if (c == '-' && *ptr == '-' && next == ' ') return ptr + 1;
			if (tokenControl & TOKEN_AS_IS && next == ' ' && ptr[1] && !IsWhiteSpace(ptr[2])) return ptr + 1; // our token ends and there is more text to come
			if (!(tokenControl & TOKEN_AS_IS)) break; // funny things at end of word
		}
		if (c == '/' && IsNumericDate(start,end)) return end; //  return entire token as date   12/20/1993  

		// special interpretations of period
		if (c == '.') 
        {
			int x = ValidPeriodToken(start,end,next,next2);
			if (x == TOKEN_INCLUSIVE) return end;
			else if (x == TOKEN_INCOMPLETE) continue;
			else break;
        }
	}
	if (*(ptr-1) == '"' && start != (ptr-1)) --ptr;// trailing double quote stuck on something else
    return ptr;
}

char* Tokenize(char* input,unsigned int &mycount,char** words,bool all,bool nomodify) //   return ptr to stuff to continue analyzing later
{	// all is true if to pay no attention to end of sentence -- eg for a quoted string
	// nomodify is true on analyzing outputs into sentences, because user format may be fixed
    char* ptr = SkipWhitespace(input);
	int count = 0;

	bool oobStart = true;

	if (tokenControl == UNTOUCHED_INPUT)
	{
		while (ALWAYS) {
			input = SkipWhitespace(input);
			char* space = strchr(input,' '); // find separator
			if (space) {
				++count;
				words[count] = reuseAllocation(words[count],input,space-input); // the token
				input = space;
			}
			else if (*input) {
				++count;
				words[count] = reuseAllocation(words[count],input,strlen(input)); // the token
				input += strlen(input);
				break;
			}
			else break;
		}
		mycount = count;
		return input;
	}

	// convert html data
	char* html = input;
	while ((html = strstr(html,"&#")) != 0) // &#32;
	{
		if (IsDigit(html[2]) && IsDigit(html[3]) && html[4] == ';')
		{
			*html = (char)atoi(html+2);
			memmove(html+1,html+5,strlen(html+4));
		}
		else ++html;
	}
	unsigned int quoteCount = 0;
	char priorToken[MAX_WORD_SIZE];
	*priorToken = 0;
	int nest = 0;
	unsigned int paren = 0;
	while (ptr) // find tokens til end of sentence or end of tokens
	{
		if (!*ptr) break; 

		//test input added markers
		if (*ptr == '`') // internal marker from ^input
		{
			++ptr;
			if (*ptr == '`') ++ptr;
			if (*ptr == ' ') ++ptr;
			continue;
		}

		if (!(tokenControl & TOKEN_AS_IS)) while (*ptr == ptr[1] && !IsAlphaUTF8OrDigit(*ptr)  && *ptr != '-' && *ptr != '.' && *ptr != '[' && *ptr != ']' && *ptr != '(' && 
			*ptr != ')' && *ptr != '{' && *ptr != '}') ++ptr; // ignore repeated non-alpha non-digit characters -   - but NOT -- and not ...
		if (count == 0 && *ptr != '[' ) oobStart = false;

		// find end of word 
		int oldCount = count;
		char* end = FindWordEnd(ptr,priorToken,words,count,nomodify,oobStart); 
		if (count != oldCount || *ptr == ' ')	// FindWordEnd performed allocation already or removed stage direction start
		{
			ptr = SkipWhitespace(end);
			continue;
		}

		// get the token
		size_t len = end - ptr;
		strncpy(priorToken,ptr,len);
		priorToken[len] = 0;
		char lastc = *(end-1);
		if (*priorToken == '(') ++paren;
		else if (*priorToken && paren) --paren;

		// alter 's standalone to is
		if (!stricmp(priorToken,"'s") && *(ptr-1) == ' ') 
			priorToken[0] = 'i';

		// adjust am and AM if used as a time reference and not the verb "am"
		if (!stricmp(priorToken,"am") && count && IsDigit(words[count][0])) 
		{
			strcpy(priorToken,"a.m."); 
			len = 4;
			lastc = '.';
		}

		char startc = *priorToken;

		//   reserve next word, unless we have too many
		if (++count > REAL_SENTENCE_LIMIT ) 
		{
			mycount = REAL_SENTENCE_LIMIT;
			return ptr;
		}

		//   handle symbols for feet and inches by expanding them
		if (!(tokenControl & TOKEN_AS_IS) && IsDigit(startc) &&  (lastc == '\'' || lastc == '"'))
		{
			char* word = reuseAllocation(0,ptr,len-1);  // number w/o the '
			if (word) words[count] = word;
			++count;
			words[count] = reuseAllocation(words[count], (lastc == '"') ? (char*) "feet": (char*)"inches" ); // spell out the notation
			ptr = SkipWhitespace(end);
			continue;
		}

		//   if the word is a quoted expression, see if we KNOW it already as a noun, if so, remove quotes
		if (*priorToken == '"' && len > 2)
		{
			char buffer[MAX_WORD_SIZE];
			strcpy(buffer,priorToken);
			ForceUnderscores(buffer);
			WORDP E = FindWord(buffer+1,len-2); // do we know this unquoted?
			if (E && E->properties & PART_OF_SPEECH) strcpy(priorToken,E->word);
		}

		// assign token
 		char* token = words[count] = reuseAllocation(words[count],priorToken,len);   
		if (!token) token = words[count] = reuseAllocation(words[count],"a"); 
		else if (len == 1 && startc == 'i') *token = 'I'; // force upper case on I
		if (count == 1 && *token == '[' && !token[1]) oobStart = true; // special tokenizing rules

		//   set up for next token or ending tokenization
		ptr = SkipWhitespace(end);

		if (*token == '"' && (count == 1 || !IsDigit(*words[count-1] ))) ++quoteCount;
		if (*token == '"' && count > 1 && quoteCount && !(quoteCount & 1)) // does end of this quote end the sentence?
		{
			char c = words[count-1][0];
			if (*ptr == ',' || c == ',') {;} // comma after or inside means not at end
			else if (*ptr && IsLowerCase(*ptr)){;} // sentence continues
			else if (c == '!' || c == '?' || c == '.') break;	 // internal punctuation ends the sentence
		}
		
		if (*token == '(' && !token[1]) ++nest;
		else if (*token == ')' && !token[1]) --nest;
		else if (*token == '[' && !token[1]) ++nest;
		else if (*token == ']' && !token[1]) --nest;

		if (*ptr == ')' && nest == 1){;}
		else if (*ptr == ']' && nest == 1){;}
		else if (tokenControl & TOKEN_AS_IS) {;} // penn bank input already broken up as sentences
		else if (all || tokenControl & NO_SENTENCE_END || startc == ',' || token[1]){;}	// keep going - ) for closing whatever
		else if ( (count > 1 && *token == '\'' && ( (*words[count-1] == '.' && !words[count-1][1]) || *words[count-1] == '!' || *words[count-1] == '?'))) break; // end here
		else if (IsPunctuation(startc) & ENDERS || (startc == ']' && *words[1] == '[' && !nest)) //   done a sentence or oob fragment
		{
			if (quoteCount & 1) continue;	// cannot end quotation w/o quote mark at end
			// each punctuation ender can be separately controlled
			if (startc == '-')
			{
				if (IsDigit(*ptr)) {;} // is minus 
				else if (!(tokenControl & NO_HYPHEN_END)) // we dont want hypen to end it anyway
				{
					*token = '.';
					tokenFlags |= NO_HYPHEN_END;
					break;
				}
			}
			else if (startc == ':' && !paren)
			{
				if (!strstr(ptr," and ") || strchr(ptr,',')) {;}	// guess : is a list - could be wrong guess
				else if (!(tokenControl & NO_COLON_END))			// we dont want colon to end it anyway
				{
					tokenFlags |= NO_COLON_END;
					break;
				}
			}
			else if (startc == ';'  && !paren)
			{
				if (!(tokenControl & NO_SEMICOLON_END))  // we dont want semicolon to end it anyway
				{
					tokenFlags |= NO_SEMICOLON_END;
					break;
				}
			}
			else if (*ptr == '"' || *ptr == '\'') continue;
			else break;	// []  ? and !  and  .  are mandatory unless NO_SENTENCE_END used
		}
	}
	words[count+1] = reuseAllocation(words[count+1],"");	// mark as empty

	// if all is a quote, remove quotes if it is just around a single word
	if (count == 3 && *words[1] == '"' && *words[count] == '"')
	{
		memmove(words,words+1,count * sizeof(char*)); // move all down
		count -= 2;
	}
	// if all is a quote, remove quotes if it is just around a single word
	else if (count  == 3 && *words[1] == '\'' && *words[count] == '\'')
	{
		memmove(words,words+1,count * sizeof(char*)); // move all down
		count -= 2;
	}
	mycount = count;
	return ptr;
}


////////////////////////////////////////////////////////////////////////
// POST PROCESSING CODE
////////////////////////////////////////////////////////////////////////

static WORDP MergeProperNoun(int& start, int end,bool upperStart) 
{ // end is inclusive
	WORDP D;
	uint64 gender = 0;
	char buffer[MAX_WORD_SIZE];
	*buffer = 0;
	// build composite name
	    char* ptr = buffer;
	bool uppercase = false;
	bool name = false;
	if (IsUpperCase(*wordStarts[start]) && IsUpperCase(*wordStarts[end])) uppercase = true;	// MUST BE UPPER
    for (int i = start; i <= end; ++i)
    {
		char* word = wordStarts[i];
        size_t len = strlen(word);
        if (*word == ',' ||*word == '?' ||*word == '!' ||*word == ':')  
		{
			if (i != start) *--ptr = 0;  //   remove the understore before it 
		}
		else
		{
			// locate known sex of word if any, composite will inherit it
			D = FindWord(word,len,LOWERCASE_LOOKUP);
			if (D) gender |= D->properties & (NOUN_HE|NOUN_SHE|NOUN_HUMAN|NOUN_PROPER_SINGULAR);
 			D = FindWord(word,len,UPPERCASE_LOOKUP);
			if (D) 
			{
				gender |= D->properties & (NOUN_HE|NOUN_SHE|NOUN_HUMAN|NOUN_PROPER_SINGULAR);
				if (D->properties & NOUN_FIRSTNAME) name = true;
			}
		}

        strcpy(ptr,word);
        ptr += len;
        if (i < end) *ptr++ = '_'; // more to go
    }
	*buffer = GetUppercaseData(*buffer); // start it as uppercase

	D = FindWord(buffer,0,UPPERCASE_LOOKUP); // if we know the word in upper case
	// see if adding in determiner or title to name
	if (start > 1) // see if determiner before is known, like The Fray or Title like Mr.
	{
		WORDP E = FindWord(wordStarts[start-1],0,UPPERCASE_LOOKUP); // the word before
		if (E && !(E->properties & NOUN_TITLE_OF_ADDRESS)) E = NULL; 
		// if not a title of address is it a determiner?  "The" is most common
		if (!E) 
		{
			E = FindWord(wordStarts[start-1],0,LOWERCASE_LOOKUP);
			if (E && !(E->properties & DETERMINER)) E = NULL;
		}
		if (E) // known title of address or determiner? See if we know the composite word includes it - like the Rolling Stones is actually The_Rolling_Stones
		{
			char buffer1[MAX_WORD_SIZE];
			strcpy(buffer1,E->word);
			*buffer1 = GetUppercaseData(*buffer1); 
			strcat(buffer1,"_");
			strcat(buffer1,buffer);
			if (E->properties & DETERMINER) // if determine is part of name, revise to include it
			{
				WORDP F = FindWord(buffer1);
				if (F) 
				{
					--start;
					D = F; 
				}
			}
			else if (tokenControl & STRICT_CASING && IsUpperCase(*buffer) && IsLowerCase(*wordStarts[start-1])){;} // cannot mix lower title in
			else //   accept title as part of unknown name automatically
			{
				strcpy(buffer,buffer1);
				D = FindWord(buffer);
				--start;
			}
		}
	}
	if ((end - start)  == 0) return NULL;	// dont bother, we already have this word in the sentence
	if (!D && upperStart) 
	{
		WORDP X = FindWord(buffer,0,LOWERCASE_LOOKUP);
		if (X) D = X; // if we know it in lower case, use that since we dont know the uppercase one - eg "Artificial Intelligence"
		else 
		{
			D = FindWord(buffer,0,UPPERCASE_LOOKUP);
			if (D && D->systemFlags & LOCATIONWORD) gender = 0; // a place, not a name
			else D = StoreWord(buffer,gender|NOUN_PROPER_SINGULAR|NOUN);
		}
	}
	if (D && (D->properties & gender) != gender) AddProperty(D,gender); // wont work when dictionary is locked
	if (!D && !upperStart) return NULL; // neither known in upper case nor does he try to create it
	if (D && D->systemFlags & ALWAYS_PROPER_NAME_MERGE) return D;
	if (name) return D; // use known capitalization  - it has a first name
	if (uppercase) return D;
	return NULL; // let SetSequenceStamp find it instead
}

static bool HasCaps(char* word)
{
    if (IsMadeOfInitials(word,word+strlen(word)) == ABBREVIATION) return true;
    if (!IsUpperCase(*word) || strlen(word) == 1) return false;
    while (*++word)
    {
        if (!IsUpperCase(*word)) return true; // do not allow all caps as such a word
    }
    return false;
}

static int FinishName(int& start, int& end, bool upperStart,uint64 kind,WORDP name)
{ // start is beginning of sequence, end is on the sequence last word. i is where to continue outside after having done this one
	
    if (end == UNINIT) end = start;
	if (upperStart == false && start == 1 && end == (int)wordCount && IsUpperCase(*wordStarts[start])) upperStart = true; // assume he meant it if only literally that as sentence (eg header)
	
    //   a 1-word title gets no change. also
	if (end == (int)wordCount && start == 1 && (!IsUpperCase(*wordStarts[end]) || !IsUpperCase(*wordStarts[start]) ) && end < 5 && (!name || !(name->systemFlags & ALWAYS_PROPER_NAME_MERGE))) {;} //  entire short sentence gets ignored
	else if ( (end-start) < 1 ){;}  
	else //   make title
	{
		WORDP E = MergeProperNoun(start,end,upperStart);
		if (E) 
		{
			AddSystemFlag(E,kind); // if timeword 
			//   replace multiple words with single word
			wordStarts[start] = reuseAllocation(wordStarts[start],E->word);
			memmove(wordStarts+start+1,wordStarts+end+1,sizeof(char*) * (wordCount - end));
			wordCount -= (end - start);
		}
		tokenFlags |= DO_PROPERNAME_MERGE;
	}
	int result = start + 1;
	start = end = UNINIT;
	return result; // continue AFTER here
}

static void HandleFirstWord() // Handle capitalization of starting word of sentence
{
	if (*wordStarts[1] == '"') return; // dont touch a quoted thing

	// look at it in upper case first
    WORDP D = FindWord(wordStarts[1],0,UPPERCASE_LOOKUP); // Known in upper case?
	if (D && D->properties & (NOUN|PRONOUN_BITS)) return;	// upper case is fine for nouns and pronoun I

	// look at it in lower case
	WORDP E = FindWord(wordStarts[1],0,LOWERCASE_LOOKUP); 
	WORDP N;
	char word[MAX_WORD_SIZE];
	MakeLowerCopy(word,wordStarts[1]);
	char* noun = English_GetSingularNoun(word,true,true);
	
	if (D && !E && !IsUpperCase(*wordStarts[1]) && D->properties & NOUN_PROPER_SINGULAR)  wordStarts[1] = reuseAllocation(wordStarts[1],D->word); // have upper but not lower, use upper if not plural
	else if (!IsUpperCase(*wordStarts[1])) return; // dont change what is already ok, dont want unnecessary trace output
	else if (noun && !stricmp(word,noun)) wordStarts[1] = reuseAllocation(wordStarts[1],StoreWord(noun)->word); // lower case form is the singular form already - use that whether he gave us upper or lower
	else if (E && E->properties & (CONJUNCTION|PRONOUN_BITS|PREPOSITION)) wordStarts[1] = reuseAllocation(wordStarts[1],E->word); // simple word lower case, use it
	else if (E && E->properties & AUX_VERB && (N = FindWord(wordStarts[2])) && (N->properties & (PRONOUN_BITS | NOUN_BITS) || English_GetSingularNoun(wordStarts[2],true,false))) wordStarts[1] = reuseAllocation(wordStarts[1],E->word); // potential aux before obvious noun/pronoun, use lower case of it

	// see if multiple word (like composite name)
	char* multi = strchr(wordStarts[1],'_');
	if (!D && !E && !multi) return;  // UNKNOWN word in any case (probably a name)
	if (E && E->internalBits & HAS_SUBSTITUTE){;}
	else if (!multi || !IsUpperCase(multi[1])) // remove sentence start uppercase if known in lower case unless its a multi-word title or substitute
	{
		char word[MAX_WORD_SIZE];
		MakeLowerCopy(word,wordStarts[1]);
		if (FindWord(word,0,LOWERCASE_LOOKUP)) wordStarts[1] = reuseAllocation(wordStarts[1],StoreWord(word)->word);  // BEFORE:  DAHINDA was converted to lower case by this.
	}
	else if (multi) wordStarts[1] = reuseAllocation(wordStarts[1],StoreWord(wordStarts[1],NOUN_PROPER_SINGULAR)->word); // implied proper noun of some kind
}

bool DateZone(unsigned int i, int& start, int& end)
{
	WORDP D = FindWord(wordStarts[i],0,UPPERCASE_LOOKUP);
	if (!D || !(D->systemFlags & MONTH)) return false;
	start = i;
	end = i;
	if (i > 1 && IsDigit(*wordStarts[i-1]) && atoi(wordStarts[i-1]) < 32) start = i-1;
	else if (i < wordCount && IsDigit(*wordStarts[i+1]) && atoi(wordStarts[i+1]) < 32) end = i+1;
	else if (i > 2 && !stricmp(wordStarts[i-1],"of") && IsDigit(*wordStarts[i-2])) start = i-2;
	// dont merge "*the 2nd of april" because it might be "the 2nd of April meeting"
	if (end < (int)wordCount)
	{
		char* next = wordStarts[end+1];
		if (IsDigit(*next++) && IsDigit(*next++) &&IsDigit(*next++) && IsDigit(*next++) && !*next) ++end;	// swallow year
		else if (*wordStarts[end+1] == ',')
		{
			char* next = wordStarts[end+2];
			if (IsDigit(*next++) && IsDigit(*next++) &&IsDigit(*next++) && IsDigit(*next++) && !*next) end += 2;	// swallow comma year
		}
	}
	return (start != end); // there is something there
}

void ProcessCompositeDate()
{
    for (int i = FindOOBEnd(1); (unsigned int)i <= wordCount; ++i) 
	{
		int start,end;
		if (DateZone(i,start,end))
		{
			char word[MAX_WORD_SIZE];
			strcpy(word,wordStarts[i]); // force month first
			word[0] = toUppercaseData[*word]; // insure upper case
			int at = start - 1;
			while (++at <= end)
			{
				if (at != i && stricmp(wordStarts[at],"of"))
				{
					strcat(word,"_");
					strcat(word,wordStarts[at]);
					if (IsDigit(*wordStarts[at]))
					{
						size_t len = strlen(word);
						if (!IsDigit(word[len-1]) && IsDigit(word[len-3])) word[len-2] = 0; // 1st, 2nd, etc
					}
				}
			}
			WORDP D = StoreWord(word,NOUN|NOUN_PROPER_SINGULAR);
			wordStarts[start] = reuseAllocation(wordStarts[start],D->word);
			AddSystemFlag(D,TIMEWORD|MONTH);
			int diff = end - start;  // will be 2-4 words listing as shrunk 1-3 words
			memmove(wordStarts+start+1,wordStarts+end+1,sizeof(char*) * (wordCount - end + 1)); // 1 excess
			wordCount -= diff;
			tokenFlags |= DO_DATE_MERGE;
		}
	}
}

void ProcessCompositeName() 
{
	if (tokenControl & ONLY_LOWERCASE) return;

    int start = UNINIT;
    int end = UNINIT;
    uint64 kind = 0;
	bool upperStart = false;

    for (int i = FindOOBEnd(1); (unsigned int)i <= wordCount; ++i) 
    {
		char* word = wordStarts[i];
		if (*word == '"' || (strchr(word,'_') && !IsUpperCase(word[0])) || strchr(word,':')) // we never join composite words onto proper names unless the composite is proper already
		{
			if (start != UNINIT)  i = FinishName(start,end,upperStart,kind,NULL); // we have a name started, finish it off
			continue;
		}
		WORDP Z = FindWord(word,0,UPPERCASE_LOOKUP);
		if (IsUpperCase(*word) && Z && Z->systemFlags & NO_PROPER_MERGE)
		{
			if (start != UNINIT) i = FinishName(start,end,upperStart,kind,Z);
			continue;
		}
			
		// check for easy cases of 2 words in a row being a known uppercase word
		if (start == UNINIT && i != (int)wordCount && *wordStarts[i+1] != '"')
		{
			char composite[MAX_WORD_SIZE];
			strcpy(composite,wordStarts[i]);
			strcat(composite,"_");
			strcat(composite,wordStarts[i+1]);
			Z = FindWord(composite,0,UPPERCASE_LOOKUP);
			if (Z && Z->systemFlags & NO_PROPER_MERGE) Z = NULL;
			if (tokenControl & (ONLY_LOWERCASE|STRICT_CASING) && IsLowerCase(*composite)) Z = NULL;	// refuse to see word
			if (Z && Z->properties & NOUN) 
			{
				end = i + 1;
				if (Z->properties & NOUN_TITLE_OF_WORK && i != end && !IsUpperCase(*wordStarts[i+1])) // dont automerge title names the "The Cat", let sequences find them and keep words separate when not intended
				{
					start = end = UNINIT;
					continue;
				}
				else
				{
					i = FinishName(i,end,false,0,Z);
					continue;
				}
			}
			// now add easy triple
			if ((unsigned int)(i + 2) <= wordCount&& *wordStarts[i+2] != '"')
			{
				strcat(composite,"_");
				strcat(composite,wordStarts[i+2]);
				Z = FindWord(composite,0,UPPERCASE_LOOKUP);
				if (tokenControl & STRICT_CASING && IsLowerCase(*composite)) Z = NULL;	// refuse to see word
				if (Z && Z->systemFlags & NO_PROPER_MERGE) Z = NULL;
				if (Z && (Z->properties & NOUN || Z->systemFlags & PATTERN_WORD)) 
				{
					end = i + 2;
					i = FinishName(i,end,false,0,Z);
					continue;
				}
			}
		}
        size_t len = strlen(word);

		WORDP nextWord  = ((unsigned int) i < wordCount) ? FindWord(wordStarts[i+1],0,UPPERCASE_LOOKUP) : NULL; // grab next word
		if (tokenControl & (ONLY_LOWERCASE|STRICT_CASING) && (unsigned int) i < wordCount && wordStarts[i+1] && IsLowerCase(*wordStarts[i+1])) nextWord = NULL;	// refuse to see word
		if (nextWord && nextWord->systemFlags & NO_PROPER_MERGE) nextWord = NULL;

  		WORDP U = FindWord(word,len,UPPERCASE_LOOKUP);
		if (tokenControl & (ONLY_LOWERCASE|STRICT_CASING) && IsLowerCase(*word)) U = NULL;	// refuse to see word
		if (U && U->systemFlags & NO_PROPER_MERGE) U = NULL;
		if (U && !(U->properties & ESSENTIAL_FLAGS)) U = NULL;	//  not a real word
		WORDP D = U; // the default word to use

		WORDP L = FindWord(word,len,LOWERCASE_LOOKUP);
		if (tokenControl & STRICT_CASING && IsUpperCase(*word)) L = NULL;	// refuse to see word
		if (L && L->systemFlags & NO_PROPER_MERGE) L = NULL;
	
		if (L && !IsUpperCase(*word)) D = L;			// has lower case meaning, he didnt cap it, assume its lower case
		else if (L && i == 1 && L->properties & (PREPOSITION | PRONOUN_BITS | CONJUNCTION) ) D = L; // start of sentence, assume these word kinds are NOT in name
		if (i == 1 && L &&  L->properties & AUX_VERB && nextWord && nextWord->properties & (PRONOUN_BITS)) continue;	// obviously its not Will You but its will they
		else if (start == UNINIT && IsLowerCase(*word) && L && L->properties & (ESSENTIAL_FLAGS|QWORD)) continue; //   he didnt capitalize it himself and its a useful word, not a proper name
		
		if (!D) D = L; //   ever heard of this word? 

		//   given human first name as starter or a title
        if (start == UNINIT && D && D->properties & (NOUN_FIRSTNAME|NOUN_TITLE_OF_ADDRESS))
        {
			upperStart = (i != 1 &&  D->internalBits & UPPERCASE_HASH) ? true : false;  // the word is upper case, so it begins a potential naming
			start = i; 
			kind = 0;
            end = UNINIT;    //   have no potential end yet
            if ((unsigned int)i < wordCount) //   have a last name? or followed by a preposition? 
            {
				size_t len1 = strlen(wordStarts[i+1]);
				WORDP F = FindWord(wordStarts[i+1],len1,LOWERCASE_LOOKUP);
				if (tokenControl & STRICT_CASING && IsUpperCase(*wordStarts[i+1])) F = NULL;	// refuse to see word
				if (F && F->properties & (CONJUNCTION | PREPOSITION | PRONOUN_BITS)) //   dont want river in the to become River in the or Paris and Rome to become Paris_and_rome
				{
					start = UNINIT;
					++i;
					continue;
				}
				
				if (nextWord && !(nextWord->properties & ESSENTIAL_FLAGS)) nextWord = NULL;		//   not real
				if (nextWord && nextWord->properties & NOUN_TITLE_OF_ADDRESS) nextWord = NULL;	//  a title of address cannot be here
				if (nextWord && nextWord->systemFlags & NO_PROPER_MERGE) nextWord = NULL;
	
                if (nextWord || IsUpperCase(*wordStarts[i+1])) //   it's either capitalized or we know it is capitalizable
                {
					upperStart = true;	//   must be valid
					if (IsLowerCase(*wordStarts[i])) //   make current word upper case, do not overwrite its shared ptr
					{
						if (!wordStarts[i]) wordStarts[i] = reuseAllocation(wordStarts[i],"a");
						else *wordStarts[i] = GetUppercaseData(*wordStarts[i]);  // safe to overwrite, since it was a fresh allocation
					}
                    ++i; 
                    continue;
                }
           }
        }

		// so much for known human name pairs. Now the general issue.
        bool intended = HasCaps(word) && i != 1;
		if (HasCaps(word) && !D) intended = true;	// unknown word which had caps. He must have meant it
        uint64 type = (D) ? (D->systemFlags & TIMEWORD) : 0; // type of word if we know it
		if (!kind) kind = type;
        else if (kind && type && kind != type) intended = false;   // cant intermix time and space words

		// National Education Association, education is a known word that should be merged but Mary, George, and Larry, shouldnt merge
		if (D && D->internalBits & UPPERCASE_HASH && GetMeanings(D)) // we KNOW this word by itself, dont try to merge it
		{
			if (start == (int)i)
			{
				end = i;
				i = FinishName(start,end,upperStart,kind,D);
			}
			continue;
		}
		
		if (i == 1 && wordCount > 1) // pay close attention to sentence starter
        {
			WORDP N = FindWord(wordStarts[2]);
			if (N && N->properties & PRONOUN_BITS) continue;	// 2nd word is a pronoun, not likely a title word
 			if (D && D->properties & (DETERMINER|QWORD)) continue;   //   ignore starting with a determiner or question word(but might have to back up later to accept it)
		}

        //   Indian food is not intended
		if (intended || (D && D->properties & (NOUN_PROPER_SINGULAR|NOUN_PROPER_PLURAL|NOUN_TITLE_OF_ADDRESS))) // cap word or proper name can start
        {
			if (D && D->properties & POSSESSIVE); // not Taiwanese President
			else if (L && L->properties & QWORD); // ignore WHO for who
            else if (start == UNINIT) //   havent started yet, start now
            {
	 			upperStart = (intended && i != 1);  //   he started it properly or not
                start = i; 
				kind = (D) ? (D->systemFlags & TIMEWORD) : 0;
            }
            if (end != UNINIT) end = UNINIT;  //   swallow a word along the way that is allowed to be lower case
        }
        else if (start != UNINIT) // lowercase may end name, unless turns out to be followed by uppercase
        {
			// Do not allow lower case particles and connectors after a comma...  Shell Oil, the Dutch group 
            if (D && D->properties & LOWERCASE_TITLE && i > 1 && *wordStarts[i-1] != ',' ) // allowable particles and connecting words that can be in lower case
			{
				if (i < (int)wordCount && !IsUpperCase(*wordStarts[i+1])) // Pluto, the dog 
				{
						i = FinishName(start,end,upperStart,kind,NULL);
						continue;
				}
				//   be careful with possessives. we dont want London's Millenium Eye to match or Taiwanese President
				if (D->properties & POSSESSIVE)
				{
					end = i - 1;	// possessive is not part of it
					i = FinishName(start,end,upperStart,kind,NULL);
				}
				WORDP G = FindWord(wordStarts[1],0,LOWERCASE_LOOKUP);
				if (start == 1 && G && G->properties & BASIC_POS && !FindWord(wordStarts[1],0,UPPERCASE_LOOKUP)) // we have a NORMAL word followed by boring word. "Principality of Monoco"
				{
					end = i - 1;	// possessive is not part of it
					i = FinishName(start,end,upperStart,kind,NULL);
				}

				continue;
			}
            if (*word == ',' && (unsigned int)i < wordCount && IsUpperCase(*wordStarts[i+1])) // comma series, but DONT allow adjective to follow ("Pluto, American astronomer" 
            {
				WORDP next = FindWord(wordStarts[i+1]);
				if (next && next->properties & (DETERMINER|ADJECTIVE_BITS)) {;}
				else
				{
					end = i;
					continue;
				}
			}
            //   Hammer, Howell, & Houton, Inc. 
			end = i - 1;
			i = FinishName(start,end,upperStart,kind,NULL);
       }
    }

    if (start != UNINIT ) // proper noun is pending 
    {
        if (end == UNINIT) end = wordCount;
		FinishName(start,end,upperStart,kind,NULL);
    }

	HandleFirstWord();
}

static void MergeNumbers(int& start,int& end) //   four score and twenty = four-score-twenty
{//   start thru end exclusive of end, but put in number power order if out of order (four and twenty becomes twenty-four)
    char word[MAX_WORD_SIZE];
    char* ptr = word;
    for (int i = start; i < end; ++i)
    {
		char* item = wordStarts[i];
        if (*item == ',') continue; //   ignore commas
		if (i > start && *item == '-') ++item; // skip leading -

        size_t len = strlen(wordStarts[i]);
		//   one thousand one hundred and twenty three
		//   OR  one and twenty 
        if (*item == 'a' || *item == 'A') //   and,  maybe flip order if first, like one and twenty, then ignore
        {
			int64 power1 = NumberPower(wordStarts[i-1]);
			int64 power2 = NumberPower(wordStarts[i+1]);
			if (power1 < power2) //   latter is bigger than former --- assume nothing before and just overwrite
			{
				strcpy(word,wordStarts[i+1]);
                ptr = word + strlen(word);
                *ptr++ = '-';
                strcpy(ptr,wordStarts[i-1]);
                ptr += strlen(ptr);
                break;
			}
			if (power1 == power2) // same granularity, don't merge, like "what is two and two"
			{
				  end = start = (unsigned int)UNINIT;
				  return;
			}
            continue;
        }

        strcpy(ptr,item);
        ptr += len;
        *ptr = 0;
        if (i != start) //   prove not mixing types digits and words
        {
            if (*word == '-' && !IsDigit(*item)) 
			{
				end = start = (unsigned int)UNINIT;
				return; //   - not a sign? CANCEL MERGE
			}
        }
        if (i < (end-1) && *item != '-') *ptr++ = '-'; //   hypenate words (not digits )
        else if (i < (end-1) && strchr(wordStarts[i+1],'/')) *ptr++ = '-'; //   is a fraction? BUG
    }
    *ptr = 0;

	//   change any _ to - (substitutions or wordnet might have merged using _
	while ((ptr = strchr(word,'_'))) *ptr = '-';

	//   create the single word and replace all the tokens
    WORDP D = StoreWord(word,ADJECTIVE|NOUN|ADJECTIVE_NUMBER|NOUN_NUMBER); 
    wordStarts[start] = reuseAllocation(wordStarts[start],D->word);
	memmove(wordStarts+start+1,wordStarts+end,sizeof(char*) * (wordCount + 1 - end ));
	wordCount -= (end - start) - 1;	//   deleting all but one of the words
	tokenFlags |= DO_NUMBER_MERGE;
    end = start = (unsigned int)UNINIT;
}

void ProcessCompositeNumber() 
{
    //  convert a series of numbers into one hypenated one and remove commas from a comma-digited string
    int start = UNINIT;
	int end = UNINIT;
	char* number;

    for (unsigned int i = FindOOBEnd(1); i <= wordCount; ++i) 
    {
        bool isNumber = IsNumber(wordStarts[i]) && !IsPlaceNumber(wordStarts[i]) && !GetCurrency(wordStarts[i],number);
		size_t len = strlen(wordStarts[i]);
        if (isNumber || (start == UNINIT && *wordStarts[i] == '-' && i < wordCount && IsDigit(*wordStarts[i+1]))) // is this a number or part of one
        {
            if (start == UNINIT) start = i;
            if (end != UNINIT) end = (unsigned int)UNINIT;
        }
        else if (start == UNINIT) continue; // nothing started
		else
        {
            if (i != wordCount && i != 1) // middle words AND and , 
			{
				// AND between words 
				if (!strnicmp("and",wordStarts[i],len)) 
				{
					end = i;
					if (!IsDigit(*wordStarts[i-1]) && !IsDigit(*wordStarts[i+1])) // potential word number 
					{
						int64 before = Convert2Integer(wordStarts[i-1]);  //  non numbers return NOT_A_NUMBER   
						int64 after = Convert2Integer(wordStarts[i+1]);
						if (after > before){;} // want them ordered--- ignore four score and twenty
						else if (before == 100 || before == 1000 || before == 1000000) continue; // one thousand and five - ten thousand and fifty
					}
				}
				// comma between digit tokens
				else if (*wordStarts[i] == ',' ) 
				{
					if (IsDigit(*wordStarts[i-1]) && IsDigit(*wordStarts[i+1])) // a numeric comma
					{
						if (strlen(wordStarts[i+1]) == 3) // after comma must be exactly 3 digits 
						{
							end = i; // potential stop
							continue;
						}
					}
				}
			}
            //   this definitely breaks the sequence
            if (end  == UNINIT) end = i;
            if ((end-start) == 1) // no change if its a 1-length item
            {
                start = end = (unsigned int)UNINIT;
                continue; 
            }

			//  numbers in  series cannot merge unless triples after the first (international like 1 222 233)
			if (IsDigit(*wordStarts[start]))
			{
				for ( int j = start + 1; j < end; ++j) 
				{
					if (strlen(wordStarts[j]) != 3 && IsDigit(*wordStarts[j])) 
					{
						start = end = UNINIT;
						break;
					}
				}
			}

            if (end != UNINIT) 
			{
				i = start; // all merge, just continue to next word now
				MergeNumbers(start,end);
			}
        }
    }

    if (start != UNINIT) //   merge is pending
    {
        if (end  == UNINIT) end = wordCount+1; // drops off the end
		int count = end-start;
        if (count > 1) 
		{
			//   dont merge a date-- number followed by comma 4 digit number - January 1, 1940
			//   and 3 , 3455 or   3 , 12   makes no sense either. Must be 3 digits past the comma
			if (IsDigit(*wordStarts[start]))
			{
				for (int j = start + 1; j < end; ++j) 
				{
					//  cannot merge numbers like 1 2 3  instead numbers after the 1st digit number must be triples (international)
					if (strlen(wordStarts[j]) != 3 && IsDigit(*wordStarts[j])) return;
				}
			}

			size_t nextLen = strlen(wordStarts[start+1]);
			if (count != 2 || !IsDigit(*wordStarts[start+1]) || nextLen == 3) MergeNumbers(start,end); 
		}
    }
}

static bool Substitute(WORDP found,char* sub, unsigned int i,unsigned int erasing)
{ //   erasing is 1 less than the number of words involved
	// see if we have test condition to process (starts with !) and has [ ] with list of words to NOT match after
	if (sub && *sub == '!')
	{
		if (*++sub != '[') // not a list, a bug
		{
			if (!stricmp(sub,"tense")) // 'd depends on tense
			{
				WORDP X = (i < wordCount) ? FindWord(wordStarts[i+1]) : 0;
				WORDP Y = (i < (wordCount-1)) ? FindWord(wordStarts[i+2]) : 0;
				if (X && X->properties & VERB_INFINITIVE)
				{
					sub = "would";
				}
				else if (X && X->properties & VERB_PAST_PARTICIPLE)
				{
					sub = "had";
				}
				else if (Y && Y->properties & VERB_INFINITIVE)
				{
					sub = "would";
				}
				else // assume pastparticple "had"
				{
					sub = "had";
				}
			}
			else
			{
				ReportBug("bad substitute %s",sub)
				return false;
			}
		}
		else
		{
			char word[MAX_WORD_SIZE];
			bool match = false;
			char* ptr = sub+1;
			while (ALWAYS)
			{
				ptr = ReadSystemToken(ptr,word);
				if (*word == ']') break;
				if ( *word == '>')
				{
					if ( i == wordCount) match = true;
				}
				else if (i < wordCount && !stricmp(wordStarts[i+1],word)) match = true;
			}
			if (match) return false;	// not to do
			sub = ptr;	// here is the thing to sub
			if (!*sub) sub = 0;
		}
	}

	unsigned int erase = 1 + (int)erasing;
	if (!sub || *sub == '%') // just delete the word or note tokenbit and then delete
	{
		if (tokenControl & TOKEN_AS_IS && *found->word != '.' &&  *found->word != '?' && *found->word != '!') // cannot tamper with word count (pennbank pretokenied stuff) except trail punctuation
		{
			return false;
		}

		if (sub && *sub == '%') 
		{
			if (trace & TRACE_SUBSTITUTE && CheckTopicTrace()) Log(STDUSERLOG,"substitute flag:  %s\r\n",sub+1);
			tokenFlags |= (int)FindValueByName(sub+1);
		}
		else if (trace & TRACE_SUBSTITUTE && CheckTopicTrace()) 
		{
			Log(STDUSERLOG,"  substitute erase:  ");
			for (unsigned int j = i; j < i+erasing+1; ++j) Log(STDUSERLOG,"%s ",wordStarts[j]);
			Log(STDUSERLOG,"\r\n");
		}	
		memmove(wordStarts+i,wordStarts+i+erasing+1,sizeof(char*) * (wordCount-i-erasing));
		wordCount -= erase;
		return true;
	}

	//   substitution match
	if (!strchr(sub,'+') && erasing == 0 && !strcmp(sub,wordStarts[i])) return false; // changing single word case to what it already is?
	
    char wordlist[MAX_WORD_SIZE];
    strcpy(wordlist,sub);
    char* ptr = wordlist;
    while ((ptr= strchr(ptr,'+'))) *ptr = ' '; // change + separators to spaces but leave _ alone

	char* tokens[MAX_SENTENCE_LENGTH];			// the new tokens we will substitute
	memset(tokens,0,sizeof(char*) * MAX_SENTENCE_LENGTH);
	char* backupTokens[MAX_SENTENCE_LENGTH];	// place to copy the old tokens
	unsigned int count;
	if (*sub == '"') // use the content internally literally - like "a_lot"  meaning want it as a single word
	{
		count = 1;
		size_t len = strlen(wordlist);
		tokens[1] = reuseAllocation(tokens[1],wordlist+1,len-2); // remove quotes from it now
		if (!tokens[1]) tokens[1] = reuseAllocation(tokens[1],"a"); 
	}
    else Tokenize(wordlist,count,tokens); // get the tokenization of the substitution

	if (count == 1 && !erasing) //   simple replacement
	{
		if (trace & TRACE_SUBSTITUTE && CheckTopicTrace()) Log(STDUSERLOG,"  substitute replace: \"%s\" with %s\r\n",wordStarts[i],tokens[1]);
		wordStarts[i] = tokens[1];
	}
	else // multi replacement
	{
		if (tokenControl & TOKEN_AS_IS && !(tokenControl & DO_SUBSTITUTES) && (DO_CONTRACTIONS & (uint64)found->internalBits) && count != erase) // cannot tamper with word count (pennbank pretokenied stuff)
		{
			return false;
		}
		if ((wordCount + (count - erase)) >= REAL_SENTENCE_LIMIT) return false;	// cant fit

		if (trace & TRACE_SUBSTITUTE && CheckTopicTrace()) Log(STDUSERLOG,"  substitute replace: \"%s\" with \"%s\"\r\n",found->word,wordlist);
		memcpy(backupTokens,wordStarts + i + erasing + 1,sizeof(char*) * (wordCount - i - erasing )); // save old tokens
		memcpy(wordStarts+i,tokens+1,sizeof(char*) * count);	// move in new tokens
		memcpy(wordStarts+i+count,backupTokens,sizeof(char*) * (wordCount - i - erasing ));	// restore old tokens
		wordCount += count - erase;
	}
	return true;
}

static WORDP ViableIdiom(char* text,unsigned int i,unsigned int n,unsigned int caseform)
{ // n is words merged into "word"

	// DONT convert plural to singular here

	WORDP word = FindWord(text,0,caseform);
    if (!word) return 0; // can not 
    if (word->systemFlags & CONDITIONAL_IDIOM) //  dare not unless there are no conditions
	{
		char* script = word->w.conditionalIdiom;
		if (script[1] != '=') return 0; // no conditions listed
	}
	if (word->internalBits & HAS_SUBSTITUTE)
	{
		uint64 allowed = tokenControl & (DO_SUBSTITUTE_SYSTEM|DO_PRIVATE);
		return (allowed & word->internalBits) ? word : 0; // allowed transform
	}

	if (!(tokenControl & DO_SUBSTITUTES)) return 0; // no dictionary word merge
	
	//   exclude titles of works and , done as composites later
	if (word->properties & NOUN_TITLE_OF_WORK) return 0;

    //   dont swallow - before a number
    if (i < wordCount && IsDigit(*wordStarts[i+1]))
    {
        char* name = word->word;
        if (*name == '-' && name[1] == 0) return 0;
        if (*name == '<' && name[1] == '-' && name[2] == 0) return 0;
    }

    if (word->properties & (PUNCTUATION|COMMA|PREPOSITION|AUX_VERB) && n) return word; //   multiword prep is legal as is "used_to" helper
	if (GETMULTIWORDHEADER(word) && !(word->systemFlags & PATTERN_WORD)) return 0; // if it is not a name or interjection or preposition, we dont want to use the wordnet composite word list, UNLESS it is a pattern word (like nautical_mile)
 
	// exclude "going to" if not followed by a potential verb 
	if (!stricmp(word->word,"going_to")  && i < wordCount)
	{
		WORDP D = FindWord(wordStarts[i+2]); // +1 will be "to"
		return (D && !(D->properties & VERB_INFINITIVE)) ? word : 0;	
	}
	if (!n) return 0;

	// how to handle proper nouns for merging here
	if (!IsUpperCase(*word->word)) {;}
	else if (!(tokenControl & DO_PROPERNAME_MERGE)) return 0; // do not merge any proper name
    else if (n && IsUpperCase(*word->word) && word->properties & PART_OF_SPEECH  && !IS_NEW_WORD(word)) 
		return word;// Merge dictionary names.  We  merge other proper names later.  words declared ONLY as interjections wont convert in other slots
	else if (n  && word->properties & word->systemFlags & PATTERN_WORD) return word;//  Merge any proper name which is a keyword. 
	
	// dont merge words with underscore if each word is also a word (though wordnet does- like executive)director), unless its a known keyword like "nautical_mile"
	char* part = strchr(word->word,'_');
	if (word->properties & (NOUN|ADJECTIVE|ADVERB|VERB) && part && !(word->systemFlags & PATTERN_WORD))
	{
		char* part1 = strchr(part+1,'_');
		WORDP P2 = FindWord(part+1,0,LOWERCASE_LOOKUP);
		WORDP P1 = FindWord(word->word,(part-word->word),LOWERCASE_LOOKUP);
		if (!part1 && P1 && P2 && P1->properties & PART_OF_SPEECH && P2->properties & PART_OF_SPEECH) 
		{
			// if there a noun this is plural of? like "square feet" where "square_foot" is the keyword
			char* noun = English_GetSingularNoun(word->word,false,true);
			if (noun)
			{
				WORDP D1 = FindWord(noun);
				if (D1->systemFlags & PATTERN_WORD) {;}
				else return 0; // we dont merge non-pattern words?
			}
			else return 0;
		}
	}

    if (word->properties & (NOUN|ADJECTIVE|ADVERB|CONJUNCTION_SUBORDINATE) && !IS_NEW_WORD(word)) return word; // merge dictionary found normal word but not if we created it as a sequence ourselves
	return 0;
}

static bool ProcessIdiom(unsigned int i,unsigned int max,char* buffer,WORDP D, char* ptr)
{//   buffer is 1st word, ptr is end of it
    WORDP word;
    WORDP found = NULL;
    unsigned int idiomMatch = 0;

	unsigned int n = 0;
    for (unsigned int j = i; j <= wordCount; ++j)
    {
		if (j != i) // add next word onto original starter
		{
			if (!stricmp(loginID,wordStarts[j])) break; // user name should not be part of idiom
			*ptr++ = '_'; // separator between words
			++n; // appended word count
			size_t len = strlen(wordStarts[j]);
			if ( ((ptr - buffer) + len) >= (MAX_WORD_SIZE-40)) return false; // avoid buffer overflow
			strcpy(ptr,wordStarts[j]);
			ptr += strlen(ptr);
		}
    
		//   we have to check both cases, because idiomheaders might accidently match a substitute
		WORDP localfound = found; //   we want the longest match, but do not expect multiple matches at a particular distance
		if (i == 1 && j == wordCount)  //   try for matching at end AND start
        {
			word = NULL;
			*ptr++ = '>'; //   end marker
			*ptr-- = 0;
			word = ViableIdiom(buffer,1,n,PRIMARY_CASE_ALLOWED);
			if (word) 
			{
				found = word;  
				idiomMatch = n;     //   n words ADDED to 1st word
			}
			if (found == localfound)
			{
				word = ViableIdiom(buffer,1,n,SECONDARY_CASE_ALLOWED);
				if (word) 
				{
					found = word;  
					idiomMatch = n;     //   n words ADDED to 1st word
				}			
			}
			*ptr = 0; //   remove tail end
		}
		if (found == localfound && i == 1 && (word = ViableIdiom(buffer,1,n,PRIMARY_CASE_ALLOWED))) // match at start
		{
			found = word;   
			idiomMatch = n;   
		}
 		if (found == localfound && i == 1 && (word = ViableIdiom(buffer,1,n,SECONDARY_CASE_ALLOWED))) // match at start
		{
			found = word;   
			idiomMatch = n;   
		}
        if (found == localfound && (word = ViableIdiom(buffer+1,i,n,PRIMARY_CASE_ALLOWED))) // match normal
        {
			found = word; 
			idiomMatch = n; 
		}
        if (found == localfound && (word =  ViableIdiom(buffer+1,i,n,SECONDARY_CASE_ALLOWED))) // used to not allow upper mapping to lower, but want it for start of sentence
        {
			if (!IsUpperCase(buffer[1]) || i == 1) // lower can always try upper, but upper can try lower ONLY at sentence start
			{
				found = word; 
				idiomMatch = n; 
			}
		}
        if (found == localfound && j == wordCount)  //   sentence ender
		{
			*ptr++ = '>'; //   end of sentence marker
			*ptr-- = 0;  
			word = ViableIdiom(buffer+1,0,n,PRIMARY_CASE_ALLOWED);
			if (word)
            {
				found = word; 
				idiomMatch = n; 
			}
			if (found == localfound)
			{
				word = ViableIdiom(buffer+1,0,n,SECONDARY_CASE_ALLOWED);
				if (word)
				{
					found = word; 
					idiomMatch = n; 
				}
			}
			*ptr= 0; //   back to normal
        }
		if (found == localfound && *(ptr-1) == 's' && j != i) // try singularlizing a noun
		{
			size_t len = strlen(buffer+1);
			word = FindWord(buffer+1,len-1,PRIMARY_CASE_ALLOWED|SECONDARY_CASE_ALLOWED); // remove s
			if (len > 3 && !word && *(ptr-2) == 'e') 
				word = FindWord(buffer+1,len-2,PRIMARY_CASE_ALLOWED|SECONDARY_CASE_ALLOWED); // remove es
			if (len > 3 && !word && *(ptr-2) == 'e' && *(ptr-3) == 'i') // change ies to y
			{
				char noun[MAX_WORD_SIZE];
				strcpy(noun,buffer);
				strcpy(noun+len-3,"y");
				word = FindWord(noun,0,PRIMARY_CASE_ALLOWED|SECONDARY_CASE_ALLOWED);
			}
			if (word && ViableIdiom(word->word,i,n,PRIMARY_CASE_ALLOWED|SECONDARY_CASE_ALLOWED)) // was composite
			{
				char* second = strchr(buffer,'_');
				if ( !IsUpperCase(*word->word) || (second && IsUpperCase(second[1]))) // be case sensitive in matching composites
				{
					found = StoreWord(buffer+1,NOUN_PLURAL); // generate the plural
					idiomMatch = n; 
				}
			}
		}

        if (n == max) break; //   peeked ahead to max length so we are done
	} //   end J loop

	if (!found) return false;

	D = GetSubstitute(found);
    if (D == found)  return false;

	bool result = false;
	
	//   dictionary match to multiple word entry
	if (found->internalBits & HAS_SUBSTITUTE) // a special substitution
	{
		result = Substitute(found,D ? D->word : NULL,i,idiomMatch);//   do substitution
		if (result) tokenFlags |= found->internalBits & (DO_SUBSTITUTE_SYSTEM|DO_PRIVATE); // we did this kind of substitution
	}
	else // must be a composite word, not a substitute
	{

		if (trace & TRACE_SUBSTITUTE && CheckTopicTrace()) 
		{
			Log(STDUSERLOG,"use multiword: %s instead of ",found->word);
			for (unsigned int j = i;  j < i + idiomMatch+1; ++j) Log(STDUSERLOG,"%s ",wordStarts[j]);
			Log(STDUSERLOG,"\r\n");
		}
		wordStarts[i] = reuseAllocation(wordStarts[i],found->word);
		if (!wordStarts[i]) wordStarts[i] = reuseAllocation(wordStarts[i],"a");
		memmove(wordStarts+i+1,wordStarts+i+idiomMatch+1,sizeof(char*) * (wordCount - i - idiomMatch));
		wordCount -= idiomMatch;
		result =  true;
	}

	return result;
}

void ProcessSubstitutes() // revise contiguous words based on LIVEDATA files
{
    char buffer[MAX_WORD_SIZE];
    *buffer = '<';	// sentence start marker

    unsigned int cycles = 0;
    for (unsigned int i = FindOOBEnd(1); i <= wordCount; ++i)
    {
		if (!stricmp(loginID,wordStarts[i])) continue; // dont match user's name

		//   put word into buffer to start with
        size_t len = strlen(wordStarts[i]);
		if (len > (MAX_WORD_SIZE-40)) continue;	// too big
		char* ptr = buffer+1;
        strcpy(ptr,wordStarts[i]);
        ptr += len;

        //   can this start a substition?  It must have an idiom count != ZERO_IDIOM_COUNT
 
        unsigned int count = 0;
		WORDP D = FindWord(buffer+1,0,PRIMARY_CASE_ALLOWED); // main word a header?
  		if (D) count = GETMULTIWORDHEADER(D);
        
		//   does secondary form longer phrases?
        WORDP E  = FindWord(buffer+1,0,SECONDARY_CASE_ALLOWED);
		if (E && GETMULTIWORDHEADER(E) > count) count = GETMULTIWORDHEADER(E);

        //   now see if start-bounded word does better
        if (i == 1) 
        {
			D = FindWord(buffer,0,PRIMARY_CASE_ALLOWED); // with < header
            if (D && GETMULTIWORDHEADER(D) > count) count = GETMULTIWORDHEADER(D);
			D = FindWord(buffer,0,SECONDARY_CASE_ALLOWED);
			if (D && GETMULTIWORDHEADER(D) > count) count = GETMULTIWORDHEADER(D);
 		}

		//   now see if end-bounded word does better
		if (i == wordCount)
        {
            *ptr++ = '>'; //   append boundary
            *ptr-- = 0;
            D = FindWord(buffer+1,0,PRIMARY_CASE_ALLOWED);
            if (D && GETMULTIWORDHEADER(D) > count) count = GETMULTIWORDHEADER(D);
			D = FindWord(buffer+1,0,SECONDARY_CASE_ALLOWED);
			if (D &&  GETMULTIWORDHEADER(D) > count) count = GETMULTIWORDHEADER(D);

			if (i == 1) //   can use start and end simultaneously
			{
				D = FindWord(buffer,0,PRIMARY_CASE_ALLOWED); 
				if (D && GETMULTIWORDHEADER(D) > count) count = GETMULTIWORDHEADER(D);
				D = FindWord(buffer,0,SECONDARY_CASE_ALLOWED);
				if (D && GETMULTIWORDHEADER(D) > count) count = GETMULTIWORDHEADER(D);
			}
			*ptr = 0;	// remove tail
		}
        
		//   use max count
        if (count && ProcessIdiom(i,count-1,buffer,D,ptr)) 
		{
			if (cycles > 20) // something is probably wrong
			{
				Log(STDUSERLOG,"Substitute cycle overflow %s\r\n",buffer);
				break;
			}

			i = 0;  //   restart since we modified sentence
			++cycles;
		}
	}
}
