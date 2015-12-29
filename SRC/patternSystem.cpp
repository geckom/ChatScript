#include "common.h"

#define INFINITE_MATCH (unsigned int)(-(200 << 8)) // allowed to match anywhere

#define GAPPASSBACK  0X0000FFFF
#define NOT_BIT 0X00010000
#define FREEMODE_BIT 0X00020000
#define QUOTE_BIT 0X00080000
#define WILDGAP 0X00100000
#define WILDSPECIFIC 0X00200000

bool matching = false;
bool clearUnmarks = false;
bool deeptrace = false;

unsigned int positionStart;		// where current match token started
unsigned int positionEnd;		// where most recent matched token ended

static bool MatchTest(bool reverse,WORDP D, unsigned int start,char* op, char* compare,int quote,bool &uppercasematch, bool exact = false);

// function calling data
static unsigned int functionNest = 0;	// recursive depth of macro calling
#define MAX_PAREN_NEST 50
static char* ptrStack[MAX_PAREN_NEST];
static int argStack[MAX_PAREN_NEST];
static int baseStack[MAX_PAREN_NEST];
static int fnVarBaseStack[MAX_PAREN_NEST];

bool MatchesPattern(char* word, char* pattern) //   does word match pattern of characters and *
{
	if (!*pattern && *word) return false;	// no more pattern but have more word so fails 
	size_t len = 0;
	while (IsDigit(*pattern)) len = (len * 10) + *pattern++ - '0'; //   length test leading characters can be length of word
	if (len && strlen(word) != len) return false; // length failed
	char* start = pattern;

	--pattern;
	while (*++pattern && *pattern != '*' && *word) //   must match leading non-wild exactly
	{
		if (*pattern != '.' &&  *pattern != GetLowercaseData(*word)) return false; // accept a single letter either correctly OR as 1 character wildcard
		++word;
	}
	if (pattern == start && len) return true;	// just a length test, no real pattern
	if (!*word) return !*pattern || (*pattern == '*' && !pattern[1]);	// the word is done. If pattern is done or is just a trailing wild then we are good, otherwise we are bad.
	if (*word && !*pattern) return false;		// pattern ran out w/o wild and word still has more

	// Otherwise we have a * in the pattern now and have to match it against more word
	
	//   wildcard until does match
	char find = *++pattern; //   the characters AFTER wildcard
	if (!find) return true; // pattern ended on wildcard - matches all the rest of the word including NO rest of word

	// now resynch
	--word;
	while (*++word)
	{
		if (*pattern == GetLowercaseData(*word) && MatchesPattern(word + 1,pattern + 1)) return true;
	}
	return false; // failed to resynch
}

static bool SysVarExists(char* ptr) //   %system variable
{
	char* sysvar = SystemVariable(ptr,NULL);
	if (!*sysvar) return false;
	return (*sysvar) ? true : false;	// value != null
}

static bool FindPartialInSentenceTest(char* test, unsigned int start,unsigned int originalstart,bool reverse)
{
	if (!test || !*test) return false;
	if (reverse)
	{
		for (unsigned int i = originalstart-1; i >= 1; --i) // can this be found in sentence backwards
		{
			char word[MAX_WORD_SIZE];
			MakeLowerCopy(word,wordStarts[i]);
			if (unmarked[i] || !MatchesPattern(word,test)) continue;	// if universally unmarked, skip it. Or if they dont match
			// we have a match of a word
			positionStart = i;
			positionEnd = i;
			return true;
		}
	}
	else 
	{
		for (unsigned int i = start+1; i <= wordCount; ++i) // can this be found in sentence
		{
			char word[MAX_WORD_SIZE];
			MakeLowerCopy(word,wordStarts[i]);
			if (unmarked[i] || !MatchesPattern(word,test)) continue;	// if universally unmarked, skip it. Or if they dont match
			// we have a match of a word
			positionStart = i;
			positionEnd = i;
			return true;
		}
	}
	return false;
}

static bool MatchTest(bool reverse,WORDP D, unsigned int start,char* op, char* compare,int quote,bool &uppercasematch, bool exact) // is token found somewhere after start?
{
	uppercasematch = false;
	if (deeptrace) Log(STDUSERLOG," matchtesting:%s ",D->word);
	while (GetNextSpot(D,start,positionStart,positionEnd,reverse)) // find a spot later where token is in sentence
    {
		if (deeptrace) Log(STDUSERLOG," matchtest:%s %d-%d ",D->word,positionStart,positionEnd);
		if (exact && (start+1) != positionStart) return false;	// we are doing _0?~hello or whatever. Must be on the mark
 		if (deeptrace) Log(STDUSERLOG," matchtest:ok ");
        start = positionStart; // where to try next if fail on test
        if (op) // we have a test to perform
        {
			char* word;
			if (D->word && (IsAlphaUTF8(*D->word) || D->internalBits & UTF8)) word = D->word; //   implicitly all normal words are relation tested as given
			else word = quote ? wordStarts[positionStart] : wordCanonical[positionStart];
			unsigned int id;
			if (deeptrace) Log(STDUSERLOG," matchtest:optest ");
 			if (HandleRelation(word,op,compare,false,id) & ENDCODES) continue; // failed 
        }
 		if (*D->word == '~') 
		{
			if (D->internalBits & UPPERCASE_MATCH) uppercasematch = true; //how can this be upper case? BW BUG
			return true; // we CANNOT tell whether original or canon led to set...
		}
       if (!quote) return true; // can match canonical or original
		
        //   we have a match, but prove it is a original match, not a canonical one
		if (positionEnd < positionStart) continue;	// trying to match within a composite. 
		if (positionStart == positionEnd && !stricmp(D->word,wordStarts[positionStart])) return true;   // literal word match
		else // match a phrase literally
		{
			char word[MAX_WORD_SIZE];
			char* at = word;
			for (unsigned int i = positionStart; i <= positionEnd; ++i)
			{
				strcpy(at,wordStarts[i]);
				at += strlen(wordStarts[i]);
				if (i != positionEnd) *at++ = '_';
			}
			*at = 0;
			if (!stricmp(D->word,word)) return true;
		}
    } 
	 if (deeptrace) Log(STDUSERLOG," matchtest:%s failed ",D->word);
     return false;
}

bool FindPhrase(char* word, unsigned int start,bool reverse)
{   // Phrases are dynamic, might not be marked, so have to check each word separately. -- faulty in not respecting ignored(unmarked) words
	if (start > wordCount) return false;
	bool matched = false;
	positionEnd = start;
	unsigned int oldend;
	oldend = start = 0; // allowed to match anywhere or only next

	unsigned int n = BurstWord(word);
	for (unsigned int i = 0; i < n; ++i) // use the set of burst words - but "Andy Warhol" might be a SINGLE word.
	{
		WORDP D = FindWord(GetBurstWord(i));
		bool junk;
		matched = MatchTest(reverse,D,positionEnd,NULL,NULL,0,junk);
		if (matched)
		{
			if (oldend > 0 && positionStart != (oldend + 1)) // do our words match in sequence
			{
				matched = false;
				break;
			}
			if (i == 1) start = positionStart;
			oldend = positionEnd;
		}
		else break;
	}
	if (matched) 
	{
		positionStart = start;
	}
	return matched;
}

bool Match(char* ptr, unsigned int depth, int startposition, char kind, bool wildstart,unsigned int& gap,unsigned int& wildcardSelector,unsigned int &returnstart,unsigned int& returnend,bool &uppercasem,int& firstMatched,bool reverse)
{//   always STARTS past initial opening thing ( [ {  and ends with closing matching thing
	ChangeDepth(1,"Match");
    char word[MAX_WORD_SIZE];
	char* orig = ptr;
	int statusBits = 0; //   turns off: not, quote, startedgap, freemode, gappassback,wildselectorpassback
    if (trace & TRACE_PATTERN  && CheckTopicTrace()) Log(STDUSERTABLOG, "%c ",kind); //   start on new indented line
    bool matched;
	unsigned int startNest = functionNest;
	unsigned int result;
    unsigned int hold;
    WORDP D;
	unsigned int oldtrace = trace;
	bool oldecho = echo;
	bool success = false;
    char* compare;
	bool returned = false;	// came back from a nesting, if we dont start a new nesting, we need to restore tab on this level
    firstMatched = -1; //   ()  should return spot it started (firstMatched) so caller has ability to bind any wild card before it
    if (wildstart)  positionStart = INFINITE_MATCH; //   INFINITE_MATCH means we are in initial startup, allows us to match ANYWHERE forward to start
    positionEnd = startposition; //   we scan starting 1 after this
 	int basicStart = startposition;	//   we must not match real stuff any earlier than here
    char* argumentText = NULL; //   pushed original text from a function arg -- function arg never decodes to name another function arg, we would have expanded it instead
    bool uppercasematch = false;
	while (ALWAYS) //   we have a list of things, either () or { } or [ ].  We check each item until one fails in () or one succeeds in  [ ] or { }
    {
        unsigned int oldStart = positionStart; //  allows us to restore if we fail, and confirm legality of position advance.
        unsigned int oldEnd = positionEnd;
		unsigned int id;

		ptr = ReadCompiledWord(ptr,word);

		if (trace & TRACE_PATTERN  && CheckTopicTrace())
		{
			if (*word && *word != '(' && *word != '[' && *word != '{') 
			{
				char* at = word;
				if (*word == '=') at += 2; //   skip = flag and accelerator
				
				if (*word == '\'' || *word == '!' || (*word == '_' && !IsDigit(word[1]))) Log(STDUSERLOG,"%c ",*word); // prefix always resumes on rest of its word
				else if (returned) Log(STDUSERTABLOG,"%s ",at); //   restore indent level from before
				else Log(STDUSERLOG,"%s ",at);
			}
			returned = false;
		}

		char c = *word;

		if (deeptrace) Log(STDUSERLOG," token:%s ",word);
        switch(c) 
        {
			// prefixs on tokens
            case '!': //   NOT condition - not a stand-alone token, attached to another token
				ptr -= strlen(word); // back up to remove rest of token
				if (*ptr == '!') ++ptr; // normally ptr points past a space after token. But if end of input then it wont.
				statusBits |= NOT_BIT;
				continue;
			case '\'': //   single quoted item    
				if (!stricmp(word,"'s"))
				{
					matched = MatchTest(reverse,FindWord(word),(positionEnd < basicStart && firstMatched < 0) ? basicStart : positionEnd,NULL,NULL,statusBits & QUOTE_BIT,uppercasematch);
					if (!matched || !(wildcardSelector & WILDSPECIFIC)) uppercasematch = false;
					if (!(statusBits & NOT_BIT) && matched && firstMatched < 0) firstMatched = positionStart;
					break;
				}
				else
				{
					statusBits |= QUOTE_BIT;
					ptr -= strlen(word); 
					if (*ptr == '\'') ++ptr; // normally ptr points past a space after token. But if end of input then it wont.
					continue;
				}
			case '_': //     memorization coming - there can be up-to-two memorizations in progress: _* and _xxx  OR  simply names a memorized value like _8
				
				// a wildcard id?
				if (IsDigit(word[1]))
				{
					matched = GetwildcardText(GetWildcardID(word),false)[0] != 0; // simple _2  means is it defined
					break;
				}
				
				// if we are going to memorize something AND we previously matched inside a phrase, we need to move to after...
				if ((positionStart - positionEnd) == 1) positionEnd = positionStart; // If currently matched a phrase, move to end. 
				uppercasematch = false;
				if (word[1] != '*' || IsDigit(word[2]) || word[2] == '-' || (word[2] && word[3] != '*' && word[2] != '~' )) wildcardSelector |= WILDSPECIFIC; // no gap or specific gap
				else if (word[1] == '*' && IsAlphaUTF8(word[2]))  wildcardSelector |= WILDSPECIFIC; // *dda* pattern
				else wildcardSelector |=  WILDGAP;
				ptr -= strlen(word); 
				if (*ptr == '_') ++ptr; // normally ptr points past a space after token. But if end of input then it wont.
				continue;
			case '@': // factset ref
				if (word[1] == '_') // set positional reference  @_20+ or @_0-   
				{
					if (firstMatched < 0) firstMatched = NORETRY; // cannot retry this match
	
					// memorize gap to end based on direction...xxxx
					if (gap && !reverse) // close to end of sentence 
					{
						positionStart = wordCount; // pretend to match at end of sentence
						int start = gap & 0x000000ff;
						unsigned int limit = (gap >> 8);
						gap = 0;   //   turn off
  						if ((positionStart + 1 - start) > limit) //   too long til end
						{
							matched = false;
 							wildcardSelector &= -1 ^ WILDGAP;
							break;
						}
						if (wildcardSelector & WILDGAP) 
						{
							SetWildCard(start,wordCount);  //   legal swallow of gap //   request memorize
 							wildcardSelector &= -1 ^ WILDGAP;
						}
					}

					char* end = word+3;  // skip @_2
					if (IsDigit(*end)) ++end; // point to proper + or - ending
					unsigned int wild = wildcardPosition[GetWildcardID(word+1)];
					if (*end == '+') 
					{
						positionStart = WILDCARD_START(wild);
						positionEnd = WILDCARD_END(wild);
						reverse = false;
					}
					else if (*end == '-') 
					{
						reverse = true;
						positionStart = WILDCARD_END(wild);
						positionEnd = WILDCARD_START(wild); 
					}
					if (!positionEnd) break;
					oldEnd = positionEnd; // forced match ok
					oldStart = positionStart;
					matched = true;
				}
				else
				{
					int set = GetSetID(word);
					if (set == ILLEGAL_FACTSET) matched = false;
					else matched = FACTSET_COUNT(set) != 0;
				}
				break;
   			case '<': //   sentence start marker OR << >> set
				if (firstMatched < 0) firstMatched = NORETRY; // cannot retry this match
				if (word[1] == '<') //   << 
				{
					statusBits |= FREEMODE_BIT;
					positionEnd = startposition;  //   allowed to pick up after here - oldStart/oldEnd synch automatically works
					positionStart = INFINITE_MATCH; 
					continue;
				}
                else 
				{
					if (gap && !reverse) // cannot memorize going forward to  start of sentence
					{
						gap = 0;  
						matched = false;
 						wildcardSelector &= -1 ^ WILDGAP;
					}
					else { // match can FORCE it to go to start from any direction
						positionStart = positionEnd = 0; //   idiom < * and < _* handled under *
						matched = true;
					}
				}
                break;
            case '>': //   sentence end marker
				if (word[1] == '>') //   >> closer, and reset to start of sentence wild again...
				{
					statusBits &= -1 ^ FREEMODE_BIT; //   positioning left for a start of sentence
					positionStart = positionEnd = INFINITE_MATCH; //   INFINITE_MATCH means we are in initial startup, allows us to match ANYWHERE forward to start
					continue;
				}
				if (gap && reverse) // cannot memorize going backward to  end of sentence
				{
					gap = 0;  
					matched = false;
 					wildcardSelector &= -1 ^ WILDGAP;
				}
				else if (gap || positionEnd == wordCount)// you can go to end from anywhere if you have a gap OR you are there
				{
					matched =  true;
					positionStart = positionEnd = wordCount + 1; //   pretend to match a word off end of sentence
				}
				else matched = false;
                break;
             case '*': //   GAP - accept anything (perhaps with length restrictions)
				if (word[1] == '-') //   backward gap, -1 is word before now -- BUG does not respect unmark system
				{
					int at = positionEnd - (word[2] - '0') - 1; // limited to 9 back
					if (at >= 0) //   no earlier than pre sentence start
					{
						oldEnd = at; //   set last match BEFORE our word
						positionStart = positionEnd = at + 1; //   cover the word now
						matched = true; 
					}
					else matched = false;
				}
				else if (IsDigit(word[1]))  // fixed length gap
                {
					unsigned int at;
					unsigned int count = word[1] - '0';	// how many to swallow
					if (reverse)
					{
						at = positionStart; // start here
						while (count-- && --at >= 1) // can we swallow this (not an ignored word)
						{
							if (unmarked[at]) ++count;	// ignore this word
						}
						if (at >= 1 ) // pretend match
						{ 
							positionEnd = positionStart - 1 ; // pretend match here -  wildcard covers the gap
							positionStart = at; 
							matched = true; 
						}
						else  matched = false;
					}
					else
					{
						at = positionEnd; // start here
						while (count-- && ++at <= wordCount) // can we swallow this (not an ignored word)
						{
							if (unmarked[at]) ++count;	// ignore this word
						}
						if (at <= wordCount ) // pretend match
						{ 
							positionStart = positionEnd + 1 ; // pretend match here -  wildcard covers the gap
							positionEnd = at; 
							matched = true; 
						}
						else  matched = false;
					}
                }
				else if (IsAlphaUTF8(word[1]) || word[1] == '*') matched = FindPartialInSentenceTest(word+1,(positionEnd < basicStart && firstMatched < 0) ? basicStart : positionEnd,positionStart,reverse); // wildword match like st*m* or *team* matches steamroller
                else // variable gap
                {
                    if (word[1] == '~') gap = (word[2]-'0') << 8; // *~3 - limit 9 back
                    else // I * meat
					{
						gap = 200 << 8;  // 200 is a safe infinity
						if (positionStart == 0) positionStart = INFINITE_MATCH; // < * resets to allow match anywhere
					}
                    gap |= (reverse) ? (positionStart  - 1) : (positionEnd  + 1);
					continue;
                }
                break;
            case '$': // is user variable defined
				matched = (HandleRelation(word,"!=","",false,id) & ENDCODES) ? 0 : 1;
                break;
            case '^': //   function call, function argument  or indirect function variable assign ref like ^$$tmp = null
                 if  (IsDigit(word[1]) || word[1] == '$' || word[1] == '_') //   macro argument substitution or indirect function variable
                {
                    argumentText = ptr; //   transient substitution of text

					if (IsDigit(word[1]))  ptr = callArgumentList[word[1]-'0'+fnVarBase];  // nine argument limit
					else if (word[1] == '$') ptr = GetUserVariable(word+1); // get value of variable and continue in place
					else ptr = wildcardCanonicalText[GetWildcardID(word+1)]; // ordinary wildcard substituted in place (bug)?
					continue;
                }
                
				D = FindWord(word,0); // find the function
				if (!D || !(D->internalBits & FUNCTION_NAME)) matched = false; // shouldnt fail
				else if (D->x.codeIndex) // system function - execute it
                {
					char* old = currentOutputBase;
					char* oldrule = currentRuleOutputBase;
					currentRuleOutputBase = currentOutputBase = AllocateBuffer(); // start an independent buffer
					FunctionResult result;
					matching = true;
					ptr = DoFunction(word,ptr,currentOutputBase,result);
					matching = false;
					matched = !(result & ENDCODES); 

					// allowed to do comparisons on answers from system functions but cannot have space before them, but not from user macros
					if (*ptr == '!' && ptr[1] == ' ' ){;} // simple not operator
					else if (ptr[1] == '<' || ptr[1] == '>'){;} // << and >> are not comparison operators in a pattern
					else if (IsComparison(*ptr) && *(ptr-1) != ' ' && (*ptr != '!' || ptr[1] == '='))  // ! w/o = is not a comparison
					{
						char op[10];
						char* opptr = ptr;
						*op = *opptr;
						op[1] = 0;
						char* rhs = ++opptr; 
						if (*opptr == '=') // was == or >= or <= or &= 
						{
							op[1] = '=';
							op[2] = 0;
							++rhs;
						}
						char copy[MAX_WORD_SIZE];
						ptr = ReadCompiledWord(rhs,copy);
						rhs = copy;

						if (*rhs == '^') // local function argument or indirect ^$ var  is LHS. copy across real argument
						{
							char* at = "";
							if (rhs[1] == '$') at = GetUserVariable(rhs+1); 
							else if (IsDigit(rhs[1])) at = callArgumentList[rhs[1]-'0'+fnVarBase];
							at = SkipWhitespace(at);
							strcpy(rhs,at);
						}
				
						if (*op == '?' && opptr[0] != '~')
						{
							bool junk;
							matched = MatchTest(reverse,FindWord(currentOutputBase),(positionEnd < basicStart && firstMatched < 0) ? basicStart : positionEnd,NULL,NULL,false,junk); 
							if (!(statusBits & NOT_BIT) && matched && firstMatched < 0) firstMatched = positionStart; //   first SOLID match
						}
						else
						{
							unsigned int id;
							result = HandleRelation(currentOutputBase,op,rhs,false,id); 
							matched = (result & ENDCODES) ? 0 : 1;
						}
					}
					FreeBuffer();
					currentOutputBase = old;
					currentRuleOutputBase = oldrule;
                }
				else // user function - execute it in pattern context as continuation of current code
				{ 
					//   save old base data
					baseStack[functionNest] = callArgumentBase; 
					argStack[functionNest] = callArgumentIndex; 
					fnVarBaseStack[functionNest] = fnVarBase;

					if ((trace & TRACE_PATTERN || D->internalBits & MACRO_TRACE)  && CheckTopicTrace()) Log(STDUSERLOG,"("); 
					ptr += 2; // skip ( and space
					// read arguments
					while (*ptr && *ptr != ')' ) 
					{
						char* arg = callArgumentList[callArgumentIndex++];
						ptr = ReadArgument(ptr,arg);  // gets the unevealed arg
						if ((trace & TRACE_PATTERN || D->internalBits & MACRO_TRACE)  && CheckTopicTrace()) Log(STDUSERLOG," %s, ",arg); 
					}
					if ((trace & TRACE_PATTERN || D->internalBits & MACRO_TRACE)  && CheckTopicTrace()) Log(STDUSERLOG,")\r\n"); 
					fnVarBase = callArgumentBase = argStack[functionNest];
					ptrStack[functionNest++] = ptr+2; // skip closing paren and space
					ptr = (char*) D->w.fndefinition + 1; // continue processing within the macro, skip argument count
					oldecho = echo;
					oldtrace = trace;
					if (D->internalBits & MACRO_TRACE  && CheckTopicTrace()) 
					{
						trace = (unsigned int)-1;
						echo = true;
					}
					continue;
				}
				break;
          case 0: // end of data (argument or function - never a real rule)
	           if (argumentText) // return to normal from argument substitution
                {
                    ptr = argumentText;
                    argumentText = NULL;
                    continue;
                }
                else if (functionNest > startNest) // function call end
                {
 					if (trace & TRACE_PATTERN  && CheckTopicTrace()) Log(STDUSERTABLOG,""); 
					--functionNest;
                    callArgumentIndex = argStack[functionNest]; //   end of argument list (for next argument set)
                    callArgumentBase = baseStack[functionNest]; //   base of callArgumentList
                    fnVarBase = fnVarBaseStack[functionNest];
					ptr = ptrStack[functionNest]; // continue using prior code
					trace = oldtrace;
                    echo = oldecho;
					continue;
                }
                else 
				{
					ChangeDepth(-1,"Match");
 					return false; // shouldn't happen
				}
                break;
            case '(': case '[':  case '{': // nested condition (required or optional) (= consecutive  [ = choice   { = optional
                hold = wildcardIndex;
				{
					int oldgap = gap;
					unsigned int returnStart = positionStart;
					unsigned int returnEnd = positionEnd;
					unsigned int oldselect = wildcardSelector;
					wildcardSelector = 0;
					bool uppercasemat = false;
					// nest inherits gaps leading to it. memorization requests withheld til he returns
					int whenmatched = 0;
					matched = Match(ptr,depth+1,positionEnd,*word, positionStart == INFINITE_MATCH,gap,wildcardSelector,returnStart,returnEnd,uppercasemat,whenmatched,reverse); //   subsection ok - it is allowed to set position vars, if ! get used, they dont matter because we fail
					wildcardIndex = hold; //   flushes all wildcards swallowed within
					wildcardSelector = oldselect;
					if (matched) 
					{
						if (!(statusBits & NOT_BIT)  && firstMatched < 0) firstMatched = whenmatched;
						positionStart = returnStart;
						if (positionStart == INFINITE_MATCH && returnStart > 0 &&  returnStart != INFINITE_MATCH) positionStart = returnEnd;
						positionEnd = returnEnd;
						if (wildcardSelector) gap = oldgap;	 // to size a gap
						uppercasematch = uppercasemat;
						// The whole thing matched but if @_ was used, which way it ran and what to consider the resulting zone is completely confused.
						// So force a tolerable meaning so it acts like it is contiguous to caller.  If we are memorizing it may be silly but its what we can do.
						if (*word == '(' && positionStart == NORETRY) 
						{
							positionEnd = positionStart = (reverse) ? (oldStart - 1) : (oldEnd + 1) ;  // claim we only moved 1 unit
						}
						else if (positionEnd) oldEnd = (reverse) ? (positionEnd + 1) : (positionEnd - 1); //   nested checked continuity, so we allow match whatever it found - but not if never set it (match didnt have words)
					}
					else if (*word == '{') 
					{
						gap = oldgap; // restore any pending gap we didnt plug  (eg *~2 {xx yy zz} a )
					}
				}
				if (*word == '(' && matched) {;} // WE ALREADY saw and swallowed the paren
				else ptr = BalanceParen(ptr); // skip over the material including closer 
       			returned = true;
				if (!matched) // failed, revert wildcard index - if ! was used, we will need this
                {
  				    if (*word == '{') 
                    {
						if (wildcardSelector & WILDSPECIFIC) //   we need to memorize failure because optional cant fail
						{
							wildcardSelector ^= WILDSPECIFIC;
							SetWildCard(0, wordCount); 
						}

                        if (gap) continue;   //   if we are waiting to close a wildcard, ignore our failed existence entirely
                        statusBits |= NOT_BIT; //   we didnt match and pretend we didnt want to
                    }
   					else wildcardSelector = 0;
                }
                else if (*word == '{') //   was optional, revert the wildcard index (keep position data)
                {
                    wildcardIndex = hold;	// drop any wildcards bound (including reserve)
                    if (!matched) continue; // be transparent in case wildcard pending
                }
                else if (wildcardSelector > 0)  wildcardIndex = hold; //   drop back to this index so we can save on it 
                break;
            case ')': case ']': case '}' :  //   end sequence/choice/optional
				matched = (kind == '('); //   [] and {} must be failures if we are here
				if (gap) //   pending gap  -  [ foo fum * ] and { foo fot * } are pointless but [*3 *2] is not 
                {
					if (depth != 0) // for simplicity don't end with a gap 
					{
						gap = wildcardSelector = 0;
						matched = false; //   force match failure
					}
					else positionStart = wordCount + 1; //   at top level a close implies > )
				}
                break; 
            case '"':  //   double quoted string
				matched = FindPhrase(word,(positionEnd < basicStart && firstMatched < 0) ? basicStart : positionEnd, reverse);
				if (!(statusBits & NOT_BIT) && matched && firstMatched < 0) firstMatched = positionStart; //   first SOLID match
				break;
            case '%': //   system variable
				if (!word[1]) // simple % 
				{
					bool junk;
					matched = MatchTest(reverse,FindWord(word),(positionEnd < basicStart && firstMatched < 0) ? basicStart: positionEnd,NULL,NULL,statusBits & QUOTE_BIT,junk); //   possessive 's
					if (!(statusBits & NOT_BIT) && matched && firstMatched < 0) firstMatched = positionStart; //   first SOLID match
				}
                else matched = SysVarExists(word);
                break;
            case '?': //  question sentence? 
				if (!word[1]) matched = (tokenFlags & QUESTIONMARK) ? true : false;
				else matched = false;
	            break;
            case '=': //   a comparison test - never quotes the left side. Right side could be quoted
				//   format is:  = 1-bytejumpcodeToComparator leftside comparator rightside
				if (!word[1]) //   the simple = being present
				{
					bool junk;
					matched = MatchTest(reverse,FindWord(word),(positionEnd < basicStart && firstMatched < 0)  ? basicStart : positionEnd,NULL,NULL,statusBits & QUOTE_BIT,junk); //   possessive 's
					if (!(statusBits & NOT_BIT) && matched && firstMatched < 0) firstMatched = positionStart; //   first SOLID match
				}
				//   if left side is anything but a variable $ or _ or @, it must be found in sentence and that is what we compare against
				else 
				{
					// get the operator
					compare = word + Decode(word+1,true); // use accelerator to point to op in the middle
					char op[10];
					char* opptr = compare;
					*op = *opptr;
					op[1] = 0;
					char* lhs = word + 2;
					char* rhs = ++opptr; 
					if (*opptr == '=') // was == or >= or <= or &= 
					{
						op[1] = '=';
						op[2] = 0;
						++rhs;
					}
					*compare = 0;		// separate left and right
					char copy[MAX_WORD_SIZE];
					strcpy(copy,rhs);		// we duplicate rhs because lhs owns the memory and might overwrite it
					rhs = copy; // right hand side of comparator operation
	
					if (*lhs == '^') // local function arg indirect ^$ var or _ as LHS
					{
						char* at = "";
						if (lhs[1] == '$') at = GetUserVariable(lhs+1); 
						else if (IsDigit(lhs[1])) at = callArgumentList[lhs[1]-'0'+fnVarBase];
						at = SkipWhitespace(at);
						strcpy(lhs,at);
					}

					if (*rhs == '^') // local function argument or indirect ^$ var  is LHS. copy across real argument
					{
						char* at = "";
						if (rhs[1] == '$') at = GetUserVariable(rhs+1); 
						else if (IsDigit(rhs[1])) at = callArgumentList[rhs[1]-'0'+fnVarBase];
						at = SkipWhitespace(at);
						strcpy(rhs,at);
					}
				
					bool quoted = false;
					if (*lhs == '\'') // left side is quoted
					{
						++lhs; 
						quoted = true;
					}
			
					if (*op == '?' && opptr[0] != '~') // NOT a ? into a set test - means does this thing exist in sentence
					{
						char* val = "";
						if (*lhs == '$') val = GetUserVariable(lhs);
						else if (*lhs == '_') val = (quoted) ? wildcardOriginalText[GetWildcardID(lhs)] : wildcardCanonicalText[GetWildcardID(lhs)];
						else if (*lhs == '%') val = SystemVariable(lhs,NULL);
						else val = lhs; // direct word
						bool junk;
						matched = MatchTest(reverse,FindWord(val),(positionEnd < basicStart && firstMatched < 0) ? basicStart : positionEnd,NULL,NULL,quoted,junk); 
						if (!(statusBits & NOT_BIT) && matched && firstMatched < 0) firstMatched = positionStart; //   first SOLID match
						break;
					}
	
					result = *lhs;
					if (result == '%' || result == '$' || result == '_' || result == '@' || (*op == '?' && rhs)) // otherwise for words and concepts, look up in sentence and check relation there
					{
						if (result == '_' && quoted) --lhs; // include the quote
						FunctionResult answer = HandleRelation(lhs,op,rhs,false,id); 
						matched = (answer & ENDCODES) ? 0 : 1;
					}
					else // find and test
					{
						bool junk;
						matched = MatchTest(reverse,FindWord(lhs),(positionEnd < basicStart && firstMatched < 0) ? basicStart : positionEnd,op,rhs,quoted,junk); //   MUST match later 
						if (!matched) break;
					}
 				}
				break;
            case '\\': //   escape to allow [ ] () < > ' {  } ! as words and 's possessive And anything else for that matter
				{
					bool junk;
					matched =  MatchTest(reverse,FindWord(word+1),(positionEnd < basicStart && firstMatched < 0) ? basicStart : positionEnd,NULL,NULL,statusBits & QUOTE_BIT,junk);
					if (!(statusBits & NOT_BIT) && matched && firstMatched < 0) firstMatched = positionStart; 
					if (matched) {}
					else if (word[1] == '!' ) matched =  (wordCount && (tokenFlags & EXCLAMATIONMARK)); //   exclamatory sentence
  					else if (word[1] == '?') matched =  (tokenFlags & QUESTIONMARK) ? true : false; //   question sentence
					break;
				}
			case '~': // current topic ~ and named topic
				if (word[1] == 0) // current topic
				{
					matched = IsCurrentTopic(currentTopicID); // clearly we are executing rules from it but is the current topic interesting
					break;
				}
			default: //   ordinary words, concept/topic, numbers, : and ~ and | and & accelerator
				matched = MatchTest(reverse,FindWord(word),(positionEnd < basicStart && firstMatched < 0) ? basicStart : positionEnd,NULL,NULL,statusBits & QUOTE_BIT,uppercasematch);
				if (*word == '~' && matched && trace & TRACE_PATTERN  && CheckTopicTrace()) 
				{
					if (positionStart == positionEnd) Log(STDUSERLOG,"//concept %s -> %s(%d)// ",word,wordStarts[positionStart],positionStart);
					else Log(STDUSERLOG,"//concept %s -> %s(%d-%d)// ",word,wordStarts[positionStart],positionStart,positionEnd);
				}
				if (!matched || !(wildcardSelector & WILDSPECIFIC)) uppercasematch = false;
				if (!(statusBits & NOT_BIT) && matched && firstMatched < 0) firstMatched = positionStart;
         } 
		statusBits &= -1 ^ QUOTE_BIT; // turn off any pending quote

        if (statusBits & NOT_BIT && matched) // flip success to failure
        {
            matched = false; 
			uppercasematch = false;
            statusBits &= -1 ^ NOT_BIT;
            positionStart = oldStart; //   restore any changed position values (if we succeed we would and if we fail it doesnt harm us)
            positionEnd = oldEnd;
        }

		//   prove GAP was legal, accounting for ignored words if needed
 		unsigned int started;
		if (!reverse) started = (positionStart < REAL_SENTENCE_LIMIT) ? positionStart : 0; // position start may be the unlimited access value
		else started = (positionStart < REAL_SENTENCE_LIMIT) ? positionEnd : wordCount; // position start may be the unlimited access value
		bool legalgap = false;
        if (gap && matched) // test for legality of gap
        {
			unsigned int begin = started; // where we think we are now
			started = (gap & 0x000000ff); // actual word we started at
			unsigned int ignore = started;
			int x;
			int limit = gap >> 8;
			if (reverse)
			{
				x = started - begin; // *~2 debug() something will generate a -1 started... this is safe here
				while (ignore > begin) // no charge for ignored words in gap
				{
					if (unmarked[ignore--]) --x; 
				}
			}
			else
			{
				x = begin - started; // *~2 debug() something will generate a -1 started... this is safe here
				while (ignore < begin) // no charge for ignored words in gap
				{
					if (unmarked[ignore++]) --x; 
				}
			}
  			if (x <= limit) legalgap = true;   //   we know this was legal, so allow advancement test not to fail- matched gap is started...oldEnd-1
			else  
			{
				matched = false;  // more words than limit
				wildcardSelector &= -1 ^ WILDGAP; //   turn off any save flag
			}
		}

		if (matched) // perform any memorization
		{
			if (oldEnd == positionEnd && oldStart == positionStart); // something like function call, didnt change position
			else if (wildcardSelector) //   memorize ONE or TWO things 
			{
				if (started == INFINITE_MATCH) started = 1;
				if (wildcardSelector & WILDGAP) //   would be first if both
				{
					if (reverse)
					{
						if ((started - positionEnd) == 0) SetWildCard("","",0,positionEnd+1); // empty gap
						else SetWildCard(positionEnd + 1,oldStart-1);  //   wildcard legal swallow between elements
					}	
					else if ((positionStart - started) == 0) SetWildCard("","",0,oldEnd+1); // empty gap
					else SetWildCard(started,positionStart-1);  //   wildcard legal swallow between elements
				}
				if (positionStart == INFINITE_MATCH) positionStart = 1;
				if (wildcardSelector & WILDSPECIFIC) 
				{
					SetWildCard(positionStart,positionEnd);  // specific swallow 
					if (uppercasematch)
					{
						WORDP D = FindWord(wildcardOriginalText[wildcardIndex-1],0,UPPERCASE_LOOKUP); // find without underscores..
						if (D) 
						{
							strcpy(wildcardOriginalText[wildcardIndex-1],D->word);
							strcpy(wildcardCanonicalText[wildcardIndex-1],D->word);
						}
						else
						{
							char word[MAX_WORD_SIZE];
							strcpy(word,wildcardOriginalText[wildcardIndex-1]);
							char* at = word;
							while ((at = strchr(at,' '))) *at = '_';
							D = FindWord(word,0,UPPERCASE_LOOKUP); // find with underscores..
							if (D) 
							{
								strcpy(wildcardOriginalText[wildcardIndex-1],D->word);
								strcpy(wildcardCanonicalText[wildcardIndex-1],D->word);
							}
						}
						uppercasematch = false;
					}
					else if (strchr(wildcardCanonicalText[wildcardIndex-1],' ')) // is lower case canonical a dictionary word with content?
					{
						char word[MAX_WORD_SIZE];
						strcpy(word,wildcardCanonicalText[wildcardIndex-1]);
						char* at = word;
						while ((at = strchr(at,' '))) *at = '_';
						WORDP D = FindWord(word,0); // find without underscores..
						if (D && D->properties & PART_OF_SPEECH)  strcpy(wildcardCanonicalText[wildcardIndex-1],D->word);
					}
				}
				gap = wildcardSelector = 0;
			}
			else gap = wildcardSelector = 0; /// should NOT clear this inside a [] or a {} on failure
		}
		else //   fix side effects of anything that failed by reverting
        {
            positionStart = oldStart;
            positionEnd = oldEnd;
  			if (kind == '(') gap = wildcardSelector = 0; /// should NOT clear this inside a [] or a {} on failure since they must try again
			if (trace & TRACE_PATTERN && !(statusBits & NOT_BIT))
			{
				char copy[MAX_WORD_SIZE];
				strncpy(copy,ptr,80);
				strcpy(copy+75,"...");
				char* at = strchr(copy,')');
				if (at) at[1] = 0;
				if (positionEnd) Log(STDUSERLOG," :: Matched at: %s(%d), Fails: \"%s\", Remaining pattern: \"%s\" ::\r\n",wordStarts[positionEnd],positionEnd, word, copy);
				else Log(STDUSERLOG," :: Fails: \"%s\", Remaining pattern: \"%s\" ::\r\n", word, copy);
			}
        }

        //   end sequence/choice/optional
        if (*word == ')' || *word ==  ']' || *word == '}') 
        {
			if (matched)
			{
				if (statusBits & GAPPASSBACK ) //   passing back a gap at end of nested (... * )
				{
					gap = statusBits & GAPPASSBACK;
					wildcardSelector =  statusBits & (WILDSPECIFIC|WILDGAP);
				}
			}
         //   if (matched && firstMatched > 0)  matched = firstMatched; //   tell spot we matched for top level retry
			success = matched != 0; 

			if (success && argumentText) //   we are ok, but we need to resume old data
			{
				ptr = argumentText;
				argumentText = NULL;
				continue;
			}

			break;
        }

		//   postprocess match of single word or paren expression
		if (statusBits & NOT_BIT) //   flip failure result to success now (after wildcardsetting doesnt happen because formally match failed first)
        {
            matched = true; 
			statusBits &= -1 ^ NOT_BIT;
         }

		//   word ptr may not advance more than 1 at a time (allowed to advance 0 - like a string match or test) unless global unmarks in progress
        //   But if initial start was INFINITE_MATCH, allowed to match anywhere to start with
		if (!matched  || positionStart == INFINITE_MATCH || oldStart == INFINITE_MATCH || legalgap) {;}
		else if (reverse)
		{
			if (oldStart < oldEnd && positionEnd >= (oldStart - 1) ){;} // legal move ahead given matched WITHIN last time
			else if (positionEnd < (oldStart - 1 ))  // failed to match position advance
			{
				unsigned int ignored = oldStart - 1;
				if (oldStart && unmarked[ignored]) while (--ignored > positionEnd && unmarked[ignored]); // dont have to account for these
				if (ignored != positionStart) // position track failed
				{
					if ((unsigned int) firstMatched == positionStart) firstMatched = 0; // drop recog of it
					matched = false;
					positionStart = oldStart;
					positionEnd = oldEnd;
				}
			}
		}
		else // forward
		{
			if (oldEnd < oldStart && positionStart <= (oldStart + 1)){;} // legal move ahead given matched WITHIN last time -- what does match within mean?
			else if (positionStart > (oldEnd + 1))  // failed to match position advance of one
			{
				unsigned int ignored = oldEnd+1;
				if (unmarked[ignored]) while (++ignored < positionStart && unmarked[ignored]); // dont have to account for these
				if (ignored != positionStart) // position track failed
				{
					if ((unsigned int) firstMatched == positionStart) firstMatched = 0; // drop recog of it
					matched = false;
					positionStart = oldStart;
					positionEnd = oldEnd;
				}
			}
		}

        //   now verify position of match, NEXT is default for (type, not matter for others
        if (kind == '(') //   ALL must match in sequence
        {
			//   we failed, retry shifting the start if we can
			if (!matched)
			{
				if (wildstart && firstMatched > 0 && firstMatched < NORETRY) //   we are top level and have a first matcher, we can try to shift it
				{
					if (trace & TRACE_PATTERN  && CheckTopicTrace()) Log(STDUSERTABLOG,"retry past %d ----------- ",firstMatched);
					//   reset to initial conditions, mostly 
					ptr = orig;
					wildcardIndex = 0; 
					basicStart = positionEnd = firstMatched;  //   THIS is different from inital conditions
					firstMatched = -1; 
					positionStart = INFINITE_MATCH; 
					gap = 0;
					wildcardSelector = 0;
					statusBits &= -1 ^ (NOT_BIT | FREEMODE_BIT);
					argumentText = NULL; 
					continue;
				}
				break; //   default fail
			}
			if (statusBits & FREEMODE_BIT) 
			{
				positionEnd = startposition;  //   allowed to pick up after here
				positionStart = INFINITE_MATCH; //   re-allow anywhere
			}
		}
        else if (matched /* && *word != '>' */ ) // was could not be END of sentence marker, why not???  
        {
			if (argumentText) //   we are ok, but we need to resume old data
			{
				ptr = argumentText;
				argumentText = NULL;
			}
			else
			{
				success = true; //   { and [ succeed when one succeeeds 
				break;
			}
		}
    } 

	//   begin the return sequence
	
	if (functionNest > startNest)//   since we are failing, we need to close out all function calls in progress at this level
    {
        callArgumentIndex = argStack[startNest];
        callArgumentBase = baseStack[startNest];
		fnVarBase = fnVarBaseStack[startNest];
		functionNest = startNest;
    }
	
	if (success)
	{
		returnstart = (firstMatched > 0) ? firstMatched : positionStart; // if never matched a real token, report 0 as start
		returnend = positionEnd;
	}

	//   if we leave this level w/o seeing the close, show it by elipsis 
	//   can only happen on [ and { via success and on ) by failure
	if (trace & TRACE_PATTERN && depth  && CheckTopicTrace())
	{
		if (*word != ')' && *word != '}' && *word !=  ']')
		{
			if (success) Log(STDUSERTABLOG,"%c ... + %d:%d ",(kind == '{') ? '}' : ']',positionStart,positionEnd);
			else Log(STDUSERTABLOG,") ... - ");
		}
		else if (*word == ')') Log(STDUSERLOG,"+%d:%d ",positionStart,positionEnd);
	}
	
	ChangeDepth(-1,"Match");
    return success; 
}

