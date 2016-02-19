#include "common.h"
//------------------------
// ALWAYS AVAILABLE
//------------------------
char* newBuffer = 0;

static char* incomingPtrSys = 0;			// cache AFTER token find ptr when peeking.
static char lookaheadSys[MAX_WORD_SIZE];	// cache token found when peeking
static unsigned int hasWarnings;			// number of warnings generated
unsigned int hasErrors;
uint64 grade = 0;						// vocabulary warning
char* lastDeprecation = 0;
bool compiling = false;			// script compiler in progress
bool patternContext = false;	// current compiling a pattern
uint64 buildId; // current build
char* overrideSystemToken = 0;
static bool overrriding = false;

#define MAX_WARNINGS 150
static char warnings[MAX_WARNINGS][MAX_WORD_SIZE];
static unsigned int warnIndex = 0;
static char baseName[MAX_WORD_SIZE];

#define MAX_ERRORS 150
static char errors[MAX_ERRORS][MAX_WORD_SIZE];
static unsigned int errorIndex = 0;

static char functionArguments[MAX_ARGUMENT_COUNT+1][500];
static int functionArgumentCount = 0;
static char botheader[MAX_WORD_SIZE];
static bool renameInProgress = false;
static bool endtopicSeen = false; // needed when ending a plan

uint64 buildID = 0;

static char* topicFiles[] = //   files created by a topic refresh from scratch 
{
	"TOPIC/describe",		//   document variables functions concepts topics etc
	"TOPIC/facts",			//   hold facts	
	"TOPIC/keywords",		//   holds topic and concepts keywords
	"TOPIC/macros",			//   holds macro definitions
	"TOPIC/script",			//   hold topic definitions
	"TOPIC/plans",			//   hold plan definitions
	"TOPIC/patternWords",	//   things we want to detect in patterns that may not be normal words
	"TOPIC/dict",			//   dictionary changes	
	"TOPIC/private",		//   private substitutions changes	
	"TOPIC/canon",			//   private canonical values 	

	"TOPIC/missingLabel.txt",	//   reuse/unerase needing delayed testing for label
	"TOPIC/missingSets.txt",	//   sets needing delayed testing
	0
};
static void WritePatternWord(char* word);
static void WriteKey(char* word);

void InitScriptSystem()
{
}

void AddWarning(char* buffer)
{
	sprintf(warnings[warnIndex++],"line %d of %s: %s",currentFileLine,currentFilename,buffer);
	if (warnIndex >= MAX_WARNINGS) --warnIndex;
}

void ScriptWarn()
{
	if (compiling)
	{
		++hasWarnings; 
		if (*currentFilename) Log(STDUSERLOG,"*** Warning- line %d of %s: ",currentFileLine,currentFilename);
		else Log(STDUSERLOG,"*** Warning-  ");
	}
}

void AddError(char* buffer)
{
	sprintf(errors[errorIndex++],"line %d of %s: %s",currentFileLine,currentFilename,buffer);
	if (errorIndex >= MAX_ERRORS) --errorIndex;
}

void ScriptError()
{
	++hasErrors; 
	renameInProgress = false;
	if (compiling)
	{
		patternContext = false; 
		Log(STDUSERLOG,"*** Error- line %d of %s: ",currentFileLine,currentFilename);
	}
}

void EraseTopicFiles(uint64 build,char* name)
{
	int i = -1;
	while (topicFiles[++i])
	{
		char word[MAX_WORD_SIZE];
		sprintf(word,"%s%s.txt",topicFiles[i],name);
		remove(word);
	}
}

static char* FindComparison(char* word)
{
	if (!*word || !word[1] || !word[2]) return NULL; //   if token is short, we cannot do the below word+1 scans 
	if (*word == '.') return NULL; //  .<_3 is not a comparison
	if (*word == '\\') return NULL; // escaped is not a comparison
	char* at = strchr(word+1,'!'); 
	if (!at) at = strchr(word+1,'<');
	if (!at) at = strchr(word+1,'>');
	if (!at) 
	{
		at = strchr(word+1,'&');
		if (at && (at[1] == '_' || at[1] == ' ')) at = 0;	// ignore & as part of a name
	}
	if (!at) at = strchr(word+1,'=');
	if (!at) at = strchr(word+1,'?');  //   member of set
	if (!at)
	{
		at = strchr(word+1,'!');  //   negation
		if (at && (at[1] == '=' || at[1] == '?'));
		else at = NULL;
	}
	return at;
}

static void FlipPrivateBuffer(bool status) // full private buffer
{
	if (status) 
	{
		overrideSystemToken = incomingPtrSys;
		incomingPtrSys = 0;
	}
	else 
	{
		incomingPtrSys = 0;
		overrideSystemToken = 0;
	}
	overrriding = status;
}

char* ReadNextSystemToken(FILE* in,char* ptr, char* word, bool separateUnderscore, bool peek)
{ 

#ifdef INFORMATION
The outside can ask for the next real token or merely peek ahead one token. And sometimes the outside
after peeking, decides it wants to back up a real token (passing it to some other processor).

To support backing up a real token, the system must keep the current readBuffer filled with the data that
led to that token (to allow a ptr - strlen(word) backup).

To support peeking, the system may have to read a bunch of lines in to find a token. It is going to need to
track that buffer separately, so when it needs a real token which was the peek, it can both get the peek value
and be using contents of the new buffer thereafter. 

So peeks must never touch the real readBuffer. And real reads must know whether the last token was peeked 
and from which buffer it was peeked.

And, if someone wants to back up to allow the old token to be reread, they have to CANCEL any peek data, so the token
comes from the old buffer. Meanwhile the newbuffer continues to have content for when the old buffer runs out.
#endif
	
	//   clear peek cache
	if (!in && !ptr) // clear cache request, next get will be from main buffer (though secondary buffer may still have peek read data)
	{
		if (word) *word = 0;
		incomingPtrSys = NULL; // no longer holding a PEEK value.
		return NULL;
	}

	char* result = NULL;
	if (incomingPtrSys ) //  had a prior PEEK, now in cache. use up cached value, unless duplicate peeking
	{
		result = incomingPtrSys; // caller who is peeking will likely ignore this
		if (!peek)
		{
			// he wants reality now...
			if (*newBuffer && !overrriding) // prior peek was from this buffer, make it real data in real buffer
			{
				strcpy(readBuffer,newBuffer);
				result = (result - newBuffer) + readBuffer; // adjust pointer to current buffer
				*newBuffer = 0;
			}
			strcpy(word,lookaheadSys);
			incomingPtrSys = 0;
		}
		else 
		{
			strcpy(word,lookaheadSys); // duplicate peek
			result = (char*)1;	// NO ONE SHOULD KEEP A PEEKed PTR
		}

		return result;
	}

	*word = 0;

	if (ptr) result = ReadSystemToken(ptr,word,separateUnderscore);
	bool newline = false;
	while (!*word) // found no token left in existing buffer - we have to juggle buffers now unless running overwrite 
	{
		if (overrriding) break;
		else if (!newline && *newBuffer) // use pre-read buffer per normal, it will have a token
		{
			strcpy(readBuffer,newBuffer);
			*newBuffer = 0;
			result = ReadSystemToken(readBuffer,word,separateUnderscore);
			break;
		}
		else // read new line into hypothetical buffer, not destroying old actual buffer yet
		{
			if (!in || ReadALine(newBuffer,in) < 0) return NULL; //   end of file
			if (!strnicmp(newBuffer,"#ignore",7)) // hit an ignore zone
			{
				unsigned int ignoreCount = 1;
				while (ReadALine(newBuffer,in) >= 0)
				{
					if (!strnicmp(newBuffer,"#ignore",7)) ++ignoreCount;
					else if (!strnicmp(newBuffer,"#endignore",10))
					{
						if (--ignoreCount == 0)
						{
							if (ReadALine(newBuffer,in) < 0) return NULL;	// EOF
							break;
						}
					}
				}
				if (ignoreCount) return NULL;	//EOF before finding closure
			}
			result = ReadSystemToken(newBuffer,word,separateUnderscore); // result is ptr into NEWBUFFER
			newline = true;
		}
	}

	if (peek) //   save request - newBuffer has implied newline if any
	{
		incomingPtrSys = result;  // next location in whatever buffer
		strcpy(lookaheadSys,word); // save next token peeked
		result = (char*)1;	// NO ONE SHOULD KEEP A PEEKed PTR
	}
	else if (newline) // live token from new buffer, adjust pointers and buffers to be fully up to date
	{
		strcpy(readBuffer,newBuffer);
		result = (result - newBuffer) + readBuffer; // ptr into current readBuffer now
		*newBuffer = 0;
	}

	return result; // ptr into READBUFFER or 1 if from peek zone
}

static void InsureAppropriateCase(char* word)
{
	char c;
	char* at = FindComparison(word);
	//   force to lower case various standard things
	//   topcs/sets/classes/user vars/ functions and function vars  are always lower case
 	if (at) //   a comparison has 2 sides
	{
		c = *at;
		*at = 0;
		InsureAppropriateCase(word);
		if (at[1] == '=' || at[1] == '?') InsureAppropriateCase(at+2); // == or >= or such
		else InsureAppropriateCase(at+1);
		*at = c;
	}
	else if (*word == '_' || *word == '\'') InsureAppropriateCase(word+1);
	else if ((*word == '^' && word[1] != '"') || *word == '~' || *word == '$' || *word == '%' || *word == '|' ) MakeLowerCase(word);	
	else if (*word == '@' && IsDigit(word[1])) MakeLowerCase(word);	//   potential factref like @2subject
}

static int GetFunctionArgument(char* arg) //   get index of argument (0-based) if it is value, else -1
{
	for (int i = 0; i < functionArgumentCount; ++i)
	{
		if (!stricmp(arg,functionArguments[i])) return i;
	}
	return -1; //   failed
}

static void FindDeprecated(char* ptr, char* value, char* message)
{
	char* comment = strstr(ptr,"# ");
	char* at = ptr;
	size_t len = strlen(value);
	while (at)
	{
		at = strstr(at,value);
		if (!at) break;
		if (*(at-1) == '$') // $$xxx should be ignored
		{
			at += 2;
			continue;
		}
		if (comment && at > comment) return; // inside a comment
		char word[MAX_WORD_SIZE];
		ReadCompiledWord(at,word);
		if (!stricmp(value,word))
		{
			lastDeprecation = at;
			BADSCRIPT(message);
		}
		at += len;
	}
}

char* ReadSystemToken(char* ptr, char* word, bool separateUnderscore) //   how we tokenize system stuff (rules and topic system) words -remaps & to AND
{
	*word = 0;
    if (!ptr)  return 0;
    char* start = word;
    ptr = SkipWhitespace(ptr);
	FindDeprecated(ptr,"$bot","Deprecated $bot need to be $cs_bot");
	FindDeprecated(ptr,"$login","Deprecated $login need to be $cs_login");
	FindDeprecated(ptr,"$userfactlimit","Deprecated $userfactlimit need to be $cs_userfactlimit");
	FindDeprecated(ptr,"$crashmsg","Deprecated $crashmsg need to be $cs_crashmsg");
	FindDeprecated(ptr,"$token","Deprecated $token need to be $cs_token");
	FindDeprecated(ptr,"$response","Deprecated $response need to be $cs_response");
	FindDeprecated(ptr,"$randindex","Deprecated $randindex need to be $cs_randindex");
	FindDeprecated(ptr,"$wildcardseparator","Deprecated $wildcardseparator need to be $cs_wildcardseparator");
	FindDeprecated(ptr,"$abstract","Deprecated $abstract need to be $cs_abstract");
	FindDeprecated(ptr,"$prepass","Deprecated $prepass need to be $cs_prepass");
	FindDeprecated(ptr,"$control_main","Deprecated $control_main need to be $cs_control_main");
	FindDeprecated(ptr,"$control_pre","Deprecated $control_pre need to be $cs_control_pre");
	FindDeprecated(ptr,"$control_post","Deprecated $control_post need to be $cs_control_post");

#ifdef INFORMATION
	A token is nominally a contiguous collection of characters broken off by tab or space (since return and newline are stripped off).
	Tokens to include whitespace are encased in doublequotes.

	Characters with reserved status automatically also break into individual tokens and to include them you must put \ before them. These include:
	[ ]  ( )  { }  always and separate into individual tokens except for _(  _[   _{ 

	< > and << >> are reserved, but only when at start or end of token. Allowed comparisons embedded. As is <= and >=
	Tokens ending with ' or 's break off (possessive) in patterns.  
	
	Tokens starting with prefix characters ' or ! or _ keep together, except per reserved tokens.	'$junk  is one token.
	Variables ending with punctuation separate the punctuation.  $hello. is two tokens as is _0.

	Reserved characters in a composite token with _ before or after are kept. E.g. This_(_story_is_)_done
	You can include a reserved tokens by putting \ in front of them.

	Some tokens revise their start, like the pattern tokens representing comparison. They do this in the script compiler.
#endif

	// strings
	if (*ptr == '"' || ( *ptr  == '^' && ptr[1] == '"') || (*ptr == '\\' && ptr[1] == '"')) //   doublequote maybe with functional heading
	{
		// simple \"
		if (*ptr == '\\' && (!ptr[2] || ptr[2] == ' ' || ptr[2] == '\t' || ptr[2] == ENDUNIT)) 
		{
			*word = '\\';
			word[1] = '"';
			word[2] = 0;
			return ptr+2;
		}
		bool backslash = false;
		bool noblank = true;
		bool functionString = false;
		if (*ptr == '^') 
		{
			*word++ = *ptr++;	// ^"script" 
			noblank = false; // allowed blanks at start or rear
			functionString = true;
		}
		else if (*ptr == '\\') //  \"string is this"
		{
			backslash = true;
			++ptr;
		}
		char* end = ReadQuote(ptr,word,backslash,noblank);	//   swallow ending marker and points past
		if (end)  
		{
			if (*word == '"' && word[1] != FUNCTIONSTRING && !functionString) return end; // all legal within

			// verify that [ is matched with ]
			int brackets = 0;
			if (functionString)
			{
				char* at = word;
				while (*++at)
				{
					if (*at == '[' && *(at-1) != '\\') ++brackets;
					else if (*at == ']' && *(at-1) != '\\') --brackets;
				}
			}
			if (brackets) BADSCRIPT("Mismatched brackets in function string %s",word)

			// when seeing ^, see if it remaps as a function argument
			// check for internal ^ also...
			char* hat = word-1;
			if (*word == '"' && word[1] == FUNCTIONSTRING) hat = word+1;
			else if (word[1] == '"' && *word == FUNCTIONSTRING) hat = word+1;
			
			while ( (hat = strchr(hat+1,'^'))) // find a hat within
			{
				if (IsDigit(hat[1])) continue; // normal internal
				if (*(hat-1) == '\\') continue;	// escaped
				char* at = hat;
				while (*++at && (IsAlphaUTF8OrDigit(*at)  || *at == '_')){;}
				char c = *at;
				*at = 0;
				int index = GetFunctionArgument(hat);
				WORDP D = FindWord(hat); // in case its a function name
				*at = c;
				if (index >= 0) // was a function argument
				{
					char tmp[MAX_WORD_SIZE];
					strcpy(tmp,at); // protect chunk
					sprintf(hat,"^%d%s",index,tmp);
				}
				else if (D && D->internalBits & FUNCTION_NAME){;}
				else if (!renameInProgress && !(hat[1] == '$' || hat[1] == '_'))  
				{
					*at = 0;
					WARNSCRIPT("%s is not a recognized function argument. Is it intended to be?\r\n",hat)
					*at = c;
				}
			}

			hat = word-1;
			while ((hat = strchr(hat+1,'_'))) // rename _var? 
			{
				if (IsAlphaUTF8OrDigit(*(hat-1) ) || *(hat-1) == '_' || *(hat-1) == '-') continue; // not a starter
				if (IsDigit(hat[1])) continue; // normal _ var
				if (*(hat-1) == '\\' || *(hat-1) == '"') continue;	// escaped or quoted
				char* at = hat;
				while (*++at && (IsAlphaUTF8OrDigit(*at))){;} // find end
				WORDP D = FindWord(hat,at-hat,LOWERCASE_LOOKUP);
				if (D && D->internalBits & RENAMED) // remap matchvar inside  string
				{
					char tmp[MAX_WORD_SIZE];
					strcpy(tmp,at); // protect chunk
					sprintf(hat+1,"%d%s",(unsigned int)D->properties,tmp);
				}
				else if (!renameInProgress && false) // too unreliable
				{
					char c = *at;
					*at = 0;
					WARNSCRIPT("%s is not a recognized _rename. Is it intended to be?\r\n",hat)
					*at = c;
				}
			}

			hat = word-1;
			while ((hat = strchr(hat+1,'@'))) // rename @set?  
			{
				if (IsAlphaUTF8OrDigit(*(hat-1) )) continue; // not a starter
				if (IsDigit(hat[1])) continue; // normal @ var
				if (*(hat-1) == '\\') continue;	// escaped
				char* at = GetSetEnd(hat);
				WORDP D = FindWord(hat,at-hat,LOWERCASE_LOOKUP);
				if (D && D->internalBits & RENAMED)  // rename @set inside string
				{
					char tmp[MAX_WORD_SIZE];
					strcpy(tmp,at); // protect chunk
					sprintf(hat+1,"%d%s",(unsigned int)D->properties,tmp);
				}
				else if (!renameInProgress)  // can do anything safely in a simple quoted string
				{
					char c = *at;
					*at = 0;
					WARNSCRIPT("%s is not a recognized @rename. Is it intended to be?\r\n",hat)
					*at = c;
				}
			}
			hat = word-1;
			while ((hat = strchr(hat+1,'#'))) // rename #constant or ##constant
			{
				if (*(hat-1) == '\\') continue;	// escaped
				if (IsAlphaUTF8OrDigit(*(hat-1) )) continue; // not a starter
				char* at = hat;
				if (at[1] == '#')  ++at;	// user constant
				while (*++at && (IsAlphaUTF8OrDigit(*at) || *at == '_')){;} // find end
				char tmp[MAX_WORD_SIZE];
				strcpy(tmp,at); // protect chunk
				*at = 0;
				uint64 n;
				if (hat[1] == '#' && IsAlphaUTF8(hat[2])) // user constant
				{
					WORDP D = FindWord(hat,at-hat,LOWERCASE_LOOKUP);
					if (D && D->internalBits & RENAMED)  // remap #constant inside string
					{
						n = D->properties; 
						if (D->systemFlags & CONSTANT_IS_NEGATIVE) 
						{
							int64 x = (int64) n;
							x = -x;
#ifdef WIN32
							sprintf(hat,"%I64d%s",(long long int) x,tmp); 
#else
							sprintf(hat,"%lld%s",(long long int) x,tmp); 
#endif					
						}
						else
						{
#ifdef WIN32
							sprintf(hat,"%I64d%s",(long long int) n,tmp); 
#else
							sprintf(hat,"%lld%s",(long long int) n,tmp); 
#endif		
						}
					}
					else if (!renameInProgress && false)  
					{
						char c = *at;
						*at = 0;
						WARNSCRIPT("%s is not a recognized #rename. Is it intended to be?\r\n",hat)
						*at = c;
					}
				}
				else // system constant
				{
					n = FindValueByName(hat+1);
					if (!n) n = FindSystemValueByName(hat+1);
					if (!n) n = FindParseValueByName(hat+1);
					if (!n) n = FindMiscValueByName(hat+1);
					if (n)
					{
#ifdef WIN32
						sprintf(hat,"%I64d%s",(long long int) n,tmp); 
#else
						sprintf(hat,"%lld%s",(long long int) n,tmp); 
#endif		
					}
				}
				if (!*hat) 
				{
					*hat = '#';
					BADSCRIPT("Bad # constant %s",hat)
				}
			}

			return end;					//   if we did swallow a string
		}
		if (*ptr == '\\') // was this \"xxx with NO closing
		{
			memmove(word+1,word,strlen(word)+1);
			*word = '\\';
		}
		else
		{
			word = start;
			if (*start == '^') --ptr;
		}

	}

	// the normal composite token
	bool quote = false;
	while (*ptr) 
	{
		if (*ptr == ENDUNIT) break;
		if (patternContext && quote) {} // allow stuff in comparison quote
		else if (*ptr == ' ' || *ptr == '\t') break;
		if (patternContext && *ptr == '"') quote = !quote;

		char c = *ptr++;
		*word++ = c;
		*word = 0;
		if (GetNestingData(c)) // break off nesting attached to a started token unless its an escaped token
		{
			size_t len = word - start;
			if (len == 1) break;		// automatically token by itself
			if (len == 2)
			{
				if ((*start == '_' || *start == '!') && (c == '[' || c == '(' || c == '{')) break; // one token as _( or !( 
				if (*start == '\\') break;	// one token escaped
			}
			// split off into two tokens
			--ptr;
			--word;
			break;  
		}
	}
	*word = 0;

    word = start;
	size_t len = strlen(word);
	if (len == 0) return ptr; 
	if (*word == '#') // is this a constant from dictionary.h? or user constant
	{
		uint64 n;
		if (word[1] == '#' && IsAlphaUTF8(word[2])) // user constant
		{
			WORDP D = FindWord(word,0,LOWERCASE_LOOKUP);
			if (D && D->internalBits & RENAMED)  // remap #constant 
			{
				n = D->properties; 
				if (D->systemFlags & CONSTANT_IS_NEGATIVE) 
				{
					int64 x = (int64) n;
					x = -x;
#ifdef WIN32
					sprintf(word,"%I64d",(long long int) x); 
#else
					sprintf(word,"%lld",(long long int) x); 
#endif					
				}
				else
				{
#ifdef WIN32
					sprintf(word,"%I64d",(long long int) n); 
#else
					sprintf(word,"%lld",(long long int) n); 
#endif		
				}
			}

			else if (renameInProgress) {;} // leave token alone, defining
			else BADSCRIPT("Bad user constant %s",word)
		}
		else // system constant
		{
			n = FindValueByName(word+1);
			if (!n) n = FindSystemValueByName(word+1);
			if (!n) n = FindParseValueByName(word+1);
			if (!n) n = FindMiscValueByName(word+1);
			if (n)
			{
#ifdef WIN32
				sprintf(word,"%I64d",(long long int) n); 
#else
				sprintf(word,"%lld",(long long int) n); 
#endif		
			}
			else if (!IsDigit(word[1]) && word[1] != '!') //treat rest as a comment line (except if has number after it, which is user text OR internal arg reference for function
			{
				if (IsAlphaUTF8(word[1])) 
					BADSCRIPT("Bad numeric # constant %s",word)
				*ptr = 0;
				*word = 0;
			}
		}
	}
	if ( *word == '_' && (IsAlphaUTF8(word[1]) ) ) // is this a rename _
	{
		WORDP D = FindWord(word);
		if (D && D->internalBits & RENAMED) sprintf(word+1,"%d",(unsigned int)D->properties); // remap match var convert to number
		else if (false && !renameInProgress && !patternContext)  // patterns can underscore ANYTING
			WARNSCRIPT("%s is not a recognized _rename. Is it one?\r\n",word)
	}
	if (*word == '\'' &&  word[1] == '_' && (IsAlphaUTF8(word[2]) ) ) // is this a rename _ with '
	{
		WORDP D = FindWord(word+1);
		if (D && D->internalBits & RENAMED) sprintf(word+2,"%d",(unsigned int)D->properties); // remap match var convert to number
		else if (!renameInProgress && !patternContext)  // patterns can underscore ANYTING
			WARNSCRIPT("%s is not a recognized _rename. Should it be?\r\n",word+1)
	}
	if ( *word == '@' && IsAlphaUTF8(word[1]) ) // is this a rename @
	{
		char* at = GetSetEnd(word);
		WORDP D = FindWord(word,at-word);
		if (D && D->internalBits & RENAMED) // remap @set in string
		{
			char tmp[MAX_WORD_SIZE];
			strcpy(tmp,at); // protect chunk
			sprintf(word+1,"%d%s",(unsigned int)D->properties,tmp);
		}
		else if (!renameInProgress)  WARNSCRIPT("%s is not a recognized @rename. Is it intended to be?\r\n",word)
	}
	if ( *word == '@' && word[1] == '_' && IsAlphaUTF8(word[2])) // is this a rename @_0+
	{
		size_t len = strlen(word);
		char c = word[len-1];
		word[len-1] = 0;
		WORDP D = FindWord(word+1,len-2);
		word[len-1] = c;
		if (D && D->internalBits & RENAMED) 
		{
			sprintf(word+2,"%d%c",(unsigned int)D->properties,c); // remap @set in string
		}
		else if (!renameInProgress)  WARNSCRIPT("%s is not a recognized @rename. Is it intended to be?\r\n",word)
	}

	// some tokens require special splitting
		
	//   break off starting << from <<hello   
	if (*word == '<' && word[1] != '=')
	{
		if (len == 3 && *word == word[1] && word[2] == '=') {;}
		else if (word[1] == '<')
		{
			if (word[2]) // not assign operator
			{
				ptr -= strlen(word) - 2;  // safe
				word[2] = 0;
				len -= 2;
			}
		}
	}

	//   break off ending  >> from hello>> 
	if (len > 2 && word[len-1] == '>')
	{
		if (len == 3 && *word == word[1] && word[2] == '=') {;}
		else if (word[len-2] == '>')
		{
			ptr -= 2;
			word[len-2] = 0;
			len -= 2;
		}
	}

	// break off punctuation from variable end 
	if (len > 2 && ((*word == '$' && !IsDigit(word[1]))  || *word == '^' || (*word == '@' && IsDigit(word[1])) || *word == '%' || (*word == '_' && IsDigit(word[1])) || (*word == '\'' && word[1] == '_'))) // not currency
	{
		if (!patternContext || word[len-1] != '?') // BUT NOT $$xxx? in pattern context
		{
			while (IsRealPunctuation(word[len-1])) // one would be enough, but $hello... needs to be addressed
			{
				--len;
				--ptr;
			}
			word[len] = 0;
		}
	}

	// break off opening < in pattern
	if (patternContext && *word == '<' && word[1] != '<')
	{
		ptr -= len - 1;
		len = 1;
		word[1] = 0;
	}

	// break off closing > in pattern unless escaped or notted
	if (len == 2 && (*word == '!' || *word == '\\')){;}
	else if (patternContext && len > 1 && word[len-1] == '>' && word[len-2] != '>' && word[len-2] != '_' && word[len-2] != '!')
	{
		ptr -= len - 1;
		--len;
		word[len-1] = 0;
	}

	// find internal comparison op if any
	char* at = (patternContext) ? FindComparison(word) : 0;
	if (at && *word == '*' && !IsDigit(word[1])) 
	{
		if (compiling) BADSCRIPT("TOKENS-1 Cannot do comparison on variable gap %s . Memorize and compare against _# instead later. ",word)
	}
	
	if (at) // revise comparison operators
	{
		if (*at == '!') ++at;
		++at;
		
		if (*at == '^' && at[1]) // remap function arg on right side.
		{
			int index = GetFunctionArgument(at);
			if (index >= 0) sprintf(at,"^%d",index);
		}
		if (*at == '_' && IsAlphaUTF8(word[1]) ) // remap rename matchvar arg on right side.
		{
			WORDP D = FindWord(at);
			if (D && D->internalBits & RENAMED) sprintf(at,"_%d",(unsigned int)D->properties);
		}
		if (*at == '@' && IsAlphaUTF8(word[1]) ) // remap @set arg on right side.
		{
			char* at1 = GetSetEnd(at);
			WORDP D = FindWord(at,at1-at);
			if (D && D->internalBits & RENAMED) // remap @set on right side
			{
				char tmp[MAX_WORD_SIZE];
				strcpy(tmp,at1); // protect chunk
				sprintf(at+1,"%d%s",(unsigned int)D->properties,tmp);
			}
		}

		// check for remap on LHS
		if (*word == '^')
		{
			char c = *--at;
			*at = 0;
			int index = GetFunctionArgument(word);
			*at = c;
			char hold[MAX_WORD_SIZE];
			if (index >= 0) 
			{
				sprintf(hold,"^%d%s",index,at);
				strcpy(word,hold);
			}
		}
		// check for rename on LHS
		if (*word == '_' && IsAlphaUTF8(word[1]) )
		{
			char* at = word;
			while (IsAlphaUTF8OrDigit(*++at)){;}
			WORDP D = FindWord(word,at-word);
			if (D && D->internalBits & RENAMED) // remap match var
			{
				char hold[MAX_WORD_SIZE];
				sprintf(hold,"%d%s",(unsigned int)D->properties,at);
				strcpy(word+1,hold);
			}
		}
		// check for rename on LHS
		if (*word == '@' && IsAlphaUTF8(word[1]) ) 
		{
			char* at = GetSetEnd(word);
			WORDP D = FindWord(word,at-word);
			if (D && D->internalBits & RENAMED) // remap @set in string
			{
				char tmp[MAX_WORD_SIZE];
				strcpy(tmp,at); // protect chunk
				sprintf(word+1,"%d%s",(unsigned int)D->properties,tmp);
			}
		}
	}
	// when seeing ^, see if it remaps as a function argument
	// check for internal ^ also...
	char* hat = word-1;
	while ( (hat = strchr(hat+1,'^'))) // find a hat within
	{
		char* at = hat;
		while (*++at && (IsAlphaUTF8(*at)  || *at == '_' || IsDigit(*at))){;}
		char c = *at;
		*at = 0;
		char trial[MAX_WORD_SIZE];
		strcpy(trial,hat);
		*at = c;
		
		while (*trial)
		{
			int index = GetFunctionArgument(trial);
			if (index >= 0) 
			{
				char tmp[MAX_WORD_SIZE];
				strcpy(tmp,at); // protect chunk
				sprintf(hat,"^%d%s%s",index,hat+strlen(trial),tmp);
				break;
			}
			else trial[0] = 0;	// just abort it for now shrink it smaller, to handle @9subject kinds of behaviors 
		}
	}

	// same for quoted function arg
	if (*word == '\'' && word[1] == '^' && word[2])
	{
		int index = GetFunctionArgument(word+1);
		if (index >= 0) sprintf(word,"'^%d",index);
	}

	// break apart math on variables eg $value+2 
	if (*word == '%' || *word == '%' || *word == '$')
	{
		char* at = word;
		while (IsAlphaUTF8(*++at) );  // find end of initial word
		if (*at && IsPunctuation(*at) & ARITHMETICS && *at != '=')
		{
			// - is legal in a var or word token
			if (*at != '-' || (!IsAlphaUTF8OrDigit(at[1]) && at[1] != '_'))
			{
				ptr -= strlen(at);
				*at = 0;
				len = at - start;
			}
		}
	}
	char* tilde = (IsAlphaUTF8(*word)) ? strchr(word+1,'~') : 0;
	if (tilde) // has specific meaning like African-american~1n or African-american~1
	{
		if (IsDigit(*++tilde)) // we know the meaning, removing any POS marker since that is redundant
		{
			if (IsDigit(*++tilde)) ++tilde;
			if (*tilde && !tilde[1])  *tilde = 0; // trim off pos marker

			// now force meaning to master
			MEANING M = ReadMeaning(word,true,false);
			if (M) 
			{
				M = GetMaster(M);
				sprintf(word,"%s~%d",Meaning2Word(M)->word,Meaning2Index(M));
			}
		}
	}

	InsureAppropriateCase(word);
	return ptr; 
}

char* ReadDisplayOutput(char* ptr,char* buffer) // locate next output fragment to display (that will be executed)
{
	char next[MAX_WORD_SIZE];
	char* hold;
	*buffer = 0;
	char* out = buffer;
	while (*ptr != ENDUNIT) // not end of data
	{
		ptr = ReadCompiledWord(ptr,out); // move token 
		char* copied = out;
		out += strlen(out);
		strcpy(out," ");
		++out;
		*out = 0;
		hold = ReadCompiledWord(ptr,next); // and the token after that?
		if (IsAlphaUTF8OrDigit(*copied) ) // simple output word was copied
		{
			if (!*next || !IsAlphaUTF8OrDigit(*next)) break; //  followed by something else simple
		}
		else if (*buffer == ':' && buffer[1]) // testing command occupies the rest always
		{
			char* end = strchr(ptr,ENDUNIT);
			if (end)
			{
				strncpy(out,ptr,end-ptr);
				out += end-ptr;
				*out = 0;
			}
			ptr = NULL;
			break;
		}
		else if (*buffer == '^' && *next == '(') // function call
		{
			char* end = BalanceParen(ptr+1); // function call args
			strncpy(out,ptr,end-ptr);
			out += end-ptr;
			*out = 0;
			ptr = end;
			break;
		}
		else if ((*buffer == '$' && (buffer[1] == '$' || IsAlphaUTF8(buffer[1]) )) || (*buffer == '%' && IsAlphaUTF8(buffer[1])) || (*buffer == '@' && IsDigit(buffer[1])) || (*buffer == '_' && IsDigit(buffer[1]))  ) // user or system variable or factset or match variable
		{
			if (*next != '=' && next[1] != '=') break; // not an assignment statement
			while (hold) // read op, value pairs
			{
				strcpy(out,next); // transfer assignment op or arithmetic op 
				out += strlen(out);
				strcpy(out," ");
				++out;
				ptr = ReadCompiledWord(hold,next); // read value
				strcpy(out,next); // transfer value
				out += strlen(out);
			
				// if value is a function call, get the whole call
				if (*next == '^' && *ptr == '(')
				{
					char* end = BalanceParen(ptr+1); // function call args
					strncpy(out,ptr,end-ptr);
					out += end-ptr;
					*out = 0;
					ptr = end;
				}

				strcpy(out," ");
				++out;
				if (*ptr != ENDUNIT) // more to rule
				{
					hold = ReadCompiledWord(ptr,next); // is there more to assign
					if (IsArithmeticOperator(next)) continue; // need to swallow op and value pair
				}
				break;
			}
			break;
		}
		else if (*buffer == '[') // choice area
		{
			//   find closing ]
			char* end = ptr-1;
			while (ALWAYS) 
			{
				end = strchr(end+1,']'); // find a closing ] 
				if (!end) break; // failed
				if (*(end-1) != '\\') break; // ignore literal \[
			}
			if (end) // found end of a [] pair
			{
				++end;
				strncpy(out,ptr,end-ptr);
				out += end-ptr;
				*out = 0;
				ptr = end + 1;
				if (*ptr != '[') break; // end of choice zone
			}
		}
		else break;
	}
	if (!stricmp(buffer,"^^loop ( -1 ) "))  strcpy(buffer,"^^loop ( ) ");	// shorter notation
	return ptr;
}

////////////////// CAN BE COMPILED AWAY

#ifndef DISCARDSCRIPTCOMPILER

#define MAX_TOPIC_SIZE  500000
#define MAX_TOPIC_RULES 32767
#define MAX_TABLE_ARGS 20

static unsigned int hasPlans;					// how many plans did we read

static int missingFiles;						// how many files of topics could not be found

static int spellCheck = 0;						// what do we spell check
static int topicCount = 0;						// how many topics did we compile
static char duplicateTopicName[MAX_WORD_SIZE];	// potential topic name repeated
static char assignKind[MAX_WORD_SIZE];	// what we are assigning from in an assignment call
static char currentTopicName[MAX_WORD_SIZE];	// current topic being read
static char lowercaseForm[MAX_WORD_SIZE];		// a place to put a lower case copy of a token
static WORDP currentFunctionDefinition;			// current macro defining or executing
static FILE* patternFile = NULL; // where to store pattern words
static char nextToken[MAX_WORD_SIZE];			// current lookahead token

static char verifyLines[100][MAX_WORD_SIZE];	// verification lines for a rule to dump after seeing a rule
static unsigned int verifyIndex = 0;			// index of how many verify lines seen

#ifdef INFORMATION
Script compilation validates raw topic data files amd converts them into efficient-to-execute forms.
This means creating a uniform spacing of tokens and adding annotations as appropriate.

Reading a topic file (on the pattern side) often has tokens jammed together. For example all grouping characters like
() [ ] { } should be independent tokens. Possessive forms like cat's and cats' should return as two tokens.

Just as all contractions will get expanded to the full word.

Some tokens can be prefixed with ! or single-quote or _ .
In order to be able to read special characters (including prefix characters) literally, one can prefix it with \  as in \[  . The token returned includes the \.
\! means the exclamation mark at end of sentence. 
You are not required to do \? because it is directly a legal token, but you can.  
You CANNOT test for . because it is the default and is subsumed automatically.
#endif

static void ClearBeenHere(WORDP D, uint64 junk)
{
	RemoveInternalFlag(D,BEEN_HERE);
}

bool TopLevelUnit(char* word) // major headers (not kinds of rules)
{
	return (!stricmp(word,":quit") || !stricmp(word,"canon:")  || !stricmp(word,"replace:")  || !stricmp(word,"query:")  || !stricmp(word,"concept:") || !stricmp(word,"data:") || !stricmp(word,"plan:") 
		|| !stricmp(word,"outputMacro:") || !stricmp(word,"patternMacro:") || !stricmp(word,"dualMacro:")  || !stricmp(word,"table:") || !stricmp(word,"tableMacro:") || !stricmp(word,"rename:") || 
		!stricmp(word,"describe:") ||  !stricmp(word,"bot:") || !stricmp(word,"topic:") || (*word == ':' && IsAlphaUTF8(word[1])) );	// :xxx is a debug command
}

static char* FlushToTopLevel(FILE* in,char* ptr,unsigned int depth,char* data)
{
	globalDepth = depth;
	if (data) *data = 0; // remove data
	char word[MAX_WORD_SIZE];
	int oldindex = jumpIndex;
	jumpIndex = -1; // prevent ReadNextSystemToken from possibly crashing.
	*newBuffer = 0;
	while (ALWAYS)
	{
		char* quote = NULL;
		while ((quote = strchr(ptr,'"'))) ptr = quote + 1; //  flush quoted things
		ptr = ReadNextSystemToken(in,ptr,word,false);
		if (!*word) break;
		MakeLowerCopy(lowercaseForm,word);
		if (TopLevelUnit(lowercaseForm) || TopLevelRule(lowercaseForm)) 
		{
			ptr -= strlen(word); // safe
			break;
		}
	}
	jumpIndex = oldindex;
	return ptr;
}

static bool IsSet(char* word)
{
	if (!word[1]) return true;
	WORDP D = FindWord(word,0,LOWERCASE_LOOKUP);
	return (D && D->internalBits & CONCEPT) ? true : false;
}

static bool IsTopic(char* word)
{
	if (!word[1]) return true;
	WORDP D = FindWord(word,0,LOWERCASE_LOOKUP);
	return (D && D->internalBits & TOPIC) ? true : false;
}

static void DoubleCheckSetOrTopic()
{
	FILE* in = FopenReadWritten("TOPIC/missingsets.txt");
	if (!in) return;
	*currentFilename = 0; // dont tell the name of the file
	while (ReadALine(readBuffer,in)  >= 0) 
    {
		char word[MAX_WORD_SIZE];
		ReadCompiledWord(readBuffer,word);
		if (!IsSet(word) && !IsTopic(word)) 
			WARNSCRIPT("Undefined set or topic %s\r\n",readBuffer)
	}
	fclose(in);
	remove("TOPIC/missingSets.txt");
}

static void CheckSetOrTopic(char* name) // we want to prove all references to set get defined
{
	if (*name == '~' && !name[1]) return; // simple ~ reference
	char word[MAX_WORD_SIZE];
	MakeLowerCopy(word,name);
	char* label = strchr(word,'.'); // set reference might be ~set or  ~set.label
	if (label) *label = 0; 
	if (IsSet(word) || IsTopic(word)) return;

	WORDP D = StoreWord(word);
	if (D->internalBits & BEEN_HERE) return; // already added to check file
	AddInternalFlag(D,BEEN_HERE);
	FILE* out = FopenUTF8WriteAppend("TOPIC/missingsets.txt");
	fprintf(out,"%s line %d in %s\r\n",word,currentFileLine,currentFilename);
	fclose(out);
}

static char* AddVerify(char* kind, char* sample)
{
	char* comment = strstr(sample,"# "); // locate any comment on the line and kill it
	if (comment) *comment = 0;
	sprintf(verifyLines[verifyIndex++],"%s %s",kind,SkipWhitespace(sample)); 
	return 0;	// kill rest of line
}

static void WriteVerify()
{
	if (!verifyIndex) return;
	char name[100];
	sprintf(name,"VERIFY/%s-b%c.txt",currentTopicName+1, (buildID == BUILD0) ? '0' : '1'); 
	FILE* valid  = FopenUTF8WriteAppend(name);
	static bool init = true;
	if (!valid && init) 
	{
		MakeDirectory("VERIFY");
		init = false;
		valid  = FopenUTF8WriteAppend(name);
	}

	if (valid)
	{
		char* space = "";
		if (REJOINDERID(currentRuleID)) space = "    ";
		for (unsigned int i = 0; i < verifyIndex; ++i) 
		{
			fprintf(valid,"%s %s.%d.%d %s\r\n",space,currentTopicName,TOPLEVELID(currentRuleID),REJOINDERID(currentRuleID),verifyLines[i]); 
		}
		fclose(valid);
	}

	verifyIndex = 0;
}

#ifdef INFORMATION
We mark words that are not normally in the dictionary as pattern words if they show up in patterns.
For example, the names of synset heads are not words, but we use them in patterns. They will
be marked during the scan phase of matching ONLY if some pattern "might want them". I.e., 
they have a pattern-word mark on them. same is true for multiword phrases we scan.

Having marked words also prevents us from spell-correcting something we were expecting but which is not a legal word.
#endif


static void DownHierarchy(MEANING T, FILE* out, int depth)
{
    if ( !T) return;
    WORDP D = Meaning2Word(T);
	if (D->internalBits & VAR_CHANGED) return;
	if (*D->word == '~') fprintf(out,"%s depth=%d\r\n",D->word,depth); 
	else  fprintf(out,"  %s\r\n",D->word); 
	D->internalBits |= VAR_CHANGED;
    unsigned int index = Meaning2Index(T);
    unsigned int size = GetMeaningCount(D);
    if (!size) size = 1; 
	if (*D->word == '~') // show set members
	{
		FACT* F = GetObjectNondeadHead(D);
		unsigned int i = 0;
		while (F)
		{
			if (F->verb == Mmember)
			{
				MEANING M = F->subject;
				WORDP S = Meaning2Word(M);
				DownHierarchy(M,out,depth+1);
			}
			F = GetObjectNondeadNext(F);
		}
		fprintf(out,". depth=%d\r\n",depth); 
	}
}

static void WriteKey(char* word)
{
	if (!compiling || spellCheck != NOTE_KEYWORDS || *word == '_' || *word == '\'' || *word == '$' || *word == '%' || *word == '@') return;
	WORDP D = StoreWord(word);
	FILE* out = FopenUTF8WriteAppend("TMP/keys.txt");
	if (out)
	{
		DownHierarchy(MakeMeaning(StoreWord(word)),out,0);
		fclose(out);
	}
}

static void WritePatternWord(char* word)
{
	if (*word == '~' || *word == '$' || *word == '^') return; // not normal words

	if (IsDigit(*word)) // any non-number stuff
	{
		char* ptr = word;
		while (*++ptr)
		{
			if (!IsDigit(*ptr) && *ptr != '.' && *ptr != ',') break;
		}
		if (!*ptr) return;	// ordinary number
	}
	
	// do we want to note this word
	WORDP D = StoreWord(word);
	if (!(D->properties & NORMAL_WORD)) AddSystemFlag(D,PATTERN_WORD);
	if (!compiling) return; 

	// case sensitivity?
	char tmp[MAX_WORD_SIZE];
	MakeLowerCopy(tmp,word);
	WORDP lower = FindWord(word,0,LOWERCASE_LOOKUP);
	WORDP upper = FindWord(word,0,UPPERCASE_LOOKUP);
	if (!strcmp(tmp,word))  {;} // came in as lower case
	else if (upper && GetMeaningCount(upper) > 0){;} // clearly known as upper case
	else if (lower && lower->properties & NORMAL_WORD && !(lower->properties & (DETERMINER|AUX_VERB))) WARNSCRIPT("Keyword %s should not be uppercase - did prior rule fail to close\r\n",word)
	else if (spellCheck && lower && lower->properties & VERB && !(lower->properties & NOUN)) 
		WARNSCRIPT("Uppercase keyword %s is usually a verb.  Did prior rule fail to close\r\n",word)
	
	if (D->properties & NORMAL_WORD) return;	// already a known word
	if (D->internalBits & BEEN_HERE) return;	//   already written to pattern file or doublecheck topic ref file
	if (patternFile) 
	{
		fprintf(patternFile,"%s\r\n",word);
		AddInternalFlag(D,BEEN_HERE);
	}
}

static void NoteUse(char* label,char* topic)
{
	MakeUpperCase(label);
	WORDP D = FindWord(label);
	if (!D || !(D->internalBits & LABEL))
	{
		FILE* out = FopenUTF8WriteAppend("TOPIC/missingLabel.txt");
		if (out)
		{
			fprintf(out,"%s %s %s %d\r\n",label,topic,currentFilename,currentFileLine);
			fclose(out);
		}
	}
}

static void ValidateCallArgs(WORDP D,char* arg1, char* arg2,char argset[50][MAX_WORD_SIZE])
{
	if (!stricmp(D->word,"^next"))
	{	
		if (stricmp(arg1,"RESPONDER") && stricmp(arg1,"REJOINDER") && stricmp(arg1,"RULE") && stricmp(arg1,"GAMBIT") && stricmp(arg1,"INPUT") && stricmp(arg1,"FACT")) 
			BADSCRIPT("CALL- 62 1st argument to ^next must be FACT OR INPUT or RULE or GAMBIT or RESPONDER or REJOINDER - %s",arg1)
	}	
	else if(!stricmp(D->word,"^keephistory"))
	{
		if (stricmp(arg1,"USER") && stricmp(arg1,"BOT") )
			BADSCRIPT("CALL- ? 1st argument to ^keephistory must be BOT OR USER - %s",arg1)
	}
	else if (!stricmp(D->word,"^conceptlist"))
	{
		if (stricmp(arg1,"TOPIC") && stricmp(arg1,"CONCEPT") && stricmp(arg1,"BOTH"))
			BADSCRIPT("CALL- ? 1st argument to ^conceptlist must be CONCEPT or TOPIC or BOTH - %s",arg1)
	}
	else if (!stricmp(D->word,"^field") && IsAlphaUTF8(*arg2))
	{	
		if (*arg2 != 's' && *arg2 != 'S' &&  *arg2 != 'v' && *arg2 != 'V' && *arg2 != 'O' && *arg2 != 'o'  && *arg2 != 'F' && *arg2 != 'f' && *arg2 != 'A' && *arg2 != 'a' && *arg2 != 'R' && *arg2 != 'r') 
			BADSCRIPT("CALL- 9 2nd argument to ^field must be SUBJECT or VERB or OBJECT or ALL or RAW or FLAG- %s",arg1)
	}
	else if (!stricmp(D->word,"^decodepos") )
	{
		if (stricmp(arg1,"POS") && stricmp(arg1,"ROLE")) 
			BADSCRIPT("CALL- ? 1st argument to ^decodepos must be POS or ROLE - %s",arg1)
	}
	else if (!stricmp(D->word,"^position") )
	{
		if (stricmp(arg1,"START") && stricmp(arg1,"END") && stricmp(arg1,"BOTH")) 
			BADSCRIPT("CALL- ? 1st argument to ^position must be START, END, BOTH, - %s",arg1)
	}
	else if (!stricmp(D->word,"^getparse") )
	{
		if (stricmp(arg2,"PHRASE") && stricmp(arg2,"VERBAL") && stricmp(arg2,"CLAUSE")&& stricmp(arg2,"NOUNPHRASE")) 
			BADSCRIPT("CALL- ? 2nd argument to ^getparse must be PHRASE, VERBAL, CLAUSE, NOUNPHRASE- %s",arg2)
	}
	else if (!stricmp(D->word,"^reset"))
	{
		if (stricmp(arg1,"user") && stricmp(arg1,"topic") && stricmp(arg1,"output")  && *arg1 != '@') 
			BADSCRIPT("CALL- 10 1st argument to ^reset must be USER or TOPIC or OUTPUT or an @set- %s",arg1)
	}
	else if (!stricmp(D->word,"^substitute"))
	{
		if (stricmp(arg1,"word") && stricmp(arg1,"character")) 
			BADSCRIPT("CALL- 11 1st argument to ^substitute must be WORD or CHARACTER- %s",arg1)
	}
	else if (!stricmp(D->word,"^setrejoinder"))
	{
		if (*arg2 && stricmp(arg1,"input") && stricmp(arg1,"output") && stricmp(arg1,"copy") ) 
			BADSCRIPT("CALL- 63 call to ^setrejoinder requires INPUT or OUTPUT or COPY as the 1st arg.")
		if (!*arg2 && (!stricmp(arg1,"input") || !stricmp(arg1,"output") || !stricmp(arg1,"copy")) )
			BADSCRIPT("CALL- 63 call to ^setrejoinder requires 2nd argument naming what rule to use as rejoinder")
	}
	else if (!stricmp(D->word,"^pos"))
	{
		if (stricmp(arg1,"conjugate") && stricmp(arg1,"raw")&& stricmp(arg1,"allupper")  && stricmp(arg1,"syllable") && stricmp(arg1,"ADJECTIVE") && stricmp(arg1,"ADVERB")   && stricmp(arg1,"VERB") && stricmp(arg1,"AUX") && stricmp(arg1,"PRONOUN") && stricmp(arg1,"TYPE") && stricmp(arg1,"HEX32")&& stricmp(arg1,"HEX64")
			 && stricmp(arg1,"NOUN") && stricmp(arg1,"DETERMINER") && stricmp(arg1,"PLACE")
 			 && stricmp(arg1,"capitalize") && stricmp(arg1,"uppercase") && stricmp(arg1,"lowercase") && stricmp(arg1,"canonical") && stricmp(arg1,"integer"))
 			BADSCRIPT("CALL- 12 1st argument to ^pos must be SYLLABLE or ALLUPPER or  VERB or AUX or PRONOUN or NOUN or ADJECTIVE or ADVERB or DETERMINER or PLACE or CAPITALIZE or UPPERCASE or LOWERCASE or CANONICAL or INTEGER or HEX32 or HEX64 - %s",arg1)
	}
	else if (!stricmp(D->word,"^getrule"))
	{
		if (stricmp(arg1,"TOPIC") &&  stricmp(arg1,"OUTPUT") && stricmp(arg1,"PATTERN") && stricmp(arg1,"LABEL") && stricmp(arg1,"TYPE")  && stricmp(arg1,"TAG") && stricmp(arg1,"USABLE")) 
 			BADSCRIPT("CALL- 13 1st argument to ^getrule must be TAG or TYPE or LABEL or PATTERN or OUTPUT or TOPIC or USABLE - %s",arg1)
	}
	else if (!stricmp(D->word,"^poptopic"))
	{
		if (*arg1 && *arg1 != '~' && *arg1 != '$' && *arg1 != '_' && *arg1 != '%' && *arg1 != '^')
 			BADSCRIPT("CALL- 61 1st argument to ^poptopic must be omitted or a topic name or variable which will return a topic name - %s",arg1)
	}
	else if (!stricmp(D->word,"^nextrule"))
	{
		if (stricmp(arg1,"GAMBIT") && stricmp(arg1,"RESPONDER") && stricmp(arg1,"REJOINDER")  && stricmp(arg1,"RULE")) 
 			BADSCRIPT("CALL- 14 1st argument to ^getrule must be TAG or TYPE or LABEL or PATTERN or OUTPUT - %s",arg1)
	}
	else if (!stricmp(D->word,"^end"))
	{
		if (stricmp(arg1,"RULE") && stricmp(arg1,"CALL") && stricmp(arg1,"LOOP") && stricmp(arg1,"TOPIC") && stricmp(arg1,"SENTENCE") && stricmp(arg1,"INPUT")  && stricmp(arg1,"PLAN")) 
 			BADSCRIPT("CALL- 15 1st argument to ^end must be RULE or LOOP or TOPIC or SENTENCE or INPUT or PLAN- %s",arg1)
	}
	else if (!stricmp(D->word,"^fail"))
	{
		if (stricmp(arg1,"RULE") && stricmp(arg1,"CALL") && stricmp(arg1,"LOOP")  && stricmp(arg1,"TOPIC") && stricmp(arg1,"SENTENCE") && stricmp(arg1,"INPUT")) 
 			BADSCRIPT("CALL- 16 1st argument to ^fail must be RULE or LOOP or TOPIC or SENTENCE or INPUT - %s",arg1)
	}
	else if (!stricmp(D->word,"^nofail"))
	{
		if (stricmp(arg1,"RULE") &&  stricmp(arg1,"LOOP") && stricmp(arg1,"TOPIC") && stricmp(arg1,"SENTENCE") && stricmp(arg1,"INPUT")) 
 			BADSCRIPT("CALL- 16 1st argument to ^nofail must be RULE or LOOP or TOPIC or SENTENCE or INPUT - %s",arg1)
	}
	else if (!stricmp(D->word,"^compute"))
	{
		char* op = arg2;
		if (stricmp(op,"+") && stricmp(op,"plus") && stricmp(op,"add") && stricmp(op,"and") &&
			stricmp(op,"sub") && stricmp(op,"minus") && stricmp(op,"subtract") && stricmp(op,"deduct") && stricmp(op,"-")  &&
			stricmp(op,"x") && strnicmp(op,"times",4) && stricmp(op,"multiply") && stricmp(op,"*") &&
			stricmp(op,"divide") && stricmp(op,"quotient") && stricmp(op,"/") &&
			stricmp(op,"remainder") && stricmp(op,"modulo") && stricmp(op,"mod") && stricmp(op,"%") && stricmp(op,"random") &&
			stricmp(op,"root") && stricmp(op,"square_root")   && stricmp(op,"power") && stricmp(op,"exponent") && *op != '^' && *op != '_' && *op != '$')  // last covers macro args and exponents

			BADSCRIPT("CALL- 17 2nd argument to ^compute must be numeric operation - %s",op)
	}
	else if (!stricmp(D->word,"^counttopic") && IsAlphaUTF8(*arg1))
	{
		if (strnicmp(arg1,"gambit",6) && stricmp(arg1,"used") && strnicmp(arg1,"rule",4) && stricmp(arg1,"available"))  
			BADSCRIPT("CALL-20 CountTopic 1st arg must be GAMBIT or RULE or AVAILABLE or USED - %s",arg1)
	}
	else if (!stricmp(D->word,"^phrase"))
	{
		if (stricmp(arg1,"adjective") && stricmp(arg1,"verbal")&& stricmp(arg1,"noun")  && stricmp(arg1,"preposition"))  BADSCRIPT("CALL-21 ^Phrase 1st arg must be adjective or verbal or noun or preposition - %s",arg1)
	}
	else if (!stricmp(D->word,"^hasgambit") && IsAlphaUTF8(*arg2))
	{
		if (stricmp(arg2,"last") && stricmp(arg2,"any") )  BADSCRIPT("CALL-21 HasGambit 2nd arg must be omitted or be LAST or ANY - %s",arg1)
	}
	else if (!stricmp(D->word,"^lastused" ))
	{
		if (strnicmp(arg2,"gambit",6) && strnicmp(arg2,"rejoinder",9) && strnicmp(arg2,"responder",9) && stricmp(arg2,"any"))  BADSCRIPT("CALL-22 LastUsed 2nd arg must be GAMBIT or REJOINDER or RESPONDER or ANY - %s",arg2)
	}
	else if ((!stricmp(nextToken,"^first") || !stricmp(nextToken,"^last") || !stricmp(nextToken,"^random")) && *arg2) BADSCRIPT("CALL-23 Too many arguments to first/last/random - %s",arg2)
	else if (!stricmp(D->word,"^respond") && atoi(arg1))  BADSCRIPT("CALL-? argument to ^respond should be a topic, not a number. Did you intend ^response? - %s",arg1)
	else if (!stricmp(D->word,"^response") && *arg1 == '~')  BADSCRIPT("CALL-? argument to ^response should be a number, not a topic. Did you intend ^respond? - %s",arg1)
	else if (!stricmp(D->word,"^burst") && !stricmp(arg1,"wordcount")) BADSCRIPT("CALL-? argument to ^burst renamed. Use 'count' instead of 'wordcount'")
	//   validate inference calls if we can
	else if (!strcmp(D->word,"^query"))
	{
		unsigned int flags = atoi(argset[9]);
		if (flags & (USER_FLAG1|USER_FLAG2|USER_FLAG3|USER_FLAG4) && !strstr(arg1,"flag_")) BADSCRIPT("CALL-24 ^query involving USER_FLAG1 must be named xxxflag_")
		if (!stricmp(arg1,"direct_s") || !stricmp(arg1,"exact_s"))
		{
			if (!*arg2 || *arg2 == '?') BADSCRIPT("CALL-24 Must name subject argument to query")
			if (*argset[3] && *argset[3] != '?') BADSCRIPT("CALL-25 Cannot name verb argument to query %s - %s",arg1,argset[3])
			if (*argset[4] && *argset[4] != '?') BADSCRIPT("CALL-26 Cannot name object argument to query %s - %s",arg1,argset[4])
			if (*argset[8] && *argset[8] != '?') BADSCRIPT("CALL-27 Cannot name propgation argument to query %s - %s",arg1,argset[8])
			if (*argset[9] && *argset[9] != '?') BADSCRIPT("CALL-28 Cannot name match argument to query %s - %s",arg1,argset[9])
		}
		flags = atoi(argset[5]);
		if (flags & (USER_FLAG1|USER_FLAG2|USER_FLAG3|USER_FLAG4)  && flags < 0x00ffffff) WARNSCRIPT("Did you want a xxxflag_ query with USER_FLAG in 9th position for %s\r\n",arg1)
		if (!stricmp(arg1,"direct_v") || !stricmp(arg1,"exact_v"))
		{
			if (*arg2 && *arg2 != '?') BADSCRIPT("CALL-29 Cannot name subject argument to query - %s",arg2)
				if (!*argset[3] || *argset[3] == '?') BADSCRIPT("CALL-30 Must name verb argument to query")
			if (*argset[4] && *argset[4] != '?') BADSCRIPT("CALL-31 Cannot name object argument to query %s - %s",arg1,argset[4])
			if (*argset[8] && *argset[8] != '?') BADSCRIPT("CALL-32 Cannot name propgation argument to query %s - %s",arg1,argset[8])
			if (*argset[9] && *argset[9] != '?') 
				BADSCRIPT("CALL-33 Cannot name match argument to query %s - %s",arg1,argset[9])
		}
		if (!stricmp(arg1,"direct_o") || !stricmp(arg1,"exact_o"))
		{
			if (*arg2 && *arg2 != '?') BADSCRIPT("CALL-34 Cannot name subject argument to query -%s",arg2)
			if (*argset[3] && *argset[3] != '?') BADSCRIPT("CALL-35 Cannot name verb argument to query %s - %s",arg1,argset[3])
			if (!*argset[4] || *argset[4] == '?') BADSCRIPT("CALL-36 Must name object argument to query")
			if (*argset[8] && *argset[8] != '?') BADSCRIPT("CALL-37 Cannot name propgation argument to query %s - %s",arg1,argset[8])
			if (*argset[9] && *argset[9] != '?') BADSCRIPT("CALL-38 Cannot name match argument to query %s - %s",arg1,argset[9])
		}
		if (!stricmp(arg1,"direct_sv") || !stricmp(arg1,"exact_sv") )
		{
			if (!*arg2 || *arg2 == '?') BADSCRIPT("CALL-39 Must name subject argument to query")
			if (!*argset[3] || *argset[3] == '?') BADSCRIPT("CALL-40 Must name verb argument to query")
			if (*argset[4] && *argset[4] != '?') BADSCRIPT("CALL-41 Cannot name object argument to query %s - %s",arg1,argset[4])
			if (*argset[8] && *argset[8] != '?') BADSCRIPT("CALL-42 Cannot name propgation argument to query %s - %s",arg1,argset[8])
			if (*argset[9] && *argset[9] != '?') BADSCRIPT("CALL-43 Cannot name match argument to query %s - %s",arg1,argset[9])
		}
		if (!stricmp(arg1,"direct_sv_member"))
		{
			if (!*arg2 || *arg2 == '?') BADSCRIPT("CALL-44 Must name subject argument to query")
			if (!*argset[3] || *argset[3] == '?') BADSCRIPT("CALL-45 Must name verb argument to query")
			if (*argset[4] && *argset[4] != '?') BADSCRIPT("CALL-46 Cannot name object argument to query %s - %s",arg1,argset[4])
			if (*argset[8] && *argset[8] != '?') BADSCRIPT("CALL-47 Cannot name propgation argument to query %s - %s",arg1,argset[8])
			if (*argset[9] && *argset[9] == '?') BADSCRIPT("CALL-48 Must name match argument to query %s - %s",arg1,argset[9])
		}
		if (!stricmp(arg1,"direct_vo")|| !stricmp(arg1,"exact_vo"))
		{
			if (*arg2 && *arg2 != '?') BADSCRIPT("CALL-49 Cannot name subject argument to query -%s",arg2)
			if (!*argset[3] || *argset[3] == '?') BADSCRIPT("CALL-50 Must name verb argument to query")
			if (!*argset[4] || *argset[4] == '?') BADSCRIPT("CALL-51 Must name object argument to query")
			if (*argset[8] && *argset[8] != '?') BADSCRIPT("CALL-52 Cannot name propgation argument to query %s - %s",arg1,argset[8])
			if (*argset[9] && *argset[9] != '?') BADSCRIPT("CALL-53 Cannot name match argument to query %s - %s",arg1,argset[9])
		}
		if (!stricmp(arg1,"direct_svo") || !stricmp(arg1,"exact_svo") )
		{
			if (!*arg2 || *arg2 == '?') BADSCRIPT("CALL-54 Must name subject argument to query")
			if (!*argset[3] || *argset[3] == '?') BADSCRIPT("CALL-55 Must name verb argument to query")
			if (!*argset[4] || *argset[4] == '?') BADSCRIPT("CALL-56 Must name object argument to query")
			if (*argset[8] && *argset[8] != '?') BADSCRIPT("CALL-57 Cannot name propgation argument to query %s - %s",arg1,argset[8])
			if (*argset[9] && *argset[9] != '?') BADSCRIPT("CALL-58 Cannot name match argument to query %s - %s",arg1,argset[9])
		}
	}
}

#define ARGSETLIMIT 50

static char* ReadCall(char* name, char* ptr, FILE* in, char* &data,bool call)
{	//   returns with no space after it
	//   ptr is just after the ^name -- user can make a call w/o ^ in name but its been patched. Or this is function argument
	char reuseTarget1[MAX_WORD_SIZE];
	char reuseTarget2[MAX_WORD_SIZE];
	*reuseTarget2 = *reuseTarget1  = 0;	//   in case this turns out to be a ^reuse call, we want to test for its target
	char argset[ARGSETLIMIT][MAX_WORD_SIZE];
	char hold[MAX_BUFFER_SIZE];
	char word[MAX_WORD_SIZE];
	char* arguments = ptr;
	char* mydata = hold;	//   read in all data, then treat callArgumentList as output data for processing
	// locate the function
	WORDP D = FindWord(name,0,LOWERCASE_LOOKUP);
	if (!call || !D || !(D->internalBits & FUNCTION_NAME))  //   not a function, is it a function variable?
	{
		if (!IsDigit(name[1])) BADSCRIPT("CALL-1 Call to function not yet defined %s",name)
		*data++ = *name++;
		*data++ = *name++;
		if (IsDigit(*name)) *data++ = *name++;
		*data = 0;
		return ptr;
	}
	SystemFunctionInfo* info = NULL;
	bool isStream = false;		//   dont check contents of stream, just format it
	if (!(D->internalBits & FUNCTION_BITS))			//   system function  (not pattern macro, outputmacro, dual macro, tablemacro, or plan macro)
	{
		info = &systemFunctionSet[D->x.codeIndex];
		if (info->argumentCount == STREAM_ARG) isStream = true;
	}
	else if (patternContext && !(D->internalBits & IS_PATTERN_MACRO)) BADSCRIPT("CALL-2 Can only call patternmacro or dual macro from pattern area - %s",name)
	else if (!patternContext && !(D->internalBits &  (IS_OUTPUT_MACRO | IS_TABLE_MACRO))) BADSCRIPT("CALL-3 Cannot call pattern or table macro from output area - %s",name)
	
	for (unsigned int i = 0; i <= 9; ++i) *argset[i] = 0; //   default EVERYTHING before we test it later
	if (!stricmp(D->word,"^debug")) 
		DebugCode(NULL); // a place for a script compile breakpoint

	// write call header
	strcpy(data,D->word); 
	data += D->length;
	*data++ = ' ';	
	*data++ = '(';	
	*data++ = ' ';	

	bool oldContext = patternContext;
	patternContext = false;

	//   validate argument counts and stuff locally, then swallow data offically as output data
	int parenLevel = 1;
	int argumentCount = 0;
	ptr = ReadNextSystemToken(in,ptr,word,false); // skip (
	while (ALWAYS) //   read as many tokens as needed to complete the call, storing them locally
	{
		ptr = ReadNextSystemToken(in,ptr,word,false);
		if (!*word) break;
		if (*word == '#' && word[1] == '!') BADSCRIPT("#! sample input seen during a call. Probably missing a closing ) ");
	
		// closing paren stuck onto token like _) - break it off 
		size_t len = strlen(word);
		if (word[len-1] == ')' && len > 1 && (*word != '\\' || len > 2) )
		{
			--ptr;
			if (*ptr != ')') ptr -= 1;
			word[len-1] = 0;
		}
		MakeLowerCopy(lowercaseForm,word);

		//   note that in making calls, [] () and {}  count as a single argument with whatver they have inside
		switch(*word)
		{
		case '(': case '[': case '{':
			++parenLevel;
			break;
		case ')': case ']': case '}':
			--parenLevel;
			if (parenLevel == 1) ++argumentCount;	//   completed a () argument
			break;
		case '"':
			if (word[1] != FUNCTIONSTRING && oldContext) // simple string is in pattern context, flip to underscore form
			{
				// convert string into its pattern form.
				unsigned int n = BurstWord(word,0);
				if (n > 1) strcpy(word,JoinWords(n));
			}
			// DROPPING THRU
		case '\'':  
			// DROPPING THRU
		default:
			if (*word == '~' ) CheckSetOrTopic(word); // set or topic

			if (!stricmp(word,"PLAN") && !stricmp(name,"^end")) endtopicSeen = true;
			if (parenLevel == 1)  
			{
				if (*word == FUNCTIONSTRING && word[1] == '"')  
				{
					word[0] = '"';
					word[1] = FUNCTIONSTRING; // show we know it
					if (word[2] == ':')	
					{
						strcpy(word+3,CompileString(word+1)+2);
					}
				}
				ReadNextSystemToken(in,ptr,nextToken,false,true);

				// argument is a function without its ^ ?
				if (*word != '^' && *nextToken == '(') //   looks like a call, reformat it if it is
				{
					char name[MAX_WORD_SIZE];
					*name = '^';
					MakeLowerCopy(name+1,word);	
					WORDP D = FindWord(name,0,PRIMARY_CASE_ALLOWED);
					if (D && D->internalBits & FUNCTION_NAME) strcpy(word,name); 
				}

				if (*word == '^' && (*nextToken == '(' || IsDigit(word[1])))   //   function call or function var ref 
				{
					WORDP D = FindWord(word,0,LOWERCASE_LOOKUP);
					if (!IsDigit(word[1]) && *nextToken == '(' && (!D || !(D->internalBits & FUNCTION_NAME))) BADSCRIPT("CALL-1 Default call to function not yet defined %s",word)
					if (*nextToken != '(' && !IsDigit(word[1])) BADSCRIPT("CALL-? Unknown function variable %s",word)

					char* arg = mydata;
					ptr = ReadCall(word,ptr,in,mydata,*nextToken == '(');
					*mydata = 0;
					strcpy(argset[++argumentCount],arg);
					*mydata++ = ' ';
					continue;
				}
				if (*word == '^' && *nextToken != '(' && word[1] != '^' && word[1] != '$' && word[1] != '_' && word[1] != '"' && !IsDigit(word[1]))
				 // ^^ indicated a deref of something
					BADSCRIPT("%s is either a function missing arguments or an undefined function variable.",word) //   not function call or function var ref
	
				strcpy(argset[++argumentCount],word);
				if (argumentCount == (ARGSETLIMIT-1)) BADSCRIPT("CALL-? Too many arguments");
			}
			else 
			{
				ReadNextSystemToken(in,ptr,nextToken,false,true);
				if (*word == '^' && *nextToken != '(' && *nextToken != ')' && word[1] != '"' && !IsDigit(word[1])) 
					WARNSCRIPT("Is %s intended as a function call?",word) //   not function call or function var ref
			}
		}
	
		if (oldContext && IsAlphaUTF8(*word) && stricmp(name,"^incontext") && stricmp(name,"^reuse") )  {
			WritePatternWord(word);
			WriteKey(word);
		}

		//   add simple item into data
		strcpy(mydata,word);
		mydata += strlen(mydata);
		if (parenLevel == 0) break;	//   we finished the call (no trailing space)
		*mydata++ = ' ';	
	}
	*--mydata = 0;  //   remove closing paren

	char* arg1 = argset[1];
	char* arg2 = argset[2];

	// validate assignment calls if we can - this will be a first,last,random call
	if (*assignKind && (!stricmp(name,"^first") || !stricmp(name,"^last") || !stricmp(name,"^random") || !stricmp(name,"^nth") ) )
	{
		char kind = arg1[2];
		if (*arg1 == '~') {;} // get nth of a concept
		else if (!kind) BADSCRIPT("CALL-5 Assignment must designate how to use factset (s v or o)- %s  in %s %s ",assignKind,name,arguments)
		else if ((kind == 'a' || kind == '+' || kind == '-') && *assignKind != '_')  
			BADSCRIPT("CALL-6 Can only spread a fact onto a match var - %s",assignKind)
		else if (*assignKind == '%' && (kind == 'f' ||  !kind))  BADSCRIPT("CALL-7 cannot assign fact into system variable") // into system variable
		else if (*assignKind == '@' && kind != 'f') BADSCRIPT("CALL-8 Cannot assign fact field into fact set") // into set, but not a fact
	}
	
	if (!stricmp(D->word,"^reuse") && (IsAlphaUTF8(*arg1) || *arg1 == '~')) 
	{
		MakeUpperCopy(reuseTarget1,arg1); // topic names & labels must be upper case
	}
	else if (!stricmp(D->word,"^enable") && IsAlphaUTF8(*arg1)) 
	{
		if (stricmp(arg1,"topic") && stricmp(arg1,"write") && stricmp(arg1,"rule") && stricmp(arg1,"usedrules") ) BADSCRIPT("CALL-18 Enable 1st arg must be TOPIC or RULE or USEDRULES - %s",arg1)
		if (*arg2 == '@'){;}
		else if (*arg2 != '~' || strchr(arg2,'.')) // not a topic or uses ~topic.rulename notation
		{
			MakeUpperCopy(reuseTarget1,arg2); // topic names & labels must be upper case
		}
	}
	else if (!stricmp(D->word,"^disable") && IsAlphaUTF8(*arg1)) 
	{
		if (stricmp(arg1,"topic") && stricmp(arg1,"rule")  && stricmp(arg1,"write")&& stricmp(arg1,"rejoinder") && stricmp(arg1,"inputrejoinder") && stricmp(arg1,"outputrejoinder")  && stricmp(arg1,"save")  ) BADSCRIPT("CALL-19 Disable 1st arg must be TOPIC or RULE or INPUTREJOINDER or OUTPUTREJOINDER or SAVE - %s",arg1)
		if (*arg2 == '@'){;}
		else if (!stricmp(arg1,"rejoinder")){;}
		else if (*arg2 != '~' || strchr(arg2,'.'))  MakeUpperCopy(reuseTarget1,arg2); // topic names & labels must be upper case 
	}

	ValidateCallArgs(D,arg1,arg2,argset);

	if (parenLevel != 0) BADSCRIPT("CALL-59 Failed to properly close (or [ in call to %s",D->word)

	if (isStream){;}  // no cares
	else if (info) // system function
	{
		if (argumentCount != info->argumentCount && info->argumentCount != VARIABLE_ARG_COUNT) 
			BADSCRIPT("CALL-60 Incorrect argument count to system function %s- given %d instead of required %d",name,argumentCount,info->argumentCount & 255)
	}
	else if ((D->internalBits & FUNCTION_BITS) == IS_PLAN_MACRO) 
	{
		if (argumentCount != (int)D->w.planArgCount)
			BADSCRIPT("CALL-60 Incorrect argument count to plan %s- given %d instead of required %d",name,argumentCount,D->w.planArgCount)
	}
	else // std macro (input, output table)
	{
		if (D->w.fndefinition && argumentCount != MACRO_ARGUMENT_COUNT(D) && !(D->internalBits & VARIABLE_ARGS_TABLE)) 
			BADSCRIPT("CALL-60 Incorrect argument count to macro %s- given %d instead of required %d",name,argumentCount,MACRO_ARGUMENT_COUNT(D))
	}

	// handle crosscheck of labels
	char* dot = strchr(reuseTarget1,'.');
	if (!*reuseTarget1);
	else if (dot) // used dotted notation, split them up
	{
		strcpy(reuseTarget2,dot+1);
		*dot = 0;
	}
	else if (*reuseTarget1 != '~') //  only had name, not topic.name, fill in
	{
		strcpy(reuseTarget2,reuseTarget1);
		if (currentFunctionDefinition) strcpy(reuseTarget1,currentFunctionDefinition->word);
		else strcpy(reuseTarget1,currentTopicName);
	}

	if (*reuseTarget1 && (*reuseTarget1 != '$' && *reuseTarget1 != '^' && *reuseTarget1 != '_' && *reuseTarget2 != '$' && *reuseTarget2 != '_')) //   we cant crosscheck variable choices
	{
		if (*reuseTarget1 != '~')
		{
			memmove(reuseTarget1+1,reuseTarget1,strlen(reuseTarget1)+1);
			*reuseTarget1 = '~';
		}
		strcat(reuseTarget1,".");
		strcat(reuseTarget1,reuseTarget2); // compose the name
		NoteUse(reuseTarget1,currentFunctionDefinition ? currentFunctionDefinition->word : currentTopicName);
	}

	//   now generate stuff as an output stream with its validation
	int oldspell = spellCheck;
	spellCheck = 0;
	ReadOutput(hold,NULL,data,NULL,NULL,D);
	spellCheck = oldspell;

	patternContext = oldContext;
	
	*data++ = ')'; //   outer layer generates trailing space
	
	return ptr;	
}

static void TestSubstitute(char* word,char* message)
{
	WORDP D = FindWord(word);
	if (!D) return;
	WORDP E = GetSubstitute(D);
	if (E)
	{
		if (E->word[0] == '!') return; // ignore conditional
		char* which = "Something";
		if (D->internalBits & DO_SUBSTITUTES) which = "Substitutes.txt";
		if (D->internalBits & DO_CONTRACTIONS) which = "Contractions.txt";
		if (D->internalBits & DO_ESSENTIALS) which = "Essentials.txt";
		if (D->internalBits & DO_INTERJECTIONS) which = "Interjections.txt";
		if (D->internalBits & DO_BRITISH) which = "British.txt";
		if (D->internalBits & DO_SPELLING) which = "Spelling.txt";
		if (D->internalBits & DO_TEXTING) which = "Texting.txt";
		if (D->internalBits & DO_PRIVATE) which = "user private substitution";
		if (E->word[1])	WARNSCRIPT("%s changes %s to %s %s\r\n",which,word,E->word,message)
		else  WARNSCRIPT("%s erases %s %s\r\n",which,word,message)
	}
}

static void SpellCheckScriptWord(char* input,int startSeen,bool checkGrade) 
{
	if (!stricmp(input,"null")) return; // assignment clears

	// remove any trailing punctuation
	char word[MAX_WORD_SIZE];
	strcpy(word,input);
	size_t len = strlen(word);
	while (len > 1 && !IsAlphaUTF8(word[len-1]) && word[len-1] != '.') word[--len] = 0;

	WORDP D = FindWord(word,0,LOWERCASE_LOOKUP);
	WORDP entry = D;
	WORDP canonical = D;
	if (word[1] == 0 || IsUpperCase(*input) || !IsAlphaUTF8(*word)  || strchr(word,'\'') || strchr(word,'.') || strchr(word,'_') || strchr(word,'-') || strchr(word,'~')) {;} // ignore proper names, sets, numbers, composite words, wordnet references, etc
	else if (!D || (!(D->properties & NORMAL_WORD) && !(D->systemFlags & PATTERN_WORD)))
	{
		uint64 sysflags = 0;
		uint64 cansysflags = 0;
		wordStarts[0] = wordStarts[1] = wordStarts[2] = wordStarts[3] = AllocateString("");
		wordCount = 1;
		uint64 flags = GetPosData(2,word,entry,canonical,sysflags,cansysflags,false,true,0);
		// do we know a possible base for it
		//char* canon = FindCanonical(word, 2,true);
		//if (!canon) canon = English_GetSingularNoun(word,true,true);
		//if (!canon) canon = English_GetInfinitive(word,true);
		//if (!canon) canon = English_GetAdjectiveBase(word,false);
		//if (!canon) canon = English_GetAdverbBase(word,false);
		if (!flags)
		{
			WORDP E = FindWord(word,0,SECONDARY_CASE_ALLOWED);
			if (E && E != D && E->word[2]) WARNSCRIPT("Word %s only known in opposite case\r\n",word)   
			else WARNSCRIPT("%s is not a known word. Is it misspelled?\r\n",word)
			canonical = E; // the base word
		}
	}
	// check vocabularly limits?
	if (grade && checkGrade)
	{
		if (canonical && !IsUpperCase(*input) && !(canonical->systemFlags & grade) && !strchr(word,'\'')) // all contractions are legal
			Log(STDUSERLOG,"Grade Limit: %s\r\n",D->word);
	}

	// see if substitition will ruin this word
	if (!(spellCheck & NO_SUBSTITUTE_WARNING) ) 
	{
		if (startSeen != -1) TestSubstitute(word,"anywhere in input");
		char test[MAX_WORD_SIZE];
		sprintf(test,"<%s",word);
		if (startSeen == 0) TestSubstitute(test,"at input start");
		sprintf(test,"%s>",word);
		if (startSeen != -1) TestSubstitute(test,"at input end");
		sprintf(test,"<%s>",word);
		if (startSeen == 0) TestSubstitute(test,"as entire input");
	}
}

static char* GetRuleElipsis(char* rule)
{
	static char value[50];
	strncpy(value,rule,45);
	value[45] = 0;
	return value;
}

static bool PatternRelationToken(char* ptr)
{
	if (*ptr == '!' && (ptr[1] == '=' || ptr[1] == '?')) return true;
	if (*ptr == '>' || *ptr == '<' || *ptr == '?' || *ptr == '&') return true;
	if (*ptr == '=') return true;;
	return false;
}

static bool RelationToken(char* word)
{
	if (*word == '=') return (word[1] == '=' || !word[1]);
	return (*word == '<' ||  *word == '>' ||  *word == '?'  || (*word == '!'  && word[1] == '=') || *word == '&');
}

static char* ReadDescribe(char* ptr, FILE* in,uint64 build)
{
	while (ALWAYS) //   read as many tokens as needed to complete the definition (must be within same file)
	{
		char word[MAX_WORD_SIZE];
		char description[MAX_WORD_SIZE];
		ptr = ReadNextSystemToken(in,ptr,word,false);
		if (!stricmp(word,"describe:")) ptr = ReadNextSystemToken(in,ptr,word,false); // keep going with local  loop
		if (!*word) break;	//   file ran dry
		size_t len = strlen(word);
		if (TopLevelUnit(word)) //   definition ends when another major unit starts
		{
			ptr -= len; //   let someone else see this starter 
			break; 
		}
		if (*word != '$' && *word != '_' && *word != '^' && *word != '~')
				BADSCRIPT("Described entity %s is not legal to describe- must be variable or function or concept/topic",word)
		ptr = ReadNextSystemToken(in,ptr,description,false);
		char file[MAX_WORD_SIZE];
		sprintf(file,"TOPIC/describe%s.txt",baseName);
		FILE* out = FopenUTF8WriteAppend(file);
		fprintf(out," %s %s\r\n",word,description);
		fclose(out);
	}
	return ptr;
}


char* ReadPattern(char* ptr, FILE* in, char* &data,bool macro, bool ifstatement)
{ //   called from topic or patternmacro
#ifdef INFORMATION //   meaning of leading characters
< >	 << >>	sentence start & end boundaries, any 
!			NOT 
nul			end of data from macro definition or argument substitution
* *1 *~ *~2 *-1	 gap (infinite, exactly 1 word, 0-2 words, 0-2 words, 1 word before)
_  _2		memorize next match or refer to 3rd memorized match (0-based)
@			factset references @5subject  and _1 (positional set)  
$			user variable 
^	^1		function call or function argument (user)
()[]{}		nesting of some kind (sequence AND, OR, OPTIONAL)
dquote		string token
?			a question input
~dat  ~		topic/set reference or current topic 
%			system variable 
=xxx		comparison test (= > < )
apostrophe and apostrophe!		non-canonical meaning on next token or exclamation test
\			escape next character as literal (\$ \= \~ \(etc)
#xxx		a constant number symbol, but only allowed on right side of comparison
------default values
-1234567890	number token
12.14		number token
1435		number token
a-z,A-Z,|,_	normal token
,			normal token (internal sentence punctuation) - period will never exist since we strip tail and cant be internal

----- these are things which must all be insured lower case (some can be on left or right side of comparison op)
%			system variable 
~dat 		topic/set reference
a: thru u:	responder codes
if/loop/loopcount	constructs
^call  call	function/macro calls with or without ^
^fnvar		function variables
^$glblvar	global function variables
$			user variable 
@			debug ahd factset references
labels on responders
responder types s: u: t: r: 
name of topic  or concept

#endif
	char word[MAX_WORD_SIZE];
	char nestKind[100];
	int nestIndex = 0;
	patternContext = true;

	//   if macro call, there is no opening ( or closing )
	//   We claim an opening and termination comes from finding a toplevel token
	if (macro) nestKind[nestIndex++] = '(';

	bool unorderedSeen = false; // << >> zone
	bool variableGapSeen = false; // wildcard pending

	// prefix characters
	bool memorizeSeen = false; // memorization pending
	bool quoteSeen = false;	// saw '
	bool notSeen = false;	 // saw !
	size_t len;
	bool startSeen = false; // starting token or not
	char* start = data;
	while (ALWAYS) //   read as many tokens as needed to complete the definition
	{
		ptr = ReadNextSystemToken(in,ptr,word);
		if (!*word) break; //   end of file
		MakeLowerCopy(lowercaseForm,word);
		if (TopLevelUnit(lowercaseForm) || TopLevelRule(lowercaseForm)) // end of pattern
		{
			ptr -= strlen(word);  // safe
			break;
		}
		char c = 0;
		char* comparison = FindComparison(word);
		if (comparison) // comparison, do normal analysis on 1st argument
		{
			c = *comparison;
			*comparison = 0;
		}
		switch(*word) // ordinary tokens, not the composite comparison blob
		{
			// token prefixes
			case '!': //   NOT
				if (quoteSeen) BADSCRIPT("PATTERN-1 Cannot have ' and ! in succession")
				if (memorizeSeen) BADSCRIPT("PATTERN-2 Cannot use _ before _")
				if (notSeen) BADSCRIPT("PATTERN-3 Cannot have two ! in succession")
				if (!word[1]) 
					BADSCRIPT("PATTERN-4 Must attach ! to next token. If you mean exclamation match, use escaped ! \r\n %s",ptr)
				notSeen = true;
				if (comparison) *comparison = c;
				ptr -= strlen(word);  // safe
				if (*ptr == '!') ++ptr;
				continue;
			case '_':	//   memorize OR var reference
				if (quoteSeen && !IsDigit(word[1])) BADSCRIPT("PATTERN-1 Cannot have ' and _ in succession except when quoting a match variable. Need to reverse them")
				if (memorizeSeen) BADSCRIPT("PATTERN-6 Cannot have two _ in succession")
				if (!word[1]) // allow separation which will be implied as needed
				{
					if (!ifstatement) BADSCRIPT("PATTERN-7 Must attach _ to next token. If you mean _ match, use escaped _. \r\n %s",ptr)
				}
				if (IsDigit(word[1])) // match variable
				{
					if (GetWildcardID(word) < 0) BADSCRIPT("PATTERN-8 _%d is max match reference - %s",MAX_WILDCARDS-1,word)
					break;
				}

				memorizeSeen = true;
				quoteSeen = false;
				if (comparison) *comparison = c;

				len = strlen(word) - 1 ;
				ptr -= len;  // the remnant
				strncpy(ptr,word+1, len); // this allows a function parameter (originally ^word but now ^0) to properly reset
				continue;
			case '\'': //   original (non-canonical) token - possessive must be \'s or \'
				if (quoteSeen) BADSCRIPT("PATTERN-10 Cannot have two ' in succession")
				if (!word[1]) BADSCRIPT("PATTERN-11 Must attach ' to next token. If you mean ' match, use \' \r\n %s",ptr)
				quoteSeen = true;
				variableGapSeen = false;
				if (comparison) *comparison = c;
				
				len = strlen(word) - 1 ;
				ptr -= len;  // the remnant
				strncpy(ptr,word+1, len); // this allows a function parameter (originally ^word but now ^0) to properly reset
				continue;
			case '<':	//   sentence start <  or  unordered start <<
				if (quoteSeen) BADSCRIPT("PATTERN-12 Cannot use ' before < or <<")
				if (notSeen) BADSCRIPT("PATTERN-13 Cannot use ! before < or <<")
				if (memorizeSeen) BADSCRIPT("PATTERN-13 Cannot use _ before < or <<")
				if (word[1] == '<')  //   <<  unordered start
				{
					if (memorizeSeen) BADSCRIPT("PATTERN-14 Cannot use _ before << ")
					if (unorderedSeen) BADSCRIPT("PATTERN-15 << already in progress")
					if (variableGapSeen) BADSCRIPT("PATTERN-16 Cannot use * before <<")
					unorderedSeen = true;
				}
				else if (word[1])  BADSCRIPT("PATTERN-17 %s cannot start with <",word)
				variableGapSeen = false;
				break; 
			case '@': 
				if (quoteSeen) BADSCRIPT("PATTERN-18 Quoting @ is meaningless.");
				if (memorizeSeen) BADSCRIPT("PATTERN-19 Cannot use _ before  @")
				if (word[1] == '_') // set match position  @_5
				{
					if (GetWildcardID(word+1) >= MAX_WILDCARDS)  BADSCRIPT("PATTERN-? %s is not a valid positional reference - must be < %d",word,MAX_WILDCARDS) 
					char* end = word+strlen(word) - 2; 
					while (IsDigit(*end)) ++end;
					if (*end)
					{
						if (*end == '+' && (!end[1] || end[1] == 'i')) {;}
						else if (*end == '-' &&  (!end[1] || end[1] == 'i')) {;}
						else  BADSCRIPT("PATTERN-? %s is not a valid positional reference - @_2+ or @_2- would be",word)  
					}
					variableGapSeen = false; // no longer after anything. we are changing direction
				}
				else if (GetSetID(word) < 0)
					BADSCRIPT("PATTERN-20 %s is not a valid factset reference",word)  // factset reference
				else if (!GetSetMod(word)) 
					BADSCRIPT("PATTERN-20 %s is not a valid factset reference",word)  // factset reference
				break;
			case '>':	//   sentence end > or unordered end >>
				if (quoteSeen) BADSCRIPT("PATTERN-21 Cannot use ' before > or >>")
				if (memorizeSeen) BADSCRIPT("PATTERN-13 Cannot use _ before > or >>")
				if (word[1] == '>') //   >>
				{
					if (memorizeSeen) BADSCRIPT("PATTERN-22 Cannot use _ before  >> ")
					if (!unorderedSeen) BADSCRIPT("PATTERN-23 Have no << in progress");
					if (variableGapSeen) BADSCRIPT("PATTERN-24 Cannot use wildcard inside >>")
					unorderedSeen = false;
				}
				variableGapSeen = false;
				break; //   sentence end align
			case '(':	//   sequential pattern unit begin
				if (quoteSeen) BADSCRIPT("PATTERN-25 Quoting ( is meaningless.");
				nestKind[nestIndex++] = '(';
				break;
			case ')':	//   sequential pattern unit end
				if (quoteSeen) BADSCRIPT("PATTERN-26 Quoting ) is meaningless.");
				if (memorizeSeen && !ifstatement) BADSCRIPT("PATTERN-27 Cannot use _ before  )")
				if (variableGapSeen && nestIndex > 1) 
					BADSCRIPT("PATTERN-26 Cannot have wildcard followed by )")
				if (nestKind[--nestIndex] != '(') BADSCRIPT("PATTERN-9 ) is not closing corresponding (")
				break;
			case '[':	//   list of pattern choices begin
				if (quoteSeen) BADSCRIPT("PATTERN-30 Quoting [ is meaningless.");
				nestKind[nestIndex++] = '[';
				break;
			case ']':	//   list of pattern choices end
				if (quoteSeen) BADSCRIPT("PATTERN-31 Quoting ] is meaningless.");
				if (memorizeSeen) BADSCRIPT("PATTERN-32 Cannot use _ before  ]")
				if (variableGapSeen) BADSCRIPT("PATTERN-33 Cannot have wildcard followed by ]")
				if (nestKind[--nestIndex] != '[') BADSCRIPT("PATTERN-34 ] is not closing corresponding [")
				break;
			case '{':	//   list of optional choices begins
				if (variableGapSeen)
				{
					// if we can see end of } and it has a gap after it... thats a problem - two gaps in succession is the equivalent
					char* end = strchr(ptr,'}');
					if (end)
					{
						end = SkipWhitespace(end);
						if (*end == '*') WARNSCRIPT("Wildcard before and after optional will probably not work since wildcards wont know where to end if optional fails. Use some other formulation")
					}
				}
				if (quoteSeen) BADSCRIPT("PATTERN-35 Quoting { is meaningless.");
				if (notSeen)  BADSCRIPT("PATTERN-36 !{ is pointless since { can fail or not anyway")
				if (nestIndex && nestKind[nestIndex-1] == '{') BADSCRIPT("PATTERN-37 {{ is illegal")
				nestKind[nestIndex++] = '{';
				break;
			case '}':	//   list of optional choices ends
				if (quoteSeen) BADSCRIPT("PATTERN-38 Quoting } is meaningless.");
				if (memorizeSeen) BADSCRIPT("PATTERN-39 Cannot use _ before  }")
				if (variableGapSeen) BADSCRIPT("PATTERN-40 Cannot have wildcard followed by }")
				if (nestKind[--nestIndex] != '{') BADSCRIPT("PATTERN-41 } is not closing corresponding {")
				break;
			case '\\': //   literal next character
				if (quoteSeen) BADSCRIPT("PATTERN-42 Quoting an escape is meaningless.");
				if (!word[1]) BADSCRIPT("PATTERN-43 Backslash must be joined to something to escape")
				variableGapSeen = false;
				if (word[1] && IsAlphaUTF8(word[1] )) memmove(word,word+1,strlen(word)); // escaping a real word, just use it
				break;
			case '*': //   gap: * *1 *~2 	(infinite, exactly 1 word, 0-2 words, 0-2 words, 1 word before) and *alpha*x* is form match
				if (quoteSeen) BADSCRIPT("PATTERN-44 Quoting a wildcard");
				if (unorderedSeen) BADSCRIPT("PATTERN-45 Cannot have wildcard %s inside << >>",word)
				if (variableGapSeen) 
					BADSCRIPT("PATTERN-46 Cannot have wildcard followed by %s",word)
				if (IsAlphaUTF8(word[1]) )
					break; // find this word as fragmented spelling like sch*ding* since it will have * as a prefix
				
				// gaps of various flavors
				if (notSeen)  BADSCRIPT("PATTERN-47 cannot have ! before gap - %s",word)
				if (IsDigit(word[1])) //   enumerated gap size
				{
					int n = word[1] - '0';
					if (n == 0) BADSCRIPT("PATTERN-48 *0 is meaningless")	 
					if (word[2]) BADSCRIPT("PATTERN-49 *9 is the largest gap allowed or bad stuff is stuck to your token- %s",word)
				}
				else if (word[1] == '-') // backwards
				{
					int n = word[2] - '0';
					if (n == 0) BADSCRIPT("PATTERN-50 *-1 is the smallest backward wildcard allowed - %s",word)
					if (word[3]) BADSCRIPT("PATTERN-51 *-9 is the largest backward wildcard or bad stuff is stuck to your token- %s",word)
				}
				else if (word[1] == '~') // close-range gap
				{
					variableGapSeen = true;
					int n = word[2] - '0';
					if (!word[2]) BADSCRIPT("PATTERN-52 *~ is not legal, you need a digit after it")
					else if (n == 0) BADSCRIPT("PATTERN-53 *~1 is the smallest close-range gap - %s",word)
					else if (word[3]) BADSCRIPT("PATTERN-54 *~9 is the largest close-range gap or bad stuff is stuck to your token- %s",word)
				}
				else if (word[1]) BADSCRIPT("PATTERN-55 * jammed against some other token- %s",word)
				else variableGapSeen = true; // std * unlimited wildcard
				startSeen = true;
				break;
			case '?': //   question input ?   
				if (quoteSeen) BADSCRIPT("PATTERN-56 Quoting a ? is meaningless.");
				if (memorizeSeen) BADSCRIPT("PATTERN-57 Cannot use _ before ?")
				if (variableGapSeen) BADSCRIPT("PATTERN-58 Cannot have wildcards before ?")
				break;
			case '$':	//   user var
				if (quoteSeen) BADSCRIPT("PATTERN-59 Quoting a $ variable is meaningless - %s",word);
				variableGapSeen = false;
				break;
			case '"': //   string
				{
					// you can quote a string, because you are quoting its members
					variableGapSeen = false;
					strcpy(word,JoinWords(BurstWord(word,CONTRACTIONS)));// change from string to std token
					WritePatternWord(word); 
					WriteKey(word);
					unsigned int n = 0;
					char* ptr = word;
					while ((ptr = strchr(ptr,'_')))
					{
						++n;
						++ptr;
					}
					if (n >= SEQUENCE_LIMIT) BADSCRIPT("PATTERN-? Too many  words in string %s, will never match",word)
				}
				break;
			case '%': //   system data
				// you can quote system variables because %topic returns a topic name which can be quoted to query
				if (memorizeSeen) BADSCRIPT("PATTERN-60 Cannot use _ before system variable - %s",word)
				if (!word[1]); //   simple %
				else if (!FindWord(word)) BADSCRIPT("PATTERN-61 %s is not a system variable",word)
				if (comparison) *comparison = c;
				variableGapSeen = false;
				break;
			case '~':
				variableGapSeen = false;
				if (quoteSeen) BADSCRIPT("PATTERN-61 cannot quote set %s because it can't be determined if set comes from original or canonical form",word)
				startSeen = true;
				WriteKey(word);
				CheckSetOrTopic(word); // set or topic
				break;
			default: //   normal token ( and anon function call)

				//    MERGE user pattern words into one? , e.g. drinking age == drinking_age in dictionary
				//   only in () sequence mode. Dont merge [old age] or {old age} or << old age >>
				if (nestKind[nestIndex-1] == '(' && !unorderedSeen) //   BUG- do we need to see what triples etc wordnet has
				{
					ReadNextSystemToken(in,ptr,nextToken,true,true); 
					WORDP F = FindWord(word);
					WORDP E = FindWord(nextToken);
					if (E && F && E->properties & PART_OF_SPEECH  && F->properties & PART_OF_SPEECH)
					{
						char join[MAX_WORD_SIZE];
						sprintf(join,"%s_%s",word,nextToken);
						E = FindWord(join,0,PRIMARY_CASE_ALLOWED); // must be direct match
						if (E && E->properties & PART_OF_SPEECH) // change to composite
						{
							strcpy(word,join);		//   joined word replaces it
							ptr = ReadNextSystemToken(in,ptr,nextToken,true,false); // swallow the lookahead
							*nextToken = 0;
						}
					}
				}
				variableGapSeen = false;
				startSeen = true;
				break;
		}

		if (comparison) //   is a comparison of some kind
		{
			 if (memorizeSeen && comparison[1]) 
				 BADSCRIPT("PATTERN-57 Cannot use _ before a comparison")
			 if (variableGapSeen) BADSCRIPT("PATTERN-16 Cannot use * before comparison since memorization will be incomplete")
	 		*comparison = c;
			if (c == '!') // move not operator out in front of token
			{
				*data++ = '!';
				*data++ = ' '; // and space it, so if we see "!=shec?~hello" we wont think != is an operator, instead = is a jump infof

				size_t len = strlen(comparison);
				memmove(comparison,comparison+1,len);
			}
			if (quoteSeen && *word == '_' && IsDigit(word[1])) // quoted match variable
			{
				quoteSeen = false;
				memmove(word+1,word,strlen(word)+1);
				++comparison;	 // moved over for the added ' 
				*word = '\'';
			}

			char* rhs = comparison+1;
			if (*rhs == '=' || *rhs == '?') ++rhs;
			if (*rhs == '^' && IsAlphaUTF8(rhs[1])) BADSCRIPT("%s is not a current function variable",rhs);
			if (!*rhs && *word == '$'); // allowed member in sentence
			else if (!*rhs && *word == '_' && IsDigit(word[1])); // allowed member in sentence
			else if (*rhs == '#') // names a constant #define to replace with number value
			{
				uint64 n = FindValueByName(rhs+1);
				if (!n) n = FindSystemValueByName(rhs+1);
				if (!n) n = FindParseValueByName(rhs+1);
				if (!n) n = FindMiscValueByName(rhs+1);
				if (!n) BADSCRIPT("PATTERN-63 No #constant recognized - %s",rhs+1)
#ifdef WIN32
			sprintf(rhs,"%I64d",(long long int) n); 
#else
			sprintf(rhs,"%lld",(long long int) n); 
#endif	
			}
			else if (IsAlphaUTF8DigitNumeric(*rhs)  ) {WriteKey(rhs); WritePatternWord(rhs);	}	//   ordinary token
			else if (*rhs == '~') 
			{
				MakeLowerCase(rhs);
				CheckSetOrTopic(rhs);	
			}
			else if (*rhs == '_' || *rhs == '@');	// match variable or factset variable
			else if (*rhs == '$' || *rhs == '%') MakeLowerCase(rhs);	// user variable or system variable
			else if (*rhs == '^' && (rhs[1] == '_' || rhs[1] == '$' || IsDigit(rhs[1]))) MakeLowerCase(rhs); // indirect match variable or indirect user vaiable or function variable
			else if (!*rhs && *comparison == '?' && !comparison[1]);
			else if (*rhs == '\'' && (rhs[1] == '$' || rhs[1]== '_')); //   unevaled user variable or raw match variable
			else if (!comparison[2] && *word == '$'); // find in sentence
			else if (*rhs == '"' && rhs[strlen(rhs)-1] == '"'){;} // quoted string
			else BADSCRIPT("PATTERN-64 Illegal comparison %s or failed to close prior rule starting at %s",word, GetRuleElipsis(start))
			int len = (comparison - word) + 2; //   include the = and jump code in length

			//   rebuild token
			char tmp[MAX_WORD_SIZE];
			*tmp = '=';		//   comparison header
			if (len > 70) BADSCRIPT("PATTERN-65 Left side of comparison must not exceed 70 characters - %s",word)
			char* x = tmp+1;
			Encode(len,x,true);
			strcpy(tmp+2,word); //   copy left side over
			strcpy(word,tmp);	//   replace original token
		}
		else if (*word == '~') CheckSetOrTopic(word); 

		ReadNextSystemToken(in,ptr,nextToken,true,true);
		
		//   see if we have an implied call (he omitted the ^)
		if (*word != '^' && *nextToken == '(') //   looks like a call, reformat it if it is
		{
			char rename[MAX_WORD_SIZE];
			*rename = '^';
			strcpy(rename+1,word);	//   in case user omitted the ^
			WORDP D = FindWord(rename,0,LOWERCASE_LOOKUP);
			if (D && D->internalBits & FUNCTION_NAME) strcpy(word,D->word); //   a recognized call
		}
		if (*word == '^')   //   function call or function var ref or indirect function variable assign ref like ^$$tmp = null
		{
			if (quoteSeen) BADSCRIPT("PATTERN-? Cannot use quote before ^ function call or variable")
			if (notSeen) 
			{
				*data++ = '!';
				notSeen = false;
			}
			if (memorizeSeen) 
			{
				if (!IsDigit(word[1])) BADSCRIPT("PATTERN-66 Cannot use _ before ^ function call")
				*data++ = '_';
				memorizeSeen = false;
			}
			if (word[1] == '$')
			{
				strcpy(data,word);
				data += strlen(data);
			}
			else 
			{
				ptr = ReadCall(word,ptr,in,data,*nextToken == '(');
				if (PatternRelationToken(ptr)) // immediate relation bound to call?
				{
					ptr = ReadNextSystemToken(in,ptr,word);
					strcpy(data,word);
					data += strlen(data);
				}
			}
			*data++ = ' ';
			continue;
		}
		
		//   put out the next token and space 
		if (notSeen) 
		{
			if (memorizeSeen) BADSCRIPT("PATTERN-67 Cannot have ! and _ together")
			*data++ = '!';
			notSeen = false;
		}
		if (quoteSeen) 
		{
			*data++ = '\'';
			quoteSeen = false;
		}
		if (memorizeSeen) 
		{
			*data++ = '_';
			if (ifstatement) *data++ = ' ';
			memorizeSeen = false;
		}

		if (IsAlphaUTF8(*word) || (*word == '*' &&  IsAlphaUTF8(word[1])) )
		{
			char* p;
			if ((p = strchr(word,'*'))) // wild word fragment?  reformat to have leading * and lower case the test
			{
				char hold[MAX_WORD_SIZE];
				MakeLowerCopy(hold,word);
				*word = '*';
				strcpy(word+1,hold);
			}
			else // ordinary word - break off possessives as needed
			{
				size_t len = strlen(word);
				unsigned int ignore = 0;
				if (len > 1 && word[len-1] == '\'' && word[len-2] != '_') // ending ' possessive plural
				{
					WritePatternWord(word);
					WriteKey(word);
					word[--len] = 0;
					ignore = 1;
				}
				else if (len > 2 && word[len-1] == 's' && word[len-2] == '\'' && word[len-3] != '_') // ending 's possessive singular
				{
					WriteKey(word);
					WritePatternWord(word);
					len -= 2;
					word[len] = 0;
					ignore = 2;
				}
				strcpy(word,JoinWords(BurstWord(word,CONTRACTIONS))); // change to std token
				if (spellCheck) SpellCheckScriptWord(word,startSeen ? 1 : 0,false);
				WriteKey(word);
				WritePatternWord(word); //   memorize it to know its important

				if (ignore)
				{
					strcpy(data,word);
					data += strlen(data);
					*data++ = '_';	
					if (ignore == 1) strcpy(word,"'");
					else strcpy(word,"'s");
				}
			}
		}

		strcpy(data,word);
		data += strlen(data);
		*data++ = ' ';	

		if (nestIndex == 0) break; //   we completed this level
	}
	*data = 0;

	//   leftovers?
	if (macro && nestIndex != 1) BADSCRIPT("PATTERN-68 Failed to balance ( or [ or { properly in macro")
	else if (!macro && nestIndex != 0) 
		BADSCRIPT("PATTERN-69 Failed to balance ( or [ or { properly");

	if (unorderedSeen) BADSCRIPT("PATTERN-70 Failed to close <<")
	patternContext = false;
	return ptr;
}

static char* GatherChunk(char* ptr, FILE* in, char* save, bool body) // get unformated data til closing marker
{
	char* original = save;
	char word[MAX_WORD_SIZE];
	char* start = save;
	unsigned int bracket = 0;
	unsigned int paren = 0;
	unsigned int squiggle = 0;
	char* startparen;
	unsigned int startpline = 0;
	unsigned int startbline = 0;
	char* startbracket = 0;
	int level = (body) ? 0 : 1;
	while (ALWAYS)
	{
		ptr = ReadNextSystemToken(in,ptr,word,false); 
		MakeLowerCopy(lowercaseForm,word);
		if (*word == '[' ) 
		{
			if (!bracket) 
			{
				startbracket = ptr;
				startbline = currentFileLine;
			}
			++bracket; 
		}
		else if (*word == ']')  --bracket;
		else if (*word == '(' ) 
		{
			if (!paren) 
			{
				startparen = ptr;
				startpline = currentFileLine;
			}
			++paren;
		}
		else if (*word == ')') --paren;
		else if (*word == '{' ) 
			++squiggle;
		else if (*word == '}') 
		{
			--squiggle;
			if (!squiggle)
			{
				if (paren)  BADSCRIPT("BODY-3 Fail to close ( on line %d - (%s ",startpline,startparen)
				if (bracket) BADSCRIPT("BODY-2 Fail to close [ on line %d - [%s ",startbline,startbracket)
			}
		}
		if (TopLevelUnit(word) || TopLevelRule(lowercaseForm) || (Rejoinder(lowercaseForm) && (!bracket || !body))) 
		{
			if (level >= 1 && !paren)
			{
				*save = 0;
				start[50] = 0;
				if (!body) BADSCRIPT("CHOICE-2 Fail to close code started with %s ",start)
				else BADSCRIPT("BODY-1 Fail to close code started with %s ",start)
			}
		}
		char c = *word;
		int prior = level;
		level += GetNestingData(c);
		if (body && level == 1 && prior == 0) start = save; 
		if (level == 0) break; //   end of stream of if body

		size_t len = strlen(word);
		if ((len + (save - original) + 3) >= maxBufferSize) BADSCRIPT("BODY-4 Body too big. Limit is %d ",maxBufferSize)
		strcpy(save,word);
		save += len;
		*save++ = ' ';
	}
	*save = 0;
	return ptr;
}

static char* ReadChoice(char* word, char* ptr, FILE* in, char* &data,char* rejoinders)
{	//   returns the stored data, not the ptr, starts with the {
	char* choice = AllocateBuffer();
	*data++ = '[';
	*data++ = ' ';
	ReadNextSystemToken(in,ptr,word,true); // get possible rejoinder label
	if (word[1] == ':' && !word[2]) // is rejoinder label
	{
		if (*word < 'a' || *word >= 'q') BADSCRIPT("CHOICE-1 Bad level label %s in [ ]",word)
		if (rejoinders) rejoinders[(int)(*word - 'a' + 1)] = 2; //   authorized level
		*data++ = *word;
		*data++ = word[1];
		*data++ = ' ';
		ptr = ReadNextSystemToken(in,ptr,word,false);
	}
	ptr = GatherChunk(ptr, in, choice,false); 
	ReadOutput(choice,NULL,data,rejoinders);
	*data++ = ']';
	*data++ = ' ';
	*data = 0;
	FreeBuffer();
	return ptr;
}

static char* ReadIfTest(char* ptr, FILE* in, char* &data)
{
	char word[MAX_WORD_SIZE];
	int paren = 0;
	//   read the (
	ptr = ReadNextSystemToken(in,ptr,word,false); //   the '('
	MakeLowerCopy(lowercaseForm,word);
	if (!*word || TopLevelUnit(word) || TopLevelRule(lowercaseForm) || Rejoinder(lowercaseForm)) BADSCRIPT("IF-1 Incomplete IF statement - %s",word)
	if (*word != '(') BADSCRIPT("IF-2 Missing (for IF test - %s",word)
	++paren;
	*data++ = '(';
	*data++ = ' ';
	//   test is either a function call OR an equality comparison OR an IN relation OR an existence test
	//   the followup will be either (or  < > ==  or  IN  or )
	//   The function call returns a status code, you cant do comparison on it
	//   but both function and existence can be notted- IF (!$var) or IF (!read(xx))
	//   You can have multiple tests, separated by AND and OR.
	pattern: 
	ptr = ReadNextSystemToken(in,ptr,word,false,false); 
	if (*word == '~') CheckSetOrTopic(word); 
	// separate ! from things if not  != and !?
	if (*word == '!' && word[1] && word[1] != '=' && word[1] != '?') 
	{
		while (*--ptr != '!' && *ptr);
		++ptr;
		word[1] = 0;
	}
	char* equal = strchr(word+1,'='); // actually a test joined on?
	if (equal)
	{
		if (equal[1] == '=' && equal[2]) // break it off
		{
			ptr -= strlen(equal);
			memmove(ptr+3,ptr+2,strlen(ptr+2)+1);
			ptr[2] = ' ';
			*equal = 0;
		}
		else if ((*(equal-1) == '!' || *(equal-1) == '>' || *(equal-1) == '<') && equal[1]) // break it off
		{
			ptr -= strlen(equal-1);
			memmove(ptr+3,ptr+2,strlen(ptr+2)+1);
			ptr[2] = ' ';
			*(equal-1) = 0;
		}
	}
	char* question = strchr(word+1,'?');
	if (question && word[1])
	{
		ptr -= strlen(question);
		memmove(ptr+1,ptr,strlen(ptr) + 1);
		*ptr = ' ';
		*question = 0;
	}

	bool notted = false;
	if (*word == '!' && !word[1]) 
	{
		notted = true;
		*data++ = '!';
		*data++ = ' ';
		ptr = ReadNextSystemToken(in,ptr,word,false,false); 
	}
	if (*word == '\'' && !word[1]) 
	{
		*data++ = '\'';
		ptr = ReadNextSystemToken(in,ptr,word,false,false); 
		if (*word != '_') BADSCRIPT("IF-3 Can only quote _matchvar in IF test")
	}
	if (*word == '!') BADSCRIPT("IF-4 Cannot do two ! in a row")
	ReadNextSystemToken(in,ptr,nextToken,false,true); 
	MakeLowerCase(nextToken);
	
	if (*nextToken != '(' && *word == '^' && word[1] != '"' && IsAlphaUTF8(word[1])) BADSCRIPT("%s is not the name of a local function argument",word)
	if (*nextToken == '(')  // function call?
	{
		if (*word != '^') //     a call w/o its ^
		{
			char rename[MAX_WORD_SIZE];
			*rename = '^';
			strcpy(rename+1,word);	//   in case user omitted the ^
			strcpy(word,rename);
		}
		ptr = ReadCall(word,ptr,in,data,true);  //   read call
		ReadNextSystemToken(in,ptr,nextToken,false,true); 
		if (RelationToken(nextToken))
		{
			if (notted) BADSCRIPT("IF-5 cannot do ! in front of comparison %s",nextToken)
			*data++ = ' ';
			ptr =  ReadNextSystemToken(in,ptr,word,false,false); //   swallow operator
			strcpy(data,word);
			data += strlen(word);
			*data++ = ' ';
			ptr =  ReadNextSystemToken(in,ptr,word,false,false); //   swallow value
			strcpy(data,word);
			data += strlen(word);
		}
	}
	else if (*nextToken == '!' && nextToken[1] == '?')
	{
		if (notted) BADSCRIPT("IF-6 cannot do ! in front of query %s",nextToken)
		if (*word == '\'' && word[1] == '_') {;}
		else if (*word != '@' &&*word != '$' && *word != '_' && *word != '^' && *word != '%') 
			BADSCRIPT("IF test query must be with $var, _# or '_#, %sysvar, @1subject or ^fnarg -%s",word)
		strcpy(data,word);
		data += strlen(word);
		*data++ = ' ';
		ptr =  ReadNextSystemToken(in,ptr,word,false,false); //   swallow operator
		strcpy(data,word);
		data += strlen(word);
		*data++ = ' ';
		ptr =  ReadNextSystemToken(in,ptr,word,false,false); //   swallow value
		if (*word == '^' && !IsDigit(word[1]))  BADSCRIPT("IF-7 not allowed 2nd function call in relation - %s",word)
		if (*word == '~') CheckSetOrTopic(word); 
		strcpy(data,word);
		data += strlen(word);
	}
	else if (RelationToken(nextToken))
	{
		if (notted && *nextToken != '?') BADSCRIPT("IF-8 cannot do ! in front of comparison %s",nextToken)
		if (*word == '\'' && (word[1] == '$' || word[1] == '_')) {;} // quoted variable
		else if (*word != '@' && *word != '$' && *word != '_' && *word != '^' && *word != '%' && !IsAlphaUTF8(*word)  && !IsDigit(*word) && *word != '+' && *word != '-') 
			BADSCRIPT("IF test comparison 1st value must be number, word, $var, _#, sysvar, @1subject or ^fnarg -%s",word)
		strcpy(data,word);
		data += strlen(word);
		*data++ = ' ';
		ptr =  ReadNextSystemToken(in,ptr,word,false,false); //   swallow operator
		strcpy(data,word);
		data += strlen(word);
		*data++ = ' ';
		ptr =  ReadNextSystemToken(in,ptr,word,false,false); //   swallow value
		if (*word == '~') CheckSetOrTopic(word);
		if (*word == '^' && !IsDigit(word[1])) BADSCRIPT("IF-9 not allowed function call in relation as 2nd arg - %s",word)
		strcpy(data,word);
		data += strlen(word);
	}
	else if (*nextToken == ')' || !stricmp(nextToken,"and") || !stricmp(nextToken,"or")) //   existence test
	{
		if (*word != '$' && *word != '_' && *word != '@' && *word != '^'  && *word != '%' && *word != '?' ) 
			BADSCRIPT("IF-10 existence test - %s. Must be uservar or systemvar or _#  or ? or @# or ~concept or ^^var ",word)
		strcpy(data,word);
		data += strlen(word);
	}
	else BADSCRIPT("IF-11 illegal test %s %s . Use (X > Y) or (Foo()) or (X IN Y) or ($var) or (_3)",word,nextToken) 
	*data++ = ' ';
	
	//   check for close or more conditions
	ptr =  ReadNextSystemToken(in,ptr,word,false,false); //   )
	if (*word == '~') CheckSetOrTopic(word); 
	if (*word == ')')
	{
		*data++ = ')';
		*data++ = ' ';
	}
	else if (!stricmp(word,"or") || !stricmp(word,"and"))
	{
		MakeLowerCopy(data,word);
		data += strlen(word);
		*data++ = ' ';
		goto pattern;	//   handle next element
	}
	else BADSCRIPT("IF-12 comparison must close with ) -%s .. Did you make a function call as 1st argument? that's illegal",word)
	*data = 0;
	return ptr;
}


static char* ReadBody(char* word, char* ptr, FILE* in, char* &data,char* rejoinders)
{	//    stored data starts with the {
	char* body = AllocateBuffer();
	*data++ = '{';
	*data++ = ' ';
	bool oldContext = patternContext;
	patternContext = false;
	ptr = GatherChunk(ptr, in, body,true); 
	ReadOutput(body+2,NULL,data,rejoinders); 
	patternContext = oldContext;
	*data++ = '}'; //   body has no blank after it, done by higher level
	FreeBuffer();
	return ptr;
}

#ifdef INFORMATION

An IF consists of:
	if (test-condition code) xx
	{body code} yy
	else (test-condition code) xx
	{body code} yy
	else (1) xx
	{body code} yy
	
spot yy is offset to end of entire if and xx if offset to next branch of if before "else".

#endif

static char* ReadIf(char* word, char* ptr, FILE* in, char* &data,char* rejoinders)
{
	char* bodyends[1000];				//   places to patch for jumps
	unsigned int bodyendIndex = 0;
	char* original = data;
	strcpy(data,"^^if ");
	data += 5;
	int paren = 0;
	patternContext = false;
	while (ALWAYS)
	{
		// stack up the test info to handle either as pattern or as if
		char patternInfo[4000];
		char token[MAX_WORD_SIZE];
		char* at = patternInfo;
		int level = 0;
		char* endptr = ptr;
		while (1)
		{
			endptr = ReadNextSystemToken(in,endptr,token,false);
			strcpy(at,token);
			at += strlen(at);
			*at++ = ' ';
			if (*token == '(') ++level;
			else if (*token == ')')
			{
				--level;
				if (level == 0) break;
			}
		}
		*at = 0;
		ptr = patternInfo;
		FlipPrivateBuffer(true); 
		char* testbase = data;
		*data++ = 'a'; //   reserve space for offset past pattern
		*data++ = 'a'; // next will be (
		*data++ = ' ';

		if (!strnicmp(patternInfo,"( pattern ",10))
		{
			patternContext = true;
			ptr = ReadPattern(ptr,in,data,false,true); //   read ( for real in the paren for pattern
			patternContext = false;
		}
		else 
			ptr = ReadIfTest(ptr, in, data); // starts by reading the ( and ends having read )
		Encode((unsigned int)(data-testbase),testbase);	// offset to after pattern
	
		// now done reading test, go onto body.
		ptr = endptr; // resume from normal reading of if test
		FlipPrivateBuffer(false); 

		char* ifbase = data;
		*data++ = 'a'; //   reserve space for offset after the closing ), which is how far to go past body
		*data++ = 'a';
		*data++ = ' ';

		//   swallow body of IF after test --  must have { surrounding now
		ReadNextSystemToken(in,ptr,word,false,true); //   {
		if (*word != '{') 
		{
			*data = 0;
			BADSCRIPT("IF-13 body must start with { instead of %s  -- saw pattern %s",word,readBuffer,original)
		}
		ptr = ReadBody(word,ptr,in,data,rejoinders);
		*data++ = ' ';
		bodyends[bodyendIndex++] = data; //   jump offset to end of if (backpatched)
		DummyEncode(data); //   reserve space for offset after the closing ), which is how far to go past body
		*data++ = ' ';
		Encode((unsigned int)(data-ifbase),ifbase);	// offset to ELSE or ELSE IF from body start 
		
		//   now see if ELSE branch exists
		ReadNextSystemToken(in,ptr,word,false,true); //   else?
		if (stricmp(word,"else"))  break; //   caller will add space after our jump index

		//   there is either else if or else
		ptr = ReadNextSystemToken(in,ptr,word,false,false); //   swallow the else
		strcpy(data,"else ");
		data += 5;
		ReadNextSystemToken(in,ptr,word,false,true); //   see if or {
		if (*word == '{') //   swallow the ELSE body now since no IF - add fake successful test
		{
			//   successful test condition for else
			*data++ = '(';
			*data++ = ' ';
			*data++ = '1';
			*data++ = ' ';
			*data++ = ')';
			*data++ = ' ';

			ifbase = data; 
			DummyEncode(data);//   reserve skip data
			*data++ = ' ';
			ptr = ReadBody(word,ptr,in,data,rejoinders);
			*data++ = ' ';
			bodyends[bodyendIndex++] = data; //   jump offset to end of if (backpatched)
			DummyEncode(data);//   reserve space for offset after the closing ), which is how far to go past body
			Encode((unsigned int)(data-ifbase),ifbase);	// offset to ELSE or ELSE IF from body start (accelerator)
			break;
		}
		ptr = ReadNextSystemToken(in,ptr,word,false,false); //   eat the IF
	}
	if (*(data-1) == ' ') --data;	//   remove excess blank
	patternContext = false;

	//   store offsets from successful bodies to the end
	while (bodyendIndex != 0)
	{
		char* at = bodyends[--bodyendIndex];
		Encode((unsigned int)(data-at+1),at); // accerators on completion of if to end of whole if
	}

	*data = 0;
	return ptr; //   we return with no extra space after us, caller adds it
}

static char* ReadLoop(char* word, char* ptr, FILE* in, char* &data,char* rejoinders)
{
	strcpy(data,"^^loop ");
	data += 7;
	ptr = ReadNextSystemToken(in,ptr,word,false,false); //   (
	*data++ = '(';
	*data++ = ' ';
	if (*word != '(') BADSCRIPT("LOOP-1 count must be ()  or (count) -%s",word)
	ptr = ReadNextSystemToken(in,ptr,word,false,false); //   counter - 
	if (*word == '^'  && IsAlphaUTF8(word[1])) BADSCRIPT("%s is not the name of a local function argument",word)
	if (*word == ')') strcpy(data,"-1"); //   omitted, use -1
	else if (!IsDigit(*word) && *word != '$' && *word != '_' && *word != '%'  && *word != '^'  && *word != '@') 
		BADSCRIPT("LOOP-2 counter must be $var, _#, %var, @factset or ^fnarg  -%s",word)
	else 
	{
		strcpy(data,word);
		ptr = ReadNextSystemToken(in,ptr,word,false,false);
	}
	data += strlen(data);
	*data++ = ' ';
	if (*word != ')') BADSCRIPT("LOOP-3 counter must end with )  -%s",word)
	*data++ = ')';
	*data++ = ' ';
	char* loopstart = data;
	DummyEncode(data);  // reserve loop jump to end accelerator
	*data++ = ' ';

	//   now do body
	ReadNextSystemToken(in,ptr,word,false,true); 
	if (*word != '{') BADSCRIPT("LOOP-4 body must start with { -%s",word)
	ptr = ReadBody(word,ptr,in,data,rejoinders);
	Encode((unsigned int)(data - loopstart + 1),loopstart);	// offset to body end from body start (accelerator)
	*data = 0;
	return ptr; // caller adds extra space after
}

char* ReadOutput(char* ptr, FILE* in,char* &data,char* rejoinders,char* supplement,WORDP call)
{
	char* original = data;
	*data = 0;
	char word[MAX_WORD_SIZE];
	char assignlhs[MAX_WORD_SIZE];
	*assignlhs = 0;
	*assignKind = 0;
	int paren = 0;
	int insert = 0;
	bool oldContext = patternContext;
	patternContext = false;
	char hold[MAX_WORD_SIZE];
	*hold = 0;
	while (ALWAYS) //   read as many tokens as needed to complete the responder definition
	{
		if ((data-original) >= MAX_JUMP_OFFSET) BADSCRIPT("OUTPUT-1 code exceeds size limit of %d bytes",MAX_JUMP_OFFSET)

		if (*hold) // pending assignment code
		{
			if (*hold == '=')
			{
				strcpy(word,"=");
				memmove(hold,hold+1,strlen(hold));
			}
			else
			{
				strcpy(word,hold);
				*hold = 0;
			}
		}
		else if (supplement && *supplement)
		{
			strcpy(word,supplement);
			supplement = NULL;
		}
		else ptr = ReadNextSystemToken(in,ptr,word,false); 
		if (!*word)  break; //   end of file
		if (*word == '$') // jammed together asignment?
		{
			char* assign = strchr(word,'=');
			if (assign)
			{
				strcpy(hold,assign);
				*assign = 0;
			}
		}
		if (insert) --insert;
		MakeLowerCopy(lowercaseForm,word);
		if (*word == '#' && word[1] == '!')  //   special comment
		{
			ptr -= strlen(word); //   let someone else see this  also  // safe
			break; 
		}
		if (*word == 'a' && word[2] == 0 && (word[1] == ';' || word[1] == '"' || word[1] == '\'' ) ) 
			WARNSCRIPT("Is %s supposed to be a rejoinder marker?\r\n",word,currentFilename);

		if (TopLevelUnit(word) || TopLevelRule(lowercaseForm) || Rejoinder(lowercaseForm) || !stricmp(word,"datum:")) //   responder definition ends when another major unit or top level responder starts
		{
			if (*word != ':') // allow commands here 
			{
				ptr -= strlen(word); //   let someone else see this starter also  // safe
				break; 
			}
		}

		ReadNextSystemToken(in,ptr,nextToken,false,true); //   caching request
		switch(*word)
		{
			case '(':  case '{':
				++paren;
				break;
			case '[':
				ptr = ReadChoice(word,ptr,in,data,rejoinders);
				continue;
			case ')': case ']': case '}':
				--paren;
				if (paren < 0) 
					BADSCRIPT("OUTPUT-3 Unbalanced %s",word)
				break;
			case '\'': 
				strcpy(data,word);
				data += strlen(data);
				if (*word == '\'' && word[1] == 's' && !word[2] && IsAlphaUTF8OrDigit(*nextToken) ) *data++ = ' ';
 				else if (word[1] == 0 && (*ptr == '_' || IsAlphaUTF8(*ptr)  ))  {;} // if  isolated like join(' _1) then  add space
				else *data++ = ' ';  
				continue;
			case '@': //   factset ref
				if (!IsDigit(word[1])) 
					BADSCRIPT("OUTPUT-4 bad factset reference - %s",word)
				if (!stricmp(nextToken,"+=") || !stricmp(nextToken,"-=") ) insert = 2;
				break;
		}
		if (*assignlhs) // during continued assignment?
		{
			if (!stricmp(word,"^") || !stricmp(word,"|") || !stricmp(word,"&") || (!stricmp(word,"+") || !stricmp(word,"-") || !stricmp(word,"*") || !stricmp(word,"/")))
			{
				if (!stricmp(nextToken,assignlhs)) 
				{
					WARNSCRIPT("Possibly faulty assignment. %s has changed value during prior assignment.",assignlhs)
					*assignlhs = 0;
				}
			}
			else if (!stricmp(nextToken,"^") || !stricmp(nextToken,"|") || !stricmp(nextToken,"&") || !stricmp(nextToken,"+") || !stricmp(nextToken,"-") || !stricmp(nextToken,"*") || !stricmp(nextToken,"/"))  {}
			else *assignlhs = 0;
		}
	
		char* nakedNext = nextToken;
		if (*nakedNext == '^') ++nakedNext;	// word w/o ^ 
		char* nakedWord = word;
		if (*nakedWord == '^') ++nakedWord;	// word w/o ^ 
		
		if (*word == '^' && *nextToken != '(' && word[1] != '^' && word[1] != '$' && word[1] != '_' && word[1] != '"' && !IsDigit(word[1])) BADSCRIPT("%s either references a function w/o arguments or names a function variable that doesn't exist",word)
	
		// note left hand of assignment
		if (!stricmp(nextToken,"|^=") || !stricmp(nextToken,"&=") || !stricmp(nextToken,"|=") || !stricmp(nextToken,"^=") || !stricmp(nextToken,"=") || !stricmp(nextToken,"+=") || !stricmp(nextToken,"-=") || !stricmp(nextToken,"/=") || !stricmp(nextToken,"*="))  strcpy(assignlhs,word);

		if (*nextToken == '=' && !nextToken[1]) // simple assignment
		{
			*assignKind = 0;
			strcpy(data,word);	//   add simple item into data
			data += strlen(data);
			*data++ = ' ';
			ptr = ReadNextSystemToken(in,ptr,nextToken,false,false); //   use up lookahead of =
			strcpy(data,"=");	
			++data;
			*data++ = ' ';
			ReadNextSystemToken(in,ptr,nextToken,false,true); //   aim lookahead at followup
			if (!stricmp(nextToken,"^respond") || !stricmp(nextToken,"^gambit") ||  !stricmp(nextToken,"^reuse") ||  !stricmp(nextToken,"^refine"))
					BADSCRIPT("%s always returns null, so assignment is pointless",nextToken)
			if (!stricmp(nakedNext,"first") || !stricmp(nakedNext,"last") || !stricmp(nakedNext,"random") || !stricmp(nakedNext,"nth") ) 
				strcpy(assignKind,word); // verify usage fact retrieved from set
			if (*nextToken == '=' || *nextToken == '<' || *nextToken == '>')
			{
				if (!IsAlphaUTF8(nextToken[1])) WARNSCRIPT("Possibly assignment followed by another binary operator")
			}
			continue;
		}
		else if (*nextToken == '{' && !stricmp(nakedWord,"loop"))  // loop missing () 
		{
			ptr = ReadLoop(word,ptr,in,data,rejoinders);
			*data++ = ' ';
			continue;
		}
		else if (*nextToken != '(')
		{
		}
		else if (!stricmp(nakedWord,"if"))  // strip IF of ^
		{
			ptr = ReadIf(word,ptr,in,data,rejoinders);
			*data++ = ' ';
			continue;
		}
		else if (!stricmp(nakedWord,"loop"))  // strip LOOP of ^
		{
			ptr = ReadLoop(word,ptr,in,data,rejoinders);
			*data++ = ' ';
			continue;
		}
		else if (*word != '^') //   looks like a call ... if its ALSO a normal word, presume it is not a call, like: I like (American) football
		{
			// be wary.. respond(foo) might have been text...  
			// How does he TELL us its text? interpret normal word SPACE ( as not a function call?
			char rename[MAX_WORD_SIZE];
			*rename = '^';
			strcpy(rename+1,word);	//   in case user omitted the ^
			MakeLowerCase(rename);
			WORDP D = FindWord(rename,0,PRIMARY_CASE_ALLOWED);
			if (D && D->internalBits & FUNCTION_NAME) // it is a function
			{
				// is it also english. If builtin function, do that for sure
				// if user function AND english, more problematic.  maybe he forgot
				WORDP E = FindWord(word);
				if (!E || !(E->properties & PART_OF_SPEECH) || D->x.codeIndex) strcpy(word,rename); //   a recognized call
				else if (*ptr == '(') strcpy(word,rename); // use his spacing to decide
			}
		}
		// a function call, 
		if (*word == '^' && !IsDigit(word[1]) && word[1] != '^'&& word[1] != '=' && word[1] != '"' && word[1] != '\'' && word[1] != '$' && word[1] != '_' && word[1] && *nextToken == '(' )
		{
			WORDP D = FindWord(word,0,LOWERCASE_LOOKUP);
			if ((!D || !(D->internalBits & FUNCTION_NAME))) BADSCRIPT("OUTPUT-5 Apparent call to %s is not yet defined",word)
			ptr = ReadCall(word,ptr,in,data,*nextToken == '('); //   add function call 
			*assignKind = 0;
		}
		else if (*word == '^' && IsDigit(word[1]) ) // fn var
		{
			strcpy(data,word);	//   add simple item into data
			data += strlen(data);
		}		
		else 
		{
			if (*word == '~' ) CheckSetOrTopic(word);
			if (IsAlphaUTF8(*word) && spellCheck == OUTPUT_SPELL) SpellCheckScriptWord(word,-1,true);
			strcpy(data,word);	//   add simple item into data
			data += strlen(data);
		}
		*data++ = ' ';
	}
	while (*(data-1) == ' ') *--data = 0;
	*data++ = ' ';
	*data = 0;

	//   now verify no choice block exceeds CHOICE_LIMIT and that each [ is closed with ]
	while (*original)
	{
		original = ReadCompiledWord(original,word);
		if (*original != '[') continue;

		unsigned int count = 0;
		char* at = original;
		while (*at == '[')
		{
			//   find the closing ]
			while (ALWAYS) 
			{
				at = strchr(at+1,']'); //   find closing ] - we MUST find it (check in initsql)
				if (!at) BADSCRIPT("OUTPUT-5 Failure to close [ choice")
				if (*(at-2) != '\\') break; //   found if not a literal \[
			}
            ++count;
			at += 2;	//   at next token
		}
		if (count >= (CHOICE_LIMIT - 1)) BADSCRIPT("OUTPUT-6 Max %d choices in a row",CHOICE_LIMIT)
		original = at;
	}
	patternContext = oldContext;
	return ptr;
}

static char* ReadTopLevelRule(char* typeval,char* ptr, FILE* in,char* data,char* basedata)
{//   handles 1 responder/gambit + all rejoinders attached to it
	char type[10];
	strcpy(type,typeval);
	char kind[MAX_WORD_SIZE];
	strcpy(kind,type);
	char word[MAX_WORD_SIZE];
	char rejoinders[256];	//   legal levels a: thru q:
	memset(rejoinders,0,sizeof(rejoinders));
	WriteVerify();	// dump any accumulated verification data before the rule
	//   rejoinders == 1 is normal, 2 means authorized in []  3 means authorized and used
	*rejoinders = 1;	//   we know we have a responder. we will see about rejoinders later
	while (ALWAYS) //   read responser + all rejoinders
	{
		MakeLowerCase(kind);
		char* original = data;
		int level = 0;
		//   validate rejoinder is acceptable
		if (Rejoinder(kind))
		{
			int count = level = *kind - 'a' + 1;	//   1 ...
			if (rejoinders[level] >= 2) rejoinders[level] = 3; //   authorized by [b:] and now used
			else if (!rejoinders[level-1]) BADSCRIPT("RULE-1 Illegal rejoinder level %s",kind)
			else rejoinders[level] = 1; //   we are now at this level, enables next level
			//   levels not authorized by [b:][g:] etc are disabled
			while (++count < 20)
			{
				if (rejoinders[count] == 1) rejoinders[count] = 0;
			}
			
			currentRuleID += ONE_REJOINDER;
			WriteVerify();
		}
		strcpy(data,kind); 
		data += 2;
		*data++ = ' ';	
		bool patternDone = false;

#ifdef INFORMATION

A responder of any kind consists of a prefix of `xx  spot xx is an encoded jump offset to go the the
end of the responder. Then it has the kind item (t:   s:  etc). Then a space.
Then one of 3 kinds of character:
	a. a (- indicates start of a pattern
	b. a space - indicates no pattern exists
	c. a 1-byte letter jump code - indicates immediately followed by a label and the jump code takes you to the (

#endif
		char label[MAX_WORD_SIZE];
		*label = 0;
		while (ALWAYS) //   read as many tokens as needed to complete the responder definition
		{
			ptr = ReadNextSystemToken(in,ptr,word,false); 
			if (!*word)  break;
			MakeLowerCopy(lowercaseForm,word);

			size_t len = strlen(word);
			if (TopLevelUnit(word) || TopLevelRule(lowercaseForm) || !stricmp(word,"datum:")) 
			{
				*word = 0;
				break;//   responder definition ends when another major unit or top level responder starts
			}

			if (*word == '(') //   found pattern, no label
			{
				ptr = ReadPattern(ptr-1,in,data,false,false); //   back up and pass in the paren for pattern
				patternDone = true;
				*word = 0;
				break;
			}
			else //   label or start of output
			{
				ReadNextSystemToken(in,ptr,nextToken,false,true);	//   peek what comes after

				if (*nextToken == '(' && (IsAlphaUTF8(*word)  ||IsDigit(*word))) //  label exists
				{
					char name[MAX_WORD_SIZE];
					*name = '^';
					strcpy(name+1,word);
					WORDP D = FindWord(name,0,LOWERCASE_LOOKUP);
					if (D && D->internalBits & FUNCTION_NAME) WARNSCRIPT("label: %s is a potential macro in %s. Add ^ if you want it treated as such.\r\n",word,currentFilename)
					else if (!stricmp(word,"if") || !stricmp(word,"loop")) WARNSCRIPT("label: %s is a potential flow control (if/loop) in %s. Add ^ if you want it treated as a control word.\r\n",word,currentFilename)
					//  potential ^reuse label
					strcpy(label,currentTopicName); 
					strcat(label,".");
					strcat(label,word); 
					MakeUpperCase(label); // full label to test if exists.
					WORDP E = StoreWord(label,0);
					AddInternalFlag(E,LABEL);
					if (strchr(word,'.')) BADSCRIPT("RULE-2 Label %s must not contain a period",word)
					if (len > 40) BADSCRIPT("RULE-2 Label %s must be less than 40 characters",word)
					*data++ = (char)('0' + len + 2); //   prefix attached to label
					strcpy(data,word);
					data += len;
					*data++ = ' ';
					ReadNextSystemToken(NULL,NULL,NULL); // drop lookahead token
					ptr = ReadPattern(ptr,in,data,false,false); //   read ( for real in the paren for pattern
					patternDone = true;
					*word = 0;
				}
				else //   we were seeing start of output (no label and no pattern) for gambit, proceed to output
				{
					if (*type != GAMBIT && *type != RANDOM_GAMBIT) BADSCRIPT("RULE-3 Missing pattern for responder")
					*data++ = ' ';
					patternDone = true;
					// leave word intact to pass to readoutput
				}
				break;
			}
		} //   END OF WHILE
		if (patternDone) 
		{
			ptr = ReadOutput(ptr,in,data,rejoinders,word);
	
			//   data points AFTER last char added. Back up to last char, if blank, leave it to be removed. else restore it.
			while (*--data == ' '); 
			*++data = ' ';
			strcpy(data+1,ENDUNITTEXT); //   close out last topic item+
			data += strlen(data);

			while (ALWAYS) // read all verification comments for next rule if any, getting the next real word token
			{
				ptr = ReadNextSystemToken(in,ptr,word,false); 
				if (*word != '#' || word[1] != '!') break;
				ptr = AddVerify(word,ptr);
			}

			MakeLowerCopy(lowercaseForm,word);
			if (!*word || TopLevelUnit(word) || TopLevelRule(lowercaseForm) || !stricmp(word,"datum:"))  
			{
				ptr -= strlen(word);  // safe
				if (trace & TRACE_SCRIPT) 
				{
					char c = original[40];
					original[40] = 0;
					while (level-- > 0) 
						Log(STDUSERLOG,"  ");
					Log(STDUSERLOG,"rule: %s\r\n",original);
					original[40] = c;
				}
				break;//   responder definition ends when another major unit or top level responder starts
			}

			//  word is a rejoinder type
			strcpy(kind,lowercaseForm);
		}
		else ReportBug("unexpected word in ReadTopLevelRule - %s",word)
		if (trace & TRACE_SCRIPT) 
		{
			char c = original[40];
			original[40] = 0;
			while (level-- > 0) 
				Log(STDUSERLOG,"  ");
			Log(STDUSERLOG,"rule: %s\r\n",original);
			original[40] = c;
		}
	}

	//   did he forget to fill in any [] jumps
	for (unsigned int i = ('a'-'a'); i <= ('q'-'a'); ++i)
	{
		if (rejoinders[i] == 2) BADSCRIPT("RULE-4 Failed to define rejoinder %c: for responder just ended", i + 'a' - 1)
	}

	*data = 0;
	return ptr;
}

static char* ReadMacro(char* ptr,FILE* in,char* kind,uint64 build)
{
	bool table = !stricmp(kind,"table:"); // create as a transient notwrittentofile 
	uint64 typeFlags = 0;
	if (!stricmp(kind,"tableMacro:") || table) typeFlags = IS_TABLE_MACRO;
	else if (!stricmp(kind,"outputMacro:")) typeFlags = IS_OUTPUT_MACRO;
	else if (!stricmp(kind,"patternMacro:")) typeFlags = IS_PATTERN_MACRO;
	else if (!stricmp(kind,"dualMacro:")) typeFlags = IS_PATTERN_MACRO | IS_OUTPUT_MACRO;
	char macroName[MAX_WORD_SIZE];
	*macroName = 0;
	functionArgumentCount = 0;
	char data[MAX_BUFFER_SIZE];
	*data = 0;
	char* pack = data;
	int parenLevel = 0;
	WORDP D = NULL;
	bool gettingArguments = true;
	patternContext = false;
	while (gettingArguments) //   read as many tokens as needed to get the name and argumentList
	{
		char word[MAX_WORD_SIZE];
		ptr = ReadNextSystemToken(in,ptr,word,false);
		if (!*word) break; //   end of file

		if (!*macroName) //   get the macro name
		{
			if (*word == '^') memmove(word,word+1,strlen(word)); //   remove his ^
			MakeLowerCase(word);
			if (!table && !IsAlphaUTF8(*word) ) BADSCRIPT("MACRO-1 Macro name must start alpha %s",word)
			if (table)
			{
				strcpy(macroName,"tbl:");
				strcpy(macroName+4,word);
				Log(STDUSERLOG,"Reading table %s\r\n",macroName);
			}
			else
			{
				if (!IsLegalName(word)) BADSCRIPT("MACRO-2 Illegal characters in function name %s",word)
				*macroName = '^';
				strcpy(macroName+1,word);
				Log(STDUSERLOG,"Reading %s %s\r\n",kind,macroName);
			}
			D = StoreWord(macroName);
			if (D->internalBits & FUNCTION_NAME && !table) BADSCRIPT("MACRO-3 macro %s already defined",macroName)
			continue;
		}
		if (parenLevel == 0 && !stricmp(word,"variable")) // putting "variable" before the args list paren allows you to NAME all args but get ones not supplied filled in with * (tables) or null (macros)
		{
			D->internalBits |= VARIABLE_ARGS_TABLE;
			continue;
		}

		size_t len = strlen(word);
		if (TopLevelUnit(word)) //   definition ends when another major unit starts
		{
			ptr -= len; //   let someone else see this starter also
			break; 
		}
		char* restrict = NULL;
		switch(*word)
		{
			case '(': 
				if (parenLevel++ != 0) BADSCRIPT("MACRO-4 bad paren level in macro definition %s",macroName)
				continue; //   callArgumentList open
			case ')':
				if (--parenLevel != 0) BADSCRIPT("MACRO-5 bad closing paren in macro definition %s",macroName)
				gettingArguments = false;
				break;
			case '^':  //   declaring a new argument
				if (IsDigit(word[1])) BADSCRIPT("MACRO-6 Function arguments must be alpha names, not digits like %s ",word)
				restrict = strchr(word,'.');
				if (restrict)
				{
					if (!stricmp(restrict+1,"KEEP_QUOTES") && (typeFlags == IS_TABLE_MACRO || typeFlags == IS_OUTPUT_MACRO))	D->x.macroFlags |= 1 << functionArgumentCount; // a normal string where spaces are kept instead of _ (format string)
					else if (!stricmp(restrict+1,"HANDLE_QUOTES"))	
					{
						if (typeFlags != IS_OUTPUT_MACRO) BADSCRIPT("MACRO-? HANDLE_QUOTES only valid with OUTPUTMACRO or DUALMACRO - %s ",word)
						D->x.macroFlags |= 1 << functionArgumentCount; // outputmacros
					}
					else if (!stricmp(restrict+1,"COMPILE") && typeFlags == IS_TABLE_MACRO) D->x.macroFlags |= (1 << 16) << functionArgumentCount; // a compile string " " becomes "^:"
					else if (!stricmp(restrict+1,"UNDERSCORE") && typeFlags == IS_TABLE_MACRO) {;} // default for quoted strings is _ 
					else if (typeFlags != IS_TABLE_MACRO && typeFlags != IS_OUTPUT_MACRO) BADSCRIPT("Argument restrictions only available on Table Macros or OutputMacros  - %s ",word)
					else  BADSCRIPT("MACRO-? Table/Tablemacro argument restriction must be KEEP_QUOTES OR COMPILE or UNDERSCORE - %s ",word)
					*restrict = 0;
				}
				else  // default for quoted strings on argumet is UNDERSCORE
				{
				}
				strcpy(functionArguments[functionArgumentCount++],word);
				if (functionArgumentCount > MAX_ARG_LIMIT)  BADSCRIPT("MACRO-7 Too many callArgumentList to %s - max is %d",macroName,MAX_ARG_LIMIT)
				continue;
			default:
				BADSCRIPT("MACRO-7 Bad argument to macro definition %s",macroName)
		}
	}
	if (!D) return ptr; //   nothing defined

	AddInternalFlag(D,(unsigned int)(FUNCTION_NAME|build|typeFlags));
	*pack++ = (unsigned char)(functionArgumentCount + 'A'); // some 30 can be had
	
	currentFunctionDefinition = D;
	ptr = ((typeFlags & FUNCTION_BITS) == IS_PATTERN_MACRO) ? ReadPattern(ptr,in,pack,true,false) : ReadOutput(ptr,in,pack,NULL); 
	*pack = 0;

	//   record that it is a macro, with appropriate validation information
	D->w.fndefinition = (unsigned char*) AllocateString(data);

	if (!table) // tables are not real macros, they are temporary
	{
		char filename[MAX_WORD_SIZE];
		sprintf(filename,"TOPIC/macros%s.txt",baseName);
		//   write out definition -- this is the real save of the data
		FILE* out = FopenUTF8WriteAppend(filename);
		if ((D->internalBits & FUNCTION_BITS) ==  IS_TABLE_MACRO) fprintf(out,"%s T %d %d %s\r\n",macroName,D->x.macroFlags,functionArgumentCount,data);
		else if ((D->internalBits & FUNCTION_BITS) == (IS_OUTPUT_MACRO|IS_PATTERN_MACRO))  fprintf(out,"%s %c %d %d %s\r\n",macroName,'D',D->x.macroFlags,functionArgumentCount,data);
		else fprintf(out,"%s %c %d %d %s\r\n",macroName,((D->internalBits & FUNCTION_BITS) == IS_OUTPUT_MACRO) ? 'O' : 'P',D->x.macroFlags,functionArgumentCount,data);
		fclose(out);
	}
	return ptr;
}

static char* ReadTable(char* ptr, FILE* in,uint64 build,bool fromtopic)
{
	char name[MAX_WORD_SIZE];
	char word[MAX_WORD_SIZE];
	char post[MAX_WORD_SIZE]; 
	char args[MAX_TABLE_ARGS+1][MAX_WORD_SIZE];
	unsigned short quoteProcessing = 0;
	unsigned int indexArg = 0;
	char* pre = NULL;
	ptr = SkipWhitespace(ptr);
	ReadNextSystemToken(in,ptr,name,false,true); 
	if (*name != '^')  // add function marker if it lacks one
	{
		memmove(name+1,name,strlen(name)+1);
		*name = '^';
	}
	currentFunctionDefinition = FindWord(name);
	unsigned int sharedArgs;
	bool tableMacro = false;
	if (!currentFunctionDefinition) // go define a temporary tablemacro function since this is a spontaneous table  Table:
	{
		if (fromtopic) BADSCRIPT("datum: from topic must use predefined table %s",name)
		memmove(word,name+1,strlen(name));
		ptr = ReadMacro(ptr,in,"table:",build); //   defines the name,argumentList, and script
		ptr = ReadNextSystemToken(in,ptr,word,false,false); //   the DATA: separator
		if (stricmp(word,"DATA:")) 	BADSCRIPT("TABLE-1 missing DATA: separator for table - %s",word)
		sharedArgs = 0;
	}
	else // this is an existing table macro being executed
	{
		tableMacro = true;
		ptr = ReadNextSystemToken(in,ptr,word,false,false);  // swallow function name
		ptr = ReadNextSystemToken(in,ptr,word,false,false);  // swallow (
		if (*word != '(') BADSCRIPT("TABLE-2 Must have ( before arguments")
		while (ALWAYS) // read argument values we supply to the existing tablemacro
		{
			ptr = ReadNextSystemToken(in,ptr,args[indexArg],false,false);  
			if (*args[indexArg] == ')') break;
			if (*args[indexArg] == '^') 
				BADSCRIPT("TABLE-3 TableMacro %s requires real args, not redefinition args",currentFunctionDefinition->word)
			if (++indexArg >= MAX_TABLE_ARGS) BADSCRIPT("TABLE-4 too many table args")
		}
		sharedArgs = indexArg;
	}
	quoteProcessing = currentFunctionDefinition->x.macroFlags; // values of KEEP_QUOTES for each argument

	// now we have the function definition and any shared arguments. We need to read the real arguments per table line now and execute.

	char* argumentList = AllocateBuffer();
	++jumpIndex;
	int holdDepth = globalDepth;
	char* xxbase = ptr;  // debug hook
	while (ALWAYS) 
	{
		if (setjmp(scriptJump[jumpIndex])) // flush on error
		{
			ptr = FlushToTopLevel(in,ptr,holdDepth,0);
			break;
		}
		ptr = ReadNextSystemToken(in,ptr,word,false,false); 
		char* original = ptr - strlen(word);
		if (*word == '\\' && word[1] == 'n') continue; // newline means pretend new table entry

		if (*word == ':' && word[1]) // debug command
		{
			ptr = original;  // safe
			char output[MAX_WORD_SIZE];
			DoCommand(ptr,output);
			*ptr = 0;
			continue;
		}
		if (!*word || TopLevelUnit(word) || TopLevelRule(word)) // end
		{
			ptr = original;  // safe
			break;
		}
	
		
		//   process a data set from the line
		char* systemArgumentList = argumentList;
		*systemArgumentList++ = '(';
		*systemArgumentList++ = ' ';
		unsigned int argCount = 0;

		// common arguments processing
		for (unsigned int i = 0; i < sharedArgs; ++i)
		{
			strcpy(systemArgumentList,args[i]);
			systemArgumentList += strlen(systemArgumentList);
			*systemArgumentList++ = ' ';
			++argCount;
		}

		// now fill in args of table data from a single line
		char* choiceArg = NULL; //   the multiple interior
		bool startup = true;
		while (ALWAYS) 
		{
			if (!startup) ptr = ReadSystemToken(ptr,word);	//   next item to associate
			if (!stricmp(word,":debug")) 
			{
				DebugCode(word);
				continue;
			}
			startup = false;
			if (!*word) break;					//   end of LINE of items stuff

			if (!stricmp(word,"...")) break;	// pad to end of arg count

			if (!stricmp(word,"\\n"))			// fake end of line
			{
				memmove(readBuffer,ptr,strlen(ptr)+1);	//   erase earlier stuff we've read
				ptr = readBuffer;
				break; 
			}

			if (*word == '[' ) // choice set (one per line allowed)
			{
				if (choiceArg) BADSCRIPT("TABLE-5 Only allowed 1 multiple choice [] arg")
				pre = systemArgumentList;  //   these are the fixed arguments before the multiple choice one
				choiceArg = ptr; //   multiple choices arg 
				char* at = strchr(ptr,']'); //  find end of multiple choice
				if (!at) BADSCRIPT("TABLE-6 bad [ ] ending %s in table %s",readBuffer,currentFunctionDefinition->word)
				ptr = at + 1; //   continue fixed argumentList AFTER the multiple choices set (but leave blank if there)
				++argCount;
				continue; //   skipping over this arg, move on to next arg now.
			}
			uint64 flag = 0;

			// how do we store string arguments - with underscores, as is, compiled,
			bool keepQuotes = (quoteProcessing & ( 1 << argCount)) ? 1 : 0; // want to use quotes and spaces, instead of none and convert to _ which is the default // a normal string where spaces are kept instead of _ (format string)
			bool xxotherNotation = (quoteProcessing & ( (1 << 16) << argCount)) ? 1 : 0; // unused at present  
			if (*word == FUNCTIONSTRING && word[1] == '"')
			{
				strcpy(word,CompileString(word)); // no underscores in string, compiled as executable // a compile string " " becomes "^:"
				flag = AS_IS;
			}
			else if (*word == '"' && keepQuotes) // no underscores in string, preserve string. Quotes needed to detect as single argument for fact creation
			{
				flag = AS_IS;
			}
			else 
			{
				unsigned int n = BurstWord(word,(*word == '"') ? POSSESSIVES : 0);
				strcpy(word,JoinWords(n)); // by default strings are stored with _, pretending they are composite words.
				if (n > 1)  flag = AS_IS;
			}
			if ( *word == '\\') memmove(word,word+1,strlen(word)); // remove escape
			if (*word == '"' && !word[1]) BADSCRIPT("TABLE-? isolated doublequote argument- start of string not recognized?");
			if (flag != AS_IS && *word != '"' && strstr(word," ")) BADSCRIPT("TABLE-7 unexpected space in string %s - need to use doublequotes around string",word);
			WORDP baseWord = StoreWord(word,flag);
			strcpy(word,baseWord->word); 
	
			strcpy(systemArgumentList,word);
			systemArgumentList += strlen(systemArgumentList);
			*systemArgumentList++ = ' ';
			++argCount;

			//   handle synonyms as needed
			ptr = SkipWhitespace(ptr); //   to align to see if (given 
			MEANING base = MakeMeaning(baseWord);
			if (*ptr == '(' && ++ptr) while (ALWAYS) // synonym listed, create a fact for it
			{
				ptr = ReadSystemToken(ptr,word);
				if (!*word || *word == '[' || *word == ']')  BADSCRIPT("TABLE-8 Synomym in table %s lacks token",currentFunctionDefinition->word)
				if (*word == ')') break;	//   end of synonms
				strcpy(word,JoinWords(BurstWord(word,CONTRACTIONS)));
				if (IsUpperCase(*word)) CreateFact(MakeMeaning(StoreWord(word,NOUN|NOUN_PROPER_SINGULAR)),Mmember,base); 
				else CreateFact(MakeMeaning(StoreWord(word,NOUN|NOUN_SINGULAR)),Mmember,base);
			}
			if ((MACRO_ARGUMENT_COUNT(currentFunctionDefinition) - sharedArgs) == 1)
			{
				memmove(readBuffer,ptr,strlen(ptr)+1);	
				ptr = readBuffer;
				break;
			}
		}

		while ( argCount < MACRO_ARGUMENT_COUNT(currentFunctionDefinition) && (!stricmp(word,"...") || currentFunctionDefinition->internalBits & VARIABLE_ARGS_TABLE))
		{
			strcpy(systemArgumentList,"*");
			systemArgumentList += strlen(systemArgumentList);
			*systemArgumentList++ = ' ';
			++argCount;
		}

		*systemArgumentList = 0;
		if (choiceArg) strcpy(post,pre); // save argumentList after the multiple choices

		//   now we have one map of the argumentList row
		if (argCount && argCount != MACRO_ARGUMENT_COUNT(currentFunctionDefinition)) 
			BADSCRIPT("TABLE-9 Bad table %s in table %s, want %d arguments and have %d",original,currentFunctionDefinition->word,MACRO_ARGUMENT_COUNT(currentFunctionDefinition),argCount)

		//   table line is read, now execute rules on it, perhaps multiple times, after stuffing in the choice if one
		if (argCount) //   we swallowed a dataset. Process it
		{
			while (ALWAYS)
			{
				//   prepare variable argumentList
				if (choiceArg) //   do it with next multi
				{
					choiceArg = ReadSystemToken(choiceArg,word); //   get choice
					if (!*word || *word == ']') break;			//   end of multiple choice

					unsigned int control = 0;
					if (*word == FUNCTIONSTRING && word[1] == '"') strcpy(word,CompileString(word)); // readtable
					else strcpy(word,JoinWords(BurstWord(word,CONTRACTIONS|control)));
					strcpy(word,StoreWord(word,(control) ? AS_IS : 0)->word); 

					if (*word == '\'') //   quoted value
					{
						choiceArg = ReadSystemToken(choiceArg,word); //   get 1st of choice
						if (!*word || *word == ']') break;			//   end of LINE of items stuff
						ForceUnderscores(word);
						strcpy(pre,StoreWord(word)->word); //   record the local w/o any set expansion
					}
					else 
					{
						WORDP D = StoreWord(word);
						strcpy(pre,D->word); //   record the multiple choice
						choiceArg = SkipWhitespace(choiceArg);
						if (*choiceArg == '(' && ++choiceArg) while(choiceArg) //   synonym 
						{
							choiceArg = ReadSystemToken(choiceArg,word);
							if (!*word) BADSCRIPT("TABLE-10 Failure to close synonym list in table %s",currentFunctionDefinition->word)
							if (*word == ')') break;	//   end of synonms
							ForceUnderscores(word);
							CreateFact(MakeMeaning(StoreWord(word)),Mmember,MakeMeaning(D)); 
						}
					}		

					char* at = pre + strlen(pre);
					*at++ = ' ';
					strcpy(at,post); //   add rest of argumentList
					systemArgumentList = at + strlen(post);
				}
				*systemArgumentList++ = ')';	//   end of call setup
				*systemArgumentList = 0;
				
				ChangeDepth(1,"readTable");
				currentRule = NULL;
				FunctionResult result;
				DoFunction(currentFunctionDefinition->word,argumentList,currentOutputBase,result);
				ChangeDepth(-1,"readTable");
				if (!choiceArg) break;
			}
		}
		if (fromtopic) break; // one entry only
	}
	FreeBuffer();

	if (!tableMacro)  // delete dynamic function
	{
		currentFunctionDefinition->internalBits &= -1LL ^ FUNCTION_NAME;
		currentFunctionDefinition->w.fndefinition = NULL;
		AddInternalFlag(currentFunctionDefinition,DELETED_MARK);
	}
	currentFunctionDefinition = NULL; 
	--jumpIndex;
	return ptr;
}

static void SetJumpOffsets(char* data) // store jump offset for each rule
{
    char* at = data;
    char* end = data;
    while (*at && *++at) // find each responder end
    {
        if (*at == ENDUNIT) 
        {
            int diff = (int)(at - end  + 1);
			if (diff > MAX_JUMP_OFFSET) BADSCRIPT("TOPIC-9 Jump offset too far - %d but limit %d near %s",diff,MAX_JUMP_OFFSET,readBuffer) //   limit 2 char (12 bit) 
			Encode(diff,end);
            end = at + 1;
        }
    }
 }

static char* ReadKeyword(char* word,char* ptr,bool &notted, bool &quoted, MEANING concept,uint64 type,bool ignoreSpell,uint64 build,bool duplicate)
{
	// read the keywords zone of the concept
	char* at;
	MEANING M;
	WORDP D;
	size_t len = strlen(word);
	switch(*word) 
	{
		case '!':	// excuded keyword
			if (len == 1) BADSCRIPT("CONCEPT-5 Must attach ! to keyword in %s",Meaning2Word(concept)->word);
			if (notted) BADSCRIPT("CONCEPT-5 Cannot use ! after ! in %s",Meaning2Word(concept)->word);
			notted = true;
			ptr -= len;
			if (*ptr == '!') ++ptr;
			break;
		case '\'': 
			if (len == 1) BADSCRIPT("CONCEPT-6 Must attach ' to keyword in %s",Meaning2Word(concept)->word);
			if (quoted) BADSCRIPT("CONCEPT-5 Cannot use ' after ' in %s",Meaning2Word(concept)->word);
			quoted = true;	//   since we emitted the ', we MUST emit the next token
			ptr -= len;
			if (*ptr == '\'') ++ptr;
			break;
		default:
			if (*word == '$' || *word == '_' || *word == '%') BADSCRIPT("CONCEPT-? Cannot use $var or _var or %var as a keyword in %s",Meaning2Word(concept)->word);
			if (*word == '~') MakeLowerCase(word); //   sets are always lower case
			if ((at = strchr(word+1,'~'))) //   wordnet meaning request, confirm definition exists
			{
				char level[10];
				strcpy(level,at);
				M = ReadMeaning(word);
				if (!M) BADSCRIPT("CONCEPT-7 WordNet word doesn't exist %s",word)
				WORDP D = Meaning2Word(M);
				unsigned int index = Meaning2Index(M);
				if ((GetMeaningCount(D) == 0 && !(GETTYPERESTRICTION(M) & BASIC_POS)) || (index && !strcmp(word,D->word) && index > GetMeaningCount(D)))
				{
					if (index) 
						WARNSCRIPT("WordNet word does not have such meaning %s\r\n",word)
					M &= -1 ^ INDEX_BITS;
				}
			}
			else // ordinary word or concept-- see if it makes sense
			{
				char end = word[strlen(word)-1];
				if (!IsAlphaUTF8OrDigit(end) && end != '"')  
				{
					if (end != '.' || strlen(word) > 6) WARNSCRIPT("last character of keyword %s is punctuation. Is this intended? \r\n",word)
				}
				M = ReadMeaning(word);
				D = Meaning2Word(M);
					
				if (type) AddProperty(D,type); // augment its type

				if (*D->word == '~') // concept
				{
					if (M == concept) 
						BADSCRIPT("CONCEPT-8 Cannot include topic into self - %s",D->word);
					CheckSetOrTopic(D->word);
				}
				else if ( ignoreSpell || !spellCheck || strchr(D->word,'_') || !D->word[1] || IsUpperCase(*D->word)) {;}	// ignore spelling issues, phrases, short words &&  proper names
				else if (!(D->properties & PART_OF_SPEECH && !(D->systemFlags & (PATTERN_WORD))))
				{
					SpellCheckScriptWord(D->word,-1,false);
					WriteKey(D->word);
					WritePatternWord(D->word);
				}
			} // end ordinary word
			unsigned int flags = quoted ? ORIGINAL_ONLY : 0;
			if (duplicate) flags |= FACTDUPLICATE;
			if (build & BUILD1) flags |= FACTBUILD1; // concept facts from build 1
			else if (build & BUILD2) flags |= FACTBUILD2; // concept facts from build 1
			CreateFact(M,(notted) ? Mexclude : Mmember,concept, flags); 
			quoted = false;
			notted = false;
	} 
	return ptr;
}

static char* ReadBot(char* ptr, FILE* in, uint64 build)
{
	*botheader = ' ';
	char word[MAX_WORD_SIZE];
	ptr = ReadCompiledWord(ptr,word);
	MakeLowerCopy(botheader,word);
	char* x;
	while ((x = strchr(botheader,','))) *x = ' ';	// change comma to space. all bot names have spaces on both sides
	Log(STDUSERLOG,"Reading bot restriction: %s\r\n",botheader);
	return ptr;
}

static char* ReadTopic(char* ptr, FILE* in,uint64 build)
{
	patternContext = false;

	char* data = (char*) malloc(MAX_TOPIC_SIZE); // use a big chunk of memory for the data
	*data = 0;
	char* pack = data;

	++topicCount;
	*currentTopicName = 0;
	unsigned int flags = 0;
	bool topicFlagsDone = false;
	bool keywordsDone = false;
	int parenLevel = 0;
	bool quoted = false;
	bool notted = false;
	MEANING topic = 0;
	int holdDepth = globalDepth;
	WORDP topicName = NULL;
	unsigned int gambits = 0;
	unsigned int toplevelrules = 0; // does not include rejoinders
	currentRuleID = 0;	// reset rule notation
	verifyIndex = 0;	
	bool stayRequested = false;
	if (setjmp(scriptJump[++jumpIndex])) 
	{
		ptr = FlushToTopLevel(in,ptr,holdDepth,data); //   if error occurs lower down, flush to here
	}
	while (ALWAYS) //   read as many tokens as needed to complete the definition
	{
		char word[MAX_WORD_SIZE];
		ptr = ReadNextSystemToken(in,ptr,word,false);
		if (!*word) break;

		if (!*currentTopicName) //   get the topic name
		{
			if (*word != '~') BADSCRIPT("Topic name - %s must start with ~",word)
			strcpy(currentTopicName,word);
			Log(STDUSERLOG,"Reading topic %s\r\n",currentTopicName);
			topicName = FindWord(currentTopicName);
			if (topicName && topicName->internalBits & CONCEPT && !(topicName->internalBits & TOPIC) && topicName->internalBits & (BUILD0|BUILD1|BUILD2)) 
				BADSCRIPT("TOPIC-1 Concept already defined with this topic name %s",currentTopicName)
			topicName = StoreWord(currentTopicName);
			if (!IsLegalName(currentTopicName)) BADSCRIPT("TOPIC-2 Illegal characters in topic name %s",currentTopicName)
			topic = MakeMeaning(topicName);

			// handle potential multiple topics of same name
			duplicateCount = 0;
			while (topicName->internalBits & TOPIC)
			{
				++duplicateCount;
				char name[MAX_WORD_SIZE];
				sprintf(name,"%s%c%d",currentTopicName,DUPLICATETOPICSEPARATOR,duplicateCount);
				topicName = StoreWord(name);
				if (!*duplicateTopicName) 
					strcpy(duplicateTopicName,currentTopicName);
			}
			strcpy(currentTopicName,topicName->word);
			AddInternalFlag(topicName,(unsigned int)(build|CONCEPT|TOPIC));
			topicName->w.botNames = NULL;
			continue;
		}

		if (TopLevelUnit(word)) //   definition ends when another major unit starts
		{
			ptr -= strlen(word); //   let someone else see this starter also  // safe
			break; 
		}

		switch(*word)
		{
		case '(': case '[':
			if (!keywordsDone && topicFlagsDone) BADSCRIPT("TOPIC-3 Illegal bracking in topic keywords %s",word)
			if (flags & TOPIC_SHARE && flags & TOPIC_SYSTEM) BADSCRIPT("TOPIC-? Don't need SHARE on SYSTEM topic %s, it is already shared via system",currentTopicName)
			topicFlagsDone = true; //   topic flags must occur before list of keywords
			++parenLevel;
			break;
		case ')': case ']':
			--parenLevel;
			if (parenLevel == 0) keywordsDone = true;
			break;
		case '#':
			if (*word == '#' && word[1] == '!')  ptr = AddVerify(word,ptr);
			continue;
		default:
			MakeLowerCopy(lowercaseForm,word);
			if (!topicFlagsDone) //   do topic flags
			{
				if (!strnicmp(word,"bot=",4)) // bot restriction on the topic
				{
					char botlist[MAX_WORD_SIZE];
					MakeLowerCopy(botlist,word+4);
					char* x;
					while ((x = strchr(botlist,','))) *x = ' ';	// change comma to space. all bot names have spaces on both sides
					topicName->w.botNames = AllocateString(botlist,strlen(botlist)); // bot=harry,georgia,roger
				}
                else if (!stricmp(word,"deprioritize")) flags |= TOPIC_LOWPRIORITY; 
				else if (!stricmp(word,"noblocking")) flags |= TOPIC_NOBLOCKING; 
 				else if (!stricmp(word,"nopatterns") || !stricmp(word,"nopattern")) flags |= TOPIC_NOPATTERNS; 
 				else if (!stricmp(word,"nogambits") || !stricmp(word,"nogambit")) flags |= TOPIC_NOGAMBITS; 
 				else if (!stricmp(word,"nosamples") || !stricmp(word,"nosample")) flags |= TOPIC_NOSAMPLES; 
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
				else if (!stricmp(word,"stay")) 
				{
					flags &= -1 ^TOPIC_NOSTAY;
					stayRequested = true;
				}
				else if (!stricmp(word,"erase")) flags &= -1 ^TOPIC_KEEP;
				else if (!stricmp(word,"system")) 
				{
					flags |= TOPIC_SYSTEM | TOPIC_KEEP | TOPIC_NOSTAY;
					if (stayRequested) BADSCRIPT("TOPIC-4 Topic %s cannot be both STAY and SYSTEM",currentTopicName)
				}
				else if (!stricmp(word,"user"));
                else BADSCRIPT("Bad topic flag %s for topic %s",word,currentTopicName)
			}
			else if (!keywordsDone) ptr = ReadKeyword(word,ptr,notted,quoted,topic,0,false,build,false);//   absorb keyword list
			else if (!stricmp(word,"datum:")) // absorb a top-level data table line
			{
				ptr = ReadTable(ptr,in,build,true);
			}
			else if (TopLevelRule(lowercaseForm))//   absorb a responder/gambit and its rejoinders
			{
				if (IsUpperCase(*word)) BADSCRIPT("Rule ID must be lower case: %s",word);
				++toplevelrules;
				if (TopLevelGambit(word)) ++gambits;
				if (pack == data)
				{
					strcpy(pack,ENDUNITTEXT+1);	//   init 1st rule
					pack += strlen(pack);
				}
				ptr = ReadTopLevelRule(lowercaseForm,ptr,in,pack,data);
				currentRuleID = TOPLEVELID(currentRuleID) + 1;
				pack += strlen(pack);
				if ((pack - data) > (MAX_TOPIC_SIZE - 2000)) BADSCRIPT("TOPIC-4 Topic %s data too big. Split it by calling another topic using u: () respond(~subtopic) and putting the rest of the rules in that subtopic",currentTopicName)
			}
			else BADSCRIPT("Expecting responder for topic %s, got %s",currentTopicName,word)
		}
	}

	--jumpIndex;

	if (parenLevel) BADSCRIPT("TOPIC-5 Failure to balance ( in %s",currentTopicName)
	if (!topicName) BADSCRIPT("TOPIC-6 No topic name?")
	if (toplevelrules > MAX_TOPIC_RULES) BADSCRIPT("TOPIC-8 %s has too many rules- %d must be limited to %d. Call a subtopic.",currentTopicName,toplevelrules,MAX_TOPIC_RULES)
	if (!topicName->w.botNames && *botheader) topicName->w.botNames = AllocateString(botheader,strlen(botheader)); //  harry,georgia,roger

	size_t len = pack-data;
	bool hasUpperCharacters;
	bool hasUTF8Characters;
	unsigned int checksum = (unsigned int) (Hashit((unsigned char*) data, len,hasUpperCharacters,hasUTF8Characters) & 0x0ffffffff);
	
	//   trailing blank after jump code
    SetJumpOffsets(data); 
	if (len >= (MAX_TOPIC_SIZE-100)) BADSCRIPT("TOPIC-7 Too much data in one topic")
	char filename[MAX_WORD_SIZE];
	sprintf(filename,"TOPIC/script%s.txt",baseName);
	FILE* out = FopenUTF8WriteAppend(filename);
	
	// write out topic data
	char* restriction = (topicName->w.botNames) ? topicName->w.botNames : (char*)"all";
	unsigned int len1 = (unsigned int)strlen(restriction);
	fprintf(out,"TOPIC: %s 0x%x %d %d %d %d %s\r\n",currentTopicName,(unsigned int) flags,(unsigned int) checksum,(unsigned int) toplevelrules,(unsigned int) gambits,(unsigned int)(len + len1 + 7),currentFilename); 
	fprintf(out,"\" %s \" %s\r\n",restriction,data);
	fclose(out);
	
	free(data);
	
	return ptr;
}

static char* ReadRename(char* ptr, FILE* in,uint64 build)
{
	renameInProgress = true;
	while (ALWAYS) //   read as many tokens as needed to complete the definition
	{
		char word[MAX_WORD_SIZE];
		char basic[MAX_WORD_SIZE];
		ptr = ReadNextSystemToken(in,ptr,word,false);
		if (!*word) break;

		if (TopLevelUnit(word)) //   definition ends when another major unit starts
		{
			ptr -= strlen(word); //   let someone else see this starter also  // safe
			break; 
		}
		if (*word != '_' && *word != '@' && (*word != '#' || word[1] != '#')) BADSCRIPT("Rename  %s must start with _ or @ or ##",word)
		ptr = ReadNextSystemToken(in,ptr,basic,false);
		if (*word != '#' && (*basic != *word || !IsDigit(basic[1]) )) BADSCRIPT("Rename  %s must start same as %s and have a number after it",basic,word)
		if (*word == '#' && !IsDigit(*basic) && *basic != '-' && *basic != '+') BADSCRIPT("Rename  %s followed by number or sign as %s",word,basic)
		MakeLowerCase(word); 
		int64 n;
		if (*word == '#') 
		{
			ReadInt64(basic,n);
			if (*basic == '-') n = -n; // force positive
		}
		else ReadInt64(basic+1,n);
		WORDP D = StoreWord(word,n);
		AddInternalFlag(D,(unsigned int)(RENAMED|build)); 
		if (*word == '#' && *basic == '-') AddSystemFlag(D,CONSTANT_IS_NEGATIVE);
		Log(STDUSERLOG,"Rename %s as %s\r\n",basic,word);
	}	
	renameInProgress = false;
	return ptr;
}

static char* ReadPlan(char* ptr, FILE* in,uint64 build)
{
	char planName[MAX_WORD_SIZE];
	char baseName[MAX_WORD_SIZE];
	*planName = 0;
	functionArgumentCount = 0;
	int parenLevel = 0;
	WORDP D = NULL;
	bool gettingArguments = true;
	endtopicSeen = false;
	patternContext = false;
	int baseArgumentCount = 0;
	unsigned int duplicateCount = 0;
	while (gettingArguments) //   read as many tokens as needed to get the name and argumentList
	{
		char word[MAX_WORD_SIZE];
		ptr = ReadNextSystemToken(in,ptr,word,false);
		if (!*word) break; //   end of file

		if (!*planName) //   get the plan name
		{
			if (*word == '^') memmove(word,word+1,strlen(word)); //   remove his ^
			MakeLowerCase(word);
			if (!IsAlphaUTF8(*word) ) BADSCRIPT("PLAN-1 Plan name must start alpha %s",word)
			if (!IsLegalName(word)) BADSCRIPT("PLAN-2 Illegal characters in plan name %s",word)
			*planName = '^';
			strcpy(planName+1,word);
			strcpy(baseName,planName);
			Log(STDUSERLOG,"Reading plan %s\r\n",planName);

			// handle potential multiple plans of same name
			WORDP plan = FindWord(planName);
			char name[MAX_WORD_SIZE];
			strcpy(name,planName);
			if (plan) baseArgumentCount = plan->w.planArgCount;
			while (plan && plan->internalBits & FUNCTION_NAME)
			{
				++duplicateCount;
				sprintf(name,"%s%c%d",baseName,DUPLICATETOPICSEPARATOR,duplicateCount);
				plan = FindWord(name);
				strcpy(planName,name);
			}

			D = StoreWord(planName);
			continue;
		}

		size_t len = strlen(word);
		if (TopLevelUnit(word)) //   definition ends when another major unit starts
		{
			ptr -= len; //   let someone else see this starter also
			break; 
		}
		switch(*word)
		{
			case '(': 
				if (parenLevel++ != 0) BADSCRIPT("PLAN-4 bad paren level in plan definition %s",planName)
				continue; //   callArgumentList open
			case ')':
				if (--parenLevel != 0) BADSCRIPT("PLAN-5 bad closing paren in plan definition %s",planName)
				gettingArguments = false;
				break;
			case '^':  //   declaring a new argument
				if (IsDigit(word[1])) BADSCRIPT("PLAN-6 Plan arguments must be alpha names, not digits like %s ",word)
				strcpy(functionArguments[functionArgumentCount++],word);
				if (functionArgumentCount > MAX_ARG_LIMIT)  BADSCRIPT("PLAN-7 Too many callArgumentList to %s - max is %d",planName,MAX_ARG_LIMIT)
				continue;
			default:
				BADSCRIPT("PLAN-7 Bad argument to plan definition %s",planName)
		}
	}
	if (!D) return ptr; //   nothing defined
	if (parenLevel) BADSCRIPT("PLAN-5 Failure to balance ( in %s",planName)
	if (duplicateCount && functionArgumentCount != baseArgumentCount) 
		BADSCRIPT("PLAN->? Additional copies of %s must have %d arguments",planName,baseArgumentCount)
	AddInternalFlag(D,(unsigned int)(FUNCTION_NAME|build|IS_PLAN_MACRO));
	D->w.planArgCount = functionArgumentCount;
	currentFunctionDefinition = D;
	
	char* data = (char*) malloc(MAX_TOPIC_SIZE); // use a big chunk of memory for the data
	*data = 0;
	char* pack = data;

	int holdDepth = globalDepth;
	unsigned int toplevelrules = 0; // does not include rejoinders

	if (setjmp(scriptJump[++jumpIndex])) 
	{
		ptr = FlushToTopLevel(in,ptr,holdDepth,data); //   if error occurs lower down, flush to here
	}
	while (ALWAYS) //   read as many tokens as needed to complete the definition
	{
		char word[MAX_WORD_SIZE];
		ptr = ReadNextSystemToken(in,ptr,word,false);
		if (!*word) break;

		if (TopLevelUnit(word)) //   definition ends when another major unit starts
		{
			ptr -= strlen(word); //   let someone else see this starter also  // safe
			break; 
		}

		switch(*word)
		{
		case '#':
			if (*word == '#' && word[1] == '!')  BADSCRIPT("PLAN-? Verification not meaningful in a plan")
			continue;
		default:
			MakeLowerCopy(lowercaseForm,word);
			if (TopLevelRule(lowercaseForm))//   absorb a responder/gambit and its rejoinders
			{
				++toplevelrules;
				if (pack == data)
				{
					strcpy(pack,ENDUNITTEXT+1);	//   init 1st rule
					pack += strlen(pack);
				}
				ptr = ReadTopLevelRule(lowercaseForm,ptr,in,pack,data);
				pack += strlen(pack);
				if ((pack - data) > (MAX_TOPIC_SIZE - 2000)) BADSCRIPT("PLAN-4 Plan %s data too big. Split it by calling another topic using u: () respond(~subtopic) and putting the rest of the rules in that subtopic",planName)
			}
			else BADSCRIPT("Expecting responder for plan %s, got %s",planName,word)
		}
	}

	--jumpIndex;

	if (toplevelrules > MAX_TOPIC_RULES) BADSCRIPT("PLAN-8 %s has too many rules- %d must be limited to %d. Call a plantopic.",planName,toplevelrules,MAX_TOPIC_RULES)

	size_t len = pack-data;
	if (!len)  WARNSCRIPT("No data in plan %s\r\n",currentTopicName)

	if (!endtopicSeen) BADSCRIPT("PLAN-8 Plan %s cannot succeed since no ^end(plan) exists\n",planName)

	//   trailing blank after jump code
    SetJumpOffsets(data); 
	if (len >= (MAX_TOPIC_SIZE-100)) BADSCRIPT("PLAN-7 Too much data in one plan")
	*pack = 0;

		
	//   write how many plans were found (for when we preload during normal startups)
	if (hasPlans == 0)
	{
		char filename[MAX_WORD_SIZE];
		sprintf(filename,"TOPIC/plans%s.txt",baseName);
		// init the plan output file
		FILE* out = FopenUTF8Write(filename);
		fprintf(out,"0     \r\n"); //   reserve 5-digit count for number of plans
		fclose(out);
	}
	++hasPlans;

	// write out plan data
	FILE* out = FopenUTF8WriteAppend(build == BUILD0 ? (char*)"TOPIC/plans0.txt" : (char*)"TOPIC/plans1.txt");
	char* restriction =  (char*)"all";
	unsigned int len1 = (unsigned int)strlen(restriction);
	fprintf(out,"PLAN: %s %d %d %d %s\r\n",planName,(unsigned int) functionArgumentCount,(unsigned int) toplevelrules,(unsigned int)(len + len1 + 7),currentFilename); 
	fprintf(out,"\" %s \" %s\r\n",restriction,data);
	fclose(out);

	free(data);
	return ptr;
}

static char* ReadQuery(char* ptr, FILE* in, uint64 build) // readquery: name "xxxxx" text
{
	while (ALWAYS) //   read as many tokens as needed to complete the definition (must be within same file)
	{
		char word[MAX_WORD_SIZE];
		char query[MAX_WORD_SIZE];
		ptr = ReadNextSystemToken(in,ptr,word,false); // name of query
		if (!*word) break;	
		size_t len = strlen(word);
		if (!IsAlphaUTF8(*word)) BADSCRIPT("query label %s must be alpha",word);
		if (TopLevelUnit(word)) //   definition ends when another major unit starts
		{
			ptr -= len; //   let someone else see this starter 
			break; 
		}
		ptr = ReadNextSystemToken(in,ptr,query,false);
		if (*query != '"') BADSCRIPT("query body %s must be in quotes",query);
		WORDP D = StoreWord(word);
		AddInternalFlag(D, (unsigned int)(QUERY_KIND|build));
		char* at = strchr(query+1,'"'); 
		*at = 0;
 	    D->w.userValue = AllocateString(query+1);    
	}
	return ptr;
}

static char* ReadReplace(char* ptr, FILE* in, uint64 build)
{
	while (ALWAYS) //   read as many tokens as needed to complete the definition (must be within same file)
	{
		char word[MAX_WORD_SIZE];
		char replace[MAX_WORD_SIZE];
		ptr = ReadNextSystemToken(in,ptr,word,false);
		if (!stricmp(word,"replace:")) ptr = ReadNextSystemToken(in,ptr,word,false); // keep going with local replace loop
		if (!*word) break;	//   file ran dry
		size_t len = strlen(word);
		if (TopLevelUnit(word)) //   definition ends when another major unit starts
		{
			ptr -= len; //   let someone else see this starter 
			break; 
		}
		ptr = ReadNextSystemToken(in,ptr,replace,false);
		char filename[MAX_WORD_SIZE];
		sprintf(filename,"TOPIC/private%s.txt",baseName);
		FILE* out = FopenUTF8WriteAppend(filename);
		fprintf(out," %s %s\r\n",word,replace);
		fclose(out);
	}
	return ptr;
}

void SaveCanon(char* word, char* canon)
{
	char filename[MAX_WORD_SIZE];
	sprintf(filename,"TOPIC/canon%s.txt",baseName);
	FILE* out = FopenUTF8WriteAppend(filename);
	fprintf(out," %s %s\r\n",word,canon);
	fclose(out);
	WritePatternWord(word);		// must recognize this word for spell check
	WritePatternWord(canon);	// must recognize this word for spell check
}

static char* ReadCanon(char* ptr, FILE* in, uint64 build)
{
	while (ALWAYS) //   read as many tokens as needed to complete the definition (must be within same file)
	{
		char word[MAX_WORD_SIZE];
		char canon[MAX_WORD_SIZE];
		ptr = ReadNextSystemToken(in,ptr,word,false);
		if (!stricmp(word,"canonical:")) ptr = ReadNextSystemToken(in,ptr,word,false); // keep going with local  loop
		if (!*word) break;	//   file ran dry
		size_t len = strlen(word);
		if (TopLevelUnit(word)) //   definition ends when another major unit starts
		{
			ptr -= len; //   let someone else see this starter 
			break; 
		}
		ptr = ReadNextSystemToken(in,ptr,canon,false);
		SaveCanon(word,canon);
	}
	return ptr;
}

static char* ReadConcept(char* ptr, FILE* in,uint64 build)
{
	char conceptName[MAX_WORD_SIZE];
	*conceptName = 0;
	MEANING concept = 0;
	WORDP D;
	bool ignoreSpell = false;
	
	patternContext = false;
	bool quoted = false;
	bool notted = false;
	bool more = false;
	bool undeclared = true;
	int parenLevel = 0;
	uint64 type = 0;
	uint64 sys;
	bool duplicate = false;
	while (ALWAYS) //   read as many tokens as needed to complete the definition (must be within same file)
	{
		char word[MAX_WORD_SIZE];
		ptr = ReadNextSystemToken(in,ptr,word,false);
		if (!*word) break;	//   file ran dry
		size_t len = strlen(word);
		if (TopLevelUnit(word)) //   definition ends when another major unit starts
		{
			if (TopLevelUnit(word)) ptr -= len; //   let someone else see this starter 
			break; 
		}

		// establish name and characteristics of the concept
		if (!*conceptName) //   get the concept name, will be ~xxx or :xxx 
		{
			if (*word != '~' ) BADSCRIPT("CONCEPT-1 Concept name must begin with ~ or : - %s",word)

			// Users may not create repeated user topic names. Ones already saved in dictionary are fine to overwrite
			MakeLowerCopy(conceptName,word);
			if (!IsLegalName(conceptName)) BADSCRIPT("CONCEPT-2 Illegal characters in concept name %s",conceptName)
				// create concept header
			D = StoreWord(conceptName);
			concept = MakeMeaning(D);
			sys = type = 0;
			parenLevel = 0;
			Log(STDUSERLOG,"Reading concept %s\r\n",conceptName);
			// read the control flags of the concept
			ptr = SkipWhitespace(ptr);
			while (*ptr && *ptr != '(' && *ptr != '[' && *ptr != '"') // not started and no concept comment given (concept comments come after all control flags
			{
				ptr = ReadCompiledWord(ptr,word);
				size_t len = strlen(word);
				if (word[len-1] == '(') 
				{
					word[len-1] = 0;
					--ptr;
					if (*ptr != '(') --ptr;
				}
				if (!stricmp(word,"more"))
				{
					more = true;
					continue;
				}
				if (!stricmp(word,"duplicate")) // allow duplicate keywords
				{
					duplicate = true;
					continue;
				}
				char* paren = strchr(word,'(');
				if (paren) // handle attachment of paren + stuff
				{
					while (*--ptr != '(');
					*paren = 0;
				}

				ptr = SkipWhitespace(ptr);
				uint64 bits = FindValueByName(word);
				type |= bits;
				uint64 bits1 = FindSystemValueByName(word);
				sys |= bits1;
				unsigned int bits2 = (unsigned int)FindParseValueByName(word);

				if (sys & NOCONCEPTLIST)
				{
					AddInternalFlag(D,FAKE_NOCONCEPTLIST);
					sys ^= NOCONCEPTLIST;
				}
				if (bits) AddProperty(D, bits);
				else if (bits1) AddSystemFlag(D, bits1);
				else if (bits2) AddParseBits(D,bits2);
				else if (!stricmp(word,"IGNORESPELLING")) ignoreSpell = true;
				else if (!stricmp(word,"UPPERCASE_MATCH")) AddInternalFlag(D,UPPERCASE_MATCH);
				else if (!stricmp(word,"ONLY_NOUNS")) AddSystemFlag(D,NOUN);
				else if (!stricmp(word,"ONLY_VERBS")) AddSystemFlag(D,VERB);
				else if (!stricmp(word,"ONLY_ADJECTIVES"))  AddSystemFlag(D,ADJECTIVE);
				else if (!stricmp(word,"ONLY_ADVERBS")) AddSystemFlag(D,ADVERB);
				else if (!stricmp(word,"ONLY_NONE"))  AddSystemFlag(D,ONLY_NONE); // disable ONLY here and below
				else BADSCRIPT("CONCEPT-4 Unknown concept property %s",word) 
			}
			continue;  // read more tokens now that concept has been established
		}
		if (undeclared)
		{
			undeclared = false; // dont test this again
			if (!more)
			{
				if (D->internalBits & CONCEPT && D->internalBits & (BUILD0|BUILD1|BUILD2))
					BADSCRIPT("CONCEPT-3 Concept/topic already defined %s",conceptName)
			}
			AddInternalFlag(D,(unsigned int)(build|CONCEPT));
		}

		// read the keywords zone of the concept
		switch(*word) //   THE MEAT OF CONCEPT DEFINITIONS
		{
			case '(':  case '[':	// start keyword list
				if (parenLevel) BADSCRIPT("CONCEPT-5 Cannot use [ or ( within a keyword list for %s",conceptName);
				parenLevel++;
				break;
			case ')': case ']':		// end keyword list
				--parenLevel;
				if (parenLevel < 0) BADSCRIPT("CONCEPT-6 Missing ( for concept definition %s",conceptName)
				break;
			default: 
				 ptr = ReadKeyword(word,ptr,notted,quoted,concept,type,ignoreSpell,build,duplicate);
		}
		if (parenLevel == 0) break;

	}
	if (parenLevel) BADSCRIPT("CONCEPT-7 Failure to give closing ( in concept %s",conceptName)
	return ptr;
}

static void ReadTopicFile(char* name,uint64 build) //   read contents of a topic file (.top or .tbl)
{	
	size_t len = strlen(name);
	if (len > 1 && name[len-1] == '~') return; // unix backup editor file
	if (len > 4 && !stricmp(name+len-4,".bak")) return; // windows backup file

	*botheader = 0;
	if (name[len-1] == '~') return; // ignore linux edit backup files

	FILE* in = FopenReadNormal(name);
	if (!in) 
	{
		if (strchr(name,'.') || build & FROM_FILE) // names a file, not a directory
		{
			WARNSCRIPT("Missing file %s\r\n",name) 
			++missingFiles;
		}
		return;
	}
	build &= -1 ^ FROM_FILE; // remove any flag indicating it came as a direct file, not from a directory listing

	Log(STDUSERLOG,"\r\n----Reading file %s\r\n",currentFilename);

	//   if error occurs lower down, flush to here
	int holdDepth = globalDepth;
	patternContext = false;
	char* ptr = "";
	if (setjmp(scriptJump[++jumpIndex])) 
	{
		ptr = FlushToTopLevel(in,ptr,holdDepth,0);
	}
	char word[MAX_WORD_SIZE];
	while (ALWAYS) 
	{
		ptr = ReadNextSystemToken(in,ptr,word,false); //   eat tokens (should all be top level)
		if (!*word) break;						//   no more tokens found

		currentFunctionDefinition = NULL; //   can be set by ReadTable or ReadMacro
		if (!stricmp(word,":quit")) break;
				
		if (*word == ':' && word[1])		// testing command
		{
			char output[MAX_WORD_SIZE];
			DoCommand(readBuffer,output);
			*readBuffer = 0;
			*ptr = 0;
		}
		else if (!stricmp(word,"concept:")) ptr = ReadConcept(ptr,in,build);
		else if (!stricmp(word,"query:")) ptr = ReadQuery(ptr,in,build);
		else if (!stricmp(word,"replace:")) ptr = ReadReplace(ptr,in,build);
		else if (!stricmp(word,"canon:")) ptr = ReadCanon(ptr,in,build);
		else if (!stricmp(word,"topic:"))  ptr = ReadTopic(ptr,in,build);
		else if (!stricmp(word,"plan:"))  ptr = ReadPlan(ptr,in,build);
		else if (!stricmp(word,"bot:"))  ptr = ReadBot(ptr,in,build);
		else if (!stricmp(word,"table:")) ptr = ReadTable(ptr,in,build,false);
		else if (!stricmp(word,"rename:")) ptr = ReadRename(ptr,in,build);
		else if (!stricmp(word,"describe:")) ptr = ReadDescribe(ptr,in,build);
		else if (!stricmp(word,"patternMacro:") || !stricmp(word,"outputMacro:") || !stricmp(word,"dualMacro:") || !stricmp(word,"tableMacro:")) ptr = ReadMacro(ptr,in,word,build);
		else BADSCRIPT("FILE-1 Unknown top-level declaration %s in %s",word,name)
	}
	fclose(in);
	--jumpIndex;
}

void DoubleCheckReuse()
{
	FILE* in = FopenReadWritten("TOPIC/missingLabel.txt");
	if (!in) return;

	char word[MAX_WORD_SIZE];
	char topic[MAX_WORD_SIZE];
	while (ReadALine(readBuffer,in) >= 0)
	{
		char *ptr = ReadCompiledWord(readBuffer,word);		// topic + label
		ptr = ReadCompiledWord(ptr,topic);					// from topic
		ptr = ReadCompiledWord(ptr,tmpWord);				// from file
		unsigned int line;
		ReadInt(ptr,line);									// from line
		WORDP D = FindWord(word);
		if (!D) // cannot find full label
		{
			if (!strcmp(topic,word))  WARNSCRIPT("Missing local label %s for reuse/unerase in topic %s in File: %s Line: %d\r\n",word,topic,tmpWord,line)
			else  WARNSCRIPT("Missing cross-topic label %s for reuse in File: %s Line: %d\r\n",word,tmpWord,line)
		}
	}
	fclose(in);
	remove("TOPIC/missingLabel.txt");
}

static void WriteConcepts(WORDP D, uint64 build)
{
	char* name = D->word;
	if (*name != '~' || !(D->internalBits & build)) return; // not a topic or concept or not defined this build
	RemoveInternalFlag(D,(BUILD0|BUILD1|BUILD2));
		
	// write out keywords 
	FILE* out = NULL;
	char filename[MAX_WORD_SIZE];
	sprintf(filename,"TOPIC/keywords%s.txt",baseName);
	out = FopenUTF8WriteAppend(filename);
	fprintf(out,(D->internalBits & TOPIC) ? "T%s " : "%s ", D->word);

	uint64 properties = D->properties;	
	uint64 bit = START_BIT;
	while (properties && bit)
	{
		if (properties & bit && bit)
		{
			properties ^= bit;
			fprintf(out,"%s ",FindNameByValue(bit));
		}
		bit >>= 1;
	}

	properties = D->systemFlags;	
	bit = START_BIT;
	while (properties && bit)
	{
		// dont write this out in keywords see FAKE_NOCONCEPTLIST - these go in DICTn file
		if (properties & bit && !(bit & (PATTERN_WORD|NOCONCEPTLIST)))
		{
			char* name = FindSystemNameByValue(bit);
			properties ^= bit;
			fprintf(out,"%s ",name);
		}
		bit >>= 1;
	}
	if (D->internalBits & FAKE_NOCONCEPTLIST) fprintf(out,"NOCONCEPTLIST ");
	if (D->internalBits & UPPERCASE_MATCH) fprintf(out,"UPPERCASE_MATCH ");
	fprintf(out,"( ");

	size_t lineSize = 0;
	NextInferMark();

	FACT* F = GetObjectNondeadHead(D);
	if (F)
	{
		while (F) 
		{
			if (build == BUILD1 && !(F->flags & FACTBUILD1)) {;} // defined by earlier level
			else if (build == BUILD2 && !(F->flags & FACTBUILD2)) {;} // defined by earlier level
			else if (F->verb == Mmember|| F->verb == Mexclude) // the only relevant facts
			{
				char word[MAX_WORD_SIZE];
				WORDP E = Meaning2Word(F->subject);
				AddInternalFlag(E,BEEN_HERE);
				if (*E->word == '"') // change string to std token
				{
					strcpy(word,E->word+1);
					size_t len = strlen(word);
					word[len-1] = ' ';			// remove trailing quote
					ForceUnderscores(word); 
				}
				else if (F->flags & ORIGINAL_ONLY) sprintf(word,"'%s ",WriteMeaning(F->subject));
				else sprintf(word,"%s ",WriteMeaning(F->subject,true));

				char* dict = strchr(word+1,'~'); // has a wordnet attribute on it
				if (*word == '~' || dict  ) // concept or full wordnet word reference
				{
					if (E->inferMark != inferMark) SetTried(D,0);
					E->inferMark = inferMark; 
					if (dict)
					{
						unsigned int which = atoi(dict+1);
						if (which) // given a meaning index, mark it
						{
							uint64 offset = 1 << which;
							SetTried(E,GetTried(E) | offset);	
						}
					}
				}

				// write it out- this INVERTS the order now and when read back in, will be reestablished correctly 
				// but dictionary storage locations will be inverted
				if (F->verb == Mexclude) fwrite("!",1,1,out);
				size_t wlen = strlen(word);
				lineSize += wlen;
				fwrite(word,1,wlen,out);
				if (lineSize > 500) // avoid long lines
				{
					fprintf(out,"\r\n    ");
					lineSize = 0;
				}
				KillFact(F);
			}
			F = GetObjectNondeadNext(F);
		}
	}

	fprintf(out,")\r\n");
	fclose(out);
}

static void WriteDictionaryChange(FILE* dictout, uint64 build)
{
	// Note that topic labels (topic.name) and pattern words  will not get written
	FILE* in = NULL;
	if ( build == BUILD0) in = FopenReadWritten("TMP/prebuild0.bin");
	else if ( build == BUILD1) in = FopenReadWritten("TMP/prebuild1.bin");
	else if ( build == BUILD2) in = FopenReadWritten("TMP/prebuild2.bin");
	if (!in) 
	{
		ReportBug("prebuild bin not found")
		myexit("Dictionary Change not determinable");
	}
	for (WORDP D = dictionaryBase+1; D < dictionaryFree; ++D) 
	{
		uint64 oldproperties = 0;
		uint64 oldflags = 0;
		bool notPrior = false;
		if ( (build == BUILD0 && D < dictionaryPreBuild[0] ) || (build == BUILD1 && D < dictionaryPreBuild[1]) || 
			 (build == BUILD2 && D < dictionaryPreBuild[2])) // word preexisted this level, so see if it changed
		{
			unsigned int offset = D - dictionaryBase;
			unsigned int xoffset;
			fread(&xoffset,1,4,in);
			if (xoffset != offset) printf("Bad dictionary change test\r\n");
			fread(&oldproperties,1,8,in);
			fread(&oldflags,1,8,in);
			fread(&xoffset,1,4,in); //old internal
			char junk;
			fread(&junk,1,1,in); // multiword header info
			fread(&junk,1,1,in); // 0 marker
			if (junk != 0) printf("out of dictionary change data2?\r\n"); // multiword header 
		}
		else notPrior = true;
		if (!D->word ||  *D->word == '$') continue;		// dont write topic names or concept names, let keywords do that and  no variables
		if (*D->word == '~' && !( D->systemFlags & NOCONCEPTLIST) ) 
			continue;		// dont write topic names or concept names, let keywords do that and  no variables
		if (D->internalBits & FUNCTION_BITS) continue;	 // functions written out in macros file.

		if (D->internalBits & QUERY_KIND && D->internalBits & build && *D->word != '@' && *D->word != '#' && *D->word != '_') 
		{
			fprintf(dictout,"+query %s \"%s\" \r\n",D->word,D->w.userValue); // query defn , not a rename
			continue;
		}

		uint64 prop = D->properties;
		uint64 flags = D->systemFlags;
		if ((*D->word == '_' || *D->word == '@' || *D->word == '#' ) && D->internalBits & RENAMED) 
		{
			if (!notPrior) continue;	// written out before
		}
		else if (D->properties & AS_IS) 
		{
			RemoveProperty(D,AS_IS); // fact field value
			uint64 prop1 = D->properties;
			prop1 &= -1LL ^ oldproperties;
			uint64 sys1 = flags;
			sys1 &= -1LL ^ oldflags;
			sys1 &= -1LL ^ (NO_EXTENDED_WRITE_FLAGS); // we dont need these- concepts will come from keywords file
			if ( (build == BUILD0 && D < dictionaryPreBuild[0] ) ||
				(build == BUILD1 && D < dictionaryPreBuild[1]) ||
				(build == BUILD2 && D < dictionaryPreBuild[2]))
			{
				if (!prop1 && !sys1) continue;	// no need to write out, its in the prior world (though flags might be wrong)
			}
		}
		else if (D->systemFlags & SUBSTITUTE_RECIPIENT) continue; // ignore pattern words, etc EXCEPT when field of a fact
		else if (D->systemFlags & NO_EXTENDED_WRITE_FLAGS && !GetSubjectNondeadHead(D) && !GetVerbNondeadHead(D) && !GetObjectNondeadHead(D)) continue; // ignore pattern words, etc EXCEPT when field of a fact
		else if (D->properties & (NOUN_NUMBER|ADJECTIVE_NUMBER)  && IsDigit(*D->word)) continue; // no numbers
		else if (!D->properties && D->internalBits & UPPERCASE_HASH && !D->systemFlags) continue; // boring uppercase pattern word, just not marked as pattern word because its uppercase

		char* at = D->word - 1;
		while (IsDigit(*++at)){;}
		if (*at == 0) continue;  // purely a number - not allowed to write it out. not allowed to have unusual flags

		// only write out changes in flags and properties
		D->properties &= -1LL ^ oldproperties; // remove the old properties
		D->systemFlags &= -1 ^  oldflags; // remove the old flags

		// if the ONLY change is an existing word got made into a concept, dont write it out anymore
		if (!D->properties && !D->systemFlags && D->internalBits & CONCEPT && D <= dictionaryPreBuild[0] ) {;}  // preexisting word a concept
		else if (D->properties || D->systemFlags || notPrior ||  ((*D->word == '_' || *D->word == '@' || *D->word == '#') && D->internalBits & RENAMED))  // there were changes
		{
			fprintf(dictout,"+ %s ",D->word);
			if ((*D->word == '_' || (*D->word == '@')) && D->internalBits & RENAMED) fprintf(dictout,"%d",(unsigned int)D->properties); // rename value
			else if (*D->word == '#' &&  D->internalBits & RENAMED)
			{
				int64 x = (int64)D->properties;
				if (D->systemFlags & CONSTANT_IS_NEGATIVE) 
				{
					fprintf(dictout,"%c",'-');
					x = -x;
				}
#ifdef WIN32
				fprintf(dictout,"%I64d",x); 
#else
				fprintf(dictout,"%lld",x); 
#endif
			}
			else WriteDictionaryFlags(D,dictout); // write the new
			fprintf(dictout,"\r\n");
		}
		D->properties = prop;
		D->systemFlags = flags;
	}
	fclose(in);
    fclose(dictout);
}

static void WriteExtendedFacts(FILE* factout,FILE* dictout,uint64 build)
{
	if (!factout || !dictout) return;

	char* buffer = AllocateBuffer();
	bool oldshared = shared;
	shared = false;
	char* ptr = WriteUserVariables(buffer,false,true);
	shared = oldshared;
	fwrite(buffer,ptr-buffer,1,factout);
	FreeBuffer();

	WriteDictionaryChange(dictout,build);
	if (build == BUILD0) WriteFacts(factout,factsPreBuild[0]);
	else if (build == BUILD1) WriteFacts(factout,factsPreBuild[1]);
	else if (build == BUILD2) WriteFacts(factout,factsPreBuild[2],FACTBUILD2);
}

static void ClearTopicConcept(WORDP D, uint64 build)
{
	unsigned int k = (ulong_t) build;
	if ((D->internalBits & (TOPIC | CONCEPT)) & k)   RemoveInternalFlag(D,CONCEPT|BUILD0|BUILD1|BUILD2|TOPIC);
}

static void DumpErrors()
{
	if (errorIndex) Log(STDUSERLOG,"\r\n ERROR SUMMARY: \r\n");
	for (unsigned int i = 0; i < errorIndex; ++i) Log(STDUSERLOG,"  %s\r\n",errors[i]);
}

static unsigned int DumpWarnings(unsigned int& substitutes,unsigned int &cases, unsigned int &function)
{
	if (warnIndex) Log(STDUSERLOG,"\r\nWARNING SUMMARY: \r\n");
	unsigned int count = 0;
	cases = 0;
	substitutes = 0;
	function = 0;
	for (unsigned int i = 0; i < warnIndex; ++i) 
	{
		if (strstr(warnings[i],"is not a known word")) {++count;}
		else if (strstr(warnings[i]," changes ")) {++substitutes;}
		else if (strstr(warnings[i],"is unknown as a word")) {++count;}
		else if (strstr(warnings[i],"in opposite case")){++cases;}
		else if (strstr(warnings[i],"a function call")){++function;}
		else Log(STDUSERLOG,"  %s\r\n",warnings[i]);
	}
	return count;
}

static void EmptyVerify(char* name, uint64 junk)
{
	char* x = strstr(name,"-b");
	if (!x) return;
	char c = (buildID == BUILD0) ? '0' : '1';
	if (x[2] == c) unlink(name);
}

void ReadTopicFiles(char* name,uint64 build,int spell)
{
	overrriding = false;
	if (build == BUILD2) // for dynamic segment, we are allowed full names
	{
		strcpy(baseName,name+5);
		char* dot = strchr(baseName,'.');
		*dot = 0;
	}
	else if (build == BUILD1) strcpy(baseName,"1");
	else strcpy(baseName,"0");

	char* output = testOutput;
	testOutput = NULL;
	FILE* in = FopenReadNormal(name); // default was top level chatscript
	if (!in)
	{
		char file[MAX_WORD_SIZE];
		sprintf(file,"RAWDATA/%s",name); // 2nd default is rawdata itself
		in = FopenReadNormal(file);
		if (!in)
		{
			sprintf(file,"private/%s",name); // 3rd default is private
			in = FopenReadNormal(file);
			if (!in)
			{
				sprintf(file,"../%s",name); // 4th default is just above chatscript folder
				in = FopenReadNormal(file);
				if (!in)
				{
					printf("%s not found\r\n",name);
					return;
				}
			}
		}
	}
	lastDeprecation = 0;
	hasPlans = 0;
	char word[MAX_WORD_SIZE];
	buildID = build;				// build 0 or build 1
	*duplicateTopicName = 0;	// an example of a repeated topic name found
	*newBuffer = 0;
	missingFiles = 0;
	spellCheck = spell;			// what spell checking to perform

	//   erase facts and dictionary to appropriate level
	if (build == BUILD2) ReturnToLayer(1,false); // rip dictionary back to start of build (but props and systemflags can be wrong)
	else if (build == BUILD1) ReturnToLayer(0,true); // rip dictionary back to start of build (but props and systemflags can be wrong)
	else  ReturnDictionaryToWordNet();
	WalkDictionary(ClearTopicConcept,build);				// remove concept/topic flags from prior defined by this build
	EraseTopicFiles(build,baseName);

	WalkDirectory("VERIFY",EmptyVerify,0); // clear verification of this level

	ClearUserVariables();
	compiling = true;
	errorIndex = warnIndex = hasWarnings = hasErrors = 0;
	echo = true;
	
	//   store known pattern words in pattern file that we want to recognize (not spellcorrect on input)
	char filename[MAX_WORD_SIZE];
	sprintf(filename,"TOPIC/patternWords%s.txt",baseName);
	patternFile = FopenUTF8Write(filename);
	if (!patternFile)
	{
		printf("Unable to create patternfile  in the TOPIC subdirectory? Make sure this directory exists and is writable.\r\n");
		return;
	}

	AllocateOutputBuffer();

	// init the script output file
	sprintf(filename,"TOPIC/script%s.txt",baseName);
	FILE* out = FopenUTF8Write(filename);
	if (strlen(name) > 100) name[99] = 0;
	if (!strnicmp(name,"files",5)) name += 5; // dont need the prefix
	char* at = strchr(name,'.');
	*at = 0;
	fprintf(out,"0     %s %s\r\n",GetMyTime(time(0)),name); //   reserve 5-digit count for number of topics + timestamp  (AFTER BOM)
	fclose(out);
	
	uint64 oldtokenControl = tokenControl;
	tokenControl = 0;
	topicCount = 0;
	
	//   read file list to service
	while (ReadALine(readBuffer,in) >= 0)
	{
		ReadCompiledWord(readBuffer,word);
		if (*word == '#' || !*word) continue;
		if (!stricmp(word,"stop") || !stricmp(word,"exit")) break; //   fast abort
		size_t len = strlen(word);
		char output[MAX_WORD_SIZE];
		if (word[len-1] == '/') 
		{
			Log(STDUSERLOG,"\r\n>>Reading folder %s\r\n",word);
			WalkDirectory(word,ReadTopicFile,build); // read all files in folder (top level)
			Log(STDUSERLOG,"\r\n<<end folder %s\r\n",word);
		}
		else if (*word == ':' && word[1]) DoCommand(readBuffer,output); // testing command
		else ReadTopicFile(word,build|FROM_FILE); // was explicitly named
	}
	if (in) fclose(in);
	fclose(patternFile);

	StartFile("Post compilation Verification");

	// verify errors across all files
	DoubleCheckSetOrTopic();	//   prove all sets/topics he used were defined
	DoubleCheckReuse();		// see if jump labels are defined
	if (*duplicateTopicName)  WARNSCRIPT("At least one duplicate topic name, i.e., %s, which may intended if bot restrictions differ.\r\n",duplicateTopicName)
	WalkDictionary(ClearBeenHere,0);

	// write out compiled data

	//   write how many topics were found (for when we preload during normal startups)
	sprintf(filename,"TOPIC/script%s.txt",baseName);
	out = FopenUTF8WriteAppend(filename,"rb+");
	if (out)
	{
		fseek(out,0,SEEK_SET);
		sprintf(word,"%05d",topicCount);
		unsigned char bom[3];
		bom[0] = 0xEF;
		bom[1] = 0xBB;
		bom[2] = 0xBF;
		fwrite(bom,1,3,out);
		fwrite(word,1,5 * sizeof(char),out);
		fclose(out);
	}

	if (hasPlans)
	{
		sprintf(filename,"TOPIC/plans%s.txt",baseName);
		out = FopenUTF8WriteAppend(filename,"rb+");
		if (out)
		{
			char word[MAX_WORD_SIZE];
			fseek(out,0,SEEK_SET);
			sprintf(word,"%05d",hasPlans);
			fwrite(word,1,5 * sizeof(char),out);
			fclose(out);
		}
	}

	// we delay writing out keywords til now, allowing multiple accumulation across tables and concepts
	WalkDictionary(WriteConcepts,build);
	WalkDictionary(ClearBeenHere,0);

	// dump variables, dictionary changes, topic facts
	sprintf(filename,"TOPIC/facts%s.txt",baseName);
	char filename1[MAX_WORD_SIZE];
	sprintf(filename1,"TOPIC/dict%s.txt",baseName);
	WriteExtendedFacts(FopenUTF8Write(filename), FopenUTF8Write(filename1),  build); 
	
	// cleanup
	buildID = 0;
	numberOfTopics = 0;
	tokenControl  = oldtokenControl;
	currentRuleOutputBase = currentOutputBase = NULL;
	FreeOutputBuffer();
	compiling = false;
	jumpIndex = 0;

	testOutput = output; // allow summary to go out the server
	if (hasErrors) 
	{
		EraseTopicFiles(build,baseName);
		DumpErrors();
		if (missingFiles) Log(STDUSERLOG,"%d topic files were missing.\r\n",missingFiles);
		Log(STDUSERLOG,"r\n%d errors - press Enter to quit. Then fix and try again.\r\n",hasErrors);
		if (!server && !commandLineCompile) ReadALine(readBuffer,stdin);
	}
	else if (hasWarnings) 
	{
		unsigned int substitutes;
		unsigned int cases;
		unsigned int function;
		unsigned int count = DumpWarnings(substitutes,cases,function);
		if (missingFiles) Log(STDUSERLOG,"%d topic files were missing.\r\n",missingFiles);
		Log(STDUSERLOG,"%d function warnings, %d spelling warnings, %d case warnings, %d substitution warnings,  and %d more serious warnings\r\n    ",function,count,cases,substitutes,hasWarnings-count-substitutes-cases);
	}
	else 
	{
		if (missingFiles) Log(STDUSERLOG,"%d topic files were missing.\r\n",missingFiles);
		Log(STDUSERLOG,"No errors or warnings\r\n\r\n");
	}
	ReturnDictionaryToWordNet();
	Log(STDUSERLOG,"\r\n\r\nFinished compile\r\n\r\n");
}

char* CompileString(char* ptr) // incoming is:  ^"xxx"
{
	char tmp[MAX_WORD_SIZE * 2];
	strcpy(tmp,ptr); // protect copy from multiple readcalls
	size_t len = strlen(tmp);
	if (tmp[len-1] != '"') BADSCRIPT("STRING-1 String not terminated with doublequote %s",tmp)
	tmp[len-1] = 0;	// remove trailing quote

	// flip the FUNCTION marker inside the string
	static char data[MAX_WORD_SIZE * 2];	
	char* pack = data;
	*pack++ = '"';
	*pack++ = FUNCTIONSTRING;
	*pack++ = ':'; // a internal marker that is has in fact been compiled - otherwise it is a format string whose spaces count but cant fully execute

	if (tmp[2] == '(')  ReadPattern(tmp+2,NULL,pack,false,false); // incoming is:  ^"(xxx"
	else ReadOutput(tmp+2,NULL,pack,NULL);

	TrimSpaces(data,false);
	len = strlen(data);
	data[len]  = '"';	// put back closing quote
	data[len+1] = 0;
	return data;
}
#endif
