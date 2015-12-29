 // tagger.cpp - used for pos tagging

#include "common.h"

unsigned int lowercaseWords;
unsigned int knownWords;
unsigned int tagRuleCount = 0;
uint64* tags = NULL;
char** comments = NULL;
static char* Describe(unsigned int i,char* buffer);

char* wordCanonical[MAX_SENTENCE_LENGTH]; //   chosen canonical form
WORDP originalLower[MAX_SENTENCE_LENGTH];
WORDP originalUpper[MAX_SENTENCE_LENGTH];
WORDP canonicalLower[MAX_SENTENCE_LENGTH];
WORDP canonicalUpper[MAX_SENTENCE_LENGTH];
uint64 finalPosValues[MAX_SENTENCE_LENGTH];
uint64 allOriginalWordBits[MAX_SENTENCE_LENGTH];	// starting pos tags in this word position
uint64 lcSysFlags[MAX_SENTENCE_LENGTH];      // current system tags lowercase in this word position (there are no interesting uppercase flags)
uint64 posValues[MAX_SENTENCE_LENGTH];			// current pos tags in this word position
uint64 canSysFlags[MAX_SENTENCE_LENGTH];		// canonical sys flags lowercase in this word position 
unsigned int parseFlags[MAX_SENTENCE_LENGTH];

static unsigned char describeVerbal[100];
static unsigned char describePhrase[100];
static unsigned char describeClause[100];
static unsigned  int describedVerbals;
static unsigned  int describedPhrases;
static unsigned  int describedClauses;

// dynamic cumulative data across assignroles calls
unsigned int phrases[MAX_SENTENCE_LENGTH];
unsigned int clauses[MAX_SENTENCE_LENGTH];
unsigned int verbals[MAX_SENTENCE_LENGTH];
unsigned char ignoreWord[MAX_SENTENCE_LENGTH];
unsigned char coordinates[MAX_SENTENCE_LENGTH]; // for conjunctions
unsigned char crossReference[MAX_SENTENCE_LENGTH]; // object back to spawner,  particle back to verb
unsigned char phrasalVerb[MAX_SENTENCE_LENGTH]; // linking verbs and particles (potential)
uint64 roles[MAX_SENTENCE_LENGTH];
unsigned char tried[MAX_SENTENCE_LENGTH];

unsigned char objectRef[MAX_SENTENCE_LENGTH] ;  // link from verb to any main object ( allow use of 0 and end for holding)
unsigned char indirectObjectRef[MAX_SENTENCE_LENGTH];  // link from verb to any indirect object
unsigned char complementRef[MAX_SENTENCE_LENGTH ];  // link from verb to any 2ndary complement
// also posValues

int itAssigned = 0;
int theyAssigned = 0;

char* GetNounPhrase(int i,const char* avoid)
{
	static char buffer[MAX_WORD_SIZE];
	*buffer = 0;
#ifndef DISCARDPARSER
	if (clauses[i-1] != clauses[i]) // noun is a clause
	{
		unsigned int clause = clauses[i];
		unsigned int at = i-1;
		while (clauses[++at] & clause)
		{
			char* word = wordStarts[at];							
			if (tokenFlags & USERINPUT) strcat(buffer,word);		
			else if (!stricmp(word,"my")) strcat(buffer,"your");	
			else if (!stricmp(word,"your")) strcat(buffer,"my");	
			else strcat(buffer,word);
			strcat(buffer," ");
		}
		size_t len = strlen(buffer);
		buffer[len-1] = 0;
		return buffer;
	}

	if (posValues[i+1] & (NOUN_INFINITIVE|NOUN_GERUND)) // noun is a verbal 
	{
		unsigned int verbal = verbals[i];
		unsigned int at = i-1;
		while (verbals[++at] & verbal)
		{
			char* word = wordStarts[at];							
			if (tokenFlags & USERINPUT) strcat(buffer,word);		
			else if (!stricmp(word,"my")) strcat(buffer,"your");	
			else if (!stricmp(word,"your")) strcat(buffer,"my");	
			else strcat(buffer,word);
			strcat(buffer," ");
		}
		size_t len = strlen(buffer);
		buffer[len-1] = 0;
		return buffer;
	}

	if (clauses[i-1] != clauses[i]) return wordStarts[i]; // cannot cross clause boundary
	if (verbals[i-1] != verbals[i]) return wordStarts[i]; // cannot cross verbal boundary
	if (phrases[i-1] != phrases[i]) return wordStarts[i]; // cannot cross phrase boundary

	int start = (int) i; // on the noun
	// NOTE posvalues still has adjectivenoun as adjective.  Finalposvalues has it as a noun.
	while (--start > 0 && posValues[start] & (NOUN_BITS | COMMA | CONJUNCTION_COORDINATE | ADJECTIVE_BITS | DETERMINER | PREDETERMINER | ADVERB | POSSESSIVE | PRONOUN_POSSESSIVE)) 
	{
		if (roles[start] & (MAININDIRECTOBJECT|INDIRECTOBJECT2)) break; // cannot switch to this
		if (posValues[start] & TO_INFINITIVE) break;
		if (posValues[start] & COMMA && !(posValues[start-1] & ADJECTIVE_BITS)) break; // NOT like:  the big, red, tall human
		if (posValues[start] & CONJUNCTION_COORDINATE)
		{
			if ( canonicalLower[start] && strcmp(canonicalLower[start]->word,"and")) break;	// not "and"
			if (!(posValues[start-1] & (ADJECTIVE_BITS|COMMA))) break;	// NOT like:  the big, red, and very tall human
			if (posValues[start-1] & COMMA && !(posValues[start-2] & ADJECTIVE_BITS)) break;	// NOT like:  the big, red, and very tall human
		}
		if (posValues[start] & NOUN_GERUND) break; 
		if (posValues[start] & ADVERB && !(posValues[start+1] & ADJECTIVE_BITS)) break;

		WORDP canon = canonicalLower[start];
		WORDP orig = originalLower[start];
		if (orig && (!strcmp("here",orig->word) || !strcmp("there",orig->word))) break;
		//if (orig && (!strcmp("this",orig->word) || !strcmp("that",orig->word) || !strcmp("these",orig->word) || !strcmp("those",orig->word))) break;
		if (canon && canon->properties & PRONOUN_BITS && !strcmp(canon->word,avoid)) break; // avoid recursive pronoun expansions... like "their teeth"
		if (posValues[start] & NOUN_PROPER_SINGULAR) break; // proper singular blocks appostive 
	}
	
	// start is NOT a member
	while (++start <= i)
	{
		char* word = wordStarts[start];							
		if (tokenFlags & USERINPUT) strcat(buffer,word);		
		else if (!stricmp(word,"my")) strcat(buffer,"your");	
		else if (!stricmp(word,"your")) strcat(buffer,"my");	
		else strcat(buffer,word);
		if (start != i) strcat(buffer," ");
	}
#endif
	return buffer;
}

static char* DescribeComponent(unsigned int i,char* buffer,char* open, char* close) // verbal or phrase or clause
{
	strcat(buffer,open);
	Describe(i,buffer);
	strcat(buffer,close);
	return buffer;
}

static char* Describe(unsigned int i,char* buffer)
{
	// before
	unsigned int currentPhrase = phrases[i] & (-1 ^ phrases[i-1]); // only the new bit
	if (!currentPhrase) currentPhrase = phrases[i];
	unsigned int currentVerbal = verbals[i] & (-1 ^ verbals[i-1]); // only the new bit
	if (!currentVerbal) currentVerbal = verbals[i];
	unsigned int currentClause = clauses[i] & (-1 ^ clauses[i-1]); // only the new bit
	if (!currentClause) currentClause = clauses[i];
	bool found = false;
	char word[MAX_WORD_SIZE];
	for (unsigned int j = 1; j < i; ++j) // find things before
	{
		if (ignoreWord[j]) continue;
		if (crossReference[j] == i && posValues[j] & IDIOM)
		{
			strcat(buffer,wordStarts[j]);
			strcat(buffer,"_");
		}
		else if (crossReference[j] == i && phrases[j] ^ currentPhrase)
		{
			if (!found) strcat(buffer," [");
			else  strcat(buffer," ");
			found = true;
			++describedPhrases;
			describePhrase[describedPhrases] = (unsigned char)j;
			sprintf(word,"p%d",describedPhrases);
			strcat(buffer,word);
			strcat(buffer," ");
		}
		else if (crossReference[j] == i && verbals[j] ^ currentVerbal)
		{
			if (!found) strcat(buffer," [");
			else  strcat(buffer," ");
			found = true;
			++describedVerbals;
			describeVerbal[describedVerbals] =  (unsigned char)j;
			sprintf(word,"v%d",describedVerbals);
			strcat(buffer,word);
			strcat(buffer," ");
		}
		else if (crossReference[j] == i && clauses[j] ^ currentClause)
		{
			if (!found) strcat(buffer," [");
			else  strcat(buffer," ");
			found = true;
			++describedClauses;
			describeClause[describedClauses] =  (unsigned char)j;
			sprintf(word,"c%d",describedClauses);
			strcat(buffer,word);
			strcat(buffer," ");
		}
		else if (crossReference[j] == i && !(roles[j] & (MAINSUBJECT|MAINOBJECT|MAININDIRECTOBJECT)))
		{
			if (roles[j] & OBJECT_COMPLEMENT && posValues[j] & NOUN_BITS && !phrases[j] && !clauses[j] && !verbals[j]) continue;
			if (!found) strcat(buffer," [");
			else  strcat(buffer," ");
			found = true;
			if (posValues[j] != TO_INFINITIVE) Describe(j,buffer);
			else strcat(buffer,"to");
		}
	}
	if (found) 
	{
		char* end = buffer + strlen(buffer) - 1;
		if (*end == ' ') *end = 0;
		strcat(buffer,"]");
	}
	found = false;
	if (!(posValues[i-1] & IDIOM)) strcat(buffer," ");

	// the word
	strcat(buffer,wordStarts[i]);
	if (*wordStarts[i] == '"') strcat(buffer,"...\""); // show omitted quotation

	// after
	for (unsigned int j = i+1; j <= wordCount; ++j) // find things after
	{
		if (ignoreWord[j]) continue;
		if (crossReference[j] == i && posValues[j] & PARTICLE)
		{
			strcat(buffer,"_");
			strcat(buffer,wordStarts[j]);
		}
		else if (crossReference[j] == i && phrases[j] ^ currentPhrase)
		{
			if (!found) strcat(buffer," [");
			else  strcat(buffer," ");
			found = true;
			++describedPhrases;
			describePhrase[describedPhrases] =  (unsigned char)j;
			sprintf(word,"p%d",describedPhrases);
			strcat(buffer,word);
			strcat(buffer," ");
		}
		else if (crossReference[j] == i && verbals[j] ^ currentVerbal)
		{
			if (!found) strcat(buffer," [");
			else  strcat(buffer," ");
			found = true;
			++describedVerbals;
			describeVerbal[describedVerbals] =  (unsigned char)j;
			sprintf(word,"v%d",describedVerbals);
			strcat(buffer,word);
			strcat(buffer," ");
		}
		else if (crossReference[j] == i && clauses[j] ^ currentClause)
		{
			if (!found) strcat(buffer," [");
			else  strcat(buffer," ");
			found = true;
			++describedClauses;
			describeClause[describedClauses] =  (unsigned char)j;
			sprintf(word,"c%d",describedClauses);
			strcat(buffer,word);
			strcat(buffer," ");
		}
		else if (currentPhrase && phrases[j] == currentPhrase && roles[j] & OBJECT2 && crossReference[j] == i)
		{
			strcat(buffer," ");
			Describe(j,buffer);
		}
		else if (posValues[i] & TO_INFINITIVE && posValues[j] & (NOUN_INFINITIVE|VERB_INFINITIVE))
		{
			strcat(buffer," ");
			Describe(j,buffer);
		}
		else if (crossReference[j] == i && !(roles[j] & (MAINSUBJECT|MAINOBJECT|MAININDIRECTOBJECT)))
		{
			if (roles[j] & OBJECT_COMPLEMENT && posValues[j] & NOUN_BITS && !phrases[j] && !clauses[j] && !verbals[j]) continue;
			if (!found && !(posValues[i] & PREPOSITION)) strcat(buffer," [");
			found = true;
			Describe(j,buffer);
			strcat(buffer," ");
		}
	}
	if (found) 
	{
		char* end = buffer + strlen(buffer) - 1;
		if (*end == ' ') *end = 0;
		strcat(buffer,"] ");
	}

	if (coordinates[i] > i) // conjoined
	{
		strcat(buffer," + " );
		Describe(coordinates[i],buffer);
	}

	return buffer;
}

void DescribeUnit(unsigned int i, char* buffer, char* msg,unsigned int verbal, unsigned int clause)
{
	char word[MAX_WORD_SIZE];
	if (i) // adjective object or causal infinitive
	{
		strcat(buffer,msg);
		if (verbals[i] != verbal)  
		{
			++describedVerbals;
			describeVerbal[describedVerbals] =  (unsigned char)i;
			sprintf(word,"v%d",describedVerbals);
			strcat(buffer,word);
		}
		else if (clauses[i] != clause)
		{
			++describedClauses;
			describeClause[describedClauses] =  (unsigned char)i;
			sprintf(word,"c%d",describedClauses);
			strcat(buffer,word);
		}
		else Describe(i,buffer);
		strcat(buffer," ");
	}
}

void DumpSentence(unsigned int start,unsigned int end)
{
#ifndef DISCARDPARSER
	unsigned int to = end;
	unsigned int subject = 0, verb = 0, indirectobject = 0, object = 0,complement = 0;
	unsigned int i;
	bool notFound = false;
	char word[MAX_WORD_SIZE];
	describedVerbals = 0;
	describedPhrases = 0;
	describedClauses = 0;

	for ( i = start; i <= to; ++i) // main sentence
	{
		if (ignoreWord[i] && *wordStarts[i] != '"') continue;
		if (roles[i] & MAINSUBJECT && !subject) subject = i;
		if (roles[i] & MAINVERB && !verb) verb = i;
		if (roles[i] & OBJECT_COMPLEMENT && posValues[i] & NOUN_BITS && !complement) complement = i;
		if (roles[i] & OBJECT_COMPLEMENT && posValues[i] & (ADJECTIVE_BITS|VERB_INFINITIVE|NOUN_INFINITIVE) && !complement) complement = i;
		if (roles[i] & SUBJECT_COMPLEMENT && !complement) complement = i;
		if (!stricmp(wordStarts[i],"not")) notFound = true;
		if (roles[i] & SENTENCE_END) 
		{
			to = i;
			break;
		}
		if ((roles[i] & CONJUNCT_KINDS) == CONJUNCT_SENTENCE)
		{
			to = i;
			break;
		}
	}
	char* buffer = AllocateBuffer();
	strcat(buffer,"  MainSentence: ");

	for (i = start; i <= to; ++i)
	{
		if (roles[i] & ADDRESS)
		{
			Describe(i,buffer);
			strcat(buffer," :  ");
		}
	}
	
	if (subject) DescribeUnit(subject,buffer, "Subj:",0,0);
	else if (tokenFlags& IMPLIED_YOU) 	strcat(buffer,"YOU   ");
	
	if (verb) 
	{
		object = objectRef[verb];
		indirectobject = indirectObjectRef[verb];
		strcat(buffer,"  Verb:");
		if (notFound) strcat(buffer,"(NOT!) ");
		Describe(verb,buffer);
		strcat(buffer,"   ");
	}

	if (indirectobject) 
	{
		strcat(buffer,"  IndObj:");
		Describe(indirectobject,buffer);
		strcat(buffer,"   ");
	}

	DescribeUnit(object,buffer, "  Obj:",0,0);
	DescribeUnit(complement,buffer, "Compl:",0,0);

	if (clauses[start]){;}
	else if (!stricmp(wordStarts[start],"when")) strcat(buffer,"(:when) ");
	else if (!stricmp(wordStarts[start],"where")) strcat(buffer,"(:where) ");
	else if (!stricmp(wordStarts[start],"why")) strcat(buffer,"(:why) ");
	else if (!stricmp(wordStarts[start],"who") && subject != 1 && object != 1) strcat(buffer,"(:who) ");
	else if (!stricmp(wordStarts[start],"what") && subject != 1 && object != 1) strcat(buffer,"(:what) ");
	else if (!stricmp(wordStarts[start],"how")) strcat(buffer,"(:how) ");

	if (tokenFlags & QUESTIONMARK)  strcat(buffer,"? ");

	if (tokenFlags & PAST) strcat(buffer," PAST ");
	else if (tokenFlags & FUTURE) strcat(buffer," FUTURE ");
	else if (tokenFlags & PRESENT) strcat(buffer," PRESENT ");

	if (tokenFlags & PERFECT) strcat(buffer,"PERFECT ");
	if (tokenFlags & CONTINUOUS) strcat(buffer,"CONTINUOUS ");

	if (tokenFlags & PASSIVE) strcat(buffer," PASSIVE ");
	strcat(buffer,"\n");
	for (unsigned int i = 1; i <= describedPhrases; ++i)
	{
		sprintf(word,"Phrase %d :",i);
		strcat(buffer,word);
		Describe(describePhrase[i],buffer);
		strcat(buffer,"\n");
	}
	for (unsigned int i = 1; i <= describedVerbals; ++i)
	{
		sprintf(word,"Verbal %d: ",i);
		strcat(buffer,word);
		unsigned int verbal = describeVerbal[i]; 
		unsigned int verbalid = verbals[verbal] & (-1 ^ verbals[verbal-1]);
		if (!verbalid) verbalid = verbals[verbal];
		for (unsigned int j = i; j <= endSentence; ++j)
		{
			if (!(verbals[j] & verbalid)) continue;
			if (roles[j] & VERB2) 
			{
				strcat(buffer,"  Verb:");
				Describe(j,buffer); // the verb
				if (indirectObjectRef[j]) 
				{
					strcat(buffer,"  Indirect: ");
					Describe(indirectObjectRef[j],buffer);
				}
				DescribeUnit(objectRef[j],buffer, "  Direct:",verbalid,0);
				DescribeUnit(complementRef[j],buffer, " Complement:",verbalid,0);
				break;
			}
		}
		strcat(buffer,"\n");
	}
	for (unsigned int i = 1; i <= describedClauses; ++i)
	{
		sprintf(word,"Clause %d %s : ",i,wordStarts[describeClause[i]]);
		strcat(buffer,word);
		unsigned int clause = describeClause[i];
		unsigned int clauseid = clauses[clause] & (-1 ^ clauses[clause-1]);
		if (!clauseid) clauseid = clauses[clause];
		for (unsigned int j = i; j <= endSentence; ++j)
		{
			if (!(clauses[j] & clauseid)) continue;
			if (roles[j] & SUBJECT2)  
			{
				strcat(buffer,"  Subj:");
				Describe(j,buffer); // the subject
				strcat(buffer,"  ");
			}
			if (roles[j] & VERB2)  
			{
				strcat(buffer,"  Verb:");
				Describe(j,buffer); // the verb
				if (indirectObjectRef[j]) 
				{
					strcat(buffer,"  Indirect: ");
					Describe(indirectObjectRef[j],buffer);
				}
				DescribeUnit(objectRef[j],buffer, "  Direct:",0,clauseid);
				DescribeUnit(complementRef[j],buffer, "  Complement:",0,clauseid);
			}
		}
		strcat(buffer,"\n");
	}

	for (unsigned int i = start; i <= to; ++i) // show phrases
	{
		if (ignoreWord[i]) continue;
		if (i >= to) continue; // ignore
		if (coordinates[i] && posValues[i] & CONJUNCTION_COORDINATE)
		{
			strcat(buffer,"\r\n Coordinate ");
			uint64 crole = roles[i] & CONJUNCT_KINDS;
			if (crole == CONJUNCT_NOUN) strcat(buffer,"Noun: ");
			else if (crole == CONJUNCT_VERB) strcat(buffer,"Verb: ");
			else if (crole == CONJUNCT_ADJECTIVE) strcat(buffer,"Adjective: ");
			else if (crole == CONJUNCT_ADVERB) strcat(buffer,"Adverb: ");
			else if (crole == CONJUNCT_PHRASE) strcat(buffer,"Phrase: ");
			else strcat(buffer,"Sentence: ");
			strcat(buffer,wordStarts[i]);
			strcat(buffer," (");
			if (coordinates[i] && coordinates[coordinates[i]])
			{
				strcat(buffer,wordStarts[coordinates[coordinates[i]]]); // the before
				strcat(buffer,"/");
				strcat(buffer,wordStarts[coordinates[i]]); // the after
			}
			strcat(buffer,") ");
		}
	}

	for (unsigned int i = start; i <= to; ++i) // show phrases
	{
		if (ignoreWord[i]) continue;
		if ( phrases[i] && phrases[i] != phrases[i-1] && (i != wordCount || phrases[wordCount] != phrases[1])) 
		{
			if (posValues[i] & (NOUN_BITS|PRONOUN_BITS)) strcat(buffer,"\r\n  Absolute Phrase: ");
			//else if (posValues[i] & (ADJECTIVE_BITS|ADVERB)) strcat(buffer,"\r\n  Time Phrase: ");
			else continue;
			if (i == 1 && phrases[wordCount] == phrases[1]) 
			{
				DescribeComponent(wordCount,buffer,"{","}"); // wrapped?
				strcat(buffer," ");
			}
			DescribeComponent(i,buffer,"{","}"); // wrapped?
			strcat(buffer," ");
		}

		if (roles[i] & TAGQUESTION) strcat(buffer," TAGQUESTION ");
	}

	Log(STDUSERLOG,"%s\r\n",buffer);

	FreeBuffer();
	if (to < end) DumpSentence(to+1,end); // show next piece
#endif
 }
 
char* roleSets[] = 
{
	"~mainsubject","~mainverb","~mainobject","~mainindirectobject",
	"~whenunit","~whereunit","~howunit","~whyunit",
	"~subject2","~verb2","~object2","~indirectobject2","~byobject2","~ofobject2",
	"~appositive","~adverbial","~adjectival",
	"~subjectcomplement","~objectcomplement","~address","~postnominal_adjective","adjective_complement","omitted_time_prep","omitted_of_prep",
	"~comma_phrase","tagquestion","~absolute_phrase","~omitted_subject_verb","~reflexive","~DISTANCE_NOUN_MODIFY_ADVERB","~DISTANCE_NOUN_MODIFY_ADJECTIVE","~TIME_NOUN_MODIFY_ADVERB","~TIME_NOUN_MODIFY_ADJECTIVE",
	"~conjunct_noun","~conjunct_verb","~conjunct_adjective","conjunct_adverb","conjunct_phrase","conjunct_clause","conjunct_sentence",
	NULL
};
	
char* GetRole(uint64 role)
{
	static char answer[MAX_WORD_SIZE];
	*answer = 0; 
#ifndef DISCARDPARSER
	if (role & APPOSITIVE) strcat(answer, "APPOSITIVE ");
	if (role & ADVERBIAL) strcat(answer, "ADVERBIAL ");
	if (role & ADJECTIVAL) strcat(answer, "ADJECTIVAL ");  // if it is not specified as adverbial or adjectival, it is used as a noun  -- prep after a noun will be adjectival, otherwize adverbial
	// THey claim a preposition phrase to act as a noun � "During a church service is not a good time to discuss picnic plans" or "In the South Pacific is where I long to be" 
	// but inverted it's - a good time to discuss picnic plans is not during a church service. 

	if ((role & ADVERBIALTYPE) == WHENUNIT) strcat(answer, "WHENUNIT ");	
	if ((role & ADVERBIALTYPE)  == WHEREUNIT) strcat(answer, "WHEREUNIT ");
	if ((role & ADVERBIALTYPE)   == HOWUNIT) strcat(answer, "HOWUNIT "); // how and in what manner
	if ((role & ADVERBIALTYPE)   == WHYUNIT) strcat(answer, "WHYUNIT ");

	if (role & MAINSUBJECT) strcat(answer,"MAINSUBJECT ");
	if (role & MAINVERB) strcat(answer, "MAINVERB ");
	if (role & MAINOBJECT) strcat(answer, "MAINOBJECT ");
	if (role & MAININDIRECTOBJECT) strcat(answer,  "MAININDIRECTOBJECT ");
	
	if (role & OBJECT2) strcat(answer,  "OBJECT2 ");
	if (role & BYOBJECT2) strcat(answer,  "BYOBJECT2 ");
	if (role & OFOBJECT2) strcat(answer,  "OFOBJECT2 ");
	if (role & SUBJECT2) strcat(answer,  "SUBJECT2 ");
	if (role & VERB2) strcat(answer,  "VERB2 ");
	if (role & INDIRECTOBJECT2) strcat(answer, "INDIRECTOBJECT2 ");
	if (role & OBJECT_COMPLEMENT) strcat(answer,   "OBJECT_COMPLEMENT ");
	if (role & SUBJECT_COMPLEMENT) strcat(answer,   "SUBJECT_COMPLEMENT ");
	
	unsigned int crole = role & CONJUNCT_KINDS;

	if (crole == CONJUNCT_NOUN) strcat(answer, "CONJUNCT_NOUN ");
	else if (crole == CONJUNCT_VERB) strcat(answer, "CONJUNCT_VERB ");
	else if (crole == CONJUNCT_ADJECTIVE) strcat(answer, "CONJUNCT_ADJECTIVE ");
	else if (crole == CONJUNCT_ADVERB) strcat(answer, "CONJUNCT_ADVERB ");
	else if (crole == CONJUNCT_PHRASE) strcat(answer, "CONJUNCT_PHRASE ");
	else if (crole== CONJUNCT_CLAUSE) strcat(answer, "CONJUNCT_CLAUSE ");
	else if (crole == CONJUNCT_SENTENCE) strcat(answer, "CONJUNCT_SENTENCE ");
	
	if (role & POSTNOMINAL_ADJECTIVE) strcat(answer, "POSTNOMINAL_ADJECTIVE ");
	if (role & ADJECTIVE_COMPLEMENT) strcat(answer, "ADJECTIVE_COMPLEMENT ");
	if (role & OMITTED_TIME_PREP) strcat(answer, "OMITTED_TIME_PREP ");
	if (role & DISTANCE_NOUN_MODIFY_ADVERB) strcat(answer, "DISTANCE_NOUN_MODIFY_ADVERB ");
	if (role & DISTANCE_NOUN_MODIFY_ADJECTIVE) strcat(answer, "DISTANCE_NOUN_MODIFY_ADJECTIVE ");
	if (role & TIME_NOUN_MODIFY_ADVERB) strcat(answer, "TIME_NOUN_MODIFY_ADVERB ");
	if (role & TIME_NOUN_MODIFY_ADJECTIVE) strcat(answer, "TIME_NOUN_MODIFY_ADJECTIVE ");
	if (role & OMITTED_OF_PREP) strcat(answer, "OMITTED_OF_PREP ");
	if (role & ADDRESS) strcat(answer, "ADDRESS ");
	if (role & COMMA_PHRASE) strcat(answer, "COMMA_PHRASE ");
	if (role & TAGQUESTION) strcat(answer, "TAGQUESTION ");
	if (role & ABSOLUTE_PHRASE) strcat(answer, "ABSOLUTE_PHRASE ");
	if (role & OMITTED_SUBJECT_VERB) strcat(answer, "OMITTED_SUBJECT_VERB ");

#endif
	return answer;
}
