#ifndef _ENGLISHH_
#define _ENGLISHH_
#ifdef INFORMATION
Copyright (C) 2011-2015 by Bruce Wilcox

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
#endif

#define MAINLEVEL 1

#define MAX_CLAUSES 50
extern unsigned int ambiguousWords;
extern unsigned int posTiming;
extern unsigned char quotationInProgress;
extern unsigned int roleIndex;
extern unsigned int needRoles[MAX_CLAUSES]; 
extern unsigned char subjectStack[MAX_CLAUSES];
extern unsigned char verbStack[MAX_CLAUSES];
extern char* usedTrace;
extern unsigned int usedWordIndex;
extern uint64 usedType;

void SetRole(unsigned int i, uint64 role, bool revise = false, unsigned int currentVerb = verbStack[roleIndex]);
void DecodeTag(char* buffer, uint64 type, uint64 tie,uint64 originalbits);

uint64 GetPosData(unsigned int at, char* original,WORDP &entry,WORDP &canonical,uint64 &sysflags,uint64 &cansysflags, bool firstTry = true,bool nogenerate = false,unsigned int start = 0);
char* English_GetAdjectiveBase(char* word,bool nonew);
char* English_GetAdverbBase(char* word,bool nonew);
char* English_GetPastTense(char* word);
char* English_GetPastParticiple(char* word);
char* English_GetPresentParticiple(char* word);
char* English_GetThirdPerson(char* word);
char* English_GetPresent(char* word);
char* English_GetInfinitive(char* word,bool nonew);
char* English_GetSingularNoun(char* word,bool initial,bool nonew);
char* English_GetPluralNoun(WORDP noun);
char* English_GetAdjectiveMore(char* word);
char* English_GetAdjectiveMost(char* word);
char* English_GetAdverbMore(char* word);
char* English_GetAdverbMost(char* word);
void English_SetSentenceTense(unsigned int start, unsigned int end);
uint64 ProbableAdjective(char* original, unsigned int len,uint64& expectedBase);
uint64 ProbableAdverb(char* original, unsigned int len,uint64& expectedBase);
uint64 ProbableNoun(char* original,unsigned int len);
uint64 ProbableVerb(char* original,unsigned int len);
bool IsDeterminedNoun(unsigned int i,unsigned int& det);
#endif
