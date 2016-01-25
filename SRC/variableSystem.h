#ifndef _VARIABLESYSTEMH_
#define _VARIABLESYSTEMH_
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

#define ALREADY_HANDLED -1
#define MAX_USER_VARS 5000
#define MAX_USERVAR_SIZE 5000

#define MAX_WILDCARDS 20  // _0 ... _20 inclusive
#define WILDCARD_START(x) (x & 0x0000ffff)
#define WILDCARD_END(x) ( x >> 16)

extern  unsigned int wildcardIndex;
extern char wildcardOriginalText[MAX_WILDCARDS+1][MAX_USERVAR_SIZE+1];  //   spot wild cards can be stored
extern char wildcardCanonicalText[MAX_WILDCARDS+1][MAX_USERVAR_SIZE+1];  //   spot wild cards can be stored
extern char wildcardConceptText[MAX_WILDCARDS+1][MAX_USERVAR_SIZE+1];  //   spot wild cards can be stored
extern unsigned int wildcardPosition[MAX_WILDCARDS+1]; //   spot it started and ended in sentence (16bit end 16bit start)
extern int impliedSet;
extern int impliedWild;
extern char impliedOp;
extern unsigned int userVariableIndex;
extern unsigned int botVariableIndex;
extern WORDP userVariableList[MAX_USER_VARS];
extern WORDP botVariableList[MAX_USER_VARS];
extern char wildcardSeparator[2];

// wildcard accessors
char* GetwildcardText(unsigned int i, bool canon);
void SetWildCard(char* value,char* canonicalVale,const char* index,unsigned int position,char* concept = NULL);
void SetWildCard(unsigned int start, unsigned int end, bool inpattern = false, char* concept = NULL);
void SetWildCardIndexStart(unsigned int);
int GetWildcardID(char* x);

// Variables loaded from bot (topic system)
void ClearBotVariables();
void ReestablishBotVariables();
void NoteBotVariables();
void InitVariableSystem();

// debug data
void ShowChangedVariables();
void DumpUserVariables();

// user variable accessors
void ClearUserVariableSetFlags();
void ClearUserVariables(char* above = 0);
char* GetUserVariable(const char* word);
void SetUserVariable(const char* var, char* word);
void Add2UserVariable(char* var, char* word,char* op);

char* PerformAssignment(char* word,char* ptr,FunctionResult& result);


#endif
