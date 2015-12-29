#ifndef _MARKSYSTEMH_
#define _MARKSYSTEMH_
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

#define SEQUENCE_LIMIT 5		// max number of words in a row to hit on as an entry
#define MAX_XREF_SENTENCE 32	// number of places a word can hit to in sentence * 2 = 64 bytes
extern unsigned int maxRefSentence;

extern char respondLevel;
extern char unmarked[MAX_SENTENCE_LENGTH];
extern bool showMark;
extern unsigned int concepts[MAX_SENTENCE_LENGTH]; 
extern unsigned int topics[MAX_SENTENCE_LENGTH]; 

void VerifyWhere();
MEANING* GetTemps(WORDP D);
unsigned int GetNextSpot(WORDP D,int start,unsigned int& startx,unsigned int& endx,bool reverse = false);
unsigned int GetIthSpot(WORDP D,unsigned int i,unsigned int& start,unsigned int& end);
void MarkWordHit(WORDP D, unsigned int start,unsigned int end);
void MarkFacts(MEANING M,unsigned int start,unsigned int end,bool canonical = false, bool sequence = false);
void RemoveMatchValue(WORDP D, unsigned int position);
void MarkAllImpliedWords();
void ClearWhereInSentence();
void ClearTemps();
void AllocateWhereInSentence(WORDP D);
void SetTried(WORDP D,uint64 bits);
uint64 GetTried(WORDP D);
char* DumpAnalysis(unsigned int start, unsigned int end, uint64 posValues[MAX_SENTENCE_LENGTH],const char* label,bool original,bool roles);
#endif
