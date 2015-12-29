#ifndef _EXECUTE
#define _EXECUTE


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

#include "common.h"

#define MAX_ARGUMENT_COUNT 400 //  assume 10 args 40 nested calls max. 


#define FAILCODES ( FAILINPUT_BIT | FAILTOPIC_BIT | FAILLOOP_BIT | FAILRULE_BIT | FAILSENTENCE_BIT | RETRYSENTENCE_BIT | RETRYTOPIC_BIT | UNDEFINED_FUNCTION | RETRYINPUT_BIT )
#define SUCCESSCODES ( ENDINPUT_BIT | ENDSENTENCE_BIT | ENDTOPIC_BIT | ENDRULE_BIT | ENDCALL_BIT | ENDLOOP_BIT)
#define ENDCODES ( FAILCODES | SUCCESSCODES  )
#define RESULTBEYONDTOPIC ( FAILSENTENCE_BIT | ENDSENTENCE_BIT | RETRYSENTENCE_BIT | ENDINPUT_BIT | FAILINPUT_BIT | RETRYINPUT_BIT )
	
typedef FunctionResult (*EXECUTEPTR)(char* buffer);

#define SAMELINE 2

typedef struct SystemFunctionInfo 
{
	const char* word;					//   dictionary word entry
	EXECUTEPTR fn;				//   function to use to get it
	int argumentCount;			//   how many callArgumentList it takes
	int	properties;				//   non-zero means does its own argument tracing
	const char* comment;
} SystemFunctionInfo;

//   special argeval codes
#define VARIABLE_ARG_COUNT -1
#define STREAM_ARG -2
			
// codes returned from :command
enum TestMode { 
	FAILCOMMAND = 0,
	COMMANDED = 1,
	NOPROCESS = 2,
	BEGINANEW = 3,
	OUTPUTASGIVEN = 4,
};

//   argument data for system calls
extern TestMode wasCommand;

#define MAX_ARG_LIST 200
#define MAX_CALL_DEPTH 400
extern unsigned int callIndex;
extern WORDP callStack[MAX_CALL_DEPTH];
extern unsigned int callArgumentBases[MAX_CALL_DEPTH];    // arguments to functions

extern long http_response;

#define MAX_ARG_LIMIT 15 // max args to a call -- limit using 2 bit (COMPILE/KEEP_QUOTES) per arg for table mapping behavior
extern unsigned int currentIterator;

extern char lastInputSubstitution[INPUT_BUFFER_SIZE];
extern int globalDepth;
#define ARGUMENT(n) callArgumentList[callArgumentBase+n]
#ifdef WIN32
FunctionResult InitWinsock();
#endif

#ifndef DISCARDDATABASE
void PGUserFilesCode();
void PGUserFilesCloseCode();
void pguserLog(const void* buffer,size_t size);
void pguserBug(const void* buffer,size_t size);
extern char* pguserdb;
#endif

//   argument data for user calls
#define MAX_ARG_BYTES 50000
extern char callArgumentList[MAX_ARGUMENT_COUNT+1][MAX_ARG_BYTES];    //   function callArgumentList
extern unsigned int callArgumentIndex;
extern unsigned int callArgumentBase;
extern unsigned int fnVarBase;
extern SystemFunctionInfo systemFunctionSet[];

extern bool planning;
extern bool nobacktrack;
FunctionResult MemoryMarkCode(char* buffer);
FunctionResult MemoryFreeCode(char* buffer);
void ResetReuseSafety();
void InitFunctionSystem(); 
char* DoFunction(char* name, char* ptr, char* buffer,FunctionResult &result);
void DumpFunctions();
unsigned int Callback(WORDP D,char* arguments);
void ResetFunctionSystem();
void SaveMark(char* buffer,unsigned int iterator);

FunctionResult KeywordTopicsCode(char* buffer);
void SetBaseMemory();
void ResetBaseMemory();
void InitJSONNames();

// utilities
char* ResultCode(FunctionResult result);
FunctionResult FLR(char* buffer,char* which);
void ResetUser(char* input);
bool RuleTest(char* rule);
FunctionResult DebugCode(char* buffer);
FunctionResult IdentifyCode(char* buffer);
FunctionResult MatchCode(char* buffer);
#endif
