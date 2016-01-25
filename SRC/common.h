#ifndef _MAXH_
#define _MAXH_

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

#define INPUT_BUFFER_SIZE   4000
#define MAX_BUFFER_SIZE		80000

// These can be used to shed components of the system to save space
//#define DISCARDSERVER 1
//#define DISCARDSCRIPTCOMPILER 1
//#define DISCARDPARSER 1
//#define DISCARDTESTING 1
//#define DISCARDTCPOPEN 1
//#define DISCARDDATABASE 1
//#define DISCARDDICTIONARYBUILD 1 // only a windows version can build a dictionary from scratch
//#define DISCARDJSON 1

#ifdef LOEBNER
#define DISCARDSERVER 1
#define DISCARDSCRIPTCOMPILER 1
#define DISCARDTESTING 1
#define DISCARDTCPOPEN 1
#define DISCARDDATABASE 1
#define DISCARDDICTIONARYBUILD 1
#define DISCARDCOUNTER 1
#define DISCARDCLIENT 1
#define DISCARDJSON 1
#elif WIN32
//#define USERPATHPREFIX 1
#define DISCARDDATABASE 1
#define DISCARDDICTIONARYBUILD 1 // only a windows version can build a dictionary from scratch
#elif IOS
#define DISCARDCOUNTER 1
#define DISCARDDICTIONARYBUILD 1 
#define DISCARDDATABASE 1
#define SEPARATE_STRING_SPACE 1
#define DISCARDCOUNTER 1
#define DISCARDCLIENT 1
#define DISCARDJSON 1
#elif ANDROID
#define DISCARDCOUNTER 1
#define DISCARDDICTIONARYBUILD 1 
#define DISCARDDATABASE 1
#define DISCARDCOUNTER 1
#define DISCARDCLIENT 1
#define DISCARDJSON 1
#elif MACH
#define DISCARDDICTIONARYBUILD 1 
#define SEPARATE_STRING_SPACE 1
#define DISCARDCOUNTER 1
#define DISCARDCLIENT 1
#define DISCARDJSON 1
#else // GENERIC LINUX
#define DISCARDDICTIONARYBUILD 1  
#define SEPARATE_STRING_SPACE 1
#endif


// These can be used to include LINUX EVSERVER component - this is automatically done by the makefile in src - EV Server does not work under windows
// #define EVSERVER 1

// These can be used to embed chatscript within another application (then you must call InitSystem on startup yourself)
// #define NOMAIN 1

typedef unsigned long long int  uint64;
typedef signed long long  int64;
#define ALWAYS (1 == always)

#ifndef WIN32
	typedef long long long_t; 
	typedef unsigned long long ulong_t; 
	#include <sys/time.h> 
	#include <termios.h> 
	#include <unistd.h>
	#define stricmp strcasecmp 
	#define strnicmp strncasecmp 
#else
	typedef long long_t;       
	typedef unsigned long ulong_t; 
#endif

#ifdef WIN32
	#pragma comment(lib, "ws2_32.lib") 
	#pragma warning( disable : 4100 ) 
	#pragma warning( disable : 4189 ) 
	#pragma warning( disable : 4290 ) 
	#pragma warning( disable : 4706 )
	#pragma warning( disable : 4996 ) 

	#define _CRT_SECURE_NO_DEPRECATE
	#define _CRT_SECURE_NO_WARNINGS 1
	#define _CRT_NONSTDC_NO_DEPRECATE
	#define _CRT_NONSTDC_NO_WARNINGS 1
#ifndef WIN32_LEAN_AND_MEAN
	#define WIN32_LEAN_AND_MEAN
#endif
	#include <winsock2.h> // needs to compile before any refs to winsock.h
	#include <ws2tcpip.h>
	#include <iphlpapi.h>
	#pragma comment(lib, "Ws2_32.lib")
	#pragma comment (lib, "Mswsock.lib")
	#pragma comment (lib, "AdvApi32.lib")
#elif IOS
	#include <dirent.h>
	#include <mach/clock.h>
	#include <mach/mach.h>
	#define DISCARDDATABASE 1
#elif __MACH__
	#include <dirent.h>
	#include <mach/clock.h>
	#include <mach/mach.h>
	#define DISCARDDATABASE 1
#else  // LINUX
	#include <dirent.h>
	#ifndef LINUX
		#define LINUX 1
	#endif
#endif

#ifdef IOS
#elif __MACH__
#include <sys/malloc.h>
#else
#include <malloc.h>
#endif
	
#define NUMBER_OF_LAYERS 3

#ifdef BIG_DICTIONARY
typedef uint64 MEANING;							//   a flagged indexed dict ptr
#define MAX_DICTIONARY	0x000fffffffffffffULL  //   vocabulary limit 
#define NODEBITS		0x00ffffffffffffffULL
#define MULTIWORDHEADER_SHIFT 56
#define MULTIHEADERBITS 0xFF00000000000000ULL

#define SYNSET_MARKER		0x0800000000000000ULL  // this meaning is a synset head - on keyword import, its quote flag for binary read
#define INDEX_BITS          0x03F0000000000000ULL  //   7 bits of ontology meaning indexing ability  63 possible meanings allowed
#define INDEX_OFFSET        52          //   shift for ontoindex  (rang 0..63)  
#define MAX_MEANING			63			// limit
#define INDEX_MINUS			0x0010000000000000ULL  // what to decrement to decrement the meaning index
#define MEANING_BASE		0x000fffffffffffffULL	//   the index of the dictionary item
#define TYPE_RESTRICTION	0xf000000000000000ULL  // corresponds to basic pos
#define TYPE_RESTRICTION_SHIFT 32

#else
typedef unsigned int MEANING;					//   a flagged indexed dict ptr
#define MAX_DICTIONARY	 0x000fffff				//   1M word vocabulary limit (doubling this FAILS on amazon server)
#define NODEBITS 0x00ffffff
#define MULTIWORDHEADER_SHIFT 24
#define MULTIHEADERBITS 0xFF000000

#define SYNSET_MARKER		0x08000000  // this meaning is a synset head - on keyword import, its quote flag for binary read
#define INDEX_BITS          0x03F00000  //   7 bits of ontology meaning indexing ability  63 possible meanings allowed
#define INDEX_OFFSET        20          //   shift for ontoindex  (rang 0..63)  
#define MAX_MEANING			63			// limit
#define INDEX_MINUS			0x00100000  // what to decrement to decrement the meaning index
#define MEANING_BASE		0x000fffff	//   the index of the dictionary item
#define TYPE_RESTRICTION	0xf0000000  // corresponds to basic pos
#define TYPE_RESTRICTION_SHIFT 0
#endif

#include <algorithm>
#include <assert.h>
#include <cstddef>
#include <cstdio>
#include <ctime>
#include <ctype.h>
#include <errno.h>
#include <exception>  
#include <fcntl.h>
#include <iostream>
#include <math.h>
#include <memory.h>
#include <setjmp.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h> 
#include <stdlib.h> 
#include <string>  
#include <string.h>
#include <sys/stat.h>
#include <sys/timeb.h> 
#include <sys/types.h>
#include <time.h>
#include <utility>
#include <vector>

using namespace std;

#undef WORDP //   remove windows version (unsigned short) for ours

#ifdef EVSERVER
#define EV_STANDALONE 1
#define EV_CHILD_ENABLE 1
#define LOCKUSERFILE 1		// protext from multiple servers hitting same file
//#define USERPATHPREFIX 1	// do binary tree of log file - for high speed servers recommend userlog, no server log and this (large server logs are a pain to handle)
#endif

#define BIG_WORD_SIZE   10000
#define MAX_WORD_SIZE   1500       

#include "dictionarySystem.h"
#include "os.h"
#include "mainSystem.h"
#include "functionExecute.h"

#include "csocket.h"
#include "constructCode.h"
#include "english.h"
#include "factSystem.h"
#include "infer.h"
#include "markSystem.h"
#include "outputSystem.h"
#include "patternSystem.h"
#include "scriptCompile.h"
#include "spellcheck.h"
#include "systemVariables.h"
#include "testing.h"
#include "textUtilities.h"
#include "tagger.h"
#include "tokenSystem.h"
#include "topicSystem.h"
#include "userCache.h"
#include "userSystem.h"
#include "variableSystem.h"

#endif