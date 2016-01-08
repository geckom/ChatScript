debugserver: DEFINES+= -DLOCKUSERFILE=1 -DEVSERVER=1 -DEVSERVER_FORK=1 -DDISCARDDATABASE=1 
debugserver: PGLOAD= -pthread
debugserver: INCLUDEDIRS=-Ievserver
debugserver: all
debugserver: EXECUTABLE=ChatScriptDebug
debugserver: CFLAGS=-c -Wall  -funsigned-char  -Wno-write-strings -Wno-char-subscripts -Wno-strict-aliasing -g

debugpgserver: DEFINES+= -DLOCKUSERFILE=1 -DEVSERVER=1 -DEVSERVER_FORK=1 
debugpgserver: PGLOAD= -lpq -pthread
debugpgserver: INCLUDEDIRS=-Ievserver
debugpgserver: all
debugpgserver: EXECUTABLE=ChatScriptpgDebug
debugpgserver: CFLAGS=-c -Wall  -funsigned-char  -Wno-write-strings -Wno-char-subscripts -Wno-strict-aliasing -g

server: DEFINES+= -DLOCKUSERFILE=1 -DEVSERVER=1 -DEVSERVER_FORK=1 -DDISCARDDATABASE=1
server: PGLOAD= -pthread
server: INCLUDEDIRS=-Ievserver
server: all
server: EXECUTABLE=ChatScript
server: CFLAGS=-c -Wall  -funsigned-char  -Wno-write-strings -Wno-char-subscripts -Wno-strict-aliasing 

standalone: DEFINES+=  -DDISCARDSERVER=1 -DDISCARDDATABASE=1 
standalone: PGLOAD= -pthread
standalone: INCLUDEDIRS=-Ievserver
standalone: all
standalone: EXECUTABLE=ChatScript
standalone: CFLAGS=-c -Wall  -funsigned-char  -Wno-write-strings -Wno-char-subscripts -Wno-strict-aliasing 

pgserver: DEFINES+= -DLOCKUSERFILE=1 -DEVSERVER=1 -DEVSERVER_FORK=1 
pgserver: PGLOAD= -lpq -pthread
pgserver: all
pgserver: EXECUTABLE=ChatScriptpg
pgserver: INCLUDEDIRS=-Ievserver -Ipostgres
pgserver: CFLAGS=-c -Wall  -funsigned-char  -Wno-write-strings -Wno-char-subscripts -Wno-strict-aliasing 

UNAME := $(shell uname)

CC=g++

ifeq ($(UNAME), Linux)
$(info ************ LINUX VERSION ************)
LDFLAGS= -lrt -lcurl --verbose $(PGLOAD) 
endif

ifeq ($(UNAME), Darwin)
$(info ************ MAC VERSION ************)
LDFLAGS=-mmacosx-version-min=10.7 $(PGLOAD)  
CFLAGS=-mmacosx-version-min=10.7 -c -Wall  -funsigned-char -Wno-write-strings -Wno-char-subscripts 
endif

SOURCES=constructCode.cpp evserver.cpp csocket.cpp cs_ev.c dictionarySystem.cpp englishTagger.cpp factSystem.cpp  functionExecute.cpp english.cpp infer.cpp jsmn.cpp markSystem.cpp os.cpp outputSystem.cpp patternSystem.cpp  scriptCompile.cpp spellcheck.cpp secure.cpp systemVariables.cpp tagger.cpp testing.cpp textUtilities.cpp tokenSystem.cpp topicSystem.cpp userCache.cpp userSystem.cpp variableSystem.cpp mainSystem.cpp 
OBJECTS=$(SOURCES:.cpp=.o)
 
all: $(SOURCES) binary

clean:
	-rm -f $(EXECUTABLE)
	-rm -f ../$(EXECUTABLE)
	-rm -f *.o

binary: $(OBJECTS)
	$(CC) $(OBJECTS) $(LDFLAGS) $(DEFINES) $(INCLUDEDIRS) -o $(EXECUTABLE)
	cp $(EXECUTABLE) ..

.cpp.o:
	$(CC) $(CFLAGS) $(DEFINES) $(INCLUDEDIRS) $< -o $@
