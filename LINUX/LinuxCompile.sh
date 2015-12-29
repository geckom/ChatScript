g++ -funsigned-char src/*.cpp -O2  -DDISCARDDATABASE=1 -o LinuxChatScript -lpthread -lrt 2>>err.txt

!// -lpq  to add in postgresql -I /usr/include/postgresql/include and remove -DDISCARDDATABASE=1 



