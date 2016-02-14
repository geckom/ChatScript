
g++ -funsigned-char src/*.cpp  -o ChatScript -L/user/lib -lcurl -lpthread 2>err.txt

or maybe below if the above doesnt work for you

g++ -funsigned-char src/*.cpp  -o ChatScript  -lpthread -lcurl 2>err.txt
