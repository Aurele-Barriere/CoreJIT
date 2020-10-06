LIB=$(shell opam config var lib)/ocaml

all: native_lib.o

native_lib.o: native_lib.c
	gcc -O2 -g -fPIC -I$(LIB) -c native_lib.c -o native_lib.o
