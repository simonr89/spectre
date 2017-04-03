CXX=g++
CXXFLAGS=-std=c++11 $(XFLAGS) -Wall -I.
LDFLAGS=
BISON=bison
FLEX=flex
EXEC=invgen
SRC=main.cpp\
    logic/Formula.cpp\
    logic/Sort.cpp\
    logic/Signature.cpp\
    logic/Term.cpp\
    logic/Theory.cpp\
    parser/GclParser.cpp\
    parser/GclScanner.cpp\
    program/Expression.cpp\
    program/GclAnalyzer.cpp\
    program/GuardedCommandCollection.cpp\
    program/Properties.cpp\
    program/Variable.cpp\
    program/Type.cpp
OBJ=$(SRC:.cpp=.o)

all: $(EXEC) parser_src

invgen: $(OBJ)
	$(CXX) -o $@ $^ $(LDFLAGS)

parser/GclParser.cpp parser/GclParser.hpp: parser/GclParser.yy
	$(BISON) --defines=parser/GclParser.hpp -o parser/GclParser.cpp parser/GclParser.yy

parser/GclScanner.cpp: parser/GclScanner.ll
	$(FLEX) -o $@ parser/GclScanner.ll

.PHONY: clean parser_src cleanparser

clean:
	rm -fr $(OBJ)

parser_src: parser/GclParser.cpp parser/GclScanner.cpp

cleanparser:
	rm parser/GclParser.cpp parser/GclParser.hpp parser/GclScanner.cpp parser/stack.hh

%.o: %.cpp
	$(CXX) -o $@ -c $< $(CXXFLAGS)
