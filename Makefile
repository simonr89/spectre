EXEC=invgen
OBJDIR=obj
SRCDIR=src
# SRC=main.cpp\
#     logic/Formula.cpp\
#     logic/Sort.cpp\
#     logic/Signature.cpp\
#     logic/Term.cpp\
#     logic/Theory.cpp\
#     parser/GclParser.cpp\
#     parser/GclScanner.cpp\
#     program/Expression.cpp\
#     program/GclAnalyzer.cpp\
#     program/GuardedCommandCollection.cpp\
#     program/Properties.cpp\
#     program/Variable.cpp\
#     program/Type.cpp\
#     util/Options.cpp
PARSER_SRC=$(SRCDIR)/parser/GclParser.cpp
PARSER_HDR=$(SRCDIR)/parser/GclParser.hpp
SCANNER_SRC=$(SRCDIR)/parser/GclScanner.cpp
SRC := $(wildcard $(SRCDIR)/**/*.cpp) $(wildcard $(SRCDIR)/*.cpp) $(PARSER_SRC) $(SCANNER_SRC)
OBJ := $(SRC:$(SRCDIR)/%.cpp=$(OBJDIR)/%.o)
CXX=g++
CXXFLAGS=-std=c++11 $(XFLAGS) -Wall -I$(SRCDIR)
LDFLAGS=
BISON=bison
FLEX=flex

all: $(PARSER_SRC) $(SCANNER_SRC) $(EXEC)

invgen: $(OBJ)
	$(CXX) -o $@ $^ $(CXXFLAGS) $(LDFLAGS)

$(PARSER_SRC) $(PARSER_HDR): $(SRCDIR)/parser/GclParser.yy
	$(BISON) --defines=$(PARSER_HDR) -o $(PARSER_SRC) $^

$(SCANNER_SRC): $(SRCDIR)/parser/GclScanner.ll
	$(FLEX) -o $@ $^

.PHONY: clean cleanparser

clean:
	rm -fr $(OBJ)

mrproper: clean
	rm $(EXEC)
	rm $(PARSER_SRC) $(SCANNER_SRC) $(SRCDIR)/parser/stack.hh

$(OBJDIR)/%.o: $(SRCDIR)/%.cpp
	mkdir -p $(@D)
	$(CXX) -o $@ -c $< $(CXXFLAGS)
