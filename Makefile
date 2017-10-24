EXEC=invgen
OBJDIR=obj
SRCDIR=src
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

all: $(PARSER_SRC) $(PARSER_HDR) $(SCANNER_SRC) $(EXEC)

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
	find $(OBJDIR) -depth -type d -empty -exec rmdir "{}" \;

$(OBJDIR)/%.o: $(SRCDIR)/%.cpp
	mkdir -p $(@D)
	$(CXX) -o $@ -c $< $(CXXFLAGS)
