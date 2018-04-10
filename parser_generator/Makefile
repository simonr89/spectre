SRCDIR=../src

PARSER_SRC=$(SRCDIR)/parser/GclParser.cpp
PARSER_HDR=$(SRCDIR)/parser/GclParser.hpp
SCANNER_SRC=$(SRCDIR)/parser/GclScanner.cpp

BISON=bison
FLEX=flex

all: $(PARSER_SRC) $(PARSER_HDR) $(SCANNER_SRC)

$(PARSER_SRC) $(PARSER_HDR): GclParser.yy
	$(BISON) --defines=$(PARSER_HDR) -o $(PARSER_SRC) $^

$(SCANNER_SRC): GclScanner.ll
	$(FLEX) -o $@ $^

.PHONY: clean mrproper

clean:

mrproper: 
	rm $(PARSER_SRC) $(PARSER_HDR) $(SCANNER_SRC) stack.hh
