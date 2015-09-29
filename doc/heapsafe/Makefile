SYSTEM=$(shell uname)

EXE=$(shell if rst2latex.py /dev/null >/dev/null 2>/dev/null; then echo .py; fi)

TARGETS = heapsafe.html
IMAGES = $(wildcard *.png)

all: $(TARGETS)

clean:
	rm -f $(TARGETS) heapsafe.tex heapsafe.out heapsafe.aux heapsafe.log

heapsafe.pdf: heapsafe.tex
	pdflatex heapsafe.tex

heapsafe.tex: heapsafe.txt
	rst2latex$(EXE) --documentoptions=10pt,letter --use-latex-footnotes --section-numbering heapsafe.txt | sed -f heapsafe.sed > heapsafe.tex

heapsafe.html: heapsafe.txt
	rst2html$(EXE) heapsafe.txt heapsafe.html
