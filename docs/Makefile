MAIN := smt-model-definitions
PDF := $(MAIN).pdf
TEX := $(MAIN).tex
LATEX := pdflatex
LATEXFLAGS := -interaction=nonstopmode -halt-on-error

.PHONY: all pdf clean distclean

all: pdf

pdf: $(PDF)

$(PDF): $(TEX)
	$(LATEX) $(LATEXFLAGS) $(TEX)

clean:
	rm -f $(MAIN).aux $(MAIN).log $(MAIN).out $(MAIN).toc \
	      $(MAIN).fls $(MAIN).fdb_latexmk $(MAIN).synctex.gz

distclean: clean
	rm -f $(PDF)
