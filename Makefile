alectryon_args := --copy-assets none --traceback
alectryon := ./driver.py $(alectryon_args)
export PYTHONPATH=$(shell dirname $(shell realpath $(shell which alectryon))):$$PYTHONPATH

vfiles := $(wildcard snippets/*.v)
rstfiles := $(wildcard snippets/*.rst)
inputs := $(vfiles:.v=) $(rstfiles:.rst=)
pdfs := $(inputs:=.pdf) snippets/Qle-pairwise.unfolded.nofonts.pdf snippets/nsum-gauss.unfolded.nofonts.pdf
htmls := $(inputs:=.html)
literatevs := $(rstfiles:=.coq)
apis := snippets/api.pp snippets/api.json
outputs := $(apis) $(htmls) $(pdfs) $(literatevs)
objs := $(inputs:=.svg) $(outputs)

all: $(outputs)

list:
	@echo $(vfiles) $(rstfiles)

snippets/ap%.pp snippets/ap%.json: snippets/ap%.py
	cd snippets/; python3 api.py; ./api.json.js

snippets/%.coqdoc.html: snippets/%.coqdoc.v
	$(alectryon) --frontend coqdoc $< -o $@

snippets/%.plain.html: snippets/%.plain.v
	$(alectryon) --frontend coq $< -o $@

snippets/%.html: snippets/%.v snippets/%.driver.py
	snippets/$*.driver.py $(alectryon_args) $< -o $@

snippets/%.html: snippets/%.v
	$(alectryon) $< -o $@

snippets/%.html: snippets/%.rst
	$(alectryon) $< -o $@

snippets/%.rst.coq: snippets/%.rst
	$(alectryon) $< --backend coq+rst -o $@

snippets/%.svg: snippets/%.html
	$(html2img) $< $@

snippets/%.pdf: snippets/%.html snippets/%.screenshot.js snippets/screenshot-lib.js snippets/screenshot.css snippets/docutils_basic.css pdfcrop Makefile
	./snippets/$*.screenshot.js $< $@
	./pdfcrop $@ $@

snippets/%.pdf: snippets/%.html snippets/screenshot.js snippets/screenshot-lib.js snippets/docutils_basic.css pdfcrop Makefile
	./snippets/screenshot.js $< $@
	./pdfcrop $@ $@

snippets/%.nofonts.pdf: snippets/%.pdf
	 gs -o $@ -dNoOutputFonts -sDEVICE=pdfwrite $<

index.html: index.rst Makefile
	./driver.py --no-header $< -o $@

snippets/emacs-screenshot.pdf: snippets/emacs-screenshot.svg
	svg2pdf $< $@

gen_html_indices:
	find . -type d \
		-not -path '*/_*' \
		-not -path '*/.*' \
		-not -path '.' \
		-not -path './bench/lf*' \
		-not -path './bench/refman*' \
		-exec ./trees.sh {} \;

serve:
	python3 -m http.server

clean:
	rm -f $(objs) api.py.out
