alectryon := ./driver.py --copy-assets none
export PYTHONPATH=$(shell realpath ../../):$$PYTHONPATH

# 3.3in obtained with \usepackage{printlen} and \uselengthunit{in}\printlength\linewidth
# html2pdf := wkhtmltopdf --margin-bottom 0 --margin-top 0 --margin-left 0 --margin-right 0 --page-width 3.2in --page-height 15in
# ~96 pixels per inch → 320px
# html2img := wkhtmltoimage --width 320 --disable-smart-width

vfiles := $(wildcard snippets/*.v)
rstfiles := $(wildcard snippets/*.rst)
inputs := $(vfiles:.v=) $(rstfiles:.rst=)
pdfs := $(inputs:=.pdf)
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

snippets/%.html: snippets/%.v
	$(alectryon) $< -o $@

snippets/%.html: snippets/%.rst
	$(alectryon) $< -o $@

snippets/%.rst.coq: snippets/%.rst
	$(alectryon) $< --backend coq+rst -o $@

snippets/%.svg: snippets/%.html
	$(html2img) $< $@

snippets/%.pdf: snippets/%.html snippets/%.screenshot.js snippets/screenshot-lib.js snippets/docutils_basic.css pdfcrop Makefile
	./snippets/$*.screenshot.js $< $@
	./pdfcrop $@ $@

snippets/%.pdf: snippets/%.html snippets/screenshot.js snippets/screenshot-lib.js snippets/docutils_basic.css pdfcrop Makefile
	./snippets/screenshot.js $< $@
	./pdfcrop $@ $@

index.html: index.rst Makefile
	./driver.py $< -o $@

snippets/emacs.pdf: snippets/emacs.svg
	svgo $<
	svg2pdf $< $@

update-css:
	find . -name alectryon.css -exec echo cp alectryon_with_webfont.css {} \;

clean:
	echo $(objs)
	rm -f $(objs) api.py.out
