root := $(PWD)

# Make sure to run this in the right OPAM environment

# Needs Coq 8.10.2 for compatibility with Software Foundations
alectryon = $(shell realpath $(shell which alectryon))
export ALECTRYON:=$(alectryon)

##########
# Refman #
##########

# PYTHONPATH=$(realpath ~/documents/mit/plv/blog/alectryon/):$PYTHONPATH make V=1 SPHINXWARNERROR=0 refman-html

refman:
	rsync -az /build/coq/8.10.2/doc/sphinx/_build/html/ refman/

.PHONY: refman

######
# LF #
######

lf_vs := $(shell find lf -name '*.v')
lf_vos := $(lf_vs:.v=.vo)
lf_htmls := $(lf_vs:.v=.html)

lf/.sync:
	+$(MAKE) -C lf $(patsubst lf/%,%,$(lf_vos))
	touch $@

lf/%.html: lf/%.v lf/.sync
	$(alectryon) --frontend coqdoc -Q lf LF $< -o $@

lf-all: $(lf_htmls)

lf-clean:
	rm -f $(lf_htmls)

#########
# Books #
#########

books_rsts = $(wildcard books/*.rst)
books_htmls = $(books_rsts:.rst=.html)
books_vs = $(books_rsts:.rst=.v)

books/%.html: books/%.rst
	$(alectryon) --cache-directory . --frontend rst $< -o $@

books/%.v: books/%.rst
	$(alectryon) --frontend rst --backend coq+rst $< -o $@

books-all: $(books_htmls) $(books_vs)

books-clean:
	rm -f $(books_htmls) $(books_vs)

##########
# Common #
##########

compiler := ./compile.sh
coq_rsync := rsync -a --delete-during --include="*.vo" --include="*.v" --exclude="*.*"

#########
# Flocq #
#########

flocq := flocq-3.3.1

# Save the dependency order into a file so that we don't have to plug into their build system
$(flocq)/: Makefile
	wget https://gforge.inria.fr/frs/download.php/file/38329/$(flocq).tar.gz
	tar -xf $(flocq).tar.gz
	cd $(flocq); ./configure
	cd $(flocq); ./remake -j8 all check check-more 2>&1 | grep Finished | grep -v Pff | tee ../flocq.inputs

flocq_coqargs := -R src Flocq -R examples FlocqEx

$(flocq)/full.%.timings:
	cd $(flocq); cat ../flocq.inputs | COQC_ARGS="$(flocq_coqargs)" xargs -n1 ../$(compiler) $* 1 | tee ../$@

.PHONY: $(flocq)

##########
# Stdlib #
##########

coqlib := $(shell opam config var coq:lib)

stdlib/%/.sync: Makefile
	$(coq_rsync) "$(coqlib)/$*/" stdlib/$*/
	touch $@

stdlib: stdlib/plugins/.sync stdlib/theories/.sync

STDLIB_REPEAT ?= 5

stdlib_excluded := \
	-not -path stdlib/theories/Numbers/Cyclic/Int63/Int63.v \
	-not -path stdlib/theories/Classes/Morphisms.v \
	-not -path stdlib/theories/Classes/CEquivalence.v \
	-not -path stdlib/theories/Classes/CMorphisms.v \
	-not -path stdlib/theories/Classes/Morphisms_Prop.v \
	-not -path stdlib/theories/Logic/StrictProp.v

stdlib_find := find stdlib/ -not -path 'stdlib/theories/Init/*' $(stdlib_excluded) -name '*.v'

stdlib/full.%.timings: stdlib
	 $(stdlib_find) -exec $(compiler) $* 1 {} \; | tee $@

join-paths = \( -false $(patsubst %,-or -path 'stdlib/theories/%', $1) \)

stdlib_files := Arith/Le.v FSets/FSetDecide.v FSets/FSetProperties.v Logic/ClassicalChoice.v Numbers/DecimalNat.v Numbers/NatInt/NZMul.v Program/Tactics.v ZArith/Zgcd_alt.v
stdlib/stdlib.%.timings: stdlib
	 $(stdlib_find) $(call join-paths,$(stdlib_files)) -exec $(compiler) $*  $(STDLIB_REPEAT) {} \; | tee $@

breakdown_files := Strings/Byte.v Lists/ListSet.v Reals/Ranalysis3.v
stdlib/breakdown.%.timings: stdlib
	 $(stdlib_find) $(call join-paths,$(breakdown_files)) -exec $(compiler) $* $(STDLIB_REPEAT) {} \; | tee $@

compilers := coqc coqtop sertop alectryon-api alectryon-json alectryon-coqdoc alectryon-html
breakdowns := $(patsubst %,stdlib/breakdown.%.timings,$(compilers))

breakdown: $(breakdowns);

.PHONY: breakdown

#######
# All #
#######

# $(flocq)/full.alectryon-coqdoc.timings $(flocq)/full.coqc.timings
timings: breakdown stdlib/stdlib.alectryon.timings stdlib/stdlib.coqc.timings stdlib/full.alectryon-coqdoc.timings stdlib/full.coqc.timings

clean:
	find stdlib/theories -name '*.html' -not -name index.html -delete
	rm -rf $(lf_htmls) stdlib/plugins stdlib/*.timings $(flocq)/*.timings

.PHONY: timings
