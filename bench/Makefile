root := $(PWD)

# Make sure to run this in the right OPAM environment

# Needs Coq 8.10.2 for compatibility with Software Foundations
alectryon = $(shell realpath ../../../alectryon.py)
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
lf_htmls := $(lf_vs:.v=.html)

lf/%.html: lf/%.v
	$(alectryon) --frontend coqdoc -Q lf LF $< -o $@

lf-all: $(lf_htmls)

lf-clean:
	rm -f $(lf_htmls)

########
# Frap #
########

frap_rsts = $(wildcard frap/*.rst)
frap_htmls = $(frap_rsts:.rst=.html)
frap_vs = $(frap_rsts:.rst=.v)

frap/%.html: frap/%.rst
	$(alectryon) --frontend rst $< -o $@

frap/%.v: frap/%.rst
	$(alectryon) --frontend rst --backend coq+rst $< -o $@

frap-all: $(frap_htmls) $(frap_vs)

frap-clean:
	rm -f $(frap_htmls) $(frap_vs)

##########
# Common #
##########

compiler := ./compile.sh
coq_rsync := rsync -av  --delete-during --include="*.vo" --include="*.v" --exclude="*.*"

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

stdlib/: Makefile
	$(coq_rsync) "$(coqlib)/theories/" stdlib/theories/
	$(coq_rsync) "$(coqlib)/plugins/" stdlib/plugins/

stdlib_find := find stdlib/ -not -path 'stdlib/theories/Init/*' -name '*.v'

stdlib/full.%.timings:
	 $(stdlib_find) -exec $(compiler) $* 1 {} \; | tee $@

join-paths = \( -false $(patsubst %,-or -path 'stdlib/theories/%', $1) \)

stdlib_files := Arith/Le.v FSets/FSetDecide.v FSets/FSetProperties.v Logic/ClassicalChoice.v Numbers/DecimalNat.v Numbers/NatInt/NZMul.v Program/Tactics.v ZArith/Zgcd_alt.v
stdlib/stdlib.%.timings:
	 $(stdlib_find) $(call join-paths,$(stdlib_files)) -exec $(compiler) $* 5 {} \; | tee $@

breakdown_files := Strings/Byte.v Lists/ListSet.v Reals/Ranalysis3.v
stdlib/breakdown.%.timings:
	 $(stdlib_find) $(call join-paths,$(breakdown_files)) -exec $(compiler) $* 5 {} \; | tee $@

compilers := coqc coqtop sertop alectryon-api alectryon-json alectryon-coqdoc alectryon-html
breakdowns := $(patsubst %,stdlib/breakdown.%.timings,$(compilers))

breakdown: $(breakdowns);

.PHONY: breakdown

#######
# All #
#######

timings: breakdown stdlib/stdlib.alectryon.timings stdlib/stdlib.coqc.timings stdlib/full.alectryon-coqdoc.timings stdlib/full.coqc.timings $(flocq)/full.coqc.timings $(flocq)/full.alectryon-coqdoc.timings

all: stdlib

clean:
	rm -rf $(lf_htmls) stdlib/theories stdlib/plugins stdlib/*.timings $(flocq)/*.timings

.PHONY: timings stdlib all
