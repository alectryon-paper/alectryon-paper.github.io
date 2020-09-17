Alectryon: SLE 2020 AEC
=======================

Introduction
------------

Thanks for reviewing this artifact! We hope that you'll find it easy to
use and evaluate.  A copy of the submitted paper is in the current
folder, under the name ‘alectryon.pdf’ (‘~/alectryon-sle2020/alectryon.pdf’).

This VM packages Alectryon and all scripts and data that we used to evaluate it.
If you want to run Alectryon on your own machine instead, you can follow the
publicly available-instructions at https://github.com/cpitclaudel/alectryon .

The set up of this virtual machine was done using the scripts in the “vm”
directory of the Alectryon repository; the entire configuration can be
replicated using the `provision.sh` script at

    https://github.com/cpitclaudel/alectryon/tree/sle2020/etc/vm

### Contents of this artifact

This artifact is made of two parts:

1. First, a walk through simple examples, following the tutorial presented in
   the paper.  We encourage reviewers to experiment with their own Coq programs,
   too.

2. Then, a set of scripts, intended to replicate our experimental results.

Getting started: a simple walkthrough (§2)
------------------------------------------

The following assumes that you have read through the Introduction and
Tutorial sections of the paper.

To begin, open a terminal and navigate to `~/alectryon-sle2020/ae/`: ``cd ~/alectryon-sle2020/ae/``

This directory contains all examples used in the tutorial (in the
`snippets/` directory) as well as all larger examples that the paper
links to (in the `bench/` directory).

### Recording proofs (pages 3 and 4 of the paper)

Use ``alectryon snippets/folded.v`` to generate `snippets/folded.html`.

Open `snippets/folded.html` in Firefox to observe the generated webpage.  You
can hover any statement showing a small bubble, and click statements to reveal
the corresponding goal.

The webpage has a header describing how to step through the proof with the
keyboard.  You can also toggle between various display styles using the links at
the top, including an IDE style that reproduces the usual two-window interface
for Coq.

Other examples are provided in `snippets/ide.v` and `snippets/classical.v`.  You
can build the corresponding HTML pages using ``alectryon snippets/ide.v`` and
``alectryon snippets/classical.v``.  Notice how `snippets/classical.v` uses
special annotations to determine what should be visible by default (such as `(*
.messages .unfold *)`), as described at the beginning of page 4.

### Compiling reST documents (page 4)

Use ``alectryon snippets/doc.rst`` to generate `snippets/doc.html`.
reStructuredText parts are rendered by Docutils and Coq parts are rendered by
Alectryon.

### Compiling literate Coq files (page 4)

Use ``alectryon snippets/doc.v`` to regenerate `snippets/doc.html`, this time
from a literate `.v` file.  A custom reader translates the Coq document to reST,
which is then fed to Docutils.

### Toggling between woven and tangled views (pages 4 and 5)

* On the command line

  Use ``alectryon snippets/doc.rst -o snippets/doc.rst.v`` to tangle `doc.rst`
  into a Coq file, `doc.rst.v`.  Use ``alectryon snippets/doc.v -o
  snippets/doc.v.rst`` to weave `doc.v` into a reStructuredText file,
  `doc.v.rst`.

* Using Emacs (Appendix A)

  We have installed Emacs with `alectryon.el` and Proof General pre-configured
  in this VM.  Open `doc.v` in Emacs and press <kbd>C-c C-S-a</kbd> to switch
  between to a reStructuredText view.  Make changes to the document and press
  `C-c C-S-a` to switch back.  Notice how your changes are reflected in the
  original Coq file.

  Note: You can also try introducing reStructuredText errors in the `(*| … |*)`
  comments of the Coq file: notice how errors are reported within these
  comments. If you want to explore how the side by side screenshot of Appendix A
  was made, you can read through the Emacs script used to generate it; it is
  distributed in `~/alectryon-sle2020/src/etc/elisp/screenshot/`

### Recording JSON movie files (page 5)

Use ``alectryon --frontend coq --backend json snippets/api.v`` to generate
`snippets/alectryon.io.json`.  The paper uses a compact representation to save
space: the generated JSON file contains more information (the more compact JSON
representation can be generated using the `minimal_json_of_annotated` function
found in `~/alectryon-sle2020/src/alectryon/json.py`, but in practice the
complete JSON representation is the useful one, since it can easily be read
back).

### Using the Coqdoc compatibility mode (page 5)

Use ``alectryon --frontend coqdoc snippets/functions.coqdoc.v`` to convert a
Coqdoc document to HTML using Alectryon.  Comments are passed to Coqdoc, and
other parts are processed using Alectryon.

### Using custom filters (appendix B)

Use ``alectryon snippets/Qle-pairwise.unfolded.rst`` to generate
`snippets/Qle-pairwise.unfolded.html`.

Use ``alectryon snippets/nsum-gauss.rst`` and `snippets/nsum-gauss.html`.

Both of these files use MathJax to provide better math rendering.  This is
achieve using custom Coq notations and a bit of JavaScript, which is imported in
from `snippets/latex.rst`.

Experimental results (§4)
-------------------------

This section reproduces our performance results.

One word of caution: performance measurements are well-known to be
finicky.  The following factors can affect measurements by introducing
noise that blurs the results:

* Power saving (on laptops)
* Dynamic frequency scaling (most commonly on laptops)
* Caching issues (on all types of computers, especially when running
  tests)

Additionally, results collected inside a VM tend to be more noisy.
Still, our benchmarks should be relatively straightforward to reproduce.

To begin, open a terminal and navigate to `~/alectryon-sle2020/ae/bench/`:
``cd ~/alectryon-sle2020/ae/bench/``.

All build and benchmarking commands are gathered in a `Makefile`.

Run ``make clean`` to remove existing timings.

Run ``make STDLIB_REPEAT=1 timings`` to gather all the data required by the
plots.  This will take in the order of an hour, and generate three sets of
`.timing` files.  Each of these files contains data in the following format:

    <compiler-name>	<file>	real: <time>	user: <time>	sys: <time>	<exit-code>

These records are created by running each compiler and measuring its execution
time and printed as they are collected.  These files are then used by the
`plot.py` script to generate diagrams.  Run ``./plot.py`` to generate the plots.

It produces output similar to the following:

    Skipping …
    Stdlib:
    # Ratios:
    Median: Arith/Lt.v: 0.571s/0.189s = 3.02
    90th percentile: Sets/Relations_2_facts.v: 0.733s/0.106s = 6.92
    95th percentile: Reals/PartSum.v: 8.920s/0.766s = 11.64
    Range: Strings/Byte.v (1.2005516154452325) → Reals/Ranalysis3.v (110.12984054669704)
    # Total runtimes:
    coqc 0:05:37.347000
    alectryon-coqdoc 0:30:45.913000
    # Total slowdown: 1845.913s/337.347s = 5.47
    # File count: 482

These were the original numbers at paper submission time; they are
included in the alectryon-paper repository (Lines starting with
'Skipping …' indicate that compilation failed for a given file; this can
happen if SerAPI fails to compile a file.)

Alectryon's performance has improved slightly since submission, and
these values will fluctuate somewhat in any case; for example, running
inside a VM, you might observe something along these lines:

    Stdlib:
    # Ratios:
    Median: stdlib/plugins/rtauto/Bintree.v: 1.250s/0.439s = 2.85
    90th percentile: Numbers/NatInt/NZOrder.v: 3.049s/0.550s = 5.54
    95th percentile: Reals/Rcomplete.v: 8.649s/0.956s = 9.05
    Range: QArith/QArith.v (0.9657794676806083) → Reals/Ranalysis3.v (92.91219512195123)
    # Total runtimes:
    coqc 0:07:04.583000
    alectryon-coqdoc 0:31:22.197000
    # Total slowdown: 1882.197s/424.583s = 4.43
    # File count: 482

If you would like to get the most accurate result, run with a larger
value of `STDLIB_REPEAT`: this will repeat each measurement multiple
times to smooth out the noise, and plot.py will be able to compute
confidence intervals.

### Compilation times: coqc vs Alectryon (Figure 1)

This figure uses detailed measurements focusing on two compilers, for a
randomly-chosen subset of the standard library:

    stdlib/stdlib.alectryon.timings
    stdlib/stdlib.coqc.timings

`plot.py` places it in `stdlib/stdlib.pdf`.

### Compilation times: cumulative overheads (Figure 2)

This figure uses coarse measurements for almost all files in the standard
library:

    stdlib/full.alectryon-coqdoc.timings
    stdlib/full.coqc.timings

`plot.py` places it in `stdlib/ratios.pdf`.

### Compilation times: breakdowns (Figure 3)

This figure Detailed measurements with various compilations strategies, for 3
representative files:

      stdlib/breakdown.alectryon-api.timings
      stdlib/breakdown.alectryon-coqdoc.timings
      stdlib/breakdown.alectryon-html.timings
      stdlib/breakdown.alectryon-json.timings
      stdlib/breakdown.coqc.timings
      stdlib/breakdown.coqtop.timings
      stdlib/breakdown.sertop.timings

`plot.py` places it in `stdlib/measurements.pdf`.

Optional: Further exploration
-----------------------------

### Trying Alectryon on your own examples

For more examples, we recommend having a look at Alectryon's
[README](https://github.com/cpitclaudel/alectryon).  The
[recipes](https://github.com/cpitclaudel/alectryon/tree/sle2020/recipes)
directory is a good place to start.

For help with Alectryon's command-line interface, use `alectryon --help`.

### Applying Alectryon to larger projects

To generate webpages for all files in a project using Alectryon, the
best way to proceed is usually to compile the complete project using
coq_makefile or Dune, and then to run Alectryon on all files of that
project (the initial compilation allows Alectryon to load dependencies).
This is how we generate HTML for *Logical Foundations*, *CPDT*,
etc. (you can see examples in the `Makefile` of the `web/` directory).

To apply Alectryon to the reference manual, we patched the existing
coqrst scripts to call Alectryon instead; the code is at
https://github.com/cpitclaudel/coq/tree/alectryon (a branch based on Coq
8.10.2).

To apply Alectryon to book passages, use the `make book-clean` and `make
book-all` targets of the `Makefile` in the `bench/` directory.

### Real-world examples

Lastly, you may be interested in a real-life example of Alectryon in the wild:
the [PLV blog at MIT](https://plv.csail.mit.edu/blog/).  The annotated Coq
sources are [on Github](https://github.com/mit-plv/blog/tree/master/content).

Conclusion
----------

Thanks again for evaluating this artifact! We hope that these
instructions were useful in exploring and evaluating our work.

(Use ‘grep --only-matching --extended-regexp '``.*?``' README.md’ to
list all commands contained in this file)
