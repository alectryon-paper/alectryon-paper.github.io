Installation instructions
=========================

Prerequisites
-------------

You will need the [Coq proof assistant](https://coq.inria.fr/) (>= 8.7)
with the `Reals` theory compiled in.

The `.tar.gz` file is distributed with a working set of configure files. They
are not in the git repository though. Consequently, if you are building from
git, you will need `autoconf` (>= 2.59).


Configuring, compiling and installing
-------------------------------------

Ideally, you should just have to type:

    ./configure && ./remake --jobs=2 && ./remake install

The environment variable `COQC` can be passed to the configure script in order
to set the Coq compiler command. The configure script defaults to `coqc`.
Similarly, `COQDEP` can be used to specify the location of `coqdep`. The
`COQBIN` environment variable can be used to set both variables at once.

The option `--libdir=DIR` can be set to the directory where the compiled
library files should be installed by `./remake install`. By default, the
target directory is `` `$COQC -where`/user-contrib/Flocq ``.

The files are compiled at a logical location starting with `Flocq`.
