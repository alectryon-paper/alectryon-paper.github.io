#!/usr/bin/env python3
# Invoke with (cd ..; ./stdlib/plot_stdlib.py)

import re
import random
import math
from os import path
from datetime import timedelta

import numpy as np
import scipy.stats as st
import matplotlib
matplotlib.use('Agg')
from matplotlib import pyplot as plt, patches, ticker

LINE_RE = re.compile(
    "^"
    "(?P<compiler>.*?)\t"
    "(stdlib/theories/)?(?P<fname>.*?)\t"
    "real: (?P<real>.*?)\t"
    "user: (?P<user>.*?)\t"
    "sys: (?P<sys>.*?)\t"
    "(?P<err>.*?)"
    "$")

TYPES = {
    "compiler": str,
    "fname": str,
    "real": float,
    "user": float,
    "sys": float,
    "err": int,
}

def read(fpath):
    with open(fpath) as s:
        for line in s:
            m = LINE_RE.match(line)
            if m:
                r = { k: cast(m.group(k)) for k, cast in TYPES.items() }
                if r["err"] != 0:
                    print(f"Skipping {r['compiler']} @ {r['fname']}")
                else:
                    yield r

def group_by_fname(measurements):
    grouped = {}
    for r in measurements:
        grouped.setdefault(r["fname"], []).append(r["real"])
    return grouped

# https://www.statology.org/confidence-intervals-python/
# https://stackoverflow.com/questions/15033511/compute-a-confidence-interval-from-sample-data
class Summary:
    def __init__(self, values):
        self.values = np.array(list(values))
        self.mean = np.mean(self.values)
        if len(self.values) > 1:
            self.sem = st.sem(self.values)
            self.ci95 = st.t.interval(alpha=0.95, df=len(self.values)-1, loc=self.mean, scale=self.sem)
            self.ci95delta = (self.mean - self.ci95[0], self.ci95[1] - self.mean)
        else:
            self.sem = self.ci95 = np.NaN
            self.ci95delta = (np.NaN, np.NaN)

    def __repr__(self):
        return repr(vars(self))

def summarize(by_fname):
    return { fname: Summary(rs)
        for fname, rs in by_fname.items() }

HEX = {"yellow": ("#fce94f", "#edd400", "#c4a000"),
       "orange": ("#fcaf3e", "#f57900", "#ce5c00"),
       "brown":  ("#e9b96e", "#c17d11", "#8f5902"),
       "green":  ("#8ae234", "#73d216", "#4e9a06"),
       "blue":   ("#729fcf", "#3465a4", "#204a87"),
       "purple": ("#ad7fa8", "#75507b", "#5c3566"),
       "red":    ("#ef2929", "#cc0000", "#a40000"),
       "grey":   ("#eeeeec", "#d3d7cf", "#babdb6"),
       "black":  ("#888a85", "#555753", "#2e3436")}

COMPILERS = {
    "coqtop":
    ("coqtop", "yellow"),
    "coqc":
    ("coqc", "orange"),
    "sertop":
    ("sertop", "brown"),
    "alectryon":
    ("alectryon", "purple"),
    "alectryon-api":
    ("alectryon-api", "blue"),
    "alectryon-json":
    ("alectryon-json", "green"),
    "alectryon-html":
    ("alectryon-html", "purple"),
    "alectryon-coqdoc":
    ("alectryon-coqdoc", "red")
}

def all_files(summaries_by_compiler):
    keys = [set(d.keys()) for d in summaries_by_compiler.values()]
    return set.intersection(*keys) if keys else {}

SEED = 42
RNG = random.Random(SEED)

def rcParams(fontsize=10, **extra):
    matplotlib.rcParams.update({
        "font.size": fontsize,
        "font.family": "serif",
        "font.serif": "Iosevka",
        "font.weight": 400,
        "axes.titlesize": "small",
        "axes.labelsize": "small",
        "axes.titleweight": 400,
        "axes.labelweight": 400,
        "xtick.labelsize": "small",
        "ytick.labelsize": "small",
        "legend.fontsize": "small",
        "legend.labelspacing": 0,
        "text.usetex": False,
        "figure.titleweight": 400,
        "savefig.bbox": "tight",
        "savefig.pad_inches": 0.05
    })

    matplotlib.rcParams.update(**extra)

def to_inches(points):
    return points / 72.26999

def random_files(summaries_by_compiler, nfiles):
    files = all_files(summaries_by_compiler)
    coqc = summaries_by_compiler["coqc"]
    threshold = 0.5 * max(s.mean for s in coqc.values())
    not_too_slow = sorted(f for f in files if coqc[f].mean < threshold and len(f) < 24)
    return sorted(RNG.sample(not_too_slow, k=nfiles))

def files_by_ratio(summaries_by_compiler, kslow, kfast):
    files = all_files(summaries_by_compiler)
    fast = summaries_by_compiler.get(kfast)
    slow = summaries_by_compiler.get(kslow)
    if fast is None or slow is None:
        return []
    return slow, fast, sorted(
        (slow[f].mean / fast[f].mean,
         slow[f].mean, fast[f].mean, f)
        for f in files)

# Recorded for reproducibility
STDLIB_FILES = ['Arith/Le.v', 'FSets/FSetDecide.v', 'FSets/FSetProperties.v', 'Logic/ClassicalChoice.v', 'Numbers/DecimalNat.v', 'Numbers/NatInt/NZMul.v', 'Program/Tactics.v', 'ZArith/Zgcd_alt.v']
BREAKDOWN_FILES = ['Strings/Byte.v', 'Lists/ListSet.v', 'Reals/Ranalysis3.v']

def truncate(fnames, max):
    for f in fnames:
        f = path.splitext(f)[0]
        prefix = ""
        while len(f) > max and '/' in f:
            prefix = "…/"
            f = f.split('/', 1)[1]
        yield prefix + f

def plot1(summaries_by_compiler, files, ax):
    y = np.arange(len(files))[::-1]
    nbars = len(summaries_by_compiler)
    height = 0.75 / nbars
    legend_patches = []

    delta = - nbars / 2
    for compiler, by_file in summaries_by_compiler.items():
        points = [by_file[f] for f in files]
        x, ci = zip(*((s.mean, s.ci95delta) for s in points))

        alias, color = COMPILERS[compiler]
        _light, medium, dark = HEX[color]

        ci = np.array(list(ci))
        ax.barh(y - (delta + 0.5) * height, x,
                height=height,
                color=medium,
                xerr=ci.T,
                error_kw={ "ecolor": dark, "lw": 0.5,
                           "capsize": 1, "capthick": 0.5 })
        patch = patches.Patch(facecolor=medium,
                              edgecolor=dark,
                              label=alias)
        legend_patches.append(patch)
        delta += 1

    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    ax.spines['left'].set_visible(False)
    ax.yaxis.set_tick_params(which="both", pad=5, length=0, rotation=0)
    # ax.set_ylabel("File")
    ax.set_yticks(y)
    ax.set_yticklabels(list(truncate(files, 18)), va="center")

    return legend_patches

XLABEL = "Compilation time (seconds, 95% CI)"

def plot_stdlib(summaries_by_compiler, files):
    fig, ax = plt.subplots(1, 1, figsize=(3.2, 1.5))
    legend_patches = plot1(summaries_by_compiler, files, ax)
    ax.set_xlabel(XLABEL)
    ax.legend(handles=legend_patches, loc="upper right")
    fig.tight_layout(pad=0.5)
    return fig

def plot_breakdowns(summaries_by_compiler, files):
    fig, axs = plt.subplots(len(files), 1, figsize=(3.2, 2.5))
    ax, legend_patches = None, None
    for ax, f in zip(axs, files):
        legend_patches = plot1(summaries_by_compiler, [f], ax)
    ax.set_xlabel(XLABEL)
    fig.legend(handles=legend_patches,
               loc="lower center",
               bbox_to_anchor=(0.5, 0),
               ncol=2)
    fig.tight_layout(pad=0.5, rect=(0,0.18,1,1))
    return fig

def plot_overheads(summaries_by_compiler):
    ratios = [r[0] for r in files_by_ratio(summaries_by_compiler, "alectryon-coqdoc", "coqc")[-1]]
    fig, ax = plt.subplots(1, 1, figsize=(3.2, 0.8))
    y = np.arange(0, len(ratios)) / len(ratios)
    # ax.hist(ratios, bins="knuth",
    #         cumulative=True, density=True, histtype='stepfilled',
    #         color=HEX["blue"][1],edgecolor=None)
    light, medium, dark = HEX["blue"]
    plt.step(ratios, y, where='post', marker=None,
             solid_joinstyle="miter", linewidth=0.5, color=medium)
    ax.fill_between(ratios, y, color=light, linewidth=0)
    ax.set_ylabel("Number of files")
    ax.set_xlabel("Slowdown (alectryon-coqdoc / coqc)")
    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    nth95 = ratios[95 * len(ratios) // 100]
    ax.set_xlim((1, nth95))
    ax.set_ylim((0, 1))
    ax.xaxis.set_ticks(np.arange(1, math.ceil(nth95), 1))
    ax.yaxis.set_major_formatter(ticker.PercentFormatter(1.0))
    return fig

def summarize_full(summaries_by_compiler):
    print("# Ratios:")
    slow, fast, ratios = files_by_ratio(summaries_by_compiler, "alectryon-coqdoc", "coqc")
    print("Median:", ratios[int(0.50 * len(ratios))])
    print("90th percentile:", ratios[int(0.90 * len(ratios))])
    print("95th percentile:", ratios[int(0.95 * len(ratios))])
    print("Range:", f"{ratios[0][-1]} ({ratios[0][0]}) → {ratios[-1][-1]} ({ratios[-1][0]})")
    print("# Total runtimes:")
    summ = lambda by_file: sum(s.mean for s in by_file.values())
    for (compiler, by_file) in summaries_by_compiler.items():
        print(compiler, timedelta(seconds=summ(by_file)))
    print("# Total:", summ(slow) / summ(fast))
    print("# Files:", len(ratios))

def read1(d, dir, compiler, kind):
    f = f"{dir}/{kind}.{compiler}.timings"
    if path.exists(f):
        d[compiler] = summarize(group_by_fname(read(f)))

def main():
    rcParams(fontsize=8)
    stdlib, breakdowns, full, flocq = {}, {}, {}, {}
    for compiler in COMPILERS:
        read1(stdlib, "stdlib", compiler, "stdlib")
        read1(breakdowns, "stdlib", compiler, "breakdown")
        read1(full, "stdlib", compiler, "full")
        read1(flocq, "flocq-3.3.1", compiler, "full")
    plot_stdlib(stdlib, STDLIB_FILES).savefig("stdlib/stdlib.pdf")
    plot_breakdowns(breakdowns, BREAKDOWN_FILES).savefig("stdlib/breakdowns.pdf")
    plot_overheads(full).savefig("stdlib/ratios.pdf")
    plot_overheads(flocq).savefig("flocq-3.3.1/flocq-ratios.pdf")
    print("Stdlib:")
    summarize_full(full)
    print("Flocq:")
    summarize_full(flocq)

if __name__ == '__main__':
    main()
