#!/usr/bin/python3

import pandas, seaborn, matplotlib.pyplot
import latest_benchmark_results

BENCHMARK_ALIASES = [
    ('crc32', 'crc32'),
    ('utf8_decode', 'utf8'),
    ('murmur3', 'm3s'),
    ('upstr', 'upstr'),
    ('ip_checksum', 'ip'),
    ('revcomp', 'fasta'),
    ('fnv1a64', 'fnv1a'),
]

COMPILER_ALIASES = [
    ("gcc-9.4.0", "GCC 9.4"),
    ("gcc-10.3.0", "GCC 10.3"),
    ("gcc-11.1.0", "GCC 11.1"),
    # ("clang-10.0.0", "Clang 10.0"),
    ("clang-11.0.0", "Clang 11.0"),
    ("clang-12.0.0", "Clang 12.0"),
    ("clang-13.0.1", "Clang 13.0"),
]

LANGUAGE_ALIASES = [
    ("rupicola", "Rupicola"),
    ("c",        "C"),
]

def main():
    df = pandas.DataFrame(latest_benchmark_results.data).explode(3)
    df[3] = df[3].apply(lambda x: x/1024/1024)
    df.columns=['benchmark', 'language', 'compiler', 'cycles/byte']

    df['benchmark'].replace(*zip(*BENCHMARK_ALIASES), inplace=True)
    df['compiler'].replace(*zip(*COMPILER_ALIASES), inplace=True)
    df['language'].replace(*zip(*LANGUAGE_ALIASES), inplace=True)

    df['bench'] = df['language'] + "/" + df['benchmark']
    df['comp']  = df['language'] + " " + df['compiler']

    COMPILERS = [k for _, k in COMPILER_ALIASES]
    LANGUAGES = [k for _, k in LANGUAGE_ALIASES]
    KEYS = [(c, l) for l in LANGUAGES for c in COMPILERS]
    COMPS = [l + " " + c for (c, l) in KEYS]

    colors = [["#e9b96e", "#c17d11", "#8f5902", "#fcaf3e", "#f57900", "#ce5c00"],
              ["#ad7fa8", "#75507b", "#5c3566", "#729fcf", "#3465a4", "#204a87"]]
    PALETTE = [colors[LANGUAGES.index(l)][COMPILERS.index(c)]
               for (c, l) in KEYS]

    palette = seaborn.color_palette(PALETTE)
    seaborn.set_theme(font="Inconsolata", font_scale=1.5, style='ticks', palette=palette)
    # seaborn.set_context("paper", rc={"font.size":10, "axes.titlesize":10, "axes.labelsize":8})

    # Create an array with the colors you want to use

    width, height = 4.7, 8
    plot = seaborn.catplot(
        data=df,
        kind='bar',
        sharex=True,
        x='cycles/byte', y='benchmark',
        order=[k for _,k in BENCHMARK_ALIASES],
        hue='comp', hue_order=COMPS,
        legend = False,
        linewidth=0,
        height=height, aspect=width/height,
    )
    plot.set(xlim=(0, None))
    plot.set_axis_labels("Cycles per byte on 1MiB input (lower is better)", "")
    plot.add_legend(title="", label_order=COMPS, labelspacing=0.2, loc='center right')
    plot.set_titles("") #"{row_name}")

    plot.figure.tight_layout()
    plot.figure.savefig("plot.pdf")
    # matplotlib.pyplot.tight_layout()
    # matplotlib.pyplot.show()

if __name__ == '__main__':
    main()
