#!/usr/bin/python3

import pandas, seaborn, matplotlib.pyplot
import latest_benchmark_results

df = pandas.DataFrame(latest_benchmark_results.data).explode(3)
df[3] = df[3].apply(lambda x: x/1024/1024)
df.columns=['benchmark', 'language', 'compiler', 'cycles/byte']
seaborn.catplot(kind='boxen', data=df, col='benchmark', x='language', hue='compiler', y='cycles/byte', sharey=False, linewidth=0, palette='colorblind').set(ylim=(0, None)).set_axis_labels("", "Haswell cycles/byte on 1MiB input").set_titles("{col_name}")
matplotlib.pyplot.show()
