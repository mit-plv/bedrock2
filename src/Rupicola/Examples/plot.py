#!/usr/bin/python3

import pandas, seaborn, matplotlib.pyplot
import latest_benchmark_results

df = pandas.DataFrame(latest_benchmark_results.data).explode(2)
df.columns=['language', 'benchmark', 'cycles']
seaborn.catplot(kind='boxen', data=df, x='language', col='benchmark', y='cycles', sharey=False, linewidth=0, palette='colorblind').set(ylim=(0, None))
matplotlib.pyplot.show()
