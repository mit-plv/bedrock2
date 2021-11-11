fnv1a.run: fnv1a64.cpp
	g++ -O3 $< -pthread -lbenchmark -std=c++11 -o fnv1a.exe
	./fnv1a.exe --benchmark_report_aggregates_only=true --benchmark_repetitions=10 --benchmark_format=json

fnv1a.opt:
	dune build --profile release
	dune exec ./driver.exe -- -ci-absolute

fnv1a-java:
	java fnv1a.java
