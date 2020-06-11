svg := $(wildcard *.svg)
png := $(patsubst %.svg,png/%.png,$(svg))

png/%.png: %.svg Makefile
	inkscape --export-area-drawing --export-dpi=300 --export-png=$@ $<

default: $(png);
