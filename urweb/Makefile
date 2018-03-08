CFLAGS := -I/usr/include/urweb
CXXFLAGS := -I/usr/include/urweb

all: timl.exe

timl.exe: timl.urp timl.urs timl.ur cmodule.h cmodule.o examples.html \
			../examples/basic.timl  \
			../examples/list.timl  \
			../examples/nat.timl  \
			../examples/array.timl  \
			../examples/ragged-matrix.timl  \
			../examples/tree.timl  \
			../examples/msort.timl  \
			../examples/insertion-sort.timl  \
			../examples/braun-tree.timl  \
			../examples/rbt.timl  \
			../examples/dynamic-table.timl  \
			../examples/functional-queue.timl  \
			../examples/array-bsearch.timl  \
			../examples/array-heap.timl  \
			../examples/array-msort.timl  \
			../examples/array-msort-inplace.timl  \
			../examples/array-kmed.timl  \
			../examples/dlist.timl  \
			../examples/qsort.timl  \
			../examples/dijkstra.timl  \
			../examples/perversive-list.timl  \
			../examples/braun-tree-sortedness.timl  \
			../examples/rbt-sortedness.timl  \

	urweb timl
