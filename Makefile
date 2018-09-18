.PHONY: Main.main

default: smlnj

all: smlnj mlton

mlton: main

FILES = $(shell ruby generate-file-list.rb Makefile)

main: main.mlb $(FILES)
	mlyacc sexp/sexp.grm
	mllex sexp/sexp.lex
	mlyacc parser/timl.grm
	mllex parser/timl.lex
	mlyacc parser/etiml.grm
	mllex parser/etiml.lex
	time ./format-mlton.rb mlton $(MLTON_FLAGS) -default-ann "'nonexhaustiveMatch error'" -default-ann "'redundantMatch error'" main.mlb

main.mlb: generate-file-list.rb
	ruby generate-file-list.rb mlton > main.mlb

profile:
	mlprof -show-line true -raw true main mlmon.out

smlnj: main.cm $(FILES)
	time ./format.rb ml-build -Ccontrol.poly-eq-warn=false -Ccompiler-mc.error-non-exhaustive-match=true -Ccompiler-mc.error-non-exhaustive-bind=true main.cm Main.main main-image

main.cm: generate-file-list.rb
	./generate-file-list.rb smlnj > main.cm

# unit-test: main.cm $(FILES)
# 	time ./format.rb ml-build -Ccontrol.poly-eq-warn=false -Ccompiler-mc.error-non-exhaustive-match=true -Ccompiler-mc.error-non-exhaustive-bind=true main.cm UnitTestMain.main main-image

unit-test-bin: unit-test.mlb $(FILES)
	time ./format-mlton.rb mlton $(MLTON_FLAGS) -default-ann "'nonexhaustiveMatch error'" -default-ann "'redundantMatch error'" -output unit-test-bin unit-test.mlb

unit-test.mlb: generate-file-list.rb
	ruby generate-file-list.rb mlton unit-test > unit-test.mlb

%.t.sml: %.sml
	cp $< $@
	# cat $< | ruby preprocess.rb > $@
	# sed -i '1i(* Auto-generated. Do not edit! *)' $@
	ex -sc '1i|(* Auto-generated. Do not edit! *)' -cx file

clean:
	find . -type f ! -name '*.exe' | xargs touch
	rm -f main
	rm -f main-image*
	rm -f main.cm
	rm -f main.mlb
	rm -f unit-test.mlb

print-%  : ; @echo $* = $($*)
