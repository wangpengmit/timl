#!/usr/bin/env ruby

require 'stringio'

def usage
 puts "usage: THIS_SCRIPT [smlnj|mlton|Makefile]"  
end

def wrong_arguments
  puts "wrong arguments"
  usage
  exit 1
end

if ARGV.size != 1 then
  wrong_arguments
end

target = ARGV[0]

if target == "smlnj" then
  target = :smlnj
elsif target == "mlton" then
  target = :mlton
elsif target == "Makefile" then
  target = :Makefile
else
  wrong_arguments
end

captured_stdio = StringIO.new('', 'w')
old_stdout = $stdout
$stdout = captured_stdio

if target == :smlnj then
  
print %{
Group is
      
cont-smlnj.sml
}

elsif target == :mlton then

print %{  
$(SML_LIB)/basis/basis.mlb
$(SML_LIB)/basis/build/sources.mlb
$(SML_LIB)/mlyacc-lib/mlyacc-lib.mlb
$(SML_LIB)/smlnj-lib/Util/smlnj-lib.mlb
$(SML_LIB)/smlnj-lib/PP/pp-lib.mlb
}

end

if target == :mlton || target == :Makefile then
  
print %{
cont-mlton.sml
}

end

print %{
enumerator.sml
util.sml
ord-key-util.sml
list-pair-map.sml
set-util.sml
map-util.sml
unique-map.sml
region.sml
time.sml
operators.sml
parser/ast.sml
sexp/sexp.sml
}

if target == :smlnj || target == :Makefile then

print %{  
sexp/sexp.grm
sexp/sexp.lex
parser/timl.grm
parser/timl.lex
}

elsif target == :mlton then

print %{  
sexp/sexp.grm.sig
sexp/sexp.grm.sml
sexp/sexp.lex.sml
parser/timl.grm.sig
parser/timl.grm.sml
parser/timl.lex.sml
}

end

print %{
sexp/parser.sml
parser/parser.sml
cont-util.sml
module-context.sml
to-string-util.sml
long-id.sml
uvar.sig
base-sorts.sml
bind.sml
visitor-util.sml                                 
unbound.sml
idx.sig
idx-visitor.sml
idx.sml
shift-util.sml
idx-trans.sml
type.sig
type-visitor.sml
type.sml
type-trans.sml
pattern.sml
pattern-visitor.sml                                 
hyp.sml
expr.sig
expr-util.sml
expr-visitor.sml                                 
expr-fn.sml
get-region.sml
base-types.sml
idx-util.sml
type-util.sml
idx-type-expr.sig
idx-type-expr-fn.sml
expr-trans.sml
simp.sml
simp-type.sml
vc.sml
equal.sml
subst.sml
long-id-subst.sml
export.sml
to-string-raw.sml
to-string-nameful.sml
to-string.sml
pp-util.sml
pp-nameful.sml
pretty-print.sml
uvar.sml
uniquefy.sml
expr.sml
underscore-exprs.sml
pervasive.sml
elaborate.sml
name-resolve.sml
package.sml
typecheck-util.sml
normalize.sml
simp-expr.sml
collect-var.sml
collect-uvar.sml
parallel-subst.sml
fresh-uvar.sml
uvar-forget.sml
unify.sml
redundant-exhaust.sml
collect-mod.sml
subst-uvar.sml
update-expr.sml
sortcheck.sml
topo-sort-fn.sml
compiler/evm-costs.sml
compiler/micro-timl-costs.sml
free-evars.sml
live-vars.sml
compiler/pattern-ex.sml
typecheck-main.sml
trivial-solver.sml
derived-trans.sml
unpackage.sml
post-typecheck.sml
typecheck.sml
smt2-printer.sml
smt-solver.sml
long-id-map.sml
bigO-solver.sml
simp-ctx.sml
nouvar-expr.sml
visitor.sml                                 
parse-filename.sml
vc-solver.sml
remove-open.sml
merge-modules.sml
compiler/micro-timl.sml
compiler/micro-timl-visitor.t.sml
compiler/micro-timl-long-id.sml
compiler/micro-timl-visitor2.sml
compiler/micro-timl-util.sml
compiler/micro-timl-pp.sml
compiler/post-process.sml
compiler/export-pp.sml
compiler/micro-timl-util-timl.sml
compiler/timl-to-micro-timl.sml
compiler/eval-constr.sml
compiler/micro-timl-live-vars.sml
compiler/micro-timl-simp.sml
compiler/micro-timl-free-evars.sml
compiler/micro-timl-typecheck.sml
compiler/micro-timl-locally-nameless.sml
compiler/compiler-util.sml
compiler/cps.sml
compiler/anf.sml
compiler/cc.sml
# compiler/pair-alloc.sml
# compiler/tital.sml
# compiler/tital-visitor.sml
# compiler/tital-pp.sml
# compiler/tital-export-pp.sml
# compiler/tital-tc.sml
# compiler/tital-eval.sml
# compiler/code-gen.sml
compiler/evm1.sml
compiler/evm1-visitor.sml
compiler/evm1-pp.sml
compiler/evm1-export-pp.sml
compiler/evm1-pp.sml
compiler/evm1-util.sml
compiler/evm1-tc.sml
compiler/evm1-assemble.sml
compiler/evm1-simp.sml
compiler/to-evm1.sml
unit-test.sml
main.sml
}

if target == :smlnj then

print %{  
$/basis.cm
$/smlnj-lib.cm
$/ml-yacc-lib.cm
$/pp-lib.cm
}

elsif target == :mlton || target == :Makefile then

print %{  
mlton-main.sml
}

end

$stdout = old_stdout
output = captured_stdio.string

output.gsub!(/#.*/, '')

print output
