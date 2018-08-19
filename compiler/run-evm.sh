# This is for only showing the whole log string
evm --codefile ../examples/evm-bytecode.tmp --gas 1000000000 --statdump --debug --nomemory --nostack run 2>&1 | perl -lne '/\|(.)\|/ && print $1' | paste -sd "" - | perl -lpe 's/\./\n/g'

# This is for showing the whole log
# evm --codefile ../examples/evm-bytecode.tmp --gas 1000000000 --statdump --debug --nomemory --nostack run 2>&1 | perl -lne '/(^[0-9a-fA-F]{8} .*\|.*|^Gas used\:.*)/ && print $1'
