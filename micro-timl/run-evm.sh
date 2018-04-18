evm --codefile ../examples/evm-bytecode.tmp --gas 1000000000 --debug --nomemory --nostack run 2>&1 | perl -lne '/\|(.)\|/ && print $1' | paste -sd "" - | perl -lpe 's/\./\n/g'
