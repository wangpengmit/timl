TiML: A Functional Programming Language with Time Complexity
===========================================

Setup Instructions
-----------------------

1. Install SML/NJ. Make sure command `sml` and `ml-build` is in current PATH.
   On Ubuntu, use this command to install all necessary components of SML/NJ:
       
   ```
   sudo apt-get install smlnj libsmlnj-smlnj ml-yacc ml-ulex
   ```

2. Install the Z3 SMT solver version 4.4.1. Make sure command `z3` is in current PATH. Z3-4.4.1 is required. Z3-4.4.2 has a known issue.

3. Install Ruby. Make sure command `ruby` is in current PATH.

4. Use `make` to build TiML.

5. (Optional). Install MLton (a whole-program optimizing SML compiler). Make sure command `mlton`, `mlyacc` and `mllex` is in current PATH. Use `make mlton` to build TiML with MLton.

6. (Optional). Follow [emacs/README.rst](emacs/README.rst) to install TiML mode on Emacs.

