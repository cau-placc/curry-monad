# curry-monad

This repository is part of the paper "A Monadic Implementation of Functional Logic Programs" (publication pending).
It contains :
- the tool that was used to generate the monadic code
- the actual "curry-monad"
- the benchmark programs

## GHC-Plugin and Curry-Monad

We used the tool in the sub-repository `curry-ghc-language-plugin` to generate the monadic code.
The tool itself is part of a different publication (still pending), and is not the topic of interest for this publication.
However, it contains the implementation of the curry-monad that we benchmarked in
`curry-ghc-language-plugin/src/Plugin/CurryPlugin/Monad.hs`.
This file contains stuff that is only relevant for the plugin and does not integrate any extensions to the basic curry-monad.
Since these extensions are orthogonal to the performance of the monad, benchmark results are still accurate.

The full implementation of our monad can be found in `src/MemoizedCurry.hs`.
It contains a commented implementation with set functions, unification and other stuff.
Some parts of the implementation were factored out into different files.
Tests and Benchmarks can be found in `src/MemoizedCurryTests.hs` and `src/MemoizedCurryBench.hs`, both of which are uncommented.
The actual Benchmarks were not taken from that file.
They were from previous investigations into this matter.
We just kept them here.

To open an interactive GHC session, just use `stack repl` and optionally provide the path to the file that you want to open.
Editor support with `haskell-language-server` should work.

## Benchmarks

All benchmarked programs can be found in the subdirectory `becnhmarks`.
This directory contains a Makefile that will automatically build the benchmarks from the paper and a few other ones and time their execution with various compilers as well as with our implementation.
To use it, you need the three compilers `pakcs` `kics2` `curry2go` together with the Haskell-Tool `stack` and adapt their executable paths in the Makefile.
If all tools are on your PATH, no changes to the Makefile are neccessary.

Our implementation does not directly use the benchmark programs from this directory, but instead has its own implementations in `curry-ghc-language-plugin/sandbox/src/`.
That directory contains a `Main.hs`, which combines all benchmarks for our implementation into one executable, where the specific benchmark can be selected with a command line option.
The implementation also includes the benchmarks with the determinism optimization.
The optimization was performed manually, but the resulting code is equivalent to what we expect to get in the future.
By adding the suffix `D` to the benchmark command line option of the aforementioned executable, the optimized code will be executed.
