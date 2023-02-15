# Proof mode evaluation

This folder contains a number of example theorems proved using the proof mode or the Hilbert-system. To evaluate proof sizes, the extracted Haskell code needs to be executed (see `evaluator.hs` in the main directory). For the Haskell compilation, the following imports need to be added into the generated `Test.hs` (due to a bug in the Haskell extraction process of Coq):

```
import qualified Data.Bits
import qualified Data.Char
```

To check proof sizes, compile `evaluator.hs` in the main directory, with the option `-XNoPolyKinds`. The individual functions in that file refer to the different proof sizes for the proofs in this directory.
