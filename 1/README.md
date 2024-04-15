```haskell
cabal install tasty
cabal install --lib tasty
cabal install --lib tasty-hunit
cabal install --lib tasty-smallcheck
cabal install --lib tasty-quickcheck
cabal install --lib transformers

runhaskell Tests.hs
```