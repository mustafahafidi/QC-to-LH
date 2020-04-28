## Semi-automatic QuickCheck to LiquidHaskell migration

This project aims to facilitate the migration/conversion of QuickCheck properties to LiquidHaskell proofs, by automating the translation process of QuickCheck tests to LiquidHaskell formal proof obligations.

## Roadmap / Timeline :calendar:

### 1) Study automatic translation of GHC properties to Liquidhaskell proofs

- :heavy_check_mark: Find a simple library that uses quickcheck to take into consideration (smaller than xmonad)~~ -> **Data.CircularList**
- :heavy_check_mark: Get familiar with LH to parse the codebase
- :heavy_check_mark: Transform not very deep test properties to formal proofs with LiquidHaskell
- :heavy_check_mark: Find patterns to implement --> light properties like `prop_empty, prop_isEmpty, prop_size, prop_focus` get proved automatically with no additional equational reasoning, and `prop_list, prop_rot` by assumption on some refined types. Added multiple properties with proofs.
- :heavy_check_mark: Do the induction for the properties ignored
- :heavy_check_mark: Apply everything on the examples of quickcheck (github)
- :heavy_check_mark: Make a report/table on the proofs done until now

- [..] Redefine Eq == and rewrite properties, then prove them
- [..] Solve the Heap proofs (try the refined data-type to ease the proofs)

- [..] Add more examples to try the tool on

### 2) Design the tool and implement it

### 3) Write paper/thesis describing the whole work (can happen in parallel to the work)

### 4) Defend thesis (17 July 2020)

## Usage

- To run liquid `stack exec -- liquid -isrc/ src/Main.hs`

- To run liquid continously by watching file changes, run `spy run -n "stack exec -- liquid -isrc/ src/Main.hs" src/`

In `package.json` are provided some other commands that run liquidhaskell with `stack` which you can either copy paste in your terminal, or run using `yarn` or `npm`
