## Semi-automatic QuickCheck to LiquidHaskell migration

This project aims to facilitate the migration/conversion of QuickCheck properties to LiquidHaskell proofs, by automating the translation process of QuickCheck tests to LiquidHaskell formal proof obligations.

## Roadmap / Timeline :calendar:

- Study automatic translation of GHC properties to Liquidhaskell proofs
- Design the tool and implement it
- Write paper/thesis describing the whole work (can happen in parallel to the work)
- Defend thesis (mid-end of July 2020)

#### Currently Doing :hammer:

- :heavy_check_mark: Find a simple library that uses quickcheck to take into consideration (smaller than xmonad)~~ -> **Data.CircularList**
- :heavy_check_mark: Get familiar with LH to parse the codebase
- :heavy_check_mark: Transform not very deep test properties to formal proofs with LiquidHaskell
- [...] Find patterns to implement --> light properties like `prop_empty, prop_isEmpty, prop_size, prop_focus` get proved automatically with no additional equational reasoning, and `prop_list, prop_rot` by assumption on some refined types

## Usage

- To run liquid `stack exec -- liquid -isrc/ src/Main.hs`

- To run liquid continously by watching file changes, run `spy run -n "stack exec -- liquid -isrc/ src/Main.hs" src/`

In `package.json` are provided some other commands that run liquidhaskell with `stack` which you can either copy paste in your terminal, or run using `yarn` or `npm`
