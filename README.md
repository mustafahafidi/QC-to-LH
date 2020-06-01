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
- :heavy_check_mark: Redefine Eq == and rewrite properties, then prove them
  - :heavy_check_mark: Create bug issues to show why reflecting mRotL,mRotR doesn't work
- :heavy_check_mark: Solve the Heap proofs (try the refined data-type to ease the proofs)

### 2) Design the tool and implement it

- :heavy_check_mark: Check Template Haskell and GHC Plugin
- :heavy_check_mark: Parse property declaration given as a String
- :heavy_check_mark: Build refinement type and proof body of the parsed property
- :heavy_check_mark: Build a syntactic sugar quasiquoter
- :heavy_check_mark: Possibility to pass options to the custom quasiquoter
- :heavy_check_mark: Parse options to automatically generate ple, ignore, reflect annotations
- :heavy_check_mark: Added option to run LH on a single proof
- [..] Give it a try on CList
- [..] Give it a try on Heap

### 3) Write paper/thesis describing the whole work (can happen in parallel to the work)

### 4) Defend thesis (17 July 2020)

## Usage

This repository provides the `lhp` QuasiQuoter that generates boilerplate code to write proofs in liquidhaskell, and possibly tries to help in proving them.
Take this as an example:

```haskell
[lhp|
property :: Bool -> [Bool] -> Bool
property x ls = SOMETHING
|]
```

Will generate a proof like this:

```haskell
{-@ property_proof :: p1:Bool -> p2:[Bool] -> { property p1 p2 } @-}
property_proof :: Bool -> [Bool] -> Bool
property_proof x ls = SOMETHING
                    ***QED
```

The `lhp` QQ used like this, generates only `property_proof` but not the declaration of `property` passed in to it. That's why, to avoid duplicating the code, you can give the option `genProp` to `lhp` to do this for you:

```haskell
[lhp|genProp
property :: Bool -> [Bool] -> Bool
property x ls = SOMETHING
|]
```

Will generate both the proof and the property.

```haskell
property :: Bool -> [Bool] -> Bool
property x ls = SOMETHING

{-@ property_proof :: p1:Bool -> p2:[Bool] -> { property p1 p2 } @-}
property_proof :: Bool -> [Bool] -> Bool
property_proof x ls = SOMETHING
                    ***QED
```

You might want to use reflection on `property` and PLE on `propert_proof`, so you can either use `lhp` options:

```haskell
[lhp|genProp|reflect|ple
property :: Bool -> [Bool] -> Bool
property x ls = SOMETHING
|]
```

Or, manually add LH annotations as:

```haskell
{-@ reflect property @-}
{-@ ple property_proof @-}
[lhp|genProp
property :: Bool -> [Bool] -> Bool
property x ls = SOMETHING
|]
```

#### Running LiquidHaskell locally to a proof

You could use `runLiquidW` option to run liquidhaskell locally on a proof and see its result as a warning:

```haskell
[lhp|ple|reflect|genProp|runLiquidW
property :: Bool -> [Bool] -> Bool
property x ls = SOMETHING
|]
```

Will show `LH`'s result on the binders `property` and `property_proof` as a warning. Why? This is useful for IDE integration, because those warnings will automatically show in your IDE without you having to integrate liquidhaskell.

Or if you have an extension that reads `.liquid` dirs to show you the errors ([like this one for vscode](https://marketplace.visualstudio.com/items?itemName=MustafaHafidi.liquidhaskell-diagnostics)), you can use the option `runLiquid` instead, which will run silently LH on the proof.

#### Debugging

To see what `lhp` has generated, you can run ghci/ghc/liquidhaskell with the option `-dth-dec-file` or put on top of your module
`{-# OPTIONS_GHC -dth-dec-file #-}`
This will cause GHC to generate a "\*.th.hs" containing what `lhp` expands to.

If you don't want to see all of that, and you want to see only the LH annotations that `lhp` generates, then you can use the option `debug`:

```haskell
[lhp|ple|reflect|genProp|debug
property :: Bool -> [Bool] -> Bool
property x ls = SOMETHING
|]
```

Will show you this warnings in your IDE/ghci/ghc:

```haskell
    [qc-to-lh]: ple property_proof

    [qc-to-lh]: reflect property

    [qc-to-lh]: property_proof :: p_0:Bool  -> p_1: [Bool]  -> {v:Proof | property p_2 p_3}
```

## CList and Skew Heap Proofs Case studies

- `src/CList_Proofs.hs` contains the formal proofs of the QuickCheck properties in `src/Lib/CL/QuickCheck.hs`
- `src/Heap_Proofs.hs` contains the formal proofs of the QuickCheck properties in `src/Lib/QC/Heap.hs`

- To run LH on them: `stack exec -- liquid -isrc/ {target_file}`

- To run LH continously by watching file changes, run `spy run -n "stack exec -- liquid -isrc/ {target_file}" src/`

In `package.json` are provided some other commands that run liquidhaskell with `stack` which you can either copy paste in your terminal, or run using `yarn` or `npm`
