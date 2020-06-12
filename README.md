## Semi-automatic QuickCheck to LiquidHaskell migration

This project aims to facilitate the migration/conversion of QuickCheck properties to LiquidHaskell proofs, by automating the translation process of QuickCheck tests to LiquidHaskell formal proof obligations.

It can also be used as a mini proof assistant to help the overall experience and reduce the manual work in LiquidHaskell proofs.

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

(Having the property separated from your proof eases the parsing of your specification to LH)

### LH annotations

You might want to use reflection on `property` and PLE on `propert_proof`, so you can either use `lhp` options:

```haskell
[lhp|genProp|reflect|ple
property :: Bool -> [Bool] -> Bool
property x ls = SOMETHING
|]
```

Or, since the symbols `property_proof` and `property` are available in the scope, you can manually add LH annotations as:

```haskell
{-@ reflect property @-}
{-@ ple property_proof @-}
[lhp|genProp
property :: Bool -> [Bool] -> Bool
property x ls = SOMETHING
|]
```

You can use the symbols in any other Haskell code, so you're not limited only to LH. For instance, the property can be run with QuickCheck.

## Proof Automation

### Automatic Case Splitting

You can use the option `caseExpand` to automatically do case splitting on your proof's parameters, this will drastically ease the proof to `PLE`.

For example, writing this:

```haskell
data Fruit = Apple | Banana
[lhp|ple|caseExpand
property :: Bool -> Fruit  -> Bool
property bl fr = True
|]
```

Is the same as writing this proof:

```haskell
{-@ ple property_proof @-}
property_proof :: Bool -> Fruit -> Proof
property_proof bl@False fr@Apple
  = (True) *** QED
property_proof bl@False fr@Banana
  = (True) *** QED
property_proof bl@True fr@Apple
  = (True) *** QED
property_proof bl@True fr@Banana
  = (True) *** QED
```

### Helping LH with a single case

Using case expansion, you might want to add information on a single case, for example by adding an inductive hypothesis:

```haskell
[lhp|genProp|reflect|ple|caseExpand
assocP :: Eq a => [a] -> [a] -> [a] -> Bool
assocP (x:xs) ys zs = () ? assocP_proof xs ys zs
assocP xs ys zs = xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
|]
```

You only have to make sure that the plain boolean property is the last one you declare. You can specify anything that you want `lhp` to include in the proof above that.
If you use `genProp` the property generated will not include the additional information that you provide with the "?" combinator.

### Limiting case expansion on certain parameters

When you have several parameters, the case expansion might generate many clauses, having negative effect on verification time.
You can use the option `caseExpandP:n` to instruct `lhp` to do pattern matching only on the first `n` parameters of your proof:

```haskell
[lhp|genProp|reflect|ple|caseExpandP:1
assocP ::  Eq a => [a] -> [a] -> [a] -> Bool
assocP xs ys zs = xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
|]
```

The above will generate only 2 clauses instead of 8:

```haskell
assocP ::  Eq a => [a] -> [a] -> [a] -> Bool
assocP_proof xs@[] ys zs = ...
assocP_proof xs@(_ : _) ys zs =...
```

## Exhaustive Induction

The tool implements a heuristic to automatically generate induction hypotheses for your proofs. It generates all possible inductive hypotheses on your recursive (well defined) parameters. This heuristic works only when you use the automatic case expansion, otherwise the proof generator wouldn't be sure that you'd have a base case for your proof (thus that it terminates).

Suppose you want to prove the following property:

```haskell
property xs = xs ++ [] == xs
```

where `++` is defined as:

```haskell
(++) :: [a] -> [a] -> [a]
[]       ++ ys = ys
(x : xs) ++ ys = x : (xs ++ ys)
```

You will notice that `PLE` alone does not suffice but it's necessary to give a manual proof:

```haskell
{-@ rightId :: xs:[a] -> { xs ++ [] == xs } @-}
rightId :: [a] -> Proof
rightId []
   =   [] ++ []
  === []
  *** QED
rightId (x:xs)
  =   (x:xs) ++ []
  === x : (xs ++ [])
      ? rightId xs
  === x : xs
  *** QED
```

Namely, this proof contains the recursive call `rightId xs` (which acts as an inductive hypothesis in the proof).
With the `lhp` proof assistant you can use the `induction` option and prove the property automatically:

```haskell
[lhp|genProp|reflect|ple|caseExpand|induction
rightIdP :: Eq a => [a] -> Bool
rightIdP xs  = xs ++ [] == xs
|]
```

Under the hood, it generates all possible inductive calls on the subparts of the recursive (well defined) parameters of your proof, then it filters out those that endanger the proof's termination.

### Limit the generated inductive calls

The `exhaustive induction` may increase the verification time even when you have simple proofs as this one:

```haskell
{-@ assocP :: xs:[a] -> ys:[a] -> zs:[a]
        -> { xs ++ (ys ++ zs) == (xs ++ ys) ++ zs }  @-}
assocP :: [a] -> [a] -> [a] -> Proof
assocP [] _ _       = trivial
assocP (x:xs) ys zs = () ? assocP xs ys zs
```

The case expansion + induction will generate 8 clauses with multiple inductive hypothesis:

```haskell
assocP_proof :: forall a. Eq a => [a] -> [a] -> [a] -> Proof
assocP_proof xs@[] ys@[] zs@[]
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs) *** QED
assocP_proof xs@[] ys@[] zs@(p072 : p073)
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
       ? ((assocP_proof xs) ys) p073)
      *** QED
assocP_proof xs@[] ys@(p070 : p071) zs@[]
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
       ? ((assocP_proof xs) p071) zs)
      *** QED
assocP_proof xs@[] ys@(p070 : p071) zs@(p072 : p073)
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
       ? ((assocP_proof xs) p071) zs
       ? ((assocP_proof xs) p071) p073
       ? ((assocP_proof xs) ys) p073)
      *** QED
assocP_proof xs@(p068 : p069) ys@[] zs@[]
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
       ? ((assocP_proof p069) ys) zs)
      *** QED
assocP_proof xs@(p068 : p069) ys@[] zs@(p072 : p073)
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
       ? ((assocP_proof p069) ys) zs
       ? ((assocP_proof p069) ys) p073
       ? ((assocP_proof xs) ys) p073)
      *** QED
assocP_proof xs@(p068 : p069) ys@(p070 : p071) zs@[]
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
       ? ((assocP_proof p069) ys) zs
       ? ((assocP_proof p069) p071) zs
       ? ((assocP_proof xs) p071) zs)
      *** QED
assocP_proof xs@(p068 : p069) ys@(p070 : p071) zs@(p072 : p073)
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
       ? ((assocP_proof p069) p071) zs
       ? ((assocP_proof p069) p071) p073
       ? ((assocP_proof p069) ys) zs
       ? ((assocP_proof p069) ys) p073
       ? ((assocP_proof xs) p071) zs
       ? ((assocP_proof xs) p071) p073
       ? ((assocP_proof xs) ys) p073)
      *** QED
```

To avoid this explosion, you can use the option `inductionP:1` where `1` means that you want the induction to be generated only on the first parameter of the proof. That will cut all the excess and reduce the verification time.
Thus, for the case above, you would have an inductive call only for the cases where the first parameter `xs` is non-empty (thus 4). The following is safe:

```haskell
[lhp|genProp|reflect|ple|caseExpand|inductionP:1
assocP ::  Eq a => [a] -> [a] -> [a] -> Bool
assocP xs ys zs = xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
|]
```

Will generate this:

```haskell
assocP_proof :: forall a. Eq a => [a] -> [a] -> [a] -> Proof
assocP_proof xs@[] ys@[] zs@[]
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs) *** QED
assocP_proof xs@[] ys@[] zs@(p072 : p073)
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs) *** QED
assocP_proof xs@[] ys@(p070 : p071) zs@[]
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs) *** QED
assocP_proof xs@[] ys@(p070 : p071) zs@(p072 : p073)
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs) *** QED
assocP_proof xs@(p068 : p069) ys@[] zs@[]
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
       ? ((assocP_proof p069) ys) zs)
      *** QED
assocP_proof xs@(p068 : p069) ys@[] zs@(p072 : p073)
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
       ? ((assocP_proof p069) ys) zs)
      *** QED
assocP_proof xs@(p068 : p069) ys@(p070 : p071) zs@[]
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
       ? ((assocP_proof p069) ys) zs)
      *** QED
assocP_proof xs@(p068 : p069) ys@(p070 : p071) zs@(p072 : p073)
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
       ? ((assocP_proof p069) ys) zs)
      *** QED
```

Alternatively, you are flexible to limit the case expansion and let the induction follow:

```haskell
[lhp|genProp|reflect|ple|induction|caseExpandP:1
assocP ::  Eq a => [a] -> [a] -> [a] -> Bool
assocP xs ys zs = xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
|]
```

Generates 1 inductive call and 2 clauses. Just the needed to prove the property:

```haskell
assocP_proof xs@[] ys zs
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs) *** QED
assocP_proof xs@(p686 : p687) ys zs
  = (xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
       ? ((assocP_proof p687) ys) zs)
      *** QED
```

## Debugging

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

    [qc-to-lh]: property_proof :: p_0:Bool  -> p_1: [Bool]  -> {v:Proof | property p_0 p_1}
```

### Running LiquidHaskell locally to a proof (experimental)

You could use `runLiquidW` option to run liquidhaskell locally on a proof and see its result as a warning:

```haskell
[lhp|ple|reflect|genProp|runLiquidW
property :: Bool -> [Bool] -> Bool
property x ls = SOMETHING
|]
```

Will show `LH`'s result on the binders `property` and `property_proof` as a warning at compile time. This is useful for IDE integration, because those warnings will automatically show in your IDE without you having to integrate liquidhaskell.

Or if you have an extension that reads `.liquid` dirs to show you the errors ([like this one for vscode](https://marketplace.visualstudio.com/items?itemName=MustafaHafidi.liquidhaskell-diagnostics)), you can use the option `runLiquid` instead, which will run silently LH on the proof.

## CList and Skew Heap Proofs Case studies

- `src/CList_Proofs.hs` contains the formal proofs of the QuickCheck properties in `src/Lib/CL/QuickCheck.hs`
  - The proofs have been rewritten using the ProofGenerator lhp in `src/Test/CList_Proofs.hs`
- `src/Heap_Proofs.hs` contains the formal proofs of the QuickCheck properties in `src/Lib/QC/Heap.hs`
  - The proofs have been rewritten using the ProofGenerator lhp in `src/Test/Heap_Proofs.hs`
- To run LH on them: `stack exec -- liquid -isrc/ {target_file}`

- To run LH continously by watching file changes, run `spy run -n "stack exec -- liquid -isrc/ {target_file}" src/`

In `package.json` are provided some other commands that run liquidhaskell with `stack` which you can either copy paste in your terminal, or run using `yarn` or `npm`

# TODO:

- [..] Benchmark `lhp`
- [..] Support for higher order properties (arrows as arguments)
- [..] Consider support for case expansion in sub terms (for example the type [[a]])
- [..](optimization) make case expansion reuse user-provided cases, if induction prop is used, then it should add them directly to pre-existing clause
