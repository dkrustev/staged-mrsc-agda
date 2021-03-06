# Codata and corecursion: cleaning before whistling

By using codata and corecursion, we can decompose `lazy-mrsc` into two stages
```
    lazy-mrsc ≗ prune-cograph ∘ build-cograph
```
where `build-cograph` constructs a (potentially) infinite tree,
while `prune-cograph` traverses this tree and turns it into
a lazy graph (which is finite).

## Lazy cographs of configurations

A `LazyCograph C` represents a (potentially) infinite set of
graphs of configurations whose type is `Graph C` (see
`Cographs.agda`). 

```
data LazyCograph (C : Set) : Set where
  Ø     : LazyCograph C
  stop  : (c : C) → LazyCograph C
  build : (c : C) (lss : ∞(List (List (LazyCograph C)))) → LazyCograph C
```
Note that `LazyCograph C` differs from `LazyGraph C` the evaluation
of `lss` in build-nodes is delayed.

## Building lazy cographs

Lazy cographs are produced by the function `build-cograph`
```
build-cograph : (c : Conf) → LazyCograph Conf
```
which can be derived from the function `lazy-mrsc` by removing
the machinery related to whistles.

`build-cograph` is defined in terms of a more general function
`build-cographs′`.
```
build-cograph′ : (h : History) (c : Conf) → LazyCograph Conf
build-cograph c = build-cograph′ [] c

```
The definition of `build-cograph′` uses auxiliary functions
`build-cograph⇉` and `build-cograph*`, while the definition of
`lazy-mrsc` just calls `map` at corresponding places. This is
necessary in order for `build-cograph′` to pass Agda's
"productivity" check.
```
build-cograph⇉ : (h : History) (c : Conf) (css : List (List Conf)) →
  List (List (LazyCograph Conf))

build-cograph* : (h : History) (cs : List Conf) → List (LazyCograph Conf)

build-cograph′ h c with foldable? h c
... | yes f = stop c
... | no ¬f =
  build c (♯ build-cograph⇉ h c (c ⇉))

build-cograph⇉ h c [] = []
build-cograph⇉ h c (cs ∷ css) =
  build-cograph* (c ∷ h) cs ∷ build-cograph⇉ h c css

build-cograph* h [] = []
build-cograph* h (c ∷ cs) =
  build-cograph′ h c ∷ build-cograph* h cs
```

## Pruning lazy cographs

A lazy cograph can be pruned by means of the function `prune-cograph`
to obtain a finite lazy graph.
```
prune-cograph : (l : LazyCograph Conf) → LazyGraph Conf
```
which can be derived from the function `lazy-mrsc` by removing
the machinery related to generation of nodes (since it only consumes
nodes that have been generated by `build-cograph`).

`prune-cograph` is defined in terms of a more general function
`prune-cograph′`:
```
prune-cograph l = prune-cograph′ [] bar[] l
```
The definition of `prune-cograph′` uses the auxiliary function
`prune-cograph*`.
```
prune-cograph* : (h : History) (b : Bar ↯ h)
  (ls : List (LazyCograph Conf)) → List (LazyGraph Conf)

prune-cograph′ h b Ø = Ø
prune-cograph′ h b (stop c) = stop c
prune-cograph′ h b (build c lss) with  ↯? h
... | yes w = Ø
... | no ¬w with b
... | now bz with ¬w bz
... | ()
prune-cograph′ h b (build c lss) | no ¬w | later bs =
  build c (map (prune-cograph* (c ∷ h) (bs c)) (♭ lss))

prune-cograph* h b [] = []
prune-cograph* h b (l ∷ ls) =
  prune-cograph′ h b l ∷ (prune-cograph* h b ls)
```
Note that, when processing a node `build c lss`, the evaluation of
`lss` has to be explicitly forced by `♭`.

`prune-cograph` and `build-cograph` are correct with respect
to `lazy-mrsc`:
```
 prune∘build-correct :
    prune-cograph ∘ build-cograph ≗ lazy-mrsc
```
A proof of this theorem can be found in `Cographs.agda`.

## Promoting some cleaners over the whistle

Suppose `clean∞` is a cograph cleaner such that
```
     clean ∘ prune-cograph ≗ prune-cograph ∘ clean∞
```
then 
```
     clean ∘ lazy-mrsc ≗
       clean ∘ prune-cograph ∘ build-cograph ≗
       prune-cograph ∘ clean∞ ∘ build-cograph
```

The good thing about `build-cograph` and `clean∞` is that they
work in a lazy way, generating subtrees by demand. Hence, evaluating
```
     ⟪ prune-cograph ∘ (clean∞ (build-cograph c))  ⟫
```
may be less time and space consuming than evaluating
```
     ⟪ clean (lazy-mrsc c) ⟫
```
In `Cographs.agda` there is defined a cograph cleaner `cl-bad-conf∞`
that takes a lazy cograph and prunes subrees containing bad
configurations, returning a lazy subgraph (which can be infinite):
```
cl-bad-conf∞ : {C : Set} (bad : C → Bool) (l : LazyCograph C) →
  LazyCograph C
```
`cl-bad-conf∞` is correct with respect to `cl-bad-conf`:
```
  cl-bad-conf∞-correct : (bad : Conf → Bool) →
    cl-bad-conf bad ∘ prune-cograph ≗
      prune-cograph ∘ cl-bad-conf∞ bad
```
A proof of this theorem can be found in `Cographs.agda`.
