# Dragonfly

A Haskell dependent-type learning kernel plus a minimal CCHM computational-
univalence kernel adapted directly from cubicaltt. Both use explicit,
noncumulative universe levels: `Type l : Type (l + 1)`.

## Run

```sh
cabal build all
cabal test all --test-show-details=direct
cabal run dragonfly
```

The executable begins with an actual cubical reduction:

```text
Computational univalence: transport along the pair-swap equivalence
  (false, true) -> (true,false)
```

It then runs the original dependent identity examples. The cubical kernel uses
`containers`, `mtl`, and `pretty` in addition to `base`; no parser generators or
external proof assistant are needed.

## Computational univalence

Import `Dragonfly.Cubical` (qualified if also using the original kernel):

```haskell
import qualified Dragonfly.Cubical as C

-- A checked closed term: ua_0 applied to the pair-swap equivalence.
result = C.normalizeClosed
  (C.transport C.swapPath (C.Pair C.false C.true))
-- Right "(true,false)"

-- Generic, level-indexed univalence is itself checked by the kernel.
checked = C.checkClosed (C.ua 2) (C.uaType 2)
-- Right ()
```

`ua l` is an ordinary annotated term with type
`(A B : Type l) -> Equiv A B -> Path (Type l) A B`. It is built as:

```text
ua_l A B e = <i> Glue_l B
  [ (i=0) -> (A,e), (i=1) -> (B,identityEquivalence B) ]
```

There is no `ua` evaluator constructor or univalence postulate. Equivalences
are functions with contractible fibers. Identity equivalence and the pair-swap
equivalence include checked fiber-contraction proofs made from ordinary terms.
Transport is composition with an empty tube. The end-to-end test checks the
equivalence, checks its universe path and endpoints, and verifies that transport
changes a closed pair to the swapped pair. It also verifies that this result is
not convertible to the unchanged pair.

The public AST is deliberately close to cubicaltt: named term binders, typed
lambdas, dimension abstractions `PLam`, dimension applications `AppFormula`,
and `U l` for `Type l`. This is a separate AST from the original de Bruijn
`Dragonfly.Syntax.Term`, so the original kernel and its tests stay intact.
Use `Ann term type` for introductions that need an inferred type.

The checked API provides:

```haskell
checkClosed     :: Ter -> Ter -> Either TypeError ()
inferClosed     :: Ter -> Either TypeError String
normalizeClosed :: Ter -> Either TypeError String
normalizesTo    :: Ter -> Ter -> Ter -> Either TypeError Bool
```

`normalizesTo term expected type` checks both terms before comparing their
computed values, including eta conversion. `inferClosed` and `normalizeClosed`
render semantic results for inspection. They do not expose unchecked values.

### Implemented boundary

- Separate nominal dimensions with De Morgan connections and substitution.
- Dependent paths with endpoint checks and beta/eta conversion.
- Face systems represented by finite disjunctions of conjunctions of endpoint
  constraints. Every supplied side is checked, including overlap compatibility,
  before system absorption. `system` constructs a map; use unique face keys.
- CCHM composition/filling for Pi, Sigma, paths, Glue, and universes.
- `Glue l base equivalences`, with its base and partial domains in `Type l`.
- `GlueElem type base partialElements` and `UnGlueElem element type`; explicit
  type annotations also support universe-composition elements. Unglue needs an
  explicit `Glue` or universe `Comp` presentation, optionally wrapped in `Ann`;
  a dynamically computed alias alone is rejected because reduction can erase
  the elimination data on a face.
- A closed Boolean type used only to demonstrate nontrivial computation.

Pi/Sigma formation takes the maximum universe level. Dependent paths inherit
the family level. Composition checks a family in one fixed universe, and Glue
checks each partial equivalence at its declared level. Semantic universe and
universe-composition values retain levels. There is no cumulativity, implicit
resizing, `U : U`, or `Type l : Type l` rule.

This is the minimum AST-only univalence milestone. Recursive declarations,
general inductive types, higher inductive types, holes, undefined terms, the
parser, and the REPL are not exposed or accepted by the checked cubical API.
Some unused upstream evaluator forms remain internally to avoid rewriting the
reference algorithms. Raw internal evaluation assumes checked inputs.
CCHM computations can retain neutral composition terms; in particular, no
extra rule claiming every constant-family transport is judgmentally identity
has been added.

### Modules and validation

- `src/Dragonfly/Cubical/Connections.hs`: interval algebra, faces, nominal
  substitution, and systems, adapted from cubicaltt.
- `Syntax.hs` and `Eval.hs` in that directory: level-indexed syntax and the
  reference composition, universe-composition, and Glue algorithms.
- `Check.hs`: pure checking boundary with explicit levels and checked systems.
- `Univalence.hs`: ordinary AST builders for equivalences, `ua`, and the witness.
- `test-cubical/Main.hs`: the computational target plus universe rejection,
  endpoints, dimension scoping, De Morgan laws, overlapping faces, filling,
  Glue computation, and composition in a universe-composition type.
- `test/Main.hs`: the original non-cubical kernel regressions and interval tests.

Source provenance, the pinned upstream commit, adaptation notes, and the MIT
license are in `vendor/cubicaltt/`. Dragonfly's own code remains Apache-2.0.
The mathematical references are the
[CCHM paper](https://arxiv.org/abs/1611.02108) and
[cubicaltt](https://github.com/mortberg/cubicaltt).

The focused [correctness and soundness audit](docs/cubical-audit.md) records the
bugs fixed, adversarial tests, universe checks, and remaining proof obligations.
Run its tests with `cabal test cubical-audit-tests`; check package encapsulation
with `cabal exec -- bash test-audit/check-exports.sh`.

The following sections describe the original learning kernel.

## 1. Syntax and binding

Read `src/Dragonfly/Syntax.hs` first. `Term` is the input language; there is no
parser yet. `Var 0` refers to the nearest enclosing binder, `Var 1` to the next,
and so on. Binder names are hints for printing and do not affect conversion.
`Natural` makes negative variable indices and universe levels unrepresentable.

For example, `(A : Type 0) -> (x : A) -> A` is:

```haskell
Pi "A" (Universe 0) (Pi "x" (Var 0) (Var 1))
```

The domain of `x` sees only `A`, at index 0. The result sees both `x` and `A`,
so `A` has index 1. Its inhabitant is `Lam "A" (Lam "x" (Var 0))`.

`shift amount cutoff` raises free indices at or above the cutoff. The cutoff
increases under a binder. `substitute index replacement body` replaces the
selected variable **and removes its context entry**; larger indices decrease.
The replacement is shifted as substitution crosses binders to avoid capture.
`instantiate argument body` specializes this operation to index 0.

## 2. Evaluation and normalization

Read `src/Dragonfly/Eval.hs`. Evaluation uses an environment of semantic values.
A lambda becomes a closure containing its body and environment; applying it
extends that environment with the argument. Pi codomains are closures too.
Explicit syntax substitution is useful for studying binding, but evaluation
does not repeatedly traverse syntax to substitute arguments.

Open variables become neutral values. Applying an unknown function extends its
neutral application spine instead of trying to reduce it. Semantic variables
use levels counted from the outside: adding a binder does not renumber them.
Reification converts a level to an index with `depth - level - 1`.

`quote` reifies values, including underneath lambdas and Pi binders, to
beta-normal syntax. `convertible` compares values structurally, ignores binder
names, and compares functions on a fresh neutral argument. This supplies eta
conversion on demand; printed normal forms are not necessarily eta-long.

Low-level evaluation/conversion APIs assume well-typed inputs (and compatible
contexts). They report structural evaluation failures, but unchecked untyped
terms can still diverge. Use the checked entry points below for input terms.

## 3. Bidirectional checking

Read `src/Dragonfly/Check.hs`. The public closed-term interface is:

```haskell
inferClosed     :: Term -> Either TypeError Term
checkClosed     :: Term -> Term -> Either TypeError ()
normalizeClosed :: Term -> Either TypeError (Term, Term)
```

The pair from `normalizeClosed` is `(inferredType, normalForm)`. `checkClosed`
first verifies that its second argument is a type.

Inference handles variables, universes, Pi formation, applications, and
annotations. A bare lambda needs an expected Pi type, so give a top-level lambda
an `Ann` when asking to infer or normalize it. Application checks the argument
against the domain, then instantiates the codomain closure with that argument.
The fallback checking rule compares inferred and expected types by conversion.

`Universe l` has type `Universe (l + 1)`. A Pi whose domain and codomain inhabit
levels `l` and `r` inhabits `max l r`. Universes are noncumulative: checking
`Universe 0` against `Universe 2` fails, even though it checks against
`Universe 1`. There is no `Type : Type` rule.

## 4. Examples and tests

Read `src/Dragonfly/Examples.hs`, then `src/Main.hs`. To add an example, construct
a `Term` in the `examples` list. For example:

```haskell
App (identity 1) (Universe 0)
```

Here `identity 1` accepts a type in `Type 1`, so `Type 0` is a valid argument.
The result has type `(x : Type 0) -> Type 0` and normal form `\x. x`.

`src/Dragonfly/Pretty.hs` prints terms with fresh binder names and formats
structured errors. Free indices in error terms appear as `#n`; the printer's
output is for inspection, not a round-trip source format.

`test/Main.hs` exercises capture avoidance, closures, beta reduction under
binders, alpha/eta equality, eta conversion within dependent types, dependent
applications, universe rules, and rejection of invalid terms. It uses a small
assertion runner and exits unsuccessfully on the first failed assertion.
