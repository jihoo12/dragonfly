# Dragonfly

A small Haskell learning kernel for dependent type theory, intended as a
foundation for a future CCHM cubical implementation. The current milestone has
Pi types, lambdas, application, annotations, and a noncumulative universe
hierarchy. It does not yet implement intervals, paths, or composition.

## Run

With the prepared GHC/Cabal toolchain:

```sh
cabal build all
cabal test --test-show-details=direct
cabal run dragonfly
```

The kernel and its tests require only `base`. The executable prints inferred
types and beta-normal forms for polymorphic identity and its applications,
then demonstrates rejection of `Type 0 : Type 0`.

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

## Future milestones

Plan these separately before implementing them:

1. Dependent pairs and projections.
2. A separate dimension context and De Morgan interval expressions, without
   assuming Boolean excluded middle.
3. Dependent paths, dimension abstraction/application, and endpoint checking.
4. Face formulas, compatible partial systems, and CCHM composition.
5. Universe composition, Glue types, and computational univalence.

The intended references are the
[CCHM paper](https://arxiv.org/abs/1611.02108) and
[cubicaltt](https://github.com/mortberg/cubicaltt).
Parsing, a REPL, implicit arguments, metavariables, general recursion, and higher
inductive types remain outside the first milestone.
