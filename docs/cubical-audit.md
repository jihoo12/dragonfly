# Cubical kernel correctness and soundness audit

This is a source review and adversarial regression audit, not a proof of
soundness. The baseline computational-univalence and non-cubical tests were
kept unchanged. No universe discipline or language feature was added.

References: cubicaltt commit `9baa6f2491cc61dbd4fd81d58323c04100381451`
and [CCHM, sections 4–7 and appendix A](https://arxiv.org/html/1611.02108).
The paper supplies the composition, filling, Glue, and universe-composition
rules; the level-indexed boundary is Dragonfly's adaptation.

## Bugs found and fixed

### 1. Unglue lost its presentation under dimension substitution

`UnGlueElem` previously dispatched on the evaluated type unless its annotation
was syntactically `Glue`. On a full face, Glue reduces to its partial domain;
universe composition reduces to the endpoint of its tube. At that point the
result no longer contains the base and equivalence/line information needed for
elimination. Deferred lambda evaluation could reach the fallback `error` through
`inferClosed` or `normalizeClosed`, despite successful checking in the generic
dimension context.

The initial audit reproduced exceptions in four probes: checking and using the
endpoint of an annotated-Glue elimination path, and the analogous universe-
composition path. The final regressions force both errors and successful results
to avoid overlooking lazy exceptions.

Fix: checker and evaluator share `gluePresentation`, which preserves the base
and partial system from an explicit `Glue` or `Comp` annotation, peeling outer
`Ann` nodes. Universe presentations additionally require the entire family to
be convertible to a constant `Type l`; merely ending at a universe is not
sufficient. The evaluator now uses the appropriate equivalence application or
backward transport even when the annotated type has reduced on a full face.

**Intentional restriction:** unglue annotations given only by a dynamically
computed type alias are rejected with `TypeError`. They need an explicit `Glue`
or universe `Comp` presentation (possibly inside `Ann`). Recovering erased
information from an arbitrary reduced type was unsafe. Supporting arbitrary
aliases would require checked elaboration retaining the presentation; this audit
does not introduce that feature. Existing tests did not rely on aliases.

This was an evaluator-safety/subject-reduction defect; the probes did not
establish a closed inhabitant of a false type or a universe inconsistency.

### 2. AST builders used lossy pretty-printing to choose fresh names

`freshIdentifier` searched `show terms`. The printer omits the target annotation
of `GlueElem`, so a free name appearing only there could be captured by `path`'s
generated dimension binder. This could change the intended AST or cause valid
helper-generated syntax to be rejected.

Fix: names are collected structurally, including target annotations, system
faces, and every existing raw syntax constructor. The new regression exhibited
the capture before the fix. This is a helper hygiene defect, not evidence that
the checker accepted an ill-typed term.

## Universe-boundary audit

| Upstream boundary | Dragonfly rule / finding |
| --- | --- |
| `infer U = VU` | `infer (U l) = VU (l+1)`; levels are `Natural`. No self-universe case. |
| Pi/Sigma `checkFam` | Infer both formation levels and return their maximum. Lambda annotations are independently checked as types before conversion. |
| Path formation / `checkPLam (constPath VU)` | Infer one uniform family universe; both endpoints are checked in its endpoint types. A path *in* `Type l` forms in `Type (l+1)`. |
| Glue formation | Base and every partial domain are checked against exactly `VU l`; no subtyping, lifting, or resizing. |
| `mkEquiv` and partial equivalences | Domain field is checked against `VU l`, then function and fiber-contraction fields are checked dependently. The bundled partial equivalence type itself is larger because it quantifies over `Type l`; it is not silently assigned to `Type l`. |
| Ordinary `equiv A B` | This is an ordinary Sigma/Pi expression. For inputs at different levels it can form at their maximum, but cannot be checked at the smaller level. `ua_l` and Glue demand both inputs at the same specified level. Formation of a heterogeneous equivalence type is not a resizing operation or an equivalence witness. |
| `Comp` / `Fill` family checks | Infer one family level and check the start and every tube in the family. Result is its target type, or the dependent path for filling. A total tube does not bypass validation of the start. |
| Composition *in* a universe | `comp` on `VU l` constructs `VCompU l`. On a full face it returns a checked tube endpoint in that same universe. Universe introductions/eliminations validate their retained presentation. |
| Glue/universe element checks | Formation of the annotated target precedes element checks. Every side has the partial domain type and maps/ transports to the base value on that face. |
| Conversion / substitution / normalization | `VU`, `VGlue`, and `VCompU` preserve levels. Glue and universe-composition conversion compare level tags; distinct `VU` constructors are unequal. Full-face reductions can discard a tag only by returning an already checked same-level component. |
| Upstream `mkIso`, declarations/telescopes, recursive/parameterized sums, splits, HITs, `Id`/`IdJ`, `PCon`, `HComp` checks using `VU` | Not ported into the checked fragment. Unsupported constructors are hidden from the public API and rejected by checker fallback. Only closed nullary sums are accepted internally; the public module supplies the fixed Boolean type and its two constructors as terms. |

The audit found no public checked-API route to `Type l : Type l`, unintended
cumulativity, resizing, mixed-level Glue, or an incorrectly assigned universe-
composition level. This is a bounded empirical result supported by source review,
not a universal theorem about all inputs.

## Computation-rule audit

Direct comparison with the pinned source found `compGlue`, `compU`, `lemEq`,
`compLine`, `fill`, `fillLine`, and `pathComp` unchanged apart from whitespace.
The `comp` dispatcher retains the Pi, Sigma, and Path rules and adds level tags
at the universe and Glue boundaries. The unglue adaptation is the correction
described above; neutral unglue values also retain their result type.

The regression suite checks full-tube computation, filling boundaries, Pi
composition applied to closed arguments, the Path-composition endpoint-face
rule, full-face Glue type/element reduction, glue/unglue beta, nested Glue,
nested universe composition, and both orders of combining Glue with universe
composition. Constant-family transport on a **neutral** argument is not assumed
to be judgmentally identity; the tests use the actual CCHM computation rule.

The evaluator and checker contain no dispatch on `ua`, `swapEquivalence`,
`pairBool`, or the strings `Bool`, `false`, or `true`. Bool uses the generic
closed-nullary-sum evaluator and constructor composition, not a demonstration
shortcut. The `Sum` environment-erasure adaptation is valid only for that closed
fragment; parameterized sums remain rejected.

An independently constructed associativity equivalence maps
`Bool × (Bool × Bool)` to `(Bool × Bool) × Bool`. These endpoint types are checked
to be definitionally distinct. Its Glue path is built without calling `ua` or
`swapEquivalence`, and transport computes the expected reassociation on all
eight inputs. This tests general Sigma/Glue composition beyond the original
endomorphism witness. Neither test is a formal proof of the full univalence
theorem (for example, that `idtoequiv` is itself an equivalence).

## Additional validation

`test-audit/Main.hs` contains **364 directed checks** and **830 bounded AST
crash probes**, all through `Dragonfly.Cubical`. The crash probes fully force
rendered success/error results and use per-case timeouts. They are a totality
smoke test, not an independent typing oracle or exhaustive fuzzing.

Directed coverage includes a 288-case universe formation matrix, malformed
proof fields, full/absorbed invalid sides, unbound and shadowed dimensions,
incorrect path/fill endpoints, term-name shadowing, mixed universe levels,
nested introductions/eliminations, the two bug regressions, and independent
computational witnesses. Original tests remain unmodified.

`test-audit/check-exports.sh` first compiles a positive public-API control, then
checks that 20 internal constructors/helpers and all five internal cubical
modules are unavailable to a package consumer. It verifies the reason for each
compiler failure instead of treating an arbitrary build failure as success.

Commands (a temporary `CABAL_DIR` was used for this workspace's permissions):

```sh
cabal build all --offline
cabal test all --offline --test-show-details=direct
cabal exec --offline -- bash test-audit/check-exports.sh
cabal run dragonfly --offline
```

All three test suites, all 25 negative export checks, and the demonstration pass.

## Internal reachability and remaining assumptions

- Public construction exposes no `Hole`, `Undef`, `Where`, recursive declaration,
  `Split`, `PCon`, `HSum`, `HComp`, `Id`, `IdPair`, or `IdJ` constructor. Their
  corresponding raw evaluator branches remain in the imported source, but have
  no entry from accepted public syntax. The old `VOpaque`/declaration environments
  cannot be introduced by this checker. This was checked by export probes and
  source/call-path review, not by a machine-checked reachability proof.
- Public `bool`, `false`, and `true` do contain hidden `Sum`/`Con` nodes. Those
  particular forms are validated. The other intentionally reachable semantic
  forms include neutrals, closures, `VComp`, `VCompU`, Glue values, and printable
  normal-form lambdas. They are generated by evaluation, not supplied by callers.
- Conversion assumes well-typed semantic operands in a common context. Internal
  functions use partial pattern matches and maps whose invariants are maintained
  by the checker and the inherited algorithms. No proof establishes all of those
  invariants for every possible accepted input.
- `system` retains its documented `Map.fromList` semantics: duplicate identical
  face keys are replaced before checking. This is not a source parser preserving
  two competing clauses. Different overlapping keys are retained and checked
  before absorption. `Face` maps likewise encode one endpoint per name; a
  contradictory conjunction is represented by absence of a feasible face, not
  by duplicate map entries. Callers must not interpret map union as unchecked
  logical conjunction of contradictory constraints.
- The trust boundary is finite, total Haskell ASTs passed through the exported
  checked package API. Haskell bottom, `unsafeCoerce`, importing implementation
  source directly, and resource exhaustion are outside that guarantee.

## Differences and independent verification still needed

Dragonfly uses noncumulative explicit universes, exact small-domain Glue checks,
a restricted AST-only checked language, and explicit elimination presentations.
It has no generic declaration checker or parser, and no rule `U : U`. Its
universe-composition evaluator uses cubicaltt's specialized `VCompU`/`compU`
representation rather than expanding the paper's construction into a complete
ordinary equivalence term each time. The public API is consequently a strict
implementation fragment, not a complete CCHM elaborator.

Independent review should concentrate on subject reduction and dimension
substitution for the level-indexed checker, conversion soundness and completeness,
and the specialized universe-composition/Glue algorithms on arbitrary overlapping
systems. A formal level-indexed semantics, a proof of inaccessible raw branches,
and broad differential testing against another stratified cubical implementation
have not been supplied. The full univalence theorem and canonicity/normalization
for the entire fragment are also not machine-verified by these tests.
