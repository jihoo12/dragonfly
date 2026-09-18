# cubicaltt provenance

Source: https://github.com/mortberg/cubicaltt
Commit: 9baa6f2491cc61dbd4fd81d58323c04100381451
License: MIT (preserved in LICENSE).

Dragonfly.Cubical.Syntax, Connections, and Eval adapt CTT.hs, Connections.hs,
and Eval.hs from this commit. The checker adapts the path, face/system, Glue,
and composition checks in TypeChecker.hs, replacing its universe boundary.

Changes: namespaced modules; explicit Natural universe levels in terms/values;
term annotations; removal of the embedded QuickCheck generators; a restricted,
level-indexed checker instead of the upstream U : U checker. Upstream raw syntax
and evaluation helpers are retained to keep the computational algorithms close
to their source. They are internal, unchecked implementation details. The public
checked interface rejects holes, undefined terms, recursive declarations,
inductive definitions, and other forms outside the supported fragment.

The adapted evaluator additionally retains the target type on neutral unglue
values (the upstream inferType case noted this omission), and evaluates the
supported closed nullary sums without irrelevant surrounding environments.
Glue introductions/eliminations carry an explicit target-type annotation.
Universe-composition and Glue semantic values carry their declared level.
The checker is pure, checks source face scopes and all overlaps before system
absorption, and substitutes fresh semantic names for dimension binders.
Local warning exceptions in the three imported modules cover upstream naming,
unused bindings, partial low-level functions, and orphan instances. The new
checker, public API, and term builders compile under the project-wide -Wall.
