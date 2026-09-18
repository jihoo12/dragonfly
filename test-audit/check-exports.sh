#!/usr/bin/env bash
# Run from the project root: cabal exec --offline -- bash test-audit/check-exports.sh
set -euo pipefail
audit_tmp=$(mktemp -d)
trap 'rm -rf "$audit_tmp"' EXIT
compile_probe() {
  ghc -fno-code -fforce-recomp -v0 -hide-all-packages -package base -package dragonfly \
    -outputdir "$audit_tmp" "$audit_tmp/Probe.hs" >"$audit_tmp/log" 2>&1
}
printf '%s\n' 'module Probe where' 'import Dragonfly.Cubical' 'ok = U 0' >"$audit_tmp/Probe.hs"
if ! compile_probe; then
  cat "$audit_tmp/log"
  exit 1
fi
checks=0
for identifier in Hole Undef Where HComp Id IdPair IdJ Sum HSum Split Con PCon eval comp compUniv VU VGlue VCompU emptyEnv gluePresentation; do
  printf '%s\n' 'module Probe where' 'import Dragonfly.Cubical' "bad = $identifier" >"$audit_tmp/Probe.hs"
  if compile_probe; then
    echo "Unexpected public export: $identifier"
    exit 1
  fi
  case "$(cat "$audit_tmp/log")" in
    *'not in scope'*) ;;
    *) cat "$audit_tmp/log"; exit 1 ;;
  esac
  checks=$((checks+1))
done
for private_module in Syntax Connections Eval Check Univalence; do
  printf '%s\n' 'module Probe where' "import Dragonfly.Cubical.$private_module" >"$audit_tmp/Probe.hs"
  if compile_probe; then
    echo "Unexpected exposed module: $private_module"
    exit 1
  fi
  case "$(cat "$audit_tmp/log")" in
    *'hidden module'*) ;;
    *) cat "$audit_tmp/log"; exit 1 ;;
  esac
  checks=$((checks+1))
done
echo "$checks negative export checks passed."
