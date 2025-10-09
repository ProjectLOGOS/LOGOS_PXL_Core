#!/usr/bin/env bash
set -euo pipefail

fail=0

echo "[policy] scanning for Admitted. under modules/IEL ..."
if grep -R -nE '\\bAdmitted\\s*\\.' modules/IEL ; then
  echo "::error::Admitted. found under modules/IEL" >&2
  fail=1
else
  echo "[policy] OK: no Admitted. under modules/IEL"
fi

echo "[policy] scanning for Add LoadPath under modules/IEL ..."
if grep -RIn --include="*.v" '\bAdd[[:space:]]+LoadPath\b' modules/IEL/ ; then
  echo "::error::Add LoadPath found under modules/IEL (use -Q in _CoqProject)" >&2
  fail=1
else
  echo "[policy] OK: no Add LoadPath under modules/IEL"
fi

echo "[policy] scanning for Axiom in source/pillars ..."
if grep -R -nE '\\bAxiom\\b' modules/IEL/source modules/IEL/pillars ; then
  echo "::error::Axiom found in source/pillars" >&2
  fail=1
else
  echo "[policy] OK: no Axiom in source/pillars"
fi

echo "[policy] scanning for Axiom outside infra/ChronoPraxis ..."
if grep -R -nE '\\bAxiom\\b' modules/IEL/infra | grep -v 'infra/ChronoPraxis' ; then
  echo "::error::Axiom found outside infra/ChronoPraxis" >&2
  fail=1
else
  echo "[policy] OK: Axiom only in infra/ChronoPraxis"
fi

exit "${fail}"