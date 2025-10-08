#!/usr/bin/env bash
set -euo pipefail

fail=0

echo "[policy] scanning for Admitted. under modules/IEL ..."
if grep -RIn --include="*.v" '\bAdmitted\.' modules/IEL/ | grep -v '\(\*.*TODO.*\)\|\(\*.*remove.*Admitted\)' ; then
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

exit "${fail}"