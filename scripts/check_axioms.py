"""Check the output of `lake env lean scripts/CheckAxioms.lean`.

Every `#print axioms` line in the Lean file must produce one report, and each report may list only
Lean's standard axioms. `sorry` shows up as the axiom `sorryAx`, so it fails here too.
"""

import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

output = open(sys.argv[1]).read()
expected = re.findall(r"^#print axioms (\S+)", open(sys.argv[2]).read(), re.M)

failures = []
for name in expected:
    short = re.escape(name)
    if re.search(rf"'{short}' does not depend on any axioms", output):
        continue
    match = re.search(rf"'{short}' depends on axioms: \[(.*?)\]", output, re.S)
    if not match:
        failures.append(f"{name}: no axiom report")
        continue
    used = {a.strip() for a in match.group(1).split(",") if a.strip()}
    if used - ALLOWED:
        failures.append(f"{name}: uses {sorted(used - ALLOWED)}")

if failures:
    print("Axiom check failed:")
    print("\n".join("  " + f for f in failures))
    sys.exit(1)
print(f"Axiom check passed: {len(expected)} theorems use only {sorted(ALLOWED)}.")
