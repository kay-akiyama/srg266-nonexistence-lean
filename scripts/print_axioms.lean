/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.FractionalNearFrameMain

/-!
# Axiom report for the headline theorem

```
lake env lean scripts/print_axioms.lean
```

prints the axioms `SRG266.srg266_nonexistence` rests on.  The expected report
is `[propext, Classical.choice, Quot.sound]` -- the three standard axioms
routinely used by Mathlib, and nothing else.  In particular `ofReduceBool`
must not appear: it is what `native_decide` adds, and this development uses
`decide +kernel` throughout so that every certificate is replayed by the
kernel rather than by compiled code.

The bridge theorems are reported too, so the report also witnesses that the
statement being proved is the intended one.
-/

#print axioms SRG266.isHypothetical_iff
#print axioms SRG266.srg266_nonexistence_of_noResidualCherryCover
#print axioms SRG266.srg266_nonexistence
