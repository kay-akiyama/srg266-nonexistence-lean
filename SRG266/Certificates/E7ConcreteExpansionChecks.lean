/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.E7ConcreteExpansionDefs
import SRG266.Hosts.E7CentroidKeyCodes

/-!
# Finite checks behind the concrete E7 profile expansion

Every statement in this module is one bounded kernel evaluation.  None of them
touches the 120,036-leaf magnitude search: the search is handled by the
filtering sweep of `SRG266/Certificates/E7ConcreteFilterAssembly.lean`, and
what remains here are literal lookups over the 37 listed component codes, the
335 surviving profiles and the 956 listed centroid profile pairs.
-/

namespace SRG266

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

/-- The listed component codes are exactly the codes stored in the tree. -/
theorem e7ConcreteKeyCodeTree_toList :
    e7ConcreteKeyCodeTree.toList = e7ConcreteKeyCodes := by
  decide +kernel

/-- Every listed component code is a proper packed code. -/
theorem e7ConcreteKeyCodes_lt :
    ∀ code ∈ e7ConcreteKeyCodes, code < e7NormBase * e7CodeBase ^ 43 := by
  decide +kernel

/-- Every listed component code is found by the tree. -/
theorem e7ConcreteKeyCodeTree_contains :
    ∀ code ∈ e7ConcreteKeyCodes, e7ConcreteKeyCodeTree.contains code = true := by
  decide +kernel

/-- The squared norm of every listed component code is found by the norm
tree. -/
theorem e7ConcreteNormTree_contains :
    ∀ code ∈ e7ConcreteKeyCodes,
      e7ConcreteNormTree.contains (code % e7NormBase) = true := by
  decide +kernel

/-- Every squared norm stored in the norm tree is small. -/
theorem e7ConcreteNormTree_lt :
    ∀ norm ∈ e7ConcreteNormTree.toList, norm < e7NormBase := by
  decide +kernel

/-- The listed fibre table describes the surviving profiles. -/
theorem e7ConcreteFibreTable_checked :
    ∀ entry ∈ e7ConcreteFibreTable, e7ConcreteFibre entry.1 = entry.2 := by
  decide +kernel

/-- The listed fibre table has an entry for every listed component code. -/
theorem e7ConcreteFibreTable_isSome :
    ∀ code ∈ e7ConcreteKeyCodes,
      (e7ConcreteFibreTable.find? fun entry => decide (entry.1 = code)).isSome
        = true := by
  decide +kernel

/-- Both components of a listed key pair are listed component codes. -/
theorem e7ConcreteCodePairs_codes :
    ∀ codes ∈ e7ConcreteCodePairs,
      codes.1 ∈ e7ConcreteKeyCodes ∧ codes.2 ∈ e7ConcreteKeyCodes := by
  decide +kernel

/-- Every listed key pair is a pair of packed codes of listed centroid
profiles. -/
theorem e7ConcreteCodePairs_mem_centroid :
    ∀ pair ∈ e7ConcreteCodePairs, pair ∈ e7ListedCentroidKeyCodePairs := by
  decide +kernel

/-- Every packed code pair of a listed centroid profile is listed. -/
theorem e7CentroidKeyCodePairs_mem_concrete :
    ∀ pair ∈ e7ListedCentroidKeyCodePairs, pair ∈ e7ConcreteCodePairs := by
  decide +kernel

/-- Every listed centroid profile has a squared norm below `e7NormBase`. -/
theorem e7ListedCentroidCodeOk_checked : e7ListedCentroidCodeOk = true := by
  decide +kernel

end SRG266
