/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7ScalarDP
import SRG266.Hosts.E7CentroidProfiles

/-!
# Interface for the E7 scalar-DP and trace audit

The trace-filtered output of the bounded scalar dynamic program is contained
in the 956 listed centroid profile pairs.  That inclusion is the only fact the
elimination chain uses, and it is discharged by
`SRG266/Hosts/E7ScalarDPInstance.lean`.

`e7ScalarAuditSummary` records the counts (107 scalar-feasible pairs, 43 after
the trace filter, 43 listed keys). It is an untrusted diagnostic: all four
fields route through `List.mergeSort`, which is
defined by well-founded recursion and therefore has no definitional unfolding,
so no kernel evaluation can reach them.
-/

namespace SRG266

def e7HistogramPairLe
    (a b : E7ComponentKey × E7ComponentKey) : Bool :=
  match compare a.1 b.1 with
  | .lt => true
  | .eq => (compare a.2 b.2).isLE
  | .gt => false

def e7ListedCentroidHistogramPairsUpToSwap :
    List (E7ComponentKey × E7ComponentKey) :=
  e7DedupAdjacent <|
    (e7ListedCentroidProfiles.flatMap fun pair =>
      let keys :=
        (e7ComponentKey (Array.ofFn pair.1),
          e7ComponentKey (Array.ofFn pair.2))
      [keys, (keys.2, keys.1)]).mergeSort
      e7HistogramPairLe

structure E7ScalarAuditSummary where
  scalarCount : ℕ
  traceCount : ℕ
  listedKeyCount : ℕ
  sameTraceKeys : Bool
  deriving DecidableEq

def e7ScalarAuditSummary : E7ScalarAuditSummary :=
  let scalar :=
    e7EligibleHistogramPairs.filter e7ScalarDPFeasible
  let trace :=
    scalar.filter fun pair =>
      decide (38 ≤ pair.1.norm ∧ pair.1.norm ≤ 262)
  { scalarCount := scalar.length
    traceCount := trace.length
    listedKeyCount := e7ListedCentroidHistogramPairsUpToSwap.length
    sameTraceKeys :=
      decide (
        trace.toFinset =
          e7ListedCentroidHistogramPairsUpToSwap.toFinset) }

/-- Every trace-filtered scalar-feasible histogram pair is one of the listed
centroid histogram pairs, up to exchange of the two E₇ factors. -/
class E7ScalarDPAuditInput : Prop where
  trace_subset :
    ∀ pair : E7ComponentKey × E7ComponentKey,
      pair ∈ e7TraceFeasibleHistogramPairs →
      pair ∈ e7ListedCentroidHistogramPairsUpToSwap

end SRG266
