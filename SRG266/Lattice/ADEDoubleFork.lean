/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.ADECartanGraph

/-!
# The bounded double-fork obstruction

A tree with two vertices of degree three contains a double fork: a path
between the branch vertices, with two extra leaves at each endpoint.  Giving
weight two to the path and weight one to the four leaves is a null vector of
its simply-laced Cartan matrix.

The SRG application only uses root systems of rank at most fifteen, so the
path has between two and fifteen vertices.  We verify these fourteen tiny
integer identities directly in the Lean kernel.  This is bounded reduction
with the ordinary `decide` tactic; it uses neither `native_decide` nor
`bv_decide`.
-/

namespace SRG266
namespace Lattice

/-- The oriented relations whose symmetrization is the double-fork graph. -/
def doubleForkRel (n : ℕ) :
    (Fin n ⊕ (Fin 2 ⊕ Fin 2)) → (Fin n ⊕ (Fin 2 ⊕ Fin 2)) → Prop :=
  fun x y ↦
    match x, y with
    | Sum.inl i, Sum.inl j => (SimpleGraph.pathGraph n).Adj i j
    | Sum.inl i, Sum.inr (Sum.inl _) => i.1 = 0
    | Sum.inl i, Sum.inr (Sum.inr _) => i.1 + 1 = n
    | _, _ => False

/-- A path on `n` vertices with two leaves attached at each endpoint. -/
def doubleForkGraph (n : ℕ) : SimpleGraph (Fin n ⊕ (Fin 2 ⊕ Fin 2)) :=
  SimpleGraph.fromRel (doubleForkRel n)

/-- The affine-D null weighting: two on the central path and one on every
leaf. -/
def doubleForkWeight {n : ℕ} : Fin n ⊕ (Fin 2 ⊕ Fin 2) → ℤ
  | Sum.inl _ => 2
  | Sum.inr _ => 1

set_option maxHeartbeats 2000000

/-- Every double fork which can occur in rank at most fifteen has zero Cartan
energy. -/
theorem doubleFork_cartanEnergy_zero (n : ℕ) (hnlo : 2 ≤ n) (hnhi : n ≤ 15) :
    graphCartanEnergy (doubleForkGraph n) doubleForkWeight = 0 := by
  interval_cases n <;>
    norm_num [graphCartanEnergy, Matrix.toBilin'_apply, graphCartanMatrix,
      doubleForkGraph, doubleForkWeight, SimpleGraph.fromRel_adj,
      doubleForkRel, SimpleGraph.pathGraph_adj, Fin.sum_univ_succ] <;>
    decide

set_option maxHeartbeats 200000

end Lattice
end SRG266
