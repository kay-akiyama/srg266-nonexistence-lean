/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.ShellGram
import SRG266.Hosts.E7ResidualElimination
import SRG266.Certificates.E7PairingRows

/-!
# From an E7 Gram realization to a residual shell packing

The residual E7 eliminations use the aggregated structure `E7ShellPacking`.
This module supplies the missing host-independent bridge from a direct
coordinate realization indexed by the 220 local Gram occurrences.

Fiber counting and the weighted profile are delegated to `ShellGram`; only
the two E7 centroid equations remain host-specific.
-/

open scoped BigOperators

namespace SRG266

set_option maxRecDepth 100000

universe u

theorem e7WeightPairing2_le_three
    (u v : E7WeightIndex) :
    e7WeightPairing2 u v ≤ 3 := by
  exact (e7WeightPairing2_le_three_and_eq_three u v).1

theorem e7WeightPairing2_eq_three_iff
    (u v : E7WeightIndex) :
    e7WeightPairing2 u v = 3 ↔ u = v := by
  exact (e7WeightPairing2_le_three_and_eq_three u v).2

/-- Inner product three detects equality in the paired minuscule shell. -/
theorem e7ShellInner_eq_three_iff
    (u v : E7ShellIndex) :
    e7ShellInner u v = 3 ↔ u = v := by
  constructor
  · intro hinner
    have hleft := e7WeightPairing2_le_three u.1 v.1
    have hright := e7WeightPairing2_le_three u.2 v.2
    have hleftEq : e7WeightPairing2 u.1 v.1 = 3 := by
      unfold e7ShellInner at hinner
      omega
    have hrightEq : e7WeightPairing2 u.2 v.2 = 3 := by
      unfold e7ShellInner at hinner
      omega
    exact Prod.ext
      ((e7WeightPairing2_eq_three_iff u.1 v.1).mp hleftEq)
      ((e7WeightPairing2_eq_three_iff u.2 v.2).mp hrightEq)
  · rintro rfl
    have hleft : e7WeightPairing2 u.1 u.1 = 3 :=
      (e7WeightPairing2_eq_three_iff u.1 u.1).2 rfl
    have hright : e7WeightPairing2 u.2 u.2 = 3 :=
      (e7WeightPairing2_eq_three_iff u.2 u.2).2 rfl
    unfold e7ShellInner
    rw [hleft, hright]
    norm_num

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A direct realization of the local Gram occurrences in one residual E7
shell, together with the two coordinate centroid equations. -/
structure E7ShellGramRealization
    (x : V) (d₁ d₂ : Fin 8 → ℤ) where
  shell :
    SecondSubconstituent G x → E7ResidualEligibleIndex d₁ d₂
  gram :
    ∀ B C, e7ShellInner (shell B).1 (shell C).1 =
      localGramMatrix G x B C
  leftCentroid :
    ∀ i, ∑ B, e7Weight4 (shell B).1.1 i = 110 * d₁ i
  rightCentroid :
    ∀ i, ∑ B, e7Weight4 (shell B).1.2 i = 110 * d₂ i

def E7ShellGramRealization.toFiniteShell
    {x : V} {d₁ d₂ : Fin 8 → ℤ}
    (realization : E7ShellGramRealization G x d₁ d₂) :
    FiniteShellGramRealization G x
      (E7ResidualEligibleIndex d₁ d₂)
      (fun u v => e7ShellInner u.1 v.1) where
  shell := realization.shell
  gram := realization.gram
  eq_of_inner_eq_three := by
    intro u v huv
    exact Subtype.ext ((e7ShellInner_eq_three_iff u.1 v.1).mp huv)

/-- A direct residual E7 realization uses at least 74 distinct eligible shell
vectors.  This is the residual-E7 specialization of the shared support bound
for 220 local occurrences with fibers of size at most three. -/
theorem E7ShellGramRealization.seventyFour_le_eligible_card
    (hG : IsHypothetical G) (x : V) {d₁ d₂ : Fin 8 → ℤ}
    (realization : E7ShellGramRealization G x d₁ d₂) :
    74 ≤ Fintype.card (E7ResidualEligibleIndex d₁ d₂) := by
  let finite := realization.toFiniteShell G
  calc
    74 ≤
        (Finset.univ.filter
          (fun s => 0 < finite.multiplicity G s)).card :=
      finite.seventyFour_le_support_card G hG x
    _ ≤ Finset.univ.card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = Fintype.card (E7ResidualEligibleIndex d₁ d₂) := Finset.card_univ

/-- Aggregate a direct E7 realization into the packing consumed by all five
canonical residual eliminations. -/
def E7ShellGramRealization.toPacking
    (hG : IsHypothetical G) (x : V) {d₁ d₂ : Fin 8 → ℤ}
    (realization : E7ShellGramRealization G x d₁ d₂) :
    E7ShellPacking d₁ d₂ := by
  let finite := realization.toFiniteShell G
  exact
    { multiplicity := finite.multiplicity G
      le_three := finite.multiplicity_le_three G hG x
      total := by
        rw [finite.sum_multiplicity G,
          secondSubconstituent_card G hG x]
      leftCentroid := by
        intro i
        rw [finite.sum_multiplicity_mul G
          (fun w => e7Weight4 w.1.1 i)]
        exact realization.leftCentroid i
      rightCentroid := by
        intro i
        rw [finite.sum_multiplicity_mul G
          (fun w => e7Weight4 w.1.2 i)]
        exact realization.rightCentroid i
      twoProfile := finite.twoProfile G hG x
      nonnegative := finite.nonnegative G hG x }

/-- A direct realization at any of the five canonical profiles is
impossible. -/
theorem no_e7ResidualCanonical_realization
    (hG : IsHypothetical G) (x : V) (t : E7ResidualType) :
    IsEmpty
      (E7ShellGramRealization G x
        (e7ResidualCanonical t).1 (e7ResidualCanonical t).2) := by
  refine ⟨fun realization => ?_⟩
  exact
    (no_e7ResidualCanonical_packing t).false
      (realization.toPacking G hG x)

end SRG266
