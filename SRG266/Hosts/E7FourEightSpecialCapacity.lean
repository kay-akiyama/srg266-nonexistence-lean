/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.E7FourEightSpecialColumns

/-!
# Column capacities for the special `4 × 8` E7 residual

The Clebsch cross-independence circuit and shell nonnegativity bound every
paired column total by fifteen.
-/

namespace SRG266
namespace E7FourEightSpecial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- First-factor vertices having positive multiplicity in one column. -/
def support (packing : E7ShellPacking d₄ d₈)
    (b : SecondWeight) : Finset FirstWeight :=
  Finset.univ.filter fun a =>
    0 < packing.multiplicity (shellEquiv (b, a))

/-- Vertices with no negative edge from a given first-factor subset. -/
def crossAllowed (s : Finset FirstWeight) : Finset FirstWeight :=
  Finset.univ.filter fun b =>
    ∀ a ∈ s, 0 ≤ e7WeightPairing2 a.1 b.1

/-- Exhaustive Clebsch cross-independence bound, checked as a 16-bit circuit. -/
theorem clebsch_cross_bound (s : Finset FirstWeight) :
    min s.card (crossAllowed s).card ≤ 5 := by
  simpa [E7FourEightSpecialCrossData.crossAllowed, crossAllowed,
    E7FourEightSpecialCrossData.d₄, d₄] using
    E7FourEightSpecialCrossData.clebsch_cross_bound_finset s

theorem paired_cross_negative
    (r : PairIndex) (a b : FirstWeight)
    (hpair : e7WeightPairing2 a.1 b.1 < 0) :
    e7ShellInner
      (shellEquiv (positiveColumn r, a)).1
      (shellEquiv (negativeColumn r, b)).1 < 0 := by
  decide +kernel +revert

theorem paired_support_subset
    (packing : E7ShellPacking d₄ d₈) (r : PairIndex) :
    support packing (negativeColumn r) ⊆
      crossAllowed (support packing (positiveColumn r)) := by
  intro b hb
  simp only [crossAllowed, Finset.mem_filter, Finset.mem_univ, true_and]
  intro a ha
  by_contra hab
  have hpair : e7WeightPairing2 a.1 b.1 < 0 := by omega
  have haPos :
      0 < packing.multiplicity
        (shellEquiv (positiveColumn r, a)) :=
    (Finset.mem_filter.mp ha).2
  have hbPos :
      0 < packing.multiplicity
        (shellEquiv (negativeColumn r, b)) :=
    (Finset.mem_filter.mp hb).2
  have hshell := paired_cross_negative r a b hpair
  exact (not_lt_of_ge
    (packing.nonnegative _ _ haPos hbPos)) hshell

theorem columnTotal_le_support
    (packing : E7ShellPacking d₄ d₈) (b : SecondWeight) :
    columnTotal packing b ≤ 3 * (support packing b).card := by
  have hsum :
      columnTotal packing b =
        ∑ a ∈ support packing b,
          packing.multiplicity (shellEquiv (b, a)) := by
    rw [columnTotal, support]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a _ ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      not_lt] at ha
    exact Nat.eq_zero_of_le_zero ha
  rw [hsum]
  calc
    (∑ a ∈ support packing b,
        packing.multiplicity (shellEquiv (b, a))) ≤
        (support packing b).card • 3 :=
      Finset.sum_le_card_nsmul _ _ _ fun a _ =>
        packing.le_three _
    _ = 3 * (support packing b).card := by
      simp
      omega

theorem paired_column_total_le_fifteen
    (packing : E7ShellPacking d₄ d₈) (r : PairIndex) :
    columnTotal packing (positiveColumn r) ≤ 15 := by
  have hsubset := Finset.card_le_card (paired_support_subset packing r)
  have hmin := clebsch_cross_bound
    (support packing (positiveColumn r))
  rw [min_le_iff] at hmin
  rcases hmin with hsmall | hallowed
  · have hcol := columnTotal_le_support packing (positiveColumn r)
    omega
  · have hneg :
        columnTotal packing (negativeColumn r) ≤
          3 * (support packing (negativeColumn r)).card :=
      columnTotal_le_support packing (negativeColumn r)
    have heq := paired_column_totals_equal packing r
    omega

end E7FourEightSpecial
end SRG266
