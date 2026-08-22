/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.A15PackingReduction

/-!
# Direct A15 realizations as bounded centroid solutions

This small interface is shared by the centroid sweep and the mined
15-profile reduction.  It contains no generated centroid-certificate data.
-/

open scoped BigOperators Matrix

namespace SRG266

set_option maxRecDepth 100000

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Multiplicities of a direct A15 shell realization, viewed as integers. -/
def A15ShellGramRealization.integerMultiplicity
    {x : V} {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d)
    (s : A15EligibleIndex d) : ℤ :=
  ((realization.toFiniteShell G).multiplicity G s : ℤ)

/-- A direct shell realization supplies the bounded integer solution tested
by a centroid Farkas certificate. -/
theorem A15ShellGramRealization.exists_centroid_bounded_solution
    (hG : IsHypothetical G) (x : V) {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d) :
    ∃ m : A15EligibleIndex d → ℤ,
      (∀ s, 0 ≤ m s) ∧
      (∀ s, m s ≤ 3) ∧
      a15CentroidMatrix d *ᵥ m = a15CentroidTarget d := by
  let finite := realization.toFiniteShell G
  let m := realization.integerMultiplicity G
  refine ⟨m, ?_, ?_, ?_⟩
  · intro s
    exact Int.natCast_nonneg _
  · intro s
    change ((finite.multiplicity G s : ℕ) : ℤ) ≤ 3
    exact_mod_cast finite.multiplicity_le_three G hG x s
  · funext row
    cases row with
    | count =>
        simp only [Matrix.mulVec, dotProduct, a15CentroidMatrix,
          a15CentroidTarget, m,
          A15ShellGramRealization.integerMultiplicity]
        simp only [one_mul]
        rw [← Nat.cast_sum,
          (realization.toFiniteShell G).sum_multiplicity G,
          secondSubconstituent_card G hG x]
        norm_num
    | coordinate i =>
        simp only [Matrix.mulVec, dotProduct, a15CentroidMatrix,
          a15CentroidTarget, m,
          A15ShellGramRealization.integerMultiplicity]
        calc
          (∑ s,
              a15ShellVector4 d s i *
                ((realization.toFiniteShell G).multiplicity G s : ℤ)) =
              ∑ s,
                ((realization.toFiniteShell G).multiplicity G s : ℤ) *
                  a15ShellVector4 d s i := by
            apply Finset.sum_congr rfl
            intro s _
            ring
          _ = ∑ B, a15ShellVector4 d (realization.shell B) i := by
            rw [(realization.toFiniteShell G).sum_multiplicity_mul G
              (fun s => a15ShellVector4 d s i)]
            simp [A15ShellGramRealization.toFiniteShell]
          _ = 11 * d i := realization.centroid i

/-- A direct A15 realization uses at least 74 distinct eligible shell
vectors.  This elementary support bound belongs in the shared realization
layer, rather than behind either enumeration implementation. -/
theorem A15ShellGramRealization.seventyFour_le_eligible_card
    (hG : IsHypothetical G) (x : V) {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d) :
    74 ≤ Fintype.card (A15EligibleIndex d) := by
  let finite := realization.toFiniteShell G
  have hsupport := finite.seventyFour_le_support_card G hG x
  calc
    74 ≤
        (Finset.univ.filter
          (fun s => 0 < finite.multiplicity G s)).card := hsupport
    _ ≤ Finset.univ.card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = Fintype.card (A15EligibleIndex d) := Finset.card_univ

end SRG266
