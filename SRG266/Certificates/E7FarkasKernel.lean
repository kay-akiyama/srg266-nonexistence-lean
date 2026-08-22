/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.E7E7Plus

/-!
# Kernel-checkable `E₇ ⊕ E₇` Farkas certificates

This module factors the expensive paired-shell evaluation through four
one-factor tables.  A generated certificate records the 28 positive-weight
evaluations for each centroid and separator component.  Lean checks those
tables against the mathematical weight formula, then performs the remaining
small exact convolution.  The soundness theorem below connects that fast
calculation to the original bounded Farkas system.
-/

open scoped BigOperators Matrix

namespace SRG266

/-- Extend evaluations on the 28 positive minuscule weights to both signs. -/
def e7SignedEvaluation
    (values : E7PairIndex → ℤ) (w : E7WeightIndex) : ℤ :=
  if w.1 then -values w.2 else values w.2

/-- The Farkas support sum evaluated from cached one-factor tables. -/
def e7FastFarkasSupport
    (leftCentroid rightCentroid leftSeparator rightSeparator :
      E7WeightIndex → ℤ)
    (countSeparator : ℤ) : ℤ :=
  ∑ w : E7ShellIndex,
    if leftCentroid w.1 + rightCentroid w.2 = 120 then
      integerPositivePart
        (countSeparator + leftSeparator w.1 + rightSeparator w.2)
    else 0

/-- The exact Farkas gap obtained from cached one-factor evaluations. -/
def e7FastFarkasGap
    (y₁ y₂ : Fin 8 → ℤ) (q : E7CentroidRow → ℤ)
    (leftCentroid rightCentroid leftSeparator rightSeparator :
      E7WeightIndex → ℤ) : ℤ :=
  integerDot q (e7CentroidTarget y₁ y₂) -
    3 * e7FastFarkasSupport leftCentroid rightCentroid
      leftSeparator rightSeparator (q .count)

/-- The eligible paired-shell count obtained from cached one-factor
evaluations. -/
def e7FastEligibleCount
    (leftCentroid rightCentroid : E7WeightIndex → ℤ) : ℕ :=
  ∑ w : E7ShellIndex,
    if leftCentroid w.1 + rightCentroid w.2 = 120 then 1 else 0

private theorem integerDot_weight4_true
    (a : Fin 8 → ℤ) (p : E7PairIndex) :
    integerDot a (e7Weight4 (true, p)) =
      -integerDot a (e7Weight4 (false, p)) := by
  simp only [integerDot]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp [e7Weight4]

theorem e7SignedEvaluation_eq_integerDot
    (a : Fin 8 → ℤ) (values : E7PairIndex → ℤ)
    (hvalues : ∀ p, values p = integerDot a (e7Weight4 (false, p))) :
    ∀ w, e7SignedEvaluation values w = integerDot a (e7Weight4 w) := by
  rintro ⟨sign, p⟩
  cases sign with
  | false => simpa [e7SignedEvaluation] using hvalues p
  | true =>
      simp only [e7SignedEvaluation, if_true]
      rw [hvalues, integerDot_weight4_true]

private def e7CentroidRowEquiv :
    E7CentroidRow ≃ Unit ⊕ (Fin 8 ⊕ Fin 8) where
  toFun
    | .count => Sum.inl ()
    | .left i => Sum.inr (Sum.inl i)
    | .right i => Sum.inr (Sum.inr i)
  invFun
    | Sum.inl _ => .count
    | Sum.inr (Sum.inl i) => .left i
    | Sum.inr (Sum.inr i) => .right i
  left_inv r := by cases r <;> rfl
  right_inv r := by rcases r with _ | (_ | _) <;> rfl

private theorem integerDot_centroidColumn
    (y₁ y₂ : Fin 8 → ℤ) (q : E7CentroidRow → ℤ)
    (w : E7EligibleIndex y₁ y₂) :
    integerDot q (fun r => e7CentroidMatrix y₁ y₂ r w) =
      q .count +
        integerDot (fun i => q (.left i)) (e7Weight4 w.1.1) +
        integerDot (fun i => q (.right i)) (e7Weight4 w.1.2) := by
  unfold integerDot
  let g : Unit ⊕ (Fin 8 ⊕ Fin 8) → ℤ
    | Sum.inl _ => q .count
    | Sum.inr (Sum.inl i) =>
        q (.left i) * e7Weight4 w.1.1 i
    | Sum.inr (Sum.inr i) =>
        q (.right i) * e7Weight4 w.1.2 i
  calc
    (∑ r, q r * e7CentroidMatrix y₁ y₂ r w) = ∑ s, g s := by
      apply Fintype.sum_equiv e7CentroidRowEquiv
      intro r
      cases r <;> simp [g, e7CentroidRowEquiv, e7CentroidMatrix]
    _ = _ := by simp [g, add_assoc]

theorem e7FarkasSupport_eq_fast
    (y₁ y₂ : Fin 8 → ℤ) (q : E7CentroidRow → ℤ)
    (leftCentroid rightCentroid leftSeparator rightSeparator :
      E7WeightIndex → ℤ)
    (hLeftCentroid : ∀ w,
      leftCentroid w = integerDot y₁ (e7Weight4 w))
    (hRightCentroid : ∀ w,
      rightCentroid w = integerDot y₂ (e7Weight4 w))
    (hLeftSeparator : ∀ w,
      leftSeparator w =
        integerDot (fun i => q (.left i)) (e7Weight4 w))
    (hRightSeparator : ∀ w,
      rightSeparator w =
        integerDot (fun i => q (.right i)) (e7Weight4 w)) :
    (∑ w : E7EligibleIndex y₁ y₂,
      integerPositivePart
        (integerDot q (fun r => e7CentroidMatrix y₁ y₂ r w))) =
      e7FastFarkasSupport leftCentroid rightCentroid
        leftSeparator rightSeparator (q .count) := by
  let columnValue : E7ShellIndex → ℤ := fun w =>
    integerPositivePart
      (q .count +
        integerDot (fun i => q (.left i)) (e7Weight4 w.1) +
        integerDot (fun i => q (.right i)) (e7Weight4 w.2))
  calc
    _ = ∑ w : E7EligibleIndex y₁ y₂, columnValue w := by
      apply Finset.sum_congr rfl
      intro w _
      simp only [columnValue]
      rw [integerDot_centroidColumn]
    _ = ∑ w : E7ShellIndex,
        if e7Eligible y₁ y₂ w then columnValue w else 0 := by
      rw [show (Finset.univ : Finset (E7EligibleIndex y₁ y₂)) =
          Finset.subtype (e7Eligible y₁ y₂)
            (Finset.univ : Finset E7ShellIndex) by
        ext w
        simp]
      rw [Finset.sum_subtype_eq_sum_filter, Finset.sum_filter]
    _ = _ := by
      unfold e7FastFarkasSupport
      apply Finset.sum_congr rfl
      intro w _
      rw [hLeftCentroid, hRightCentroid,
        hLeftSeparator, hRightSeparator]
      by_cases hw : e7Eligible y₁ y₂ w
      · have hw' : integerDot y₁ (e7Weight4 w.1) +
            integerDot y₂ (e7Weight4 w.2) = 120 := hw
        simp only [hw, hw', if_true, columnValue]
      · have hw' : ¬(integerDot y₁ (e7Weight4 w.1) +
            integerDot y₂ (e7Weight4 w.2) = 120) := hw
        simp only [hw, hw', if_false]

theorem e7EligibleCount_eq_fast
    (y₁ y₂ : Fin 8 → ℤ)
    (leftCentroid rightCentroid : E7WeightIndex → ℤ)
    (hLeftCentroid : ∀ w,
      leftCentroid w = integerDot y₁ (e7Weight4 w))
    (hRightCentroid : ∀ w,
      rightCentroid w = integerDot y₂ (e7Weight4 w)) :
    e7EligibleCount y₁ y₂ =
      e7FastEligibleCount leftCentroid rightCentroid := by
  rw [e7EligibleCount, Fintype.card_subtype, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  unfold e7FastEligibleCount
  apply Finset.sum_congr rfl
  intro w _
  rw [hLeftCentroid, hRightCentroid]
  rfl

/-- A generated Farkas record together with cached one-factor evaluations. -/
structure E7KernelCentroidCertificate where
  base : E7CentroidCertificate
  leftCentroidPositive : E7PairIndex → ℤ
  rightCentroidPositive : E7PairIndex → ℤ
  leftSeparatorPositive : E7PairIndex → ℤ
  rightSeparatorPositive : E7PairIndex → ℤ

/-- Kernel-friendly checker for a generated E7 separator certificate. -/
def E7KernelCentroidCertificate.check
    (c : E7KernelCentroidCertificate) : Bool :=
  decide (
    (∀ p, c.leftCentroidPositive p =
      integerDot c.base.y₁ (e7Weight4 (false, p))) ∧
    (∀ p, c.rightCentroidPositive p =
      integerDot c.base.y₂ (e7Weight4 (false, p))) ∧
    (∀ p, c.leftSeparatorPositive p =
      integerDot (fun i => c.base.q (.left i))
        (e7Weight4 (false, p))) ∧
    (∀ p, c.rightSeparatorPositive p =
      integerDot (fun i => c.base.q (.right i))
        (e7Weight4 (false, p))) ∧
    e7FastEligibleCount
        (e7SignedEvaluation c.leftCentroidPositive)
        (e7SignedEvaluation c.rightCentroidPositive) =
      c.base.reportedEligible ∧
    e7FastFarkasGap c.base.y₁ c.base.y₂ c.base.q
        (e7SignedEvaluation c.leftCentroidPositive)
        (e7SignedEvaluation c.rightCentroidPositive)
        (e7SignedEvaluation c.leftSeparatorPositive)
        (e7SignedEvaluation c.rightSeparatorPositive) =
      c.base.reportedGap ∧
    0 < c.base.reportedGap)

theorem E7KernelCentroidCertificate.no_bounded_solution
    (c : E7KernelCentroidCertificate) (hcheck : c.check = true) :
    ¬∃ m : E7EligibleIndex c.base.y₁ c.base.y₂ → ℤ,
      (∀ w, 0 ≤ m w) ∧
      (∀ w, m w ≤ 3) ∧
      e7CentroidMatrix c.base.y₁ c.base.y₂ *ᵥ m =
        e7CentroidTarget c.base.y₁ c.base.y₂ := by
  have h := of_decide_eq_true (by
    simpa only [E7KernelCentroidCertificate.check] using hcheck)
  rcases h with ⟨hly, hry, hlq, hrq, _, hgap, hpos⟩
  have hsly := e7SignedEvaluation_eq_integerDot
    c.base.y₁ c.leftCentroidPositive hly
  have hsry := e7SignedEvaluation_eq_integerDot
    c.base.y₂ c.rightCentroidPositive hry
  have hslq := e7SignedEvaluation_eq_integerDot
    (fun i => c.base.q (.left i)) c.leftSeparatorPositive hlq
  have hsrq := e7SignedEvaluation_eq_integerDot
    (fun i => c.base.q (.right i)) c.rightSeparatorPositive hrq
  apply no_bounded_solution_of_farkas
    (e7CentroidMatrix c.base.y₁ c.base.y₂)
    (e7CentroidTarget c.base.y₁ c.base.y₂) c.base.q
  unfold BoundedFarkasSeparates
  rw [e7FarkasSupport_eq_fast c.base.y₁ c.base.y₂ c.base.q
    _ _ _ _ hsly hsry hslq hsrq]
  rw [← hgap] at hpos
  unfold e7FastFarkasGap at hpos
  omega

end SRG266
