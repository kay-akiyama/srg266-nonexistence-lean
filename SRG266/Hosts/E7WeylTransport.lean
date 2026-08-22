/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7PackingReduction
import SRG266.Hosts.E7E7Plus
import SRG266.Hosts.E7WeylTransportCore

/-!
# Checked Weyl transport on the E7 minuscule shell

The survivor certificate contains explicit root-reflection paths for the two
centroid components.  This module reconstructs the induced permutation of
the 56 minuscule weights for every supplied root.

The reflective checker verifies the cleared reflection formula and that the
resulting map is an involution.  Native algebra then proves preservation of
the exact weight pairing.  Later transport lemmas use the same cleared
formula to move centroid equations without trusting Python orbit labels.
-/

open scoped BigOperators

namespace SRG266

set_option maxRecDepth 100000

theorem e7ReflectionTransportCheck.isRoot
    {a : Fin 8 → ℤ}
    (hcheck : e7ReflectionTransportCheck a = true) :
    e7IsRoot a = true := by
  have hparts :
      e7IsRoot a = true ∧
        decide (
          (∀ u, e7WeightReflects a u (e7ReflectedWeight a u)) ∧
          ∀ u, e7ReflectedWeight a (e7ReflectedWeight a u) = u) =
          true := by
    simpa only [e7ReflectionTransportCheck, Bool.and_eq_true] using hcheck
  exact hparts.1

theorem e7ReflectionTransportCheck.reflects
    {a : Fin 8 → ℤ}
    (hcheck : e7ReflectionTransportCheck a = true) :
    ∀ u, e7WeightReflects a u (e7ReflectedWeight a u) := by
  have hparts :
      e7IsRoot a = true ∧
        decide (
          (∀ u, e7WeightReflects a u (e7ReflectedWeight a u)) ∧
          ∀ u, e7ReflectedWeight a (e7ReflectedWeight a u) = u) =
          true := by
    simpa only [e7ReflectionTransportCheck, Bool.and_eq_true] using hcheck
  exact (of_decide_eq_true hparts.2).1

theorem e7ReflectionTransportCheck.involution
    {a : Fin 8 → ℤ}
    (hcheck : e7ReflectionTransportCheck a = true) :
    ∀ u, e7ReflectedWeight a (e7ReflectedWeight a u) = u := by
  have hparts :
      e7IsRoot a = true ∧
        decide (
          (∀ u, e7WeightReflects a u (e7ReflectedWeight a u)) ∧
          ∀ u, e7ReflectedWeight a (e7ReflectedWeight a u) = u) =
          true := by
    simpa only [e7ReflectionTransportCheck, Bool.and_eq_true] using hcheck
  exact (of_decide_eq_true hparts.2).2

/-- The checked weight map as an actual equivalence. -/
def e7ReflectedWeightEquiv
    (a : Fin 8 → ℤ)
    (hcheck : e7ReflectionTransportCheck a = true) :
    E7WeightIndex ≃ E7WeightIndex where
  toFun := e7ReflectedWeight a
  invFun := e7ReflectedWeight a
  left_inv := e7ReflectionTransportCheck.involution hcheck
  right_inv := e7ReflectionTransportCheck.involution hcheck

theorem e7ReflectionTransportCheck.root_norm
    {a : Fin 8 → ℤ}
    (hcheck : e7ReflectionTransportCheck a = true) :
    integerDot a a = 8 := by
  have hroot :
      (∑ i, a i) = 0 ∧
      integerDot a a = 8 ∧
      ∀ i, a i % 2 = a 0 % 2 :=
    of_decide_eq_true
      (e7ReflectionTransportCheck.isRoot hcheck)
  exact hroot.2.1

/-- Cleared reflection formula for arbitrary doubled-coordinate vectors. -/
def e7VectorReflects
    (a u v : Fin 8 → ℤ) : Prop :=
  ∀ i, 4 * v i = 4 * u i - integerDot u a * a i

theorem e7Reflect?_vectorReflects
    {a u v : Fin 8 → ℤ}
    (hreflect : e7Reflect? u a = some v) :
    e7VectorReflects a u v := by
  unfold e7Reflect? at hreflect
  split at hreflect
  next hroot =>
    dsimp at hreflect
    split at hreflect
    next hdiv =>
      simp only [Option.some.injEq] at hreflect
      subst v
      intro i
      have hdvd : (4 : ℤ) ∣ integerDot u a :=
        Int.dvd_iff_emod_eq_zero.mpr hdiv
      have hcancel :
          integerDot u a / 4 * 4 = integerDot u a :=
        Int.ediv_mul_cancel hdvd
      have hterm :
          4 * ((integerDot u a / 4) * a i) =
            integerDot u a * a i := by
        calc
          4 * ((integerDot u a / 4) * a i) =
              (integerDot u a / 4 * 4) * a i := by ring
          _ = integerDot u a * a i := by rw [hcancel]
      rw [mul_sub, hterm]
    next =>
      simp at hreflect
  next =>
    simp at hreflect

/-- A root reflection preserves the integral dot product whenever both
vectors satisfy the cleared reflection formula. -/
theorem e7VectorReflects_dot
    {a u u' v v' : Fin 8 → ℤ}
    (hnorm : integerDot a a = 8)
    (hu : e7VectorReflects a u u')
    (hv : e7VectorReflects a v v') :
    integerDot u' v' = integerDot u v := by
  have hscaled :
      16 * integerDot u' v' = 16 * integerDot u v := by
    have h00 :
        (∑ i, (4 * u i) * (4 * v i)) =
          16 * integerDot u v := by
      unfold integerDot
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h01 :
        (∑ i, (4 * u i) * (integerDot v a * a i)) =
          4 * integerDot v a * integerDot u a := by
      unfold integerDot
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h10 :
        (∑ i, (integerDot u a * a i) * (4 * v i)) =
          4 * integerDot u a * integerDot v a := by
      unfold integerDot
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h11 :
        (∑ i, (integerDot u a * a i) *
          (integerDot v a * a i)) =
          integerDot u a * integerDot v a * integerDot a a := by
      unfold integerDot
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    unfold integerDot
    calc
      16 * (∑ i, u' i * v' i) =
          ∑ i, (4 * u' i) * (4 * v' i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i,
          (4 * u i - integerDot u a * a i) *
            (4 * v i - integerDot v a * a i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hu i, hv i]
      _ = 16 * (∑ i, u i * v i) := by
        simp_rw [sub_mul, mul_sub]
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          Finset.sum_sub_distrib, h00, h01, h10, h11, hnorm]
        unfold integerDot
        ring
  omega

private theorem e7_four_dot_of_reflects
    {a : Fin 8 → ℤ} {u v : E7WeightIndex}
    (huv : e7WeightReflects a u v) :
    ∀ i, 4 * e7Weight4 v i =
      4 * e7Weight4 u i -
        integerDot (e7Weight4 u) a * a i :=
  huv

/-- The checked reflection preserves the exact doubled E7 weight pairing. -/
theorem e7ReflectedWeight_pairing
    {a : Fin 8 → ℤ}
    (hcheck : e7ReflectionTransportCheck a = true)
    (u v : E7WeightIndex) :
    e7WeightPairing2
        (e7ReflectedWeight a u) (e7ReflectedWeight a v) =
      e7WeightPairing2 u v := by
  let u' := e7ReflectedWeight a u
  let v' := e7ReflectedWeight a v
  have hu := e7_four_dot_of_reflects
    (e7ReflectionTransportCheck.reflects hcheck u)
  have hv := e7_four_dot_of_reflects
    (e7ReflectionTransportCheck.reflects hcheck v)
  have hnorm := e7ReflectionTransportCheck.root_norm hcheck
  have hscaled :
      16 * integerDot (e7Weight4 u') (e7Weight4 v') =
        16 * integerDot (e7Weight4 u) (e7Weight4 v) := by
    have h00 :
        (∑ i, (4 * e7Weight4 u i) *
          (4 * e7Weight4 v i)) =
          16 * integerDot (e7Weight4 u) (e7Weight4 v) := by
      unfold integerDot
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h01 :
        (∑ i, (4 * e7Weight4 u i) *
          (integerDot (e7Weight4 v) a * a i)) =
          4 * integerDot (e7Weight4 v) a *
            integerDot (e7Weight4 u) a := by
      unfold integerDot
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h10 :
        (∑ i, (integerDot (e7Weight4 u) a * a i) *
          (4 * e7Weight4 v i)) =
          4 * integerDot (e7Weight4 u) a *
            integerDot (e7Weight4 v) a := by
      unfold integerDot
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h11 :
        (∑ i, (integerDot (e7Weight4 u) a * a i) *
          (integerDot (e7Weight4 v) a * a i)) =
          integerDot (e7Weight4 u) a *
            integerDot (e7Weight4 v) a * integerDot a a := by
      unfold integerDot
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp only [integerDot]
    calc
      16 * (∑ i, e7Weight4 u' i * e7Weight4 v' i) =
          ∑ i, (4 * e7Weight4 u' i) *
            (4 * e7Weight4 v' i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i,
          (4 * e7Weight4 u i -
              integerDot (e7Weight4 u) a * a i) *
            (4 * e7Weight4 v i -
              integerDot (e7Weight4 v) a * a i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hu i, hv i]
      _ = 16 * (∑ i, e7Weight4 u i * e7Weight4 v i) := by
        simp_rw [sub_mul, mul_sub]
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          Finset.sum_sub_distrib, h00, h01, h10, h11, hnorm]
        unfold integerDot
        ring
  unfold e7WeightPairing2
  have hdot :
      integerDot (e7Weight4 u') (e7Weight4 v') =
        integerDot (e7Weight4 u) (e7Weight4 v) := by
    omega
  rw [hdot]

/-- A checked root reflection gives an equivalence between the corresponding
left-reflected residual shells. -/
def e7ResidualReflectLeftEquiv
    {a d₁ d₁' d₂ : Fin 8 → ℤ}
    (hcheck : e7ReflectionTransportCheck a = true)
    (hd : e7Reflect? d₁ a = some d₁') :
    E7ResidualEligibleIndex d₁ d₂ ≃
      E7ResidualEligibleIndex d₁' d₂ :=
  ((e7ReflectedWeightEquiv a hcheck).prodCongr
    (Equiv.refl E7WeightIndex)).subtypeEquiv fun w => by
      have hdot :
          integerDot d₁'
              (e7Weight4 (e7ReflectedWeight a w.1)) =
            integerDot d₁ (e7Weight4 w.1) :=
        e7VectorReflects_dot
          (e7ReflectionTransportCheck.root_norm hcheck)
          (e7Reflect?_vectorReflects hd)
          (e7ReflectionTransportCheck.reflects hcheck w.1)
      change e7ResidualEligible d₁ d₂ w ↔
        e7ResidualEligible d₁' d₂
          (e7ReflectedWeight a w.1, w.2)
      unfold e7ResidualEligible e7ResidualEvaluation
      rw [hdot]

/-- Right-factor version of `e7ResidualReflectLeftEquiv`. -/
def e7ResidualReflectRightEquiv
    {a d₁ d₂ d₂' : Fin 8 → ℤ}
    (hcheck : e7ReflectionTransportCheck a = true)
    (hd : e7Reflect? d₂ a = some d₂') :
    E7ResidualEligibleIndex d₁ d₂ ≃
      E7ResidualEligibleIndex d₁ d₂' :=
  ((Equiv.refl E7WeightIndex).prodCongr
    (e7ReflectedWeightEquiv a hcheck)).subtypeEquiv fun w => by
      have hdot :
          integerDot d₂'
              (e7Weight4 (e7ReflectedWeight a w.2)) =
            integerDot d₂ (e7Weight4 w.2) :=
        e7VectorReflects_dot
          (e7ReflectionTransportCheck.root_norm hcheck)
          (e7Reflect?_vectorReflects hd)
          (e7ReflectionTransportCheck.reflects hcheck w.2)
      change e7ResidualEligible d₁ d₂ w ↔
        e7ResidualEligible d₁ d₂'
          (w.1, e7ReflectedWeight a w.2)
      unfold e7ResidualEligible e7ResidualEvaluation
      rw [hdot]

/-- Swapping the two factors preserves the residual eligible shell. -/
def e7ResidualSwapEquiv (d₁ d₂ : Fin 8 → ℤ) :
    E7ResidualEligibleIndex d₁ d₂ ≃
      E7ResidualEligibleIndex d₂ d₁ :=
  (Equiv.prodComm E7WeightIndex E7WeightIndex).subtypeEquiv fun w => by
    change e7ResidualEligible d₁ d₂ w ↔
      e7ResidualEligible d₂ d₁ (w.2, w.1)
    unfold e7ResidualEligible
    simp only [add_comm]

/-- A checked reflection list preserves the eligible-shell cardinality in
the left factor. -/
theorem e7Residual_card_applyReflections_left
    {d₁ d₁' d₂ : Fin 8 → ℤ}
    (roots : List (Fin 8 → ℤ))
    (hchecks : roots.all e7ReflectionTransportCheck = true)
    (happly : e7ApplyReflections d₁ roots = some d₁') :
    Fintype.card (E7ResidualEligibleIndex d₁ d₂) =
      Fintype.card (E7ResidualEligibleIndex d₁' d₂) := by
  induction roots generalizing d₁ with
  | nil =>
      simp only [e7ApplyReflections, Option.some.injEq] at happly
      subst d₁'
      rfl
  | cons a roots ih =>
      have hparts :
          e7ReflectionTransportCheck a = true ∧
            roots.all e7ReflectionTransportCheck = true := by
        simpa only [List.all_cons, Bool.and_eq_true] using hchecks
      simp only [e7ApplyReflections] at happly
      cases hreflect : e7Reflect? d₁ a with
      | none => simp [hreflect] at happly
      | some next =>
          have htail : e7ApplyReflections next roots = some d₁' := by
            simpa [hreflect] using happly
          calc
            _ = Fintype.card (E7ResidualEligibleIndex next d₂) :=
              Fintype.card_congr
                (e7ResidualReflectLeftEquiv hparts.1 hreflect)
            _ = _ := ih hparts.2 htail

/-- Right-factor version of
`e7Residual_card_applyReflections_left`. -/
theorem e7Residual_card_applyReflections_right
    {d₁ d₂ d₂' : Fin 8 → ℤ}
    (roots : List (Fin 8 → ℤ))
    (hchecks : roots.all e7ReflectionTransportCheck = true)
    (happly : e7ApplyReflections d₂ roots = some d₂') :
    Fintype.card (E7ResidualEligibleIndex d₁ d₂) =
      Fintype.card (E7ResidualEligibleIndex d₁ d₂') := by
  induction roots generalizing d₂ with
  | nil =>
      simp only [e7ApplyReflections, Option.some.injEq] at happly
      subst d₂'
      rfl
  | cons a roots ih =>
      have hparts :
          e7ReflectionTransportCheck a = true ∧
            roots.all e7ReflectionTransportCheck = true := by
        simpa only [List.all_cons, Bool.and_eq_true] using hchecks
      simp only [e7ApplyReflections] at happly
      cases hreflect : e7Reflect? d₂ a with
      | none => simp [hreflect] at happly
      | some next =>
          have htail : e7ApplyReflections next roots = some d₂' := by
            simpa [hreflect] using happly
          calc
            _ = Fintype.card (E7ResidualEligibleIndex d₁ next) :=
              Fintype.card_congr
                (e7ResidualReflectRightEquiv hparts.1 hreflect)
            _ = _ := ih hparts.2 htail

/-- Certificate-scale and residual eligibility agree when division by five
and the two one-factor divisions by eight are exact. -/
theorem e7Eligible_iff_residual_of_factor_audits
    (y₁ y₂ : Fin 8 → ℤ)
    (hdiv₁ : ∀ i, y₁ i % 5 = 0)
    (hdiv₂ : ∀ i, y₂ i % 5 = 0)
    (heval₁ : ∀ w : E7WeightIndex,
      integerDot (fun i => y₁ i / 5) (e7Weight4 w) % 8 = 0)
    (heval₂ : ∀ w : E7WeightIndex,
      integerDot (fun i => y₂ i / 5) (e7Weight4 w) % 8 = 0)
    (w : E7ShellIndex) :
    e7Eligible y₁ y₂ w ↔
      e7ResidualEligible (fun i => y₁ i / 5) (fun i => y₂ i / 5) w := by
  let a := integerDot (fun i => y₁ i / 5) (e7Weight4 w.1)
  let b := integerDot (fun i => y₂ i / 5) (e7Weight4 w.2)
  have hscale₁ : integerDot y₁ (e7Weight4 w.1) = 5 * a := by
    simp only [integerDot, a]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hcancel := Int.ediv_mul_cancel
      (Int.dvd_iff_emod_eq_zero.mpr (hdiv₁ i))
    calc
      y₁ i * e7Weight4 w.1 i =
          (y₁ i / 5 * 5) * e7Weight4 w.1 i := by rw [hcancel]
      _ = 5 * (y₁ i / 5 * e7Weight4 w.1 i) := by ring
  have hscale₂ : integerDot y₂ (e7Weight4 w.2) = 5 * b := by
    simp only [integerDot, b]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hcancel := Int.ediv_mul_cancel
      (Int.dvd_iff_emod_eq_zero.mpr (hdiv₂ i))
    calc
      y₂ i * e7Weight4 w.2 i =
          (y₂ i / 5 * 5) * e7Weight4 w.2 i := by rw [hcancel]
      _ = 5 * (y₂ i / 5 * e7Weight4 w.2 i) := by ring
  have ha := Int.ediv_mul_cancel
    (Int.dvd_iff_emod_eq_zero.mpr (heval₁ w.1))
  have hb := Int.ediv_mul_cancel
    (Int.dvd_iff_emod_eq_zero.mpr (heval₂ w.2))
  unfold e7Eligible e7ResidualEligible e7ResidualEvaluation
  rw [hscale₁, hscale₂]
  constructor <;> intro h <;> nlinarith

/-- The preceding pointwise equivalence as an equivalence of finite shell
types, used to transport their cardinalities. -/
def e7CentroidResidualEquivOfFactorAudits
    (y₁ y₂ : Fin 8 → ℤ)
    (hdiv₁ : ∀ i, y₁ i % 5 = 0)
    (hdiv₂ : ∀ i, y₂ i % 5 = 0)
    (heval₁ : ∀ w : E7WeightIndex,
      integerDot (fun i => y₁ i / 5) (e7Weight4 w) % 8 = 0)
    (heval₂ : ∀ w : E7WeightIndex,
      integerDot (fun i => y₂ i / 5) (e7Weight4 w) % 8 = 0) :
    E7EligibleIndex y₁ y₂ ≃
      E7ResidualEligibleIndex (fun i => y₁ i / 5) (fun i => y₂ i / 5) :=
  (Equiv.refl E7ShellIndex).subtypeEquiv
    (e7Eligible_iff_residual_of_factor_audits
      y₁ y₂ hdiv₁ hdiv₂ heval₁ heval₂)

private theorem e7_reflected_centroid
    {ι : Type*} [Fintype ι]
    {a d d' : Fin 8 → ℤ}
    (hcheck : e7ReflectionTransportCheck a = true)
    (hd : e7Reflect? d a = some d')
    (weight : ι → E7WeightIndex)
    (hcentroid : ∀ i,
      ∑ k, e7Weight4 (weight k) i = 110 * d i) :
    ∀ i, ∑ k, e7Weight4 (e7ReflectedWeight a (weight k)) i =
      110 * d' i := by
  intro i
  have hdvector := e7Reflect?_vectorReflects hd
  have hsumdot :
      (∑ k, integerDot (e7Weight4 (weight k)) a) =
        110 * integerDot d a := by
    unfold integerDot
    calc
      (∑ k, ∑ j, e7Weight4 (weight k) j * a j) =
          ∑ j, ∑ k, e7Weight4 (weight k) j * a j := by
        rw [Finset.sum_comm]
      _ = ∑ j, (∑ k, e7Weight4 (weight k) j) * a j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
      _ = ∑ j, (110 * d j) * a j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hcentroid j]
      _ = 110 * ∑ j, d j * a j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hscaled :
      4 * (∑ k,
          e7Weight4 (e7ReflectedWeight a (weight k)) i) =
        4 * (110 * d' i) := by
    calc
      4 * (∑ k,
          e7Weight4 (e7ReflectedWeight a (weight k)) i) =
          ∑ k, 4 *
            e7Weight4 (e7ReflectedWeight a (weight k)) i := by
        rw [Finset.mul_sum]
      _ = ∑ k, (4 * e7Weight4 (weight k) i -
          integerDot (e7Weight4 (weight k)) a * a i) := by
        apply Finset.sum_congr rfl
        intro k _
        exact e7ReflectionTransportCheck.reflects hcheck (weight k) i
      _ = (∑ k, 4 * e7Weight4 (weight k) i) -
          ∑ k, integerDot (e7Weight4 (weight k)) a * a i := by
        rw [Finset.sum_sub_distrib]
      _ = 4 * (110 * d i) -
          (110 * integerDot d a) * a i := by
        rw [← Finset.mul_sum, hcentroid i, ← Finset.sum_mul, hsumdot]
      _ = 4 * (110 * d' i) := by
        have hi := hdvector i
        ring_nf at hi ⊢
        omega
  omega

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Reflect the left E7 factor of a direct shell realization. -/
def E7ShellGramRealization.reflectLeft
    {x : V} {a d₁ d₁' d₂ : Fin 8 → ℤ}
    (realization : E7ShellGramRealization G x d₁ d₂)
    (hcheck : e7ReflectionTransportCheck a = true)
    (hd : e7Reflect? d₁ a = some d₁') :
    E7ShellGramRealization G x d₁' d₂ where
  shell B := by
    let old := realization.shell B
    let next : E7ShellIndex :=
      (e7ReflectedWeight a old.1.1, old.1.2)
    refine ⟨next, ?_⟩
    have hdot :
        integerDot d₁'
            (e7Weight4 (e7ReflectedWeight a old.1.1)) =
          integerDot d₁ (e7Weight4 old.1.1) :=
      e7VectorReflects_dot
        (e7ReflectionTransportCheck.root_norm hcheck)
        (e7Reflect?_vectorReflects hd)
        (e7ReflectionTransportCheck.reflects hcheck old.1.1)
    unfold e7ResidualEligible e7ResidualEvaluation
    rw [hdot]
    exact old.2
  gram B C := by
    change
      e7ShellInner
          (e7ReflectedWeight a (realization.shell B).1.1,
            (realization.shell B).1.2)
          (e7ReflectedWeight a (realization.shell C).1.1,
            (realization.shell C).1.2) =
        localGramMatrix G x B C
    unfold e7ShellInner
    rw [e7ReflectedWeight_pairing hcheck]
    exact realization.gram B C
  leftCentroid :=
    e7_reflected_centroid hcheck hd
      (fun B => (realization.shell B).1.1)
      realization.leftCentroid
  rightCentroid := realization.rightCentroid

/-- Reflect the right E7 factor of a direct shell realization. -/
def E7ShellGramRealization.reflectRight
    {x : V} {a d₁ d₂ d₂' : Fin 8 → ℤ}
    (realization : E7ShellGramRealization G x d₁ d₂)
    (hcheck : e7ReflectionTransportCheck a = true)
    (hd : e7Reflect? d₂ a = some d₂') :
    E7ShellGramRealization G x d₁ d₂' where
  shell B := by
    let old := realization.shell B
    let next : E7ShellIndex :=
      (old.1.1, e7ReflectedWeight a old.1.2)
    refine ⟨next, ?_⟩
    have hdot :
        integerDot d₂'
            (e7Weight4 (e7ReflectedWeight a old.1.2)) =
          integerDot d₂ (e7Weight4 old.1.2) :=
      e7VectorReflects_dot
        (e7ReflectionTransportCheck.root_norm hcheck)
        (e7Reflect?_vectorReflects hd)
        (e7ReflectionTransportCheck.reflects hcheck old.1.2)
    unfold e7ResidualEligible e7ResidualEvaluation
    rw [hdot]
    exact old.2
  gram B C := by
    change
      e7ShellInner
          ((realization.shell B).1.1,
            e7ReflectedWeight a (realization.shell B).1.2)
          ((realization.shell C).1.1,
            e7ReflectedWeight a (realization.shell C).1.2) =
        localGramMatrix G x B C
    unfold e7ShellInner
    rw [e7ReflectedWeight_pairing hcheck]
    exact realization.gram B C
  leftCentroid := realization.leftCentroid
  rightCentroid :=
    e7_reflected_centroid hcheck hd
      (fun B => (realization.shell B).1.2)
      realization.rightCentroid

/-- Transport a direct realization through a checked sequence in its left
E7 factor. -/
theorem E7ShellGramRealization.nonempty_reflectLeftList
    {x : V} {d₁ d₁' d₂ : Fin 8 → ℤ}
    (realization : E7ShellGramRealization G x d₁ d₂)
    (roots : List (Fin 8 → ℤ))
    (hchecks : roots.all e7ReflectionTransportCheck = true)
    (happly : e7ApplyReflections d₁ roots = some d₁') :
    Nonempty (E7ShellGramRealization G x d₁' d₂) := by
  induction roots generalizing d₁ with
  | nil =>
      simp only [e7ApplyReflections, Option.some.injEq] at happly
      subst d₁'
      exact ⟨realization⟩
  | cons a roots ih =>
      have hparts :
          e7ReflectionTransportCheck a = true ∧
            roots.all e7ReflectionTransportCheck = true := by
        simpa only [List.all_cons, Bool.and_eq_true] using hchecks
      simp only [e7ApplyReflections] at happly
      cases hreflect : e7Reflect? d₁ a with
      | none =>
          simp [hreflect] at happly
      | some next =>
          have htail :
              e7ApplyReflections next roots = some d₁' := by
            simpa [hreflect] using happly
          exact ih
            (realization.reflectLeft G hparts.1 hreflect)
            hparts.2 htail

/-- Transport a direct realization through a checked sequence in its right
E7 factor. -/
theorem E7ShellGramRealization.nonempty_reflectRightList
    {x : V} {d₁ d₂ d₂' : Fin 8 → ℤ}
    (realization : E7ShellGramRealization G x d₁ d₂)
    (roots : List (Fin 8 → ℤ))
    (hchecks : roots.all e7ReflectionTransportCheck = true)
    (happly : e7ApplyReflections d₂ roots = some d₂') :
    Nonempty (E7ShellGramRealization G x d₁ d₂') := by
  induction roots generalizing d₂ with
  | nil =>
      simp only [e7ApplyReflections, Option.some.injEq] at happly
      subst d₂'
      exact ⟨realization⟩
  | cons a roots ih =>
      have hparts :
          e7ReflectionTransportCheck a = true ∧
            roots.all e7ReflectionTransportCheck = true := by
        simpa only [List.all_cons, Bool.and_eq_true] using hchecks
      simp only [e7ApplyReflections] at happly
      cases hreflect : e7Reflect? d₂ a with
      | none =>
          simp [hreflect] at happly
      | some next =>
          have htail :
              e7ApplyReflections next roots = some d₂' := by
            simpa [hreflect] using happly
          exact ih
            (realization.reflectRight G hparts.1 hreflect)
            hparts.2 htail

/-- Exchange the two E7 factors of a direct realization. -/
def E7ShellGramRealization.swap
    {x : V} {d₁ d₂ : Fin 8 → ℤ}
    (realization : E7ShellGramRealization G x d₁ d₂) :
    E7ShellGramRealization G x d₂ d₁ where
  shell B := by
    let old := realization.shell B
    refine ⟨(old.1.2, old.1.1), ?_⟩
    simpa only [e7ResidualEligible, add_comm] using old.2
  gram B C := by
    simpa only [e7ShellInner, add_comm] using realization.gram B C
  leftCentroid := realization.rightCentroid
  rightCentroid := realization.leftCentroid

/-- Strengthen the orbit checker by reconstructing the shell permutation
induced by every root appearing in both reflection paths. -/
def E7SurvivorOrbitCertificate.transportCheck
    (c : E7SurvivorOrbitCertificate) : Bool :=
  c.check &&
    c.leftReflections.all e7ReflectionTransportCheck &&
    c.rightReflections.all e7ReflectionTransportCheck

theorem E7SurvivorOrbitCertificate.transportCheck_parts
    (c : E7SurvivorOrbitCertificate)
    (hcheck : c.transportCheck = true) :
    c.check = true ∧
      c.leftReflections.all e7ReflectionTransportCheck = true ∧
      c.rightReflections.all e7ReflectionTransportCheck = true := by
  have houter :
      (c.check &&
        c.leftReflections.all e7ReflectionTransportCheck) = true ∧
      c.rightReflections.all e7ReflectionTransportCheck = true := by
    simpa only [E7SurvivorOrbitCertificate.transportCheck,
      Bool.and_eq_true] using hcheck
  have hleft :
      c.check = true ∧
        c.leftReflections.all e7ReflectionTransportCheck = true := by
    simpa only [Bool.and_eq_true] using houter.1
  exact ⟨hleft.1, hleft.2, houter.2⟩

/-- A fully checked survivor witness transports every direct realization to
its declared canonical residual type. -/
theorem E7SurvivorOrbitCertificate.toCanonical
    {x : V} (c : E7SurvivorOrbitCertificate)
    (hcheck : c.transportCheck = true)
    (realization :
      E7ShellGramRealization G x
        (fun i => c.y₁ i / 5) (fun i => c.y₂ i / 5)) :
    Nonempty
      (E7ShellGramRealization G x
        (e7ResidualCanonical c.residualType).1
        (e7ResidualCanonical c.residualType).2) := by
  have hparts := c.transportCheck_parts hcheck
  have horbit :
      (∀ i, c.y₁ i % 5 = 0) ∧
      (∀ i, c.y₂ i % 5 = 0) ∧
      e7EligibleCount c.y₁ c.y₂ = c.reportedEligible ∧
      e7ApplyReflections (fun i => c.y₁ i / 5) c.leftReflections =
        some (if c.swapFactors then
          (e7ResidualCanonical c.residualType).2
        else (e7ResidualCanonical c.residualType).1) ∧
      e7ApplyReflections (fun i => c.y₂ i / 5) c.rightReflections =
        some (if c.swapFactors then
          (e7ResidualCanonical c.residualType).1
        else (e7ResidualCanonical c.residualType).2) := by
    exact of_decide_eq_true (by
      simpa only [E7SurvivorOrbitCertificate.check] using hparts.1)
  obtain ⟨left⟩ :=
    realization.nonempty_reflectLeftList G c.leftReflections
      hparts.2.1 horbit.2.2.2.1
  obtain ⟨both⟩ :=
    left.nonempty_reflectRightList G c.rightReflections
      hparts.2.2 horbit.2.2.2.2
  cases hswap : c.swapFactors with
  | false =>
      simpa [hswap] using Nonempty.intro both
  | true =>
      simpa [hswap] using Nonempty.intro (both.swap G)

/-- Hence none of the 54 checked survivor profiles can carry a direct Gram
realization. -/
theorem E7SurvivorOrbitCertificate.no_realization
    (hG : IsHypothetical G) (x : V)
    (c : E7SurvivorOrbitCertificate)
    (hcheck : c.transportCheck = true) :
    IsEmpty
      (E7ShellGramRealization G x
        (fun i => c.y₁ i / 5) (fun i => c.y₂ i / 5)) := by
  refine ⟨fun realization => ?_⟩
  obtain ⟨canonical⟩ := c.toCanonical G hcheck realization
  exact
    (no_e7ResidualCanonical_realization
      G hG x c.residualType).false canonical

end SRG266
