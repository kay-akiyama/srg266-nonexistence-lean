/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7E7Plus
import SRG266.Hosts.ShellGram

/-!
# The full mixed `(E₇ ⊕ E₇)⁺ ⊕ ℤ` norm-three shell

The pure shell contains pairs of minuscule E7 weights.  Adding one norm-one
direction adds exactly the vectors consisting of an E7 root in either factor
and a signed unit vector.  All E7 coordinates are scaled by four; roots are
stored doubled, so their four-scaled coordinates are twice `e7Root2`.

This module defines the finite shell, its centroid moment system, and the
exact bounded Farkas checker.  Python may generate separators, but Lean
regenerates every eligible column and checks the strict integer gap.
-/

open scoped BigOperators Matrix

namespace SRG266

set_option maxRecDepth 100000

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The 56 coordinate-difference roots, indexed without repetition. -/
abbrev E7DifferenceRootIndex :=
  {p : Fin 8 × Fin 8 // p.1 ≠ p.2}

/-- The 70 half-integral roots, indexed by their four positive signs. -/
abbrev E7HalfRootIndex :=
  {s : Finset (Fin 8) // s.card = 4}

/-- The 126 roots of E7 in doubled coordinates. -/
inductive E7RootIndex
  | difference (root : E7DifferenceRootIndex)
  | half (root : E7HalfRootIndex)
  deriving DecidableEq, Fintype

/-- Doubled E7 root coordinates.  Their squared coordinate norm is eight. -/
def e7Root2 : E7RootIndex → Fin 8 → ℤ
  | .difference root, k =>
      if k = root.1.1 then 2 else if k = root.1.2 then -2 else 0
  | .half root, k => if k ∈ root.1 then 1 else -1

/-- Sign of the norm-one coordinate. -/
def e7MixedUnitSign (sign : Bool) : ℤ :=
  if sign then -1 else 1

/-- The complete norm-three shell in `(E7 ⊕ E7)+ ⊕ ℤ`. -/
inductive E7MixedShellIndex
  | pure (shell : E7ShellIndex)
  | leftRoot (root : E7RootIndex) (unitSign : Bool)
  | rightRoot (root : E7RootIndex) (unitSign : Bool)
  deriving DecidableEq, Fintype

/-- Four-scaled coordinates in the left E7 factor. -/
def e7MixedLeft4 : E7MixedShellIndex → Fin 8 → ℤ
  | .pure shell => e7Weight4 shell.1
  | .leftRoot root _ => fun k => 2 * e7Root2 root k
  | .rightRoot _ _ => 0

/-- Four-scaled coordinates in the right E7 factor. -/
def e7MixedRight4 : E7MixedShellIndex → Fin 8 → ℤ
  | .pure shell => e7Weight4 shell.2
  | .leftRoot _ _ => 0
  | .rightRoot root _ => fun k => 2 * e7Root2 root k

/-- The unscaled integral norm-one coordinate. -/
def e7MixedUnit : E7MixedShellIndex → ℤ
  | .pure _ => 0
  | .leftRoot _ sign => e7MixedUnitSign sign
  | .rightRoot _ sign => e7MixedUnitSign sign

/-- Integral inner product on the complete shell. -/
def e7MixedInner (s t : E7MixedShellIndex) : ℤ :=
  (integerDot (e7MixedLeft4 s) (e7MixedLeft4 t) +
      integerDot (e7MixedRight4 s) (e7MixedRight4 t)) / 16 +
    e7MixedUnit s * e7MixedUnit t

/-- Exact centroid eligibility.  The E7 centroid is `(y1/2,y2/2)` and the
unit coordinate is `t`. -/
def e7MixedEligible
    (y₁ y₂ : Fin 8 → ℤ) (t : ℤ) (s : E7MixedShellIndex) : Prop :=
  integerDot y₁ (e7MixedLeft4 s) +
      integerDot y₂ (e7MixedRight4 s) +
      8 * t * e7MixedUnit s = 120

instance (y₁ y₂ : Fin 8 → ℤ) (t : ℤ) :
    DecidablePred (e7MixedEligible y₁ y₂ t) :=
  fun s => by
    unfold e7MixedEligible
    infer_instance

abbrev E7MixedEligibleIndex (y₁ y₂ : Fin 8 → ℤ) (t : ℤ) :=
  {s : E7MixedShellIndex // e7MixedEligible y₁ y₂ t s}

instance (y₁ y₂ : Fin 8 → ℤ) (t : ℤ) :
    Fintype (E7MixedEligibleIndex y₁ y₂ t) :=
  Fintype.subtype
    (Finset.univ.filter (e7MixedEligible y₁ y₂ t)) (by simp)

/-- Rows of the mixed centroid moment system. -/
inductive E7MixedCentroidRow
  | count
  | left (i : Fin 8)
  | right (i : Fin 8)
  | unit
  deriving DecidableEq, Fintype

def e7MixedCentroidMatrix
    (y₁ y₂ : Fin 8 → ℤ) (t : ℤ) :
    Matrix E7MixedCentroidRow (E7MixedEligibleIndex y₁ y₂ t) ℤ
  | .count, _ => 1
  | .left i, s => e7MixedLeft4 s.1 i
  | .right i, s => e7MixedRight4 s.1 i
  | .unit, s => e7MixedUnit s.1

def e7MixedCentroidTarget
    (y₁ y₂ : Fin 8 → ℤ) (t : ℤ) : E7MixedCentroidRow → ℤ
  | .count => 220
  | .left i => 22 * y₁ i
  | .right i => 22 * y₂ i
  | .unit => 11 * t

def e7MixedEligibleCount
    (y₁ y₂ : Fin 8 → ℤ) (t : ℤ) : ℕ :=
  Fintype.card (E7MixedEligibleIndex y₁ y₂ t)

def e7MixedFarkasGap
    (y₁ y₂ : Fin 8 → ℤ) (t : ℤ)
    (q : E7MixedCentroidRow → ℤ) : ℤ :=
  integerDot q (e7MixedCentroidTarget y₁ y₂ t) -
    3 * ∑ s : E7MixedEligibleIndex y₁ y₂ t,
      integerPositivePart
        (integerDot q (fun row => e7MixedCentroidMatrix y₁ y₂ t row s))

theorem e7Mixed_no_bounded_solution_of_positive_gap
    (y₁ y₂ : Fin 8 → ℤ) (t : ℤ)
    (q : E7MixedCentroidRow → ℤ)
    (hgap : 0 < e7MixedFarkasGap y₁ y₂ t q) :
    ¬∃ m : E7MixedEligibleIndex y₁ y₂ t → ℤ,
      (∀ s, 0 ≤ m s) ∧ (∀ s, m s ≤ 3) ∧
      e7MixedCentroidMatrix y₁ y₂ t *ᵥ m =
        e7MixedCentroidTarget y₁ y₂ t := by
  apply no_bounded_solution_of_farkas
    (e7MixedCentroidMatrix y₁ y₂ t)
    (e7MixedCentroidTarget y₁ y₂ t) q
  unfold BoundedFarkasSeparates e7MixedFarkasGap at *
  omega

/-- One exact mixed-shell Farkas certificate. -/
structure E7MixedCentroidCertificate where
  y₁ : Fin 8 → ℤ
  y₂ : Fin 8 → ℤ
  t : ℤ
  q : E7MixedCentroidRow → ℤ
  reportedEligible : ℕ
  reportedGap : ℤ

def E7MixedCentroidCertificate.check
    (certificate : E7MixedCentroidCertificate) : Bool :=
  decide (
    e7MixedEligibleCount certificate.y₁ certificate.y₂ certificate.t =
        certificate.reportedEligible ∧
    e7MixedFarkasGap certificate.y₁ certificate.y₂ certificate.t
        certificate.q = certificate.reportedGap ∧
    0 < certificate.reportedGap)

theorem E7MixedCentroidCertificate.no_bounded_solution
    (certificate : E7MixedCentroidCertificate)
    (hcheck : certificate.check = true) :
    ¬∃ m : E7MixedEligibleIndex certificate.y₁ certificate.y₂
        certificate.t → ℤ,
      (∀ s, 0 ≤ m s) ∧ (∀ s, m s ≤ 3) ∧
      e7MixedCentroidMatrix certificate.y₁ certificate.y₂
          certificate.t *ᵥ m =
        e7MixedCentroidTarget certificate.y₁ certificate.y₂
          certificate.t := by
  have h := of_decide_eq_true (by
    simpa only [E7MixedCentroidCertificate.check] using hcheck)
  exact e7Mixed_no_bounded_solution_of_positive_gap
    certificate.y₁ certificate.y₂ certificate.t certificate.q (by omega)

/-- A local Gram realization in one eligible full mixed shell. -/
structure E7MixedShellGramRealization
    (x : V) (y₁ y₂ : Fin 8 → ℤ) (t : ℤ) where
  shell : SecondSubconstituent G x → E7MixedEligibleIndex y₁ y₂ t
  gram : ∀ B C,
    e7MixedInner (shell B).1 (shell C).1 = localGramMatrix G x B C
  eq_of_inner_eq_three : ∀ s r : E7MixedEligibleIndex y₁ y₂ t,
    e7MixedInner s.1 r.1 = 3 → s = r
  centroid_left : ∀ i, ∑ B, e7MixedLeft4 (shell B).1 i = 22 * y₁ i
  centroid_right : ∀ i, ∑ B, e7MixedRight4 (shell B).1 i = 22 * y₂ i
  centroid_unit : ∑ B, e7MixedUnit (shell B).1 = 11 * t

def E7MixedShellGramRealization.toFiniteShell
    {x : V} {y₁ y₂ : Fin 8 → ℤ} {t : ℤ}
    (realization : E7MixedShellGramRealization G x y₁ y₂ t) :
    FiniteShellGramRealization G x (E7MixedEligibleIndex y₁ y₂ t)
      (fun s r => e7MixedInner s.1 r.1) where
  shell := realization.shell
  gram := realization.gram
  eq_of_inner_eq_three := realization.eq_of_inner_eq_three

theorem E7MixedShellGramRealization.has_bounded_moment_solution
    (hG : IsHypothetical G) (x : V)
    {y₁ y₂ : Fin 8 → ℤ} {t : ℤ}
    (realization : E7MixedShellGramRealization G x y₁ y₂ t) :
    ∃ m : E7MixedEligibleIndex y₁ y₂ t → ℤ,
      (∀ s, 0 ≤ m s) ∧ (∀ s, m s ≤ 3) ∧
      e7MixedCentroidMatrix y₁ y₂ t *ᵥ m =
        e7MixedCentroidTarget y₁ y₂ t := by
  let finite := realization.toFiniteShell G
  let m : E7MixedEligibleIndex y₁ y₂ t → ℤ :=
    fun s => (finite.multiplicity G s : ℤ)
  refine ⟨m, ?_, ?_, ?_⟩
  · intro s
    exact Int.natCast_nonneg _
  · intro s
    change ((finite.multiplicity G s : ℕ) : ℤ) ≤ 3
    exact_mod_cast finite.multiplicity_le_three G hG x s
  · funext row
    cases row with
    | count =>
        simp only [Matrix.mulVec, dotProduct, e7MixedCentroidMatrix,
          e7MixedCentroidTarget, m, one_mul]
        rw [← Nat.cast_sum, finite.sum_multiplicity G,
          secondSubconstituent_card G hG x]
        norm_num
    | left i =>
        simp only [Matrix.mulVec, dotProduct, e7MixedCentroidMatrix,
          e7MixedCentroidTarget, m]
        calc
          (∑ s, e7MixedLeft4 s.1 i * (finite.multiplicity G s : ℤ)) =
              ∑ s, (finite.multiplicity G s : ℤ) *
                e7MixedLeft4 s.1 i := by
            apply Finset.sum_congr rfl
            intro s _
            ring
          _ = ∑ B, e7MixedLeft4 (realization.shell B).1 i := by
            rw [finite.sum_multiplicity_mul G (fun s => e7MixedLeft4 s.1 i)]
            rfl
          _ = 22 * y₁ i := realization.centroid_left i
    | right i =>
        simp only [Matrix.mulVec, dotProduct, e7MixedCentroidMatrix,
          e7MixedCentroidTarget, m]
        calc
          (∑ s, e7MixedRight4 s.1 i * (finite.multiplicity G s : ℤ)) =
              ∑ s, (finite.multiplicity G s : ℤ) *
                e7MixedRight4 s.1 i := by
            apply Finset.sum_congr rfl
            intro s _
            ring
          _ = ∑ B, e7MixedRight4 (realization.shell B).1 i := by
            rw [finite.sum_multiplicity_mul G (fun s => e7MixedRight4 s.1 i)]
            rfl
          _ = 22 * y₂ i := realization.centroid_right i
    | unit =>
        simp only [Matrix.mulVec, dotProduct, e7MixedCentroidMatrix,
          e7MixedCentroidTarget, m]
        calc
          (∑ s, e7MixedUnit s.1 * (finite.multiplicity G s : ℤ)) =
              ∑ s, (finite.multiplicity G s : ℤ) *
                e7MixedUnit s.1 := by
            apply Finset.sum_congr rfl
            intro s _
            ring
          _ = ∑ B, e7MixedUnit (realization.shell B).1 := by
            rw [finite.sum_multiplicity_mul G (fun s => e7MixedUnit s.1)]
            rfl
          _ = 11 * t := realization.centroid_unit

theorem no_e7MixedShellGramRealization_of_certificate
    (hG : IsHypothetical G) (x : V)
    (certificate : E7MixedCentroidCertificate)
    (hcheck : certificate.check = true) :
    ¬Nonempty (E7MixedShellGramRealization G x
      certificate.y₁ certificate.y₂ certificate.t) := by
  rintro ⟨realization⟩
  exact certificate.no_bounded_solution hcheck
    (realization.has_bounded_moment_solution G hG x)

end SRG266
