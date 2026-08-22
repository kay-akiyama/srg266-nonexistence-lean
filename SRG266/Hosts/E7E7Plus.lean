/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.Farkas
import SRG266.Hosts.E7ResidualCore

/-!
# The finite `E₇ ⊕ E₇` shell model

This file defines the exact finite model used by the Python
`E₇ ⊕ E₇` centroid certificates.  A minuscule `E₇` weight is stored after
multiplication by four: for an unordered pair `{i,j} ⊆ {0,…,7}` it is

`±(3 at i and j, -1 elsewhere)`.

Thus there are `2 * choose(8,2) = 56` weights.  A shell column consists of
one weight from each factor.  For doubled centroid coordinates `y₁,y₂`,
eligibility is the exact integral equation

`y₁ · w₁ + y₂ · w₂ = 120`.

The resulting 17-row system has a count row followed by the eight
coordinates in each factor.  Its target is `(220, 22y₁, 22y₂)`.

-/

open scoped BigOperators Matrix

namespace SRG266

/-- Exact shell eligibility for doubled centroid coordinates.

The scale is chosen to avoid division: it is equivalent to
`⟨c₁,w₁⟩ + ⟨c₂,w₂⟩ = 15` in the unscaled coordinate model. -/
def e7Eligible
    (y₁ y₂ : Fin 8 → ℤ) (w : E7ShellIndex) : Prop :=
  integerDot y₁ (e7Weight4 w.1) +
    integerDot y₂ (e7Weight4 w.2) = 120

instance (y₁ y₂ : Fin 8 → ℤ) : DecidablePred (e7Eligible y₁ y₂) :=
  fun w => by
    unfold e7Eligible
    infer_instance

/-- The finite set of eligible shell columns for a centroid profile. -/
abbrev E7EligibleIndex
    (y₁ y₂ : Fin 8 → ℤ) :=
  {w : E7ShellIndex // e7Eligible y₁ y₂ w}

instance (y₁ y₂ : Fin 8 → ℤ) : Fintype (E7EligibleIndex y₁ y₂) :=
  Fintype.subtype
    (Finset.univ.filter (e7Eligible y₁ y₂))
    (by simp)

/-- Rows of the centroid moment system: one count row and two coordinate
blocks of length eight. -/
inductive E7CentroidRow
  | count
  | left (i : Fin 8)
  | right (i : Fin 8)
  deriving DecidableEq, Fintype

/-- The 17 by `#eligible` integral shell-column matrix. -/
def e7CentroidMatrix
    (y₁ y₂ : Fin 8 → ℤ) :
    Matrix E7CentroidRow (E7EligibleIndex y₁ y₂) ℤ
  | .count, _ => 1
  | .left i, w => e7Weight4 w.1.1 i
  | .right i, w => e7Weight4 w.1.2 i

/-- The exact target `(220, 22y₁, 22y₂)` of the centroid system. -/
def e7CentroidTarget
    (y₁ y₂ : Fin 8 → ℤ) : E7CentroidRow → ℤ
  | .count => 220
  | .left i => 22 * y₁ i
  | .right i => 22 * y₂ i

/-- Number of shell columns regenerated from a centroid profile. -/
def e7EligibleCount (y₁ y₂ : Fin 8 → ℤ) : ℕ :=
  Fintype.card (E7EligibleIndex y₁ y₂)

/-- Exact strict Farkas gap.  A positive value is a certificate of
infeasibility for multiplicities in the interval `[0,3]`. -/
def e7FarkasGap
    (y₁ y₂ : Fin 8 → ℤ) (q : E7CentroidRow → ℤ) : ℤ :=
  integerDot q (e7CentroidTarget y₁ y₂) -
    3 * ∑ w : E7EligibleIndex y₁ y₂,
      integerPositivePart
        (integerDot q (fun r => e7CentroidMatrix y₁ y₂ r w))

theorem e7_no_bounded_solution_of_positive_gap
    (y₁ y₂ : Fin 8 → ℤ) (q : E7CentroidRow → ℤ)
    (hgap : 0 < e7FarkasGap y₁ y₂ q) :
    ¬∃ m : E7EligibleIndex y₁ y₂ → ℤ,
      (∀ w, 0 ≤ m w) ∧
      (∀ w, m w ≤ 3) ∧
      e7CentroidMatrix y₁ y₂ *ᵥ m = e7CentroidTarget y₁ y₂ := by
  apply no_bounded_solution_of_farkas
    (e7CentroidMatrix y₁ y₂) (e7CentroidTarget y₁ y₂) q
  unfold BoundedFarkasSeparates e7FarkasGap at *
  omega

/-- Declarative data carried by one rejected centroid profile.

The reported eligible-column count and gap are audit fields: `check`
regenerates both values from `y₁`, `y₂`, and `q`. -/
structure E7CentroidCertificate where
  y₁ : Fin 8 → ℤ
  y₂ : Fin 8 → ℤ
  q : E7CentroidRow → ℤ
  reportedEligible : ℕ
  reportedGap : ℤ

/-- Reflective checker for one `E₇ ⊕ E₇` centroid separator. -/
def E7CentroidCertificate.check
    (c : E7CentroidCertificate) : Bool :=
  decide (
    e7EligibleCount c.y₁ c.y₂ = c.reportedEligible ∧
    e7FarkasGap c.y₁ c.y₂ c.q = c.reportedGap ∧
    0 < c.reportedGap)

theorem E7CentroidCertificate.no_bounded_solution
    (c : E7CentroidCertificate) (hcheck : c.check = true) :
    ¬∃ m : E7EligibleIndex c.y₁ c.y₂ → ℤ,
      (∀ w, 0 ≤ m w) ∧
      (∀ w, m w ≤ 3) ∧
      e7CentroidMatrix c.y₁ c.y₂ *ᵥ m =
        e7CentroidTarget c.y₁ c.y₂ := by
  have h := of_decide_eq_true (by
    simpa only [E7CentroidCertificate.check] using hcheck)
  exact e7_no_bounded_solution_of_positive_gap c.y₁ c.y₂ c.q
    (by omega)

/-- One supplied centroid survivor together with explicit Weyl-reflection
witnesses reducing it to a canonical residual type. -/
structure E7SurvivorOrbitCertificate where
  y₁ : Fin 8 → ℤ
  y₂ : Fin 8 → ℤ
  reportedEligible : ℕ
  residualType : E7ResidualType
  swapFactors : Bool
  leftReflections : List (Fin 8 → ℤ)
  rightReflections : List (Fin 8 → ℤ)

/-- Check divisibility by five, the original eligible count, and both
root-reflection witnesses. -/
def E7SurvivorOrbitCertificate.check
    (c : E7SurvivorOrbitCertificate) : Bool :=
  let canonical := e7ResidualCanonical c.residualType
  let target₁ := if c.swapFactors then canonical.2 else canonical.1
  let target₂ := if c.swapFactors then canonical.1 else canonical.2
  decide (
    (∀ i, c.y₁ i % 5 = 0) ∧
    (∀ i, c.y₂ i % 5 = 0) ∧
    e7EligibleCount c.y₁ c.y₂ = c.reportedEligible ∧
    e7ApplyReflections (fun i => c.y₁ i / 5) c.leftReflections =
      some target₁ ∧
    e7ApplyReflections (fun i => c.y₂ i / 5) c.rightReflections =
      some target₂)

end SRG266
