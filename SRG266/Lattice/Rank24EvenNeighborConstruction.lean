/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.Rank24RootMomentReduction
import SRG266.Lattice.StandardRationalLattice
import SRG266.Lattice.VanDerBlijReduction

/-!
# Construction of the rank-24 even neighbour

Let `L` be a positive-definite integral unimodular lattice of rank `n`, put
`m = 24 - n`, and choose a characteristic vector `c` of `L`.  In the rational
quadratic space underlying

`L orthogonal-sum Z^m`

we construct the standard even neighbour associated with `(c, 1, ..., 1)`.
This file supplies the algebraic data consumed by
`Rank24RootMomentReduction.lean`.

Van der Blij's formula `c^2 = n (mod 8)` is accepted here through the reusable
`VanDerBlijCongruenceInput` factorization; `VanDerBlij.lean` proves that
interface internally.  All lattice construction and root bookkeeping after
the formula are checked here by Lean.
-/

namespace SRG266.Lattice

open scoped BigOperators

/-! ## The orthogonal product presentation -/

/-- Rational ambient space for the stabilization. -/
abbrev StabilizationSpace (n : ℕ) :=
  (Fin n → ℚ) × (Fin (24 - n) → ℚ)

/-- Orthogonal sum of the coordinate form of `L` and the standard dot
product. -/
noncomputable def stabilizationForm {n : ℕ} (L : PDUnimodularLattice n) :
    LinearMap.BilinForm ℚ (StabilizationSpace n) :=
  prodForm (pdRatForm L) (standardRatForm (24 - n))

/-- Integral product lattice before adjoining the half-characteristic glue
vector. -/
def stabilizationIntegerLattice (n : ℕ) :
    Submodule ℤ (StabilizationSpace n) :=
  (coordinateIntegerLattice n).prod
    (coordinateIntegerLattice (24 - n))

theorem stabilizationForm_isSymm {n : ℕ} (L : PDUnimodularLattice n) :
    (stabilizationForm L).IsSymm :=
  prodForm_isSymm (pdRatForm_isSymm L)
    (standardRatForm_isSymm (24 - n))

theorem stabilizationForm_posDef {n : ℕ} (L : PDUnimodularLattice n) :
    ∀ x : StabilizationSpace n, x ≠ 0 →
      0 < stabilizationForm L x x :=
  prodForm_posDef (pdRatForm_posDef L)
    (standardRatForm_posDef (24 - n))

theorem stabilizationIntegerLattice_isLattice (n : ℕ) :
    IsLattice ℚ (stabilizationIntegerLattice n) :=
  isLattice_prod (coordinateIntegerLattice_isLattice n)
    (coordinateIntegerLattice_isLattice (24 - n))

theorem stabilizationIntegerLattice_selfDual {n : ℕ}
    (L : PDUnimodularLattice n) :
    (stabilizationForm L).dualSubmodule (stabilizationIntegerLattice n) =
      stabilizationIntegerLattice n := by
  rw [stabilizationForm, stabilizationIntegerLattice,
    dualSubmodule_prodForm, pdRatForm_dual_coordinateIntegerLattice,
    standardRatForm_dual_coordinateIntegerLattice]

/-- Integral coordinates of a lattice vector in the selected basis. -/
noncomputable def latticeCoords {n : ℕ} (L : PDUnimodularLattice n) :
    L.carrier →ₗ[ℤ] (Fin n → ℤ) :=
  (pdFinBasis L).equivFun

@[simp]
theorem pdCoordEquiv_latticeCoords {n : ℕ} (L : PDUnimodularLattice n)
    (x : L.carrier) :
    pdCoordEquiv L (latticeCoords L x) = x := by
  simp [pdCoordEquiv, latticeCoords]

/-- Coordinate inclusion of the left lattice into the rational product. -/
noncomputable def leftCoordinateMap {n : ℕ} (L : PDUnimodularLattice n) :
    L.carrier →ₗ[ℤ] StabilizationSpace n :=
  (LinearMap.inl ℤ (Fin n → ℚ) (Fin (24 - n) → ℚ)).comp
    (intCoordsToRat.comp (latticeCoords L))

@[simp]
theorem leftCoordinateMap_pairing {n : ℕ} (L : PDUnimodularLattice n)
    (x y : L.carrier) :
    stabilizationForm L (leftCoordinateMap L x) (leftCoordinateMap L y) =
      ((L.pairing x y : ℤ) : ℚ) := by
  simp only [stabilizationForm, leftCoordinateMap, LinearMap.comp_apply,
    LinearMap.inl_apply, prodForm_apply, pdRatForm_intCoords, map_zero,
    add_zero]
  rw [pdCoordEquiv_latticeCoords, pdCoordEquiv_latticeCoords]

theorem leftCoordinateMap_mem {n : ℕ} (L : PDUnimodularLattice n)
    (x : L.carrier) :
    leftCoordinateMap L x ∈ stabilizationIntegerLattice n := by
  apply Submodule.mem_prod.mpr
  exact ⟨intCoordsToRat_mem _, (coordinateIntegerLattice (24 - n)).zero_mem⟩

/-! ## Characteristic and primitive vectors -/

/-- The all-ones integral coordinate vector. -/
def onesInt (m : ℕ) : Fin m → ℤ := fun _ => 1

/-- The characteristic vector `(c, 1, ..., 1)` in rational coordinates. -/
noncomputable def stabilizationCharacteristic {n : ℕ}
    (L : PDUnimodularLattice n) (c : L.carrier) : StabilizationSpace n :=
  (intCoordsToRat (latticeCoords L c),
    intCoordsToRat (onesInt (24 - n)))

theorem stabilizationCharacteristic_mem {n : ℕ}
    (L : PDUnimodularLattice n) (c : L.carrier) :
    stabilizationCharacteristic L c ∈ stabilizationIntegerLattice n := by
  exact Submodule.mem_prod.mpr ⟨intCoordsToRat_mem _, intCoordsToRat_mem _⟩

/-- The first basis vector in the added standard summand. -/
def stabilizationPrimitive {n : ℕ} (hm : 0 < 24 - n) :
    StabilizationSpace n :=
  (0, intCoordsToRat (Pi.single ⟨0, hm⟩ 1))

theorem stabilizationPrimitive_mem {n : ℕ} (hm : 0 < 24 - n) :
    stabilizationPrimitive hm ∈ stabilizationIntegerLattice n := by
  exact Submodule.mem_prod.mpr
    ⟨(coordinateIntegerLattice n).zero_mem, intCoordsToRat_mem _⟩

theorem stabilizationCharacteristic_pair_primitive {n : ℕ}
    (L : PDUnimodularLattice n) (c : L.carrier) (hm : 0 < 24 - n) :
    stabilizationForm L (stabilizationCharacteristic L c)
      (stabilizationPrimitive hm) = 1 := by
  simp only [stabilizationForm, stabilizationCharacteristic,
    stabilizationPrimitive, prodForm_apply, map_zero, zero_add,
    standardRatForm_apply, intCoordsToRat_apply, onesInt]
  norm_num only [Int.cast_one, one_mul]
  rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin (24 - n))]
  · simp
  · intro j _ hji
    simp [hji]
  · exact fun h => absurd (Finset.mem_univ (⟨0, hm⟩ : Fin (24 - n))) h

/-- Every integer satisfies `z^2 - z = 0 (mod 2)`. -/
theorem even_int_sq_sub_self (z : ℤ) : ∃ a : ℤ, z * z - z = 2 * a := by
  obtain ⟨a, ha⟩ := (Int.even_mul_pred_self z).two_dvd
  exact ⟨a, by simpa [mul_sub] using ha⟩

/-- The all-ones vector is characteristic for the standard integer lattice. -/
theorem standard_ones_characteristic (m : ℕ) (z : Fin m → ℤ) :
    ∃ a : ℤ,
      intDot z z - intDot (onesInt m) z = 2 * a := by
  choose a ha using fun i => even_int_sq_sub_self (z i)
  refine ⟨∑ i, a i, ?_⟩
  simp only [intDot, onesInt, one_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => ha i

/-- The product vector is characteristic in the rational lattice. -/
theorem stabilizationCharacteristic_isCharacteristicIn {n : ℕ}
    (L : PDUnimodularLattice n) (c : L.carrier)
    (hc : IsCharacteristic L.pairing c) :
    IsCharacteristicIn (stabilizationForm L)
      (stabilizationIntegerLattice n) (stabilizationCharacteristic L c) := by
  intro x hx
  obtain ⟨hxL, hxR⟩ := Submodule.mem_prod.mp hx
  obtain ⟨a, ha⟩ := mem_coordinateIntegerLattice.mp hxL
  obtain ⟨b, hb⟩ := mem_coordinateIntegerLattice.mp hxR
  have hleft := hc (pdCoordEquiv L a)
  obtain ⟨u, hu⟩ := hleft
  obtain ⟨v, hv⟩ := standard_ones_characteristic (24 - n) b
  refine ⟨u + v, ?_⟩
  have hxEq : x = (intCoordsToRat a, intCoordsToRat b) := by
    apply Prod.ext
    · funext i
      exact (ha i).symm
    · funext i
      exact (hb i).symm
  rw [hxEq]
  simp only [stabilizationForm, stabilizationCharacteristic, prodForm_apply,
    pdRatForm_intCoords, standardRatForm_apply, intCoordsToRat_apply]
  rw [pdCoordEquiv_latticeCoords]
  have hbb : (∑ i, (b i : ℚ) * (b i : ℚ)) = ((intDot b b : ℤ) : ℚ) := by
    simp only [intDot]
    push_cast
    rfl
  have hones : (∑ i, (onesInt (24 - n) i : ℚ) * (b i : ℚ)) =
      ((intDot (onesInt (24 - n)) b : ℤ) : ℚ) := by
    simp only [intDot]
    push_cast
    rfl
  rw [hbb, hones]
  change
    (((L.pairing (pdCoordEquiv L a) (pdCoordEquiv L a) : ℤ) : ℚ) +
        ((intDot b b : ℤ) : ℚ)) -
      (((L.pairing c (pdCoordEquiv L a) : ℤ) : ℚ) +
        ((intDot (onesInt (24 - n)) b : ℤ) : ℚ)) =
      (((2 * (u + v) : ℤ)) : ℚ)
  norm_cast
  linear_combination hu + hv

/-- Van der Blij's congruence makes the stabilized characteristic norm
divisible by eight because `n + (24-n) = 24`. -/
theorem stabilizationCharacteristic_normDivisibleByEight
    (hvdB : VanDerBlijCongruenceInput) {n : ℕ} (hn : n ≤ 24)
    (L : PDUnimodularLattice n) (c : L.carrier)
    (hc : IsCharacteristic L.pairing c) :
    NormDivisibleByEight (stabilizationForm L)
      (stabilizationCharacteristic L c) := by
  obtain ⟨a, ha⟩ := hvdB n L c hc
  refine ⟨a + 3, ?_⟩
  have hnorm : stabilizationForm L (stabilizationCharacteristic L c)
      (stabilizationCharacteristic L c) =
      (((L.pairing c c + ((24 - n : ℕ) : ℤ)) : ℤ) : ℚ) := by
    simp only [stabilizationForm, stabilizationCharacteristic, prodForm_apply,
      pdRatForm_intCoords, standardRatForm_apply, intCoordsToRat_apply,
      onesInt, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [pdCoordEquiv_latticeCoords]
    norm_num
  rw [hnorm]
  have hint : L.pairing c c + ((24 - n : ℕ) : ℤ) = 8 * (a + 3) := by
    rw [ha]
    omega
  exact_mod_cast hint

/-! ## Roots cannot lie in the half-integral coset -/

/-- The standard even neighbour in its rational product presentation. -/
noncomputable def stabilizationEvenNeighbor {n : ℕ}
    (L : PDUnimodularLattice n) (c : L.carrier) :
    Submodule ℤ (StabilizationSpace n) :=
  evenNeighbor (stabilizationForm L) (stabilizationIntegerLattice n)
    (stabilizationCharacteristic L c)

/-- In at least nine added coordinates, a half-integral coset vector has
standard norm strictly greater than two.  Hence every norm-two vector in the
even neighbour already belongs to the original product lattice. -/
theorem normTwo_mem_stabilizationIntegerLattice {n : ℕ}
    (hnhi : n ≤ 15) (L : PDUnimodularLattice n) (c : L.carrier)
    {z : StabilizationSpace n}
    (hzH : z ∈ stabilizationEvenNeighbor L c)
    (hznorm : stabilizationForm L z z = 2) :
    z ∈ stabilizationIntegerLattice n := by
  classical
  let m := 24 - n
  have hm : 9 ≤ m := by omega
  obtain ⟨x, hx0, a, hxa⟩ :=
    (mem_evenNeighbor_iff.mp hzH :
      ∃ x ∈ characteristicEvenPart (stabilizationForm L)
        (stabilizationIntegerLattice n) (stabilizationCharacteristic L c),
        ∃ a : ℤ, x + a • halfVector (stabilizationCharacteristic L c) = z)
  obtain ⟨b, hb⟩ := mem_coordinateIntegerLattice.mp
    (Submodule.mem_prod.mp hx0.1).2
  have hzcoord : ∀ i : Fin m,
      z.2 i = (b i : ℚ) + (a : ℚ) / 2 := by
    intro i
    rw [← hxa]
    have hxi : x.2 i = (b i : ℚ) := (hb i).symm
    simp only [Prod.snd_add, Pi.add_apply]
    rw [hxi]
    simp only [halfVector, stabilizationCharacteristic]
    rw [← Int.cast_smul_eq_zsmul ℚ]
    change (b i : ℚ) + (a : ℚ) * ((1 / 2 : ℚ) * 1) =
      (b i : ℚ) + (a : ℚ) / 2
    ring
  have hleftNonneg : 0 ≤ pdRatForm L z.1 z.1 :=
    ratNonneg_of_posDef (pdRatForm_posDef L) z.1
  have hrightLe : standardRatForm m z.2 z.2 ≤ 2 := by
    have hsum : pdRatForm L z.1 z.1 + standardRatForm m z.2 z.2 = 2 := by
      simpa [stabilizationForm, m] using hznorm
    linarith
  rcases Int.even_or_odd a with haEven | haOdd
  · obtain ⟨k, hk⟩ := haEven
    have haHalf : a • halfVector (stabilizationCharacteristic L c) =
        k • stabilizationCharacteristic L c := by
      rw [hk, add_smul]
      calc
        k • halfVector (stabilizationCharacteristic L c) +
            k • halfVector (stabilizationCharacteristic L c) =
            k • (halfVector (stabilizationCharacteristic L c) +
              halfVector (stabilizationCharacteristic L c)) :=
          (smul_add k _ _).symm
        _ = k • ((2 : ℤ) • halfVector (stabilizationCharacteristic L c)) := by
          rw [two_smul ℤ]
        _ = k • stabilizationCharacteristic L c := by
          rw [two_smul_halfVector]
    have hrightMem : k • stabilizationCharacteristic L c ∈
        stabilizationIntegerLattice n :=
      (stabilizationIntegerLattice n).smul_mem k
        (stabilizationCharacteristic_mem L c)
    rw [← hxa]
    exact (stabilizationIntegerLattice n).add_mem hx0.1
      (by rw [haHalf]; exact hrightMem)
  · have hcoordLower : ∀ i : Fin m, (1 / 4 : ℚ) ≤ z.2 i * z.2 i := by
      intro i
      obtain ⟨k, hk⟩ := haOdd
      have hd0 : 2 * b i + a ≠ 0 := by omega
      have hsq : (1 : ℤ) ≤ (2 * b i + a) * (2 * b i + a) := by
        rcases lt_or_gt_of_ne hd0 with hdneg | hdpos
        · have : 2 * b i + a ≤ -1 := by omega
          nlinarith
        · have : 1 ≤ 2 * b i + a := by omega
          nlinarith
      have hsqQ : (1 : ℚ) ≤
          ((2 * b i + a : ℤ) : ℚ) * ((2 * b i + a : ℤ) : ℚ) := by
        exact_mod_cast hsq
      rw [hzcoord]
      push_cast at hsqQ
      nlinarith
    have hsumLower : (m : ℚ) * (1 / 4 : ℚ) ≤
        standardRatForm m z.2 z.2 := by
      rw [standardRatForm_apply]
      calc
        (m : ℚ) * (1 / 4 : ℚ) = ∑ _i : Fin m, (1 / 4 : ℚ) := by
          simp
        _ ≤ ∑ i, z.2 i * z.2 i :=
          Finset.sum_le_sum fun i _ => hcoordLower i
    have hmQ : (2 : ℚ) < (m : ℚ) * (1 / 4 : ℚ) := by
      have : (8 : ℚ) < (m : ℚ) := by exact_mod_cast (show 8 < m by omega)
      linarith
    linarith

/-! ## Exact root partition in the integral product -/

/-- A norm-two vector of the integral product belongs entirely to one factor.
The potentially mixed `(1,1)` case is excluded by the norm-one-free
hypothesis on `L`. -/
theorem normTwo_product_eq_leftRoot_or_dRoot {n : ℕ}
    (L : PDUnimodularLattice n)
    (hfree : ∀ v : L.carrier, L.pairing v v ≠ 1)
    {z : StabilizationSpace n}
    (hzM : z ∈ stabilizationIntegerLattice n)
    (hznorm : stabilizationForm L z z = 2) :
    (∃ r : NormTwoRoot L, z = leftCoordinateMap L r.1) ∨
      ∃ r : DRoot (24 - n),
        z = (0, intCoordsToRat r.vector) := by
  classical
  obtain ⟨hzL, hzR⟩ := Submodule.mem_prod.mp hzM
  obtain ⟨a, ha⟩ := mem_coordinateIntegerLattice.mp hzL
  obtain ⟨b, hb⟩ := mem_coordinateIntegerLattice.mp hzR
  let x : L.carrier := pdCoordEquiv L a
  have hzEq : z = (intCoordsToRat a, intCoordsToRat b) := by
    apply Prod.ext
    · funext i
      exact (ha i).symm
    · funext i
      exact (hb i).symm
  have hsum : L.pairing x x + intDot b b = 2 := by
    have hsumQ :
        (((L.pairing x x + intDot b b : ℤ)) : ℚ) = 2 := by
      rw [← hznorm, hzEq]
      simp only [stabilizationForm, prodForm_apply, pdRatForm_intCoords,
        standardRatForm_apply, intCoordsToRat_apply, x]
      simp only [intDot]
      push_cast
      rfl
    exact_mod_cast hsumQ
  have hxNonneg : 0 ≤ L.pairing x x := by
    by_cases hx : x = 0
    · simp [hx]
    · exact (L.positiveDefinite x hx).le
  have hbNonneg : 0 ≤ intDot b b := intDot_self_nonneg b
  have hxNeOne : L.pairing x x ≠ 1 := hfree x
  have hcases : L.pairing x x = 0 ∨ L.pairing x x = 2 := by omega
  rcases hcases with hx0 | hx2
  · right
    have hxzero : x = 0 := by
      by_contra hxne
      have := L.positiveDefinite x hxne
      rw [hx0] at this
      omega
    have ha0 : a = 0 := by
      apply (pdCoordEquiv L).injective
      simpa [x] using hxzero
    have hb2 : intDot b b = 2 := by omega
    obtain ⟨r, hr⟩ := DRoot.exists_vector_eq_of_intDot_self_eq_two b hb2
    refine ⟨r, ?_⟩
    rw [hzEq, ha0, ← hr]
    apply Prod.ext
    · funext i
      simp [intCoordsToRat]
    · rfl
  · left
    have hb0 : intDot b b = 0 := by omega
    have hbzero : b = 0 := (intDot_self_eq_zero_iff b).mp hb0
    let r : NormTwoRoot L := ⟨x, hx2⟩
    refine ⟨r, ?_⟩
    rw [hzEq, hbzero]
    apply Prod.ext
    · change intCoordsToRat a = intCoordsToRat (latticeCoords L x)
      congr 1
      apply (pdCoordEquiv L).injective
      rw [pdCoordEquiv_latticeCoords]
    · simp [leftCoordinateMap]

/-! ## A duplicate-free root equivalence -/

theorem stabilizationCharacteristic_pair_left {n : ℕ}
    (L : PDUnimodularLattice n) (c x : L.carrier) :
    stabilizationForm L (stabilizationCharacteristic L c)
      (leftCoordinateMap L x) = ((L.pairing c x : ℤ) : ℚ) := by
  simp only [stabilizationForm, stabilizationCharacteristic, leftCoordinateMap,
    LinearMap.comp_apply, LinearMap.inl_apply, prodForm_apply,
    pdRatForm_intCoords, map_zero, add_zero]
  rw [pdCoordEquiv_latticeCoords, pdCoordEquiv_latticeCoords]

theorem leftCoordinateMap_injective {n : ℕ} (L : PDUnimodularLattice n) :
    Function.Injective (leftCoordinateMap L) := by
  intro x y hxy
  have hfirst := congrArg Prod.fst hxy
  simp only [leftCoordinateMap, LinearMap.comp_apply, LinearMap.inl_apply] at hfirst
  have hcoords : latticeCoords L x = latticeCoords L y := by
    funext i
    have hi := congrFun hfirst i
    change (((latticeCoords L x i : ℤ) : ℚ)) =
      (((latticeCoords L y i : ℤ) : ℚ)) at hi
    exact_mod_cast hi
  change (pdFinBasis L).equivFun x = (pdFinBasis L).equivFun y at hcoords
  exact (pdFinBasis L).equivFun.injective hcoords

/-- A `D_m` root placed in the right factor. -/
def dRootCoordinate {n : ℕ} (r : DRoot (24 - n)) : StabilizationSpace n :=
  (0, intCoordsToRat r.vector)

theorem dRootCoordinate_injective {n : ℕ} :
    Function.Injective (@dRootCoordinate n) := by
  intro r s hrs
  apply DRoot.vector_injective
  have hright := congrArg Prod.snd hrs
  funext i
  have hi := congrFun hright i
  change (((r.vector i : ℤ) : ℚ)) = (((s.vector i : ℤ) : ℚ)) at hi
  exact_mod_cast hi

/-- Roots in the rational presentation, before transport to a bundled
`PDUnimodularLattice 24`. -/
def StabilizationRoot {n : ℕ} (L : PDUnimodularLattice n) (c : L.carrier) :=
  {z : StabilizationSpace n //
    z ∈ stabilizationEvenNeighbor L c ∧ stabilizationForm L z z = 2}

/-- A root of `L` lies in the even part of the standard neighbour. -/
noncomputable def leftStabilizationRoot {n : ℕ}
    (L : PDUnimodularLattice n) (c : L.carrier)
    (hc : IsCharacteristic L.pairing c) (r : NormTwoRoot L) :
    StabilizationRoot L c := by
  refine ⟨leftCoordinateMap L r.1, ?_, ?_⟩
  · apply characteristicEvenPart_le_evenNeighbor
    refine ⟨leftCoordinateMap_mem L r.1, ?_⟩
    obtain ⟨a, ha⟩ := hc r.1
    refine ⟨1 - a, ?_⟩
    rw [stabilizationCharacteristic_pair_left]
    have hpair : L.pairing c r.1 = 2 * (1 - a) := by
      rw [r.2] at ha
      omega
    rw [hpair]
  · rw [leftCoordinateMap_pairing]
    exact_mod_cast r.2

/-- A `D_m` root lies in the even part of the standard neighbour. -/
noncomputable def dStabilizationRoot {n : ℕ}
    (L : PDUnimodularLattice n) (c : L.carrier)
    (r : DRoot (24 - n)) : StabilizationRoot L c := by
  refine ⟨dRootCoordinate r, ?_, ?_⟩
  · apply characteristicEvenPart_le_evenNeighbor
    refine ⟨Submodule.mem_prod.mpr
        ⟨(coordinateIntegerLattice n).zero_mem, intCoordsToRat_mem _⟩, ?_⟩
    obtain ⟨a, ha⟩ := r.sum_vector_even
    refine ⟨a, ?_⟩
    simp only [stabilizationForm, stabilizationCharacteristic, dRootCoordinate,
      prodForm_apply, map_zero, zero_add, standardRatForm_apply,
      intCoordsToRat_apply, onesInt]
    norm_num only [Int.cast_one, one_mul]
    exact_mod_cast ha
  · simp only [stabilizationForm, dRootCoordinate, prodForm_apply, map_zero,
      zero_add, standardRatForm_apply, intCoordsToRat_apply]
    exact_mod_cast r.intDot_self

theorem leftStabilizationRoot_injective {n : ℕ}
    (L : PDUnimodularLattice n) (c : L.carrier)
    (hc : IsCharacteristic L.pairing c) :
    Function.Injective (leftStabilizationRoot L c hc) := by
  intro r s hrs
  apply Subtype.ext
  apply leftCoordinateMap_injective L
  exact Subtype.ext_iff.mp hrs

theorem dStabilizationRoot_injective {n : ℕ}
    (L : PDUnimodularLattice n) (c : L.carrier) :
    Function.Injective (dStabilizationRoot L c) := by
  intro r s hrs
  apply dRootCoordinate_injective
  exact Subtype.ext_iff.mp hrs

/-- Exact disjoint decomposition of the neighbour's roots. -/
noncomputable def stabilizationRootEquiv {n : ℕ} (hnhi : n ≤ 15)
    (L : PDUnimodularLattice n) (c : L.carrier)
    (hc : IsCharacteristic L.pairing c)
    (hfree : ∀ v : L.carrier, L.pairing v v ≠ 1) :
    (NormTwoRoot L ⊕ DRoot (24 - n)) ≃ StabilizationRoot L c := by
  let f : (NormTwoRoot L ⊕ DRoot (24 - n)) → StabilizationRoot L c
    | Sum.inl r => leftStabilizationRoot L c hc r
    | Sum.inr r => dStabilizationRoot L c r
  apply Equiv.ofBijective f
  constructor
  · intro r s hrs
    rcases r with r | r <;> rcases s with s | s
    · exact congrArg Sum.inl (leftStabilizationRoot_injective L c hc hrs)
    · exfalso
      have hcoord : leftCoordinateMap L r.1 = dRootCoordinate s :=
        Subtype.ext_iff.mp hrs
      have hzero : leftCoordinateMap L r.1 = 0 := by
        apply Prod.ext
        · simpa [dRootCoordinate] using congrArg Prod.fst hcoord
        · simp [leftCoordinateMap]
      have hrne : r.1 ≠ 0 := by
        change normTwoRootVal r ≠ 0
        exact normTwoRootVal_ne_zero r
      apply hrne
      apply leftCoordinateMap_injective L
      simpa only [map_zero] using hzero
    · exfalso
      have hcoord : dRootCoordinate r = leftCoordinateMap L s.1 :=
        Subtype.ext_iff.mp hrs
      have hzero : leftCoordinateMap L s.1 = 0 := by
        apply Prod.ext
        · simpa [dRootCoordinate] using (congrArg Prod.fst hcoord).symm
        · simp [leftCoordinateMap]
      have hsne : s.1 ≠ 0 := by
        change normTwoRootVal s ≠ 0
        exact normTwoRootVal_ne_zero s
      apply hsne
      apply leftCoordinateMap_injective L
      simpa only [map_zero] using hzero
    · exact congrArg Sum.inr (dStabilizationRoot_injective L c hrs)
  · intro z
    have hzM := normTwo_mem_stabilizationIntegerLattice hnhi L c z.2.1 z.2.2
    rcases normTwo_product_eq_leftRoot_or_dRoot L hfree hzM z.2.2 with
      ⟨r, hr⟩ | ⟨r, hr⟩
    · refine ⟨Sum.inl r, Subtype.ext ?_⟩
      exact hr.symm
    · refine ⟨Sum.inr r, Subtype.ext ?_⟩
      exact hr.symm

/-! ## Transport to the bundled rank-24 lattice -/

/-- Van der Blij's congruence supplies all algebraic data required by the
rank-24 moment transport. -/
theorem exists_evenNeighbor24Data_of_vanDerBlij
    (hvdB : VanDerBlijCongruenceInput) {n : ℕ}
    (hnlo : 12 ≤ n) (hnhi : n ≤ 15) (L : PDUnimodularLattice n)
    (hfree : ∀ v : L.carrier, L.pairing v v ≠ 1) :
    Nonempty (EvenNeighbor24Data L) := by
  classical
  obtain ⟨c, hc⟩ := exists_characteristicVector L
  let F := stabilizationForm L
  let M := stabilizationIntegerLattice n
  let w := stabilizationCharacteristic L c
  let H := stabilizationEvenNeighbor L c
  have hsymm : F.IsSymm := stabilizationForm_isSymm L
  have hpd : ∀ x : StabilizationSpace n, x ≠ 0 → 0 < F x x :=
    stabilizationForm_posDef L
  have hMlat : IsLattice ℚ M := stabilizationIntegerLattice_isLattice n
  have hMself : F.dualSubmodule M = M :=
    stabilizationIntegerLattice_selfDual L
  have hwM : w ∈ M := stabilizationCharacteristic_mem L c
  have hwdual : w ∈ F.dualSubmodule M := by
    rw [hMself]
    exact hwM
  have hchar : IsCharacteristicIn F M w :=
    stabilizationCharacteristic_isCharacteristicIn L c hc
  have hw8 : NormDivisibleByEight F w :=
    stabilizationCharacteristic_normDivisibleByEight hvdB (by omega) L c hc
  have hmpos : 0 < 24 - n := by omega
  let p := stabilizationPrimitive hmpos
  have hpM : p ∈ M := stabilizationPrimitive_mem hmpos
  have hwp : F w p = 1 :=
    stabilizationCharacteristic_pair_primitive L c hmpos
  have hHlat : IsLattice ℚ H :=
    evenNeighbor_isLattice hMlat hwdual
  have hHself : F.dualSubmodule H = H :=
    evenNeighbor_dual_eq_self hsymm hMself hwM hpM hwp hw8
  have hHeven : ∀ x ∈ H, IsEvenInteger (F x x) :=
    evenNeighbor_evenNorm hsymm hMself hchar hw8
  have hrank : Module.finrank ℚ (StabilizationSpace n) = 24 := by
    simp only [StabilizationSpace, Module.finrank_prod, Module.finrank_fin_fun]
    omega
  obtain ⟨N, e, he⟩ :=
    exists_pdUnimodularLattice hsymm hpd hrank hHlat hHself

  let leftDoubleH : L.carrier →ₗ[ℤ] H :=
    { toFun := fun x => ⟨(2 : ℤ) • leftCoordinateMap L x,
        characteristicEvenPart_le_evenNeighbor F M w
          (two_smul_mem_characteristicEvenPart
            (leftCoordinateMap_mem L x) (hwdual _ (leftCoordinateMap_mem L x)))⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        change (2 : ℤ) • leftCoordinateMap L (x + y) =
          (2 : ℤ) • leftCoordinateMap L x + (2 : ℤ) • leftCoordinateMap L y
        rw [map_add, smul_add]
      map_smul' := by
        intro a x
        apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply, map_smul]
        module }
  let leftDouble : L.carrier →ₗ[ℤ] N.carrier :=
    e.toLinearMap.comp leftDoubleH
  let leftRootH : NormTwoRoot L → H := fun r =>
    ⟨(leftStabilizationRoot L c hc r).1,
      (leftStabilizationRoot L c hc r).2.1⟩
  let leftRoot : NormTwoRoot L → N.carrier := fun r => e (leftRootH r)
  let dRootH : DRoot (24 - n) → H := fun r =>
    ⟨(dStabilizationRoot L c r).1, (dStabilizationRoot L c r).2.1⟩
  let dRoot : DRoot (24 - n) → N.carrier := fun r => e (dRootH r)

  have hEvenN : ∀ z : N.carrier, Even (N.pairing z z) := by
    intro z
    obtain ⟨a, ha⟩ := hHeven (e.symm z) (e.symm z).2
    refine ⟨a, ?_⟩
    have hp := he (e.symm z) (e.symm z)
    rw [e.apply_symm_apply] at hp
    have hEq : N.pairing z z = 2 * a := by
      exact_mod_cast hp.trans ha
    omega

  have hLeftDoublePairing : ∀ x y,
      N.pairing (leftDouble x) (leftDouble y) = 4 * L.pairing x y := by
    intro x y
    have hp := he (leftDoubleH x) (leftDoubleH y)
    change (((N.pairing (leftDouble x) (leftDouble y) : ℤ)) : ℚ) =
      F ((2 : ℤ) • leftCoordinateMap L x)
        ((2 : ℤ) • leftCoordinateMap L y) at hp
    have hF : F ((2 : ℤ) • leftCoordinateMap L x)
        ((2 : ℤ) • leftCoordinateMap L y) =
        (((4 * L.pairing x y : ℤ)) : ℚ) := by
      dsimp only [F]
      simp only [map_zsmul, LinearMap.smul_apply, leftCoordinateMap_pairing]
      push_cast
      ring
    rw [hF] at hp
    apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℚ)))
    exact hp
  have hLeftRootPairing : ∀ r x,
      N.pairing (leftRoot r) (leftDouble x) = 2 * L.pairing r.1 x := by
    intro r x
    have hp := he (leftRootH r) (leftDoubleH x)
    change (((N.pairing (leftRoot r) (leftDouble x) : ℤ)) : ℚ) =
      F (leftCoordinateMap L r.1) ((2 : ℤ) • leftCoordinateMap L x) at hp
    have hF : F (leftCoordinateMap L r.1)
        ((2 : ℤ) • leftCoordinateMap L x) =
        (((2 * L.pairing r.1 x : ℤ)) : ℚ) := by
      dsimp only [F]
      simp only [map_zsmul, leftCoordinateMap_pairing]
      push_cast
      ring
    rw [hF] at hp
    apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℚ)))
    exact hp
  have hDRootPairing : ∀ r s,
      N.pairing (dRoot r) (dRoot s) = intDot r.vector s.vector := by
    intro r s
    have hp := he (dRootH r) (dRootH s)
    change (((N.pairing (dRoot r) (dRoot s) : ℤ)) : ℚ) = _ at hp
    simp only [dRootH, dStabilizationRoot, dRootCoordinate, F,
      stabilizationForm, prodForm_apply, map_zero, zero_add,
      standardRatForm_apply, intCoordsToRat_apply] at hp
    exact_mod_cast hp
  have hCrossDouble : ∀ x r,
      N.pairing (leftDouble x) (dRoot r) = 0 := by
    intro x r
    have hp := he (leftDoubleH x) (dRootH r)
    change (((N.pairing (leftDouble x) (dRoot r) : ℤ)) : ℚ) =
      F ((2 : ℤ) • leftCoordinateMap L x) (dRootCoordinate r) at hp
    have hF : F ((2 : ℤ) • leftCoordinateMap L x) (dRootCoordinate r) = 0 := by
      dsimp only [F, stabilizationForm, dRootCoordinate, leftCoordinateMap]
      simp
    rw [hF] at hp
    apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℚ)))
    simpa only [Int.cast_zero] using hp
  have hCrossRoot : ∀ x r,
      N.pairing (leftRoot x) (dRoot r) = 0 := by
    intro x r
    have hp := he (leftRootH x) (dRootH r)
    change (((N.pairing (leftRoot x) (dRoot r) : ℤ)) : ℚ) =
      F (leftCoordinateMap L x.1) (dRootCoordinate r) at hp
    have hF : F (leftCoordinateMap L x.1) (dRootCoordinate r) = 0 := by
      dsimp only [F, stabilizationForm, dRootCoordinate, leftCoordinateMap]
      simp
    rw [hF] at hp
    apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℚ)))
    simpa only [Int.cast_zero] using hp

  let rootTransport : StabilizationRoot L c ≃ NormTwoRoot N := by
    let g : StabilizationRoot L c → NormTwoRoot N := fun r =>
      ⟨e ⟨r.1, r.2.1⟩, by
        have hp := he ⟨r.1, r.2.1⟩ ⟨r.1, r.2.1⟩
        exact_mod_cast hp.trans r.2.2⟩
    apply Equiv.ofBijective g
    constructor
    · intro r s hrs
      apply Subtype.ext
      have hv : e ⟨r.1, r.2.1⟩ = e ⟨s.1, s.2.1⟩ :=
        Subtype.ext_iff.mp hrs
      have hu : (⟨r.1, r.2.1⟩ : H) = ⟨s.1, s.2.1⟩ := e.injective hv
      have huv : r.1 = s.1 := congrArg (fun q : H => q.1) hu
      exact huv
    · intro r
      let u : H := e.symm r.1
      have huNorm : F u.1 u.1 = 2 := by
        have hp := he u u
        rw [e.apply_symm_apply] at hp
        calc
          F u.1 u.1 = ((N.pairing r.1 r.1 : ℤ) : ℚ) := hp.symm
          _ = 2 := by exact_mod_cast r.2
      let z : StabilizationRoot L c := ⟨u.1, u.2, huNorm⟩
      refine ⟨z, Subtype.ext ?_⟩
      exact e.apply_symm_apply r.1
  let rootEquiv : (NormTwoRoot L ⊕ DRoot (24 - n)) ≃ NormTwoRoot N :=
    (stabilizationRootEquiv hnhi L c hc hfree).trans rootTransport
  have hRootSum : ∀ f : N.carrier → ℤ,
      (∑ r : NormTwoRoot N, f r.1) =
        (∑ r : NormTwoRoot L, f (leftRoot r)) +
          ∑ r : DRoot (24 - n), f (dRoot r) := by
    intro f
    calc
      (∑ r : NormTwoRoot N, f r.1) =
          ∑ s : NormTwoRoot L ⊕ DRoot (24 - n), f (rootEquiv s).1 :=
        (rootEquiv.sum_comp (fun r : NormTwoRoot N => f r.1)).symm
      _ = (∑ r : NormTwoRoot L, f (leftRoot r)) +
          ∑ r : DRoot (24 - n), f (dRoot r) := by
        rw [Fintype.sum_sum_type]
        rfl
  exact ⟨{
    neighbor := N
    evenNorm := hEvenN
    leftDouble := leftDouble
    leftDoublePairing := hLeftDoublePairing
    leftRoot := leftRoot
    leftRootPairing := hLeftRootPairing
    dRoot := dRoot
    dRootPairing := hDRootPairing
    crossDoublePairing := hCrossDouble
    crossRootPairing := hCrossRoot
    rootSum := hRootSum }⟩

/-- The complete algebraic rank-24 neighbour input follows from van der
Blij's characteristic-norm congruence. -/
theorem evenNeighbor24Input_of_vanDerBlij
    (hvdB : VanDerBlijCongruenceInput) : EvenNeighbor24Input := by
  intro n hnlo hnhi L hfree
  exact exists_evenNeighbor24Data_of_vanDerBlij hvdB hnlo hnhi L hfree

/-- It is enough to provide one correctly normed characteristic vector per
lattice. -/
theorem evenNeighbor24Input_of_vanDerBlijWitness
    (hvdB : VanDerBlijWitnessInput) : EvenNeighbor24Input :=
  evenNeighbor24Input_of_vanDerBlij (vanDerBlijCongruence_of_witness hvdB)

/-- The low-rank theta moment boundary factors into van der Blij's
finite congruence and the scalar root-shell theorem in rank twenty four. -/
theorem thetaRootSecondMoment_of_vanDerBlij_and_rank24
    (hvdB : VanDerBlijCongruenceInput)
    (h24 : EvenUnimodular24RootScalarInput) :
    ThetaRootSecondMomentInput :=
  thetaRootSecondMoment_of_evenNeighbor24
    (evenNeighbor24Input_of_vanDerBlij hvdB) h24

/-- Audit-facing version with the minimal van der Blij witness boundary. -/
theorem thetaRootSecondMoment_of_vanDerBlijWitness_and_rank24
    (hvdB : VanDerBlijWitnessInput)
    (h24 : EvenUnimodular24RootScalarInput) :
    ThetaRootSecondMomentInput :=
  thetaRootSecondMoment_of_evenNeighbor24
    (evenNeighbor24Input_of_vanDerBlijWitness hvdB) h24

end SRG266.Lattice
