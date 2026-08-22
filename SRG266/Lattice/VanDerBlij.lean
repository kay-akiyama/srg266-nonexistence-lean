/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.EvenUnimodularRank
import SRG266.Lattice.Rank24EvenNeighborConstruction

/-!
# Van der Blij's characteristic-vector congruence

This file proves van der Blij's lemma for positive-definite integral
unimodular lattices.  The proof avoids a separate finite Gauss-sum
calculation.  Given a characteristic vector `c`, append between one and
eight standard coordinates so that the norm of `(c, 1, ..., 1)` is divisible
by eight.  Its standard even neighbour is an even unimodular lattice.
Divisibility of the rank of that neighbour by eight then gives

`c · c = rank L (mod 8)`.

All analytic input needed for the rank-divisibility theorem is proved in
`EvenUnimodularRank.lean` from lattice Poisson summation.
-/

namespace SRG266.Lattice

open scoped BigOperators

/-! ## Arbitrary-rank standard stabilization -/

/-- Rational ambient space obtained by appending `m` standard coordinates. -/
abbrev VanDerBlijStabilizationSpace (n m : ℕ) :=
  (Fin n → ℚ) × (Fin m → ℚ)

/-- Orthogonal product of the coordinate form of `L` and the standard form. -/
noncomputable def vanDerBlijStabilizationForm {n m : ℕ}
    (L : PDUnimodularLattice n) :
    LinearMap.BilinForm ℚ (VanDerBlijStabilizationSpace n m) :=
  prodForm (pdRatForm L) (standardRatForm m)

/-- Integral product lattice before adjoining the half-characteristic. -/
def vanDerBlijStabilizationIntegerLattice (n m : ℕ) :
    Submodule ℤ (VanDerBlijStabilizationSpace n m) :=
  (coordinateIntegerLattice n).prod (coordinateIntegerLattice m)

theorem vanDerBlijStabilizationForm_isSymm {n m : ℕ}
    (L : PDUnimodularLattice n) :
    (vanDerBlijStabilizationForm (m := m) L).IsSymm :=
  prodForm_isSymm (pdRatForm_isSymm L) (standardRatForm_isSymm m)

theorem vanDerBlijStabilizationForm_posDef {n m : ℕ}
    (L : PDUnimodularLattice n) :
    ∀ x : VanDerBlijStabilizationSpace n m, x ≠ 0 →
      0 < vanDerBlijStabilizationForm L x x :=
  prodForm_posDef (pdRatForm_posDef L) (standardRatForm_posDef m)

theorem vanDerBlijStabilizationIntegerLattice_isLattice (n m : ℕ) :
    IsLattice ℚ (vanDerBlijStabilizationIntegerLattice n m) :=
  isLattice_prod (coordinateIntegerLattice_isLattice n)
    (coordinateIntegerLattice_isLattice m)

theorem vanDerBlijStabilizationIntegerLattice_selfDual {n m : ℕ}
    (L : PDUnimodularLattice n) :
    (vanDerBlijStabilizationForm (m := m) L).dualSubmodule
        (vanDerBlijStabilizationIntegerLattice n m) =
      vanDerBlijStabilizationIntegerLattice n m := by
  rw [vanDerBlijStabilizationForm,
    vanDerBlijStabilizationIntegerLattice, dualSubmodule_prodForm,
    pdRatForm_dual_coordinateIntegerLattice,
    standardRatForm_dual_coordinateIntegerLattice]

/-- The product characteristic vector `(c, 1, ..., 1)`. -/
noncomputable def vanDerBlijStabilizationCharacteristic {n m : ℕ}
    (L : PDUnimodularLattice n) (c : L.carrier) :
    VanDerBlijStabilizationSpace n m :=
  (intCoordsToRat (latticeCoords L c), intCoordsToRat (onesInt m))

theorem vanDerBlijStabilizationCharacteristic_mem {n m : ℕ}
    (L : PDUnimodularLattice n) (c : L.carrier) :
    vanDerBlijStabilizationCharacteristic (m := m) L c ∈
      vanDerBlijStabilizationIntegerLattice n m :=
  Submodule.mem_prod.mpr ⟨intCoordsToRat_mem _, intCoordsToRat_mem _⟩

/-- The first basis vector in the nonempty standard summand. -/
def vanDerBlijStabilizationPrimitive {n m : ℕ} (hm : 0 < m) :
    VanDerBlijStabilizationSpace n m :=
  (0, intCoordsToRat (Pi.single ⟨0, hm⟩ 1))

theorem vanDerBlijStabilizationPrimitive_mem {n m : ℕ} (hm : 0 < m) :
    vanDerBlijStabilizationPrimitive (n := n) hm ∈
      vanDerBlijStabilizationIntegerLattice n m :=
  Submodule.mem_prod.mpr
    ⟨(coordinateIntegerLattice n).zero_mem, intCoordsToRat_mem _⟩

theorem vanDerBlijStabilizationCharacteristic_pair_primitive {n m : ℕ}
    (L : PDUnimodularLattice n) (c : L.carrier) (hm : 0 < m) :
    vanDerBlijStabilizationForm L
        (vanDerBlijStabilizationCharacteristic (m := m) L c)
        (vanDerBlijStabilizationPrimitive (n := n) hm) = 1 := by
  simp only [vanDerBlijStabilizationForm,
    vanDerBlijStabilizationCharacteristic,
    vanDerBlijStabilizationPrimitive, prodForm_apply, map_zero, zero_add,
    standardRatForm_apply, intCoordsToRat_apply, onesInt]
  norm_num only [Int.cast_one, one_mul]
  rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
  · simp
  · intro j _ hji
    simp [hji]
  · exact fun h => absurd (Finset.mem_univ (⟨0, hm⟩ : Fin m)) h

/-- The product vector is characteristic in the integral product lattice. -/
theorem vanDerBlijStabilizationCharacteristic_isCharacteristicIn {n m : ℕ}
    (L : PDUnimodularLattice n) (c : L.carrier)
    (hc : IsCharacteristic L.pairing c) :
    IsCharacteristicIn (vanDerBlijStabilizationForm L)
      (vanDerBlijStabilizationIntegerLattice n m)
      (vanDerBlijStabilizationCharacteristic L c) := by
  intro x hx
  obtain ⟨hxL, hxR⟩ := Submodule.mem_prod.mp hx
  obtain ⟨a, ha⟩ := mem_coordinateIntegerLattice.mp hxL
  obtain ⟨b, hb⟩ := mem_coordinateIntegerLattice.mp hxR
  obtain ⟨u, hu⟩ := hc (pdCoordEquiv L a)
  obtain ⟨v, hv⟩ := standard_ones_characteristic m b
  refine ⟨u + v, ?_⟩
  have hxEq : x = (intCoordsToRat a, intCoordsToRat b) := by
    apply Prod.ext
    · funext i
      exact (ha i).symm
    · funext i
      exact (hb i).symm
  rw [hxEq]
  simp only [vanDerBlijStabilizationForm,
    vanDerBlijStabilizationCharacteristic, prodForm_apply,
    pdRatForm_intCoords, standardRatForm_apply, intCoordsToRat_apply]
  rw [pdCoordEquiv_latticeCoords]
  have hbb : (∑ i, (b i : ℚ) * (b i : ℚ)) = ((intDot b b : ℤ) : ℚ) := by
    simp only [intDot]
    push_cast
    rfl
  have hones : (∑ i, (onesInt m i : ℚ) * (b i : ℚ)) =
      ((intDot (onesInt m) b : ℤ) : ℚ) := by
    simp only [intDot]
    push_cast
    rfl
  rw [hbb, hones]
  change
    (((L.pairing (pdCoordEquiv L a) (pdCoordEquiv L a) : ℤ) : ℚ) +
        ((intDot b b : ℤ) : ℚ)) -
      (((L.pairing c (pdCoordEquiv L a) : ℤ) : ℚ) +
        ((intDot (onesInt m) b : ℤ) : ℚ)) =
      (((2 * (u + v) : ℤ)) : ℚ)
  norm_cast
  linear_combination hu + hv

theorem vanDerBlijStabilizationCharacteristic_norm {n m : ℕ}
    (L : PDUnimodularLattice n) (c : L.carrier) :
    vanDerBlijStabilizationForm L
        (vanDerBlijStabilizationCharacteristic (m := m) L c)
        (vanDerBlijStabilizationCharacteristic (m := m) L c) =
      (((L.pairing c c + (m : ℤ) : ℤ)) : ℚ) := by
  simp only [vanDerBlijStabilizationForm,
    vanDerBlijStabilizationCharacteristic, prodForm_apply,
    pdRatForm_intCoords, standardRatForm_apply, intCoordsToRat_apply,
    onesInt, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [pdCoordEquiv_latticeCoords]
  norm_num

theorem vanDerBlijStabilizationCharacteristic_normDivisibleByEight
    {n m : ℕ} (L : PDUnimodularLattice n) (c : L.carrier)
    {a : ℤ} (hdiv : L.pairing c c + (m : ℤ) = 8 * a) :
    NormDivisibleByEight (vanDerBlijStabilizationForm (m := m) L)
      (vanDerBlijStabilizationCharacteristic (m := m) L c) := by
  refine ⟨a, ?_⟩
  rw [vanDerBlijStabilizationCharacteristic_norm, hdiv]

/-! ## The even neighbour and rank comparison -/

/-- Appending a nonempty standard summand and choosing divisible
characteristic norm produces an even unimodular lattice of rank `n + m`. -/
theorem exists_even_unimodular_vanDerBlijStabilization {n m : ℕ}
    (hm : 0 < m) (L : PDUnimodularLattice n) (c : L.carrier)
    (hc : IsCharacteristic L.pairing c) {a : ℤ}
    (hdiv : L.pairing c c + (m : ℤ) = 8 * a) :
    ∃ E : PDUnimodularLattice (n + m),
      ∀ x : E.carrier, Even (E.pairing x x) := by
  let F := vanDerBlijStabilizationForm (m := m) L
  let M := vanDerBlijStabilizationIntegerLattice n m
  let w := vanDerBlijStabilizationCharacteristic (m := m) L c
  let H := evenNeighbor F M w
  let p := vanDerBlijStabilizationPrimitive (n := n) hm
  have hsymm : F.IsSymm := vanDerBlijStabilizationForm_isSymm L
  have hpd : ∀ x : VanDerBlijStabilizationSpace n m, x ≠ 0 → 0 < F x x :=
    vanDerBlijStabilizationForm_posDef L
  have hMlat : IsLattice ℚ M :=
    vanDerBlijStabilizationIntegerLattice_isLattice n m
  have hMself : F.dualSubmodule M = M :=
    vanDerBlijStabilizationIntegerLattice_selfDual L
  have hwM : w ∈ M := vanDerBlijStabilizationCharacteristic_mem L c
  have hwdual : w ∈ F.dualSubmodule M := by rw [hMself]; exact hwM
  have hchar : IsCharacteristicIn F M w :=
    vanDerBlijStabilizationCharacteristic_isCharacteristicIn L c hc
  have hw8 : NormDivisibleByEight F w :=
    vanDerBlijStabilizationCharacteristic_normDivisibleByEight L c hdiv
  have hpM : p ∈ M := vanDerBlijStabilizationPrimitive_mem hm
  have hwp : F w p = 1 :=
    vanDerBlijStabilizationCharacteristic_pair_primitive L c hm
  have hHlat : IsLattice ℚ H := evenNeighbor_isLattice hMlat hwdual
  have hHself : F.dualSubmodule H = H :=
    evenNeighbor_dual_eq_self hsymm hMself hwM hpM hwp hw8
  have hHeven : ∀ x ∈ H, IsEvenInteger (F x x) :=
    evenNeighbor_evenNorm hsymm hMself hchar hw8
  have hrank : Module.finrank ℚ (VanDerBlijStabilizationSpace n m) = n + m := by
    simp [VanDerBlijStabilizationSpace, Module.finrank_prod]
  obtain ⟨E, e, he⟩ :=
    exists_pdUnimodularLattice hsymm hpd hrank hHlat hHself
  refine ⟨E, ?_⟩
  intro z
  obtain ⟨d, hd⟩ := hHeven (e.symm z) (e.symm z).2
  refine ⟨d, ?_⟩
  have hp := he (e.symm z) (e.symm z)
  rw [e.apply_symm_apply] at hp
  have hEq : E.pairing z z = 2 * d := by
    exact_mod_cast hp.trans hd
  omega

/-! ## Van der Blij congruence -/

/-- Van der Blij's characteristic-norm congruence, proved internally. -/
theorem vanDerBlijCongruence : VanDerBlijCongruenceInput := by
  intro n L c hc
  let q : ℤ := L.pairing c c
  let r : ℤ := q % 8
  let m : ℕ := Int.toNat (8 - r)
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    exact Int.emod_nonneg q (by norm_num)
  have hr8 : r < 8 := by
    dsimp only [r]
    exact Int.emod_lt_of_pos q (by norm_num)
  have hmCast : (m : ℤ) = 8 - r := by
    dsimp only [m]
    rw [Int.toNat_of_nonneg]
    omega
  have hm : 0 < m := by
    have hmInt : (0 : ℤ) < (m : ℤ) := by rw [hmCast]; omega
    exact_mod_cast hmInt
  have hqr : r + 8 * (q / 8) = q := by
    dsimp only [r]
    exact Int.emod_add_mul_ediv q 8
  have hdiv : q + (m : ℤ) = 8 * (q / 8 + 1) := by
    rw [hmCast]
    omega
  obtain ⟨E, hEeven⟩ := exists_even_unimodular_vanDerBlijStabilization
    hm L c hc hdiv
  obtain ⟨b, hb⟩ := eight_dvd_rank_of_even_unimodular E hEeven
  have hbInt : (n : ℤ) + (m : ℤ) = 8 * (b : ℤ) := by
    exact_mod_cast hb
  refine ⟨q / 8 + 1 - (b : ℤ), ?_⟩
  change q = (n : ℤ) + 8 * (q / 8 + 1 - (b : ℤ))
  omega

/-- Minimal witness form used by the rank-24 stabilization. -/
theorem vanDerBlijWitness : VanDerBlijWitnessInput := by
  intro n L
  obtain ⟨c, hc⟩ := exists_characteristicVector L
  exact ⟨c, hc, vanDerBlijCongruence n L c hc⟩

end SRG266.Lattice
