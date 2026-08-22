/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.CharacteristicVector

/-!
# Algebraic reduction of van der Blij's congruence

Characteristic vectors in a unimodular lattice form one coset of `2L`, and
their norms are congruent modulo eight.  Consequently the full van der Blij
statement follows once one correctly normed characteristic vector is known
for each lattice.

This file proves the algebraic reduction to `VanDerBlijWitnessInput`.
-/

namespace SRG266.Lattice

variable {n : ℕ}

/-- The difference of two characteristic vectors pairs evenly with every
lattice vector. -/
theorem two_dvd_pairing_characteristic_sub (L : PDUnimodularLattice n)
    {c d : L.carrier} (hc : IsCharacteristic L.pairing c)
    (hd : IsCharacteristic L.pairing d) (x : L.carrier) :
    (2 : ℤ) ∣ L.pairing (c - d) x := by
  obtain ⟨a, ha⟩ := hc x
  obtain ⟨b, hb⟩ := hd x
  refine ⟨b - a, ?_⟩
  rw [map_sub, LinearMap.sub_apply]
  linear_combination hb - ha

/-- Half of the pairing with the difference of two characteristic vectors,
specified first on the selected integral basis. -/
noncomputable def characteristicHalfCoeff (L : PDUnimodularLattice n)
    {c d : L.carrier} (hc : IsCharacteristic L.pairing c)
    (hd : IsCharacteristic L.pairing d) (i : Fin n) : ℤ :=
  (two_dvd_pairing_characteristic_sub L hc hd (pdFinBasis L i)).choose

theorem characteristicHalfCoeff_spec (L : PDUnimodularLattice n)
    {c d : L.carrier} (hc : IsCharacteristic L.pairing c)
    (hd : IsCharacteristic L.pairing d) (i : Fin n) :
    L.pairing (c - d) (pdFinBasis L i) =
      2 * characteristicHalfCoeff L hc hd i :=
  (two_dvd_pairing_characteristic_sub L hc hd (pdFinBasis L i)).choose_spec

/-- The integral functional obtained by halving the characteristic
difference. -/
noncomputable def characteristicHalfFunctional (L : PDUnimodularLattice n)
    {c d : L.carrier} (hc : IsCharacteristic L.pairing c)
    (hd : IsCharacteristic L.pairing d) : L.carrier →ₗ[ℤ] ℤ where
  toFun x := ∑ i, (pdFinBasis L).equivFun x i *
    characteristicHalfCoeff L hc hd i
  map_add' x y := by
    simp only [map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [RingHom.id_apply]
    ring

/-- Twice the halved functional is pairing with `c-d`. -/
theorem two_mul_characteristicHalfFunctional (L : PDUnimodularLattice n)
    {c d : L.carrier} (hc : IsCharacteristic L.pairing c)
    (hd : IsCharacteristic L.pairing d) (x : L.carrier) :
    2 * characteristicHalfFunctional L hc hd x = L.pairing (c - d) x := by
  let phi := characteristicHalfFunctional L hc hd
  have hmaps : (2 : ℤ) • phi = L.pairing (c - d) := by
    apply LinearMap.ext_on (pdFinBasis L).span_eq
    rintro _ ⟨i, rfl⟩
    change 2 * (∑ j, (pdFinBasis L).equivFun (pdFinBasis L i) j *
      characteristicHalfCoeff L hc hd j) =
        L.pairing (c - d) (pdFinBasis L i)
    simp only [Module.Basis.equivFun_self]
    rw [Finset.sum_eq_single i]
    · simpa only [if_pos, one_mul] using
        (characteristicHalfCoeff_spec L hc hd i).symm
    · intro j _ hji
      simp [Ne.symm hji]
    · exact fun hi => absurd (Finset.mem_univ i) hi
  have hx := LinearMap.congr_fun hmaps x
  simpa only [LinearMap.smul_apply, smul_eq_mul, phi] using hx

/-- Any two characteristic vectors differ by twice a lattice vector. -/
theorem characteristic_sub_eq_two_smul (L : PDUnimodularLattice n)
    {c d : L.carrier} (hc : IsCharacteristic L.pairing c)
    (hd : IsCharacteristic L.pairing d) :
    ∃ y : L.carrier, c - d = (2 : ℤ) • y := by
  let phi := characteristicHalfFunctional L hc hd
  obtain ⟨y, hy⟩ := L.unimodular.2 phi
  refine ⟨y, L.unimodular.1 ?_⟩
  apply LinearMap.ext
  intro x
  have hhalf := two_mul_characteristicHalfFunctional L hc hd x
  have hyx := LinearMap.congr_fun hy x
  simp only [map_zsmul, LinearMap.smul_apply, smul_eq_mul]
  rw [hyx]
  exact hhalf.symm

/-- Characteristic norms are constant modulo eight. -/
theorem characteristic_norm_mod_eight (L : PDUnimodularLattice n)
    {c d : L.carrier} (hc : IsCharacteristic L.pairing c)
    (hd : IsCharacteristic L.pairing d) :
    ∃ a : ℤ, L.pairing c c = L.pairing d d + 8 * a := by
  obtain ⟨y, hcd⟩ := characteristic_sub_eq_two_smul L hc hd
  have hcEq : c = d + (2 : ℤ) • y := by
    rw [← hcd]
    abel
  obtain ⟨a, ha⟩ := hd y
  have heven : ∃ b : ℤ, L.pairing d y + L.pairing y y = 2 * b := by
    refine ⟨L.pairing d y + a, ?_⟩
    linear_combination ha
  obtain ⟨b, hb⟩ := heven
  refine ⟨b, ?_⟩
  rw [hcEq]
  simp only [map_add, LinearMap.add_apply, map_zsmul,
    LinearMap.smul_apply, smul_eq_mul]
  rw [L.symmetric.eq y d]
  linear_combination 4 * hb

/-- Minimal witness form of van der Blij's lemma. -/
abbrev VanDerBlijWitnessInput : Prop :=
  ∀ (n : ℕ) (L : PDUnimodularLattice n),
    ∃ c : L.carrier, IsCharacteristic L.pairing c ∧
      ∃ a : ℤ, L.pairing c c = (n : ℤ) + 8 * a

/-- One correctly normed characteristic vector per lattice implies the full
congruence for every characteristic vector. -/
theorem vanDerBlijCongruence_of_witness
    (h : VanDerBlijWitnessInput) : VanDerBlijCongruenceInput := by
  intro n L c hc
  obtain ⟨d, hd, a, ha⟩ := h n L
  obtain ⟨b, hb⟩ := characteristic_norm_mod_eight L hc hd
  refine ⟨a + b, ?_⟩
  rw [hb, ha]
  ring

end SRG266.Lattice
