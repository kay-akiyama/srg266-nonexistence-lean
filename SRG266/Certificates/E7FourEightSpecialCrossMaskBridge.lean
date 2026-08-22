/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.E7FourEightSpecialCrossCircuitCounts
import SRG266.Certificates.E7FourEightSpecialSelectedBridge
import SRG266.Certificates.E7FourEightSpecialAllowedCountBridge

/-!
# Transport from the Clebsch circuit to finite subsets
-/

namespace SRG266
namespace E7FourEightSpecialCrossData

open E7FourEightSpecialCrossCircuit

def bitFunction (bits : BitVec 16) : ShellBits :=
  fun i => bits[i.1]

def negativeMask : Fin 16 → BitVec 16 := ![
  BitVec.ofNat 16 3968, BitVec.ofNat 16 5728,
  BitVec.ofNat 16 9552, BitVec.ofNat 16 17584,
  BitVec.ofNat 16 6668, BitVec.ofNat 16 10506,
  BitVec.ofNat 16 18566, BitVec.ofNat 16 12361,
  BitVec.ofNat 16 20517, BitVec.ofNat 16 24595,
  BitVec.ofNat 16 32783, BitVec.ofNat 16 32881,
  BitVec.ofNat 16 33170, BitVec.ofNat 16 33444,
  BitVec.ofNat 16 33608, BitVec.ofNat 16 31744
]

theorem allowedAt_iff_cells (bits : BitVec 16) (j : Fin 16) :
    allowedAt (bitFunction bits) j ↔
      (bits[0] = true → compatible 0 j = true) ∧
      (bits[1] = true → compatible 1 j = true) ∧
      (bits[2] = true → compatible 2 j = true) ∧
      (bits[3] = true → compatible 3 j = true) ∧
      (bits[4] = true → compatible 4 j = true) ∧
      (bits[5] = true → compatible 5 j = true) ∧
      (bits[6] = true → compatible 6 j = true) ∧
      (bits[7] = true → compatible 7 j = true) ∧
      (bits[8] = true → compatible 8 j = true) ∧
      (bits[9] = true → compatible 9 j = true) ∧
      (bits[10] = true → compatible 10 j = true) ∧
      (bits[11] = true → compatible 11 j = true) ∧
      (bits[12] = true → compatible 12 j = true) ∧
      (bits[13] = true → compatible 13 j = true) ∧
      (bits[14] = true → compatible 14 j = true) ∧
      (bits[15] = true → compatible 15 j = true) := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7,
      h 8, h 9, h 10, h 11, h 12, h 13, h 14, h 15⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7,
      h8, h9, h10, h11, h12, h13, h14, h15⟩ i hi
    fin_cases i <;> simp_all [bitFunction]

/-- A bitwise characterization of disjoint bit-vector support. -/
theorem bitVec_and_eq_zero_iff
    {n : Nat} (x y : BitVec n) :
    x &&& y = 0#n ↔
      ∀ i : Fin n, x[i.1] = true → y[i.1] = false := by
  constructor
  · intro h i hi
    have hbit := congrArg (fun z : BitVec n => z[i.1]) h
    simpa [hi] using hbit
  · intro h
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp only [BitVec.getElem_and, BitVec.getElem_zero]
    by_cases hx : x[i] = true
    · simp [hx, h ⟨i, hi⟩ hx]
    · have hx' : x[i] = false := Bool.eq_false_of_not_eq_true hx
      simp [hx']

/-- The stored negative mask is exactly the Boolean complement of the
compatibility column. -/
theorem negativeMask_bit_eq_not_compatible (i j : Fin 16) :
    (negativeMask j)[i.1] = !(compatible i j) := by
  decide +kernel +revert

theorem mask_zero_iff_allowedAt (bits : BitVec 16) (j : Fin 16) :
    bits &&& negativeMask j = 0#16 ↔ allowedAt (bitFunction bits) j := by
  rw [bitVec_and_eq_zero_iff]
  constructor
  · intro h i hi
    have hm := h i hi
    rw [negativeMask_bit_eq_not_compatible] at hm
    simpa using hm
  · intro h i hi
    rw [negativeMask_bit_eq_not_compatible]
    have hc := h i hi
    simpa using hc

theorem sum_fin16 (f : Fin 16 → Nat) :
    (∑ i, f i) =
      f ⟨0, by decide⟩ + f ⟨1, by decide⟩ +
      f ⟨2, by decide⟩ + f ⟨3, by decide⟩ +
      f ⟨4, by decide⟩ + f ⟨5, by decide⟩ +
      f ⟨6, by decide⟩ + f ⟨7, by decide⟩ +
      f ⟨8, by decide⟩ + f ⟨9, by decide⟩ +
      f ⟨10, by decide⟩ + f ⟨11, by decide⟩ +
      f ⟨12, by decide⟩ + f ⟨13, by decide⟩ +
      f ⟨14, by decide⟩ + f ⟨15, by decide⟩ := by
  rw [Finset.sum_fin_eq_sum_range]
  norm_num [Finset.sum_range_succ]

theorem selectedCountNat_eq_selectedCount (bits : BitVec 16) :
    E7FourEightSpecialCrossCircuit.selectedCountNat bits =
      selectedCount (bitFunction bits) := by
  simp only [E7FourEightSpecialCrossCircuit.selectedCountNat,
    selectedCount, bitFunction, sum_fin16]
  rfl

theorem allowedCountNat_eq_allowedCount (bits : BitVec 16) :
    E7FourEightSpecialCrossCircuit.allowedCountNat bits =
      allowedCount (bitFunction bits) := by
  simp only [E7FourEightSpecialCrossCircuit.allowedCountNat,
    allowedCount, sum_fin16]
  simp only [← mask_zero_iff_allowedAt]
  simp [negativeMask]
  rfl

def characteristicVector (s : Finset FirstWeight) : BitVec 16 :=
  (BitVec.iunfoldr
    (fun i (_ : Unit) => ((), characteristic s i)) ()).2

@[simp] theorem characteristicVector_getElem
    (s : Finset FirstWeight) (i : Fin 16) :
    (characteristicVector s)[i.1] = characteristic s i := by
  have h := BitVec.iunfoldr_getLsbD (f :=
      fun i (_ : Unit) => ((), characteristic s i))
      (fun _ => ()) i (by simp)
  rw [BitVec.getLsbD_eq_getElem i.2] at h
  exact h

theorem bitFunction_characteristicVector (s : Finset FirstWeight) :
    bitFunction (characteristicVector s) = characteristic s := by
  funext i
  exact characteristicVector_getElem s i

theorem circuitSelectedCount_card (s : Finset FirstWeight) :
    E7FourEightSpecialCrossCircuit.selectedCountNat
        (characteristicVector s) = s.card := by
  rw [selectedCountNat_eq_selectedCount,
    bitFunction_characteristicVector, selectedCount_characteristic]

theorem circuitAllowedCount_card (s : Finset FirstWeight) :
    E7FourEightSpecialCrossCircuit.allowedCountNat
        (characteristicVector s) = (crossAllowed s).card := by
  rw [allowedCountNat_eq_allowedCount,
    bitFunction_characteristicVector, allowedCount_characteristic]

/-- Kernel-checked circuit bound transported back to arbitrary subsets. -/
theorem clebsch_cross_bound_finset (s : Finset FirstWeight) :
    min s.card (crossAllowed s).card ≤ 5 := by
  let bits := characteristicVector s
  rcases E7FourEightSpecialCrossCircuit.clebsch_bound bits with h | h
  · have hnat :
        (E7FourEightSpecialCrossCircuit.selectedCount bits).toNat ≤
          (5#5).toNat := by
      simpa [BitVec.le_def] using h
    rw [E7FourEightSpecialCrossCircuit.selectedCount_toNat,
      circuitSelectedCount_card] at hnat
    norm_num at hnat
    exact (min_le_left _ _).trans hnat
  · have hnat :
        (E7FourEightSpecialCrossCircuit.allowedCount bits).toNat ≤
          (5#5).toNat := by
      simpa [BitVec.le_def] using h
    rw [E7FourEightSpecialCrossCircuit.allowedCount_toNat,
      circuitAllowedCount_card] at hnat
    norm_num at hnat
    exact (min_le_right _ _).trans hnat

end E7FourEightSpecialCrossData
end SRG266
