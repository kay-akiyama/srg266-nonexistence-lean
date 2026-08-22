/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.E7FourEightSpecialCrossCircuit

/-!
# Natural-number interpretation of the Clebsch bit-vector circuit
-/

namespace SRG266
namespace E7FourEightSpecialCrossCircuit

def selectedCountNat (bits : BitVec 16) : Nat :=
  (if bits[0] then 1 else 0) + (if bits[1] then 1 else 0) +
  (if bits[2] then 1 else 0) + (if bits[3] then 1 else 0) +
  (if bits[4] then 1 else 0) + (if bits[5] then 1 else 0) +
  (if bits[6] then 1 else 0) + (if bits[7] then 1 else 0) +
  (if bits[8] then 1 else 0) + (if bits[9] then 1 else 0) +
  (if bits[10] then 1 else 0) + (if bits[11] then 1 else 0) +
  (if bits[12] then 1 else 0) + (if bits[13] then 1 else 0) +
  (if bits[14] then 1 else 0) + (if bits[15] then 1 else 0)

def allowedCountNat (bits : BitVec 16) : Nat :=
  (if bits &&& BitVec.ofNat 16 3968 = 0#16 then 1 else 0) +
  (if bits &&& BitVec.ofNat 16 5728 = 0#16 then 1 else 0) +
  (if bits &&& BitVec.ofNat 16 9552 = 0#16 then 1 else 0) +
  (if bits &&& BitVec.ofNat 16 17584 = 0#16 then 1 else 0) +
  (if bits &&& BitVec.ofNat 16 6668 = 0#16 then 1 else 0) +
  (if bits &&& BitVec.ofNat 16 10506 = 0#16 then 1 else 0) +
  (if bits &&& BitVec.ofNat 16 18566 = 0#16 then 1 else 0) +
  (if bits &&& BitVec.ofNat 16 12361 = 0#16 then 1 else 0) +
  (if bits &&& BitVec.ofNat 16 20517 = 0#16 then 1 else 0) +
  (if bits &&& BitVec.ofNat 16 24595 = 0#16 then 1 else 0) +
  (if bits &&& BitVec.ofNat 16 32783 = 0#16 then 1 else 0) +
  (if bits &&& BitVec.ofNat 16 32881 = 0#16 then 1 else 0) +
  (if bits &&& BitVec.ofNat 16 33170 = 0#16 then 1 else 0) +
  (if bits &&& BitVec.ofNat 16 33444 = 0#16 then 1 else 0) +
  (if bits &&& BitVec.ofNat 16 33608 = 0#16 then 1 else 0) +
  (if bits &&& BitVec.ofNat 16 31744 = 0#16 then 1 else 0)

@[simp] theorem boolCount_toNat (b : Bool) :
    (boolCount b).toNat = if b then 1 else 0 := by
  cases b <;> rfl

@[simp] theorem allowedTerm_toNat (bits mask : BitVec 16) :
    (allowedTerm bits mask).toNat =
      if bits &&& mask = 0#16 then 1 else 0 := by
  by_cases h : bits &&& mask = 0#16 <;> simp [allowedTerm, h]

theorem selectedCount_toNat (bits : BitVec 16) :
    (selectedCount bits).toNat = selectedCountNat bits := by
  simp only [selectedCount, BitVec.toNat_add, boolCount_toNat,
    selectedCountNat]
  have h0 : (if bits[0] then 1 else 0) ≤ 1 := by split <;> omega
  have h1 : (if bits[1] then 1 else 0) ≤ 1 := by split <;> omega
  have h2 : (if bits[2] then 1 else 0) ≤ 1 := by split <;> omega
  have h3 : (if bits[3] then 1 else 0) ≤ 1 := by split <;> omega
  have h4 : (if bits[4] then 1 else 0) ≤ 1 := by split <;> omega
  have h5 : (if bits[5] then 1 else 0) ≤ 1 := by split <;> omega
  have h6 : (if bits[6] then 1 else 0) ≤ 1 := by split <;> omega
  have h7 : (if bits[7] then 1 else 0) ≤ 1 := by split <;> omega
  have h8 : (if bits[8] then 1 else 0) ≤ 1 := by split <;> omega
  have h9 : (if bits[9] then 1 else 0) ≤ 1 := by split <;> omega
  have h10 : (if bits[10] then 1 else 0) ≤ 1 := by split <;> omega
  have h11 : (if bits[11] then 1 else 0) ≤ 1 := by split <;> omega
  have h12 : (if bits[12] then 1 else 0) ≤ 1 := by split <;> omega
  have h13 : (if bits[13] then 1 else 0) ≤ 1 := by split <;> omega
  have h14 : (if bits[14] then 1 else 0) ≤ 1 := by split <;> omega
  have h15 : (if bits[15] then 1 else 0) ≤ 1 := by split <;> omega
  omega

theorem allowedCount_toNat (bits : BitVec 16) :
    (allowedCount bits).toNat = allowedCountNat bits := by
  simp only [allowedCount, BitVec.toNat_add, allowedTerm_toNat,
    allowedCountNat]
  have h0 : (if bits &&& BitVec.ofNat 16 3968 = 0#16 then 1 else 0) ≤ 1 := by split <;> omega
  have h1 : (if bits &&& BitVec.ofNat 16 5728 = 0#16 then 1 else 0) ≤ 1 := by split <;> omega
  have h2 : (if bits &&& BitVec.ofNat 16 9552 = 0#16 then 1 else 0) ≤ 1 := by split <;> omega
  have h3 : (if bits &&& BitVec.ofNat 16 17584 = 0#16 then 1 else 0) ≤ 1 := by split <;> omega
  have h4 : (if bits &&& BitVec.ofNat 16 6668 = 0#16 then 1 else 0) ≤ 1 := by split <;> omega
  have h5 : (if bits &&& BitVec.ofNat 16 10506 = 0#16 then 1 else 0) ≤ 1 := by split <;> omega
  have h6 : (if bits &&& BitVec.ofNat 16 18566 = 0#16 then 1 else 0) ≤ 1 := by split <;> omega
  have h7 : (if bits &&& BitVec.ofNat 16 12361 = 0#16 then 1 else 0) ≤ 1 := by split <;> omega
  have h8 : (if bits &&& BitVec.ofNat 16 20517 = 0#16 then 1 else 0) ≤ 1 := by split <;> omega
  have h9 : (if bits &&& BitVec.ofNat 16 24595 = 0#16 then 1 else 0) ≤ 1 := by split <;> omega
  have h10 : (if bits &&& BitVec.ofNat 16 32783 = 0#16 then 1 else 0) ≤ 1 := by split <;> omega
  have h11 : (if bits &&& BitVec.ofNat 16 32881 = 0#16 then 1 else 0) ≤ 1 := by split <;> omega
  have h12 : (if bits &&& BitVec.ofNat 16 33170 = 0#16 then 1 else 0) ≤ 1 := by split <;> omega
  have h13 : (if bits &&& BitVec.ofNat 16 33444 = 0#16 then 1 else 0) ≤ 1 := by split <;> omega
  have h14 : (if bits &&& BitVec.ofNat 16 33608 = 0#16 then 1 else 0) ≤ 1 := by split <;> omega
  have h15 : (if bits &&& BitVec.ofNat 16 31744 = 0#16 then 1 else 0) ≤ 1 := by split <;> omega
  omega

end E7FourEightSpecialCrossCircuit
end SRG266
