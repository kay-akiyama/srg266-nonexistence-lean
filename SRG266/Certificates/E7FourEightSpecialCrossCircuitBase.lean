/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Bit-vector circuit for the special `4 × 8` Clebsch bound

The sixteen negative neighbourhoods are literal bit masks. Both cardinalities
fit in five bits, so the circuit has no arithmetic overflow. Its exhaustive
kernel audit is split into bounded modules downstream.
-/

namespace SRG266
namespace E7FourEightSpecialCrossCircuit

def boolCount (b : Bool) : BitVec 5 :=
  if b then 1#5 else 0#5

def selectedCount (bits : BitVec 16) : BitVec 5 :=
  boolCount bits[0] + boolCount bits[1] +
  boolCount bits[2] + boolCount bits[3] +
  boolCount bits[4] + boolCount bits[5] +
  boolCount bits[6] + boolCount bits[7] +
  boolCount bits[8] + boolCount bits[9] +
  boolCount bits[10] + boolCount bits[11] +
  boolCount bits[12] + boolCount bits[13] +
  boolCount bits[14] + boolCount bits[15]

def allowedTerm (bits mask : BitVec 16) : BitVec 5 :=
  if bits &&& mask = 0#16 then 1#5 else 0#5

def allowedCount (bits : BitVec 16) : BitVec 5 :=
  allowedTerm bits (BitVec.ofNat 16 3968) +
  allowedTerm bits (BitVec.ofNat 16 5728) +
  allowedTerm bits (BitVec.ofNat 16 9552) +
  allowedTerm bits (BitVec.ofNat 16 17584) +
  allowedTerm bits (BitVec.ofNat 16 6668) +
  allowedTerm bits (BitVec.ofNat 16 10506) +
  allowedTerm bits (BitVec.ofNat 16 18566) +
  allowedTerm bits (BitVec.ofNat 16 12361) +
  allowedTerm bits (BitVec.ofNat 16 20517) +
  allowedTerm bits (BitVec.ofNat 16 24595) +
  allowedTerm bits (BitVec.ofNat 16 32783) +
  allowedTerm bits (BitVec.ofNat 16 32881) +
  allowedTerm bits (BitVec.ofNat 16 33170) +
  allowedTerm bits (BitVec.ofNat 16 33444) +
  allowedTerm bits (BitVec.ofNat 16 33608) +
  allowedTerm bits (BitVec.ofNat 16 31744)

def clebschProperty (bits : BitVec 16) : Prop :=
  selectedCount bits ≤ 5#5 ∨ allowedCount bits ≤ 5#5

def clebschBlock (q : Nat) : Prop :=
  ∀ r : Fin 1024,
    clebschProperty (BitVec.ofNat 16 (1024 * q + r.1))

end E7FourEightSpecialCrossCircuit
end SRG266
