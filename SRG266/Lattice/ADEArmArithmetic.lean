/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import Mathlib.NumberTheory.ADEInequality

/-!
# Elementary arithmetic of three positive arm lengths

The three affine obstructions make the usual reciprocal inequality
unnecessary.  Three positive arm lengths either describe `D`, `E6`, `E7`, or
`E8`, or (after a permutation) dominate one of `(2,2,2)`, `(1,3,3)`, or
`(1,2,5)`.
-/

namespace SRG266
namespace Lattice

def IsDArmTriple (a b c : ℕ) : Prop :=
  (a = 1 ∧ b = 1) ∨ (a = 1 ∧ c = 1) ∨ (b = 1 ∧ c = 1)

def IsE6ArmTriple (a b c : ℕ) : Prop :=
  (a = 1 ∧ b = 2 ∧ c = 2) ∨
  (b = 1 ∧ a = 2 ∧ c = 2) ∨
  (c = 1 ∧ a = 2 ∧ b = 2)

def IsE7ArmTriple (a b c : ℕ) : Prop :=
  (a = 1 ∧ b = 2 ∧ c = 3) ∨ (a = 1 ∧ c = 2 ∧ b = 3) ∨
  (b = 1 ∧ a = 2 ∧ c = 3) ∨ (b = 1 ∧ c = 2 ∧ a = 3) ∨
  (c = 1 ∧ a = 2 ∧ b = 3) ∨ (c = 1 ∧ b = 2 ∧ a = 3)

def IsE8ArmTriple (a b c : ℕ) : Prop :=
  (a = 1 ∧ b = 2 ∧ c = 4) ∨ (a = 1 ∧ c = 2 ∧ b = 4) ∨
  (b = 1 ∧ a = 2 ∧ c = 4) ∨ (b = 1 ∧ c = 2 ∧ a = 4) ∨
  (c = 1 ∧ a = 2 ∧ b = 4) ∨ (c = 1 ∧ b = 2 ∧ a = 4)

def HasAffineE6Subtripod (a b c : ℕ) : Prop := 2 ≤ a ∧ 2 ≤ b ∧ 2 ≤ c

def HasAffineE7Subtripod (a b c : ℕ) : Prop :=
  (1 ≤ a ∧ 3 ≤ b ∧ 3 ≤ c) ∨
  (1 ≤ b ∧ 3 ≤ a ∧ 3 ≤ c) ∨
  (1 ≤ c ∧ 3 ≤ a ∧ 3 ≤ b)

def HasAffineE8Subtripod (a b c : ℕ) : Prop :=
  (1 ≤ a ∧ 2 ≤ b ∧ 5 ≤ c) ∨ (1 ≤ a ∧ 2 ≤ c ∧ 5 ≤ b) ∨
  (1 ≤ b ∧ 2 ≤ a ∧ 5 ≤ c) ∨ (1 ≤ b ∧ 2 ≤ c ∧ 5 ≤ a) ∨
  (1 ≤ c ∧ 2 ≤ a ∧ 5 ≤ b) ∨ (1 ≤ c ∧ 2 ≤ b ∧ 5 ≤ a)

/-- Data-bearing form of the complete three-arm case split.  Constructor
names record the order of the three arms. -/
inductive ArmOutcome (a b c : ℕ) : Type
  | d01 (ha : a = 1) (hb : b = 1)
  | d02 (ha : a = 1) (hc : c = 1)
  | d12 (hb : b = 1) (hc : c = 1)
  | e6_012 (ha : a = 1) (hb : b = 2) (hc : c = 2)
  | e6_102 (hb : b = 1) (ha : a = 2) (hc : c = 2)
  | e6_201 (hc : c = 1) (ha : a = 2) (hb : b = 2)
  | e7_012 (ha : a = 1) (hb : b = 2) (hc : c = 3)
  | e7_021 (ha : a = 1) (hc : c = 2) (hb : b = 3)
  | e7_102 (hb : b = 1) (ha : a = 2) (hc : c = 3)
  | e7_120 (hb : b = 1) (hc : c = 2) (ha : a = 3)
  | e7_201 (hc : c = 1) (ha : a = 2) (hb : b = 3)
  | e7_210 (hc : c = 1) (hb : b = 2) (ha : a = 3)
  | e8_012 (ha : a = 1) (hb : b = 2) (hc : c = 4)
  | e8_021 (ha : a = 1) (hc : c = 2) (hb : b = 4)
  | e8_102 (hb : b = 1) (ha : a = 2) (hc : c = 4)
  | e8_120 (hb : b = 1) (hc : c = 2) (ha : a = 4)
  | e8_201 (hc : c = 1) (ha : a = 2) (hb : b = 4)
  | e8_210 (hc : c = 1) (hb : b = 2) (ha : a = 4)
  | affineE6 (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
  | affineE7_0 (ha : 1 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c)
  | affineE7_1 (hb : 1 ≤ b) (ha : 3 ≤ a) (hc : 3 ≤ c)
  | affineE7_2 (hc : 1 ≤ c) (ha : 3 ≤ a) (hb : 3 ≤ b)
  | affineE8_012 (ha : 1 ≤ a) (hb : 2 ≤ b) (hc : 5 ≤ c)
  | affineE8_021 (ha : 1 ≤ a) (hc : 2 ≤ c) (hb : 5 ≤ b)
  | affineE8_102 (hb : 1 ≤ b) (ha : 2 ≤ a) (hc : 5 ≤ c)
  | affineE8_120 (hb : 1 ≤ b) (hc : 2 ≤ c) (ha : 5 ≤ a)
  | affineE8_201 (hc : 1 ≤ c) (ha : 2 ≤ a) (hb : 5 ≤ b)
  | affineE8_210 (hc : 1 ≤ c) (hb : 2 ≤ b) (ha : 5 ≤ a)

/-- Complete Presburger split for three nonempty arms. -/
def three_arm_arithmetic_classification {a b c : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) : ArmOutcome a b c := by
  by_cases ha1 : a = 1
  · by_cases hb1 : b = 1
    · exact .d01 ha1 hb1
    · by_cases hc1 : c = 1
      · exact .d02 ha1 hc1
      · by_cases hb2 : b = 2
        · by_cases hc2 : c = 2
          · exact .e6_012 ha1 hb2 hc2
          · by_cases hc3 : c = 3
            · exact .e7_012 ha1 hb2 hc3
            · by_cases hc4 : c = 4
              · exact .e8_012 ha1 hb2 hc4
              · exact .affineE8_012 ha (by omega) (by omega)
        · by_cases hc2 : c = 2
          · by_cases hb3 : b = 3
            · exact .e7_021 ha1 hc2 hb3
            · by_cases hb4 : b = 4
              · exact .e8_021 ha1 hc2 hb4
              · exact .affineE8_021 ha (by omega) (by omega)
          · exact .affineE7_0 ha (by omega) (by omega)
  · by_cases hb1 : b = 1
    · by_cases hc1 : c = 1
      · exact .d12 hb1 hc1
      · by_cases ha2 : a = 2
        · by_cases hc2 : c = 2
          · exact .e6_102 hb1 ha2 hc2
          · by_cases hc3 : c = 3
            · exact .e7_102 hb1 ha2 hc3
            · by_cases hc4 : c = 4
              · exact .e8_102 hb1 ha2 hc4
              · exact .affineE8_102 hb (by omega) (by omega)
        · by_cases hc2 : c = 2
          · by_cases ha3 : a = 3
            · exact .e7_120 hb1 hc2 ha3
            · by_cases ha4 : a = 4
              · exact .e8_120 hb1 hc2 ha4
              · exact .affineE8_120 hb (by omega) (by omega)
          · exact .affineE7_1 hb (by omega) (by omega)
    · by_cases hc1 : c = 1
      · by_cases ha2 : a = 2
        · by_cases hb2 : b = 2
          · exact .e6_201 hc1 ha2 hb2
          · by_cases hb3 : b = 3
            · exact .e7_201 hc1 ha2 hb3
            · by_cases hb4 : b = 4
              · exact .e8_201 hc1 ha2 hb4
              · exact .affineE8_201 hc (by omega) (by omega)
        · by_cases hb2 : b = 2
          · by_cases ha3 : a = 3
            · exact .e7_210 hc1 hb2 ha3
            · by_cases ha4 : a = 4
              · exact .e8_210 hc1 hb2 ha4
              · exact .affineE8_210 hc (by omega) (by omega)
          · exact .affineE7_2 hc (by omega) (by omega)
      · exact .affineE6 (by omega) (by omega) (by omega)

end Lattice
end SRG266
