/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15CentroidEnumeration

/-!
# Positional codes for A15 centroid profiles

Comparing two 2,212-element lists of `Array ℤ` by repeated membership tests is
quadratic, so the comparison uses one natural number per profile, in the style
of `SRG266.Hosts.E7ComponentCode`.

A scaled A15 centroid profile has sixteen coordinates `d = 4a + r` with
`|a| ≤ 17` and `r ∈ {0, 2}`, so every coordinate lies in `[-68, 70]`.  Shifting
by seventy turns a coordinate into a digit in `[0, 140]`, and reading the
sixteen digits as a base-`141` numeral, most significant coordinate first,
gives `a15ProfileCode`.

The point of this module is `a15ProfileCode_injective`: on arrays of length
sixteen with coordinates in `[-70, 70]` the code determines the profile.  That
is what lets a set comparison of profiles be replaced by a set comparison of
codes.  Nothing here is evaluated by the kernel.
-/

namespace SRG266

/-- The digit of one profile coordinate, shifted to be nonnegative. -/
def a15ProfileDigit (z : ℤ) : ℕ := (z + 70).toNat

/-- The positional value of a coordinate list in base `141`, most significant
coordinate first. -/
def a15CodeOfList : List ℤ → ℕ
  | [] => 0
  | z :: rest => 141 ^ rest.length * a15ProfileDigit z + a15CodeOfList rest

/-- The base-`141` code of a profile array. -/
def a15ProfileCode (profile : Array ℤ) : ℕ := a15CodeOfList profile.toList

/-- The profiles on which the code is faithful: sixteen coordinates, each in
the range `[-70, 70]` that a single base-`141` digit represents. -/
def a15CodableProfile (profile : Array ℤ) : Bool :=
  (profile.toList.length == 16) &&
    profile.toList.all fun z => decide (-70 ≤ z) && decide (z ≤ 70)

theorem a15CodableProfile_length {profile : Array ℤ}
    (h : a15CodableProfile profile = true) : profile.toList.length = 16 := by
  simp only [a15CodableProfile, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem a15CodableProfile_bounds {profile : Array ℤ}
    (h : a15CodableProfile profile = true) :
    ∀ z ∈ profile.toList, -70 ≤ z ∧ z ≤ 70 := by
  simp only [a15CodableProfile, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  intro z hz
  exact h.2 z hz

/-- Every digit of a codable coordinate is a base-`141` digit. -/
theorem a15ProfileDigit_lt {z : ℤ} (h : z ≤ 70) : a15ProfileDigit z < 141 := by
  have : z + 70 ≤ 140 := by omega
  simpa [a15ProfileDigit] using Int.toNat_lt_toNat (by omega : (0:ℤ) < 141)
    |>.mpr (by omega : z + 70 < 141)

/-- A codable coordinate is recovered from its digit. -/
theorem a15ProfileDigit_cast {z : ℤ} (h : -70 ≤ z) :
    ((a15ProfileDigit z : ℕ) : ℤ) = z + 70 := by
  simp only [a15ProfileDigit]
  exact Int.toNat_of_nonneg (by omega)

/-- A code is bounded by the base raised to the number of coordinates. -/
theorem a15CodeOfList_lt :
    ∀ l : List ℤ, (∀ z ∈ l, z ≤ 70) → a15CodeOfList l < 141 ^ l.length := by
  intro l
  induction l with
  | nil => intro _; simp [a15CodeOfList]
  | cons z rest ih =>
      intro hb
      have hz : a15ProfileDigit z < 141 :=
        a15ProfileDigit_lt (hb z (List.mem_cons_self ..))
      have hrest : a15CodeOfList rest < 141 ^ rest.length :=
        ih fun w hw => hb w (List.mem_cons_of_mem _ hw)
      have hmul : 141 ^ rest.length * a15ProfileDigit z
          ≤ 141 ^ rest.length * 140 :=
        Nat.mul_le_mul_left _ (by omega)
      have hpow : 141 ^ (rest.length + 1) = 141 ^ rest.length * 141 := by
        ring
      simp only [a15CodeOfList, List.length_cons, hpow]
      omega

/-- On codable coordinate lists of a common length the code is injective. -/
theorem a15CodeOfList_injective :
    ∀ l₁ l₂ : List ℤ, l₁.length = l₂.length →
      (∀ z ∈ l₁, -70 ≤ z ∧ z ≤ 70) → (∀ z ∈ l₂, -70 ≤ z ∧ z ≤ 70) →
      a15CodeOfList l₁ = a15CodeOfList l₂ → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ hlen _ _ _
      exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | cons z₁ rest₁ ih =>
      intro l₂ hlen hb₁ hb₂ hcode
      match l₂ with
      | [] => simp at hlen
      | z₂ :: rest₂ =>
          have hrest : rest₁.length = rest₂.length := by
            simpa using hlen
          have hlt₁ : a15CodeOfList rest₁ < 141 ^ rest₁.length :=
            a15CodeOfList_lt rest₁
              fun w hw => (hb₁ w (List.mem_cons_of_mem _ hw)).2
          have hlt₂ : a15CodeOfList rest₂ < 141 ^ rest₂.length :=
            a15CodeOfList_lt rest₂
              fun w hw => (hb₂ w (List.mem_cons_of_mem _ hw)).2
          rw [hrest] at hlt₁
          have hpos : 0 < 141 ^ rest₂.length := Nat.pow_pos (by omega)
          have hcode' :
              141 ^ rest₂.length * a15ProfileDigit z₁ + a15CodeOfList rest₁ =
                141 ^ rest₂.length * a15ProfileDigit z₂ +
                  a15CodeOfList rest₂ := by
            simpa [a15CodeOfList, hrest] using hcode
          -- the low part is the remainder, the high part the quotient
          have hmod : a15CodeOfList rest₁ = a15CodeOfList rest₂ := by
            have h₁ := Nat.mul_add_mod (141 ^ rest₂.length)
              (a15ProfileDigit z₁) (a15CodeOfList rest₁)
            have h₂ := Nat.mul_add_mod (141 ^ rest₂.length)
              (a15ProfileDigit z₂) (a15CodeOfList rest₂)
            rw [hcode', h₂, Nat.mod_eq_of_lt hlt₂] at h₁
            rw [Nat.mod_eq_of_lt hlt₁] at h₁
            exact h₁.symm
          have hdig : a15ProfileDigit z₁ = a15ProfileDigit z₂ := by
            have := hcode'
            rw [hmod] at this
            exact Nat.eq_of_mul_eq_mul_left hpos (by omega)
          have hz : z₁ = z₂ := by
            have h₁ := a15ProfileDigit_cast (hb₁ z₁ (List.mem_cons_self ..)).1
            have h₂ := a15ProfileDigit_cast (hb₂ z₂ (List.mem_cons_self ..)).1
            rw [hdig] at h₁
            omega
          have hr : rest₁ = rest₂ :=
            ih rest₂ hrest
              (fun w hw => hb₁ w (List.mem_cons_of_mem _ hw))
              (fun w hw => hb₂ w (List.mem_cons_of_mem _ hw)) hmod
          rw [hz, hr]

/-- On codable profiles the base-`141` code determines the profile. -/
theorem a15ProfileCode_injective {x y : Array ℤ}
    (hx : a15CodableProfile x = true) (hy : a15CodableProfile y = true)
    (h : a15ProfileCode x = a15ProfileCode y) : x = y := by
  have hlist : x.toList = y.toList :=
    a15CodeOfList_injective x.toList y.toList
      ((a15CodableProfile_length hx).trans (a15CodableProfile_length hy).symm)
      (a15CodableProfile_bounds hx) (a15CodableProfile_bounds hy) h
  exact Array.toList_inj.mp hlist

end SRG266
