/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.RootCoordinates

/-!
# Packed vertex sets and triple families

The second rooted search uses two levels of bit coordinates without a lookup
table.  A vertex set is encoded by its ordinary 11-bit characteristic mask.
A family of vertex sets is encoded in a 2048-bit natural number, at the
position given by that characteristic mask.  In particular, a family of
triples uses only 165 of those positions but needs no separately trusted
triple numbering.

This file proves the complete dictionaries, including that intersections are
`Nat.land` and cardinalities are `SRG266.Search.popcount`.
-/

namespace SRG266.QuasiSymmetric

open SRG266.Search

set_option exponentiation.threshold 4096

/-- The 11-bit characteristic mask of a set of vertices. -/
def vertexMask (s : Finset (Fin 11)) : ℕ :=
  s.fold (· ||| ·) 0 fun v => 2 ^ v.val

@[simp] theorem vertexMask_empty : vertexMask (∅ : Finset (Fin 11)) = 0 := rfl

theorem vertexMask_insert {v : Fin 11} {s : Finset (Fin 11)} (hv : v ∉ s) :
    vertexMask (insert v s) = 2 ^ v.val ||| vertexMask s := by
  classical
  rw [vertexMask, vertexMask, Finset.fold_insert hv]

theorem testBit_vertexMask (s : Finset (Fin 11)) (k : ℕ) :
    (vertexMask s).testBit k = true ↔ ∃ v ∈ s, v.val = k := by
  classical
  induction s using Finset.induction with
  | empty => simp [vertexMask_empty]
  | insert v s hv ih =>
      rw [vertexMask_insert hv, Nat.testBit_or, Bool.or_eq_true,
        Nat.testBit_two_pow, ih]
      constructor
      · rintro (h | ⟨w, hw, rfl⟩)
        · exact ⟨v, Finset.mem_insert_self _ _, by simpa using h⟩
        · exact ⟨w, Finset.mem_insert_of_mem hw, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Or.inl (by simp)
        · exact Or.inr ⟨w, hw, rfl⟩

theorem vertexMask_lt (s : Finset (Fin 11)) : vertexMask s < 2 ^ 11 := by
  classical
  induction s using Finset.induction with
  | empty => simp [vertexMask_empty]
  | insert v s hv ih =>
      rw [vertexMask_insert hv]
      exact Nat.or_lt_two_pow (Nat.pow_lt_pow_right (by norm_num) v.isLt) ih

@[simp] theorem testBit_vertexMask_val (s : Finset (Fin 11)) (v : Fin 11) :
    (vertexMask s).testBit v.val = decide (v ∈ s) := by
  apply Bool.eq_iff_iff.mpr
  rw [testBit_vertexMask, decide_eq_true_eq]
  constructor
  · rintro ⟨w, hw, hval⟩
    exact Fin.val_injective hval ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem vertexMask_injective : Function.Injective vertexMask := by
  intro s t h
  ext v
  have hbit := congrArg (fun m : ℕ => m.testBit v.val) h
  simpa only [testBit_vertexMask_val, decide_eq_decide] using hbit

/-- Decode the low eleven bits of a natural number as a vertex set. -/
def verticesOfMask (m : ℕ) : Finset (Fin 11) :=
  Finset.univ.filter fun v => m.testBit v.val

@[simp] theorem mem_verticesOfMask (m : ℕ) (v : Fin 11) :
    v ∈ verticesOfMask m ↔ m.testBit v.val = true := by
  simp [verticesOfMask]

/-- Decoding a genuine vertex-set mask recovers the set. -/
@[simp] theorem verticesOfMask_vertexMask (s : Finset (Fin 11)) :
    verticesOfMask (vertexMask s) = s := by
  ext v
  simp [verticesOfMask, testBit_vertexMask_val]

/-- Encoding the decoding recovers every mask confined to eleven bits. -/
theorem vertexMask_verticesOfMask {m : ℕ} (hm : m < 2 ^ 11) :
    vertexMask (verticesOfMask m) = m := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 11
  · let v : Fin 11 := ⟨k, hk⟩
    change (vertexMask (verticesOfMask m)).testBit v.val = m.testBit v.val
    rw [testBit_vertexMask_val]
    apply Bool.eq_iff_iff.mpr
    simp [verticesOfMask]
  · have hle : 11 ≤ k := Nat.le_of_not_gt hk
    have hpow : 2 ^ 11 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hle
    have hleft : (vertexMask (verticesOfMask m)).testBit k = false :=
      Nat.testBit_lt_two_pow
        (lt_of_lt_of_le (vertexMask_lt (verticesOfMask m)) hpow)
    have hright : m.testBit k = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hm hpow)
    rw [hleft, hright]

/-- Intersections of vertex sets are counted by popcount of mask intersection. -/
theorem popcount_and_vertexMask (s t : Finset (Fin 11)) :
    popcount (vertexMask s &&& vertexMask t) = (s ∩ t).card := by
  rw [← card_filter_testBit (fun v : Fin 11 => v.val) 11
    (fun v => v.isLt) Fin.val_injective (by simp)
    (Nat.and_lt_two_pow _ (vertexMask_lt t))]
  apply congrArg Finset.card
  ext v
  simp [Nat.testBit_and, testBit_vertexMask_val]

/-! ## Families at characteristic-mask positions -/

/-- A family of vertex sets as a 2048-bit natural number. -/
def vertexFamilyMask (S : Finset (Finset (Fin 11))) : ℕ :=
  S.fold (· ||| ·) 0 fun s => 2 ^ vertexMask s

@[simp] theorem vertexFamilyMask_empty :
    vertexFamilyMask (∅ : Finset (Finset (Fin 11))) = 0 := rfl

theorem vertexFamilyMask_insert {s : Finset (Fin 11)}
    {S : Finset (Finset (Fin 11))} (hs : s ∉ S) :
    vertexFamilyMask (insert s S) = 2 ^ vertexMask s ||| vertexFamilyMask S := by
  classical
  rw [vertexFamilyMask, vertexFamilyMask, Finset.fold_insert hs]

theorem testBit_vertexFamilyMask (S : Finset (Finset (Fin 11))) (k : ℕ) :
    (vertexFamilyMask S).testBit k = true ↔ ∃ s ∈ S, vertexMask s = k := by
  classical
  induction S using Finset.induction with
  | empty => simp [vertexFamilyMask_empty]
  | insert s S hs ih =>
      rw [vertexFamilyMask_insert hs, Nat.testBit_or, Bool.or_eq_true,
        Nat.testBit_two_pow, ih]
      constructor
      · rintro (h | ⟨t, ht, rfl⟩)
        · exact ⟨s, Finset.mem_insert_self _ _, by simpa using h⟩
        · exact ⟨t, Finset.mem_insert_of_mem ht, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact Or.inl (by simp)
        · exact Or.inr ⟨t, ht, rfl⟩

theorem vertexFamilyMask_lt (S : Finset (Finset (Fin 11))) :
    vertexFamilyMask S < 2 ^ 2048 := by
  classical
  induction S using Finset.induction with
  | empty => simp [vertexFamilyMask_empty]
  | insert s S hs ih =>
      rw [vertexFamilyMask_insert hs]
      have hslt : vertexMask s < 2048 := by
        have h := vertexMask_lt s
        norm_num at h ⊢
        exact h
      exact Nat.or_lt_two_pow (Nat.pow_lt_pow_right (by norm_num) hslt) ih

@[simp] theorem testBit_vertexFamilyMask_vertexMask
    (S : Finset (Finset (Fin 11))) (s : Finset (Fin 11)) :
    (vertexFamilyMask S).testBit (vertexMask s) = decide (s ∈ S) := by
  apply Bool.eq_iff_iff.mpr
  rw [testBit_vertexFamilyMask, decide_eq_true_eq]
  constructor
  · rintro ⟨t, ht, hmask⟩
    exact vertexMask_injective hmask ▸ ht
  · intro hs
    exact ⟨s, hs, rfl⟩

/-- Intersections of families are counted by popcount of their 2048-bit masks. -/
theorem popcount_and_vertexFamilyMask
    (S T : Finset (Finset (Fin 11))) :
    popcount (vertexFamilyMask S &&& vertexFamilyMask T) = (S ∩ T).card := by
  have hcard : Fintype.card (Finset (Fin 11)) = 2048 := by
    rw [Fintype.card_finset, Fintype.card_fin]
    norm_num
  rw [← card_filter_testBit vertexMask 2048
    (fun s => by
      have h := vertexMask_lt s
      norm_num at h ⊢
      exact h)
    vertexMask_injective hcard
    (Nat.and_lt_two_pow _ (vertexFamilyMask_lt T))]
  apply congrArg Finset.card
  ext s
  simp [Nat.testBit_and, testBit_vertexFamilyMask_vertexMask]

end SRG266.QuasiSymmetric
