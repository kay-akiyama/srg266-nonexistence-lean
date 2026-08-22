/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Search.SubsetDFS

/-!
# Subset search at arbitrary bit positions

`maskDFS` scans a contiguous bit window.  The cross-row generator instead has
only 140 admissible triples spread over 2048 characteristic-mask positions.
`itemMaskDFS` branches only at its supplied positions.  Its path relation is
exactly equivalent to output membership, so later domain-completeness proofs
may construct the mathematical branch without trusting a generator.
-/

namespace SRG266.Search

/-- A successful include/exclude path through `itemMaskDFS`. -/
inductive ItemMaskPath (guard accept : ℕ → Bool) : List ℕ → ℕ → ℕ → Prop where
  | nil {m} (haccept : accept m = true) : ItemMaskPath guard accept [] m m
  | take {i items m result} (hguard : guard (m ||| 2 ^ i) = true)
      (hrest : ItemMaskPath guard accept items (m ||| 2 ^ i) result) :
      ItemMaskPath guard accept (i :: items) m result
  | skip {i items m result} (hguard : guard m = true)
      (hrest : ItemMaskPath guard accept items m result) :
      ItemMaskPath guard accept (i :: items) m result

/-- Depth-first subset enumeration at the listed bit positions. -/
def itemMaskDFS (guard accept : ℕ → Bool) : List ℕ → ℕ → List ℕ
  | [], m => if accept m then [m] else []
  | i :: items, m =>
      (if guard (m ||| 2 ^ i) then
        itemMaskDFS guard accept items (m ||| 2 ^ i)
       else []) ++
      (if guard m then itemMaskDFS guard accept items m else [])

/-- The arbitrary-position DFS returns exactly its successful paths. -/
theorem mem_itemMaskDFS_iff (guard accept : ℕ → Bool)
    (items : List ℕ) (m result : ℕ) :
    result ∈ itemMaskDFS guard accept items m ↔
      ItemMaskPath guard accept items m result := by
  induction items generalizing m result with
  | nil =>
      constructor
      · intro h
        by_cases ha : accept m = true
        · have hr : result = m := by simpa [itemMaskDFS, ha] using h
          subst result
          exact .nil ha
        · simp [itemMaskDFS, ha] at h
      · intro h
        cases h with
        | nil ha => simp [itemMaskDFS, ha]
  | cons i items ih =>
      constructor
      · intro h
        simp only [itemMaskDFS, List.mem_append] at h
        rcases h with h | h
        · by_cases hg : guard (m ||| 2 ^ i) = true
          · simp [hg] at h
            exact .take hg ((ih _ _).mp h)
          · simp [hg] at h
        · by_cases hg : guard m = true
          · simp [hg] at h
            exact .skip hg ((ih _ _).mp h)
          · simp [hg] at h
      · intro h
        cases h with
        | take hg hrest =>
            simp only [itemMaskDFS, List.mem_append]
            exact Or.inl (by simpa [hg] using (ih _ _).mpr hrest)
        | skip hg hrest =>
            simp only [itemMaskDFS, List.mem_append]
            exact Or.inr (by simpa [hg] using (ih _ _).mpr hrest)

namespace ItemMaskPath

/-- Every successful path ends at a mask accepted by the leaf predicate. -/
theorem accept {guard accept : ℕ → Bool} {items : List ℕ} {m result : ℕ}
    (path : ItemMaskPath guard accept items m result) :
    accept result = true := by
  induction path with
  | nil haccept => exact haccept
  | take _ _ ih => exact ih
  | skip _ _ ih => exact ih

/-- Unless the search has no item at all, its final mask passed the hereditary
guard at the last include/exclude decision. -/
theorem guard_result_of_ne_nil {guard accept : ℕ → Bool} {items : List ℕ}
    {m result : ℕ} (path : ItemMaskPath guard accept items m result)
    (hitems : items ≠ []) : guard result = true := by
  induction path with
  | nil _ => exact (hitems rfl).elim
  | @take item items m result hguard hrest ih =>
      cases items with
      | nil =>
          cases hrest with
          | nil _ => exact hguard
      | cons next tail =>
          exact ih (by simp)
  | @skip item items m result hguard hrest ih =>
      cases items with
      | nil =>
          cases hrest with
          | nil _ => exact hguard
      | cons next tail =>
          exact ih (by simp)

/-- A path whose starting mask and item positions fit in a fixed bit window
also ends inside that window. -/
theorem result_lt_two_pow {guard accept : ℕ → Bool} {items : List ℕ}
    {m result width : ℕ} (path : ItemMaskPath guard accept items m result)
    (hstart : m < 2 ^ width) (hitems : ∀ item ∈ items, item < width) :
    result < 2 ^ width := by
  induction path with
  | nil _ => exact hstart
  | @take item items m result _ _ ih =>
      apply ih
      · exact Nat.or_lt_two_pow hstart
          (Nat.pow_lt_pow_right (by omega) (hitems item (by simp)))
      · intro tail htail
        exact hitems tail (by simp [htail])
  | @skip item items m result _ _ ih =>
      apply ih hstart
      intro tail htail
      exact hitems tail (by simp [htail])

end ItemMaskPath

/-- An empty result refutes every successful path. -/
theorem no_itemMaskPath_of_eq_nil {guard accept : ℕ → Bool}
    {items : List ℕ} {m : ℕ}
    (h : itemMaskDFS guard accept items m = []) :
    ∀ result, ¬ItemMaskPath guard accept items m result := by
  intro result hp
  have hm := (mem_itemMaskDFS_iff guard accept items m result).mpr hp
  rw [h] at hm
  exact List.not_mem_nil hm

/-- **Completeness from a hereditary mask predicate.**  Every target bit not
already present in `m` must occur among the remaining item positions.  The DFS
then follows the target's include/exclude branch and cannot be pruned. -/
theorem itemMaskDFS_complete_of_hereditary
    {P accept : ℕ → Bool} (hP : Hereditary P)
    {items : List ℕ} {m target : ℕ}
    (hsub : Submask m target)
    (hcover : ∀ k, target.testBit k = true → m.testBit k = false → k ∈ items)
    (hTarget : P target = true) (haccept : accept target = true) :
    target ∈ itemMaskDFS P accept items m := by
  rw [mem_itemMaskDFS_iff]
  induction items generalizing m with
  | nil =>
      have hmt : m = target := by
        apply Nat.eq_of_testBit_eq
        intro k
        rcases Bool.eq_false_or_eq_true (target.testBit k) with ht | ht
        · have hm : m.testBit k = true := by
            rcases Bool.eq_false_or_eq_true (m.testBit k) with hm | hm
            · exact hm
            · have : k ∈ ([] : List ℕ) := hcover k ht hm
              simp at this
          rw [hm, ht]
        · have hm : m.testBit k = false := by
            rcases Bool.eq_false_or_eq_true (m.testBit k) with hm | hm
            · exact absurd (hsub k hm) (by simp [ht])
            · exact hm
          rw [hm, ht]
      subst m
      exact .nil haccept
  | cons i items ih =>
      by_cases ht : target.testBit i = true
      · by_cases hm : m.testBit i = true
        · apply ItemMaskPath.skip (hP m target hsub hTarget)
          apply ih hsub
          intro k htk hmk
          rcases List.mem_cons.mp (hcover k htk hmk) with hki | hk
          · subst k
            rw [hm] at hmk
            exact Bool.noConfusion hmk
          · exact hk
        · have htakeSub : Submask (m ||| 2 ^ i) target := by
            intro k hk
            simp only [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true] at hk
            rcases hk with hk | hki
            · exact hsub k hk
            · have hik : i = k := by simpa using hki
              simpa [← hik] using ht
          apply ItemMaskPath.take (hP _ target htakeSub hTarget)
          apply ih htakeSub
          intro k htk hnew
          have hmfalse : m.testBit k = false := by
            simp only [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_false_iff] at hnew
            exact hnew.1
          rcases List.mem_cons.mp (hcover k htk hmfalse) with hki | hk
          · subst k
            simp at hnew
          · exact hk
      · have hm : m.testBit i = false := by
          rcases Bool.eq_false_or_eq_true (m.testBit i) with hm | hm
          · exact absurd (hsub i hm) ht
          · exact hm
        apply ItemMaskPath.skip (hP m target hsub hTarget)
        apply ih hsub
        intro k htk hmk
        rcases List.mem_cons.mp (hcover k htk hmk) with hki | hk
        · subst k
          exact (ht htk).elim
        · exact hk

end SRG266.Search
