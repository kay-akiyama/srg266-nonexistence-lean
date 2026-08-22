/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Search.ItemMaskDFS

/-!
# Subset search with suffix-aware pruning

The ordinary sparse mask search can only test a partial mask.  Exact-cover
searches also have strong lower bounds: after a position is processed, the
unseen suffix must still contain enough incident items to meet every demand.
This module passes that suffix to the guard and proves completeness directly.
-/

namespace SRG266.Search

/-- The mask containing exactly the positions listed in `items` (duplicates,
if present, are harmless). -/
def itemPositionsMask : List ℕ → ℕ
  | [] => 0
  | i :: items => 2 ^ i ||| itemPositionsMask items

/-- Every listed position is set in `itemPositionsMask`. -/
theorem testBit_itemPositionsMask_of_mem {items : List ℕ} {k : ℕ}
    (hk : k ∈ items) : (itemPositionsMask items).testBit k = true := by
  induction items with
  | nil => simp at hk
  | cons i items ih =>
      rw [itemPositionsMask, Nat.testBit_or, Bool.or_eq_true]
      rcases List.mem_cons.mp hk with rfl | hk
      · exact Or.inl (by simp)
      · exact Or.inr (ih hk)

/-- The mask assembled from a list has exactly the listed bit positions. -/
theorem testBit_itemPositionsMask_iff {items : List ℕ} {k : ℕ} :
    (itemPositionsMask items).testBit k = true ↔ k ∈ items := by
  induction items with
  | nil => simp [itemPositionsMask]
  | cons i items ih =>
      simp only [itemPositionsMask, Nat.testBit_or, Bool.or_eq_true,
        Nat.testBit_two_pow, decide_eq_true_eq, List.mem_cons, ih]
      constructor
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr h

/-- A list of positions below `width` assembles a mask below `2^width`. -/
theorem itemPositionsMask_lt {items : List ℕ} {width : ℕ}
    (hitems : ∀ i ∈ items, i < width) : itemPositionsMask items < 2 ^ width := by
  induction items with
  | nil => simp [itemPositionsMask]
  | cons i items ih =>
      rw [itemPositionsMask]
      apply Nat.or_lt_two_pow
      · exact Nat.pow_lt_pow_right (by omega) (hitems i (by simp))
      · exact ih fun j hj => hitems j (by simp [hj])

/-- A partial mask together with the positions still available covers a target
when every missing target position occurs in the remaining list. -/
theorem submask_or_itemPositionsMask_of_cover
    {items : List ℕ} {m target : ℕ}
    (hcover : ∀ k, target.testBit k = true → m.testBit k = false → k ∈ items) :
    Submask target (m ||| itemPositionsMask items) := by
  intro k htk
  rw [Nat.testBit_or, Bool.or_eq_true]
  rcases Bool.eq_false_or_eq_true (m.testBit k) with hmk | hmk
  · exact Or.inl hmk
  · exact Or.inr (testBit_itemPositionsMask_of_mem (hcover k htk hmk))

/-- A successful include/exclude path whose guard may inspect the unprocessed
suffix. -/
inductive RemainingItemPath (guard : List ℕ → ℕ → Bool) (accept : ℕ → Bool) :
    List ℕ → ℕ → ℕ → Prop where
  | nil {m} (haccept : accept m = true) :
      RemainingItemPath guard accept [] m m
  | take {i items m result} (hguard : guard items (m ||| 2 ^ i) = true)
      (hrest : RemainingItemPath guard accept items (m ||| 2 ^ i) result) :
      RemainingItemPath guard accept (i :: items) m result
  | skip {i items m result} (hguard : guard items m = true)
      (hrest : RemainingItemPath guard accept items m result) :
      RemainingItemPath guard accept (i :: items) m result

/-- Every successful path ends at a leaf satisfying the exact acceptance
predicate. -/
theorem RemainingItemPath.accept
    {guard : List ℕ → ℕ → Bool} {accept : ℕ → Bool}
    {items : List ℕ} {initial result : ℕ}
    (h : RemainingItemPath guard accept items initial result) :
    accept result = true := by
  induction h with
  | nil haccept => exact haccept
  | take _ _ ih => exact ih
  | skip _ _ ih => exact ih

/-- Sparse subset DFS with suffix-aware pruning. -/
def remainingItemDFS (guard : List ℕ → ℕ → Bool) (accept : ℕ → Bool) :
    List ℕ → ℕ → List ℕ
  | [], m => if accept m then [m] else []
  | i :: items, m =>
      (if guard items (m ||| 2 ^ i) then
        remainingItemDFS guard accept items (m ||| 2 ^ i)
       else []) ++
      (if guard items m then remainingItemDFS guard accept items m else [])

/-- The suffix-aware DFS returns exactly its successful paths. -/
theorem mem_remainingItemDFS_iff (guard : List ℕ → ℕ → Bool)
    (accept : ℕ → Bool) (items : List ℕ) (m result : ℕ) :
    result ∈ remainingItemDFS guard accept items m ↔
      RemainingItemPath guard accept items m result := by
  induction items generalizing m result with
  | nil =>
      constructor
      · intro h
        by_cases ha : accept m = true
        · have hr : result = m := by simpa [remainingItemDFS, ha] using h
          subst result
          exact .nil ha
        · simp [remainingItemDFS, ha] at h
      · intro h
        cases h with
        | nil ha => simp [remainingItemDFS, ha]
  | cons i items ih =>
      constructor
      · intro h
        simp only [remainingItemDFS, List.mem_append] at h
        rcases h with h | h
        · by_cases hg : guard items (m ||| 2 ^ i) = true
          · simp [hg] at h
            exact .take hg ((ih _ _).mp h)
          · simp [hg] at h
        · by_cases hg : guard items m = true
          · simp [hg] at h
            exact .skip hg ((ih _ _).mp h)
          · simp [hg] at h
      · intro h
        cases h with
        | take hg hrest =>
            simp only [remainingItemDFS, List.mem_append]
            exact Or.inl (by simpa [hg] using (ih _ _).mpr hrest)
        | skip hg hrest =>
            simp only [remainingItemDFS, List.mem_append]
            exact Or.inr (by simpa [hg] using (ih _ _).mpr hrest)

/-- Membership in a suffix-aware DFS exposes its exact leaf predicate. -/
theorem accept_of_mem_remainingItemDFS
    {guard : List ℕ → ℕ → Bool} {accept : ℕ → Bool}
    {items : List ℕ} {initial result : ℕ}
    (h : result ∈ remainingItemDFS guard accept items initial) :
    accept result = true :=
  ((mem_remainingItemDFS_iff guard accept items initial result).mp h).accept

/-- Every successful suffix-aware path can only set a bit which was already
set initially or was named by the supplied item list. -/
theorem RemainingItemPath.submask_initial_or_items
    {guard : List ℕ → ℕ → Bool} {accept : ℕ → Bool}
    {items : List ℕ} {initial result : ℕ}
    (h : RemainingItemPath guard accept items initial result) :
    Submask result (initial ||| itemPositionsMask items) := by
  induction h with
  | nil =>
      intro k hk
      simp [itemPositionsMask, hk]
  | @take i items initial result _ hrest ih =>
      intro k hk
      have hk' := ih k hk
      simpa only [itemPositionsMask, Nat.or_assoc, Nat.or_left_comm,
        Nat.or_comm] using hk'
  | @skip i items initial result _ hrest ih =>
      intro k hk
      have hk' := ih k hk
      simp only [itemPositionsMask, Nat.testBit_or, Bool.or_eq_true] at hk' ⊢
      rcases hk' with hk' | hk'
      · exact Or.inl hk'
      · exact Or.inr (Or.inr hk')

/-- Every result of a search started from zero is supported on the listed item
positions. -/
theorem submask_itemPositionsMask_of_mem_remainingItemDFS
    {guard : List ℕ → ℕ → Bool} {accept : ℕ → Bool}
    {items : List ℕ} {result : ℕ}
    (h : result ∈ remainingItemDFS guard accept items 0) :
    Submask result (itemPositionsMask items) := by
  have hp := (mem_remainingItemDFS_iff guard accept items 0 result).mp h
  simpa using hp.submask_initial_or_items

/-- Completeness for any suffix guard which accepts every partial target whose
unselected target bits remain in the suffix. -/
theorem remainingItemDFS_complete
    {guard : List ℕ → ℕ → Bool} {accept : ℕ → Bool}
    {items : List ℕ} {m target : ℕ}
    (hsub : Submask m target)
    (hcover : ∀ k, target.testBit k = true → m.testBit k = false → k ∈ items)
    (hguard : ∀ (suffix : List ℕ) (prefixMask : ℕ),
      Submask prefixMask target →
      (∀ k, target.testBit k = true → prefixMask.testBit k = false → k ∈ suffix) →
      guard suffix prefixMask = true)
    (haccept : accept target = true) :
    target ∈ remainingItemDFS guard accept items m := by
  rw [mem_remainingItemDFS_iff]
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
        · have hnextCover : ∀ k, target.testBit k = true →
              m.testBit k = false → k ∈ items := by
            intro k htk hmk
            rcases List.mem_cons.mp (hcover k htk hmk) with hki | hk
            · subst k
              rw [hm] at hmk
              exact Bool.noConfusion hmk
            · exact hk
          apply RemainingItemPath.skip (hguard items m hsub hnextCover)
          exact ih hsub hnextCover
        · have htakeSub : Submask (m ||| 2 ^ i) target := by
            intro k hk
            simp only [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true] at hk
            rcases hk with hk | hki
            · exact hsub k hk
            · have hik : i = k := by simpa using hki
              simpa [← hik] using ht
          have hnextCover : ∀ k, target.testBit k = true →
              (m ||| 2 ^ i).testBit k = false → k ∈ items := by
            intro k htk hnew
            have hmk : m.testBit k = false := by
              simp only [Nat.testBit_or, Nat.testBit_two_pow,
                Bool.or_eq_false_iff] at hnew
              exact hnew.1
            rcases List.mem_cons.mp (hcover k htk hmk) with hki | hk
            · subst k
              simp at hnew
            · exact hk
          apply RemainingItemPath.take
            (hguard items (m ||| 2 ^ i) htakeSub hnextCover)
          exact ih htakeSub hnextCover
      · have hm : m.testBit i = false := by
          rcases Bool.eq_false_or_eq_true (m.testBit i) with hm | hm
          · exact absurd (hsub i hm) ht
          · exact hm
        have hnextCover : ∀ k, target.testBit k = true →
            m.testBit k = false → k ∈ items := by
          intro k htk hmk
          rcases List.mem_cons.mp (hcover k htk hmk) with hki | hk
          · subst k
            exact (ht htk).elim
          · exact hk
        apply RemainingItemPath.skip (hguard items m hsub hnextCover)
        exact ih hsub hnextCover

end SRG266.Search
