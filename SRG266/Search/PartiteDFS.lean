/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Mathlib.Data.List.Basic

/-!
# A kernel-checkable partite depth-first search

Many of the remaining finite searches in the quasi-symmetric-design branch
have the same shape: for each row of a matrix, choose one candidate from a
finite domain, reject an extension as soon as a hereditary constraint fails,
and check exact column constraints at the leaves.  `partiteDFS` is the small
generic checker for that shape.

The search is deliberately list based.  Certificate modules may use packed
natural numbers for the candidates and for the hot predicates, while the
logical interface remains independent of that representation.  The theorem
`mem_partiteDFS_iff` is both the soundness and the completeness theorem: a
listed selection is exactly a sequence which chooses one item from every
domain, passes every prefix guard, and passes the terminal predicate.

No evaluation tactic and no external solver is used in this module.
-/

namespace SRG266.Search

/-- A successful path through a partite search.  `chosenRev` contains the
already selected candidates in reverse order, which makes extension constant
time.  The output list is in domain order. -/
inductive PartitePath {α : Type*}
    (guard : List α → α → Bool) (accept : List α → Bool) :
    List α → List (List α) → List α → Prop where
  | nil {chosenRev} (haccept : accept chosenRev = true) :
      PartitePath guard accept chosenRev [] []
  | cons {chosenRev domain domains x xs}
      (hmem : x ∈ domain)
      (hguard : guard chosenRev x = true)
      (hrest : PartitePath guard accept (x :: chosenRev) domains xs) :
      PartitePath guard accept chosenRev (domain :: domains) (x :: xs)

/-- Depth-first enumeration which selects one candidate from each domain.

The guard sees the previously selected candidates in reverse order.  This is
the useful orientation for pairwise-intersection tests: the new candidate is
compared with every earlier candidate before the recursive call. -/
def partiteDFS {α : Type*}
    (guard : List α → α → Bool) (accept : List α → Bool) :
    List (List α) → List α → List (List α)
  | [], chosenRev => if accept chosenRev then [[]] else []
  | domain :: domains, chosenRev =>
      domain.flatMap fun x =>
        if guard chosenRev x then
          (partiteDFS guard accept domains (x :: chosenRev)).map (x :: ·)
        else
          []

/-- The DFS returns exactly its successful paths.  In particular, this is the
completeness theorem required at the Python-to-Lean boundary: a mathematical
solution supplies a `PartitePath`, hence occurs in the kernel-computed list. -/
theorem mem_partiteDFS_iff {α : Type*}
    (guard : List α → α → Bool) (accept : List α → Bool)
    (domains : List (List α)) (chosenRev xs : List α) :
    xs ∈ partiteDFS guard accept domains chosenRev ↔
      PartitePath guard accept chosenRev domains xs := by
  induction domains generalizing chosenRev xs with
  | nil =>
      constructor
      · intro hmem
        by_cases haccept : accept chosenRev = true
        · have hxs : xs = [] := by
            simpa [partiteDFS, haccept] using hmem
          subst xs
          exact PartitePath.nil haccept
        · simp [partiteDFS, haccept] at hmem
      · intro hpath
        cases hpath with
        | nil haccept => simp [partiteDFS, haccept]
  | cons domain domains ih =>
      constructor
      · intro hmem
        simp only [partiteDFS, List.mem_flatMap] at hmem
        obtain ⟨x, hx, hbranch⟩ := hmem
        by_cases hguard : guard chosenRev x = true
        · simp [hguard] at hbranch
          obtain ⟨ys, hys, rfl⟩ := hbranch
          exact PartitePath.cons hx hguard ((ih (x :: chosenRev) ys).mp hys)
        · simp [hguard] at hbranch
      · intro hpath
        cases hpath with
        | cons hx hguard hrest =>
            simp only [partiteDFS, List.mem_flatMap]
            refine ⟨_, hx, ?_⟩
            simp [hguard, (ih _ _).mpr hrest]

/-- Every returned selection has one entry per domain. -/
theorem PartitePath.length_eq {α : Type*}
    {guard : List α → α → Bool} {accept : List α → Bool}
    {chosenRev domains xs} (h : PartitePath guard accept chosenRev domains xs) :
    xs.length = domains.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ ih => simp [ih]

/-- Every returned entry belongs to the corresponding domain. -/
theorem PartitePath.forall₂_mem {α : Type*}
    {guard : List α → α → Bool} {accept : List α → Bool}
    {chosenRev domains xs} (h : PartitePath guard accept chosenRev domains xs) :
    List.Forall₂ (fun x domain => x ∈ domain) xs domains := by
  induction h with
  | nil => exact .nil
  | cons hmem _ _ ih => exact .cons hmem ih

/-- The exact leaf predicate holds for every successful path, on the reverse
of the initial accumulator followed by the reverse of the returned choices. -/
theorem PartitePath.accept_eq_true {α : Type*}
    {guard : List α → α → Bool} {accept : List α → Bool}
    {chosenRev domains xs} (h : PartitePath guard accept chosenRev domains xs) :
    accept (xs.reverse ++ chosenRev) = true := by
  induction h with
  | nil haccept => simpa using haccept
  | cons _ _ _ ih =>
      simpa [List.reverse_cons, List.append_assoc] using ih

/-- An empty DFS result is a direct refutation of every successful selection.
This is the theorem certificate modules normally consume after checking a
chunk equation in the kernel. -/
theorem no_partitePath_of_partiteDFS_eq_nil {α : Type*}
    {guard : List α → α → Bool} {accept : List α → Bool}
    {domains : List (List α)} {chosenRev : List α}
    (hempty : partiteDFS guard accept domains chosenRev = []) :
    ∀ xs, ¬PartitePath guard accept chosenRev domains xs := by
  intro xs hpath
  have hmem := (mem_partiteDFS_iff guard accept domains chosenRev xs).mpr hpath
  rw [hempty] at hmem
  exact List.not_mem_nil hmem

end SRG266.Search
