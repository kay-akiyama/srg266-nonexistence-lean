/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.A15ProfileCode

/-!
# A kernel-reducible sort used to compare two profile sets

The A15 centroid input asks for an equality of two 2,212-element sets of
profiles.  Deciding it by membership sweeps is quadratic and too expensive, so
the comparison is routed through the
base-`141` codes of `SRG266.Hosts.A15ProfileCode` and the two code lists are
compared after sorting.

`List.mergeSort` cannot be used: Lean 4.32 defines it by well-founded
recursion, so it has no definitional unfolding and no kernel evaluation can
reach it.  This module defines a bottom-up merge sort whose every recursion is
structural -- on a fuel argument for the merge, on the list of runs for a
pass, on a fuel argument for the rounds -- and which the kernel therefore
unfolds.

Only one property of the sort is proved, and it is the only one the argument
needs: `a15SortCodes_perm` says the result is a permutation of the input.
Sortedness is never used, so a bug in the comparison could only ever make the
final `decide` fail, never make it wrongly succeed.

`a15_toFinset_eq_of_sortedCodes_eq` is the module's export: two lists of
codable profiles whose sorted code lists agree have the same underlying set.
Nothing in this module is evaluated by the kernel.
-/

namespace SRG266

/-- Merge two lists of codes.  The fuel is structural recursion fodder; when
it runs out the two lists are concatenated, which keeps the permutation
statement true unconditionally. -/
def a15MergeCodes : ℕ → List ℕ → List ℕ → List ℕ
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, x :: xs, [] => x :: xs
  | fuel + 1, x :: xs, y :: ys =>
      if y < x then y :: a15MergeCodes fuel (x :: xs) ys
      else x :: a15MergeCodes fuel xs (y :: ys)

/-- One bottom-up pass: merge the runs pairwise. -/
def a15CodePass : List (List ℕ) → List (List ℕ)
  | [] => []
  | [run] => [run]
  | run₁ :: run₂ :: rest =>
      a15MergeCodes (run₁.length + run₂.length) run₁ run₂ ::
        a15CodePass rest

/-- Repeat the pass until one run is left. -/
def a15CodeRounds : ℕ → List (List ℕ) → List ℕ
  | 0, runs => runs.flatten
  | _ + 1, [] => []
  | _ + 1, [run] => run
  | fuel + 1, run₁ :: run₂ :: rest =>
      a15CodeRounds fuel (a15CodePass (run₁ :: run₂ :: rest))

/-- Sort a list of codes.  Twenty-four rounds sort any list of fewer than
`2 ^ 24` codes. -/
def a15SortCodes (codes : List ℕ) : List ℕ :=
  a15CodeRounds 24 (codes.map fun n => [n])

theorem a15MergeCodes_perm :
    ∀ (fuel : ℕ) (xs ys : List ℕ),
      List.Perm (a15MergeCodes fuel xs ys) (xs ++ ys) := by
  intro fuel
  induction fuel with
  | zero => intro xs ys; exact List.Perm.refl _
  | succ fuel ih =>
      intro xs ys
      match xs, ys with
      | [], ys => simp [a15MergeCodes]
      | x :: xs, [] => simp [a15MergeCodes]
      | x :: xs, y :: ys =>
          by_cases h : y < x
          · have : a15MergeCodes (fuel + 1) (x :: xs) (y :: ys) =
                y :: a15MergeCodes fuel (x :: xs) ys := by
              simp [a15MergeCodes, h]
            rw [this]
            exact ((ih (x :: xs) ys).cons y).trans List.perm_middle.symm
          · have : a15MergeCodes (fuel + 1) (x :: xs) (y :: ys) =
                x :: a15MergeCodes fuel xs (y :: ys) := by
              simp [a15MergeCodes, h]
            rw [this]
            exact (ih xs (y :: ys)).cons x

theorem a15CodePass_flatten :
    ∀ runs : List (List ℕ),
      List.Perm (a15CodePass runs).flatten runs.flatten := by
  intro runs
  induction runs using a15CodePass.induct with
  | case1 => exact List.Perm.refl _
  | case2 run => exact List.Perm.refl _
  | case3 run₁ run₂ rest ih =>
      simp only [a15CodePass, List.flatten_cons]
      refine List.Perm.trans
        (List.Perm.append (a15MergeCodes_perm _ _ _) ih) ?_
      simp [List.append_assoc]

theorem a15CodeRounds_perm :
    ∀ (fuel : ℕ) (runs : List (List ℕ)),
      List.Perm (a15CodeRounds fuel runs) runs.flatten := by
  intro fuel
  induction fuel with
  | zero => intro runs; exact List.Perm.refl _
  | succ fuel ih =>
      intro runs
      match runs with
      | [] => simp [a15CodeRounds]
      | [run] => simp [a15CodeRounds]
      | run₁ :: run₂ :: rest =>
          have hstep : a15CodeRounds (fuel + 1) (run₁ :: run₂ :: rest) =
              a15CodeRounds fuel (a15CodePass (run₁ :: run₂ :: rest)) := by
            simp [a15CodeRounds]
          rw [hstep]
          exact (ih _).trans (a15CodePass_flatten _)

theorem a15SortCodes_perm (codes : List ℕ) :
    List.Perm (a15SortCodes codes) codes := by
  have hflat : ∀ l : List ℕ, (l.map fun n => [n]).flatten = l := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih => simp [ih]
  have := a15CodeRounds_perm 24 (codes.map fun n => [n])
  rw [hflat] at this
  exact this

/-- Two lists of codable profiles whose sorted code lists agree have the same
underlying set.  This is the whole reason the codes exist. -/
theorem a15_toFinset_eq_of_sortedCodes_eq
    (left right : List (Array ℤ))
    (hleft : ∀ x ∈ left, a15CodableProfile x = true)
    (hright : ∀ x ∈ right, a15CodableProfile x = true)
    (hsorted :
      a15SortCodes (left.map a15ProfileCode) =
        a15SortCodes (right.map a15ProfileCode)) :
    left.toFinset = right.toFinset := by
  have hperm : List.Perm (left.map a15ProfileCode)
      (right.map a15ProfileCode) :=
    ((a15SortCodes_perm (left.map a15ProfileCode)).symm.trans
      (hsorted ▸ List.Perm.refl _)).trans
      (a15SortCodes_perm (right.map a15ProfileCode))
  have hmem : ∀ (l r : List (Array ℤ)),
      (∀ x ∈ l, a15CodableProfile x = true) →
      (∀ x ∈ r, a15CodableProfile x = true) →
      List.Perm (l.map a15ProfileCode) (r.map a15ProfileCode) →
      ∀ x ∈ l, x ∈ r := by
    intro l r hl hr hp x hx
    have hcode : a15ProfileCode x ∈ r.map a15ProfileCode :=
      hp.mem_iff.mp (List.mem_map_of_mem hx)
    obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hcode
    have : x = y := a15ProfileCode_injective (hl x hx) (hr y hy) hyx.symm
    exact this ▸ hy
  ext a
  simp only [List.mem_toFinset]
  exact ⟨fun h => hmem left right hleft hright hperm a h,
    fun h => hmem right left hright hleft hperm.symm a h⟩

end SRG266
