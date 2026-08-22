/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.A15FourSubsets

/-!
# Reindexing the four-subset table by third element

The fast A15 eligible-shell counter enumerates four-subsets `i < j < k < l`
in the order `(k, l, j, i)`: at stage `k` it holds a histogram of the pair
sums `i < j < k` and pairs it with every completion `k < l < 16`.  The
declarative reference counter instead folds over the checked 1,820-entry
table `a15FourSubsetData`.

This module bridges the two orders.  `a15QuadsByThird` is the
`(k, l, j, i)`-ordered list of index quadruples; it is characterized by the
strict ordering constraint, has 1,820 entries, and is therefore a permutation
of the table.
Counting is permutation invariant, so any `List.countP` over the table may be
replaced by the same count over `a15QuadsByThird`, which then splits into the
nested sums the fast loop accumulates.
-/

namespace SRG266

set_option maxRecDepth 100000

/-- The index quadruples `i < j < k < l < 16` generated in the order the fast
counter visits them: outer loop on the third element `k`, then the completion
`l`, then the stored pair `i < j < k`. -/
def a15QuadsByThird : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range' 2 13).flatMap fun k =>
    (List.range' (k + 1) (15 - k)).flatMap fun l =>
      (List.range k).flatMap fun j =>
        (List.range j).map fun i => (i, j, k, l)

theorem a15QuadsByThird_length : a15QuadsByThird.length = 1820 := by
  decide +kernel

/-- `a15QuadsByThird` contains exactly the strictly increasing quadruples of
indices below sixteen. -/
theorem a15_mem_quadsByThird (q : ℕ × ℕ × ℕ × ℕ) :
    q ∈ a15QuadsByThird ↔
      q.1 < q.2.1 ∧ q.2.1 < q.2.2.1 ∧ q.2.2.1 < q.2.2.2 ∧ q.2.2.2 < 16 := by
  obtain ⟨i, j, k, l⟩ := q
  simp only [a15QuadsByThird, List.mem_flatMap, List.mem_map, List.mem_range,
    List.mem_range'_1, Prod.mk.injEq]
  constructor
  · rintro ⟨k', ⟨hk1, hk2⟩, l', ⟨hl1, hl2⟩, j', hj, i', hi, rfl, rfl, rfl, rfl⟩
    omega
  · rintro ⟨hij, hjk, hkl, hl⟩
    exact ⟨k, ⟨by omega, by omega⟩, l, ⟨by omega, by omega⟩, j, by omega,
      i, by omega, rfl, rfl, rfl, rfl⟩

/-- The checked four-subset table read as plain index quadruples. -/
def a15TableQuads : List (ℕ × ℕ × ℕ × ℕ) :=
  a15FourSubsetData.toList.map (fun s => (s.a, s.b, s.c, s.d))

theorem a15TableQuads_length : a15TableQuads.length = 1820 := by
  simp [a15TableQuads, a15FourSubsetData_size]

theorem a15FourSubsetAt_injective : Function.Injective a15FourSubsetAt := by
  intro s t h
  have := congrArg a15FourSubsetRank h
  rw [a15FourSubsetAt_rank s, a15FourSubsetAt_rank t] at this
  exact Fin.ext this

theorem a15TableQuads_nodup : a15TableQuads.Nodup := by
  have hdata : a15FourSubsetData.toList.Nodup := by
    rw [List.nodup_iff_injective_get]
    intro s t h
    apply Fin.ext
    have hs : a15FourSubsetData.toList.get s = a15FourSubsetAt ⟨s.1, by
      simp⟩ := by
      simp [a15FourSubsetAt, Array.getElem_toList]
    have ht : a15FourSubsetData.toList.get t = a15FourSubsetAt ⟨t.1, by
      simp⟩ := by
      simp [a15FourSubsetAt, Array.getElem_toList]
    rw [hs, ht] at h
    have := a15FourSubsetAt_injective h
    simpa using congrArg Fin.val this
  apply hdata.map
  intro s t h
  obtain ⟨a, b, c, d⟩ := s
  obtain ⟨a', b', c', d'⟩ := t
  simp_all

theorem a15TableQuads_subset : a15TableQuads ⊆ a15QuadsByThird := by
  intro q hq
  simp only [a15TableQuads, List.mem_map] at hq
  obtain ⟨s, hs, rfl⟩ := hq
  obtain ⟨n, hn⟩ := List.get_of_mem hs
  have hidx : s = a15FourSubsetAt ⟨n.1, by simp⟩ := by
    rw [← hn]
    simp [a15FourSubsetAt, Array.getElem_toList]
  have hinc := a15FourSubsetAt_increasing ⟨n.1, by simp⟩
  rw [← hidx] at hinc
  dsimp only at hinc
  rw [a15_mem_quadsByThird]
  exact ⟨hinc.1, hinc.2.1, hinc.2.2.1, hinc.2.2.2⟩

/-- The checked table and the `(k, l, j, i)`-ordered generation list agree up
to permutation: both are duplicate-free lists of the same length listing
strictly increasing quadruples. -/
theorem a15TableQuads_perm : a15TableQuads.Perm a15QuadsByThird := by
  have hsub : List.Subperm a15TableQuads a15QuadsByThird :=
    a15TableQuads_nodup.subperm a15TableQuads_subset
  exact hsub.perm_of_length_le
    (by rw [a15QuadsByThird_length, a15TableQuads_length])

end SRG266
