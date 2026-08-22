/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.RootCoordinates
import SRG266.QuasiSymmetric.RootBlockSearch

/-!
# Packed first-level search for a rooted global design

This is the executable version of `RootBlockSearch.lean`.  Blocks are 55-bit
natural numbers in `RootCoordinates.edgeCoding`; pair intersections use the
proved popcount dictionary, and edge capacities use bit tests.  The central
theorem `actualBlockMasks_mem_rootBlockMaskDFS` transports every mathematical
`GlobalDesignRoot` into this packed search.

Thus generated modules need only list complete mask domains and check finite
DFS chunks.  They never manipulate `Finset Edge11` in a kernel-hot loop.
-/

namespace SRG266.QuasiSymmetric

open SRG266.Search
open RootCoordinates

namespace EdgeCoding

/-- Bit membership at the coded position is ordinary edge membership. -/
theorem testBit_maskOf_idx (c : EdgeCoding) (s : Finset Edge11) (e : Edge11) :
    (c.maskOf s).testBit (c.idx e) = decide (e ∈ s) := by
  apply Bool.eq_iff_iff.mpr
  rw [c.testBit_maskOf, decide_eq_true_eq]
  constructor
  · rintro ⟨f, hf, hidx⟩
    exact c.idx_injective hidx ▸ hf
  · intro he
    exact ⟨e, he, rfl⟩

end EdgeCoding

/-- Pairwise and edge-capacity guard on packed block masks. -/
def rootBlockMaskGuard (target : ℕ → ℕ) (chosenRev : List ℕ)
    (candidate : ℕ) : Bool :=
  (chosenRev.all fun prior => popcount (candidate &&& prior) == 3) &&
    ((List.range 55).all fun i =>
      ((candidate :: chosenRev).filter fun m => m.testBit i).length ≤ target i)

/-- Exact edge multiplicities at a packed-search leaf. -/
def rootBlockMaskAccept (target : ℕ → ℕ) (chosenRev : List ℕ) : Bool :=
  (List.range 55).all fun i =>
    ((chosenRev.filter fun m => m.testBit i).length == target i)

/-- Complete packed first-level DFS. -/
def rootBlockMaskDFS (target : ℕ → ℕ)
    (rows : List (Finset (Fin 11)))
    (domain : Finset (Fin 11) → List ℕ) : List (List ℕ) :=
  partiteDFS (rootBlockMaskGuard target) (rootBlockMaskAccept target)
    (rows.map domain) []

private theorem filter_length_eq_finset_card {α : Type*} [DecidableEq α]
    (l : List α) (p : α → Prop) [DecidablePred p] (h : l.Nodup) :
    (l.filter fun x => decide (p x)).length = (l.toFinset.filter p).card := by
  rw [← List.toFinset_card_of_nodup (h.filter fun x => decide (p x))]
  apply congrArg Finset.card
  ext x
  simp

namespace GlobalDesignRoot

variable (R : GlobalDesignRoot)

/-- The packed mask of a genuine neighbour block. -/
def actualBlockMask (U : Finset (Fin 11)) : ℕ :=
  edgeCoding.maskOf (R.block U)

/-- The genuine target multiplicity at a packed edge position.  Values outside
the 55-position window are irrelevant to the search. -/
def actualRootEdgeTarget (i : ℕ) : ℕ :=
  if hi : i < 55 then
    rootEdgeTarget R.root (R.block R.root) (edgeAt ⟨i, hi⟩)
  else
    0

@[simp] theorem actualRootEdgeTarget_fin (i : Fin 55) :
    R.actualRootEdgeTarget i.val =
      rootEdgeTarget R.root (R.block R.root) (edgeAt i) := by
  rw [actualRootEdgeTarget, dif_pos i.isLt]

theorem actualBlockMask_testBit (U : Finset (Fin 11)) (i : Fin 55) :
    (R.actualBlockMask U).testBit i.val = decide (edgeAt i ∈ R.block U) := by
  rw [actualBlockMask, ← idx_edgeAt i]
  exact edgeCoding.testBit_maskOf_idx (R.block U) (edgeAt i)

private theorem actualBlockMasks_path_aux
    (domain : Finset (Fin 11) → List ℕ)
    (hdom : ∀ U ∈ R.near, R.actualBlockMask U ∈ domain U)
    (done todo : List (Finset (Fin 11)))
    (hnodup : (done.reverse ++ todo).Nodup)
    (hall : ∀ U ∈ done.reverse ++ todo, U ∈ R.near)
    (hcover : (done.reverse ++ todo).toFinset = R.near) :
    PartitePath (rootBlockMaskGuard R.actualRootEdgeTarget)
      (rootBlockMaskAccept R.actualRootEdgeTarget)
      (done.map R.actualBlockMask) (todo.map domain)
      (todo.map R.actualBlockMask) := by
  induction todo generalizing done with
  | nil =>
      apply PartitePath.nil
      rw [rootBlockMaskAccept, List.all_eq_true]
      intro i hi
      have hi55 : i < 55 := List.mem_range.mp hi
      let fi : Fin 55 := ⟨i, hi55⟩
      rw [beq_iff_eq]
      have hdoneRev : done.reverse.Nodup := by simpa using hnodup
      have hdone : done.Nodup := List.nodup_reverse.mp hdoneRev
      have hfilter :
          ((done.map R.actualBlockMask).filter fun m => m.testBit i).length =
            (done.filter fun U => edgeAt fi ∈ R.block U).length := by
        rw [List.filter_map, List.length_map]
        apply congrArg List.length
        apply List.filter_congr
        intro U _
        exact R.actualBlockMask_testBit U fi
      calc
        ((done.map R.actualBlockMask).filter fun m => m.testBit i).length =
            (done.filter fun U => edgeAt fi ∈ R.block U).length := hfilter
        _ = (done.toFinset.filter fun U => edgeAt fi ∈ R.block U).card :=
              filter_length_eq_finset_card done
                (fun U => edgeAt fi ∈ R.block U) hdone
        _ = (R.near.filter fun U => edgeAt fi ∈ R.block U).card := by
              have hset : done.toFinset = R.near := by simpa using hcover
              rw [hset]
        _ = rootEdgeTarget R.root (R.block R.root) (edgeAt fi) :=
              R.near_edge_balance (edgeAt fi)
        _ = R.actualRootEdgeTarget i := by
              exact (R.actualRootEdgeTarget_fin fi).symm
  | cons U todo ih =>
      have hU : U ∈ R.near := hall U (by simp)
      apply PartitePath.cons (hdom U hU)
      · rw [rootBlockMaskGuard, Bool.and_eq_true]
        constructor
        · rw [List.all_eq_true]
          intro prior hprior
          obtain ⟨V, hV, rfl⟩ := List.mem_map.mp hprior
          rw [beq_iff_eq, actualBlockMask, actualBlockMask,
            edgeCoding.popcount_and_maskOf]
          have hVnear : V ∈ R.near := hall V (by
            apply List.mem_append_left
            exact List.mem_reverse.mpr hV)
          have hVU : V ≠ U :=
            (List.nodup_append.mp hnodup).2.2 V
              (List.mem_reverse.mpr hV) U (by simp)
          simpa [Finset.inter_comm] using R.near_block_meet hU hVnear hVU.symm
        · rw [List.all_eq_true]
          intro i hi
          rw [decide_eq_true_eq]
          have hi55 : i < 55 := List.mem_range.mp hi
          let fi : Fin 55 := ⟨i, hi55⟩
          have hdoneRev : done.reverse.Nodup :=
            (List.nodup_append.mp hnodup).1
          have hdone : done.Nodup := List.nodup_reverse.mp hdoneRev
          have hUnotDone : U ∉ done := by
            intro hUdone
            exact ((List.nodup_append.mp hnodup).2.2 U
              (List.mem_reverse.mpr hUdone) U (by simp)) rfl
          have hprefNodup : (U :: done).Nodup :=
            List.nodup_cons.mpr ⟨hUnotDone, hdone⟩
          have hprefSub : (U :: done).toFinset ⊆ R.near := by
            intro V hV
            rw [List.mem_toFinset] at hV
            rcases List.mem_cons.mp hV with rfl | hV
            · exact hU
            · apply hall V
              apply List.mem_append_left
              exact List.mem_reverse.mpr hV
          have hfilter :
              (((R.actualBlockMask U) :: done.map R.actualBlockMask).filter
                fun m => m.testBit i).length =
                ((U :: done).filter fun V => edgeAt fi ∈ R.block V).length := by
            change
              (((((U :: done).map R.actualBlockMask).filter
                fun m => m.testBit i).length)) = _
            rw [List.filter_map, List.length_map]
            apply congrArg List.length
            apply List.filter_congr
            intro V _
            exact R.actualBlockMask_testBit V fi
          calc
            (((R.actualBlockMask U) :: done.map R.actualBlockMask).filter
                fun m => m.testBit i).length =
                ((U :: done).filter fun V => edgeAt fi ∈ R.block V).length := hfilter
            _ = ((U :: done).toFinset.filter
                  fun V => edgeAt fi ∈ R.block V).card :=
                filter_length_eq_finset_card (U :: done)
                  (fun V => edgeAt fi ∈ R.block V) hprefNodup
            _ ≤ (R.near.filter fun V => edgeAt fi ∈ R.block V).card :=
                Finset.card_le_card
                  (Finset.filter_subset_filter
                    (fun V => edgeAt fi ∈ R.block V) hprefSub)
            _ = rootEdgeTarget R.root (R.block R.root) (edgeAt fi) :=
                R.near_edge_balance (edgeAt fi)
            _ = R.actualRootEdgeTarget i :=
                (R.actualRootEdgeTarget_fin fi).symm
      · apply ih (U :: done)
        · simpa [List.reverse_cons, List.append_assoc] using hnodup
        · intro V hV
          apply hall V
          simpa [List.reverse_cons, List.append_assoc] using hV
        · simpa [List.reverse_cons, List.append_assoc] using hcover

/-- **Packed first-level completeness.**  Complete mask domains force the
genuine twenty-four block masks to occur in the executable DFS output. -/
theorem actualBlockMasks_mem_rootBlockMaskDFS
    (domain : Finset (Fin 11) → List ℕ)
    (hdom : ∀ U ∈ R.near, R.actualBlockMask U ∈ domain U) :
    R.near.toList.map R.actualBlockMask ∈
      rootBlockMaskDFS R.actualRootEdgeTarget R.near.toList domain := by
  rw [rootBlockMaskDFS, mem_partiteDFS_iff]
  apply R.actualBlockMasks_path_aux domain hdom [] R.near.toList
  · simpa using R.near.nodup_toList
  · intro U hU
    simpa using hU
  · simp

/-- The packed completeness theorem with an arbitrary duplicate-free ordering
of all genuine near rows.  Executable row lists need not use `Finset.toList`'s
noncomputable order. -/
theorem actualBlockMasks_mem_rootBlockMaskDFS_rows
    (rows : List (Finset (Fin 11)))
    (hnodup : rows.Nodup)
    (hall : ∀ U ∈ rows, U ∈ R.near)
    (hcover : rows.toFinset = R.near)
    (domain : Finset (Fin 11) → List ℕ)
    (hdom : ∀ U ∈ R.near, R.actualBlockMask U ∈ domain U) :
    rows.map R.actualBlockMask ∈
      rootBlockMaskDFS R.actualRootEdgeTarget rows domain := by
  rw [rootBlockMaskDFS, mem_partiteDFS_iff]
  apply R.actualBlockMasks_path_aux domain hdom [] rows
  · simpa using hnodup
  · intro U hU
    simpa using hall U hU
  · simpa using hcover

/-- An empty kernel-checked packed search contradicts the rooted design. -/
theorem false_of_rootBlockMaskDFS_eq_nil
    (domain : Finset (Fin 11) → List ℕ)
    (hdom : ∀ U ∈ R.near, R.actualBlockMask U ∈ domain U)
    (hempty : rootBlockMaskDFS R.actualRootEdgeTarget R.near.toList domain = []) :
    False := by
  have hmem := R.actualBlockMasks_mem_rootBlockMaskDFS domain hdom
  rw [hempty] at hmem
  exact List.not_mem_nil hmem

end GlobalDesignRoot

end SRG266.QuasiSymmetric
