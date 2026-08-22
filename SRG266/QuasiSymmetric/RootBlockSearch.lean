/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.GlobalDesignRoot
import SRG266.Search.PartiteDFS

/-!
# Complete first-level search for a rooted global design

This file connects the mathematical object `GlobalDesignRoot` to the generic
partite DFS checker.  The twenty-four rows are traversed in the order of
`R.near.toList`.  A candidate block must meet every previously selected block
in three edges, and a leaf is accepted exactly when every edge has the
replication number forced by `GlobalDesignRoot.near_edge_balance`.

The candidate domains are parameters.  A generated certificate module may
therefore use a compact enumeration of cubic graphs; its only completeness
obligation is to prove that the genuine block of each row belongs to the
corresponding list.  `actualBlocks_mem_rootBlockDFS` then proves that no
mathematical solution can be missed by the DFS.

There is no computation, axiom, or solver result in this module.
-/

namespace SRG266.QuasiSymmetric

open SRG266.Search

/-- The required number of first-neighbour blocks through an edge. -/
def rootEdgeTarget (root : Finset (Fin 11)) (rootBlock : Finset Edge11)
    (e : Edge11) : ℕ :=
  if e ∈ rootBlock then 0 else 6 + (e.vertices ∩ root).card

/-- Prefix guard for the first-level search: the new block meets every earlier
one in exactly three edges. -/
def rootBlockGuard (edges : List Edge11)
    (root : Finset (Fin 11)) (rootBlock : Finset Edge11)
    (chosenRev : List (Finset Edge11))
    (candidate : Finset Edge11) : Bool :=
  (chosenRev.all fun prior => decide ((candidate ∩ prior).card = 3)) &&
    (edges.all fun e =>
      decide (((candidate :: chosenRev).filter fun b => e ∈ b).length ≤
        rootEdgeTarget root rootBlock e))

/-- Exact terminal column check for the first-level search. -/
def rootBlockAccept (edges : List Edge11)
    (root : Finset (Fin 11)) (rootBlock : Finset Edge11)
    (chosenRev : List (Finset Edge11)) : Bool :=
  edges.all fun e =>
    decide ((chosenRev.filter fun b => e ∈ b).length =
      rootEdgeTarget root rootBlock e)

/-- The first-level DFS for arbitrary, certificate-supplied row domains. -/
def rootBlockDFS (edges : List Edge11)
    (root : Finset (Fin 11)) (rootBlock : Finset Edge11)
    (rows : List (Finset (Fin 11)))
    (domain : Finset (Fin 11) → List (Finset Edge11)) :
    List (List (Finset Edge11)) :=
  partiteDFS (rootBlockGuard edges root rootBlock)
    (rootBlockAccept edges root rootBlock)
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

private theorem actualBlocks_path_aux
    (domain : Finset (Fin 11) → List (Finset Edge11))
    (hdom : ∀ U ∈ R.near, R.block U ∈ domain U)
    (edges : List Edge11)
    (done todo : List (Finset (Fin 11)))
    (hnodup : (done.reverse ++ todo).Nodup)
    (hall : ∀ U ∈ done.reverse ++ todo, U ∈ R.near)
    (hcover : (done.reverse ++ todo).toFinset = R.near) :
    PartitePath (rootBlockGuard edges R.root (R.block R.root))
      (rootBlockAccept edges R.root (R.block R.root))
      (done.map R.block) (todo.map domain) (todo.map R.block) := by
  induction todo generalizing done with
  | nil =>
      apply PartitePath.nil
      rw [rootBlockAccept, List.all_eq_true]
      intro e _
      rw [decide_eq_true_eq]
      have hdoneRev : done.reverse.Nodup := by
        simpa using hnodup
      have hdone : done.Nodup := List.nodup_reverse.mp hdoneRev
      calc
        ((done.map R.block).filter fun b => e ∈ b).length =
            (done.filter fun U => e ∈ R.block U).length := by
              simp only [List.filter_map, List.length_map, Function.comp_def]
        _ = (done.toFinset.filter fun U => e ∈ R.block U).card :=
              filter_length_eq_finset_card done (fun U => e ∈ R.block U) hdone
        _ = (R.near.filter fun U => e ∈ R.block U).card := by
              have hset : done.toFinset = R.near := by
                simpa using hcover
              rw [hset]
        _ = rootEdgeTarget R.root (R.block R.root) e := by
              exact R.near_edge_balance e
  | cons U todo ih =>
      have hU : U ∈ R.near := hall U (by simp)
      apply PartitePath.cons (hdom U hU)
      · rw [rootBlockGuard, Bool.and_eq_true]
        constructor
        · rw [List.all_eq_true]
          intro prior hprior
          obtain ⟨V, hV, rfl⟩ := List.mem_map.mp hprior
          rw [decide_eq_true_eq]
          have hVnear : V ∈ R.near := hall V (by
            apply List.mem_append_left
            exact List.mem_reverse.mpr hV)
          have hVU : V ≠ U :=
            (List.nodup_append.mp hnodup).2.2 V
              (List.mem_reverse.mpr hV) U (by simp)
          simpa [Finset.inter_comm] using R.near_block_meet hU hVnear hVU.symm
        · rw [List.all_eq_true]
          intro e _
          rw [decide_eq_true_eq]
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
          calc
            (((R.block U) :: done.map R.block).filter fun b => e ∈ b).length =
                ((U :: done).filter fun V => e ∈ R.block V).length := by
                  change
                    ((((U :: done).map R.block).filter fun b => e ∈ b).length) = _
                  rw [List.filter_map, List.length_map]
                  apply congrArg List.length
                  apply List.filter_congr
                  intro V _
                  exact decide_eq_decide.mpr Iff.rfl
            _ = ((U :: done).toFinset.filter fun V => e ∈ R.block V).card :=
                  filter_length_eq_finset_card (U :: done)
                    (fun V => e ∈ R.block V) hprefNodup
            _ ≤ (R.near.filter fun V => e ∈ R.block V).card :=
                  Finset.card_le_card
                    (Finset.filter_subset_filter (fun V => e ∈ R.block V) hprefSub)
            _ = rootEdgeTarget R.root (R.block R.root) e := R.near_edge_balance e
      · apply ih (U :: done)
        · simpa [List.reverse_cons, List.append_assoc] using hnodup
        · intro V hV
          apply hall V
          simpa [List.reverse_cons, List.append_assoc] using hV
        · simpa [List.reverse_cons, List.append_assoc] using hcover

/-- **First-level search completeness.**  If every supplied row domain contains
the genuine cubic block, the complete block selection of `R` is returned by
the DFS.  Hence an empty checked result contradicts `R`. -/
theorem actualBlocks_mem_rootBlockDFS
    (edges : List Edge11)
    (domain : Finset (Fin 11) → List (Finset Edge11))
    (hdom : ∀ U ∈ R.near, R.block U ∈ domain U) :
    R.near.toList.map R.block ∈
      rootBlockDFS edges R.root (R.block R.root) R.near.toList domain := by
  rw [rootBlockDFS, mem_partiteDFS_iff]
  apply R.actualBlocks_path_aux domain hdom edges [] R.near.toList
  · simpa using R.near.nodup_toList
  · intro U hU
    simpa using hU
  · simp

/-- A kernel-checked empty first-level search refutes the rooted object, once
domain completeness has been proved. -/
theorem false_of_rootBlockDFS_eq_nil
    (edges : List Edge11)
    (domain : Finset (Fin 11) → List (Finset Edge11))
    (hdom : ∀ U ∈ R.near, R.block U ∈ domain U)
    (hempty : rootBlockDFS edges R.root (R.block R.root) R.near.toList domain = []) :
    False := by
  have hmem := R.actualBlocks_mem_rootBlockDFS edges domain hdom
  rw [hempty] at hmem
  exact List.not_mem_nil hmem

end GlobalDesignRoot

end SRG266.QuasiSymmetric
