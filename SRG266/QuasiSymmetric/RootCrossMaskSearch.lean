/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.VertexMask
import SRG266.QuasiSymmetric.RootCrossSearch

/-!
# Packed second-level search for a rooted global design

Cross rows are encoded as 2048-bit family masks at 11-bit characteristic-mask
positions.  Row labels are themselves 11-bit masks.  Consequently every hot
intersection and column-membership test is a natural-number operation, with no
trusted triple-numbering table.
-/

namespace SRG266.QuasiSymmetric

open SRG266.Search

set_option exponentiation.threshold 4096

/-- A fully packed row of the rooted cross matrix. -/
structure RootCrossMaskChoice where
  rowMask : ℕ
  columnMask : ℕ
deriving DecidableEq

/-- Pair intersections and upper column capacities on packed cross rows. -/
def rootCrossMaskGuard (rootMask : ℕ) (secondCodes : List ℕ)
    (chosenRev : List RootCrossMaskChoice) (candidate : RootCrossMaskChoice) : Bool :=
  (chosenRev.all fun prior =>
    popcount (candidate.columnMask &&& prior.columnMask) ==
      popcount (candidate.rowMask &&& prior.rowMask) + 2) &&
    (secondCodes.all fun code =>
      ((candidate :: chosenRev).filter fun c => c.columnMask.testBit code).length ≤
        popcount (rootMask &&& code) + 3)

/-- Exact packed column weights at a leaf. -/
def rootCrossMaskAccept (rootMask : ℕ) (secondCodes : List ℕ)
    (chosenRev : List RootCrossMaskChoice) : Bool :=
  secondCodes.all fun code =>
    ((chosenRev.filter fun c => c.columnMask.testBit code).length ==
      popcount (rootMask &&& code) + 3)

/-- Complete packed second-level DFS. -/
def rootCrossMaskDFS (rootMask : ℕ) (secondCodes : List ℕ)
    (rows : List (Finset (Fin 11)))
    (domain : Finset (Fin 11) → List RootCrossMaskChoice) :
    List (List RootCrossMaskChoice) :=
  partiteDFS (rootCrossMaskGuard rootMask secondCodes)
    (rootCrossMaskAccept rootMask secondCodes) (rows.map domain) []

private theorem filter_length_eq_finset_card {α : Type*} [DecidableEq α]
    (l : List α) (p : α → Prop) [DecidablePred p] (h : l.Nodup) :
    (l.filter fun x => decide (p x)).length = (l.toFinset.filter p).card := by
  rw [← List.toFinset_card_of_nodup (h.filter fun x => decide (p x))]
  apply congrArg Finset.card
  ext x
  simp

namespace GlobalZeroRoot

variable (R : GlobalZeroRoot)

/-- The genuine cross row in packed coordinates. -/
def actualCrossMaskChoice (U : Finset (Fin 11)) : RootCrossMaskChoice :=
  ⟨vertexMask U, vertexFamilyMask (R.actualCrossColumns U)⟩

private theorem actualCrossMaskRows_path_aux
    (domain : Finset (Fin 11) → List RootCrossMaskChoice)
    (hdom : ∀ U ∈ R.near, R.actualCrossMaskChoice U ∈ domain U)
    (secondCodes : List ℕ)
    (hsecond : ∀ code ∈ secondCodes, ∃ X,
      X ∈ zeroSecond R.root R.near ∧ vertexMask X = code)
    (done todo : List (Finset (Fin 11)))
    (hnodup : (done.reverse ++ todo).Nodup)
    (hall : ∀ U ∈ done.reverse ++ todo, U ∈ R.near)
    (hcover : (done.reverse ++ todo).toFinset = R.near) :
    PartitePath
      (rootCrossMaskGuard (vertexMask R.root) secondCodes)
      (rootCrossMaskAccept (vertexMask R.root) secondCodes)
      (done.map R.actualCrossMaskChoice) (todo.map domain)
      (todo.map R.actualCrossMaskChoice) := by
  induction todo generalizing done with
  | nil =>
      apply PartitePath.nil
      rw [rootCrossMaskAccept, List.all_eq_true]
      intro code hcode
      obtain ⟨X, hXsecond, rfl⟩ := hsecond code hcode
      rw [beq_iff_eq, popcount_and_vertexMask]
      have hdoneRev : done.reverse.Nodup := by simpa using hnodup
      have hdone : done.Nodup := List.nodup_reverse.mp hdoneRev
      have hfilter :
          ((done.map R.actualCrossMaskChoice).filter fun c =>
              c.columnMask.testBit (vertexMask X)).length =
            (done.filter fun U => X ∈ R.actualCrossColumns U).length := by
        rw [List.filter_map, List.length_map]
        apply congrArg List.length
        apply List.filter_congr
        intro U _
        exact testBit_vertexFamilyMask_vertexMask (R.actualCrossColumns U) X
      calc
        ((done.map R.actualCrossMaskChoice).filter fun c =>
            c.columnMask.testBit (vertexMask X)).length =
            (done.filter fun U => X ∈ R.actualCrossColumns U).length := hfilter
        _ = (done.toFinset.filter fun U => X ∈ R.actualCrossColumns U).card :=
              filter_length_eq_finset_card done
                (fun U => X ∈ R.actualCrossColumns U) hdone
        _ = (R.near.filter fun U => X ∈ R.actualCrossColumns U).card := by
              have hset : done.toFinset = R.near := by simpa using hcover
              rw [hset]
        _ = (R.cross X).card :=
              congrArg Finset.card (R.filter_near_mem_actualCrossColumns hXsecond)
        _ = (R.root ∩ X).card + 3 := R.cross_card hXsecond
  | cons U todo ih =>
      have hU : U ∈ R.near := hall U (by simp)
      apply PartitePath.cons (hdom U hU)
      · rw [rootCrossMaskGuard, Bool.and_eq_true]
        constructor
        · rw [List.all_eq_true]
          intro prior hprior
          obtain ⟨V, hV, rfl⟩ := List.mem_map.mp hprior
          rw [beq_iff_eq, actualCrossMaskChoice, actualCrossMaskChoice,
            popcount_and_vertexFamilyMask, popcount_and_vertexMask]
          have hVnear : V ∈ R.near := hall V (by
            apply List.mem_append_left
            exact List.mem_reverse.mpr hV)
          have hVU : V ≠ U :=
            (List.nodup_append.mp hnodup).2.2 V
              (List.mem_reverse.mpr hV) U (by simp)
          have hp := R.cross_pair hU hVnear hVU.symm
          have hsets :
              R.actualCrossColumns U ∩ R.actualCrossColumns V =
                (zeroSecond R.root R.near).filter fun X =>
                  U ∈ R.cross X ∧ V ∈ R.cross X := by
            ext X
            simp [R.mem_actualCrossColumns, and_assoc, and_left_comm]
          rw [hsets]
          exact hp
        · rw [List.all_eq_true]
          intro code hcode
          rw [decide_eq_true_eq]
          obtain ⟨X, hXsecond, rfl⟩ := hsecond code hcode
          rw [popcount_and_vertexMask]
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
              (((R.actualCrossMaskChoice U) :: done.map R.actualCrossMaskChoice).filter
                fun c => c.columnMask.testBit (vertexMask X)).length =
                ((U :: done).filter fun V => X ∈ R.actualCrossColumns V).length := by
            change
              (((((U :: done).map R.actualCrossMaskChoice).filter
                fun c => c.columnMask.testBit (vertexMask X)).length)) = _
            rw [List.filter_map, List.length_map]
            apply congrArg List.length
            apply List.filter_congr
            intro V _
            exact testBit_vertexFamilyMask_vertexMask (R.actualCrossColumns V) X
          calc
            (((R.actualCrossMaskChoice U) :: done.map R.actualCrossMaskChoice).filter
                fun c => c.columnMask.testBit (vertexMask X)).length =
                ((U :: done).filter fun V => X ∈ R.actualCrossColumns V).length := hfilter
            _ = ((U :: done).toFinset.filter
                  fun V => X ∈ R.actualCrossColumns V).card :=
                filter_length_eq_finset_card (U :: done)
                  (fun V => X ∈ R.actualCrossColumns V) hprefNodup
            _ ≤ (R.near.filter fun V => X ∈ R.actualCrossColumns V).card :=
                Finset.card_le_card
                  (Finset.filter_subset_filter
                    (fun V => X ∈ R.actualCrossColumns V) hprefSub)
            _ = (R.cross X).card :=
                congrArg Finset.card (R.filter_near_mem_actualCrossColumns hXsecond)
            _ = (R.root ∩ X).card + 3 := R.cross_card hXsecond
      · apply ih (U :: done)
        · simpa [List.reverse_cons, List.append_assoc] using hnodup
        · intro V hV
          apply hall V
          simpa [List.reverse_cons, List.append_assoc] using hV
        · simpa [List.reverse_cons, List.append_assoc] using hcover

/-- **Packed second-level completeness.** -/
theorem actualCrossMaskRows_mem_rootCrossMaskDFS
    (domain : Finset (Fin 11) → List RootCrossMaskChoice)
    (hdom : ∀ U ∈ R.near, R.actualCrossMaskChoice U ∈ domain U) :
    R.near.toList.map R.actualCrossMaskChoice ∈
      rootCrossMaskDFS (vertexMask R.root)
        ((zeroSecond R.root R.near).toList.map vertexMask)
        R.near.toList domain := by
  rw [rootCrossMaskDFS, mem_partiteDFS_iff]
  apply R.actualCrossMaskRows_path_aux domain hdom
    ((zeroSecond R.root R.near).toList.map vertexMask) (by
      intro code hcode
      obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hcode
      exact ⟨X, by simpa using hX, rfl⟩) [] R.near.toList
  · simpa using R.near.nodup_toList
  · intro U hU
    simpa using hU
  · simp

/-- Packed second-level completeness with arbitrary executable row and column
orders.  Every supplied column code need only decode to a genuine second
triple; omitting constraints enlarges the search and therefore cannot lose the
genuine solution. -/
theorem actualCrossMaskRows_mem_rootCrossMaskDFS_rows
    (secondCodes : List ℕ)
    (hsecond : ∀ code ∈ secondCodes, ∃ X,
      X ∈ zeroSecond R.root R.near ∧ vertexMask X = code)
    (rows : List (Finset (Fin 11)))
    (hnodup : rows.Nodup)
    (hall : ∀ U ∈ rows, U ∈ R.near)
    (hcover : rows.toFinset = R.near)
    (domain : Finset (Fin 11) → List RootCrossMaskChoice)
    (hdom : ∀ U ∈ R.near, R.actualCrossMaskChoice U ∈ domain U) :
    rows.map R.actualCrossMaskChoice ∈
      rootCrossMaskDFS (vertexMask R.root) secondCodes rows domain := by
  rw [rootCrossMaskDFS, mem_partiteDFS_iff]
  apply R.actualCrossMaskRows_path_aux domain hdom secondCodes hsecond [] rows
  · simpa using hnodup
  · intro U hU
    simpa using hall U hU
  · simpa using hcover

/-- An empty packed second-level search contradicts the rooted object. -/
theorem false_of_rootCrossMaskDFS_eq_nil
    (domain : Finset (Fin 11) → List RootCrossMaskChoice)
    (hdom : ∀ U ∈ R.near, R.actualCrossMaskChoice U ∈ domain U)
    (hempty : rootCrossMaskDFS (vertexMask R.root)
      ((zeroSecond R.root R.near).toList.map vertexMask)
      R.near.toList domain = []) : False := by
  have hmem := R.actualCrossMaskRows_mem_rootCrossMaskDFS domain hdom
  rw [hempty] at hmem
  exact List.not_mem_nil hmem

end GlobalZeroRoot

end SRG266.QuasiSymmetric
