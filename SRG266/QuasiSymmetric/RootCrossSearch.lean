/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.RootBlockSearch

/-!
# Complete second-level search for a rooted global design

After the twenty-four neighbour blocks have been fixed, the second search
chooses, for every first-neighbour row `U`, its twenty-three neighbours among
the remaining `140` triples.  A choice is tagged with its row so that the
pairwise target `2 + #(U ∩ V)` is part of the executable guard.  At a leaf,
every second-column has its exact weight `3 + #(root ∩ X)`.

As in `RootBlockSearch.lean`, row domains are supplied by certificate modules.
The theorem `actualCrossRows_mem_rootCrossDFS` proves search completeness from
the single local obligation that every genuine row occurs in its domain.
No generated conclusion is trusted here.
-/

namespace SRG266.QuasiSymmetric

open SRG266.Search

/-- One tagged row of the `24 × 140` cross-incidence matrix. -/
structure RootCrossChoice where
  row : Finset (Fin 11)
  columns : Finset (Finset (Fin 11))
deriving DecidableEq

/-- Pairwise scalar-product guard for cross rows. -/
def rootCrossGuard (root : Finset (Fin 11))
    (secondColumns : List (Finset (Fin 11)))
    (chosenRev : List RootCrossChoice)
    (candidate : RootCrossChoice) : Bool :=
  (chosenRev.all fun prior =>
    decide ((candidate.columns ∩ prior.columns).card =
      (candidate.row ∩ prior.row).card + 2)) &&
    (secondColumns.all fun V =>
      decide (((candidate :: chosenRev).filter fun c => V ∈ c.columns).length ≤
        (root ∩ V).card + 3))

/-- Exact terminal column weights of the cross-incidence matrix. -/
def rootCrossAccept (root : Finset (Fin 11))
    (secondColumns : List (Finset (Fin 11)))
    (chosenRev : List RootCrossChoice) : Bool :=
  secondColumns.all fun V =>
    decide ((chosenRev.filter fun c => V ∈ c.columns).length =
      (root ∩ V).card + 3)

/-- The complete second-level DFS for certificate-supplied row domains. -/
def rootCrossDFS (root : Finset (Fin 11))
    (secondColumns rows : List (Finset (Fin 11)))
    (domain : Finset (Fin 11) → List RootCrossChoice) :
    List (List RootCrossChoice) :=
  partiteDFS (rootCrossGuard root secondColumns)
    (rootCrossAccept root secondColumns)
    (rows.map domain) []

private theorem filter_length_eq_finset_card {α : Type*} [DecidableEq α]
    (l : List α) (p : α → Prop) [DecidablePred p] (h : l.Nodup) :
    (l.filter fun x => decide (p x)).length = (l.toFinset.filter p).card := by
  rw [← List.toFinset_card_of_nodup (h.filter fun x => decide (p x))]
  apply congrArg Finset.card
  ext x
  simp

namespace GlobalZeroRoot

variable (R : GlobalZeroRoot)

/-- The genuine set of second columns selected in row `U`. -/
def actualCrossColumns (U : Finset (Fin 11)) :
    Finset (Finset (Fin 11)) :=
  (zeroSecond R.root R.near).filter fun V => U ∈ R.cross V

/-- The genuine tagged cross row. -/
def actualCrossChoice (U : Finset (Fin 11)) : RootCrossChoice :=
  ⟨U, R.actualCrossColumns U⟩

theorem mem_actualCrossColumns {U V : Finset (Fin 11)} :
    V ∈ R.actualCrossColumns U ↔
      V ∈ zeroSecond R.root R.near ∧ U ∈ R.cross V := by
  simp [actualCrossColumns]

/-- On a genuine second column, filtering the first-neighbourhood rows by
membership in their actual cross row recovers exactly `R.cross V`. -/
theorem filter_near_mem_actualCrossColumns {V : Finset (Fin 11)}
    (hV : V ∈ zeroSecond R.root R.near) :
    R.near.filter (fun U => V ∈ R.actualCrossColumns U) = R.cross V := by
  ext U
  constructor
  · intro hU
    exact (R.mem_actualCrossColumns.mp (Finset.mem_filter.mp hU).2).2
  · intro hU
    exact Finset.mem_filter.mpr
      ⟨R.cross_closed hV hU, R.mem_actualCrossColumns.mpr ⟨hV, hU⟩⟩

private theorem actualCrossRows_path_aux
    (domain : Finset (Fin 11) → List RootCrossChoice)
    (hdom : ∀ U ∈ R.near, R.actualCrossChoice U ∈ domain U)
    (done todo : List (Finset (Fin 11)))
    (hnodup : (done.reverse ++ todo).Nodup)
    (hall : ∀ U ∈ done.reverse ++ todo, U ∈ R.near)
    (hcover : (done.reverse ++ todo).toFinset = R.near) :
    PartitePath
      (rootCrossGuard R.root (zeroSecond R.root R.near).toList)
      (rootCrossAccept R.root (zeroSecond R.root R.near).toList)
      (done.map R.actualCrossChoice) (todo.map domain)
      (todo.map R.actualCrossChoice) := by
  induction todo generalizing done with
  | nil =>
      apply PartitePath.nil
      rw [rootCrossAccept, List.all_eq_true]
      intro V hV
      have hVsecond : V ∈ zeroSecond R.root R.near := by
        simpa using hV
      rw [decide_eq_true_eq]
      have hdoneRev : done.reverse.Nodup := by
        simpa using hnodup
      have hdone : done.Nodup := List.nodup_reverse.mp hdoneRev
      have hfilter :
          ((done.map R.actualCrossChoice).filter fun c => V ∈ c.columns).length =
            (done.filter fun U => V ∈ R.actualCrossColumns U).length := by
        rw [List.filter_map, List.length_map]
        apply congrArg List.length
        apply List.filter_congr
        intro U _
        exact decide_eq_decide.mpr Iff.rfl
      have hset := R.filter_near_mem_actualCrossColumns hVsecond
      calc
        ((done.map R.actualCrossChoice).filter fun c => V ∈ c.columns).length =
            (done.filter fun U => V ∈ R.actualCrossColumns U).length := hfilter
        _ = (done.toFinset.filter fun U => V ∈ R.actualCrossColumns U).card :=
              filter_length_eq_finset_card done
                (fun U => V ∈ R.actualCrossColumns U) hdone
        _ = (R.near.filter fun U => V ∈ R.actualCrossColumns U).card := by
              have hdoneSet : done.toFinset = R.near := by
                simpa using hcover
              rw [hdoneSet]
        _ = (R.cross V).card := congrArg Finset.card hset
        _ = (R.root ∩ V).card + 3 := R.cross_card hVsecond
  | cons U todo ih =>
      have hU : U ∈ R.near := hall U (by simp)
      apply PartitePath.cons (hdom U hU)
      · rw [rootCrossGuard, Bool.and_eq_true]
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
          have hp := R.cross_pair hU hVnear hVU.symm
          have hsets :
              R.actualCrossColumns U ∩ R.actualCrossColumns V =
                (zeroSecond R.root R.near).filter fun X =>
                  U ∈ R.cross X ∧ V ∈ R.cross X := by
            ext X
            simp [R.mem_actualCrossColumns, and_assoc, and_left_comm]
          rw [actualCrossChoice, actualCrossChoice, hsets]
          exact hp
        · rw [List.all_eq_true]
          intro X hX
          have hXsecond : X ∈ zeroSecond R.root R.near := by simpa using hX
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
          have hfilter :
              (((R.actualCrossChoice U) :: done.map R.actualCrossChoice).filter
                fun c => X ∈ c.columns).length =
                ((U :: done).filter fun V => X ∈ R.actualCrossColumns V).length := by
            change
              (((((U :: done).map R.actualCrossChoice).filter
                fun c => X ∈ c.columns).length)) = _
            rw [List.filter_map, List.length_map]
            apply congrArg List.length
            apply List.filter_congr
            intro V _
            exact decide_eq_decide.mpr Iff.rfl
          calc
            (((R.actualCrossChoice U) :: done.map R.actualCrossChoice).filter
                fun c => X ∈ c.columns).length =
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

/-- **Second-level search completeness.**  If each supplied domain contains
the genuine row, the whole cross-incidence matrix occurs in the DFS output. -/
theorem actualCrossRows_mem_rootCrossDFS
    (domain : Finset (Fin 11) → List RootCrossChoice)
    (hdom : ∀ U ∈ R.near, R.actualCrossChoice U ∈ domain U) :
    R.near.toList.map R.actualCrossChoice ∈
      rootCrossDFS R.root (zeroSecond R.root R.near).toList
        R.near.toList domain := by
  rw [rootCrossDFS, mem_partiteDFS_iff]
  apply R.actualCrossRows_path_aux domain hdom [] R.near.toList
  · simpa using R.near.nodup_toList
  · intro U hU
    simpa using hU
  · simp

/-- An empty checked second-level search contradicts the rooted object. -/
theorem false_of_rootCrossDFS_eq_nil
    (domain : Finset (Fin 11) → List RootCrossChoice)
    (hdom : ∀ U ∈ R.near, R.actualCrossChoice U ∈ domain U)
    (hempty : rootCrossDFS R.root (zeroSecond R.root R.near).toList
      R.near.toList domain = []) : False := by
  have hmem := R.actualCrossRows_mem_rootCrossDFS domain hdom
  rw [hempty] at hmem
  exact List.not_mem_nil hmem

end GlobalZeroRoot

end SRG266.QuasiSymmetric
