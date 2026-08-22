/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.RootOrbitTransport
import SRG266.Search.RemainingItemDFS

/-!
# Complete compact shells for fractional near frames

This module enumerates the regular triple-system columns attached to one
compact rooted near family.  Its exact-demand search stores the remaining
eight point degrees explicitly.  A normal Lean invariant proof shows that
every mathematical column occurs in the executable list; generated Farkas
checks may therefore use the list without trusting the generator.
-/

namespace SRG266.QuasiSymmetric

open SRG266.Search

/-! ## Compact coordinates -/

/-- The selected compact triple positions of a rooted near mask. -/
def compactNearRows (nearMask : ℕ) : List ℕ :=
  ((List.finRange 56).filter fun i => nearMask.testBit i.val).map Fin.val

/-- Safe lookup of the compact three-vertex mask at a triple position. -/
def compactTripleCodeAt (index : ℕ) : ℕ :=
  triple8Codes.toArray.getD index 0

/-- Safe lookup of the compact two-vertex mask at a pair position. -/
def compactPairCodeAt (index : ℕ) : ℕ :=
  edge8Codes.toArray.getD index 0

/-- The endpoint types in certificate order: the empty set, the eight
singletons, and the sixteen root nonedges. -/
def compactEndpointMasks (nearMask : ℕ) : List ℕ :=
  let rootGraph := reconstructedRootGraph8 nearMask
  [0] ++ (List.range 8).map (fun v => 2 ^ v) ++
    (((List.finRange 28).filter fun i => !(rootGraph.testBit i.val)).map
      fun i => compactPairCodeAt i.val)

/-- Compact triple positions incident with one active vertex. -/
def compactTripleIndicesAtVertex (vertex : ℕ) : List ℕ :=
  ((List.finRange 56).filter fun i =>
    (compactTripleCodeAt i.val).testBit vertex).map Fin.val

/-- Point degree of a compact column mask. -/
def compactColumnVertexCount (columnMask vertex : ℕ) : ℕ :=
  popcount (localAssignmentMask
    (compactTripleIndicesAtVertex vertex) columnMask)

/-- Target point degree for one endpoint shell. -/
def compactColumnVertexTarget (endpointMask vertex : ℕ) : ℕ :=
  if endpointMask.testBit vertex then 0 else 3

/-- Near rows available to a shell: selected near triples which avoid every
endpoint. -/
def compactNearColumnItems (nearMask endpointMask : ℕ) : List ℕ :=
  ((List.finRange 56).filter fun i =>
    nearMask.testBit i.val &&
      decide (compactTripleCodeAt i.val &&& endpointMask = 0)).map Fin.val

/-! ## Complete exact-demand enumeration -/

structure TransparentCompactColumnState where
  columnMask : ℕ
  demand : Fin 8 → ℕ

def transparentCompactColumnInitialDemand (endpointMask : ℕ) : Fin 8 → ℕ :=
  fun vertex => compactColumnVertexTarget endpointMask vertex.val

def transparentCompactColumnCodeValid
    (state : TransparentCompactColumnState) (code : ℕ) : Bool :=
  (!state.columnMask.testBit code) &&
    (List.finRange 8).all fun vertex =>
      !(compactTripleCodeAt code).testBit vertex.val || decide (0 < state.demand vertex)

def transparentCompactColumnPivot (state : TransparentCompactColumnState) : Option (Fin 8) :=
  (List.finRange 8).find? fun vertex => decide (0 < state.demand vertex)

def transparentCompactBundleCount (selected : List ℕ) (vertex : Fin 8) : ℕ :=
  (selected.toFinset.filter fun code =>
    (compactTripleCodeAt code).testBit vertex.val).card

def transparentCompactBundleValid
    (state : TransparentCompactColumnState) (selected : List ℕ) : Bool :=
  (List.finRange 8).all fun vertex =>
    decide (transparentCompactBundleCount selected vertex ≤ state.demand vertex)

def nextTransparentCompactState
    (state : TransparentCompactColumnState) (selected : List ℕ) :
    TransparentCompactColumnState :=
  { columnMask := state.columnMask ||| SRG266.Search.itemPositionsMask selected
    demand := fun vertex =>
      state.demand vertex - transparentCompactBundleCount selected vertex }

def addTransparentCompactBundle?
    (state : TransparentCompactColumnState) (selected : List ℕ) :
    Option TransparentCompactColumnState :=
  if transparentCompactBundleValid state selected then
    some (nextTransparentCompactState state selected)
  else none

def transparentCompactNearColumnAux (items : List ℕ) :
    ℕ → TransparentCompactColumnState → List ℕ
  | 0, _ => []
  | fuel + 1, state =>
      let validItems := items.filter fun code => transparentCompactColumnCodeValid state code
      match transparentCompactColumnPivot state with
      | none => [state.columnMask]
      | some pivot =>
          let need := state.demand pivot
          let candidates := validItems.filter fun code =>
            (compactTripleCodeAt code).testBit pivot.val
          (candidates.sublistsLen need).flatMap fun selected =>
            match addTransparentCompactBundle? state selected with
            | none => []
            | some next => transparentCompactNearColumnAux items fuel next

def transparentCompactNearColumnShell (nearMask endpointMask : ℕ) : List ℕ :=
  let items := compactNearColumnItems nearMask endpointMask
  transparentCompactNearColumnAux items 9
    ⟨0, transparentCompactColumnInitialDemand endpointMask⟩

/-! ## Logical specification -/

/-- Items of a proposed completion which have not yet been selected. -/
def transparentCompactRemaining (items : List ℕ)
    (state : TransparentCompactColumnState) (goalMask : ℕ) : Finset ℕ :=
  items.toFinset.filter fun code =>
    goalMask.testBit code = true ∧ state.columnMask.testBit code = false

/-- A search state represents exactly the unselected part of one goal mask. -/
def TransparentCompactCompletion (items : List ℕ)
    (state : TransparentCompactColumnState) (goalMask : ℕ) : Prop :=
  (∀ code, state.columnMask.testBit code = true → goalMask.testBit code = true) ∧
  (∀ code, goalMask.testBit code = true → code ∈ items) ∧
  ∀ vertex : Fin 8, state.demand vertex =
    ((transparentCompactRemaining items state goalMask).filter fun code =>
      (compactTripleCodeAt code).testBit vertex.val).card

/-- Mathematical regular-column condition in compact coordinates. -/
def IsCompactNearColumn (nearMask endpointMask columnMask : ℕ) : Prop :=
  (∀ code, columnMask.testBit code = true →
    code ∈ compactNearColumnItems nearMask endpointMask) ∧
  ∀ vertex : Fin 8,
    (((compactNearColumnItems nearMask endpointMask).toFinset.filter fun code =>
      columnMask.testBit code = true ∧
        (compactTripleCodeAt code).testBit vertex.val).card) =
      compactColumnVertexTarget endpointMask vertex.val

theorem transparentCompactCompletion_initial
    {nearMask endpointMask goalMask : ℕ}
    (hgoal : IsCompactNearColumn nearMask endpointMask goalMask) :
    TransparentCompactCompletion
      (compactNearColumnItems nearMask endpointMask)
      ⟨0, transparentCompactColumnInitialDemand endpointMask⟩ goalMask := by
  refine ⟨?_, hgoal.1, ?_⟩
  · intro code hbit
    simp at hbit
  · intro vertex
    change compactColumnVertexTarget endpointMask vertex.val = _
    rw [← hgoal.2 vertex]
    congr 1
    ext code
    simp [transparentCompactRemaining]
    tauto

theorem transparentCompactRemaining_addBundle
    {items selected : List ℕ} {state : TransparentCompactColumnState}
    {goalMask : ℕ} :
    transparentCompactRemaining items
      (nextTransparentCompactState state selected) goalMask =
    transparentCompactRemaining items state goalMask \ selected.toFinset := by
  ext code
  simp only [nextTransparentCompactState]
  have hitemFalse :
      (SRG266.Search.itemPositionsMask selected).testBit code = false ↔
        code ∉ selected := by
    constructor
    · intro hfalse hmem
      have htrue := SRG266.Search.testBit_itemPositionsMask_of_mem hmem
      rw [hfalse] at htrue
      contradiction
    · intro hnot
      cases hbit : (SRG266.Search.itemPositionsMask selected).testBit code
      · rfl
      · exact False.elim (hnot
          (SRG266.Search.testBit_itemPositionsMask_iff.mp hbit))
  simp only [transparentCompactRemaining, Finset.mem_filter, List.mem_toFinset,
    Nat.testBit_or, Bool.or_eq_false_iff, hitemFalse, Finset.mem_sdiff]
  tauto

theorem filter_sublist_filter_of_imp {α : Type*} (items : List α)
    (p q : α → Bool) (himp : ∀ x ∈ items, p x = true → q x = true) :
    List.Sublist (items.filter p) (items.filter q) := by
  induction items with
  | nil => simp
  | cons x items ih =>
      have himptail : ∀ y ∈ items, p y = true → q y = true := by
        intro y hy
        exact himp y (by simp [hy])
      have hsub := ih himptail
      cases hp : p x <;> cases hq : q x
      · simpa [hp, hq] using hsub
      · simpa [hp, hq] using List.Sublist.cons x hsub
      · exact False.elim (by
          have := himp x (by simp) hp
          simp [hq] at this)
      · simpa [hp, hq] using List.Sublist.cons_cons x hsub

theorem compactNearColumnItems_nodup (nearMask endpointMask : ℕ) :
    (compactNearColumnItems nearMask endpointMask).Nodup := by
  rw [compactNearColumnItems]
  apply List.Nodup.map_on _ ((List.nodup_finRange 56).filter _)
  intro i _ j _ hij
  exact Fin.ext hij

def transparentCompactSelected (items : List ℕ)
    (state : TransparentCompactColumnState) (goalMask : ℕ)
    (pivot : Fin 8) : List ℕ :=
  items.filter fun code =>
    goalMask.testBit code && !state.columnMask.testBit code &&
      (compactTripleCodeAt code).testBit pivot.val

theorem transparentCompactSelected_toFinset
    (items : List ℕ) (state : TransparentCompactColumnState) (goalMask : ℕ)
    (pivot : Fin 8) :
    (transparentCompactSelected items state goalMask pivot).toFinset =
      (transparentCompactRemaining items state goalMask).filter fun code =>
        (compactTripleCodeAt code).testBit pivot.val := by
  ext code
  simp [transparentCompactSelected, transparentCompactRemaining,
    Bool.and_eq_true, and_assoc]

theorem transparentCompactCodeValid_of_mem_remaining
    {items : List ℕ} {state : TransparentCompactColumnState} {goalMask code : ℕ}
    (hcompletion : TransparentCompactCompletion items state goalMask)
    (hcode : code ∈ transparentCompactRemaining items state goalMask) :
    transparentCompactColumnCodeValid state code = true := by
  rw [transparentCompactColumnCodeValid, Bool.and_eq_true]
  have hstate : state.columnMask.testBit code = false :=
    (Finset.mem_filter.mp hcode).2.2
  constructor
  · simp [hstate]
  · rw [List.all_eq_true]
    intro vertex _
    by_cases hinc : (compactTripleCodeAt code).testBit vertex.val = true
    · rw [Bool.or_eq_true]
      right
      rw [decide_eq_true_eq, hcompletion.2.2 vertex]
      exact Finset.card_pos.mpr
        ⟨code, Finset.mem_filter.mpr ⟨hcode, hinc⟩⟩
    · have hfalse : (compactTripleCodeAt code).testBit vertex.val = false :=
        Bool.eq_false_of_not_eq_true hinc
      simp [hfalse]

theorem transparentCompactSelected_length
    {items : List ℕ} {state : TransparentCompactColumnState} {goalMask : ℕ}
    (hitems : items.Nodup)
    (hcompletion : TransparentCompactCompletion items state goalMask)
    (pivot : Fin 8) :
    (transparentCompactSelected items state goalMask pivot).length =
      state.demand pivot := by
  have hnodup :
      (transparentCompactSelected items state goalMask pivot).Nodup := by
    exact hitems.filter _
  rw [← List.toFinset_card_of_nodup hnodup,
    transparentCompactSelected_toFinset, hcompletion.2.2 pivot]

theorem transparentCompactSelected_subset_remaining
    (items : List ℕ) (state : TransparentCompactColumnState) (goalMask : ℕ)
    (pivot : Fin 8) :
    (transparentCompactSelected items state goalMask pivot).toFinset ⊆
      transparentCompactRemaining items state goalMask := by
  rw [transparentCompactSelected_toFinset]
  exact Finset.filter_subset _ _

theorem transparentCompactSelected_bundleValid
    {items : List ℕ} {state : TransparentCompactColumnState} {goalMask : ℕ}
    (hcompletion : TransparentCompactCompletion items state goalMask)
    (pivot : Fin 8) :
    transparentCompactBundleValid state
      (transparentCompactSelected items state goalMask pivot) = true := by
  rw [transparentCompactBundleValid, List.all_eq_true]
  intro vertex _
  rw [decide_eq_true_eq, hcompletion.2.2 vertex]
  apply Finset.card_le_card
  intro code hcode
  rw [Finset.mem_filter] at hcode ⊢
  exact ⟨transparentCompactSelected_subset_remaining items state goalMask pivot hcode.1,
    hcode.2⟩

theorem transparentCompactCompletion_next
    {items : List ℕ} {state : TransparentCompactColumnState} {goalMask : ℕ}
    (hcompletion : TransparentCompactCompletion items state goalMask)
    (pivot : Fin 8) :
    TransparentCompactCompletion items
      (nextTransparentCompactState state
        (transparentCompactSelected items state goalMask pivot)) goalMask := by
  let selected := transparentCompactSelected items state goalMask pivot
  have hselected : selected.toFinset ⊆
      transparentCompactRemaining items state goalMask := by
    exact transparentCompactSelected_subset_remaining items state goalMask pivot
  refine ⟨?_, hcompletion.2.1, ?_⟩
  · intro code hbit
    rw [nextTransparentCompactState, Nat.testBit_or, Bool.or_eq_true] at hbit
    rcases hbit with hstate | hselectedBit
    · exact hcompletion.1 code hstate
    · have hmem : code ∈ selected :=
        SRG266.Search.testBit_itemPositionsMask_iff.mp hselectedBit
      exact (Finset.mem_filter.mp (hselected (by simpa using hmem))).2.1
  · intro vertex
    rw [transparentCompactRemaining_addBundle]
    change state.demand vertex -
      transparentCompactBundleCount selected vertex = _
    rw [hcompletion.2.2 vertex]
    let remainingAt :=
      (transparentCompactRemaining items state goalMask).filter fun code =>
        (compactTripleCodeAt code).testBit vertex.val
    let selectedAt := selected.toFinset.filter fun code =>
      (compactTripleCodeAt code).testBit vertex.val
    have hselectedAt : selectedAt ⊆ remainingAt := by
      intro code hcode
      rw [Finset.mem_filter] at hcode ⊢
      exact ⟨hselected hcode.1, hcode.2⟩
    have hset :
        ((transparentCompactRemaining items state goalMask \ selected.toFinset).filter
          fun code => (compactTripleCodeAt code).testBit vertex.val) =
        remainingAt \ selectedAt := by
      ext code
      by_cases hinc : (compactTripleCodeAt code).testBit vertex.val = true
      · simp [remainingAt, selectedAt, hinc]
      · have hfalse : (compactTripleCodeAt code).testBit vertex.val = false :=
          Bool.eq_false_of_not_eq_true hinc
        simp [remainingAt, selectedAt, hfalse]
    rw [hset, Finset.card_sdiff_of_subset hselectedAt]
    rfl

theorem transparentCompactSelected_sublist_candidates
    {items : List ℕ} {state : TransparentCompactColumnState} {goalMask : ℕ}
    (hcompletion : TransparentCompactCompletion items state goalMask)
    (pivot : Fin 8) :
    List.Sublist (transparentCompactSelected items state goalMask pivot)
      ((items.filter fun code => transparentCompactColumnCodeValid state code).filter
        fun code => (compactTripleCodeAt code).testBit pivot.val) := by
  rw [List.filter_filter]
  apply filter_sublist_filter_of_imp
  intro code hitem hselected
  have hpartsRaw :
      (goalMask.testBit code = true ∧ state.columnMask.testBit code = false) ∧
        (compactTripleCodeAt code).testBit pivot.val = true := by
    simpa [Bool.and_eq_true] using hselected
  have hparts :
      goalMask.testBit code = true ∧
        state.columnMask.testBit code = false ∧
          (compactTripleCodeAt code).testBit pivot.val = true := by
    exact ⟨hpartsRaw.1.1, hpartsRaw.1.2, hpartsRaw.2⟩
  rw [Bool.and_eq_true]
  refine ⟨hparts.2.2, transparentCompactCodeValid_of_mem_remaining hcompletion ?_⟩
  exact Finset.mem_filter.mpr ⟨by simpa using hitem, hparts.1, hparts.2.1⟩

theorem compactNearColumnItems_lt {nearMask endpointMask code : ℕ}
    (hcode : code ∈ compactNearColumnItems nearMask endpointMask) : code < 56 := by
  rw [compactNearColumnItems, List.mem_map] at hcode
  obtain ⟨index, _, rfl⟩ := hcode
  exact index.isLt

/-- Every mathematical compact column is supported on the fixed 56-position
triple dictionary. -/
theorem IsCompactNearColumn.lt_two_pow
    {nearMask endpointMask columnMask : ℕ}
    (hcolumn : IsCompactNearColumn nearMask endpointMask columnMask) :
    columnMask < 2 ^ 56 := by
  apply Nat.lt_pow_two_of_testBit
  intro index hindex
  cases hbit : columnMask.testBit index with
  | false => rfl
  | true =>
      have hmem := hcolumn.1 index hbit
      have hlt := compactNearColumnItems_lt hmem
      omega

theorem compactTripleCodeAt_has_vertex (index : Fin 56) :
    ∃ vertex : Fin 8,
      (compactTripleCodeAt index.val).testBit vertex.val = true := by
  revert index
  decide +kernel

theorem compactNearColumnItem_has_vertex
    {nearMask endpointMask code : ℕ}
    (hcode : code ∈ compactNearColumnItems nearMask endpointMask) :
    ∃ vertex : Fin 8,
      (compactTripleCodeAt code).testBit vertex.val = true := by
  let index : Fin 56 := ⟨code, compactNearColumnItems_lt hcode⟩
  simpa [index] using compactTripleCodeAt_has_vertex index

def transparentPositiveDemands (state : TransparentCompactColumnState) :
    Finset (Fin 8) :=
  Finset.univ.filter fun vertex => 0 < state.demand vertex

theorem transparentCompactPivot_none_demands_zero
    {state : TransparentCompactColumnState}
    (hpivot : transparentCompactColumnPivot state = none) :
    ∀ vertex, state.demand vertex = 0 := by
  intro vertex
  have hnot : ¬ 0 < state.demand vertex := by
    intro hpos
    have hmem : vertex ∈ List.finRange 8 := by simp
    have hfind : (List.finRange 8).find?
        (fun v => decide (0 < state.demand v)) ≠ none := by
      intro hnone
      have hall := List.find?_eq_none.mp hnone vertex hmem
      simp [hpos] at hall
    exact hfind hpivot
  omega

theorem transparentCompactPivot_some_pos
    {state : TransparentCompactColumnState} {pivot : Fin 8}
    (hpivot : transparentCompactColumnPivot state = some pivot) :
    0 < state.demand pivot := by
  have hfound := List.find?_some hpivot
  simpa [transparentCompactColumnPivot] using hfound

theorem nextTransparentCompactState_pivot_zero
    {items : List ℕ} {state : TransparentCompactColumnState} {goalMask : ℕ}
    (hcompletion : TransparentCompactCompletion items state goalMask)
    (pivot : Fin 8) :
    (nextTransparentCompactState state
      (transparentCompactSelected items state goalMask pivot)).demand pivot = 0 := by
  rw [nextTransparentCompactState]
  change state.demand pivot - _ = 0
  rw [transparentCompactBundleCount,
    transparentCompactSelected_toFinset, hcompletion.2.2 pivot]
  simp only [Finset.filter_filter]
  simp

theorem transparentPositiveDemands_next_lt
    {items : List ℕ} {state : TransparentCompactColumnState} {goalMask : ℕ}
    (hcompletion : TransparentCompactCompletion items state goalMask)
    (pivot : Fin 8) (hpivot : 0 < state.demand pivot) :
    (transparentPositiveDemands
      (nextTransparentCompactState state
        (transparentCompactSelected items state goalMask pivot))).card <
      (transparentPositiveDemands state).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff]
  refine ⟨pivot, ?_, ?_⟩
  · simp [transparentPositiveDemands,
      nextTransparentCompactState_pivot_zero hcompletion pivot]
  · rw [Finset.insert_subset_iff]
    constructor
    · simp [transparentPositiveDemands, hpivot]
    · intro vertex hvertex
      simp only [transparentPositiveDemands, Finset.mem_filter,
        Finset.mem_univ, true_and] at hvertex ⊢
      change 0 < state.demand vertex -
        transparentCompactBundleCount
          (transparentCompactSelected items state goalMask pivot) vertex at hvertex
      omega

theorem columnMask_eq_goal_of_completion_demands_zero
    {items : List ℕ} {state : TransparentCompactColumnState} {goalMask : ℕ}
    (hcompletion : TransparentCompactCompletion items state goalMask)
    (hzero : ∀ vertex, state.demand vertex = 0)
    (hcovered : ∀ code ∈ items, ∃ vertex : Fin 8,
      (compactTripleCodeAt code).testBit vertex.val = true) :
    state.columnMask = goalMask := by
  apply Nat.eq_of_testBit_eq
  intro code
  cases hgoal : goalMask.testBit code with
  | false =>
      have hstate : state.columnMask.testBit code = false := by
        cases hstate : state.columnMask.testBit code with
        | false => rfl
        | true =>
            have := hcompletion.1 code hstate
            rw [hgoal] at this
            contradiction
      exact hstate
  | true =>
      have hitem : code ∈ items := hcompletion.2.1 code hgoal
      have hstate : state.columnMask.testBit code = true := by
        cases hstate : state.columnMask.testBit code with
        | true => rfl
        | false =>
            have hremaining :
                code ∈ transparentCompactRemaining items state goalMask :=
              Finset.mem_filter.mpr ⟨by simpa using hitem, hgoal, hstate⟩
            obtain ⟨vertex, hvertex⟩ := hcovered code hitem
            have hpos : 0 <
                ((transparentCompactRemaining items state goalMask).filter fun entry =>
                  (compactTripleCodeAt entry).testBit vertex.val).card :=
              Finset.card_pos.mpr
                ⟨code, Finset.mem_filter.mpr ⟨hremaining, hvertex⟩⟩
            rw [← hcompletion.2.2 vertex, hzero vertex] at hpos
            omega
      exact hstate

theorem goal_mem_transparentCompactNearColumnAux
    (items : List ℕ) (hitems : items.Nodup)
    (hcovered : ∀ code ∈ items, ∃ vertex : Fin 8,
      (compactTripleCodeAt code).testBit vertex.val = true)
    {fuel : ℕ} {state : TransparentCompactColumnState} {goalMask : ℕ}
    (hcompletion : TransparentCompactCompletion items state goalMask)
    (hfuel : (transparentPositiveDemands state).card < fuel) :
    goalMask ∈ transparentCompactNearColumnAux items fuel state := by
  induction fuel generalizing state with
  | zero => simp at hfuel
  | succ fuel ih =>
      rw [transparentCompactNearColumnAux]
      cases hpivot : transparentCompactColumnPivot state with
      | none =>
          have hzero := transparentCompactPivot_none_demands_zero hpivot
          have heq := columnMask_eq_goal_of_completion_demands_zero
            hcompletion hzero hcovered
          simp [heq]
      | some pivot =>
          let selected := transparentCompactSelected items state goalMask pivot
          have hsub : List.Sublist selected
              (((items.filter fun code =>
                transparentCompactColumnCodeValid state code).filter fun code =>
                  (compactTripleCodeAt code).testBit pivot.val)) := by
            exact transparentCompactSelected_sublist_candidates hcompletion pivot
          have hlength : selected.length = state.demand pivot := by
            exact transparentCompactSelected_length hitems hcompletion pivot
          have hselected : selected ∈
              (((items.filter fun code =>
                transparentCompactColumnCodeValid state code).filter fun code =>
                  (compactTripleCodeAt code).testBit pivot.val).sublistsLen
                    (state.demand pivot)) :=
            List.mem_sublistsLen.mpr ⟨hsub, hlength⟩
          have hvalid : transparentCompactBundleValid state selected = true := by
            exact transparentCompactSelected_bundleValid hcompletion pivot
          have hnextCompletion : TransparentCompactCompletion items
              (nextTransparentCompactState state selected) goalMask := by
            exact transparentCompactCompletion_next hcompletion pivot
          have hpivotPos : 0 < state.demand pivot :=
            transparentCompactPivot_some_pos hpivot
          have hdecrease :
              (transparentPositiveDemands
                (nextTransparentCompactState state selected)).card <
                (transparentPositiveDemands state).card := by
            exact transparentPositiveDemands_next_lt hcompletion pivot hpivotPos
          have hnextFuel :
              (transparentPositiveDemands
                (nextTransparentCompactState state selected)).card < fuel := by
            omega
          apply List.mem_flatMap.mpr
          refine ⟨selected, hselected, ?_⟩
          rw [addTransparentCompactBundle?, hvalid]
          exact ih hnextCompletion hnextFuel

theorem isCompactNearColumn_mem_transparentShell
    {nearMask endpointMask columnMask : ℕ}
    (hcolumn : IsCompactNearColumn nearMask endpointMask columnMask) :
    columnMask ∈ transparentCompactNearColumnShell nearMask endpointMask := by
  rw [transparentCompactNearColumnShell]
  apply goal_mem_transparentCompactNearColumnAux
    (compactNearColumnItems nearMask endpointMask)
    (compactNearColumnItems_nodup nearMask endpointMask)
  · intro code hcode
    exact compactNearColumnItem_has_vertex hcode
  · exact transparentCompactCompletion_initial hcolumn
  · have hle := Finset.card_le_univ
        (s := transparentPositiveDemands
          ⟨0, transparentCompactColumnInitialDemand endpointMask⟩)
    change (transparentPositiveDemands
      ⟨0, transparentCompactColumnInitialDemand endpointMask⟩).card ≤ 8 at hle
    omega

/-- Public complete shell used by the compact fractional certificate matrix. -/
def compactNearColumnShell (nearMask endpointMask : ℕ) : List ℕ :=
  transparentCompactNearColumnShell nearMask endpointMask

/-- Every mathematically regular compact column occurs in the executable
exact-demand shell. -/
theorem isCompactNearColumn_mem_shell
    {nearMask endpointMask columnMask : ℕ}
    (hcolumn : IsCompactNearColumn nearMask endpointMask columnMask) :
    columnMask ∈ compactNearColumnShell nearMask endpointMask := by
  exact isCompactNearColumn_mem_transparentShell hcolumn

/-! ## Counting compiler -/

/-- Count exact-demand DFS leaves without constructing their column masks as
a list.  This is the scalar compiler used to certify range boundaries. -/
def transparentCompactNearColumnCountAux (items : List ℕ) :
    ℕ → TransparentCompactColumnState → ℕ
  | 0, _ => 0
  | fuel + 1, state =>
      let validItems := items.filter fun code =>
        transparentCompactColumnCodeValid state code
      match transparentCompactColumnPivot state with
      | none => 1
      | some pivot =>
          let need := state.demand pivot
          let candidates := validItems.filter fun code =>
            (compactTripleCodeAt code).testBit pivot.val
          (candidates.sublistsLen need).foldl (fun total bundle =>
            total + match addTransparentCompactBundle? state bundle with
              | none => 0
              | some next =>
                  transparentCompactNearColumnCountAux items fuel next) 0

private theorem transparentCountFoldl_eq_sumMap {α : Type*}
    (values : List α) (term : α → ℕ) (base : ℕ) :
    values.foldl (fun total value => total + term value) base =
      base + (values.map term).sum := by
  induction values generalizing base with
  | nil => simp
  | cons head tail ih =>
      rw [List.foldl_cons, ih]
      simp only [List.map_cons, List.sum_cons]
      omega

/-- The scalar counting compiler returns the length of the list-producing
compiler. -/
theorem transparentCompactNearColumnCountAux_eq_length (items : List ℕ) :
    ∀ (fuel : ℕ) (state : TransparentCompactColumnState),
      transparentCompactNearColumnCountAux items fuel state =
        (transparentCompactNearColumnAux items fuel state).length := by
  intro fuel
  induction fuel with
  | zero =>
      intro state
      rfl
  | succ fuel ih =>
      intro state
      rw [transparentCompactNearColumnCountAux,
        transparentCompactNearColumnAux]
      cases hpivot : transparentCompactColumnPivot state with
      | none => rfl
      | some pivot =>
          simp only
          rw [transparentCountFoldl_eq_sumMap, zero_add,
            List.length_flatMap]
          apply congrArg List.sum
          apply List.map_congr_left
          intro bundle _
          cases hnext : addTransparentCompactBundle? state bundle with
          | none => simp
          | some next => simpa [hnext] using ih next

/-- Number of exact-demand columns, computed without producing the shell. -/
def compactNearColumnShellCount (nearMask endpointMask : ℕ) : ℕ :=
  let items := compactNearColumnItems nearMask endpointMask
  transparentCompactNearColumnCountAux items 9
    ⟨0, transparentCompactColumnInitialDemand endpointMask⟩

theorem compactNearColumnShellCount_eq_length (nearMask endpointMask : ℕ) :
    compactNearColumnShellCount nearMask endpointMask =
      (compactNearColumnShell nearMask endpointMask).length := by
  exact transparentCompactNearColumnCountAux_eq_length
    (compactNearColumnItems nearMask endpointMask) 9
    ⟨0, transparentCompactColumnInitialDemand endpointMask⟩

/-! ## Predicate-pushed shell compiler -/

/-- Push a Boolean column predicate to the leaves of the exact-demand DFS.
Rejected leaves return `[]`, so the unfiltered shell is never materialized. -/
def transparentCompactNearColumnAuxWhere (selected : ℕ → Bool)
    (items : List ℕ) :
    ℕ → TransparentCompactColumnState → List ℕ
  | 0, _ => []
  | fuel + 1, state =>
      let validItems := items.filter fun code =>
        transparentCompactColumnCodeValid state code
      match transparentCompactColumnPivot state with
      | none => if selected state.columnMask then [state.columnMask] else []
      | some pivot =>
          let need := state.demand pivot
          let candidates := validItems.filter fun code =>
            (compactTripleCodeAt code).testBit pivot.val
          (candidates.sublistsLen need).flatMap fun bundle =>
            match addTransparentCompactBundle? state bundle with
            | none => []
            | some next =>
                transparentCompactNearColumnAuxWhere selected items fuel next

/-- Pushing the predicate to DFS leaves is extensionally the same as filtering
the list-producing search. -/
theorem transparentCompactNearColumnAuxWhere_eq_filter
    (selected : ℕ → Bool) (items : List ℕ) :
    ∀ (fuel : ℕ) (state : TransparentCompactColumnState),
      transparentCompactNearColumnAuxWhere selected items fuel state =
        (transparentCompactNearColumnAux items fuel state).filter selected := by
  intro fuel
  induction fuel with
  | zero =>
      intro state
      rfl
  | succ fuel ih =>
      intro state
      rw [transparentCompactNearColumnAuxWhere,
        transparentCompactNearColumnAux]
      cases hpivot : transparentCompactColumnPivot state with
      | none =>
          simp only
          cases hselected : selected state.columnMask <;>
            simp [hselected]
      | some pivot =>
          simp only
          rw [List.filter_flatMap]
          apply List.flatMap_congr
          intro bundle _
          cases hnext : addTransparentCompactBundle? state bundle with
          | none => simp
          | some next => simpa [hnext] using ih next

/-- Exact-demand shell with a leaf predicate pushed into the compiler. -/
def compactNearColumnShellWhere (nearMask endpointMask : ℕ)
    (selected : ℕ → Bool) : List ℕ :=
  let items := compactNearColumnItems nearMask endpointMask
  transparentCompactNearColumnAuxWhere selected items 9
    ⟨0, transparentCompactColumnInitialDemand endpointMask⟩

theorem compactNearColumnShellWhere_eq_filter (nearMask endpointMask : ℕ)
    (selected : ℕ → Bool) :
    compactNearColumnShellWhere nearMask endpointMask selected =
      (compactNearColumnShell nearMask endpointMask).filter selected := by
  exact transparentCompactNearColumnAuxWhere_eq_filter selected
    (compactNearColumnItems nearMask endpointMask) 9
    ⟨0, transparentCompactColumnInitialDemand endpointMask⟩

/-! ## Reverse-order shell compiler -/

/-- Traverse every DFS bundle list backwards and recursively emit each branch
backwards.  This computes the reverse shell without first constructing the
forward shell. -/
def transparentCompactNearColumnAuxReverse (items : List ℕ) :
    ℕ → TransparentCompactColumnState → List ℕ
  | 0, _ => []
  | fuel + 1, state =>
      let validItems := items.filter fun code =>
        transparentCompactColumnCodeValid state code
      match transparentCompactColumnPivot state with
      | none => [state.columnMask]
      | some pivot =>
          let need := state.demand pivot
          let candidates := validItems.filter fun code =>
            (compactTripleCodeAt code).testBit pivot.val
          (candidates.sublistsLen need).reverse.flatMap fun bundle =>
            match addTransparentCompactBundle? state bundle with
            | none => []
            | some next =>
                transparentCompactNearColumnAuxReverse items fuel next

/-- The reverse-order compiler returns exactly the reverse of the original
list-producing DFS. -/
theorem transparentCompactNearColumnAuxReverse_eq_reverse (items : List ℕ) :
    ∀ (fuel : ℕ) (state : TransparentCompactColumnState),
      transparentCompactNearColumnAuxReverse items fuel state =
        (transparentCompactNearColumnAux items fuel state).reverse := by
  intro fuel
  induction fuel with
  | zero =>
      intro state
      rfl
  | succ fuel ih =>
      intro state
      rw [transparentCompactNearColumnAuxReverse,
        transparentCompactNearColumnAux]
      cases hpivot : transparentCompactColumnPivot state with
      | none => rfl
      | some pivot =>
          simp only
          rw [List.reverse_flatMap]
          apply List.flatMap_congr
          intro bundle _
          cases hnext : addTransparentCompactBundle? state bundle with
          | none => simp [hnext]
          | some next => simpa [Function.comp_def, hnext] using ih next

/-- Exact-demand shell in reverse enumeration order. -/
def compactNearColumnShellReverse (nearMask endpointMask : ℕ) : List ℕ :=
  let items := compactNearColumnItems nearMask endpointMask
  transparentCompactNearColumnAuxReverse items 9
    ⟨0, transparentCompactColumnInitialDemand endpointMask⟩

theorem compactNearColumnShellReverse_eq_reverse (nearMask endpointMask : ℕ) :
    compactNearColumnShellReverse nearMask endpointMask =
      (compactNearColumnShell nearMask endpointMask).reverse := by
  exact transparentCompactNearColumnAuxReverse_eq_reverse
    (compactNearColumnItems nearMask endpointMask) 9
    ⟨0, transparentCompactColumnInitialDemand endpointMask⟩

/-! ## Short-circuit compiler for the first enumerated column -/

private def transparentFirstSome {α β : Type*} :
    List α → (α → Option β) → Option β
  | [], _ => none
  | item :: items, branch =>
      match branch item with
      | some result => some result
      | none => transparentFirstSome items branch

private theorem head?_flatMap_eq_transparentFirstSome {α β : Type*}
    (branch : α → List β) : ∀ items : List α,
    (items.flatMap branch).head? =
      transparentFirstSome items fun item => (branch item).head? := by
  intro items
  induction items with
  | nil => rfl
  | cons item items ih =>
      cases hbranch : branch item <;>
        simp [transparentFirstSome, hbranch, ih]

/-- Execute only the first successful branch of the exact-demand DFS. -/
def transparentCompactNearColumnFirstAux (items : List ℕ) :
    ℕ → TransparentCompactColumnState → Option ℕ
  | 0, _ => none
  | fuel + 1, state =>
      let validItems := items.filter fun code =>
        transparentCompactColumnCodeValid state code
      match transparentCompactColumnPivot state with
      | none => some state.columnMask
      | some pivot =>
          let need := state.demand pivot
          let candidates := validItems.filter fun code =>
            (compactTripleCodeAt code).testBit pivot.val
          transparentFirstSome (candidates.sublistsLen need) fun selected =>
            match addTransparentCompactBundle? state selected with
            | none => none
            | some next => transparentCompactNearColumnFirstAux items fuel next

/-- The short-circuit compiler preserves the head of the list-producing
search. -/
theorem transparentCompactNearColumnAux_head? (items : List ℕ) :
    ∀ (fuel : ℕ) (state : TransparentCompactColumnState),
      (transparentCompactNearColumnAux items fuel state).head? =
        transparentCompactNearColumnFirstAux items fuel state := by
  intro fuel
  induction fuel with
  | zero =>
      intro state
      rfl
  | succ fuel ih =>
      intro state
      rw [transparentCompactNearColumnAux,
        transparentCompactNearColumnFirstAux]
      cases hpivot : transparentCompactColumnPivot state with
      | none => rfl
      | some pivot =>
          simp only
          rw [head?_flatMap_eq_transparentFirstSome]
          apply congrArg (transparentFirstSome _)
          funext selected
          cases hnext : addTransparentCompactBundle? state selected with
          | none => rfl
          | some next => exact ih next

/-- First exact-demand column without materializing the complete shell. -/
def compactNearColumnFirst? (nearMask endpointMask : ℕ) : Option ℕ :=
  let items := compactNearColumnItems nearMask endpointMask
  transparentCompactNearColumnFirstAux items 9
    ⟨0, transparentCompactColumnInitialDemand endpointMask⟩

theorem compactNearColumnFirst?_eq_head? (nearMask endpointMask : ℕ) :
    compactNearColumnFirst? nearMask endpointMask =
      (compactNearColumnShell nearMask endpointMask).head? := by
  exact (transparentCompactNearColumnAux_head?
    (compactNearColumnItems nearMask endpointMask) 9
    ⟨0, transparentCompactColumnInitialDemand endpointMask⟩).symm

end SRG266.QuasiSymmetric
