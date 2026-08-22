/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.FractionalNearFrameShellArgmin

/-!
# Subtree-split lower bounds for exact-demand shell minima

`transparentCompactNearColumnMinimumAux` fuses the exact-demand shell search
with minimization.  Reducing one whole call of it in the kernel materializes
the reduction trace of the entire search, which is the memory bottleneck of a
kernel-only Farkas replay.

This module splits that obligation along the DFS itself.  A *subtree bound*
records that every value one sub-search can return is at least `L`.  The join
lemma `subtreeBounded_of_children` shows that a node inherits the bound from
its children, so the children of the root can be proved separately and then
assembled. The only data are the integer bound `L` and subtree indices.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SRG266.QuasiSymmetric

/-! ## Optional minima bounded from below -/

private theorem compactMinimumOption_ge {L : ℤ} {left right : Option ℤ}
    (hleft : ∀ r, left = some r → L ≤ r)
    (hright : ∀ r, right = some r → L ≤ r) :
    ∀ r, compactMinimumOption left right = some r → L ≤ r := by
  cases left with
  | none =>
      cases right with
      | none => intro r hr; simp [compactMinimumOption] at hr
      | some y =>
          intro r hr
          simp only [compactMinimumOption, Option.some.injEq] at hr
          subst hr
          exact hright y rfl
  | some x =>
      cases right with
      | none =>
          intro r hr
          simp only [compactMinimumOption, Option.some.injEq] at hr
          subst hr
          exact hleft x rfl
      | some y =>
          intro r hr
          simp only [compactMinimumOption, Option.some.injEq] at hr
          subst hr
          exact le_min (hleft x rfl) (hright y rfl)

private theorem foldl_compactMinimumOption_ge {α : Type*}
    (branch : α → Option ℤ) (L : ℤ) :
    ∀ (items : List α) (accumulator : Option ℤ),
      (∀ r, accumulator = some r → L ≤ r) →
      (∀ item ∈ items, ∀ r, branch item = some r → L ≤ r) →
      ∀ r, items.foldl (fun current item =>
        compactMinimumOption current (branch item)) accumulator = some r → L ≤ r := by
  intro items
  induction items with
  | nil =>
      intro accumulator haccumulator _ r hr
      exact haccumulator r (by simpa using hr)
  | cons head tail ih =>
      intro accumulator haccumulator hbranch r hr
      rw [List.foldl_cons] at hr
      refine ih _ ?_ (fun item hitem => hbranch item (List.mem_cons_of_mem _ hitem)) r hr
      exact compactMinimumOption_ge haccumulator
        (hbranch head (by simp))

/-! ## Subtree bounds -/

/-- Every value the sub-search rooted at `state` can return is at least `L`. -/
def SubtreeBoundedBy (value : ℕ → ℤ) (items : List ℕ) (fuel : ℕ)
    (state : TransparentCompactColumnState) (L : ℤ) : Prop :=
  ∀ result,
    transparentCompactNearColumnMinimumAux value items fuel state = some result →
      L ≤ result

/-- Decidable audit implying one subtree bound.  An exhausted sub-search
returns `none` and is vacuously bounded. -/
def subtreeBoundAudit (value : ℕ → ℤ) (items : List ℕ) (fuel : ℕ)
    (state : TransparentCompactColumnState) (L : ℤ) : Bool :=
  match transparentCompactNearColumnMinimumAux value items fuel state with
  | none => true
  | some result => decide (L ≤ result)

theorem subtreeBoundedBy_of_audit (value : ℕ → ℤ) (items : List ℕ) (fuel : ℕ)
    (state : TransparentCompactColumnState) (L : ℤ)
    (haudit : subtreeBoundAudit value items fuel state L = true) :
    SubtreeBoundedBy value items fuel state L := by
  intro result hresult
  simp only [subtreeBoundAudit, hresult, decide_eq_true_eq] at haudit
  exact haudit

/-- Exhausted fuel bounds vacuously. -/
theorem subtreeBoundedBy_zero (value : ℕ → ℤ) (items : List ℕ)
    (state : TransparentCompactColumnState) (L : ℤ) :
    SubtreeBoundedBy value items 0 state L := by
  intro result hresult
  simp [transparentCompactNearColumnMinimumAux] at hresult

/-! ## The children of one search node -/

/-- The states the exact-demand search descends into from `state`.  This is
read off the definition of `transparentCompactNearColumnMinimumAux`: the
available items are filtered for code validity, then for incidence with the
first unsatisfied pivot vertex, and every sub-multiset of the pivot's exact
remaining demand which keeps all eight degrees feasible yields one child. -/
def subtreeChildren (items : List ℕ) (state : TransparentCompactColumnState) :
    List TransparentCompactColumnState :=
  match transparentCompactColumnPivot state with
  | none => []
  | some pivot =>
      (((items.filter fun code => transparentCompactColumnCodeValid state code).filter
          fun code => (compactTripleCodeAt code).testBit pivot.val).sublistsLen
        (state.demand pivot)).filterMap (addTransparentCompactBundle? state)

/-- **Join lemma.**  A node inherits a lower bound from its children.  The
leaf hypothesis covers the case where the node itself is a completed column,
which has no children but does contribute its own value. -/
theorem subtreeBounded_of_children (value : ℕ → ℤ) (items : List ℕ) (fuel : ℕ)
    (state : TransparentCompactColumnState) (L : ℤ)
    (hleaf : transparentCompactColumnPivot state = none → L ≤ value state.columnMask)
    (hchildren : ∀ child ∈ subtreeChildren items state,
      SubtreeBoundedBy value items fuel child L) :
    SubtreeBoundedBy value items (fuel + 1) state L := by
  intro result hresult
  simp only [transparentCompactNearColumnMinimumAux] at hresult
  cases hpivot : transparentCompactColumnPivot state with
  | none =>
      rw [hpivot] at hresult
      have heq : value state.columnMask = result := by simpa using hresult
      rw [← heq]
      exact hleaf hpivot
  | some pivot =>
      rw [hpivot] at hresult
      have hraw :
          (((items.filter fun code => transparentCompactColumnCodeValid state code).filter
              fun code => (compactTripleCodeAt code).testBit pivot.val).sublistsLen
            (state.demand pivot)).foldl
            (fun current selected =>
              match addTransparentCompactBundle? state selected with
              | none => current
              | some next => compactMinimumOption current
                  (transparentCompactNearColumnMinimumAux value items fuel next)) none
            = some result := hresult
      have hstep :
          (fun (current : Option ℤ) (selected : List ℕ) =>
            match addTransparentCompactBundle? state selected with
            | none => current
            | some next => compactMinimumOption current
                (transparentCompactNearColumnMinimumAux value items fuel next)) =
          (fun (current : Option ℤ) (selected : List ℕ) =>
            compactMinimumOption current
              (match addTransparentCompactBundle? state selected with
               | none => none
               | some next =>
                   transparentCompactNearColumnMinimumAux value items fuel next)) := by
        funext current selected
        cases addTransparentCompactBundle? state selected <;>
          cases current <;> simp [compactMinimumOption]
      rw [hstep] at hraw
      refine foldl_compactMinimumOption_ge _ L _ none (by simp) ?_ result hraw
      intro selected hselected r hr
      cases hnext : addTransparentCompactBundle? state selected with
      | none => rw [hnext] at hr; simp at hr
      | some next =>
          have hmember : next ∈ subtreeChildren items state := by
            rw [subtreeChildren, hpivot]
            exact List.mem_filterMap.mpr ⟨selected, hselected, hnext⟩
          refine hchildren next hmember r ?_
          rw [hnext] at hr
          exact hr

/-- Join lemma at a node which is known not to be a completed column. -/
theorem subtreeBounded_of_children_of_pivot (value : ℕ → ℤ) (items : List ℕ)
    (fuel : ℕ) (state : TransparentCompactColumnState) (L : ℤ) (pivot : Fin 8)
    (hpivot : transparentCompactColumnPivot state = some pivot)
    (hchildren : ∀ child ∈ subtreeChildren items state,
      SubtreeBoundedBy value items fuel child L) :
    SubtreeBoundedBy value items (fuel + 1) state L :=
  subtreeBounded_of_children value items fuel state L
    (fun hnone => absurd (hpivot.symm.trans hnone) (by simp)) hchildren

/-! ## The search does return a value whenever the shell is inhabited -/

private theorem foldl_compactMinimumOption_isSome_base {α : Type*}
    (branch : α → Option ℤ) :
    ∀ (items : List α) (base : ℤ),
      ∃ result, items.foldl (fun current item =>
        compactMinimumOption current (branch item)) (some base) = some result := by
  intro items
  induction items with
  | nil => intro base; exact ⟨base, rfl⟩
  | cons head tail ih =>
      intro base
      rw [List.foldl_cons]
      cases hhead : branch head with
      | none => simpa [compactMinimumOption, hhead] using ih base
      | some x => simpa [compactMinimumOption, hhead] using ih (min base x)

private theorem foldl_compactMinimumOption_isSome_of_mem {α : Type*}
    (branch : α → Option ℤ) :
    ∀ (items : List α) (accumulator : Option ℤ) (item : α), item ∈ items →
      ∀ v, branch item = some v →
      ∃ result, items.foldl (fun current x =>
        compactMinimumOption current (branch x)) accumulator = some result := by
  intro items
  induction items with
  | nil => intro _ _ hitem; simp at hitem
  | cons head tail ih =>
      intro accumulator item hitem v hvalue
      rw [List.foldl_cons]
      rcases List.eq_or_mem_of_mem_cons hitem with rfl | htail
      · cases accumulator with
        | none =>
            simpa [compactMinimumOption, hvalue] using
              foldl_compactMinimumOption_isSome_base branch tail v
        | some base =>
            simpa [compactMinimumOption, hvalue] using
              foldl_compactMinimumOption_isSome_base branch tail (min base v)
      · exact ih _ item htail v hvalue

/-- Whenever the exact-demand search enumerates at least one column, its fused
minimizing form returns a value. -/
theorem transparentCompactNearColumnMinimumAux_isSome_of_mem
    (value : ℕ → ℤ) (items : List ℕ) :
    ∀ (fuel : ℕ) (state : TransparentCompactColumnState) {columnMask : ℕ},
      columnMask ∈ transparentCompactNearColumnAux items fuel state →
      ∃ result,
        transparentCompactNearColumnMinimumAux value items fuel state = some result := by
  intro fuel
  induction fuel with
  | zero =>
      intro state columnMask hmember
      simp [transparentCompactNearColumnAux] at hmember
  | succ fuel ih =>
      intro state columnMask hmember
      simp only [transparentCompactNearColumnAux] at hmember
      simp only [transparentCompactNearColumnMinimumAux]
      cases hpivot : transparentCompactColumnPivot state with
      | none => exact ⟨value state.columnMask, rfl⟩
      | some pivot =>
          rw [hpivot] at hmember
          have hflat : columnMask ∈
              (((items.filter fun code =>
                    transparentCompactColumnCodeValid state code).filter
                  fun code => (compactTripleCodeAt code).testBit pivot.val).sublistsLen
                (state.demand pivot)).flatMap
                (fun selected =>
                  match addTransparentCompactBundle? state selected with
                  | none => []
                  | some next => transparentCompactNearColumnAux items fuel next) :=
            hmember
          rcases List.mem_flatMap.mp hflat with ⟨selected, hselected, hbranch⟩
          cases hnext : addTransparentCompactBundle? state selected with
          | none => rw [hnext] at hbranch; simp at hbranch
          | some next =>
              rw [hnext] at hbranch
              rcases ih next (columnMask := columnMask) hbranch with
                ⟨branchResult, hbranchResult⟩
              have hstep :
                  (fun (current : Option ℤ) (selected : List ℕ) =>
                    match addTransparentCompactBundle? state selected with
                    | none => current
                    | some next => compactMinimumOption current
                        (transparentCompactNearColumnMinimumAux value items fuel next)) =
                  (fun (current : Option ℤ) (selected : List ℕ) =>
                    compactMinimumOption current
                      (match addTransparentCompactBundle? state selected with
                       | none => none
                       | some next =>
                           transparentCompactNearColumnMinimumAux value items fuel next)) := by
                funext current selected
                cases addTransparentCompactBundle? state selected <;>
                  cases current <;> simp [compactMinimumOption]
              have key : ∃ result,
                  (((items.filter fun code =>
                        transparentCompactColumnCodeValid state code).filter
                      fun code =>
                        (compactTripleCodeAt code).testBit pivot.val).sublistsLen
                    (state.demand pivot)).foldl
                    (fun current selected =>
                      match addTransparentCompactBundle? state selected with
                      | none => current
                      | some next => compactMinimumOption current
                          (transparentCompactNearColumnMinimumAux value items fuel next))
                    none = some result := by
                rw [hstep]
                refine foldl_compactMinimumOption_isSome_of_mem _ _ none selected
                  hselected branchResult ?_
                rw [hnext]
                exact hbranchResult
              exact key

/-! ## Bridge to the certificate interface -/

/-- A subtree bound at the root of an endpoint shell bounds the functional on
every enumerated column of that shell. -/
theorem le_value_of_subtreeBounded_of_mem_shell
    (nearMask endpointMask : ℕ) (value : ℕ → ℤ) (L : ℤ)
    (hbound : SubtreeBoundedBy value (compactNearColumnItems nearMask endpointMask) 9
      ⟨0, transparentCompactColumnInitialDemand endpointMask⟩ L)
    {columnMask : ℕ}
    (hmember : columnMask ∈ compactNearColumnShell nearMask endpointMask) :
    L ≤ value columnMask := by
  have hraw : columnMask ∈ transparentCompactNearColumnAux
      (compactNearColumnItems nearMask endpointMask) 9
      ⟨0, transparentCompactColumnInitialDemand endpointMask⟩ := by
    rw [compactNearColumnShell, transparentCompactNearColumnShell] at hmember
    exact hmember
  rcases transparentCompactNearColumnMinimumAux_isSome_of_mem value
      (compactNearColumnItems nearMask endpointMask) 9 _ hraw with ⟨result, hresult⟩
  have hminimum : compactNearColumnMinimum nearMask endpointMask value = result := by
    rw [compactNearColumnMinimum, hresult]; rfl
  have hle : compactNearColumnMinimum nearMask endpointMask value ≤ value columnMask :=
    compactNearColumnMinimum_le_of_mem nearMask endpointMask value hmember
  rw [hminimum] at hle
  exact le_trans (hbound result hresult) hle

/-- A subtree bound at the root bounds the recorded shell minimum, provided the
shell is inhabited.  `compactNearColumnMinimum` reports `0` on an exhausted
search, so this hypothesis cannot be dropped. -/
theorem compactNearColumnMinimum_ge_of_subtreeBounded_of_mem
    (nearMask endpointMask : ℕ) (value : ℕ → ℤ) (L : ℤ)
    (hbound : SubtreeBoundedBy value (compactNearColumnItems nearMask endpointMask) 9
      ⟨0, transparentCompactColumnInitialDemand endpointMask⟩ L)
    {columnMask : ℕ}
    (hmember : columnMask ∈ compactNearColumnShell nearMask endpointMask) :
    L ≤ compactNearColumnMinimum nearMask endpointMask value := by
  have hraw : columnMask ∈ transparentCompactNearColumnAux
      (compactNearColumnItems nearMask endpointMask) 9
      ⟨0, transparentCompactColumnInitialDemand endpointMask⟩ := by
    rw [compactNearColumnShell, transparentCompactNearColumnShell] at hmember
    exact hmember
  rcases transparentCompactNearColumnMinimumAux_isSome_of_mem value
      (compactNearColumnItems nearMask endpointMask) 9 _ hraw with ⟨result, hresult⟩
  have hminimum : compactNearColumnMinimum nearMask endpointMask value = result := by
    rw [compactNearColumnMinimum, hresult]; rfl
  rw [hminimum]
  exact hbound result hresult

/-- Unconditional form: on an exhausted shell the recorded minimum is `0`, so a
nonpositive bound survives. -/
theorem compactNearColumnMinimum_ge_of_subtreeBounded
    (nearMask endpointMask : ℕ) (value : ℕ → ℤ) (L : ℤ)
    (hbound : SubtreeBoundedBy value (compactNearColumnItems nearMask endpointMask) 9
      ⟨0, transparentCompactColumnInitialDemand endpointMask⟩ L)
    (hempty : L ≤ 0) :
    L ≤ compactNearColumnMinimum nearMask endpointMask value := by
  rw [compactNearColumnMinimum]
  cases hresult : transparentCompactNearColumnMinimumAux value
      (compactNearColumnItems nearMask endpointMask) 9
      ⟨0, transparentCompactColumnInitialDemand endpointMask⟩ with
  | none => simpa using hempty
  | some result => simpa using hbound result hresult

/-- A subtree bound at the root of an endpoint shell is exactly the shell lower
bound consumed by `noCompactFractionalNearFrame_of_indexedShellLowerBounds`. -/
theorem isCompactIndexedPairShellLowerBound_of_subtreeBounded
    (nearMask : ℕ) (witness : Array ℤ)
    (endpoint : CompactEndpointIndex nearMask) (L : ℤ)
    (hbound : SubtreeBoundedBy (compactKernelIndexedPairWeightSum nearMask witness)
      (compactNearColumnItems nearMask (compactEndpointMaskAt nearMask endpoint)) 9
      ⟨0, transparentCompactColumnInitialDemand
        (compactEndpointMaskAt nearMask endpoint)⟩ L) :
    IsCompactIndexedPairShellLowerBound nearMask witness endpoint L := by
  intro column hcolumn
  exact le_value_of_subtreeBounded_of_mem_shell nearMask
    (compactEndpointMaskAt nearMask endpoint)
    (compactKernelIndexedPairWeightSum nearMask witness) L hbound
    (isCompactNearColumn_mem_shell hcolumn)

/-! ## Chunked child audits -/

/-- Every listed child state carries the subtree bound. -/
def ChildrenBoundedOn (value : ℕ → ℤ) (items : List ℕ) (fuel : ℕ) (L : ℤ)
    (children : List TransparentCompactColumnState) : Prop :=
  ∀ child ∈ children, SubtreeBoundedBy value items fuel child L

/-- Audit one contiguous block of the children of `state`. -/
def childrenChunkAudit (value : ℕ → ℤ) (items : List ℕ) (fuel : ℕ)
    (state : TransparentCompactColumnState) (L : ℤ) (lo len : ℕ) : Bool :=
  (((subtreeChildren items state).drop lo).take len).all fun child =>
    subtreeBoundAudit value items fuel child L

theorem childrenBoundedOn_of_chunkAudit (value : ℕ → ℤ) (items : List ℕ)
    (fuel : ℕ) (state : TransparentCompactColumnState) (L : ℤ) (lo len : ℕ)
    (haudit : childrenChunkAudit value items fuel state L lo len = true) :
    ChildrenBoundedOn value items fuel L
      (((subtreeChildren items state).drop lo).take len) := by
  rw [childrenChunkAudit, List.all_eq_true] at haudit
  intro child hchild
  exact subtreeBoundedBy_of_audit value items fuel child L (haudit child hchild)

theorem childrenBoundedOn_append (value : ℕ → ℤ) (items : List ℕ) (fuel : ℕ)
    (L : ℤ) (left right : List TransparentCompactColumnState) :
    ChildrenBoundedOn value items fuel L (left ++ right) ↔
      ChildrenBoundedOn value items fuel L left ∧
        ChildrenBoundedOn value items fuel L right := by
  constructor
  · intro hbound
    exact ⟨fun child hchild => hbound child (List.mem_append_left right hchild),
      fun child hchild => hbound child (List.mem_append_right left hchild)⟩
  · rintro ⟨hleft, hright⟩ child hchild
    rcases List.mem_append.mp hchild with hchild | hchild
    · exact hleft child hchild
    · exact hright child hchild

/-- Join two independently audited adjacent blocks. -/
theorem childrenBoundedOn_of_adjacent_ranges (value : ℕ → ℤ) (items : List ℕ)
    (fuel : ℕ) (L : ℤ) (children : List TransparentCompactColumnState)
    (start leftLength rightLength : ℕ)
    (hleft : ChildrenBoundedOn value items fuel L
      ((children.drop start).take leftLength))
    (hright : ChildrenBoundedOn value items fuel L
      ((children.drop (start + leftLength)).take rightLength)) :
    ChildrenBoundedOn value items fuel L
      ((children.drop start).take (leftLength + rightLength)) := by
  rw [List.take_add]
  apply (childrenBoundedOn_append _ _ _ _ _ _).mpr
  exact ⟨hleft, by simpa [List.drop_drop] using hright⟩

/-- A block covering the whole child list bounds every child. -/
theorem childrenBoundedOn_of_full_range (value : ℕ → ℤ) (items : List ℕ)
    (fuel : ℕ) (L : ℤ) (children : List TransparentCompactColumnState) (len : ℕ)
    (hlen : children.length ≤ len)
    (hbound : ChildrenBoundedOn value items fuel L ((children.drop 0).take len)) :
    ChildrenBoundedOn value items fuel L children := by
  simpa [List.take_of_length_le hlen] using hbound

/-- Final assembly: audited children of a non-leaf node give the node bound. -/
theorem subtreeBounded_of_childrenBoundedOn (value : ℕ → ℤ) (items : List ℕ)
    (fuel : ℕ) (state : TransparentCompactColumnState) (L : ℤ) (pivot : Fin 8)
    (hpivot : transparentCompactColumnPivot state = some pivot)
    (hchildren : ChildrenBoundedOn value items fuel L (subtreeChildren items state)) :
    SubtreeBoundedBy value items (fuel + 1) state L :=
  subtreeBounded_of_children_of_pivot value items fuel state L pivot hpivot hchildren

/-! ## Endpoint-shell specialization

The generated per-representative modules speak about one endpoint of one near
mask rather than about an abstract search state.  These wrappers fix the
objective, the item list and the initial state from `nearMask` and `endpoint`,
so a generated module never has to spell out a search state. -/

/-- The item list of one endpoint shell. -/
def compactShellItems (nearMask : ℕ) (endpoint : CompactEndpointIndex nearMask) :
    List ℕ :=
  compactNearColumnItems nearMask (compactEndpointMaskAt nearMask endpoint)

/-- The root search state of one endpoint shell. -/
def compactShellRootState (nearMask : ℕ) (endpoint : CompactEndpointIndex nearMask) :
    TransparentCompactColumnState :=
  ⟨0, transparentCompactColumnInitialDemand (compactEndpointMaskAt nearMask endpoint)⟩

/-- Root children of one endpoint shell's exact-demand search, in the order
produced by `sublistsLen` at the root.  Chunk boundaries in a generated module
are `List.take`/`List.drop` indices into this list. -/
def compactShellRootChildren (nearMask : ℕ) (endpoint : CompactEndpointIndex nearMask) :
    List TransparentCompactColumnState :=
  subtreeChildren (compactShellItems nearMask endpoint)
    (compactShellRootState nearMask endpoint)

/-- The root of an endpoint shell branches rather than being a completed
column.  Checked once per endpoint by ordinary kernel reduction. -/
def compactShellRootBranches (nearMask : ℕ) (endpoint : CompactEndpointIndex nearMask) :
    Bool :=
  (transparentCompactColumnPivot (compactShellRootState nearMask endpoint)).isSome

/-- `bound` is below the objective of every column reachable from any listed
root child. -/
def CompactShellSubtreeLowerBoundOn (nearMask : ℕ) (witness : Array ℤ)
    (endpoint : CompactEndpointIndex nearMask)
    (children : List TransparentCompactColumnState) (bound : ℤ) : Prop :=
  ChildrenBoundedOn (compactKernelIndexedPairWeightSum nearMask witness)
    (compactShellItems nearMask endpoint) 8 bound children

/-- One shard: the window `[lo, lo + len)` of the root children. -/
def compactShellSubtreeChunkAudit (nearMask : ℕ) (witness : Array ℤ)
    (endpoint : CompactEndpointIndex nearMask) (bound : ℤ) (lo len : ℕ) : Bool :=
  childrenChunkAudit (compactKernelIndexedPairWeightSum nearMask witness)
    (compactShellItems nearMask endpoint) 8
    (compactShellRootState nearMask endpoint) bound lo len

theorem compactShellSubtreeLowerBoundOn_of_audit (nearMask : ℕ) (witness : Array ℤ)
    (endpoint : CompactEndpointIndex nearMask) (bound : ℤ) (lo len : ℕ)
    (haudit : compactShellSubtreeChunkAudit nearMask witness endpoint bound lo len = true) :
    CompactShellSubtreeLowerBoundOn nearMask witness endpoint
      (((compactShellRootChildren nearMask endpoint).drop lo).take len) bound :=
  childrenBoundedOn_of_chunkAudit _ _ _ _ _ lo len haudit

/-- Join two independently audited adjacent shards. -/
theorem compactShellSubtreeLowerBoundOn_of_take_drop (nearMask : ℕ) (witness : Array ℤ)
    (endpoint : CompactEndpointIndex nearMask) (bound : ℤ)
    (start leftLength rightLength : ℕ)
    (hleft : CompactShellSubtreeLowerBoundOn nearMask witness endpoint
      (((compactShellRootChildren nearMask endpoint).drop start).take leftLength) bound)
    (hright : CompactShellSubtreeLowerBoundOn nearMask witness endpoint
      (((compactShellRootChildren nearMask endpoint).drop (start + leftLength)).take
        rightLength) bound) :
    CompactShellSubtreeLowerBoundOn nearMask witness endpoint
      (((compactShellRootChildren nearMask endpoint).drop start).take
        (leftLength + rightLength)) bound :=
  childrenBoundedOn_of_adjacent_ranges _ _ _ _ _ start leftLength rightLength hleft hright

/-- A shard list covering every root child yields the shell lower bound that
`noCompactFractionalNearFrame_of_indexedShellLowerBounds` consumes. -/
theorem isCompactIndexedPairShellLowerBound_of_rootChildren (nearMask : ℕ)
    (witness : Array ℤ) (endpoint : CompactEndpointIndex nearMask) (bound : ℤ)
    (len : ℕ) (hlen : (compactShellRootChildren nearMask endpoint).length ≤ len)
    (hbranch : compactShellRootBranches nearMask endpoint = true)
    (hchildren : CompactShellSubtreeLowerBoundOn nearMask witness endpoint
      (((compactShellRootChildren nearMask endpoint).drop 0).take len) bound) :
    IsCompactIndexedPairShellLowerBound nearMask witness endpoint bound := by
  obtain ⟨pivot, hpivot⟩ :=
    Option.isSome_iff_exists.mp (by simpa [compactShellRootBranches] using hbranch)
  refine isCompactIndexedPairShellLowerBound_of_subtreeBounded nearMask witness
    endpoint bound ?_
  have hall : ChildrenBoundedOn (compactKernelIndexedPairWeightSum nearMask witness)
      (compactShellItems nearMask endpoint) 8 bound
      (compactShellRootChildren nearMask endpoint) :=
    childrenBoundedOn_of_full_range _ _ _ _ _ len hlen hchildren
  exact subtreeBounded_of_childrenBoundedOn _ _ _ _ _ pivot hpivot hall


/-- The exact minimum of an endpoint shell is a lower bound. -/
theorem isCompactIndexedPairShellLowerBound_of_minimum (nearMask : ℕ)
    (witness : Array ℤ) (endpoint : CompactEndpointIndex nearMask) (bound : ℤ)
    (hle : bound ≤ compactIndexedEndpointPairMinimum nearMask witness endpoint) :
    IsCompactIndexedPairShellLowerBound nearMask witness endpoint bound := by
  intro column hcolumn
  refine hle.trans ?_
  exact compactNearColumnMinimum_le_of_mem nearMask
    (compactEndpointMaskAt nearMask endpoint)
    (compactKernelIndexedPairWeightSum nearMask witness)
    (isCompactNearColumn_mem_shell hcolumn)


/-- One audit for every endpoint but the first, sharing the endpoint mask and
item lists in a single Boolean reduction. -/
def compactTailEndpointBoundsAudit (nearMask : ℕ) (witness : Array ℤ)
    (table : List ℤ) : Bool :=
  (List.ofFn fun endpoint : CompactEndpointIndex nearMask => endpoint).all
    fun endpoint =>
      endpoint.val == 0 ||
        decide (table.getD endpoint.val 0 ≤
          compactIndexedEndpointPairMinimum nearMask witness endpoint)

theorem isCompactIndexedPairShellLowerBound_of_tailAudit (nearMask : ℕ)
    (witness : Array ℤ) (table : List ℤ)
    (haudit : compactTailEndpointBoundsAudit nearMask witness table = true)
    (endpoint : CompactEndpointIndex nearMask) (hendpoint : endpoint.val ≠ 0) :
    IsCompactIndexedPairShellLowerBound nearMask witness endpoint
      (table.getD endpoint.val 0) := by
  rw [compactTailEndpointBoundsAudit, List.all_eq_true] at haudit
  have hmem : endpoint ∈
      (List.ofFn fun endpoint : CompactEndpointIndex nearMask => endpoint) := by
    simp
  have hentry := haudit endpoint hmem
  rw [Bool.or_eq_true] at hentry
  rcases hentry with hzero | hle
  · exact absurd (by simpa using hzero) hendpoint
  · exact isCompactIndexedPairShellLowerBound_of_minimum nearMask witness endpoint
      _ (by simpa using hle)


/-- The tail audit restricted to a window of endpoint indices.  One audit over
all twenty-four non-empty endpoints sets a module's peak, so the
window lets a generated module trade a little elaboration for a lower ceiling
and hence more concurrent workers. -/
def compactTailEndpointBoundsAuditRange (nearMask : ℕ) (witness : Array ℤ)
    (table : List ℤ) (lo hi : ℕ) : Bool :=
  (List.ofFn fun endpoint : CompactEndpointIndex nearMask => endpoint).all
    fun endpoint =>
      !(decide (lo ≤ endpoint.val) && decide (endpoint.val < hi)) ||
        decide (table.getD endpoint.val 0 ≤
          compactIndexedEndpointPairMinimum nearMask witness endpoint)

theorem isCompactIndexedPairShellLowerBound_of_tailAuditRange (nearMask : ℕ)
    (witness : Array ℤ) (table : List ℤ) (lo hi : ℕ)
    (haudit : compactTailEndpointBoundsAuditRange nearMask witness table lo hi = true)
    (endpoint : CompactEndpointIndex nearMask)
    (hlo : lo ≤ endpoint.val) (hhi : endpoint.val < hi) :
    IsCompactIndexedPairShellLowerBound nearMask witness endpoint
      (table.getD endpoint.val 0) := by
  rw [compactTailEndpointBoundsAuditRange, List.all_eq_true] at haudit
  have hmem : endpoint ∈
      (List.ofFn fun endpoint : CompactEndpointIndex nearMask => endpoint) := by
    simp
  have hentry := haudit endpoint hmem
  rw [Bool.or_eq_true] at hentry
  rcases hentry with houtside | hle
  · simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq,
      decide_eq_false_iff_not, not_lt] at houtside
    exact absurd (houtside hlo) (not_le.mpr hhi)
  · exact isCompactIndexedPairShellLowerBound_of_minimum nearMask witness endpoint
      _ (by simpa using hle)


end SRG266.QuasiSymmetric
