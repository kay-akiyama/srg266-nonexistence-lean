/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.FractionalNearFrame
import SRG266.QuasiSymmetric.FractionalNearFrameAudit

/-!
# Coordinates for the fractional near-frame transport

This module identifies the semantic endpoint shells and near rows of a lift
rooted at `{0,1,2}` with the eight-vertex coordinates used by the exact
certificate audit.  The small coordinate facts about the 55 edges of `K₁₁`
are replayed in Lean; no generated Farkas datum occurs here.
-/

namespace SRG266.QuasiSymmetric

open scoped BigOperators

/-- The low eight bits naming the endpoints of an edge outside the fixed
root coordinates. -/
def fixedOffRootEndpointMask (e : Edge11) : ℕ :=
  vertexMask e.vertices / 8

/-- The mathematical set represented by `fixedOffRootEndpointMask`. -/
def fixedOffRootEndpoints (e : Edge11) : Finset (Fin 8) :=
  Finset.univ.filter fun vertex => shiftRootVertex vertex ∈ e.vertices

theorem fixedOffRootEndpointMask_eq_vertexMask8 (e : Edge11) :
    fixedOffRootEndpointMask e = vertexMask8 (fixedOffRootEndpoints e) := by
  revert e
  decide +kernel

theorem fixedOffRootEndpointMask_lt (e : Edge11) :
    fixedOffRootEndpointMask e < 2 ^ 8 := by
  revert e
  decide +kernel

theorem popcount_fixedOffRootEndpointMask_le_two (e : Edge11) :
    SRG266.Search.popcount (fixedOffRootEndpointMask e) ≤ 2 := by
  revert e
  decide +kernel

theorem card_fixedOffRootEndpoints (e : Edge11) :
    (fixedOffRootEndpoints e).card =
      SRG266.Search.popcount (fixedOffRootEndpointMask e) := by
  revert e
  decide +kernel

/-- There are three fixed-root edges with zero or one active endpoint and one
edge with any prescribed pair of active endpoints. -/
theorem card_edges_with_fixed_endpoint_mask (mask : Fin (2 ^ 8))
    (hcard : SRG266.Search.popcount mask.val ≤ 2) :
    ((Finset.univ : Finset Edge11).filter fun e =>
      fixedOffRootEndpointMask e = mask.val).card =
        if SRG266.Search.popcount mask.val < 2 then 3 else 1 := by
  revert mask
  decide +kernel

/-- Two active endpoints determine the edge uniquely. -/
theorem edge_eq_of_fixed_endpoint_mask_eq_of_popcount_eq_two
    {e f : Edge11}
    (hcard : SRG266.Search.popcount (fixedOffRootEndpointMask e) = 2)
    (hmasks : fixedOffRootEndpointMask f = fixedOffRootEndpointMask e) :
    f = e := by
  revert e f
  decide +kernel

theorem mem_compactNearRows_iff {nearMask index : ℕ} :
    index ∈ compactNearRows nearMask ↔
      index < 56 ∧ nearMask.testBit index = true := by
  constructor
  · intro hindex
    rw [compactNearRows, List.mem_map] at hindex
    obtain ⟨typedIndex, htypedIndex, rfl⟩ := hindex
    rw [List.mem_filter] at htypedIndex
    exact ⟨typedIndex.isLt, by simpa using htypedIndex.2⟩
  · rintro ⟨hindex, hbit⟩
    rw [compactNearRows, List.mem_map]
    let typedIndex : Fin 56 := ⟨index, hindex⟩
    refine ⟨typedIndex, ?_, rfl⟩
    rw [List.mem_filter]
    exact ⟨List.mem_finRange _, by simpa [typedIndex] using hbit⟩

theorem compactIntersectionOnePairAt_mem (nearMask : ℕ)
    (pair : CompactPairIndex nearMask) :
    compactIntersectionOnePairAt nearMask pair ∈
      compactIntersectionOnePairs nearMask := by
  rw [compactIntersectionOnePairAt,
    List.getD_eq_getElem _ _ pair.isLt]
  exact List.getElem_mem _

private theorem mem_compactListPairs_parts {α : Type*} {pair : α × α} :
    ∀ {items : List α}, pair ∈ compactListPairs items →
      pair.1 ∈ items ∧ pair.2 ∈ items := by
  intro items hpair
  induction items with
  | nil => simp [compactListPairs] at hpair
  | cons item items ih =>
      rw [compactListPairs, List.mem_append] at hpair
      rcases hpair with hhead | htail
      · rw [List.mem_map] at hhead
        obtain ⟨right, hright, rfl⟩ := hhead
        exact ⟨by simp, by simp [hright]⟩
      · obtain ⟨hleft, hright⟩ := ih htail
        exact ⟨by simp [hleft], by simp [hright]⟩

/-- Both entries emitted by the compact pair list are selected near rows,
and their compact triples meet in one point. -/
theorem compactIntersectionOnePairAt_properties (nearMask : ℕ)
    (pair : CompactPairIndex nearMask) :
    let vertices := compactIntersectionOnePairAt nearMask pair
    vertices.1 < 56 ∧ vertices.2 < 56 ∧
      nearMask.testBit vertices.1 = true ∧
      nearMask.testBit vertices.2 = true ∧
      compactRowsMeetOne vertices.1 vertices.2 = true := by
  have hmem := compactIntersectionOnePairAt_mem nearMask pair
  rw [compactIntersectionOnePairs, List.mem_filter] at hmem
  obtain ⟨hpair, hmeet⟩ := hmem
  obtain ⟨hleftRow, hrightRow⟩ := mem_compactListPairs_parts hpair
  have hleftParts := mem_compactNearRows_iff.mp hleftRow
  have hrightParts := mem_compactNearRows_iff.mp hrightRow
  exact ⟨hleftParts.1, hrightParts.1, hleftParts.2,
    hrightParts.2, hmeet⟩

theorem compactRowsMeetOne_self_false (index : Fin 56) :
    compactRowsMeetOne index.val index.val = false := by
  revert index
  decide +kernel

theorem card_rootTripleAt_inter_eq_compactPopcount
    (left right : Fin 56) :
    ((rootTripleAt left) ∩ (rootTripleAt right)).card =
      SRG266.Search.popcount
        (compactTripleCodeAt left.val &&& compactTripleCodeAt right.val) := by
  revert left right
  decide +kernel

namespace RegularNonTwoK4RootedCubicLift

variable (R : RegularNonTwoK4RootedCubicLift)

/-- Identify the eight vertices outside a fixed `{0,1,2}` root with `Fin 8`. -/
def offRootEquiv8 (hroot : R.root = fixedRoot012) : R.OffRootVertex ≃ Fin 8 where
  toFun vertex := fixedRootComplementEquiv8
    ⟨vertex.1, by simpa [hroot] using vertex.2⟩
  invFun vertex :=
    ⟨shiftRootVertex vertex, by
      simpa [hroot] using shiftRootVertex_not_mem_fixedRoot012 vertex⟩
  left_inv vertex := by
    apply Subtype.ext
    have h := congrArg Subtype.val (fixedRootComplementEquiv8.left_inv
      ⟨vertex.1, by simpa [hroot] using vertex.2⟩)
    exact h
  right_inv vertex := fixedRootComplementEquiv8.right_inv vertex

@[simp] theorem offRootEquiv8_apply_shift (hroot : R.root = fixedRoot012)
    (vertex : Fin 8) :
    R.offRootEquiv8 hroot
      ⟨shiftRootVertex vertex, by
        simpa [hroot] using shiftRootVertex_not_mem_fixedRoot012 vertex⟩ = vertex := by
  exact (R.offRootEquiv8 hroot).apply_symm_apply vertex

/-- Encode a semantic endpoint type as an eight-bit endpoint mask. -/
def compactEndpointMask (hroot : R.root = fixedRoot012)
    (endpoint : R.EndpointType) : ℕ :=
  vertexMask8 ((endpoint.1 : Finset R.OffRootVertex).image
    (R.offRootEquiv8 hroot))

theorem compactEndpointMask_injective (hroot : R.root = fixedRoot012) :
    Function.Injective (R.compactEndpointMask hroot) := by
  intro left right heq
  apply Subtype.ext
  apply Finset.image_injective (R.offRootEquiv8 hroot).injective
  have hvertices := congrArg vertices8OfMask heq
  simpa [compactEndpointMask] using hvertices

theorem image_offRootEndpoints_equiv
    (hroot : R.root = fixedRoot012) (e : Edge11) :
    (R.offRootEndpoints e).image (R.offRootEquiv8 hroot) =
      fixedOffRootEndpoints e := by
  ext vertex
  constructor
  · intro hvertex
    obtain ⟨active, hactive, hvalue⟩ := Finset.mem_image.mp hvertex
    subst vertex
    have hback :
        shiftRootVertex (R.offRootEquiv8 hroot active) = active.1 := by
      have h := congrArg Subtype.val
        ((R.offRootEquiv8 hroot).symm_apply_apply active)
      exact h
    simpa [fixedOffRootEndpoints, hback] using hactive
  · intro hvertex
    have hshift : shiftRootVertex vertex ∈ e.vertices := by
      simpa [fixedOffRootEndpoints] using hvertex
    let active : R.OffRootVertex :=
      ⟨shiftRootVertex vertex, by
        simpa [hroot] using shiftRootVertex_not_mem_fixedRoot012 vertex⟩
    exact Finset.mem_image.mpr
      ⟨active, by simpa [active] using hshift,
        R.offRootEquiv8_apply_shift hroot vertex⟩

theorem compactEndpointMask_offRootEndpoints
    (hroot : R.root = fixedRoot012) (e : Edge11)
    (hendpoint : R.offRootEndpoints e ∈ R.endpointTypes) :
    R.compactEndpointMask hroot ⟨R.offRootEndpoints e, hendpoint⟩ =
      fixedOffRootEndpointMask e := by
  rw [compactEndpointMask, R.image_offRootEndpoints_equiv hroot,
    fixedOffRootEndpointMask_eq_vertexMask8]

/-- A root-block edge cannot meet the isolated root triple. -/
theorem rootBlock_endpoint_not_mem {e : Edge11} (he : e ∈ R.block R.root)
    {vertex : Fin 11} (hvertex : vertex ∈ e.vertices) : vertex ∉ R.root := by
  intro hrootVertex
  have hmem : e ∈ (R.block R.root).filter fun edge =>
      vertex ∈ edge.vertices := Finset.mem_filter.mpr ⟨he, hvertex⟩
  have hpos : 0 < arcDegree (R.block R.root) vertex :=
    Finset.card_pos.mpr ⟨e, hmem⟩
  rw [R.root_block_isolates hrootVertex] at hpos
  omega

theorem popcount_fixedOffRootEndpointMask_eq_two_of_avoids_fixedRoot
    (e : Edge11)
    (havoid : ∀ vertex ∈ e.vertices, vertex ∉ fixedRoot012) :
    SRG266.Search.popcount (fixedOffRootEndpointMask e) = 2 := by
  revert e
  decide +kernel

theorem popcount_fixedOffRootEndpointMask_eq_two_of_mem_rootBlock
    (hroot : R.root = fixedRoot012) {e : Edge11}
    (he : e ∈ R.block R.root) :
    SRG266.Search.popcount (fixedOffRootEndpointMask e) = 2 := by
  apply popcount_fixedOffRootEndpointMask_eq_two_of_avoids_fixedRoot
  intro vertex hvertex
  simpa [← hroot] using R.rootBlock_endpoint_not_mem he hvertex

/-- The compact endpoint mask of a semantic endpoint type is the mask of any
edge which realizes that type. -/
theorem compactEndpointMask_eq_fixed_of_offRootEndpoints_eq
    (hroot : R.root = fixedRoot012) (endpoint : R.EndpointType) (e : Edge11)
    (he : e ∈ R.nonRootEdges)
    (hendpoint : R.offRootEndpoints e = endpoint.1) :
    R.compactEndpointMask hroot endpoint = fixedOffRootEndpointMask e := by
  have htype : R.offRootEndpoints e ∈ R.endpointTypes :=
    Finset.mem_image.mpr ⟨e, he, rfl⟩
  have hmask := R.compactEndpointMask_offRootEndpoints hroot e htype
  simpa [hendpoint] using hmask

theorem fixed_endpoint_fiber_nonRoot
    (hroot : R.root = fixedRoot012) (endpoint : R.EndpointType)
    {e : Edge11}
    (hmask : fixedOffRootEndpointMask e =
      R.compactEndpointMask hroot endpoint) :
    e ∈ R.nonRootEdges := by
  rcases Finset.mem_image.mp endpoint.property with
    ⟨representative, hrepresentative, hendpoint⟩
  rw [nonRootEdges, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro heRoot
  have hrootCard :=
    R.popcount_fixedOffRootEndpointMask_eq_two_of_mem_rootBlock hroot heRoot
  have hrepresentativeMask :
      R.compactEndpointMask hroot endpoint =
        fixedOffRootEndpointMask representative :=
    R.compactEndpointMask_eq_fixed_of_offRootEndpoints_eq hroot endpoint
      representative hrepresentative hendpoint
  have hsame : fixedOffRootEndpointMask representative =
      fixedOffRootEndpointMask e := by
    rw [← hrepresentativeMask, ← hmask]
  have heq : representative = e :=
    edge_eq_of_fixed_endpoint_mask_eq_of_popcount_eq_two
      (by simpa [hsame] using hrootCard) hsame
  subst representative
  exact (Finset.mem_filter.mp hrepresentative).2 heRoot

theorem edgeClass_eq_fixed_endpoint_fiber
    (hroot : R.root = fixedRoot012) (endpoint : R.EndpointType) :
    R.edgeClass endpoint =
      (Finset.univ : Finset Edge11).filter fun e =>
        fixedOffRootEndpointMask e = R.compactEndpointMask hroot endpoint := by
  ext e
  simp only [edgeClass, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨he, hendpoint⟩
    exact (R.compactEndpointMask_eq_fixed_of_offRootEndpoints_eq hroot endpoint
      e he hendpoint).symm
  · intro hmask
    have he := R.fixed_endpoint_fiber_nonRoot hroot endpoint hmask
    refine ⟨he, ?_⟩
    have htype : R.offRootEndpoints e ∈ R.endpointTypes :=
      Finset.mem_image.mpr ⟨e, he, rfl⟩
    have hsubtype :
        (⟨R.offRootEndpoints e, htype⟩ : R.EndpointType) = endpoint := by
      apply R.compactEndpointMask_injective hroot
      rw [R.compactEndpointMask_offRootEndpoints hroot e htype]
      exact hmask
    exact congrArg Subtype.val hsubtype

theorem compactEndpointMask_popcount_le_two
    (hroot : R.root = fixedRoot012) (endpoint : R.EndpointType) :
    SRG266.Search.popcount (R.compactEndpointMask hroot endpoint) ≤ 2 := by
  rcases Finset.mem_image.mp endpoint.property with
    ⟨e, he, hendpoint⟩
  rw [R.compactEndpointMask_eq_fixed_of_offRootEndpoints_eq hroot endpoint
    e he hendpoint]
  exact popcount_fixedOffRootEndpointMask_le_two e

theorem edgeClass_card_eq_compactEndpointCoefficient
    (hroot : R.root = fixedRoot012) (endpoint : R.EndpointType) :
    ((R.edgeClass endpoint).card : ℤ) =
      compactEndpointCoefficient (R.compactEndpointMask hroot endpoint) := by
  rcases Finset.mem_image.mp endpoint.property with
    ⟨e, he, hendpoint⟩
  have hmask := R.compactEndpointMask_eq_fixed_of_offRootEndpoints_eq
    hroot endpoint e he hendpoint
  let mask : Fin (2 ^ 8) :=
    ⟨R.compactEndpointMask hroot endpoint, by
      rw [hmask]
      exact fixedOffRootEndpointMask_lt e⟩
  have hcard := card_edges_with_fixed_endpoint_mask mask
    (by simpa [mask] using R.compactEndpointMask_popcount_le_two hroot endpoint)
  change (((Finset.univ : Finset Edge11).filter fun edge =>
      fixedOffRootEndpointMask edge = R.compactEndpointMask hroot endpoint).card) =
    (if SRG266.Search.popcount (R.compactEndpointMask hroot endpoint) < 2
      then 3 else 1) at hcard
  rw [← R.edgeClass_eq_fixed_endpoint_fiber hroot endpoint] at hcard
  change (R.edgeClass endpoint).card =
    (if SRG266.Search.popcount (R.compactEndpointMask hroot endpoint) < 2
      then 3 else 1) at hcard
  by_cases hlt :
      SRG266.Search.popcount (R.compactEndpointMask hroot endpoint) < 2
  · rw [if_pos hlt] at hcard
    rw [compactEndpointCoefficient, if_pos hlt]
    exact_mod_cast hcard
  · rw [if_neg hlt] at hcard
    rw [compactEndpointCoefficient, if_neg hlt]
    exact_mod_cast hcard

/-! ## Recovering the fixed-root coordinates -/

theorem near_eq_rootTripleFamily8
    (hnear : vertexFamilyMask R.near = expandRootNearMask nearMask) :
    R.near = rootTripleFamily8 nearMask := by
  calc
    R.near = tripleFamilyOfMask (vertexFamilyMask R.near) := by
      symm
      apply tripleFamilyOfMask_vertexFamilyMask
      intro U hU
      exact R.near_closed hU
    _ = tripleFamilyOfMask (expandRootNearMask nearMask) := by rw [hnear]
    _ = rootTripleFamily8 nearMask := tripleFamilyOfMask_expandRootNearMask

theorem mem_rootBlock_iff_near_pair_eq_two
    {v w : Fin 11} (hvw : v ≠ w) (hv : v ∉ R.root) (hw : w ∉ R.root) :
    Edge11.mk' hvw ∈ R.block R.root ↔
      (R.near ∩ triplesThrough v w).card = 2 := by
  have hcount := R.near_pair_count hvw hv hw
  by_cases hedge : Edge11.mk' hvw ∈ R.block R.root
  · rw [if_pos hedge] at hcount
    exact ⟨fun _ => hcount, fun _ => hedge⟩
  · rw [if_neg hedge] at hcount
    constructor
    · exact fun h => False.elim (hedge h)
    · intro htwo
      omega

theorem reconstructedRootBlock_eq_actual
    (hroot : R.root = fixedRoot012)
    (hnear : vertexFamilyMask R.near = expandRootNearMask nearMask) :
    reconstructedRootBlock 7 (expandRootNearMask nearMask) = R.block R.root := by
  have hrootMask : vertexMask R.root = 7 := by
    rw [hroot]
    exact vertexMask_fixedRoot012
  rw [← hnear, ← hrootMask]
  ext e
  simp only [reconstructedRootBlock, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [vertexMask_and_edge_eq_zero_iff, triplePairMask,
    popcount_and_vertexFamilyMask]
  have hlohi : e.lo ≠ e.hi := e.lo_lt_hi.ne
  have heq : e = Edge11.mk' hlohi :=
    Edge11.eq_of_mem_mem hlohi e.lo_mem e.hi_mem
  constructor
  · rintro ⟨⟨hloRoot, hhiRoot⟩, htwo⟩
    exact heq.symm ▸
      (R.mem_rootBlock_iff_near_pair_eq_two hlohi hloRoot hhiRoot).mpr htwo
  · intro he
    have hloRoot := R.rootBlock_endpoint_not_mem he e.lo_mem
    have hhiRoot := R.rootBlock_endpoint_not_mem he e.hi_mem
    exact ⟨⟨hloRoot, hhiRoot⟩,
      (R.mem_rootBlock_iff_near_pair_eq_two hlohi hloRoot hhiRoot).mp
        (heq ▸ he)⟩

theorem rootBlock_eq_rootEdgeFamily8
    (hroot : R.root = fixedRoot012)
    (hnear : vertexFamilyMask R.near = expandRootNearMask nearMask) :
    R.block R.root = rootEdgeFamily8 (reconstructedRootGraph8 nearMask) := by
  rw [← reconstructedRootBlock_eq_actual R hroot hnear]
  exact reconstructedRootBlock_eq_rootEdgeFamily8 nearMask

end RegularNonTwoK4RootedCubicLift

theorem fixed_endpoint_mask_mem_prefix_of_popcount_lt_two (e : Edge11)
    (hcard : SRG266.Search.popcount (fixedOffRootEndpointMask e) < 2) :
    fixedOffRootEndpointMask e ∈
      [0] ++ (List.range 8).map (fun vertex => 2 ^ vertex) := by
  revert e
  decide +kernel

theorem fixed_endpoint_mask_avoids_root_of_popcount_eq_two (e : Edge11)
    (hcard : SRG266.Search.popcount (fixedOffRootEndpointMask e) = 2) :
    7 &&& vertexMask e.vertices = 0 := by
  revert e
  decide +kernel

theorem fixedOffRootEndpointMask_rootEdgeAt8 (index : Fin 28) :
    fixedOffRootEndpointMask (rootEdgeAt8 index) = compactPairCodeAt index.val := by
  revert index
  decide +kernel

theorem compactPairCodeAt_injective_on_fin :
    Function.Injective fun index : Fin 28 => compactPairCodeAt index.val := by
  intro left right heq
  revert left right
  decide +kernel

theorem compactPairCodeAt_not_mem_endpointPrefix (index : Fin 28) :
    compactPairCodeAt index.val ∉
      [0] ++ (List.range 8).map (fun vertex => 2 ^ vertex) := by
  revert index
  decide +kernel

theorem compactPairCodeAt_lt (index : Fin 28) :
    compactPairCodeAt index.val < 2 ^ 8 := by
  revert index
  decide +kernel

theorem endpointPrefix_value_lt {value : ℕ}
    (hvalue : value ∈ [0] ++ (List.range 8).map (fun vertex => 2 ^ vertex)) :
    value < 2 ^ 8 := by
  revert value
  decide +kernel

theorem exists_edge_of_mem_endpointPrefix (value : Fin (2 ^ 8))
    (hvalue : value.val ∈
      [0] ++ (List.range 8).map (fun vertex => 2 ^ vertex)) :
    ∃ e : Edge11,
      fixedOffRootEndpointMask e = value.val ∧
        SRG266.Search.popcount value.val < 2 := by
  revert value
  decide +kernel

theorem compactEndpointMasks_nodup (nearMask : ℕ) :
    (compactEndpointMasks nearMask).Nodup := by
  let endpointPrefix : List ℕ :=
    [0] ++ (List.range 8).map (fun vertex => 2 ^ vertex)
  let suffixIndices : List (Fin 28) :=
    (List.finRange 28).filter fun index =>
      !(reconstructedRootGraph8 nearMask).testBit index.val
  have hprefix : endpointPrefix.Nodup := by
    decide +kernel
  have hsuffixIndices : suffixIndices.Nodup :=
    (List.nodup_finRange 28).filter _
  have hsuffix :
      (suffixIndices.map fun index => compactPairCodeAt index.val).Nodup := by
    apply List.Nodup.map_on _ hsuffixIndices
    intro left _ right _ heq
    exact compactPairCodeAt_injective_on_fin heq
  have hdisjoint : ∀ value ∈ endpointPrefix,
      value ∉ suffixIndices.map (fun index => compactPairCodeAt index.val) := by
    intro value hvalue hsuffixMem
    rw [List.mem_map] at hsuffixMem
    obtain ⟨index, _, rfl⟩ := hsuffixMem
    exact compactPairCodeAt_not_mem_endpointPrefix index hvalue
  rw [compactEndpointMasks]
  exact List.Nodup.append hprefix hsuffix hdisjoint

theorem compactEndpointMask_value_lt {nearMask value : ℕ}
    (hvalue : value ∈ compactEndpointMasks nearMask) : value < 2 ^ 8 := by
  rw [compactEndpointMasks, List.mem_append] at hvalue
  rcases hvalue with hprefix | hsuffix
  · exact endpointPrefix_value_lt hprefix
  · rw [List.mem_map] at hsuffix
    obtain ⟨index, _, rfl⟩ := hsuffix
    exact compactPairCodeAt_lt index

/-- A duplicate-free list is equivalent to its subtype of members. -/
def listMemberEquivFin {α : Type*} [DecidableEq α]
    (items : List α) (hnodup : items.Nodup) :
    {value : α // value ∈ items} ≃ Fin items.length where
  toFun value := ⟨items.idxOf value.1, List.idxOf_lt_length_of_mem value.2⟩
  invFun index := ⟨items[index.val],
    List.getElem_mem (l := items) (n := index.val) (h := index.isLt)⟩
  left_inv value := by
    apply Subtype.ext
    exact List.getElem_idxOf (List.idxOf_lt_length_of_mem value.2)
  right_inv index := by
    apply Fin.ext
    exact hnodup.idxOf_getElem index.val index.isLt

namespace RegularNonTwoK4RootedCubicLift

variable (R : RegularNonTwoK4RootedCubicLift)

theorem fixed_endpoint_mask_mem_compactEndpointMasks
    (hroot : R.root = fixedRoot012)
    (hnear : vertexFamilyMask R.near = expandRootNearMask nearMask)
    {e : Edge11} (he : e ∈ R.nonRootEdges) :
    fixedOffRootEndpointMask e ∈ compactEndpointMasks nearMask := by
  by_cases hsmall : SRG266.Search.popcount (fixedOffRootEndpointMask e) < 2
  · rw [compactEndpointMasks]
    exact List.mem_append_left _
      (fixed_endpoint_mask_mem_prefix_of_popcount_lt_two e hsmall)
  · have hcard : SRG266.Search.popcount (fixedOffRootEndpointMask e) = 2 := by
      have hle := popcount_fixedOffRootEndpointMask_le_two e
      omega
    obtain ⟨index, hindex⟩ := rootEdgeAt8_surjective_offroot e
      (fixed_endpoint_mask_avoids_root_of_popcount_eq_two e hcard)
    subst e
    have hnotRootEdge :
        ¬(reconstructedRootGraph8 nearMask).testBit index.val = true := by
      intro hbit
      have hrootEdge : rootEdgeAt8 index ∈
          rootEdgeFamily8 (reconstructedRootGraph8 nearMask) := by
        rw [rootEdgeFamily8, Finset.mem_image]
        exact ⟨index, by simp [hbit], rfl⟩
      have hactual : rootEdgeAt8 index ∈ R.block R.root := by
        rw [R.rootBlock_eq_rootEdgeFamily8 hroot hnear]
        exact hrootEdge
      exact (Finset.mem_filter.mp he).2 hactual
    rw [compactEndpointMasks, List.mem_append]
    right
    rw [List.mem_map]
    exact ⟨index, by simp [hnotRootEdge],
      (fixedOffRootEndpointMask_rootEdgeAt8 index).symm⟩

theorem compactEndpointMask_mem_compactEndpointMasks
    (hroot : R.root = fixedRoot012)
    (hnear : vertexFamilyMask R.near = expandRootNearMask nearMask)
    (endpoint : R.EndpointType) :
    R.compactEndpointMask hroot endpoint ∈ compactEndpointMasks nearMask := by
  rcases Finset.mem_image.mp endpoint.property with ⟨e, he, hendpoint⟩
  rw [R.compactEndpointMask_eq_fixed_of_offRootEndpoints_eq hroot endpoint
    e he hendpoint]
  exact R.fixed_endpoint_mask_mem_compactEndpointMasks hroot hnear he

theorem exists_nonRootEdge_of_mem_compactEndpointMasks
    (hroot : R.root = fixedRoot012)
    (hnear : vertexFamilyMask R.near = expandRootNearMask nearMask)
    {value : ℕ} (hvalue : value ∈ compactEndpointMasks nearMask) :
    ∃ e ∈ R.nonRootEdges, fixedOffRootEndpointMask e = value := by
  rw [compactEndpointMasks, List.mem_append] at hvalue
  rcases hvalue with hprefix | hsuffix
  · let bounded : Fin (2 ^ 8) := ⟨value, endpointPrefix_value_lt hprefix⟩
    obtain ⟨e, heMask, heSmall⟩ := exists_edge_of_mem_endpointPrefix bounded
      (by simpa [bounded] using hprefix)
    refine ⟨e, ?_, by simpa [bounded] using heMask⟩
    rw [nonRootEdges, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro heRoot
    have heTwo :=
      R.popcount_fixedOffRootEndpointMask_eq_two_of_mem_rootBlock hroot heRoot
    rw [heMask] at heTwo
    omega
  · rw [List.mem_map] at hsuffix
    obtain ⟨index, hindex, hvalue⟩ := hsuffix
    refine ⟨rootEdgeAt8 index, ?_, ?_⟩
    · rw [nonRootEdges, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro heRoot
      have heFamily : rootEdgeAt8 index ∈
          rootEdgeFamily8 (reconstructedRootGraph8 nearMask) := by
        rw [← R.rootBlock_eq_rootEdgeFamily8 hroot hnear]
        exact heRoot
      rw [rootEdgeFamily8, Finset.mem_image] at heFamily
      obtain ⟨other, hother, heq⟩ := heFamily
      have hsame : other = index := rootEdgeAt8_injective heq
      subst other
      have hbit : (reconstructedRootGraph8 nearMask).testBit index.val = true := by
        simpa using hother
      have hnot := (List.mem_filter.mp hindex).2
      simp [hbit] at hnot
    · rw [fixedOffRootEndpointMask_rootEdgeAt8]
      exact hvalue

/-- The semantic endpoint types and the 25 compact endpoint rows are the same
finite set. -/
noncomputable def compactEndpointEquiv
    (hroot : R.root = fixedRoot012)
    (hnear : vertexFamilyMask R.near = expandRootNearMask nearMask) :
    R.EndpointType ≃ CompactEndpointIndex nearMask :=
  let semanticToValue : R.EndpointType ≃
      {value : ℕ // value ∈ compactEndpointMasks nearMask} :=
    Equiv.ofBijective
      (fun endpoint =>
        ⟨R.compactEndpointMask hroot endpoint,
          R.compactEndpointMask_mem_compactEndpointMasks hroot hnear endpoint⟩)
      ⟨by
        intro left right heq
        exact R.compactEndpointMask_injective hroot
          (congrArg Subtype.val heq), by
        rintro ⟨value, hvalue⟩
        obtain ⟨e, he, heMask⟩ :=
          R.exists_nonRootEdge_of_mem_compactEndpointMasks hroot hnear hvalue
        let endpoint : R.EndpointType :=
          ⟨R.offRootEndpoints e, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩
        refine ⟨endpoint, Subtype.ext ?_⟩
        change R.compactEndpointMask hroot endpoint = value
        rw [R.compactEndpointMask_offRootEndpoints hroot e endpoint.property]
        exact heMask⟩
  semanticToValue.trans
    (listMemberEquivFin (compactEndpointMasks nearMask)
      (compactEndpointMasks_nodup nearMask))

theorem compactEndpointMaskAt_equiv
    (hroot : R.root = fixedRoot012)
    (hnear : vertexFamilyMask R.near = expandRootNearMask nearMask)
    (endpoint : R.EndpointType) :
    compactEndpointMaskAt nearMask (R.compactEndpointEquiv hroot hnear endpoint) =
      R.compactEndpointMask hroot endpoint := by
  rw [compactEndpointMaskAt]
  exact List.getElem_idxOf
    (List.idxOf_lt_length_of_mem
      (R.compactEndpointMask_mem_compactEndpointMasks hroot hnear endpoint))

/-! ## Decoding compact concurrence rows -/

def compactPairLeftIndex (pair : CompactPairIndex nearMask) : Fin 56 :=
  ⟨(compactIntersectionOnePairAt nearMask pair).1,
    (compactIntersectionOnePairAt_properties nearMask pair).1⟩

def compactPairRightIndex (pair : CompactPairIndex nearMask) : Fin 56 :=
  ⟨(compactIntersectionOnePairAt nearMask pair).2,
    (compactIntersectionOnePairAt_properties nearMask pair).2.1⟩

theorem compactPairLeftIndex_bit (pair : CompactPairIndex nearMask) :
    nearMask.testBit (compactPairLeftIndex pair).val = true :=
  (compactIntersectionOnePairAt_properties nearMask pair).2.2.1

theorem compactPairRightIndex_bit (pair : CompactPairIndex nearMask) :
    nearMask.testBit (compactPairRightIndex pair).val = true :=
  (compactIntersectionOnePairAt_properties nearMask pair).2.2.2.1

theorem compactPairIndices_ne (pair : CompactPairIndex nearMask) :
    compactPairLeftIndex pair ≠ compactPairRightIndex pair := by
  intro heq
  have hmeet :=
    (compactIntersectionOnePairAt_properties nearMask pair).2.2.2.2
  have hfalse := compactRowsMeetOne_self_false (compactPairLeftIndex pair)
  change compactRowsMeetOne (compactPairLeftIndex pair).val
    (compactPairRightIndex pair).val = true at hmeet
  rw [← heq] at hmeet
  rw [hfalse] at hmeet
  contradiction

theorem compactPair_rootTriple_inter_card (pair : CompactPairIndex nearMask) :
    ((rootTripleAt (compactPairLeftIndex pair)) ∩
      (rootTripleAt (compactPairRightIndex pair))).card = 1 := by
  rw [card_rootTripleAt_inter_eq_compactPopcount]
  have hmeet :=
    (compactIntersectionOnePairAt_properties nearMask pair).2.2.2.2
  simpa [compactRowsMeetOne, compactPairLeftIndex,
    compactPairRightIndex] using hmeet

def compactPairLeftRow
    (hnear : vertexFamilyMask R.near = expandRootNearMask nearMask)
    (pair : CompactPairIndex nearMask) : R.NearRow :=
  ⟨rootTripleAt (compactPairLeftIndex pair), by
    rw [R.near_eq_rootTripleFamily8 hnear,
      rootTripleAt_mem_rootTripleFamily8]
    exact compactPairLeftIndex_bit pair⟩

def compactPairRightRow
    (hnear : vertexFamilyMask R.near = expandRootNearMask nearMask)
    (pair : CompactPairIndex nearMask) : R.NearRow :=
  ⟨rootTripleAt (compactPairRightIndex pair), by
    rw [R.near_eq_rootTripleFamily8 hnear,
      rootTripleAt_mem_rootTripleFamily8]
    exact compactPairRightIndex_bit pair⟩

theorem compactPairRows_ne
    (hnear : vertexFamilyMask R.near = expandRootNearMask nearMask)
    (pair : CompactPairIndex nearMask) :
    R.compactPairLeftRow hnear pair ≠ R.compactPairRightRow hnear pair := by
  intro heq
  apply compactPairIndices_ne pair
  apply rootTripleAt_injective
  exact congrArg Subtype.val heq

theorem compactPairRows_inter_card
    (hnear : vertexFamilyMask R.near = expandRootNearMask nearMask)
    (pair : CompactPairIndex nearMask) :
    (((R.compactPairLeftRow hnear pair : R.NearRow) : Finset (Fin 11)) ∩
      ((R.compactPairRightRow hnear pair : R.NearRow) :
        Finset (Fin 11))).card = 1 :=
  compactPair_rootTriple_inter_card pair

/-! ## Encoding semantic shell columns -/

/-- Encode a semantic subset of the near family by its compact triple
positions. -/
def compactNearColumnMask (nearMask : ℕ)
    (column : Finset (Finset (Fin 11))) : ℕ :=
  SRG266.Search.itemPositionsMask <|
    ((List.finRange 56).filter fun index =>
      nearMask.testBit index.val && decide (rootTripleAt index ∈ column)).map Fin.val

theorem compactNearColumnMask_lt (nearMask : ℕ)
    (column : Finset (Finset (Fin 11))) :
    compactNearColumnMask nearMask column < 2 ^ 56 := by
  rw [compactNearColumnMask]
  apply SRG266.Search.itemPositionsMask_lt
  intro code hcode
  rw [List.mem_map] at hcode
  obtain ⟨index, -, rfl⟩ := hcode
  exact index.isLt

theorem testBit_compactNearColumnMask (nearMask : ℕ)
    (column : Finset (Finset (Fin 11))) (index : Fin 56) :
    (compactNearColumnMask nearMask column).testBit index.val = true ↔
      nearMask.testBit index.val = true ∧ rootTripleAt index ∈ column := by
  rw [compactNearColumnMask, SRG266.Search.testBit_itemPositionsMask_iff,
    List.mem_map]
  constructor
  · rintro ⟨other, hother, hval⟩
    have heq : other = index := Fin.ext hval
    subst other
    simpa [Bool.and_eq_true] using hother
  · intro h
    exact ⟨index, by simp [h.1, h.2], rfl⟩

theorem compactTripleCodeAt_eq_triple8Codes (index : Fin 56) :
    compactTripleCodeAt index.val = triple8Codes[index.val] := by
  revert index
  decide +kernel

theorem shiftRootVertex_mem_rootTripleAt_iff (index : Fin 56)
    (vertex : Fin 8) :
    shiftRootVertex vertex ∈ rootTripleAt index ↔
      (compactTripleCodeAt index.val).testBit vertex.val = true := by
  rw [rootTripleAt_eq_image_shift, Finset.mem_image]
  constructor
  · rintro ⟨other, hother, heq⟩
    have hshift : other = vertex := by
      apply Fin.ext
      have hvalue := congrArg Fin.val heq
      simpa [shiftRootVertex] using hvalue
    subst other
    simpa [compactTripleCodeAt_eq_triple8Codes] using hother
  · intro hvertex
    exact ⟨vertex, by simpa [compactTripleCodeAt_eq_triple8Codes] using hvertex, rfl⟩

theorem vertexMask8_and_compactTripleCodeAt_eq_zero_iff
    (vertices : Finset (Fin 8)) (index : Fin 56) :
    vertexMask8 vertices &&& compactTripleCodeAt index.val = 0 ↔
      Disjoint vertices (vertices8OfMask (compactTripleCodeAt index.val)) := by
  revert vertices index
  decide +kernel

def offRootVertexAt (hroot : R.root = fixedRoot012) (vertex : Fin 8) :
    R.OffRootVertex :=
  ⟨shiftRootVertex vertex, by
    simpa [hroot] using shiftRootVertex_not_mem_fixedRoot012 vertex⟩

theorem shell_row_avoids_endpoint
    (endpoint : R.EndpointType)
    (column : R.NearColumnShell endpoint) {U : Finset (Fin 11)}
    (hU : U ∈ column.1) {active : R.OffRootVertex}
    (hactive : active ∈ endpoint.1) : (active : Fin 11) ∉ U := by
  intro hactiveU
  have hrow : U ∈ column.1 ∩ triplesAt active :=
    Finset.mem_inter.mpr ⟨hU,
      mem_triplesAt.mpr ⟨R.near_closed (column.property.1 hU), hactiveU⟩⟩
  have hpos : 0 < R.nearColumnPointDegree column.1 active :=
    Finset.card_pos.mpr ⟨U, hrow⟩
  rw [column.property.2 active, if_pos hactive] at hpos
  omega

theorem compactNearColumnMask_avoids_endpoint
    (hroot : R.root = fixedRoot012) (endpoint : R.EndpointType)
    (column : R.NearColumnShell endpoint) (index : Fin 56)
    (hcolumn : (compactNearColumnMask nearMask column.1).testBit index.val = true) :
    compactTripleCodeAt index.val &&& R.compactEndpointMask hroot endpoint = 0 := by
  have hrow := (testBit_compactNearColumnMask nearMask column.1 index).mp hcolumn
  rw [Nat.and_comm, compactEndpointMask,
    vertexMask8_and_compactTripleCodeAt_eq_zero_iff]
  rw [Finset.disjoint_left]
  intro vertex hvertex htriple
  obtain ⟨active, hactive, hvalue⟩ := Finset.mem_image.mp hvertex
  have hshift : shiftRootVertex vertex = active.1 := by
    rw [← hvalue]
    have h := congrArg Subtype.val
      ((R.offRootEquiv8 hroot).symm_apply_apply active)
    exact h
  have hactiveU : (active : Fin 11) ∈ rootTripleAt index := by
    rw [← hshift, shiftRootVertex_mem_rootTripleAt_iff]
    simpa only [mem_vertices8OfMask] using htriple
  exact R.shell_row_avoids_endpoint endpoint column hrow.2 hactive hactiveU

/-- Compact indices of a shell column through one active vertex. -/
def compactColumnIndicesAt (nearMask : ℕ)
    (column : Finset (Finset (Fin 11))) (vertex : Fin 8) : Finset (Fin 56) :=
  Finset.univ.filter fun index =>
    nearMask.testBit index.val = true ∧ rootTripleAt index ∈ column ∧
      (compactTripleCodeAt index.val).testBit vertex.val = true

theorem card_compactColumnIndicesAt
    (hroot : R.root = fixedRoot012)
    (hnear : vertexFamilyMask R.near = expandRootNearMask nearMask)
    {endpoint : R.EndpointType} (column : R.NearColumnShell endpoint)
    (vertex : Fin 8) :
    (compactColumnIndicesAt nearMask column.1 vertex).card =
      R.nearColumnPointDegree column.1 (R.offRootVertexAt hroot vertex) := by
  have hnearSet := R.near_eq_rootTripleFamily8 hnear
  have hset :
      (compactColumnIndicesAt nearMask column.1 vertex).image rootTripleAt =
        column.1 ∩ triplesAt (R.offRootVertexAt hroot vertex) := by
    ext U
    constructor
    · intro hU
      obtain ⟨index, hindex, rfl⟩ := Finset.mem_image.mp hU
      rw [compactColumnIndicesAt, Finset.mem_filter] at hindex
      exact Finset.mem_inter.mpr ⟨hindex.2.2.1,
        mem_triplesAt.mpr ⟨rootTripleAt_mem_triples index,
          (shiftRootVertex_mem_rootTripleAt_iff index vertex).mpr hindex.2.2.2⟩⟩
    · intro hU
      rw [Finset.mem_inter] at hU
      have hnearU : U ∈ R.near := column.property.1 hU.1
      rw [hnearSet, rootTripleFamily8, Finset.mem_image] at hnearU
      obtain ⟨index, hindex, hvalue⟩ := hnearU
      refine Finset.mem_image.mpr ⟨index, ?_, hvalue⟩
      rw [compactColumnIndicesAt, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
      · simpa using (Finset.mem_filter.mp hindex).2
      · simpa [hvalue] using hU.1
      · exact (shiftRootVertex_mem_rootTripleAt_iff index vertex).mp
          (by simpa [offRootVertexAt, hvalue] using (mem_triplesAt.mp hU.2).2)
  rw [nearColumnPointDegree, ← hset,
    Finset.card_image_of_injective _ rootTripleAt_injective]

theorem testBit_compactEndpointMask_iff
    (hroot : R.root = fixedRoot012) (endpoint : R.EndpointType)
    (vertex : Fin 8) :
    (R.compactEndpointMask hroot endpoint).testBit vertex.val = true ↔
      R.offRootVertexAt hroot vertex ∈ endpoint.1 := by
  rw [← mem_vertices8OfMask, compactEndpointMask,
    vertices8OfMask_vertexMask8]
  constructor
  · intro hvertex
    obtain ⟨active, hactive, hvalue⟩ := Finset.mem_image.mp hvertex
    have heq : active = R.offRootVertexAt hroot vertex := by
      apply (R.offRootEquiv8 hroot).injective
      exact hvalue
    exact heq ▸ hactive
  · intro hactive
    exact Finset.mem_image.mpr
      ⟨R.offRootVertexAt hroot vertex, hactive,
        R.offRootEquiv8_apply_shift hroot vertex⟩

/-- Encoding a semantic regular column produces a member of the complete
compact shell. -/
theorem isCompactNearColumn_compactNearColumnMask
    (hroot : R.root = fixedRoot012)
    (hnear : vertexFamilyMask R.near = expandRootNearMask nearMask)
    (endpoint : R.EndpointType) (column : R.NearColumnShell endpoint) :
    IsCompactNearColumn nearMask (R.compactEndpointMask hroot endpoint)
      (compactNearColumnMask nearMask column.1) := by
  constructor
  · intro code hcode
    rw [compactNearColumnMask,
      SRG266.Search.testBit_itemPositionsMask_iff, List.mem_map] at hcode
    obtain ⟨index, hindex, hvalue⟩ := hcode
    rw [compactNearColumnItems, List.mem_map]
    refine ⟨index, ?_, hvalue⟩
    rw [List.mem_filter]
    have hparts : nearMask.testBit index.val = true ∧
        rootTripleAt index ∈ column.1 := by
      have hparts := (List.mem_filter.mp hindex).2
      rw [Bool.and_eq_true] at hparts
      exact ⟨hparts.1, of_decide_eq_true hparts.2⟩
    refine ⟨List.mem_finRange _, ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hparts.1,
      R.compactNearColumnMask_avoids_endpoint hroot endpoint column index
        ((testBit_compactNearColumnMask nearMask column.1 index).mpr hparts)⟩
  · intro vertex
    let compactSet : Finset ℕ :=
      (compactNearColumnItems nearMask
        (R.compactEndpointMask hroot endpoint)).toFinset.filter fun code =>
          (compactNearColumnMask nearMask column.1).testBit code = true ∧
            (compactTripleCodeAt code).testBit vertex.val = true
    let indexSet := compactColumnIndicesAt nearMask column.1 vertex
    have hset : compactSet = indexSet.image Fin.val := by
      ext code
      constructor
      · intro hcode
        dsimp only [compactSet] at hcode
        rw [Finset.mem_filter] at hcode
        have hitems : code ∈ compactNearColumnItems nearMask
            (R.compactEndpointMask hroot endpoint) := by
          simpa using hcode.1
        rw [compactNearColumnItems, List.mem_map] at hitems
        obtain ⟨index, _, hvalue⟩ := hitems
        subst code
        have hcolumn :=
          (testBit_compactNearColumnMask nearMask column.1 index).mp hcode.2.1
        rw [Finset.mem_image]
        refine ⟨index, ?_, rfl⟩
        dsimp only [indexSet]
        rw [compactColumnIndicesAt, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hcolumn.1, hcolumn.2, hcode.2.2⟩
      · intro hcode
        rw [Finset.mem_image] at hcode
        obtain ⟨index, hindex, hvalue⟩ := hcode
        subst code
        dsimp only [indexSet] at hindex
        rw [compactColumnIndicesAt, Finset.mem_filter] at hindex
        dsimp only [compactSet]
        rw [Finset.mem_filter]
        refine ⟨?_,
          (testBit_compactNearColumnMask nearMask column.1 index).mpr
            ⟨hindex.2.1, hindex.2.2.1⟩,
          hindex.2.2.2⟩
        rw [List.mem_toFinset, compactNearColumnItems, List.mem_map]
        refine ⟨index, ?_, rfl⟩
        rw [List.mem_filter]
        refine ⟨List.mem_finRange _, ?_⟩
        rw [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hindex.2.1,
          R.compactNearColumnMask_avoids_endpoint hroot endpoint column index
            ((testBit_compactNearColumnMask nearMask column.1 index).mpr
              ⟨hindex.2.1, hindex.2.2.1⟩)⟩
    change compactSet.card = _
    rw [hset, Finset.card_image_of_injective _ Fin.val_injective,
      R.card_compactColumnIndicesAt hroot hnear column vertex,
      column.property.2, compactColumnVertexTarget]
    simp only [R.testBit_compactEndpointMask_iff hroot endpoint vertex]

/-- A semantic shell column, placed in its corresponding compact shell. -/
noncomputable def compactShellColumnOf
    (hroot : R.root = fixedRoot012)
    (hnear : vertexFamilyMask R.near = expandRootNearMask nearMask)
    (endpoint : R.EndpointType) (column : R.NearColumnShell endpoint) :
    CompactShellColumn nearMask (R.compactEndpointEquiv hroot hnear endpoint) := by
  let columnMask : Fin (2 ^ 56) :=
    ⟨compactNearColumnMask nearMask column.1,
      compactNearColumnMask_lt nearMask column.1⟩
  refine ⟨columnMask, ?_⟩
  rw [R.compactEndpointMaskAt_equiv hroot hnear endpoint]
  change IsCompactNearColumn nearMask (R.compactEndpointMask hroot endpoint)
    (compactNearColumnMask nearMask column.1)
  exact R.isCompactNearColumn_compactNearColumnMask hroot hnear endpoint column

/-- All semantic shell columns, before the coordinate injection. -/
abbrev SemanticFractionalColumn :=
  Σ endpoint : R.EndpointType, R.NearColumnShell endpoint

/-- Coordinate injection from semantic shell columns to compact columns. -/
noncomputable def compactFractionalColumnOf
    (hroot : R.root = fixedRoot012)
    (hnear : vertexFamilyMask R.near = expandRootNearMask nearMask) :
    R.SemanticFractionalColumn → CompactFractionalColumn nearMask
  | ⟨endpoint, column⟩ =>
      ⟨R.compactEndpointEquiv hroot hnear endpoint,
        R.compactShellColumnOf hroot hnear endpoint column⟩

/-- On a compact concurrence row, a semantic column has exactly its endpoint
class coefficient when it contains both decoded near rows, and zero
otherwise. -/
theorem compactFractionalMatrix_pair_source
    (hroot : R.root = fixedRoot012)
    (hnear : vertexFamilyMask R.near = expandRootNearMask nearMask)
    (pair : CompactPairIndex nearMask) (endpoint : R.EndpointType)
    (column : R.NearColumnShell endpoint) :
    (compactFractionalMatrix nearMask (Sum.inr pair)
        (R.compactFractionalColumnOf hroot hnear
          ⟨endpoint, column⟩) : ℚ) =
      ((R.edgeClass endpoint).card : ℚ) *
        R.shellPairIndicator column
          (R.compactPairLeftRow hnear pair)
          (R.compactPairRightRow hnear pair) := by
  have hcoefficientZ :=
    R.edgeClass_card_eq_compactEndpointCoefficient hroot endpoint
  have hcoefficientQ :
      ((R.edgeClass endpoint).card : ℚ) =
        (compactEndpointCoefficient
          (R.compactEndpointMask hroot endpoint) : ℚ) := by
    exact_mod_cast hcoefficientZ
  have hleftBit := compactPairLeftIndex_bit pair
  have hrightBit := compactPairRightIndex_bit pair
  have hpairBits :
      ((compactNearColumnMask nearMask column.1).testBit
          (compactIntersectionOnePairAt nearMask pair).1 = true ∧
        (compactNearColumnMask nearMask column.1).testBit
          (compactIntersectionOnePairAt nearMask pair).2 = true) ↔
      (rootTripleAt (compactPairLeftIndex pair) ∈ column.1 ∧
        rootTripleAt (compactPairRightIndex pair) ∈ column.1) := by
    change ((compactNearColumnMask nearMask column.1).testBit
          (compactPairLeftIndex pair).val = true ∧
        (compactNearColumnMask nearMask column.1).testBit
          (compactPairRightIndex pair).val = true) ↔ _
    rw [testBit_compactNearColumnMask,
      testBit_compactNearColumnMask]
    simp [hleftBit, hrightBit]
  simp only [compactFractionalMatrix, compactFractionalColumnOf]
  simp only [R.compactEndpointMaskAt_equiv hroot hnear endpoint]
  rw [hcoefficientQ]
  by_cases hp : rootTripleAt (compactPairLeftIndex pair) ∈ column.1 ∧
      rootTripleAt (compactPairRightIndex pair) ∈ column.1
  · have hbits := hpairBits.mpr hp
    simp [compactShellColumnOf, hbits, shellPairIndicator,
      compactPairLeftRow, compactPairRightRow, hp]
  · have hbits := hpairBits.not.mpr hp
    simp [compactShellColumnOf, hbits, shellPairIndicator,
      compactPairLeftRow, compactPairRightRow, hp]

/-- Push a semantic fractional frame forward to the complete compact column
space.  Compact columns outside the semantic image receive zero mass. -/
noncomputable def compactPushforwardMass
    (frame : FractionalNearFrame R)
    (hroot : R.root = fixedRoot012)
    (hnear : vertexFamilyMask R.near = expandRootNearMask nearMask)
    (column : CompactFractionalColumn nearMask) : ℚ :=
  ∑ source : R.SemanticFractionalColumn,
    if R.compactFractionalColumnOf hroot hnear source = column then
      frame.mass source.1 source.2
    else 0

theorem compactPushforwardMass_nonneg
    (frame : FractionalNearFrame R)
    (hroot : R.root = fixedRoot012)
    (hnear : vertexFamilyMask R.near = expandRootNearMask nearMask)
    (column : CompactFractionalColumn nearMask) :
    0 ≤ R.compactPushforwardMass frame hroot hnear column := by
  classical
  apply Finset.sum_nonneg
  intro source _
  split_ifs
  · exact frame.mass_nonneg source.1 source.2
  · exact le_rfl

/-- Integration against a finite pushforward equals integration before the
coordinate map. -/
theorem sum_compactPushforwardMass_mul
    (frame : FractionalNearFrame R)
    (hroot : R.root = fixedRoot012)
    (hnear : vertexFamilyMask R.near = expandRootNearMask nearMask)
    (g : CompactFractionalColumn nearMask → ℚ) :
    (∑ column : CompactFractionalColumn nearMask,
      R.compactPushforwardMass frame hroot hnear column * g column) =
    ∑ source : R.SemanticFractionalColumn,
      frame.mass source.1 source.2 *
        g (R.compactFractionalColumnOf hroot hnear source) := by
  classical
  calc
    (∑ column : CompactFractionalColumn nearMask,
      R.compactPushforwardMass frame hroot hnear column * g column) =
        ∑ column : CompactFractionalColumn nearMask,
          ∑ source : R.SemanticFractionalColumn,
            (if R.compactFractionalColumnOf hroot hnear source = column then
              frame.mass source.1 source.2 else 0) * g column := by
          apply Finset.sum_congr rfl
          intro column _
          rw [compactPushforwardMass, Finset.sum_mul]
    _ = ∑ source : R.SemanticFractionalColumn,
          ∑ column : CompactFractionalColumn nearMask,
            (if R.compactFractionalColumnOf hroot hnear source = column then
              frame.mass source.1 source.2 else 0) * g column := by
          rw [Finset.sum_comm]
    _ = ∑ source : R.SemanticFractionalColumn,
          frame.mass source.1 source.2 *
            g (R.compactFractionalColumnOf hroot hnear source) := by
          apply Finset.sum_congr rfl
          intro source _
          rw [Finset.sum_eq_single
            (R.compactFractionalColumnOf hroot hnear source)]
          · simp
          · intro column _ hne
            simp [Ne.symm hne]
          · simp

/-- The pushed mass satisfies the compact normalization row for every
endpoint shell. -/
theorem compactPushforwardMass_normalization
    (frame : FractionalNearFrame R)
    (hroot : R.root = fixedRoot012)
    (hnear : vertexFamilyMask R.near = expandRootNearMask nearMask)
    (endpoint : CompactEndpointIndex nearMask) :
    (∑ column : CompactFractionalColumn nearMask,
      (compactFractionalMatrix nearMask (Sum.inl endpoint) column : ℚ) *
        R.compactPushforwardMass frame hroot hnear column) = 1 := by
  classical
  calc
    (∑ column : CompactFractionalColumn nearMask,
      (compactFractionalMatrix nearMask (Sum.inl endpoint) column : ℚ) *
        R.compactPushforwardMass frame hroot hnear column) =
        ∑ column : CompactFractionalColumn nearMask,
          R.compactPushforwardMass frame hroot hnear column *
            (compactFractionalMatrix nearMask (Sum.inl endpoint) column : ℚ) := by
          apply Finset.sum_congr rfl
          intro column _
          ring
    _ = ∑ source : R.SemanticFractionalColumn,
          frame.mass source.1 source.2 *
            (compactFractionalMatrix nearMask (Sum.inl endpoint)
              (R.compactFractionalColumnOf hroot hnear source) : ℚ) :=
          R.sum_compactPushforwardMass_mul frame hroot hnear _
    _ = 1 := by
          let semanticEndpoint :=
            (R.compactEndpointEquiv hroot hnear).symm endpoint
          calc
            (∑ source : R.SemanticFractionalColumn,
              frame.mass source.1 source.2 *
                (compactFractionalMatrix nearMask (Sum.inl endpoint)
                  (R.compactFractionalColumnOf hroot hnear source) : ℚ)) =
                ∑ otherEndpoint : R.EndpointType,
                  ∑ column : R.NearColumnShell otherEndpoint,
                    frame.mass otherEndpoint column *
                      (compactFractionalMatrix nearMask (Sum.inl endpoint)
                        (R.compactFractionalColumnOf hroot hnear
                          ⟨otherEndpoint, column⟩) : ℚ) := by
                  exact Fintype.sum_sigma'
                    (ι := R.EndpointType)
                    (α := fun endpoint => R.NearColumnShell endpoint)
                    (M := ℚ) (fun otherEndpoint column =>
                      frame.mass otherEndpoint column *
                        (compactFractionalMatrix nearMask (Sum.inl endpoint)
                          (R.compactFractionalColumnOf hroot hnear
                            ⟨otherEndpoint, column⟩) : ℚ))
            _ = 1 := by
              have hsame :
                  endpoint = R.compactEndpointEquiv hroot hnear semanticEndpoint := by
                simp [semanticEndpoint]
              rw [Finset.sum_eq_single semanticEndpoint]
              · simp only [compactFractionalMatrix, compactFractionalColumnOf,
                  hsame, if_pos, Int.cast_one, mul_one]
                exact frame.mass_normalization semanticEndpoint
              · intro otherEndpoint _ hne
                have hcoordinate :
                    endpoint ≠ R.compactEndpointEquiv hroot hnear otherEndpoint := by
                  intro heq
                  apply hne
                  apply (R.compactEndpointEquiv hroot hnear).injective
                  simpa [semanticEndpoint] using heq.symm
                simp [compactFractionalMatrix, compactFractionalColumnOf,
                  hcoordinate]
              · simp

/-- The pushed mass satisfies every compact intersection-one concurrence
row. -/
theorem compactPushforwardMass_concurrence
    (frame : FractionalNearFrame R)
    (hroot : R.root = fixedRoot012)
    (hnear : vertexFamilyMask R.near = expandRootNearMask nearMask)
    (pair : CompactPairIndex nearMask) :
    (∑ column : CompactFractionalColumn nearMask,
      (compactFractionalMatrix nearMask (Sum.inr pair) column : ℚ) *
        R.compactPushforwardMass frame hroot hnear column) = 3 := by
  classical
  calc
    (∑ column : CompactFractionalColumn nearMask,
      (compactFractionalMatrix nearMask (Sum.inr pair) column : ℚ) *
        R.compactPushforwardMass frame hroot hnear column) =
        ∑ column : CompactFractionalColumn nearMask,
          R.compactPushforwardMass frame hroot hnear column *
            (compactFractionalMatrix nearMask (Sum.inr pair) column : ℚ) := by
          apply Finset.sum_congr rfl
          intro column _
          ring
    _ = ∑ source : R.SemanticFractionalColumn,
          frame.mass source.1 source.2 *
            (compactFractionalMatrix nearMask (Sum.inr pair)
              (R.compactFractionalColumnOf hroot hnear source) : ℚ) :=
          R.sum_compactPushforwardMass_mul frame hroot hnear _
    _ = ∑ endpoint : R.EndpointType,
          ∑ column : R.NearColumnShell endpoint,
            frame.mass endpoint column *
              (compactFractionalMatrix nearMask (Sum.inr pair)
                (R.compactFractionalColumnOf hroot hnear
                  ⟨endpoint, column⟩) : ℚ) := by
          exact Fintype.sum_sigma'
            (ι := R.EndpointType)
            (α := fun endpoint => R.NearColumnShell endpoint)
            (M := ℚ) (fun endpoint column =>
              frame.mass endpoint column *
                (compactFractionalMatrix nearMask (Sum.inr pair)
                  (R.compactFractionalColumnOf hroot hnear
                    ⟨endpoint, column⟩) : ℚ))
    _ = ∑ endpoint : R.EndpointType,
          ((R.edgeClass endpoint).card : ℚ) *
            ∑ column : R.NearColumnShell endpoint,
              frame.mass endpoint column *
                R.shellPairIndicator column
                  (R.compactPairLeftRow hnear pair)
                  (R.compactPairRightRow hnear pair) := by
          apply Finset.sum_congr rfl
          intro endpoint _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro column _
          rw [R.compactFractionalMatrix_pair_source hroot hnear]
          ring
    _ = 3 := frame.concurrence
          (R.compactPairLeftRow hnear pair)
          (R.compactPairRightRow hnear pair)
          (R.compactPairRows_ne hnear pair)
          (R.compactPairRows_inter_card hnear pair)

/-- A semantic fractional frame in fixed-root coordinates supplies a solution
to the compact rational system checked by the generated certificates. -/
theorem compactFractionalNearFrameOf
    (frame : FractionalNearFrame R)
    (hroot : R.root = fixedRoot012)
    (hnear : vertexFamilyMask R.near = expandRootNearMask nearMask) :
    CompactFractionalNearFrame nearMask := by
  refine ⟨R.compactPushforwardMass frame hroot hnear,
    R.compactPushforwardMass_nonneg frame hroot hnear, ?_⟩
  intro row
  cases row with
  | inl endpoint =>
      simpa [compactFractionalRhs] using
        R.compactPushforwardMass_normalization frame hroot hnear endpoint
  | inr pair =>
      simpa [compactFractionalRhs] using
        R.compactPushforwardMass_concurrence frame hroot hnear pair

end RegularNonTwoK4RootedCubicLift

end SRG266.QuasiSymmetric
