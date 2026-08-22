/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.RootedCubicLift
import SRG266.QuasiSymmetric.GlobalDesignSymmetry

/-!
# Choosing a non-`2K4` root

This file removes the exceptional `2K4` cubic graph from the root of the
intrinsic residual obstruction.  The argument is a four-cell pigeonhole
principle.

A `2K4` block on the eight vertices outside its isolated triple has a
two-colouring whose two colour classes have size four, and whose edges are
exactly the pairs of vertices of the same colour.  If two isolated triples are
disjoint, five vertices are active in both blocks.  Their two colourings give
only four pairs of colours, so two of the five vertices have the same colour
in both blocks.  The edge between them belongs to both blocks.

Consequently two `2K4` blocks with disjoint isolated triples cannot be
edge-disjoint.  The twenty-four neighbours of a root block in a
`GlobalDesign` have disjoint isolated triples and disjoint edge sets.  Hence a
`2K4` root has only non-`2K4` neighbours, and every global design can be rooted
at a non-`2K4` block.

The final structure in this file is the reduced finite target for the
remaining affine fourth-bit argument.  No classification, search result or
certificate is used here.
-/

namespace SRG266.QuasiSymmetric

/-- A block is the disjoint union of two complete graphs on four vertices,
with `T` as its three isolated vertices.

The Boolean colouring names the two components.  The cardinality clauses make
both active colour classes four-sets, while the edge clause completely
determines the graph (and excludes every edge incident with `T`). -/
def IsTwoK4 (T : Finset (Fin 11)) (B : Finset Edge11) : Prop :=
  T.card = 3 ∧
    ∃ colour : Fin 11 → Bool,
      (∀ b : Bool,
        (((Finset.univ : Finset (Fin 11)) \ T).filter fun v => colour v = b).card = 4) ∧
      ∀ {v w : Fin 11} (hvw : v ≠ w),
        Edge11.mk' hvw ∈ B ↔ v ∉ T ∧ w ∉ T ∧ colour v = colour w

theorem Edge11.map_mk' (permutation : Equiv.Perm (Fin 11))
    {v w : Fin 11} (hvw : v ≠ w) :
    Edge11.map permutation (Edge11.mk' hvw) =
      Edge11.mk' (fun heq => hvw (permutation.injective heq)) := by
  apply Subtype.ext
  simp [Edge11.map, Edge11.mk']

theorem mem_image_edgeMap {permutation : Equiv.Perm (Fin 11)}
    {B : Finset Edge11} {edge : Edge11} :
    edge ∈ B.image (Edge11.map permutation) ↔
      Edge11.map permutation.symm edge ∈ B := by
  constructor
  · intro hedge
    obtain ⟨source, hsource, rfl⟩ := Finset.mem_image.mp hedge
    simpa using hsource
  · intro hedge
    exact Finset.mem_image.mpr
      ⟨Edge11.map permutation.symm edge, hedge,
        Edge11.map_map_symm permutation edge⟩

/-- The `2K4` property is invariant under relabelling all vertices. -/
theorem isTwoK4_image (permutation : Equiv.Perm (Fin 11))
    {T : Finset (Fin 11)} {B : Finset Edge11} (hTwo : IsTwoK4 T B) :
    IsTwoK4 (T.image permutation) (B.image (Edge11.map permutation)) := by
  classical
  rcases hTwo with ⟨hcard, colour, hclasses, hedges⟩
  have hmembership (vertex : Fin 11) :
      vertex ∈ T.image permutation ↔ permutation.symm vertex ∈ T := by
    simpa using (mem_image_perm
      (σ := permutation) (x := permutation.symm vertex) (T := T))
  refine ⟨?_, fun vertex => colour (permutation.symm vertex), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ permutation.injective]
    exact hcard
  · intro bit
    have hset :
        (((Finset.univ : Finset (Fin 11)) \ T.image permutation).filter
          fun vertex => colour (permutation.symm vertex) = bit) =
        ((((Finset.univ : Finset (Fin 11)) \ T).filter
          fun vertex => colour vertex = bit).image permutation) := by
      ext vertex
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
        true_and, Finset.mem_image]
      constructor
      · rintro ⟨hnot, hcolour⟩
        refine ⟨permutation.symm vertex, ⟨?_, hcolour⟩, by simp⟩
        intro hmem
        exact hnot ⟨permutation.symm vertex, hmem, by simp⟩
      · rintro ⟨source, ⟨hnot, hcolour⟩, rfl⟩
        refine ⟨?_, by simpa using hcolour⟩
        intro hmem
        obtain ⟨other, hother, hvalue⟩ := hmem
        have : other = source := permutation.injective hvalue
        exact hnot (this ▸ hother)
    rw [hset, Finset.card_image_of_injective _ permutation.injective]
    exact hclasses bit
  · intro v w hvw
    rw [mem_image_edgeMap, Edge11.map_mk', hedges]
    constructor
    · rintro ⟨hv, hw, hcolour⟩
      exact ⟨fun h => hv ((hmembership v).mp h),
        fun h => hw ((hmembership w).mp h), hcolour⟩
    · rintro ⟨hv, hw, hcolour⟩
      exact ⟨fun h => hv ((hmembership v).mpr h),
        fun h => hw ((hmembership w).mpr h), hcolour⟩

/-- Equivalently, relabelling reflects as well as preserves `2K4`. -/
theorem isTwoK4_image_iff (permutation : Equiv.Perm (Fin 11))
    {T : Finset (Fin 11)} {B : Finset Edge11} :
    IsTwoK4 (T.image permutation) (B.image (Edge11.map permutation)) ↔
      IsTwoK4 T B := by
  constructor
  · intro hTwo
    have hback := isTwoK4_image permutation.symm hTwo
    have hvertices :
        (T.image permutation).image permutation.symm = T :=
      image_perm_image_symm permutation T
    have hedges :
        (B.image (Edge11.map permutation)).image
          (Edge11.map permutation.symm) = B := by
      ext edge
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨middle, ⟨source, hsource, rfl⟩, hvalue⟩
        rw [Edge11.map_symm_map] at hvalue
        rwa [← hvalue]
      · intro hedge
        exact ⟨Edge11.map permutation edge,
          ⟨edge, hedge, rfl⟩, Edge11.map_symm_map permutation edge⟩
    rwa [hvertices, hedges] at hback
  · exact isTwoK4_image permutation

/-- Two `2K4` blocks whose isolated triples are disjoint share an edge.

There are five vertices outside the union of the two triples.  Mapping each of
them to its pair of Boolean component colours maps five objects to four, so
two distinct vertices have the same two colours. -/
theorem twoK4_inter_nonempty_of_disjoint_isolatedTriples
    {T U : Finset (Fin 11)} {B D : Finset Edge11}
    (hTU : (T ∩ U).card = 0) (hB : IsTwoK4 T B) (hD : IsTwoK4 U D) :
    (B ∩ D).Nonempty := by
  classical
  rcases hB with ⟨hTcard, colourB, -, hcolourB⟩
  rcases hD with ⟨hUcard, colourD, -, hcolourD⟩
  let active : Finset (Fin 11) := Finset.univ \ (T ∪ U)
  have hUnion : (T ∪ U).card = 6 := by
    have hcard := Finset.card_union_add_card_inter T U
    omega
  have hActive : active.card = 5 := by
    have hcard : ((Finset.univ : Finset (Fin 11)) \ (T ∪ U)).card =
        (Finset.univ : Finset (Fin 11)).card -
          ((T ∪ U) ∩ Finset.univ).card := Finset.card_sdiff
    simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hUnion] at hcard
    exact hcard
  let colourPair : Fin 11 → Bool × Bool := fun v => (colourB v, colourD v)
  obtain ⟨v, hv, w, hw, hvw, hcolours⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := active) (t := (Finset.univ : Finset (Bool × Bool)))
      (f := colourPair) (by simp [hActive]) (by simp)
  have hvOutside : v ∉ T ∧ v ∉ U := by
    simpa [active] using hv
  have hwOutside : w ∉ T ∧ w ∉ U := by
    simpa [active] using hw
  have hBcolour : colourB v = colourB w := congrArg Prod.fst hcolours
  have hDcolour : colourD v = colourD w := congrArg Prod.snd hcolours
  refine ⟨Edge11.mk' hvw, ?_⟩
  rw [Finset.mem_inter, hcolourB hvw, hcolourD hvw]
  exact ⟨⟨hvOutside.1, hwOutside.1, hBcolour⟩,
    ⟨hvOutside.2, hwOutside.2, hDcolour⟩⟩

/-- The non-orthogonality lemma in disjointness form: disjoint isolated
triples do not permit edge-disjoint `2K4` blocks. -/
theorem twoK4_not_disjoint_of_disjoint_isolatedTriples
    {T U : Finset (Fin 11)} {B D : Finset Edge11}
    (hTU : (T ∩ U).card = 0) (hB : IsTwoK4 T B) (hD : IsTwoK4 U D) :
    ¬ Disjoint B D := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  exact (twoK4_inter_nonempty_of_disjoint_isolatedTriples hTU hB hD).ne_empty

namespace GlobalDesign

variable (G : GlobalDesign)

/-- Every block disjoint from a `2K4` block is non-`2K4`.  In particular, all
twenty-four neighbours of a `2K4` root are non-exceptional. -/
theorem not_isTwoK4_of_mem_disjointFrom {T U : Finset (Fin 11)}
    (hT : T ∈ triples) (hU : U ∈ G.disjointFrom T)
    (hTwo : IsTwoK4 T (G.block T)) :
    ¬ IsTwoK4 U (G.block U) := by
  intro hTwoU
  have hUt : U ∈ triples := (G.mem_disjointFrom.mp hU).1
  have hzero : (G.block T ∩ G.block U).card = 0 := (G.mem_disjointFrom.mp hU).2
  have hTU : T ≠ U := by
    intro h
    subst U
    rw [Finset.inter_self, G.block_card T hT] at hzero
    omega
  have htriples : (T ∩ U).card = 0 :=
    G.triples_disjoint_of_block_disjoint hT hUt hTU hzero
  have hnot := twoK4_not_disjoint_of_disjoint_isolatedTriples htriples hTwo hTwoU
  apply hnot
  rw [Finset.disjoint_iff_inter_eq_empty]
  exact Finset.card_eq_zero.mp hzero

/-- Every global residual design contains a block which is not `2K4`. -/
theorem exists_nonTwoK4_root :
    ∃ T ∈ triples, ¬ IsTwoK4 T (G.block T) := by
  let T : Finset (Fin 11) := {0, 1, 2}
  have hT : T ∈ triples := by
    decide +kernel
  by_cases hTwo : IsTwoK4 T (G.block T)
  · have hcard := G.card_disjointFrom hT
    have hpos : 0 < (G.disjointFrom T).card := by omega
    obtain ⟨U, hU⟩ := Finset.card_pos.mp hpos
    exact ⟨U, (G.mem_disjointFrom.mp hU).1,
      G.not_isTwoK4_of_mem_disjointFrom hT hU hTwo⟩
  · exact ⟨T, hT, hTwo⟩

end GlobalDesign

/-- A rooted cubic lift whose root is not the exceptional `2K4` graph. -/
structure NonTwoK4RootedCubicLift extends RootedCubicLift where
  /-- The chosen root is not a disjoint union of two four-cliques. -/
  root_not_twoK4 : ¬ IsTwoK4 root (block root)

/-- Existence of the intrinsic rooted obstruction with a non-`2K4` root. -/
abbrev IsNonTwoK4RootedCubicLift : Prop := Nonempty NonTwoK4RootedCubicLift

/-- The reduced intrinsic obstruction left for the affine fourth-gap
argument. -/
abbrev NoNonTwoK4RootedCubicLift : Prop := IsEmpty NonTwoK4RootedCubicLift

namespace GlobalDesign

variable (G : GlobalDesign)

/-- Root a global design at a non-`2K4` block and retain its intrinsic
twenty-four-neighbour cubic lift. -/
noncomputable def toNonTwoK4RootedCubicLift : NonTwoK4RootedCubicLift := by
  let T : Finset (Fin 11) := G.exists_nonTwoK4_root.choose
  have hT : T ∈ triples := G.exists_nonTwoK4_root.choose_spec.1
  exact
    { G.toRootedCubicLift T hT with
      root_not_twoK4 := G.exists_nonTwoK4_root.choose_spec.2 }

end GlobalDesign

/-- Refuting only non-`2K4` rooted lifts refutes every global residual design. -/
theorem isEmpty_globalDesign_of_noNonTwoK4RootedCubicLift
    (h : NoNonTwoK4RootedCubicLift) : IsEmpty GlobalDesign :=
  ⟨fun G => h.elim G.toNonTwoK4RootedCubicLift⟩

/-- The non-`2K4` rooted obstruction discharges the residual cherry-cover
boundary. -/
theorem noResidualCherryCover_of_noNonTwoK4RootedCubicLift
    (h : NoNonTwoK4RootedCubicLift) : NoResidualCherryCover :=
  noResidualCherryCover_of_isEmpty_globalDesign
    (isEmpty_globalDesign_of_noNonTwoK4RootedCubicLift h)

/-- The same reduced intrinsic obstruction eliminates the quasi-symmetric
design. -/
theorem noQuasiSymmetricDesign56_of_noNonTwoK4RootedCubicLift
    (h : NoNonTwoK4RootedCubicLift) : NoQuasiSymmetricDesign56.{u} :=
  noQuasiSymmetricDesign56_of_noResidualCherryCover
    (noResidualCherryCover_of_noNonTwoK4RootedCubicLift h)

end SRG266.QuasiSymmetric
