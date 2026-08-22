/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Basic

/-!
# The local `2-(45, 9, 8)` design

At a fixed root `x`, vertices in the second subconstituent index block
occurrences on the first subconstituent.  Blocks are indexed by occurrences:
two distinct vertices are allowed to determine the same point set.

This file proves all five design parameters directly from the strongly regular
graph axioms.  The replication and pair-multiplicity proofs use explicit
equivalences of finite types.
-/

namespace SRG266

/-- A small occurrence-based interface for a `2`-design.  Keeping the block
index type separate from the block point sets allows repeated blocks. -/
structure IsTwoDesignWith
    {Point Block : Type*}
    [Fintype Point] [DecidableEq Point]
    [Fintype Block] [DecidableEq Block]
    (blocks : Block → Finset Point)
    (numPoints numBlocks blockSize replication pairMultiplicity : ℕ) : Prop where
  point_card : Fintype.card Point = numPoints
  block_card : Fintype.card Block = numBlocks
  block_size : ∀ B, (blocks B).card = blockSize
  replication_number :
    ∀ p, ((Finset.univ : Finset Block).filter fun B => p ∈ blocks B).card = replication
  pair_multiplicity :
    ∀ ⦃p q⦄, p ≠ q →
      ((Finset.univ : Finset Block).filter fun B => p ∈ blocks B ∧ q ∈ blocks B).card =
          pairMultiplicity

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Block occurrences through a point of the first subconstituent. -/
def blocksThrough (x : V) (z : FirstSubconstituent G x) :
    Finset (SecondSubconstituent G x) :=
  Finset.univ.filter fun y => z ∈ localBlock G x y

/-- Block occurrences through a pair of points. -/
def blocksThroughPair (x : V) (z w : FirstSubconstituent G x) :
    Finset (SecondSubconstituent G x) :=
  Finset.univ.filter fun y => z ∈ localBlock G x y ∧ w ∈ localBlock G x y

omit [DecidableEq V] in
/-- A neighbor of a first-subconstituent point, other than the root direction,
cannot also be adjacent to the root: the SRG has adjacent common-neighbor
parameter zero. -/
theorem not_adj_root_of_adj_first
    (hG : IsHypothetical G) (x : V) (z : FirstSubconstituent G x)
    {w : V} (hzw : G.Adj (z : V) w) :
    ¬G.Adj x w := by
  intro hxw
  have hcard : Fintype.card (G.commonNeighbors x (z : V)) = 0 :=
    hG.of_adj x z z.property
  letI : IsEmpty (G.commonNeighbors x (z : V)) :=
    Fintype.card_eq_zero_iff.mp hcard
  exact isEmptyElim (⟨w, hxw, hzw⟩ : G.commonNeighbors x (z : V))

omit [DecidableEq V] in
/-- The first subconstituent is an independent set. -/
theorem firstSubconstituent_independent
    (hG : IsHypothetical G) (x : V)
    (z w : FirstSubconstituent G x) :
    ¬G.Adj (z : V) (w : V) :=
  fun hzw => not_adj_root_of_adj_first G hG x z hzw w.property

/-- Blocks through `z` correspond exactly to the neighbors of `z` other than
the root. -/
def blocksThroughEquiv
    (hG : IsHypothetical G) (x : V) (z : FirstSubconstituent G x) :
    ↥(blocksThrough G x z) ≃
      ↥((G.neighborFinset (z : V)).erase x) where
  toFun y := by
    refine ⟨(y.1 : V), Finset.mem_erase.mpr ⟨?_, ?_⟩⟩
    · exact ((G.compl_adj x y.1).mp y.1.property).1.symm
    · exact (G.mem_neighborFinset _ _).mpr <|
        (mem_localBlock G x y.1 z).mp (Finset.mem_filter.mp y.property).2
  invFun w := by
    have hw := Finset.mem_erase.mp w.property
    have hzw : G.Adj (z : V) (w : V) := (G.mem_neighborFinset _ _).mp hw.2
    let y : SecondSubconstituent G x :=
      ⟨w, (G.compl_adj x w).mpr
        ⟨hw.1.symm, not_adj_root_of_adj_first G hG x z hzw⟩⟩
    refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact (mem_localBlock G x y z).mpr hzw
  left_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv w := by
    apply Subtype.ext
    rfl

theorem blocksThrough_card
    (hG : IsHypothetical G) (x : V) (z : FirstSubconstituent G x) :
    (blocksThrough G x z).card = 44 := by
  calc
    (blocksThrough G x z).card =
        Fintype.card ↥(blocksThrough G x z) := (Fintype.card_coe _).symm
    _ = Fintype.card ↥((G.neighborFinset (z : V)).erase x) :=
      Fintype.card_congr (blocksThroughEquiv G hG x z)
    _ = ((G.neighborFinset (z : V)).erase x).card := Fintype.card_coe _
    _ = 44 := by
      have hx : x ∈ G.neighborFinset (z : V) :=
        (G.mem_neighborFinset _ _).mpr z.property.symm
      rw [Finset.card_erase_of_mem hx, G.card_neighborFinset_eq_degree, hG.regular z]

/-- Blocks through two distinct points correspond to their common neighbors
other than the root. -/
def blocksThroughPairEquiv
    (hG : IsHypothetical G) (x : V)
    (z w : FirstSubconstituent G x) :
    ↥(blocksThroughPair G x z w) ≃
      ↥((G.commonNeighbors (z : V) (w : V)).toFinset.erase x) where
  toFun y := by
    have hy := Finset.mem_filter.mp y.property
    have hzy : G.Adj (z : V) (y.1 : V) :=
      (mem_localBlock G x y.1 z).mp hy.2.1
    have hwy : G.Adj (w : V) (y.1 : V) :=
      (mem_localBlock G x y.1 w).mp hy.2.2
    refine ⟨(y.1 : V), Finset.mem_erase.mpr ⟨?_, ?_⟩⟩
    · exact ((G.compl_adj x y.1).mp y.1.property).1.symm
    · exact Set.mem_toFinset.mpr ⟨hzy, hwy⟩
  invFun u := by
    have hu := Finset.mem_erase.mp u.property
    have humem : (u : V) ∈ G.commonNeighbors (z : V) (w : V) :=
      Set.mem_toFinset.mp hu.2
    have hcommon : G.Adj (z : V) (u : V) ∧ G.Adj (w : V) (u : V) :=
      (G.mem_commonNeighbors).mp humem
    let y : SecondSubconstituent G x :=
      ⟨u, (G.compl_adj x u).mpr
        ⟨hu.1.symm, not_adj_root_of_adj_first G hG x z hcommon.1⟩⟩
    refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨(mem_localBlock G x y z).mpr hcommon.1,
      (mem_localBlock G x y w).mpr hcommon.2⟩
  left_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv u := by
    apply Subtype.ext
    rfl

theorem blocksThroughPair_card
    (hG : IsHypothetical G) (x : V)
    {z w : FirstSubconstituent G x} (hzw : z ≠ w) :
    (blocksThroughPair G x z w).card = 8 := by
  have hval : (z : V) ≠ (w : V) := fun h => hzw (Subtype.ext h)
  have hnot : ¬G.Adj (z : V) (w : V) :=
    firstSubconstituent_independent G hG x z w
  have hcommon : Fintype.card (G.commonNeighbors (z : V) (w : V)) = 9 :=
    hG.of_not_adj hval hnot
  have hx : x ∈ (G.commonNeighbors (z : V) (w : V)).toFinset :=
    Set.mem_toFinset.mpr ⟨z.property.symm, w.property.symm⟩
  calc
    (blocksThroughPair G x z w).card =
        Fintype.card ↥(blocksThroughPair G x z w) := (Fintype.card_coe _).symm
    _ = Fintype.card ↥((G.commonNeighbors (z : V) (w : V)).toFinset.erase x) :=
      Fintype.card_congr (blocksThroughPairEquiv G hG x z w)
    _ = ((G.commonNeighbors (z : V) (w : V)).toFinset.erase x).card :=
      Fintype.card_coe _
    _ = 8 := by
      rw [Finset.card_erase_of_mem hx, Set.toFinset_card, hcommon]

/-- The block occurrences in the second subconstituent form a
`2-(45, 9, 8)` design with 220 blocks and replication number 44. -/
theorem localDesign_isTwoDesignWith
    (hG : IsHypothetical G) (x : V) :
    IsTwoDesignWith (localBlock G x) 45 220 9 44 8 where
  point_card := firstSubconstituent_card G hG x
  block_card := secondSubconstituent_card G hG x
  block_size := localBlock_card G hG x
  replication_number z := by
    simpa [blocksThrough] using blocksThrough_card G hG x z
  pair_multiplicity := by
    intro z w hzw
    simpa [blocksThroughPair] using
      blocksThroughPair_card G hG x (z := z) (w := w) hzw

end SRG266
