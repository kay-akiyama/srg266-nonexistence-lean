/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.IncidenceMatrix
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# The graph on the second subconstituent

This file defines `H = G[Γ₂(x)]` as an induced graph.  It proves that `H` is
36-regular and connects adjacency in `H` with disjointness of local blocks.
-/

open scoped Matrix

namespace SRG266

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The graph induced by `G` on the second subconstituent at `x`. -/
abbrev secondSubconstituentGraph (x : V) :
    SimpleGraph (SecondSubconstituent G x) :=
  G.induce (Gᶜ.neighborSet x)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem secondSubconstituentGraph_adj
    (x : V) (B C : SecondSubconstituent G x) :
    (secondSubconstituentGraph G x).Adj B C ↔ G.Adj (B : V) (C : V) :=
  Iff.rfl

/-- Inside the neighbor set of a second-subconstituent vertex, belonging to
the second subconstituent is the same as not being a common neighbor of the
root and that vertex. -/
theorem second_neighbor_inter_eq_sdiff_common
    (x : V) (B : SecondSubconstituent G x) :
    G.neighborFinset (B : V) ∩ (Gᶜ.neighborSet x).toFinset =
      G.neighborFinset (B : V) \ (G.commonNeighbors x (B : V)).toFinset := by
  ext z
  have hBx : ¬G.Adj (B : V) x :=
    (((G.compl_adj x B).mp B.property).2) ∘ G.adj_symm
  simp only [Finset.mem_inter, G.mem_neighborFinset, Set.mem_toFinset,
    Finset.mem_sdiff, G.mem_commonNeighbors]
  constructor
  · rintro ⟨hBz, hzSecond⟩
    have hz := (G.compl_adj x z).mp hzSecond
    exact ⟨hBz, fun h => hz.2 h.1⟩
  · rintro ⟨hBz, hnotCommon⟩
    have hnotxz : ¬G.Adj x z := fun hxz => hnotCommon ⟨hxz, hBz⟩
    have hxne : x ≠ z := by
      intro hxz
      subst z
      exact hBx hBz
    exact ⟨hBz, (G.compl_adj x z).mpr ⟨hxne, hnotxz⟩⟩

theorem secondSubconstituentGraph_degree
    (hG : IsHypothetical G) (x : V) (B : SecondSubconstituent G x) :
    (secondSubconstituentGraph G x).degree B = 36 := by
  have hmap := G.map_neighborFinset_induce B
  have hsubset :
      (G.commonNeighbors x (B : V)).toFinset ⊆ G.neighborFinset (B : V) := by
    intro z hz
    exact (G.mem_neighborFinset _ _).mpr ((G.mem_commonNeighbors).mp
      (Set.mem_toFinset.mp hz)).2
  have hB := (G.compl_adj x B).mp B.property
  calc
    (secondSubconstituentGraph G x).degree B =
        ((secondSubconstituentGraph G x).neighborFinset B).card :=
      ((secondSubconstituentGraph G x).card_neighborFinset_eq_degree B).symm
    _ = (((secondSubconstituentGraph G x).neighborFinset B).map
        (.subtype (· ∈ Gᶜ.neighborSet x))).card := (Finset.card_map _).symm
    _ = (G.neighborFinset (B : V) ∩ (Gᶜ.neighborSet x).toFinset).card :=
      congrArg Finset.card hmap
    _ = (G.neighborFinset (B : V) \
        (G.commonNeighbors x (B : V)).toFinset).card :=
      congrArg Finset.card (second_neighbor_inter_eq_sdiff_common G x B)
    _ = (G.neighborFinset (B : V)).card -
        (G.commonNeighbors x (B : V)).toFinset.card :=
      Finset.card_sdiff_of_subset hsubset
    _ = 36 := by
      rw [G.card_neighborFinset_eq_degree, Set.toFinset_card, hG.regular B,
        hG.of_not_adj hB.1 hB.2]

theorem secondSubconstituentGraph_regular
    (hG : IsHypothetical G) (x : V) :
    (secondSubconstituentGraph G x).IsRegularOfDegree 36 :=
  secondSubconstituentGraph_degree G hG x

/-- The forward map in the common-neighbor decomposition. -/
def commonNeighborsDecompositionTo
    (x : V) (B C : SecondSubconstituent G x) :
    G.commonNeighbors (B : V) (C : V) →
      Sum ↥(localBlock G x B ∩ localBlock G x C)
        ((secondSubconstituentGraph G x).commonNeighbors B C) := fun z => by
  by_cases hxz : G.Adj x (z : V)
  · exact Sum.inl
      ⟨⟨z, hxz⟩, Finset.mem_inter.mpr
        ⟨(mem_localBlock G x B ⟨z, hxz⟩).mpr z.property.1.symm,
          (mem_localBlock G x C ⟨z, hxz⟩).mpr z.property.2.symm⟩⟩
  · have hxne : x ≠ (z : V) := by
      intro hxzEq
      have hxB : ¬G.Adj x (B : V) := ((G.compl_adj x B).mp B.property).2
      apply hxB
      simpa [hxzEq] using z.property.1.symm
    let y : SecondSubconstituent G x :=
      ⟨z, (G.compl_adj x z).mpr ⟨hxne, hxz⟩⟩
    exact Sum.inr ⟨y, z.property⟩

/-- The inverse map in the common-neighbor decomposition. -/
def commonNeighborsDecompositionInv
    (x : V) (B C : SecondSubconstituent G x) :
    Sum ↥(localBlock G x B ∩ localBlock G x C)
        ((secondSubconstituentGraph G x).commonNeighbors B C) →
      G.commonNeighbors (B : V) (C : V)
  | Sum.inl p =>
      ⟨p.1, ⟨(mem_localBlock G x B p.1).mp
        (Finset.mem_inter.mp p.property).1 |>.symm,
        (mem_localBlock G x C p.1).mp
          (Finset.mem_inter.mp p.property).2 |>.symm⟩⟩
  | Sum.inr y => ⟨y.1, y.property⟩

/-- Every common neighbor of two second-subconstituent vertices lies either in
the first subconstituent (and hence in the block intersection) or in the
second subconstituent. -/
def commonNeighborsDecomposition
    (x : V) (B C : SecondSubconstituent G x) :
    G.commonNeighbors (B : V) (C : V) ≃
      Sum ↥(localBlock G x B ∩ localBlock G x C)
        ((secondSubconstituentGraph G x).commonNeighbors B C) where
  toFun := commonNeighborsDecompositionTo G x B C
  invFun := commonNeighborsDecompositionInv G x B C
  left_inv z := by
    apply Subtype.ext
    by_cases hxz : G.Adj x (z : V)
    · simp [commonNeighborsDecompositionTo, commonNeighborsDecompositionInv, hxz]
    · simp [commonNeighborsDecompositionTo, commonNeighborsDecompositionInv, hxz]
  right_inv s := by
    cases s with
    | inl p =>
        have hp : G.Adj x (p.1 : V) := p.1.property
        simp [commonNeighborsDecompositionTo, commonNeighborsDecompositionInv, hp]
    | inr y =>
        have hxy : ¬G.Adj x (y : V) := ((G.compl_adj x y).mp y.1.property).2
        simp [commonNeighborsDecompositionTo, commonNeighborsDecompositionInv, hxy]

theorem card_commonNeighbors_decomposition
    (x : V) (B C : SecondSubconstituent G x) :
    Fintype.card (G.commonNeighbors (B : V) (C : V)) =
      blockIntersection G x B C +
        Fintype.card ((secondSubconstituentGraph G x).commonNeighbors B C) := by
  calc
    Fintype.card (G.commonNeighbors (B : V) (C : V)) =
        Fintype.card
          (Sum ↥(localBlock G x B ∩ localBlock G x C)
            ((secondSubconstituentGraph G x).commonNeighbors B C)) :=
      Fintype.card_congr (commonNeighborsDecomposition G x B C)
    _ = Fintype.card ↥(localBlock G x B ∩ localBlock G x C) +
        Fintype.card ((secondSubconstituentGraph G x).commonNeighbors B C) := by
      rw [Fintype.card_sum]
    _ = blockIntersection G x B C +
        Fintype.card ((secondSubconstituentGraph G x).commonNeighbors B C) := by
      rw [Fintype.card_coe]
      rfl

theorem card_second_commonNeighbors_of_not_adj
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x} (hne : B ≠ C)
    (hBC : ¬(secondSubconstituentGraph G x).Adj B C) :
    Fintype.card ((secondSubconstituentGraph G x).commonNeighbors B C) =
      9 - blockIntersection G x B C := by
  have hval : (B : V) ≠ (C : V) := fun h => hne (Subtype.ext h)
  have hGBC : ¬G.Adj (B : V) (C : V) := hBC
  have htotal := hG.of_not_adj hval hGBC
  have hdecomp := card_commonNeighbors_decomposition G x B C
  omega

/-- The integral adjacency matrix `H` of the second subconstituent. -/
def localAdjacencyMatrix (x : V) :
    Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ :=
  (secondSubconstituentGraph G x).adjMatrix ℤ

@[simp]
theorem localAdjacencyMatrix_mulVec_one
    (hG : IsHypothetical G) (x : V) :
    localAdjacencyMatrix G x *ᵥ (1 : SecondSubconstituent G x → ℤ) = 36 := by
  funext B
  simpa [localAdjacencyMatrix] using
    (secondSubconstituentGraph G x).adjMatrix_mulVec_const_apply_of_regular
      (secondSubconstituentGraph_regular G hG x) (a := (1 : ℤ)) (v := B)

theorem localAdjacencyMatrix_sq_apply_card_commonNeighbors
    (x : V) (B C : SecondSubconstituent G x) :
    (localAdjacencyMatrix G x * localAdjacencyMatrix G x) B C =
      Fintype.card ((secondSubconstituentGraph G x).commonNeighbors B C) := by
  rw [Matrix.mul_apply]
  simp only [localAdjacencyMatrix, SimpleGraph.adjMatrix_apply, ite_zero_mul_ite_zero,
    one_mul, Finset.sum_boole]
  norm_cast
  rw [← Set.toFinset_card]
  apply congrArg Finset.card
  ext D
  simp [SimpleGraph.mem_commonNeighbors, SimpleGraph.adj_comm]

omit [DecidableEq V] in
/-- Adjacent vertices of the second subconstituent give disjoint local
blocks, because adjacent vertices in the SRG have no common neighbor. -/
theorem localBlock_disjoint_of_adj
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x}
    (hBC : (secondSubconstituentGraph G x).Adj B C) :
    Disjoint (localBlock G x B) (localBlock G x C) := by
  rw [Finset.disjoint_left]
  intro p hpB hpC
  have hcard : Fintype.card (G.commonNeighbors (B : V) (C : V)) = 0 :=
    hG.of_adj B C hBC
  letI : IsEmpty (G.commonNeighbors (B : V) (C : V)) :=
    Fintype.card_eq_zero_iff.mp hcard
  exact isEmptyElim
    (⟨p, (mem_localBlock G x B p).mp hpB |>.symm,
      (mem_localBlock G x C p).mp hpC |>.symm⟩ :
        G.commonNeighbors (B : V) (C : V))

theorem blockIntersection_of_adj
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x}
    (hBC : (secondSubconstituentGraph G x).Adj B C) :
    blockIntersection G x B C = 0 := by
  rw [blockIntersection, Finset.card_eq_zero]
  exact Finset.disjoint_iff_inter_eq_empty.mp (localBlock_disjoint_of_adj G hG x hBC)

theorem localIntersectionMatrix_of_adj
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x}
    (hBC : (secondSubconstituentGraph G x).Adj B C) :
    localIntersectionMatrix G x B C = 0 := by
  rw [localIntersectionMatrix_apply, blockIntersection_of_adj G hG x hBC]
  norm_num

theorem blockIntersection_le_nine
    (hG : IsHypothetical G) (x : V) (B C : SecondSubconstituent G x) :
    blockIntersection G x B C ≤ 9 := by
  calc
    blockIntersection G x B C =
        (localBlock G x B ∩ localBlock G x C).card := rfl
    _ ≤ (localBlock G x B).card :=
      Finset.card_le_card Finset.inter_subset_left
    _ = 9 := localBlock_card G hG x B

theorem localAdjacencyMatrix_sq_apply
    (hG : IsHypothetical G) (x : V) (B C : SecondSubconstituent G x) :
    (localAdjacencyMatrix G x * localAdjacencyMatrix G x) B C =
      if B = C then 36
      else if (secondSubconstituentGraph G x).Adj B C then 0
      else 9 - (blockIntersection G x B C : ℤ) := by
  by_cases hEq : B = C
  · subst C
    rw [if_pos rfl]
    calc
      (localAdjacencyMatrix G x * localAdjacencyMatrix G x) B B =
          (secondSubconstituentGraph G x).degree B := by
        simpa [localAdjacencyMatrix] using
          (secondSubconstituentGraph G x).adjMatrix_mul_self_apply_self (α := ℤ) B
      _ = 36 := by exact_mod_cast secondSubconstituentGraph_degree G hG x B
  · rw [if_neg hEq]
    by_cases hBC : (secondSubconstituentGraph G x).Adj B C
    · rw [if_pos hBC, localAdjacencyMatrix_sq_apply_card_commonNeighbors]
      have htotal :
          Fintype.card (G.commonNeighbors (B : V) (C : V)) = 0 :=
        hG.of_adj B C hBC
      have hdecomp := card_commonNeighbors_decomposition G x B C
      norm_cast
      omega
    · rw [if_neg hBC, localAdjacencyMatrix_sq_apply_card_commonNeighbors,
        card_second_commonNeighbors_of_not_adj G hG x hEq hBC]
      rw [Nat.cast_sub (blockIntersection_le_nine G hG x B C)]
      norm_num

/-- The concrete `H²` identity, expressed entrywise to avoid ambiguity about
scalar actions on square matrices. -/
theorem localAdjacencyMatrix_sq
    (hG : IsHypothetical G) (x : V) :
    localAdjacencyMatrix G x * localAdjacencyMatrix G x =
      fun B C =>
        (if B = C then (36 : ℤ) else 0) + 9 -
          localIntersectionMatrix G x B C -
          if (secondSubconstituentGraph G x).Adj B C then 9 else 0 := by
  ext B C
  rw [localAdjacencyMatrix_sq_apply G hG x B C]
  by_cases hEq : B = C
  · subst C
    simp [localIntersectionMatrix_diagonal G hG x B]
  · rw [if_neg hEq]
    by_cases hBC : (secondSubconstituentGraph G x).Adj B C
    · rw [if_pos hBC, localIntersectionMatrix_of_adj G hG x hBC]
      have hGBC : G.Adj (B : V) (C : V) := hBC
      simp [hEq, hGBC]
    · rw [if_neg hBC, localIntersectionMatrix_apply]
      have hGBC : ¬G.Adj (B : V) (C : V) := hBC
      simp [hEq, hGBC]

end SRG266
