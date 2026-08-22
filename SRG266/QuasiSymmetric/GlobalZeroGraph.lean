/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.GlobalDesignLaws

/-!
# The zero-intersection graph of a global residual design

A hypothetical global residual design has `165` blocks indexed by the triples
of an eleven-element set.  This file forgets the blocks and retains only the
graph in which two triples are adjacent when their blocks are disjoint.

The resulting object is substantially smaller than either a cherry cover or a
global design.  It is a triangle-free `24`-regular spanning subgraph of the
Kneser graph on the three-subsets of `Fin 11`.  Its common-neighbour numbers
are completely rigid:

* adjacent vertices have no common neighbour;
* nonadjacent distinct triples `T`, `U` have `3 + #(T ∩ U)` common neighbours.

Two further balance laws retain the labelled Johnson-scheme information used
by the finite search.  A vertex outside `T` occurs in nine neighbours of `T`,
whereas a vertex of `T` occurs in none.  For two vertices off `T`, either two
or three neighbours of `T` contain both.

These laws are packaged with the exact reduction

`IsEmpty GlobalZeroGraph → NoResidualCherryCover`.

-/

namespace SRG266.QuasiSymmetric

/-- The block-free finite object forced by a global residual design. -/
structure GlobalZeroGraph where
  /-- The zero-intersection neighbours of a triple. -/
  neighbours : Finset (Fin 11) → Finset (Finset (Fin 11))
  /-- Neighbours of a triple are triples. -/
  closed : ∀ {T}, T ∈ triples → ∀ {U}, U ∈ neighbours T → U ∈ triples
  /-- Zero intersection is a symmetric relation. -/
  symmetric : ∀ {T U}, T ∈ triples → U ∈ triples →
    (U ∈ neighbours T ↔ T ∈ neighbours U)
  /-- No block is disjoint from itself. -/
  loopless : ∀ {T}, T ∈ triples → T ∉ neighbours T
  /-- Every triple has exactly twenty-four zero-intersection neighbours. -/
  degree : ∀ {T}, T ∈ triples → (neighbours T).card = 24
  /-- Adjacent triples are disjoint as vertex sets. -/
  supported : ∀ {T U}, T ∈ triples → U ∈ neighbours T → (T ∩ U).card = 0
  /-- The complete common-neighbour law. -/
  common : ∀ {T U}, T ∈ triples → U ∈ triples → T ≠ U →
    (neighbours T ∩ neighbours U).card =
      if U ∈ neighbours T then 0 else (T ∩ U).card + 3
  /-- A vertex off `T` occurs in nine neighbours of `T`; a vertex of `T`
  occurs in none. -/
  vertex_balance : ∀ {T}, T ∈ triples → ∀ v,
    (neighbours T ∩ triplesAt v).card = if v ∈ T then 0 else 9
  /-- Two vertices off `T` occur together in either two or three neighbours
  of `T`. -/
  pair_balance : ∀ {T}, T ∈ triples → ∀ {v w : Fin 11}, v ≠ w → v ∉ T → w ∉ T →
    (neighbours T ∩ triplesThrough v w).card = 2 ∨
      (neighbours T ∩ triplesThrough v w).card = 3

namespace GlobalDesign

variable (G : GlobalDesign)

/-- Disjointness of two global blocks is symmetric. -/
theorem mem_disjointFrom_comm {T U : Finset (Fin 11)}
    (hT : T ∈ triples) (hU : U ∈ triples) :
    U ∈ G.disjointFrom T ↔ T ∈ G.disjointFrom U := by
  constructor
  · intro h
    obtain ⟨_, hzero⟩ := G.mem_disjointFrom.mp h
    exact G.mem_disjointFrom.mpr ⟨hT, by rwa [Finset.inter_comm]⟩
  · intro h
    obtain ⟨_, hzero⟩ := G.mem_disjointFrom.mp h
    exact G.mem_disjointFrom.mpr ⟨hU, by rwa [Finset.inter_comm]⟩

/-- Forget the edge blocks of a global design, retaining their exact
zero-intersection graph. -/
def toGlobalZeroGraph : GlobalZeroGraph where
  neighbours := G.disjointFrom
  closed := fun {_T : Finset (Fin 11)} (_hT : _T ∈ triples)
      {_U : Finset (Fin 11)} (hU : _U ∈ G.disjointFrom _T) =>
    (G.mem_disjointFrom.mp hU).1
  symmetric := @mem_disjointFrom_comm G
  loopless := fun {_T : Finset (Fin 11)} (hT : _T ∈ triples) =>
    G.notMem_disjointFrom_self hT
  degree := fun {_T : Finset (Fin 11)} (hT : _T ∈ triples) =>
    G.card_disjointFrom hT
  supported := fun {T U : Finset (Fin 11)} (hT : T ∈ triples)
      (hU : U ∈ G.disjointFrom T) => by
    obtain ⟨hUt, hzero⟩ := G.mem_disjointFrom.mp hU
    have hTU : T ≠ U := by
      intro h
      subst U
      exact G.notMem_disjointFrom_self hT hU
    exact G.triples_disjoint_of_block_disjoint hT hUt hTU hzero
  common := fun {T U : Finset (Fin 11)} (hT : T ∈ triples)
      (hU : U ∈ triples) (hTU : T ≠ U) => by
    rw [G.card_disjointFrom_inter hT hU hTU]
    have hiff : (G.block T ∩ G.block U).card = 0 ↔ U ∈ G.disjointFrom T := by
      rw [G.mem_disjointFrom]
      simp only [hU, true_and]
    by_cases hzero : (G.block T ∩ G.block U).card = 0
    · rw [if_pos hzero, if_pos (hiff.mp hzero)]
    · rw [if_neg hzero, if_neg (fun h => hzero (hiff.mpr h))]
  vertex_balance := fun {_T : Finset (Fin 11)} (hT : _T ∈ triples) v =>
    G.card_disjointFrom_inter_triplesAt hT v
  pair_balance := fun {_T : Finset (Fin 11)} (hT : _T ∈ triples)
      {v w : Fin 11} hvw hvT hwT => by
    have h := G.card_disjointFrom_inter_triplesThrough hT hvw hvT hwT
    split at h <;> omega

end GlobalDesign

/-- The pure finite statement that no rigid zero-intersection graph exists. -/
abbrev NoGlobalZeroGraph : Prop := IsEmpty GlobalZeroGraph

/-- Refuting the block-free zero graph refutes every global residual design. -/
theorem isEmpty_globalDesign_of_noGlobalZeroGraph
    (h : NoGlobalZeroGraph) : IsEmpty GlobalDesign :=
  ⟨fun G => h.elim G.toGlobalZeroGraph⟩

/-- Refuting the block-free zero graph discharges the cherry-cover boundary. -/
theorem noResidualCherryCover_of_noGlobalZeroGraph
    (h : NoGlobalZeroGraph) : NoResidualCherryCover :=
  noResidualCherryCover_of_isEmpty_globalDesign
    (isEmpty_globalDesign_of_noGlobalZeroGraph h)

/-- The same finite refutation eliminates the quasi-symmetric design. -/
theorem noQuasiSymmetricDesign56_of_noGlobalZeroGraph
    (h : NoGlobalZeroGraph) : NoQuasiSymmetricDesign56.{u} :=
  noQuasiSymmetricDesign56_of_noResidualCherryCover
    (noResidualCherryCover_of_noGlobalZeroGraph h)

end SRG266.QuasiSymmetric
