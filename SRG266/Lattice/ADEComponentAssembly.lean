/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.ADEBlockCoordinates
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Assembly of connected ADE components

This file upgrades the connected Cartan-graph classifier to arbitrary finite
positive Cartan graphs.  The connected components are listed once, their ADE
coordinates are concatenated, and the resulting coordinate equivalence is
proved to transport the whole graph Cartan matrix to `adeGram`.
-/

namespace SRG266
namespace Lattice

open Function Set SimpleGraph

variable {V : Type*}

section ComponentBlocks

variable (G : SimpleGraph V)
variable (typeOf : G.ConnectedComponent → ADEType)
variable (coord : ∀ c : G.ConnectedComponent, Fin (typeOf c).rank ≃ c)

/-- Evaluate recursive component coordinates as an ambient graph vertex. -/
def componentBlockToVertex : (cs : List G.ConnectedComponent) →
    ADEBlockIndex (cs.map typeOf) → V
  | [], i => nomatch i
  | c :: _, Sum.inl i => (coord c i).1
  | _ :: cs, Sum.inr i => componentBlockToVertex cs i

/-- The component of a recursive block coordinate occurs in its component
list. -/
theorem connectedComponentMk_componentBlockToVertex :
    ∀ (cs : List G.ConnectedComponent) (i : ADEBlockIndex (cs.map typeOf)),
      G.connectedComponentMk (componentBlockToVertex G typeOf coord cs i) ∈ cs
  | [], i => nomatch i
  | c :: cs, Sum.inl i => by
      simp only [componentBlockToVertex, List.mem_cons]
      left
      exact (ConnectedComponent.mem_supp_iff c (coord c i).1).mp (coord c i).2
  | c :: cs, Sum.inr i => by
      simp only [componentBlockToVertex, List.mem_cons]
      exact Or.inr (connectedComponentMk_componentBlockToVertex cs i)

/-- Distinct entries in a component list give disjoint coordinate blocks. -/
theorem componentBlockToVertex_injective :
    ∀ {cs : List G.ConnectedComponent}, cs.Nodup →
      Function.Injective (componentBlockToVertex G typeOf coord cs)
  | [], _, i, _ => nomatch i
  | c :: cs, hnodup, i, j => by
      have hcnot : c ∉ cs := (List.nodup_cons.mp hnodup).1
      have htail : cs.Nodup := (List.nodup_cons.mp hnodup).2
      cases i with
      | inl i =>
          cases j with
          | inl j =>
              intro hij
              have hcoord : coord c i = coord c j := Subtype.ext hij
              have : i = j := (coord c).injective hcoord
              subst j
              rfl
          | inr j =>
              intro hij
              have hcomp := congrArg G.connectedComponentMk hij
              have hleft : G.connectedComponentMk (coord c i).1 = c :=
                (ConnectedComponent.mem_supp_iff c (coord c i).1).mp (coord c i).2
              have hright : G.connectedComponentMk
                  (componentBlockToVertex G typeOf coord cs j) ∈ cs :=
                connectedComponentMk_componentBlockToVertex G typeOf coord cs j
              exact (hcnot (hleft ▸ hcomp ▸ hright)).elim
      | inr i =>
          cases j with
          | inl j =>
              intro hij
              have hcomp := congrArg G.connectedComponentMk hij
              have hleft : G.connectedComponentMk
                  (componentBlockToVertex G typeOf coord cs i) ∈ cs :=
                connectedComponentMk_componentBlockToVertex G typeOf coord cs i
              have hright : G.connectedComponentMk (coord c j).1 = c :=
                (ConnectedComponent.mem_supp_iff c (coord c j).1).mp (coord c j).2
              exact (hcnot (hright ▸ hcomp.symm ▸ hleft)).elim
          | inr j =>
              intro hij
              have : i = j := componentBlockToVertex_injective htail hij
              subst j
              rfl

/-- A vertex whose component occurs in the list has a recursive block
coordinate. -/
theorem exists_componentBlockToVertex_eq :
    ∀ (cs : List G.ConnectedComponent) (v : V),
      G.connectedComponentMk v ∈ cs →
        ∃ i : ADEBlockIndex (cs.map typeOf),
          componentBlockToVertex G typeOf coord cs i = v
  | [], _, h => by simp at h
  | c :: cs, v, h => by
      rw [List.mem_cons] at h
      rcases h with h | h
      · have hv : v ∈ c := (ConnectedComponent.mem_supp_iff c v).mpr h
        obtain ⟨i, hi⟩ := (coord c).surjective ⟨v, hv⟩
        exact ⟨Sum.inl i, congrArg Subtype.val hi⟩
      · obtain ⟨i, hi⟩ := exists_componentBlockToVertex_eq cs v h
        exact ⟨Sum.inr i, hi⟩

/-- Listing every component makes recursive block evaluation surjective. -/
theorem componentBlockToVertex_surjective
    (cs : List G.ConnectedComponent)
    (hcover : ∀ c : G.ConnectedComponent, c ∈ cs) :
    Function.Surjective (componentBlockToVertex G typeOf coord cs) := by
  intro v
  exact exists_componentBlockToVertex_eq G typeOf coord cs v
    (hcover (G.connectedComponentMk v))

/-- Recursive component coordinates are equivalent to the ambient vertices
when the component list is duplicate-free and exhaustive. -/
noncomputable def componentBlockEquiv
    (cs : List G.ConnectedComponent) (hnodup : cs.Nodup)
    (hcover : ∀ c : G.ConnectedComponent, c ∈ cs) :
    ADEBlockIndex (cs.map typeOf) ≃ V :=
  Equiv.ofBijective (componentBlockToVertex G typeOf coord cs)
    ⟨componentBlockToVertex_injective G typeOf coord hnodup,
      componentBlockToVertex_surjective G typeOf coord cs hcover⟩

@[simp]
theorem componentBlockEquiv_apply
    (cs : List G.ConnectedComponent) (hnodup : cs.Nodup)
    (hcover : ∀ c : G.ConnectedComponent, c ∈ cs)
    (i : ADEBlockIndex (cs.map typeOf)) :
    componentBlockEquiv G typeOf coord cs hnodup hcover i =
      componentBlockToVertex G typeOf coord cs i :=
  rfl

/-- The ambient Cartan entry between two vertices of one component is the
Cartan entry in the induced component graph. -/
theorem graphCartanMatrix_component
    (c : G.ConnectedComponent) (u v : c) :
    graphCartanMatrix G u.1 v.1 = graphCartanMatrix c.toSimpleGraph u v := by
  classical
  by_cases huv : u = v
  · subst v
    rw [graphCartanMatrix_apply_same, graphCartanMatrix_apply_same]
  · have huvval : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
    by_cases hadj : G.Adj u.1 v.1
    · have hcadj : c.toSimpleGraph.Adj u v :=
        (ConnectedComponent.toSimpleGraph_adj c u.2 v.2).mpr hadj
      rw [graphCartanMatrix_apply_of_adj hadj,
        graphCartanMatrix_apply_of_adj hcadj]
    · have hcnot : ¬c.toSimpleGraph.Adj u v := fun h =>
        hadj ((ConnectedComponent.toSimpleGraph_adj c u.2 v.2).mp h)
      rw [graphCartanMatrix_apply_of_not_adj huvval hadj,
        graphCartanMatrix_apply_of_not_adj huv hcnot]

/-- Vertices belonging to different connected components have Cartan entry
zero. -/
theorem graphCartanMatrix_eq_zero_of_components_ne
    {u v : V} (huv : G.connectedComponentMk u ≠ G.connectedComponentMk v) :
    graphCartanMatrix G u v = 0 := by
  apply graphCartanMatrix_apply_of_not_adj
  · intro h
    exact huv (congrArg G.connectedComponentMk h)
  · intro h
    exact huv (ConnectedComponent.connectedComponentMk_eq_of_adj h)

/-- Componentwise ADE Gram identities assemble to the recursive block Gram
identity. -/
theorem graphCartanMatrix_componentBlock :
    ∀ (cs : List G.ConnectedComponent), cs.Nodup →
      (∀ c i j, graphCartanMatrix c.toSimpleGraph (coord c i) (coord c j) =
        (typeOf c).gram i j) →
      ∀ i j : ADEBlockIndex (cs.map typeOf),
        graphCartanMatrix G
            (componentBlockToVertex G typeOf coord cs i)
            (componentBlockToVertex G typeOf coord cs j) =
          adeBlockPairing (cs.map typeOf) i j
  | [], _, _, i, _ => nomatch i
  | c :: cs, hnodup, hgram, i, j => by
      have hcnot : c ∉ cs := (List.nodup_cons.mp hnodup).1
      have htail : cs.Nodup := (List.nodup_cons.mp hnodup).2
      cases i with
      | inl i =>
          cases j with
          | inl j =>
              change graphCartanMatrix G (coord c i).1 (coord c j).1 = _
              rw [graphCartanMatrix_component G c (coord c i) (coord c j), hgram]
              rfl
          | inr j =>
              change graphCartanMatrix G (coord c i).1
                (componentBlockToVertex G typeOf coord cs j) = 0
              apply graphCartanMatrix_eq_zero_of_components_ne G
              have hleft : G.connectedComponentMk (coord c i).1 = c :=
                (ConnectedComponent.mem_supp_iff c (coord c i).1).mp (coord c i).2
              have hright : G.connectedComponentMk
                  (componentBlockToVertex G typeOf coord cs j) ∈ cs :=
                connectedComponentMk_componentBlockToVertex G typeOf coord cs j
              intro heq
              exact hcnot (hleft ▸ heq ▸ hright)
      | inr i =>
          cases j with
          | inl j =>
              change graphCartanMatrix G
                (componentBlockToVertex G typeOf coord cs i) (coord c j).1 = 0
              apply graphCartanMatrix_eq_zero_of_components_ne G
              have hleft : G.connectedComponentMk
                  (componentBlockToVertex G typeOf coord cs i) ∈ cs :=
                connectedComponentMk_componentBlockToVertex G typeOf coord cs i
              have hright : G.connectedComponentMk (coord c j).1 = c :=
                (ConnectedComponent.mem_supp_iff c (coord c j).1).mp (coord c j).2
              intro heq
              exact hcnot (hright ▸ heq.symm ▸ hleft)
          | inr j =>
              exact graphCartanMatrix_componentBlock cs htail hgram i j

end ComponentBlocks

/-! ## ADE data for each connected component -/

section PositiveGraph

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable instance connectedComponentVertexFintype
    (c : G.ConnectedComponent) : Fintype c :=
  Fintype.ofFinite c

/-- Each component of a positive Cartan graph is a connected positive Cartan
graph and therefore has explicit ADE coordinates. -/
theorem connectedComponent_hasADECoordinates
    (hpos : IsPositiveCartan G) (hcard : Fintype.card V ≤ 15)
    (c : G.ConnectedComponent) : ConnectedADECoordinates c.toSimpleGraph := by
  classical
  let e : c ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hcpos : IsPositiveCartan c.toSimpleGraph := by
    change IsPositiveCartan (G.comap e)
    exact hpos.comap e
  have hccard : Fintype.card c ≤ 15 := by
    exact (Fintype.card_le_of_injective (fun x : c => x.1) Subtype.val_injective).trans hcard
  exact positiveCartan_connected_ADE hcpos c.connected_toSimpleGraph hccard

/-- The ADE type chosen for one connected component. -/
noncomputable def componentADEType
    (hpos : IsPositiveCartan G) (hcard : Fintype.card V ≤ 15)
    (c : G.ConnectedComponent) : ADEType :=
  (connectedComponent_hasADECoordinates G hpos hcard c).choose

/-- The rank of the chosen ADE type is the size of the component. -/
theorem componentADEType_rank
    (hpos : IsPositiveCartan G) (hcard : Fintype.card V ≤ 15)
    (c : G.ConnectedComponent) :
    (componentADEType G hpos hcard c).rank = Fintype.card c :=
  (connectedComponent_hasADECoordinates G hpos hcard c).choose_spec.2.1

/-- Every component classifier returns a genuine ADE type. -/
theorem componentADEType_isRegular
    (hpos : IsPositiveCartan G) (hcard : Fintype.card V ≤ 15)
    (c : G.ConnectedComponent) :
    (componentADEType G hpos hcard c).IsRegular :=
  (connectedComponent_hasADECoordinates G hpos hcard c).choose_spec.1

/-- Coordinates for the chosen ADE type of one component. -/
noncomputable def componentADECoord
    (hpos : IsPositiveCartan G) (hcard : Fintype.card V ≤ 15)
    (c : G.ConnectedComponent) :
    Fin (componentADEType G hpos hcard c).rank ≃ c :=
  (connectedComponent_hasADECoordinates G hpos hcard c).choose_spec.2.2.choose

/-- The chosen component coordinates transport its Cartan matrix to the
standard ADE Gram matrix. -/
theorem componentADECoord_gram
    (hpos : IsPositiveCartan G) (hcard : Fintype.card V ≤ 15)
    (c : G.ConnectedComponent)
    (i j : Fin (componentADEType G hpos hcard c).rank) :
    graphCartanMatrix c.toSimpleGraph
        (componentADECoord G hpos hcard c i)
        (componentADECoord G hpos hcard c j) =
      (componentADEType G hpos hcard c).gram i j :=
  (connectedComponent_hasADECoordinates G hpos hcard c).choose_spec.2.2.choose_spec i j

end PositiveGraph

/-! ## The disconnected classification -/

/-- Coordinate-level ADE classification of a finite, not necessarily
connected, Cartan graph. -/
def ADECoordinates [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ ts : List ADEType, (∀ t ∈ ts, t.IsRegular) ∧
    ADEType.rankSum ts = Fintype.card V ∧
    ∃ coord : Fin (ADEType.rankSum ts) ≃ V, ∀ i j,
      graphCartanMatrix G (coord i) (coord j) = (adeGram ts).2 i j

/-- Every positive simply-laced Cartan graph of rank at most fifteen is an
orthogonal sum of ADE Cartan matrices, with explicit coordinates. -/
theorem positiveCartan_ADECoordinates
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hpos : IsPositiveCartan G) (hcard : Fintype.card V ≤ 15) :
    ADECoordinates G := by
  classical
  let typeOf : G.ConnectedComponent → ADEType :=
    componentADEType G hpos hcard
  let coordOf : ∀ c : G.ConnectedComponent, Fin (typeOf c).rank ≃ c :=
    componentADECoord G hpos hcard
  let cs : List G.ConnectedComponent := Finset.univ.toList
  let ts : List ADEType := cs.map typeOf
  have hnodup : cs.Nodup := by
    exact Finset.nodup_toList Finset.univ
  have hcover : ∀ c : G.ConnectedComponent, c ∈ cs := by
    intro c
    simp [cs]
  let blockEquiv : ADEBlockIndex ts ≃ V :=
    componentBlockEquiv G typeOf coordOf cs hnodup hcover
  let totalEquiv : Fin (ADEType.rankSum ts) ≃ V :=
    (finADEBlockEquiv ts).trans blockEquiv
  refine ⟨ts, ?_, ?_, totalEquiv, ?_⟩
  · intro t ht
    rw [List.mem_map] at ht
    obtain ⟨c, _, rfl⟩ := ht
    exact componentADEType_isRegular G hpos hcard c
  · have hcardEquiv := Fintype.card_congr totalEquiv
    simpa using hcardEquiv
  · intro i j
    change graphCartanMatrix G
      (componentBlockToVertex G typeOf coordOf cs (finADEBlockEquiv ts i))
      (componentBlockToVertex G typeOf coordOf cs (finADEBlockEquiv ts j)) = _
    calc
      _ = adeBlockPairing ts (finADEBlockEquiv ts i) (finADEBlockEquiv ts j) := by
        apply graphCartanMatrix_componentBlock G typeOf coordOf cs hnodup
        intro c a b
        exact componentADECoord_gram G hpos hcard c a b
      _ = (adeGram ts).2 i j :=
        (adeGram_apply_eq_adeBlockPairing ts i j).symm

end Lattice
end SRG266
