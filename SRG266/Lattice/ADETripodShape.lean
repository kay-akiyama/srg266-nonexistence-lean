/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.ADEPathShape

/-!
# The three branches at a trivalent vertex

Removing a vertex from a tree separates its neighbours into distinct connected
components, and every remaining component contains a neighbour.  This file
proves the resulting equivalence.  It is the structural bridge from an
abstract positive Cartan graph to the three arms used in the ADE inequality.
-/

namespace SRG266
namespace Lattice

open SimpleGraph

variable {V : Type*}

/-- The connected component, after deleting `z`, that contains a neighbour of
`z`. -/
noncomputable def puncturedNeighborComponent (G : SimpleGraph V) (z : V)
    (w : G.neighborSet z) :
    (G.induce {x | x ≠ z}).ConnectedComponent :=
  (G.induce {x | x ≠ z}).connectedComponentMk
    ⟨w.1, w.2.ne'⟩

/-- Distinct neighbours of a vertex in a forest lie in distinct components
after that vertex is deleted. -/
theorem puncturedNeighborComponent_injective {G : SimpleGraph V} {z : V}
    (hacyc : G.IsAcyclic) :
    Function.Injective (puncturedNeighborComponent G z) := by
  classical
  intro a b hab
  apply Subtype.ext
  by_contra habv
  let S : Set V := {x | x ≠ z}
  let R : SimpleGraph S := G.induce S
  let av : S := ⟨a.1, a.2.ne'⟩
  let bv : S := ⟨b.1, b.2.ne'⟩
  have hcomp : R.connectedComponentMk av = R.connectedComponentMk bv := by
    exact hab
  have hreach : R.Reachable av bv := ConnectedComponent.exact hcomp
  let q : R.Path av bv := hreach.some.toPath
  let incl : R →g G :=
    { toFun := Subtype.val
      map_rel' := fun h ↦ h }
  let qG : G.Walk a.1 b.1 := (q.1.map incl).copy rfl rfl
  have hqG : qG.IsPath := by
    change ((q.1.map incl).copy rfl rfl).IsPath
    rw [Walk.isPath_copy]
    exact q.2.map (f := incl) Subtype.val_injective
  let p0 : G.Walk a.1 a.1 := Walk.nil
  let p1 : G.Walk a.1 z := p0.concat a.2.symm
  let p2 : G.Walk a.1 b.1 := p1.concat b.2
  have hp0 : p0.IsPath := by simp [p0]
  have hp1 : p1.IsPath := by
    apply hp0.concat
    simp [p0, a.2.ne]
  have hp2 : p2.IsPath := by
    apply hp1.concat
    simp only [p1, p0, Walk.support_concat, Walk.support_nil,
      List.mem_append, List.mem_singleton]
    intro hb
    rcases hb with hb | hb
    · exact habv hb.symm
    · exact b.2.ne' hb
  have hpq : qG = p2 :=
    Subtype.mk.inj (hacyc.path_unique ⟨qG, hqG⟩ ⟨p2, hp2⟩)
  have hzq : z ∉ qG.support := by
    simp only [qG, Walk.support_copy, Walk.support_map, incl, List.mem_map,
      not_exists, not_and]
    intro x _ hx
    exact x.2 hx
  have hzp : z ∈ p2.support := by
    simp [p2, p1, p0]
  exact hzq (hpq.symm ▸ hzp)

/-- Every component left after deleting a vertex from a connected graph
contains a neighbour of the deleted vertex. -/
theorem puncturedNeighborComponent_surjective {G : SimpleGraph V} {z : V}
    (hconn : G.Connected) :
    Function.Surjective (puncturedNeighborComponent G z) := by
  classical
  intro C
  let x : {v : V // v ≠ z} := C.out
  have hzx : z ≠ x.1 := Ne.symm x.2
  obtain ⟨p, hp⟩ := hconn.exists_isPath z x.1
  have hp_ne : ¬ p.Nil := Walk.not_nil_of_ne hzx
  have hadj : G.Adj z p.snd := p.adj_snd hp_ne
  let w : G.neighborSet z := ⟨p.snd, hadj⟩
  have htail_mem : ∀ y ∈ p.tail.support, y ≠ z := by
    intro y hy hyz
    subst y
    have hnodup := hp.support_nodup
    rw [← p.cons_support_tail hp_ne] at hnodup
    exact (List.nodup_cons.mp hnodup).1 hy
  let q := p.tail.induce {v : V | v ≠ z} htail_mem
  have hreach : (G.induce {v : V | v ≠ z}).Reachable
      ⟨p.snd, hadj.ne'⟩ x := by
    refine ⟨q.copy ?_ ?_⟩
    · rfl
    · exact Subtype.ext rfl
  refine ⟨w, ?_⟩
  dsimp only [puncturedNeighborComponent, w]
  calc
    _ = (G.induce {v : V | v ≠ z}).connectedComponentMk x :=
      ConnectedComponent.sound hreach
    _ = C := C.out_eq

/-- For a tree, the neighbours of `z` are in bijection with the connected
components remaining after `z` is deleted. -/
noncomputable def neighborEquivPuncturedComponents {G : SimpleGraph V} {z : V}
    (htree : G.IsTree) :
    G.neighborSet z ≃ (G.induce {x | x ≠ z}).ConnectedComponent :=
  Equiv.ofBijective (puncturedNeighborComponent G z)
    ⟨puncturedNeighborComponent_injective htree.isAcyclic,
      puncturedNeighborComponent_surjective htree.connected⟩

/-- The unique neighbour of `z` lying in a given component of the punctured
tree. -/
noncomputable def puncturedComponentNeighbor {G : SimpleGraph V} {z : V}
    (htree : G.IsTree)
    (C : (G.induce {x | x ≠ z}).ConnectedComponent) : G.neighborSet z :=
  (neighborEquivPuncturedComponents htree).symm C

/-- The punctured-graph vertex represented by
`puncturedComponentNeighbor`. -/
noncomputable def puncturedComponentRoot {G : SimpleGraph V} {z : V}
    (htree : G.IsTree)
    (C : (G.induce {x | x ≠ z}).ConnectedComponent) : C := by
  let w := puncturedComponentNeighbor htree C
  have hw : G.Adj z w.1 := w.2
  refine ⟨⟨w.1, hw.ne'⟩, ?_⟩
  change (G.induce {x | x ≠ z}).connectedComponentMk
    ⟨w.1, hw.ne'⟩ = C
  have h := (neighborEquivPuncturedComponents htree).apply_symm_apply C
  exact h

/-- After the unique trivalent vertex of a positive Cartan tree is removed,
each connected component has standard `A` coordinates. -/
theorem puncturedComponent_exists_A_coordinates
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hpos : IsPositiveCartan G) (hconn : G.Connected)
    (hcard : Fintype.card V ≤ 15) {z : V} (hz : G.degree z = 3)
    (C : (G.induce {x | x ≠ z}).ConnectedComponent) [Fintype C] :
    ∃ (e : Fin (Fintype.card C) ≃ C), ∀ i j,
      graphCartanMatrix C.toSimpleGraph (e i) (e j) =
        gramA (Fintype.card C) i j := by
  classical
  have hacyc : G.IsAcyclic := hpos.isAcyclic
  have htreeC : C.toSimpleGraph.IsTree :=
    (hacyc.induce {x | x ≠ z}).isTree_connectedComponent C
  have hdegC : ∀ x, C.toSimpleGraph.degree x ≤ 2 := by
    intro x
    have hx_ne : x.1.1 ≠ z := x.1.2
    have hx_le : G.degree x.1.1 ≤ 3 := hpos.degree_le_three x.1.1
    have hx_not_three : G.degree x.1.1 ≠ 3 := by
      intro hx
      exact hx_ne (hpos.eq_of_degree_eq_three hconn hcard hx hz)
    have hxG : G.degree x.1.1 ≤ 2 := by omega
    let emb : C.toSimpleGraph.neighborSet x ↪ G.neighborSet x.1.1 :=
      ⟨fun y ↦ ⟨y.1.1.1, y.2⟩, by
        intro a b hab
        have hv : a.1.1.1 = b.1.1.1 :=
          congr_arg (fun y : G.neighborSet x.1.1 ↦ y.1) hab
        exact Subtype.ext (Subtype.ext (Subtype.ext hv))⟩
    have hle := Fintype.card_le_of_embedding emb
    rw [SimpleGraph.card_neighborSet_eq_degree,
      SimpleGraph.card_neighborSet_eq_degree] at hle
    exact hle.trans hxG
  exact exists_A_coordinates_of_degree_le_two
    htreeC.connected htreeC.isAcyclic hdegC

/-- The path coordinates of a punctured component can be oriented so that
coordinate zero is the unique vertex adjacent to the deleted centre. -/
theorem puncturedComponent_exists_oriented_path_iso
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hpos : IsPositiveCartan G) (hconn : G.Connected)
    (hcard : Fintype.card V ≤ 15) {z : V} (hz : G.degree z = 3)
    (C : (G.induce {x | x ≠ z}).ConnectedComponent) [Fintype C] :
    ∃ (e : pathGraph (Fintype.card C) ≃g C.toSimpleGraph)
      (i : Fin (Fintype.card C)),
      i.1 = 0 ∧ e i = puncturedComponentRoot ⟨hconn, hpos.isAcyclic⟩ C := by
  classical
  let htree : G.IsTree := ⟨hconn, hpos.isAcyclic⟩
  let root : C := puncturedComponentRoot htree C
  let w : G.neighborSet z := puncturedComponentNeighbor htree C
  have hroot_val : root.1.1 = w.1 := by
    simp only [root, w, puncturedComponentRoot]
  have hw_ne : w.1 ≠ z := w.2.ne'
  have hw_le : G.degree w.1 ≤ 3 := hpos.degree_le_three w.1
  have hw_not_three : G.degree w.1 ≠ 3 := by
    intro hw3
    exact hw_ne (hpos.eq_of_degree_eq_three hconn hcard hw3 hz)
  have hwG : G.degree w.1 ≤ 2 := by omega
  have hroot_degree : C.toSimpleGraph.degree root ≤ 1 := by
    let emb : Option (C.toSimpleGraph.neighborSet root) ↪ G.neighborSet w.1 :=
      ⟨fun y ↦ match y with
        | none => ⟨z, w.2.symm⟩
        | some y => ⟨y.1.1.1, hroot_val ▸ y.2⟩,
        by
          intro a b hab
          cases a with
          | none =>
              cases b with
              | none => rfl
              | some b =>
                  exfalso
                  have hv : z = b.1.1.1 :=
                    congr_arg (fun y : G.neighborSet w.1 ↦ y.1) hab
                  exact b.1.1.2 hv.symm
          | some a =>
              cases b with
              | none =>
                  exfalso
                  have hv : a.1.1.1 = z :=
                    congr_arg (fun y : G.neighborSet w.1 ↦ y.1) hab
                  exact a.1.1.2 hv
              | some b =>
                  have hv : a.1.1.1 = b.1.1.1 :=
                    congr_arg (fun y : G.neighborSet w.1 ↦ y.1) hab
                  exact congr_arg some
                    (Subtype.ext (Subtype.ext (Subtype.ext hv)))⟩
    have hle := Fintype.card_le_of_embedding emb
    rw [Fintype.card_option, SimpleGraph.card_neighborSet_eq_degree,
      SimpleGraph.card_neighborSet_eq_degree] at hle
    omega
  have hacyc : G.IsAcyclic := hpos.isAcyclic
  have htreeC : C.toSimpleGraph.IsTree :=
    (hacyc.induce {x | x ≠ z}).isTree_connectedComponent C
  have hdegC : ∀ x, C.toSimpleGraph.degree x ≤ 2 := by
    intro x
    have hx_ne : x.1.1 ≠ z := x.1.2
    have hx_le : G.degree x.1.1 ≤ 3 := hpos.degree_le_three x.1.1
    have hx_not_three : G.degree x.1.1 ≠ 3 := by
      intro hx
      exact hx_ne (hpos.eq_of_degree_eq_three hconn hcard hx hz)
    have hxG : G.degree x.1.1 ≤ 2 := by omega
    let emb : C.toSimpleGraph.neighborSet x ↪ G.neighborSet x.1.1 :=
      ⟨fun y ↦ ⟨y.1.1.1, y.2⟩, by
        intro a b hab
        have hv : a.1.1.1 = b.1.1.1 :=
          congr_arg (fun y : G.neighborSet x.1.1 ↦ y.1) hab
        exact Subtype.ext (Subtype.ext (Subtype.ext hv))⟩
    have hle := Fintype.card_le_of_embedding emb
    rw [SimpleGraph.card_neighborSet_eq_degree,
      SimpleGraph.card_neighborSet_eq_degree] at hle
    exact hle.trans hxG
  obtain ⟨n, hn, ⟨e⟩⟩ := exists_iso_pathGraph_of_degree_le_two
    htreeC.connected htreeC.isAcyclic hdegC
  subst n
  exact exists_pathGraph_iso_apply_zero e root hroot_degree

/-- A trivalent vertex of a positive Cartan tree leaves exactly three
components. -/
theorem card_puncturedComponents_eq_three
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hpos : IsPositiveCartan G) (hconn : G.Connected)
    {z : V} (hz : G.degree z = 3) :
    Fintype.card (G.induce {x | x ≠ z}).ConnectedComponent = 3 := by
  classical
  have htree : G.IsTree := ⟨hconn, hpos.isAcyclic⟩
  rw [← Fintype.card_congr (neighborEquivPuncturedComponents htree)]
  simp only [SimpleGraph.card_neighborSet_eq_degree, hz]

/-! ## Data carried by one oriented arm -/

/-- A punctured component together with path coordinates oriented from the
deleted centre. -/
structure OrientedPuncturedArm (G : SimpleGraph V) (z : V) (htree : G.IsTree) where
  component : (G.induce {x | x ≠ z}).ConnectedComponent
  length : ℕ
  coord : pathGraph length ≃g component.toSimpleGraph
  zero : Fin length
  zero_val : zero.1 = 0
  coord_zero : coord zero = puncturedComponentRoot htree component

namespace OrientedPuncturedArm

variable {G : SimpleGraph V} {z : V} {htree : G.IsTree}

theorem length_pos (A : OrientedPuncturedArm G z htree) : 0 < A.length :=
  by
    have h := A.zero.isLt
    rw [A.zero_val] at h
    exact h

/-- The ambient vertex at an arm coordinate. -/
def vertex (A : OrientedPuncturedArm G z htree) (i : Fin A.length) : V :=
  (A.coord i).1.1

theorem vertex_injective (A : OrientedPuncturedArm G z htree) :
    Function.Injective A.vertex := by
  intro i j hij
  apply A.coord.injective
  apply Subtype.ext
  apply Subtype.ext
  exact hij

theorem vertex_ne_center (A : OrientedPuncturedArm G z htree) (i) :
    A.vertex i ≠ z :=
  (A.coord i).1.2

theorem adj_vertex_of_path_adj (A : OrientedPuncturedArm G z htree)
    {i j} (hij : (pathGraph A.length).Adj i j) :
    G.Adj (A.vertex i) (A.vertex j) := by
  exact A.coord.map_rel_iff.mpr hij

theorem adj_center_vertex_of_val_eq_zero
    (A : OrientedPuncturedArm G z htree) (i) (hi : i.1 = 0) :
    G.Adj z (A.vertex i) := by
  have hiz : i = A.zero := Fin.ext (hi.trans A.zero_val.symm)
  subst i
  rw [vertex, A.coord_zero]
  exact (puncturedComponentNeighbor htree A.component).2

theorem vertex_ne_of_component_ne
    (A B : OrientedPuncturedArm G z htree)
    (hAB : A.component ≠ B.component) (i j) :
    A.vertex i ≠ B.vertex j := by
  intro hij
  apply hAB
  apply ConnectedComponent.eq_of_common_vertex (v := (A.coord i).1)
  · exact (A.coord i).2
  · have hv : (A.coord i).1 = (B.coord j).1 := Subtype.ext hij
    exact hv ▸ (B.coord j).2

/-- Restrict an arm to its first `m` vertices. -/
def prefixEmbedding (A : OrientedPuncturedArm G z htree) {m : ℕ}
    (hm : m ≤ A.length) : Fin m ↪ V :=
  ⟨fun i ↦ A.vertex (Fin.castLE hm i), fun _ _ h ↦
    (Fin.castLEEmb hm).injective (A.vertex_injective h)⟩

theorem prefixEmbedding_ne_center (A : OrientedPuncturedArm G z htree)
    {m : ℕ} (hm : m ≤ A.length) (i) : A.prefixEmbedding hm i ≠ z :=
  A.vertex_ne_center _

theorem prefixEmbedding_ne_of_component_ne
    (A B : OrientedPuncturedArm G z htree)
    (hAB : A.component ≠ B.component)
    {m n : ℕ} (hm : m ≤ A.length) (hn : n ≤ B.length) (i j) :
    A.prefixEmbedding hm i ≠ B.prefixEmbedding hn j :=
  A.vertex_ne_of_component_ne B hAB _ _

theorem adj_prefixEmbedding_of_path_adj
    (A : OrientedPuncturedArm G z htree) {m : ℕ}
    (hm : m ≤ A.length) {i j : Fin m} (hij : (pathGraph m).Adj i j) :
    G.Adj (A.prefixEmbedding hm i) (A.prefixEmbedding hm j) := by
  apply A.adj_vertex_of_path_adj
  rw [SimpleGraph.pathGraph_adj] at hij ⊢
  exact hij

theorem adj_center_prefixEmbedding_of_val_eq_zero
    (A : OrientedPuncturedArm G z htree) {m : ℕ}
    (hm : m ≤ A.length) (i : Fin m) (hi : i.1 = 0) :
    G.Adj z (A.prefixEmbedding hm i) :=
  A.adj_center_vertex_of_val_eq_zero _ hi

end OrientedPuncturedArm

/-- Construct the oriented data for any punctured component of a positive
Cartan tree with one trivalent vertex. -/
noncomputable def orientedPuncturedArm
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hpos : IsPositiveCartan G) (hconn : G.Connected)
    (hcard : Fintype.card V ≤ 15) {z : V} (hz : G.degree z = 3)
    (C : (G.induce {x | x ≠ z}).ConnectedComponent) :
    OrientedPuncturedArm G z ⟨hconn, hpos.isAcyclic⟩ := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  let hex := puncturedComponent_exists_oriented_path_iso hpos hconn hcard hz C
  let e := Classical.choose hex
  let i := Classical.choose (Classical.choose_spec hex)
  have hi := (Classical.choose_spec (Classical.choose_spec hex)).1
  have he := (Classical.choose_spec (Classical.choose_spec hex)).2
  exact
    { component := C
      length := Fintype.card C
      coord := e
      zero := i
      zero_val := hi
      coord_zero := he }

end Lattice
end SRG266
