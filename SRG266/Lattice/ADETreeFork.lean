/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.ADEDoubleFork

/-!
# A positive Cartan tree has at most one branch vertex

This file supplies the second structural obstruction in the elementary ADE
classification.  In a connected acyclic graph, two degree-three vertices are
joined by a unique path.  Removing the path neighbour at each endpoint leaves
two further neighbours.  These four vertices and the path give a double fork,
whose null Cartan weighting was checked in `ADEDoubleFork`.
-/

namespace SRG266
namespace Lattice

open SimpleGraph

variable {V : Type*}

/-- In rank at most fifteen, a connected positive simply-laced Cartan graph
has at most one vertex of degree three. -/
theorem IsPositiveCartan.eq_of_degree_eq_three
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : IsPositiveCartan G) (hconn : G.Connected)
    (hcard : Fintype.card V ≤ 15) {a b : V}
    (ha : G.degree a = 3) (hb : G.degree b = 3) : a = b := by
  by_contra hab
  have hacyc : G.IsAcyclic := hG.isAcyclic
  obtain ⟨p, hp⟩ := hconn.exists_isPath a b
  have hp_not_nil : ¬ p.Nil := by
    simpa [hp.nil_iff_eq] using hab
  have hsnd_mem : p.snd ∈ G.neighborFinset a := by
    simpa using p.adj_snd hp_not_nil
  have hpen_mem : p.penultimate ∈ G.neighborFinset b := by
    simpa using (p.adj_penultimate hp_not_nil).symm
  let leftSet : Finset V := (G.neighborFinset a).erase p.snd
  let rightSet : Finset V := (G.neighborFinset b).erase p.penultimate
  have hleft_card : leftSet.card = 2 := by
    change ((G.neighborFinset a).erase p.snd).card = 2
    rw [Finset.card_erase_of_mem hsnd_mem]
    change G.degree a - 1 = 2
    omega
  have hright_card : rightSet.card = 2 := by
    change ((G.neighborFinset b).erase p.penultimate).card = 2
    rw [Finset.card_erase_of_mem hpen_mem]
    change G.degree b - 1 = 2
    omega
  obtain ⟨left, hleft_range⟩ :=
    Function.Embedding.exists_of_card_le_finset
      (α := Fin 2) (s := leftSet) (by simp [hleft_card])
  obtain ⟨right, hright_range⟩ :=
    Function.Embedding.exists_of_card_le_finset
      (α := Fin 2) (s := rightSet) (by simp [hright_card])
  have hleft_mem (i : Fin 2) : left i ∈ leftSet :=
    hleft_range (Set.mem_range_self i)
  have hright_mem (i : Fin 2) : right i ∈ rightSet :=
    hright_range (Set.mem_range_self i)
  have hleft_adj (i : Fin 2) : G.Adj a (left i) := by
    simpa using (Finset.mem_erase.mp (hleft_mem i)).2
  have hright_adj (i : Fin 2) : G.Adj b (right i) := by
    simpa using (Finset.mem_erase.mp (hright_mem i)).2
  have hleft_ne_snd (i : Fin 2) : left i ≠ p.snd := by
    exact (Finset.mem_erase.mp (hleft_mem i)).1
  have hright_ne_pen (i : Fin 2) : right i ≠ p.penultimate := by
    exact (Finset.mem_erase.mp (hright_mem i)).1
  have hleft_not_support (i : Fin 2) : left i ∉ p.support := by
    intro hm
    exact hleft_ne_snd i (hacyc.eq_snd_of_adj_start hp (hleft_adj i) hm)
  have hright_not_support (i : Fin 2) : right i ∉ p.support := by
    intro hm
    exact hright_ne_pen i (hacyc.eq_penultimate_of_adj_end hp (hright_adj i) hm)
  have hleft_right_ne (i j : Fin 2) : left i ≠ right j := by
    intro hij
    have hleft_ne_b : left i ≠ b := by
      intro hib
      exact hleft_not_support i (hib ▸ p.end_mem_support)
    let q : G.Walk a b :=
      .cons (hleft_adj i) (.cons (hij ▸ (hright_adj j).symm) .nil)
    have hq : q.IsPath := by
      simp [q, hab, hleft_ne_b, (hleft_adj i).ne]
    have hpq : p = q :=
      congrArg Subtype.val (hacyc.path_unique ⟨p, hp⟩ ⟨q, hq⟩)
    apply hleft_not_support i
    rw [hpq]
    simp [q]
  let n := p.length + 1
  have hnlo : 2 ≤ n := by
    have hlen : 0 < p.length := by
      simpa [Walk.not_nil_iff_lt_length] using hp_not_nil
    simp [n]
    omega
  have hnhi : n ≤ 15 := by
    have hlen := hp.length_lt
    simp [n]
    omega
  let pathEmb : Fin n ↪ V :=
    ⟨fun i ↦ p.getVert i.1, by
      intro i j hij
      apply Fin.ext
      exact hp.getVert_injOn
        (by simp only [Set.mem_setOf_eq]; have := i.2; simp [n] at this; omega)
        (by simp only [Set.mem_setOf_eq]; have := j.2; simp [n] at this; omega) hij⟩
  let e : Fin n ⊕ (Fin 2 ⊕ Fin 2) ↪ V :=
    ⟨fun x ↦ match x with
      | Sum.inl i => pathEmb i
      | Sum.inr (Sum.inl i) => left i
      | Sum.inr (Sum.inr i) => right i, by
      intro x y hxy
      cases x with
      | inl i =>
          cases y with
          | inl j => exact congrArg Sum.inl (pathEmb.injective hxy)
          | inr y =>
              cases y with
              | inl j =>
                  exfalso
                  change pathEmb i = left j at hxy
                  apply hleft_not_support j
                  rw [← hxy]
                  simp [pathEmb]
              | inr j =>
                  exfalso
                  change pathEmb i = right j at hxy
                  apply hright_not_support j
                  rw [← hxy]
                  simp [pathEmb]
      | inr x =>
          cases x with
          | inl i =>
              cases y with
              | inl j =>
                  exfalso
                  change left i = pathEmb j at hxy
                  apply hleft_not_support i
                  rw [hxy]
                  simp [pathEmb]
              | inr y =>
                  cases y with
                  | inl j => exact congrArg (Sum.inr ∘ Sum.inl) (left.injective hxy)
                  | inr j => exact (hleft_right_ne i j hxy).elim
          | inr i =>
              cases y with
              | inl j =>
                  exfalso
                  change right i = pathEmb j at hxy
                  apply hright_not_support i
                  rw [hxy]
                  simp [pathEmb]
              | inr y =>
                  cases y with
                  | inl j => exact (hleft_right_ne j i hxy.symm).elim
                  | inr j => exact congrArg (Sum.inr ∘ Sum.inr) (right.injective hxy)⟩
  let K : SimpleGraph (Fin n ⊕ (Fin 2 ⊕ Fin 2)) := G.comap e
  have hdir : ∀ x y, doubleForkRel n x y → G.Adj (e x) (e y) := by
    intro x y hxy
    unfold doubleForkRel at hxy
    cases x with
    | inl i =>
        cases y with
        | inl j =>
            change (SimpleGraph.pathGraph n).Adj i j at hxy
            rw [SimpleGraph.pathGraph_adj] at hxy
            rcases hxy with hij | hji
            · have hadj := p.adj_getVert_succ (i := i.1) (by
                have := j.2
                simp [n] at this
                omega)
              simpa [e, pathEmb, hij] using hadj
            · have hadj := p.adj_getVert_succ (i := j.1) (by
                have := i.2
                simp [n] at this
                omega)
              simpa [e, pathEmb, hji] using hadj.symm
        | inr y =>
            cases y with
            | inl j =>
                change i.1 = 0 at hxy
                have hi : i = 0 := Fin.ext hxy
                subst i
                simpa [e, pathEmb] using hleft_adj j
            | inr j =>
                change i.1 + 1 = n at hxy
                have hi : i.1 = p.length := by simp [n] at hxy ⊢; omega
                have hval : pathEmb i = b := by simp [pathEmb, hi]
                simpa [e, hval] using hright_adj j
    | inr x => cases x <;> simp at hxy
  have hfork_le : doubleForkGraph n ≤ K := by
    intro x y hxy
    rw [doubleForkGraph, SimpleGraph.fromRel_adj] at hxy
    rcases hxy.2 with hxy | hyx
    · exact hdir x y hxy
    · exact (hdir y x hyx).symm
  have hK : IsPositiveCartan K := hG.comap e
  exact (not_isPositiveCartan_of_nonpositive_subgraph hfork_le
    (by
      intro hzero
      have hvalue := congrFun hzero (Sum.inl (0 : Fin n))
      norm_num [doubleForkWeight] at hvalue)
    (by intro x; cases x <;> norm_num [doubleForkWeight])
    (doubleFork_cartanEnergy_zero n hnlo hnhi).le) hK

end Lattice
end SRG266
