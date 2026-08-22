/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.ADETreeFork
import SRG266.Lattice.RootLattice
import Mathlib.Data.Fin.Rev

/-!
# Connected degree-two trees are paths

The proof chooses a longest path.  Any edge leaving it either extends an
endpoint or gives an internal path vertex three distinct neighbours.  Hence a
connected acyclic graph of maximum degree two has a spanning path.
-/

namespace SRG266
namespace Lattice

open SimpleGraph

variable {V : Type*}

/-- A finite connected acyclic graph of maximum degree two admits a spanning
path. -/
theorem exists_spanning_path_of_degree_le_two
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ 2) :
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ ∀ x, x ∈ p.support := by
  letI : Nonempty V := hconn.nonempty
  obtain ⟨u, v, p, hp, hmax⟩ :=
    Walk.exists_isPath_forall_isPath_length_le_length G
  refine ⟨u, v, p, hp, ?_⟩
  intro x
  by_contra hx
  obtain ⟨q, hq⟩ := hconn.exists_isPath u x
  obtain ⟨d, _hdq, hdy, hdz⟩ :=
    q.exists_boundary_dart {x | x ∈ p.support} p.start_mem_support hx
  obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hdy
  by_cases hi0 : i = 0
  · subst i
    have hadj : G.Adj u d.snd := by
      rw [← p.getVert_zero]
      exact hi.symm ▸ d.adj
    have hpath : (p.reverse.concat hadj).IsPath := by
      apply hp.reverse.concat
      simpa using hdz
    have hle := hmax _ _ _ hpath
    simp at hle
  by_cases hiend : i = p.length
  · subst i
    have hadj : G.Adj v d.snd := by
      rw [← p.getVert_length]
      exact hi.symm ▸ d.adj
    have hpath : (p.concat hadj).IsPath := hp.concat (by simpa using hdz) hadj
    have hle := hmax _ _ _ hpath
    simp at hle
  have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
  have hi_lt : i < p.length := lt_of_le_of_ne hil hiend
  let l : V := p.getVert (i - 1)
  let r : V := p.getVert (i + 1)
  let y : V := p.getVert i
  let z : V := d.snd
  have hly : G.Adj y l := by
    have h := p.adj_getVert_succ (i := i - 1) (by omega)
    simpa [l, y, Nat.sub_add_cancel hi_pos] using h.symm
  have hyr : G.Adj y r := by
    simpa [y, r] using p.adj_getVert_succ hi_lt
  have hyz : G.Adj y z := by
    change G.Adj (p.getVert i) d.snd
    exact hi.symm ▸ d.adj
  have hlr : l ≠ r := by
    intro hlr
    have hind := hp.getVert_injOn
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) hlr
    omega
  have hlz : l ≠ z := by
    intro hlz
    apply hdz
    change l = d.snd at hlz
    change d.snd ∈ p.support
    rw [← hlz]
    exact p.getVert_mem_support _
  have hrz : r ≠ z := by
    intro hrz
    apply hdz
    change r = d.snd at hrz
    change d.snd ∈ p.support
    rw [← hrz]
    exact p.getVert_mem_support _
  let nl : ↑(G.neighborFinset y) := ⟨l, by simpa using hly⟩
  let nr : ↑(G.neighborFinset y) := ⟨r, by simpa using hyr⟩
  let nz : ↑(G.neighborFinset y) := ⟨z, by simpa using hyz⟩
  let emb : Fin 3 ↪ ↑(G.neighborFinset y) :=
    ⟨![nl, nr, nz], by
      intro a b hab
      fin_cases a <;> fin_cases b <;>
        simp [nl, nr, nz, hlr, Ne.symm hlr, hlz, Ne.symm hlz, hrz, Ne.symm hrz] at hab ⊢⟩
  have hthree := Fintype.card_le_of_embedding emb
  have hdegree : 3 ≤ G.degree y := by
    simpa only [Fintype.card_fin, Fintype.card_coe,
      G.card_neighborFinset_eq_degree] using hthree
  have hydeg := hdeg y
  omega

/-- A finite connected acyclic graph of maximum degree two is isomorphic to a
path graph.  The proof turns the spanning path above into a spanning subgraph.
Both that subgraph and the ambient graph are trees, so their equal edge counts
force equality. -/
theorem exists_iso_pathGraph_of_degree_le_two
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hconn : G.Connected) (hacyc : G.IsAcyclic)
    (hdeg : ∀ v, G.degree v ≤ 2) :
    ∃ n : ℕ, n = Fintype.card V ∧ Nonempty (pathGraph n ≃g G) := by
  classical
  obtain ⟨u, v, p, hp, hspan⟩ :=
    exists_spanning_path_of_degree_le_two hconn hdeg
  let n := p.length + 1
  let e : Fin n → V := fun i ↦ p.getVert i
  have he_injective : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) hij
  have he_surjective : Function.Surjective e := by
    intro x
    obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp (hspan x)
    refine ⟨⟨i, by simp only [n]; omega⟩, ?_⟩
    exact hi
  let f : Fin n ≃ V := Equiv.ofBijective e ⟨he_injective, he_surjective⟩
  let H : SimpleGraph V := (pathGraph n).map f
  have hpath_edge {i j : Fin n} (hij : (pathGraph n).Adj i j) :
      G.Adj (f i) (f j) := by
    rw [SimpleGraph.pathGraph_adj] at hij
    rcases hij with hij | hij
    · have hadj := p.adj_getVert_succ (i := i.1) (by omega)
      change G.Adj (p.getVert i.1) (p.getVert j.1)
      rw [← hij]
      exact hadj
    · have hadj := p.adj_getVert_succ (i := j.1) (by omega)
      change G.Adj (p.getVert i.1) (p.getVert j.1)
      rw [← hij]
      exact hadj.symm
  have hHG : H ≤ G := by
    intro x y hxy
    change ((pathGraph n).map f).Adj x y at hxy
    rw [SimpleGraph.map_adj'] at hxy
    obtain ⟨_, i, j, hij, rfl, rfl⟩ := hxy
    exact hpath_edge hij
  have hHconn : H.Connected := by
    exact (SimpleGraph.Iso.map f (pathGraph n)).connected_iff.mp
      (by simpa only [n] using SimpleGraph.pathGraph_connected p.length)
  have hHacyc : H.IsAcyclic := SimpleGraph.IsAcyclic.anti hHG hacyc
  letI : DecidableRel H.Adj := Classical.decRel _
  have hHtree : H.IsTree := ⟨hHconn, hHacyc⟩
  have hGtree : G.IsTree := ⟨hconn, hacyc⟩
  have hedge_card : H.edgeFinset.card = G.edgeFinset.card := by
    have hHcard := hHtree.card_edgeFinset
    have hGcard := hGtree.card_edgeFinset
    omega
  have hedge : H.edgeFinset = G.edgeFinset := by
    apply Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono hHG)
    simpa only [hedge_card] using le_rfl
  have hH_eq_G : H = G := SimpleGraph.edgeFinset_inj.mp hedge
  refine ⟨n, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using Fintype.card_congr f
  · refine ⟨?_⟩
    simpa only [H, hH_eq_G] using SimpleGraph.Iso.map f (pathGraph n)

/-- The Cartan matrix of a path graph is the standard `Aₙ` Gram matrix. -/
theorem graphCartanMatrix_pathGraph (n : ℕ) :
    graphCartanMatrix (pathGraph n) = gramA n := by
  classical
  ext i j
  simp only [graphCartanMatrix, gramA, gramAEntry,
    SimpleGraph.pathGraph_adj]
  split_ifs <;> omega

/-- Reversing the linear order is an automorphism of a path graph. -/
def pathGraphRevIso (n : ℕ) : pathGraph n ≃g pathGraph n where
  __ := Fin.revPerm
  map_rel_iff' := by
    intro i j
    simp only [SimpleGraph.pathGraph_adj, Fin.revPerm_apply]
    simp only [Fin.val_rev]
    omega

/-- A path vertex of degree at most one is one of the two endpoints. -/
theorem pathGraph_eq_endpoint {n : ℕ} (k : Fin n)
    (hunique : ∀ {l r}, (pathGraph n).Adj k l →
      (pathGraph n).Adj k r → l = r) :
    k.1 = 0 ∨ k.1 + 1 = n := by
  by_contra hk
  simp only [not_or] at hk
  have hkpos : 0 < k.1 := Nat.pos_of_ne_zero hk.1
  have hklt : k.1 + 1 < n := lt_of_le_of_ne k.2 hk.2
  let l : Fin n := ⟨k.1 - 1, by omega⟩
  let r : Fin n := ⟨k.1 + 1, hklt⟩
  have hl : (pathGraph n).Adj k l := by
    rw [SimpleGraph.pathGraph_adj]
    right
    simp only [l]
    omega
  have hr : (pathGraph n).Adj k r := by
    rw [SimpleGraph.pathGraph_adj]
    left
    rfl
  have hlr : l ≠ r := by
    intro h
    have := congr_arg Fin.val h
    simp only [l, r] at this
    omega
  exact hlr (hunique hl hr)

/-- Reorient path coordinates so that a specified endpoint is coordinate
zero. -/
theorem exists_pathGraph_iso_apply_zero
    {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {n : ℕ} (e : pathGraph n ≃g H) (x : W)
    (hx : H.degree x ≤ 1) :
    ∃ (e' : pathGraph n ≃g H) (i : Fin n), i.1 = 0 ∧ e' i = x := by
  classical
  have hn : 0 < n := by
    have hc := Fintype.card_congr e.toEquiv
    have hw : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨x⟩
    simp only [Fintype.card_fin] at hc
    omega
  letI : DecidableRel (pathGraph n).Adj := Classical.decRel _
  let k : Fin n := e.symm x
  have hek : e k = x := by simp [k]
  have hkdeg : (pathGraph n).degree k ≤ 1 := by
    rw [← e.degree_eq k, hek]
    exact hx
  have hkunique : ∀ {l r}, (pathGraph n).Adj k l →
      (pathGraph n).Adj k r → l = r := by
    intro l r hl hr
    apply Finset.card_le_one_iff.mp hkdeg
    · simpa using hl
    · simpa using hr
  rcases pathGraph_eq_endpoint k hkunique with hk0 | hklast
  · have hk : k = ⟨0, hn⟩ := Fin.ext hk0
    refine ⟨e, ⟨0, hn⟩, rfl, ?_⟩
    rw [← hk, hek]
  · have hrev : Fin.rev ⟨0, hn⟩ = k := by
      apply Fin.ext
      simp only [Fin.val_rev]
      omega
    refine ⟨(pathGraphRevIso n).trans e, ⟨0, hn⟩, rfl, ?_⟩
    change e (Fin.rev ⟨0, hn⟩) = x
    rw [hrev, hek]

/-- In the coordinates supplied by the path-graph isomorphism, a connected
positive Cartan component with no trivalent vertex has Gram matrix `Aₙ`. -/
theorem exists_A_coordinates_of_degree_le_two
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hconn : G.Connected) (hacyc : G.IsAcyclic)
    (hdeg : ∀ v, G.degree v ≤ 2) :
    ∃ (e : Fin (Fintype.card V) ≃ V),
      ∀ i j, graphCartanMatrix G (e i) (e j) = gramA (Fintype.card V) i j := by
  obtain ⟨n, hn, ⟨e⟩⟩ :=
    exists_iso_pathGraph_of_degree_le_two hconn hacyc hdeg
  subst n
  refine ⟨e.toEquiv, fun i j ↦ ?_⟩
  change graphCartanMatrix G (e i) (e j) = gramA (Fintype.card V) i j
  calc
    _ = graphCartanMatrix (pathGraph (Fintype.card V)) i j :=
      graphCartanMatrix_apply_iso e i j
    _ = gramA (Fintype.card V) i j := by rw [graphCartanMatrix_pathGraph]

end Lattice
end SRG266
