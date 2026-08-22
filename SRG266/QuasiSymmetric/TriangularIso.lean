/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.K11
import SRG266.QuasiSymmetric.TriangularUniqueness

/-!
# The derived block graph is `T(11)`

The `10`-cliques of the derived block graph provide the `11` vertices of
`K₁₁`. Each point lies on two such cliques and therefore corresponds to an edge
of `K₁₁`; adjacency becomes intersection at one endpoint.
-/

open scoped BigOperators

namespace SRG266.QuasiSymmetric

namespace Edge11

/-- Every `2`-subset of the vertices of `K₁₁` is the vertex set of an edge. -/
theorem exists_vertices_eq {S : Finset (Fin 11)} (h : S.card = 2) :
    ∃ e : Edge11, e.vertices = S := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
  exact ⟨mk' hab, vertices_mk' hab⟩

end Edge11

namespace Derived45

variable {P : Type*} [Fintype P] [DecidableEq P] (E : Derived45 P)

/-! ### Grand cliques

A *grand clique* is a `10`-clique of the block graph. There is no `11`-clique,
and the maximal cliques through a point are exactly the
two obtained by adjoining the point to one side of the local split; so the grand
cliques are precisely the maximal cliques, and they play the role of the `11`
vertex stars of `K₁₁`. -/

/-- The **grand cliques** of the block graph of a `Derived45`: its
`10`-cliques. -/
def grandCliques : Finset (Finset P) :=
  Finset.univ.filter fun K => E.blockGraph.IsNClique 10 K

theorem mem_grandCliques {K : Finset P} :
    K ∈ E.grandCliques ↔ E.blockGraph.IsNClique 10 K := by
  simp [grandCliques]

/-- A grand clique has `10` points. -/
theorem card_of_mem_grandCliques {K : Finset P} (hK : K ∈ E.grandCliques) : K.card = 10 :=
  (E.mem_grandCliques.mp hK).card_eq

/-- A grand clique is a clique. -/
theorem isClique_of_mem_grandCliques {K : Finset P} (hK : K ∈ E.grandCliques) :
    E.blockGraph.IsClique (K : Set P) :=
  (E.mem_grandCliques.mp hK).isClique

/-- Two distinct points of a grand clique are adjacent. -/
theorem adj_of_mem_grandClique {K : Finset P} (hK : K ∈ E.grandCliques) {p q : P}
    (hp : p ∈ K) (hq : q ∈ K) (hpq : p ≠ q) : E.blockGraph.Adj p q :=
  E.isClique_of_mem_grandCliques hK (Finset.mem_coe.mpr hp) (Finset.mem_coe.mpr hq) hpq

/-- Adjoining the centre `x` to one side of the local split at `x` produces a
grand clique. -/
theorem insert_mem_grandCliques {x : P} {X : Finset P}
    (hXsub : X ⊆ E.blockGraph.neighborFinset x) (hXcard : X.card = 9)
    (hXc : E.blockGraph.IsClique (X : Set P)) :
    insert x X ∈ E.grandCliques := by
  have hxX : x ∉ X := fun hmem =>
    ((SimpleGraph.mem_neighborFinset _ _ _).mp (hXsub hmem)).ne rfl
  refine E.mem_grandCliques.mpr ⟨?_, ?_⟩
  · rw [Finset.coe_insert]
    exact hXc.insert fun b hb _ =>
      (SimpleGraph.mem_neighborFinset _ _ _).mp (hXsub (Finset.mem_coe.mp hb))
  · rw [Finset.card_insert_of_notMem hxX, hXcard]

/-! ### The two grand cliques through a point -/

/-- A clique of the
block graph that lies inside a split local graph `X ∪ Y` and has at least `3`
points lies wholly inside `X` or wholly inside `Y`: a point of `X` has exactly
one neighbour in `Y` and vice versa, so a clique meeting both sides has at most
one point on each. -/
theorem subset_of_isClique_local {X Y S : Finset P} (hdisj : Disjoint X Y)
    (hcross : ∀ p ∈ X, (Y.filter fun q => E.blockGraph.Adj p q).card = 1)
    (hcross' : ∀ q ∈ Y, (X.filter fun p => E.blockGraph.Adj q p).card = 1)
    (hS : S ⊆ X ∪ Y) (hScard : 3 ≤ S.card)
    (hSc : E.blockGraph.IsClique (S : Set P)) : S ⊆ X ∨ S ⊆ Y := by
  classical
  by_cases hXne : (S ∩ X).Nonempty
  · by_cases hYne : (S ∩ Y).Nonempty
    · exfalso
      obtain ⟨p, hp⟩ := hXne
      obtain ⟨q, hq⟩ := hYne
      obtain ⟨hpS, hpX⟩ := Finset.mem_inter.mp hp
      obtain ⟨hqS, hqY⟩ := Finset.mem_inter.mp hq
      -- the `Y`-part of `S` sits inside the single `Y`-neighbour of `p`
      have hboundY : (S ∩ Y).card ≤ 1 := by
        have hsub : S ∩ Y ⊆ Y.filter fun r => E.blockGraph.Adj p r := by
          intro r hr
          obtain ⟨hrS, hrY⟩ := Finset.mem_inter.mp hr
          refine Finset.mem_filter.mpr ⟨hrY, ?_⟩
          have hpr : p ≠ r := fun heq =>
            Finset.disjoint_left.mp hdisj hpX (heq ▸ hrY)
          exact hSc (Finset.mem_coe.mpr hpS) (Finset.mem_coe.mpr hrS) hpr
        have hle := Finset.card_le_card hsub
        rw [hcross p hpX] at hle
        exact hle
      -- and symmetrically for the `X`-part
      have hboundX : (S ∩ X).card ≤ 1 := by
        have hsub : S ∩ X ⊆ X.filter fun r => E.blockGraph.Adj q r := by
          intro r hr
          obtain ⟨hrS, hrX⟩ := Finset.mem_inter.mp hr
          refine Finset.mem_filter.mpr ⟨hrX, ?_⟩
          have hqr : q ≠ r := fun heq =>
            Finset.disjoint_left.mp hdisj (heq ▸ hrX) hqY
          exact hSc (Finset.mem_coe.mpr hqS) (Finset.mem_coe.mpr hrS) hqr
        have hle := Finset.card_le_card hsub
        rw [hcross' q hqY] at hle
        exact hle
      have hd : Disjoint (S ∩ X) (S ∩ Y) :=
        Finset.disjoint_left.mpr fun a ha ha' =>
          Finset.disjoint_left.mp hdisj (Finset.mem_inter.mp ha).2
            (Finset.mem_inter.mp ha').2
      have hunion : S ∩ X ∪ S ∩ Y = S := by
        rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hS]
      have hcard := Finset.card_union_of_disjoint hd
      rw [hunion] at hcard
      omega
    · refine Or.inl fun r hr => ?_
      rcases Finset.mem_union.mp (hS hr) with h | h
      · exact h
      · exact absurd ⟨r, Finset.mem_inter.mpr ⟨hr, h⟩⟩ hYne
  · refine Or.inr fun r hr => ?_
    rcases Finset.mem_union.mp (hS hr) with h | h
    · exact absurd ⟨r, Finset.mem_inter.mpr ⟨hr, h⟩⟩ hXne
    · exact h

/-- Every point `x` lies on exactly two grand
cliques, and they meet in `x` alone.

They are `{x} ∪ X` and `{x} ∪ Y` for the local split `Γ(x) = X ⊔ Y`;
any grand clique `K` through `x` has `K \ {x}` a `9`-clique inside `X ∪ Y`, hence
inside one side, hence equal to it. -/
theorem exists_grandCliques_pair (x : P) :
    ∃ K₁ K₂ : Finset P, K₁ ∈ E.grandCliques ∧ K₂ ∈ E.grandCliques ∧
      x ∈ K₁ ∧ x ∈ K₂ ∧ K₁ ∩ K₂ = {x} ∧
      ∀ K ∈ E.grandCliques, x ∈ K → K = K₁ ∨ K = K₂ := by
  classical
  obtain ⟨X, Y, hXY, hdisj, hX, hY, hXc, hYc, hcross, hcross'⟩ := E.local_split_matching x
  have hXsub : X ⊆ E.blockGraph.neighborFinset x := hXY ▸ Finset.subset_union_left
  have hYsub : Y ⊆ E.blockGraph.neighborFinset x := hXY ▸ Finset.subset_union_right
  refine ⟨insert x X, insert x Y, E.insert_mem_grandCliques hXsub hX hXc,
    E.insert_mem_grandCliques hYsub hY hYc, Finset.mem_insert_self _ _,
    Finset.mem_insert_self _ _, ?_, ?_⟩
  · ext q
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hq₁, hq₂⟩
      by_contra hqx
      rcases hq₁ with rfl | hq₁
      · exact hqx rfl
      rcases hq₂ with rfl | hq₂
      · exact hqx rfl
      exact Finset.disjoint_left.mp hdisj hq₁ hq₂
    · rintro rfl
      exact ⟨Or.inl rfl, Or.inl rfl⟩
  · intro K hK hxK
    have hKcard := E.card_of_mem_grandCliques hK
    have hKc := E.isClique_of_mem_grandCliques hK
    have hScard : (K.erase x).card = 9 := by
      rw [Finset.card_erase_of_mem hxK, hKcard]
    have hSsub : K.erase x ⊆ X ∪ Y := by
      intro r hr
      obtain ⟨hrx, hrK⟩ := Finset.mem_erase.mp hr
      rw [hXY]
      exact (SimpleGraph.mem_neighborFinset _ _ _).mpr
        (E.adj_of_mem_grandClique hK hxK hrK (Ne.symm hrx))
    have hSc : E.blockGraph.IsClique ((K.erase x : Finset P) : Set P) :=
      SimpleGraph.IsClique.subset (Finset.coe_subset.mpr (Finset.erase_subset _ _)) hKc
    rcases E.subset_of_isClique_local hdisj hcross hcross' hSsub (by omega) hSc with h | h
    · refine Or.inl ?_
      have heq : K.erase x = X := Finset.eq_of_subset_of_card_le h (by omega)
      rw [← Finset.insert_erase hxK, heq]
    · refine Or.inr ?_
      have heq : K.erase x = Y := Finset.eq_of_subset_of_card_le h (by omega)
      rw [← Finset.insert_erase hxK, heq]

/-- **Every point lies on exactly `2` grand cliques.** -/
theorem card_filter_grandCliques (x : P) :
    (E.grandCliques.filter fun K => x ∈ K).card = 2 := by
  classical
  obtain ⟨K₁, K₂, h₁, h₂, hx₁, hx₂, hinter, hall⟩ := E.exists_grandCliques_pair x
  have hne : K₁ ≠ K₂ := by
    rintro rfl
    rw [Finset.inter_self] at hinter
    have hcard := E.card_of_mem_grandCliques h₁
    rw [hinter, Finset.card_singleton] at hcard
    exact absurd hcard (by norm_num)
  have hset : (E.grandCliques.filter fun K => x ∈ K) = {K₁, K₂} := by
    ext K
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hK, hxK⟩
      exact hall K hK hxK
    · rintro (rfl | rfl)
      exacts [⟨h₁, hx₁⟩, ⟨h₂, hx₂⟩]
  rw [hset, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

/-! ### Every edge lies on exactly one grand clique -/

/-- Two adjacent points lie on a common grand clique: the neighbour is on one
side of the local split, and that side plus the centre is one. -/
theorem exists_grandClique_of_adj {p q : P} (h : E.blockGraph.Adj p q) :
    ∃ K ∈ E.grandCliques, p ∈ K ∧ q ∈ K := by
  classical
  obtain ⟨X, Y, hXY, -, hX, hY, hXc, hYc⟩ := E.local_split p
  have hXsub : X ⊆ E.blockGraph.neighborFinset p := hXY ▸ Finset.subset_union_left
  have hYsub : Y ⊆ E.blockGraph.neighborFinset p := hXY ▸ Finset.subset_union_right
  have hq : q ∈ X ∪ Y := by
    rw [hXY]
    exact (SimpleGraph.mem_neighborFinset _ _ _).mpr h
  rcases Finset.mem_union.mp hq with hq | hq
  · exact ⟨insert p X, E.insert_mem_grandCliques hXsub hX hXc,
      Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hq⟩
  · exact ⟨insert p Y, E.insert_mem_grandCliques hYsub hY hYc,
      Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hq⟩

/-! ### There are eleven grand cliques -/

/-- **The incidence count.**  `10 · |𝒦| = 55 · 2`, so a `Derived45` has exactly
`11` grand cliques — the `11` vertices of `K₁₁`. -/
theorem card_grandCliques : E.grandCliques.card = 11 := by
  classical
  have hcol : ∀ K : Finset P, K.card = ∑ p : P, if p ∈ K then 1 else 0 := by
    intro K
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hrow : ∀ p : P, (E.grandCliques.filter fun K => p ∈ K).card
      = ∑ K ∈ E.grandCliques, if p ∈ K then 1 else 0 := fun p => Finset.card_filter _ _
  have hdouble : (∑ K ∈ E.grandCliques, K.card)
      = ∑ p : P, (E.grandCliques.filter fun K => p ∈ K).card := by
    rw [Finset.sum_congr rfl fun K _ => hcol K,
      Finset.sum_congr rfl fun p _ => hrow p, Finset.sum_comm]
  have hleft : (∑ K ∈ E.grandCliques, K.card) = E.grandCliques.card * 10 := by
    rw [Finset.sum_congr rfl fun K hK => E.card_of_mem_grandCliques hK,
      Finset.sum_const, smul_eq_mul]
  have hright : (∑ p : P, (E.grandCliques.filter fun K => p ∈ K).card) = 110 := by
    rw [Finset.sum_congr rfl fun p _ => E.card_filter_grandCliques p, Finset.sum_const,
      Finset.card_univ, E.point_card, smul_eq_mul]
  omega

/-! ### The `K₁₁` coordinates

Fix a labelling `ψ` of the `11` grand cliques by `Fin 11`.  A point acquires the
`2`-set of labels of the grand cliques through it, i.e. an edge of `K₁₁`. -/

section Coordinates

variable (ψ : {K : Finset P // K ∈ E.grandCliques} ≃ Fin 11)

/-- The label of a grand clique under a chosen bijection with `Fin 11`
(arbitrary on non-grand cliques). -/
def cliqueIndex (K : Finset P) : Fin 11 :=
  if h : K ∈ E.grandCliques then ψ ⟨K, h⟩ else 0

theorem cliqueIndex_of_mem {K : Finset P} (hK : K ∈ E.grandCliques) :
    E.cliqueIndex ψ K = ψ ⟨K, hK⟩ := dif_pos hK

/-- Distinct grand cliques get distinct labels. -/
theorem cliqueIndex_injOn :
    Set.InjOn (E.cliqueIndex ψ) (E.grandCliques : Set (Finset P)) := by
  intro K hK K' hK' h
  rw [E.cliqueIndex_of_mem ψ (Finset.mem_coe.mp hK),
    E.cliqueIndex_of_mem ψ (Finset.mem_coe.mp hK')] at h
  exact congrArg Subtype.val (ψ.injective h)

/-- **The `K₁₁` coordinate of a point**: the pair of labels of the two grand
cliques through it. -/
def cliquePair (p : P) : Finset (Fin 11) :=
  (E.grandCliques.filter fun K => p ∈ K).image (E.cliqueIndex ψ)

theorem mem_cliquePair {p : P} {i : Fin 11} :
    i ∈ E.cliquePair ψ p ↔ ∃ K ∈ E.grandCliques, p ∈ K ∧ E.cliqueIndex ψ K = i := by
  simp only [cliquePair, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨K, ⟨hK, hpK⟩, hidx⟩
    exact ⟨K, hK, hpK, hidx⟩
  · rintro ⟨K, hK, hpK, hidx⟩
    exact ⟨K, ⟨hK, hpK⟩, hidx⟩

/-- A point has exactly two coordinates. -/
theorem card_cliquePair (p : P) : (E.cliquePair ψ p).card = 2 := by
  rw [cliquePair,
    Finset.card_image_of_injOn ((E.cliqueIndex_injOn ψ).mono
      (Finset.coe_subset.mpr (Finset.filter_subset _ _))),
    E.card_filter_grandCliques p]

/-- **The point-to-edge map.**  The two coordinates of a point, read as an edge
of `K₁₁`. -/
noncomputable def pointEdge (p : P) : Edge11 :=
  Classical.choose (Edge11.exists_vertices_eq (E.card_cliquePair ψ p))

theorem pointEdge_vertices (p : P) : (E.pointEdge ψ p).vertices = E.cliquePair ψ p :=
  Classical.choose_spec (Edge11.exists_vertices_eq (E.card_cliquePair ψ p))

/-- A point is determined by the two grand cliques through it: the two grand
cliques through `p` meet in `p` alone, so any other point on both would be
`p`. -/
theorem cliquePair_injective : Function.Injective (E.cliquePair ψ) := by
  intro p q hpq
  obtain ⟨K₁, K₂, h₁, h₂, hp₁, hp₂, hinter, -⟩ := E.exists_grandCliques_pair p
  have hcarry : ∀ K ∈ E.grandCliques, p ∈ K → q ∈ K := by
    intro K hK hpK
    have hi : E.cliqueIndex ψ K ∈ E.cliquePair ψ p :=
      (E.mem_cliquePair ψ).mpr ⟨K, hK, hpK, rfl⟩
    rw [hpq] at hi
    obtain ⟨K', hK', hqK', hidx⟩ := (E.mem_cliquePair ψ).mp hi
    have heq : K' = K := E.cliqueIndex_injOn ψ (Finset.mem_coe.mpr hK')
      (Finset.mem_coe.mpr hK) hidx
    exact heq ▸ hqK'
  have hmem : q ∈ K₁ ∩ K₂ :=
    Finset.mem_inter.mpr ⟨hcarry K₁ h₁ hp₁, hcarry K₂ h₂ hp₂⟩
  rw [hinter, Finset.mem_singleton] at hmem
  exact hmem.symm

theorem pointEdge_injective : Function.Injective (E.pointEdge ψ) := by
  intro p q h
  refine E.cliquePair_injective ψ ?_
  rw [← E.pointEdge_vertices ψ p, ← E.pointEdge_vertices ψ q, h]

/-- The point-to-edge map is a bijection: it is injective, and both sides have
`55 = binomial 11 2` elements. -/
theorem pointEdge_bijective : Function.Bijective (E.pointEdge ψ) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨E.pointEdge_injective ψ, ?_⟩
  rw [E.point_card, Edge11.card_edge11]

/-- **Adjacency is meeting in an endpoint.**  Two points are adjacent exactly
when they lie on a common grand clique, i.e. when their edges share an
endpoint. -/
theorem adj_iff_vmeet_pointEdge (p q : P) :
    E.blockGraph.Adj p q ↔ Edge11.vmeet (E.pointEdge ψ p) (E.pointEdge ψ q) = 1 := by
  classical
  constructor
  · intro h
    obtain ⟨K, hK, hpK, hqK⟩ := E.exists_grandClique_of_adj h
    have hmem : E.cliqueIndex ψ K ∈
        (E.pointEdge ψ p).vertices ∩ (E.pointEdge ψ q).vertices := by
      rw [E.pointEdge_vertices ψ p, E.pointEdge_vertices ψ q]
      exact Finset.mem_inter.mpr
        ⟨(E.mem_cliquePair ψ).mpr ⟨K, hK, hpK, rfl⟩, (E.mem_cliquePair ψ).mpr ⟨K, hK, hqK, rfl⟩⟩
    have hne : E.pointEdge ψ p ≠ E.pointEdge ψ q := fun heq =>
      h.ne (E.pointEdge_injective ψ heq)
    have hle := Edge11.vmeet_le_one hne
    have hpos : 0 < Edge11.vmeet (E.pointEdge ψ p) (E.pointEdge ψ q) :=
      Finset.card_pos.mpr ⟨_, hmem⟩
    omega
  · intro h
    have hpos : 0 < ((E.pointEdge ψ p).vertices ∩ (E.pointEdge ψ q).vertices).card := by
      rw [← Edge11.vmeet, h]
      norm_num
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    rw [E.pointEdge_vertices ψ p, E.pointEdge_vertices ψ q, Finset.mem_inter] at hi
    obtain ⟨K, hK, hpK, hidx⟩ := (E.mem_cliquePair ψ).mp hi.1
    obtain ⟨K', hK', hqK', hidx'⟩ := (E.mem_cliquePair ψ).mp hi.2
    have heq : K' = K := E.cliqueIndex_injOn ψ (Finset.mem_coe.mpr hK')
      (Finset.mem_coe.mpr hK) (hidx'.trans hidx.symm)
    have hpq : p ≠ q := by
      rintro rfl
      rw [Edge11.vmeet_self] at h
      exact absurd h (by norm_num)
    exact E.adj_of_mem_grandClique hK hpK (heq ▸ hqK') hpq

/-- **The pair-multiplicity identity in `K₁₁` coordinates.**  Two points lie on
`9` common blocks when equal, on `1` when their edges meet, and on `2` when they
do not — that is, `t p q + vmeet = 2 + 9 · [p = q]`. -/
theorem pairMult_add_vmeet_pointEdge (p q : P) :
    E.pairMult p q + Edge11.vmeet (E.pointEdge ψ p) (E.pointEdge ψ q)
      = 2 + if p = q then 9 else 0 := by
  by_cases hpq : p = q
  · subst hpq
    rw [E.pairMult_self, Edge11.vmeet_self, if_pos rfl]
  · rw [if_neg hpq]
    have hne : E.pointEdge ψ p ≠ E.pointEdge ψ q := fun heq =>
      hpq (E.pointEdge_injective ψ heq)
    by_cases hadj : E.blockGraph.Adj p q
    · rw [hadj.2, (E.adj_iff_vmeet_pointEdge ψ p q).mp hadj]
    · have hv : Edge11.vmeet (E.pointEdge ψ p) (E.pointEdge ψ q) = 0 := by
        have hle := Edge11.vmeet_le_one hne
        have hne1 : Edge11.vmeet (E.pointEdge ψ p) (E.pointEdge ψ q) ≠ 1 := fun hone =>
          hadj ((E.adj_iff_vmeet_pointEdge ψ p q).mpr hone)
        omega
      rw [E.pairMult_of_not_adj hpq hadj, hv]

end Coordinates

/-! ### Identification with the triangular graph -/

/-- The block graph of a `Derived45` is the triangular graph `T(11)`: its `55`
points can be labelled by the edges of `K₁₁` so that two points are adjacent
exactly when the two edges share an endpoint.

The labelling sends a point to the pair of grand cliques through it
(`Derived45.exists_grandCliques_pair`); there are `11` grand cliques
(`Derived45.card_grandCliques`), the map is injective
(`Derived45.cliquePair_injective`) because the two grand cliques through a point
meet in that point alone — the `K₁ ∩ K₂ = {x}` clause of
`Derived45.exists_grandCliques_pair` — and it is therefore bijective because
`55 = binomial 11 2`. -/
theorem blockGraph_iso_T11 :
    ∃ φ : P ≃ Edge11, ∀ p q, E.blockGraph.Adj p q ↔ Edge11.vmeet (φ p) (φ q) = 1 := by
  obtain ⟨ψ⟩ : Nonempty ({K : Finset P // K ∈ E.grandCliques} ≃ Fin 11) :=
    ⟨Finset.equivFinOfCardEq E.card_grandCliques⟩
  exact ⟨Equiv.ofBijective _ (E.pointEdge_bijective ψ), E.adj_iff_vmeet_pointEdge ψ⟩

/-- The `T(11)` labelling of
`Derived45.blockGraph_iso_T11`, carrying in addition the pair-multiplicity
identity

`t p q + vmeet (φ p) (φ q) = 2 + 9 · [p = q]`.

This is `SRG266.QuasiSymmetric.CherryCover.pairCount_add_vmeet` read backwards:
its `vmeet = 1` case is the `cherry_exact` axiom, its `vmeet = 0` case is
`disjoint_twice`, and its diagonal case supplies the `9` that drives the
`two_regular` variance count of `Derived45.toCherryCover`. -/
theorem exists_equiv_edge11 :
    ∃ φ : P ≃ Edge11,
      (∀ p q, E.blockGraph.Adj p q ↔ Edge11.vmeet (φ p) (φ q) = 1) ∧
      ∀ p q, E.pairMult p q + Edge11.vmeet (φ p) (φ q) = 2 + if p = q then 9 else 0 := by
  obtain ⟨ψ⟩ : Nonempty ({K : Finset P // K ∈ E.grandCliques} ≃ Fin 11) :=
    ⟨Finset.equivFinOfCardEq E.card_grandCliques⟩
  exact ⟨Equiv.ofBijective _ (E.pointEdge_bijective ψ), E.adj_iff_vmeet_pointEdge ψ,
    E.pairMult_add_vmeet_pointEdge ψ⟩

end Derived45

end SRG266.QuasiSymmetric
