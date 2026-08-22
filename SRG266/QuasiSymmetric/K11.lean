/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.BlockGraph

/-!
# The `K₁₁` coordinates of a `Derived45`

Once the block graph of a `SRG266.QuasiSymmetric.Derived45` is
known to be the triangular graph `T(11)` its `55` points are the edges of the
complete graph `K₁₁`, each of the `45` blocks becomes a `2`-regular spanning
subgraph, and the blocks *exactly cover the cherries* of `K₁₁` — a cherry being
an unordered pair of adjacent edges.

`SRG266.QuasiSymmetric.CherryCover` packages that picture with three axioms:
each member is `2`-regular, each cherry lies in exactly one member, each
disjoint pair of edges lies in exactly two.  The file proves

* `CherryCover.edge_rep`: every edge lies in exactly `9` members;
* `CherryCover.pairCount_add_vmeet`: the single identity
  `#{i | e, f ∈ g i} + #(common endpoints of e and f) = 2 + 9·[e = f]`,
  which is the whole combinatorial content of the axioms and which drives both
  this file and `SRG266/QuasiSymmetric/ArcDegree.lean`;
* `CherryCover.block_card`: every member has `11` edges;
* `CherryCover.pair_meet`: two distinct members share exactly `2` edges;
* `CherryCover.toDerived45`: a cherry cover is a `Derived45`.

The `55` points are `SRG266.QuasiSymmetric.Edge11`, the off-diagonal part of
`Sym2 (Fin 11)`.  Nothing here uses `decide` or any external datum.
-/

open scoped BigOperators

namespace SRG266.QuasiSymmetric

/-! ### The edges of `K₁₁` -/

/-- The `55` edges of the complete graph `K₁₁`: the unordered pairs of distinct
elements of `Fin 11`. -/
abbrev Edge11 : Type := {e : Sym2 (Fin 11) // ¬ e.IsDiag}

namespace Edge11

/-- The edge joining two distinct vertices. -/
def mk' {v a : Fin 11} (h : v ≠ a) : Edge11 := ⟨s(v, a), by simpa using h⟩

/-- The two endpoints of an edge. -/
def vertices (e : Edge11) : Finset (Fin 11) := (e : Sym2 (Fin 11)).toFinset

@[simp] theorem mem_vertices {v : Fin 11} {e : Edge11} :
    v ∈ e.vertices ↔ v ∈ (e : Sym2 (Fin 11)) := Sym2.mem_toFinset

/-- An edge has exactly two endpoints. -/
theorem card_vertices (e : Edge11) : e.vertices.card = 2 :=
  Sym2.card_toFinset_of_not_isDiag _ e.2

/-- The endpoints of `mk' h`. -/
theorem vertices_mk' {v a : Fin 11} (h : v ≠ a) : (mk' h).vertices = {v, a} :=
  Sym2.toFinset_mk_eq

/-- An edge with two prescribed distinct endpoints is determined by them. -/
theorem eq_of_mem_mem {e : Edge11} {v a : Fin 11} (hva : v ≠ a)
    (hv : v ∈ e.vertices) (ha : a ∈ e.vertices) : e = mk' hva := by
  apply Subtype.ext
  exact (Sym2.mem_and_mem_iff hva).mp ⟨mem_vertices.mp hv, mem_vertices.mp ha⟩

/-- Every edge has an endpoint. -/
theorem exists_mem_vertices (e : Edge11) : ∃ v, v ∈ e.vertices := by
  have h : e.vertices.card ≠ 0 := by rw [card_vertices]; norm_num
  exact Finset.card_ne_zero.mp h

/-- The number of common endpoints of two edges. -/
def vmeet (e f : Edge11) : ℕ := (e.vertices ∩ f.vertices).card

/-- The number of common endpoints is symmetric. -/
theorem vmeet_comm (e f : Edge11) : vmeet e f = vmeet f e := by
  rw [vmeet, vmeet, Finset.inter_comm]

/-- An edge meets itself in its two endpoints. -/
theorem vmeet_self (e : Edge11) : vmeet e e = 2 := by
  rw [vmeet, Finset.inter_self, card_vertices]

/-- Two distinct edges share at most one endpoint. -/
theorem vmeet_le_one {e f : Edge11} (h : e ≠ f) : vmeet e f ≤ 1 := by
  by_contra hcon
  obtain ⟨v, hv, a, ha, hva⟩ := Finset.one_lt_card.mp (by omega : 1 < vmeet e f)
  rw [Finset.mem_inter] at hv ha
  exact h ((eq_of_mem_mem hva hv.1 ha.1).trans (eq_of_mem_mem hva hv.2 ha.2).symm)

/-- Two edges through a common vertex meet in exactly one endpoint unless they
are equal. -/
theorem vmeet_eq_one {e f : Edge11} (hef : e ≠ f) {v : Fin 11} (hv : v ∈ e.vertices)
    (hvf : v ∈ f.vertices) : vmeet e f = 1 := by
  have hge : 1 ≤ vmeet e f :=
    Finset.card_pos.mpr ⟨v, Finset.mem_inter.mpr ⟨hv, hvf⟩⟩
  have hle := vmeet_le_one hef
  omega

/-- The edges through a vertex. -/
def star (v : Fin 11) : Finset Edge11 := Finset.univ.filter fun e => v ∈ e.vertices

@[simp] theorem mem_star {v : Fin 11} {e : Edge11} : e ∈ star v ↔ v ∈ e.vertices := by
  simp [star]

/-- Every vertex of `K₁₁` lies on `10` edges. -/
theorem card_star (v : Fin 11) : (star v).card = 10 := by
  classical
  have hcard : ((Finset.univ : Finset (Fin 11)).erase v).card = 10 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
  rw [← hcard]
  refine (Finset.card_bij (fun a ha => mk' (Ne.symm (Finset.mem_erase.mp ha).1))
    ?_ ?_ ?_).symm
  · intro a ha
    rw [mem_star, vertices_mk']
    simp
  · intro a₁ ha₁ a₂ ha₂ hEq
    have h₁ : a₁ ∈ (mk' (Ne.symm (Finset.mem_erase.mp ha₁).1)).vertices := by
      rw [vertices_mk']; simp
    rw [hEq, vertices_mk'] at h₁
    have hne : a₁ ≠ v := (Finset.mem_erase.mp ha₁).1
    simpa [hne] using h₁
  · intro e he
    rw [mem_star] at he
    obtain ⟨a, ha, hav⟩ : ∃ a ∈ e.vertices, a ≠ v := by
      have hlt : 1 < e.vertices.card := by rw [card_vertices]; norm_num
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hlt
      by_cases hxv : x = v
      · exact ⟨y, hy, fun h => hxy (hxv.trans h.symm)⟩
      · exact ⟨x, hx, hxv⟩
    refine ⟨a, Finset.mem_erase.mpr ⟨hav, Finset.mem_univ a⟩, ?_⟩
    exact (eq_of_mem_mem (Ne.symm hav) he ha).symm

/-- There are `55` edges in `K₁₁`. -/
theorem card_edge11 : Fintype.card Edge11 = 55 := by
  rw [Sym2.card_subtype_not_diag, Fintype.card_fin]
  rfl

/-! #### Two double counts over the vertices -/

/-- Counting the incidences between a set of edges and the vertices. -/
theorem sum_star_card (s : Finset Edge11) :
    (∑ v : Fin 11, (s.filter fun e => v ∈ e.vertices).card) = ∑ e ∈ s, e.vertices.card := by
  classical
  have hl : ∀ v : Fin 11, (s.filter fun e => v ∈ e.vertices).card =
      ∑ e ∈ s, if v ∈ e.vertices then 1 else 0 := fun v => Finset.card_filter _ _
  have hr : ∀ e : Edge11, (∑ v : Fin 11, if v ∈ e.vertices then 1 else 0) =
      e.vertices.card := by
    intro e
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.sum_congr rfl fun v _ => hl v, ← Finset.sum_congr rfl fun e _ => hr e,
    Finset.sum_comm]

/-- Counting the pairs of edges of `s` through a common vertex. -/
theorem sum_vmeet (s : Finset Edge11) :
    (∑ e ∈ s, ∑ f ∈ s, vmeet e f) =
      ∑ v : Fin 11, (s.filter fun e => v ∈ e.vertices).card ^ 2 := by
  classical
  have hl : ∀ e f : Edge11, vmeet e f =
      ∑ v : Fin 11, (if v ∈ e.vertices then 1 else 0) * (if v ∈ f.vertices then 1 else 0) := by
    intro e f
    have hsub : ∀ v : Fin 11, (if v ∈ e.vertices then 1 else 0) *
        (if v ∈ f.vertices then 1 else 0) =
          if v ∈ e.vertices ∩ f.vertices then 1 else 0 := by
      intro v
      by_cases h1 : v ∈ e.vertices <;> by_cases h2 : v ∈ f.vertices <;> simp [h1, h2]
    rw [Finset.sum_congr rfl fun v _ => hsub v, ← Finset.card_filter,
      Finset.filter_mem_eq_inter, Finset.univ_inter]
    rfl
  have hr : ∀ v : Fin 11, (s.filter fun e => v ∈ e.vertices).card ^ 2 =
      ∑ e ∈ s, ∑ f ∈ s, (if v ∈ e.vertices then 1 else 0) *
        (if v ∈ f.vertices then 1 else 0) := by
    intro v
    rw [sq, Finset.card_filter, Finset.sum_mul_sum]
  calc (∑ e ∈ s, ∑ f ∈ s, vmeet e f)
      = ∑ e ∈ s, ∑ f ∈ s, ∑ v : Fin 11,
          (if v ∈ e.vertices then 1 else 0) * (if v ∈ f.vertices then 1 else 0) :=
        Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => hl e f
    _ = ∑ e ∈ s, ∑ v : Fin 11, ∑ f ∈ s,
          (if v ∈ e.vertices then 1 else 0) * (if v ∈ f.vertices then 1 else 0) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ v : Fin 11, ∑ e ∈ s, ∑ f ∈ s,
          (if v ∈ e.vertices then 1 else 0) * (if v ∈ f.vertices then 1 else 0) :=
        Finset.sum_comm
    _ = ∑ v : Fin 11, (s.filter fun e => v ∈ e.vertices).card ^ 2 :=
        (Finset.sum_congr rfl fun v _ => hr v).symm

/-! #### Relabelling the vertices -/

/-- The action of a permutation of the `11` vertices on the `55` edges. -/
def map (σ : Equiv.Perm (Fin 11)) (e : Edge11) : Edge11 :=
  ⟨Sym2.map σ (e : Sym2 (Fin 11)), by
    rw [Sym2.isDiag_map σ.injective]
    exact e.2⟩

@[simp] theorem coe_map (σ : Equiv.Perm (Fin 11)) (e : Edge11) :
    ((map σ e : Edge11) : Sym2 (Fin 11)) = Sym2.map σ (e : Sym2 (Fin 11)) := rfl

/-- Relabelling the vertices is a bijection of the edges. -/
def mapEquiv (σ : Equiv.Perm (Fin 11)) : Edge11 ≃ Edge11 where
  toFun := map σ
  invFun := map σ.symm
  left_inv e := by
    apply Subtype.ext
    simp [Sym2.map_map]
  right_inv e := by
    apply Subtype.ext
    simp [Sym2.map_map]

/-- Relabelling the vertices is injective on edges. -/
theorem map_injective (σ : Equiv.Perm (Fin 11)) : Function.Injective (map σ) :=
  (mapEquiv σ).injective

/-- Relabelling the vertices is surjective on edges. -/
theorem map_surjective (σ : Equiv.Perm (Fin 11)) : Function.Surjective (map σ) :=
  (mapEquiv σ).surjective

/-- The endpoints of a relabelled edge. -/
theorem vertices_map (σ : Equiv.Perm (Fin 11)) (e : Edge11) :
    (map σ e).vertices = e.vertices.image σ := by
  ext v
  simp only [mem_vertices, coe_map, Sym2.mem_map, Finset.mem_image]

/-- A vertex lies on a relabelled edge exactly when its preimage lies on the
original one. -/
theorem mem_vertices_map {σ : Equiv.Perm (Fin 11)} {v : Fin 11} {e : Edge11} :
    v ∈ (map σ e).vertices ↔ σ.symm v ∈ e.vertices := by
  rw [vertices_map]
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
    simpa using ha
  · intro h
    exact Finset.mem_image.mpr ⟨σ.symm v, h, by simp⟩

/-- Relabelling preserves the number of common endpoints. -/
theorem vmeet_map (σ : Equiv.Perm (Fin 11)) (e f : Edge11) :
    vmeet (map σ e) (map σ f) = vmeet e f := by
  classical
  rw [vmeet, vmeet, vertices_map, vertices_map,
    ← Finset.image_inter _ _ σ.injective,
    Finset.card_image_of_injective _ σ.injective]

end Edge11

/-! ### Cherry covers -/

/-- A *cherry cover* of `K₁₁`: `45` sets of edges, each `2`-regular,
covering each cherry (pair of adjacent edges) exactly once and each disjoint
pair of edges exactly twice.

This is the `K₁₁` presentation of a `SRG266.QuasiSymmetric.Derived45`; see
`CherryCover.toDerived45`. -/
structure CherryCover where
  /-- The `45` members of the cover. -/
  g : Fin 45 → Finset Edge11
  /-- Every member is `2`-regular: each vertex lies on exactly two of its
  edges. -/
  two_regular : ∀ i v, ((g i).filter fun e => v ∈ e.vertices).card = 2
  /-- Every cherry lies in exactly one member. -/
  cherry_exact : ∀ e f : Edge11, e ≠ f → Edge11.vmeet e f = 1 → pairCount g e f = 1
  /-- Every disjoint pair of edges lies in exactly two members. -/
  disjoint_twice : ∀ e f : Edge11, Edge11.vmeet e f = 0 → pairCount g e f = 2

namespace CherryCover

variable (C : CherryCover)

/-- Every edge of `K₁₁` lies in exactly `9` members of a cherry
cover.

Fix an endpoint `v` of `e`.  The `9` other edges at `v` each form a cherry with
`e`, hence lie in exactly one common member; conversely a member containing `e`
has exactly two edges at `v`, one of which is `e`.  Both counts of the incident
pairs give `9`. -/
theorem edge_rep (e : Edge11) : pairCount C.g e e = 9 := by
  classical
  obtain ⟨v, hv⟩ := Edge11.exists_mem_vertices e
  have hemem : e ∈ Edge11.star v := Edge11.mem_star.mpr hv
  set F : Finset Edge11 := (Edge11.star v).erase e with hF
  have hFcard : F.card = 9 := by
    rw [hF, Finset.card_erase_of_mem hemem, Edge11.card_star]
  -- one side: every cherry at `v` through `e` lies in exactly one member
  have hone : ∀ f ∈ F, pairCount C.g e f = 1 := by
    intro f hf
    have hfe : f ≠ e := (Finset.mem_erase.mp hf).1
    have hvf : v ∈ f.vertices :=
      Edge11.mem_star.mp (Finset.mem_of_mem_erase hf)
    exact C.cherry_exact e f (Ne.symm hfe) (Edge11.vmeet_eq_one (Ne.symm hfe) hv hvf)
  -- other side: a member through `e` has exactly one other edge at `v`
  have hother : ∀ i ∈ starFinset C.g e, (F ∩ C.g i).card = 1 := by
    intro i hi
    have hei : e ∈ C.g i := by simpa [starFinset] using hi
    have hset : F ∩ C.g i = ((C.g i).filter fun f => v ∈ f.vertices).erase e := by
      ext f
      simp only [hF, Finset.mem_inter, Finset.mem_erase, Finset.mem_filter,
        Edge11.mem_star]
      tauto
    rw [hset, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hei, hv⟩),
      C.two_regular i v]
  have hsum := sum_star_inter_card C.g e F
  rw [Finset.sum_congr rfl hother, Finset.sum_congr rfl hone, Finset.sum_const,
    Finset.sum_const, hFcard] at hsum
  rw [pairCount_self]
  simpa using hsum

/-- **The identity that carries the whole file.**  For any two edges, the
number of members containing both, plus the number of common endpoints, is `2`
— except on the diagonal, where it is `11`. -/
theorem pairCount_add_vmeet (e f : Edge11) :
    pairCount C.g e f + Edge11.vmeet e f = 2 + if e = f then 9 else 0 := by
  by_cases hef : e = f
  · subst hef
    rw [C.edge_rep e, Edge11.vmeet_self]
    simp
  · rcases Nat.eq_zero_or_pos (Edge11.vmeet e f) with h0 | hpos
    · rw [C.disjoint_twice e f h0, h0]
      simp [hef]
    · have h1 : Edge11.vmeet e f = 1 := le_antisymm (Edge11.vmeet_le_one hef) hpos
      rw [C.cherry_exact e f hef h1, h1]
      simp [hef]

/-- Every member of a cherry cover has `11` edges: it is a `2`-regular
spanning subgraph of `K₁₁`. -/
theorem block_card (i : Fin 45) : (C.g i).card = 11 := by
  have h := Edge11.sum_star_card (C.g i)
  rw [Finset.sum_congr rfl fun v _ => C.two_regular i v,
    Finset.sum_congr rfl fun e _ => Edge11.card_vertices e, Finset.sum_const,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, smul_eq_mul] at h
  omega

/-- The sum over the members of a cherry cover of their traces on a fixed
member: `11 · 9 = 99`. -/
theorem sum_inter_block (i : Fin 45) :
    (∑ j, ((C.g i) ∩ (C.g j)).card) = 99 := by
  have h := sum_inter_card C.g (C.g i)
  have hstar : ∀ e ∈ C.g i, (starFinset C.g e).card = 9 := by
    intro e _
    rw [← pairCount_self, C.edge_rep e]
  rw [Finset.sum_congr rfl hstar, Finset.sum_const, C.block_card i] at h
  simpa using h

/-- The sum over the members of a cherry cover of the squared traces on a fixed
member: `297 = 341 − 44`. -/
theorem sum_inter_block_sq (i : Fin 45) :
    (∑ j, ((C.g i) ∩ (C.g j)).card ^ 2) = 297 := by
  classical
  have h := sum_inter_card_sq C.g (C.g i)
  -- the `vmeet` half is `44`: each of the `11` vertices carries `2² = 4`
  have hvm : (∑ e ∈ C.g i, ∑ f ∈ C.g i, Edge11.vmeet e f) = 44 := by
    rw [Edge11.sum_vmeet, Finset.sum_congr rfl fun v _ => by
      rw [C.two_regular i v], Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  -- the combined sum is `2 · 11² + 9 · 11 = 341`
  have htot : (∑ e ∈ C.g i, ∑ f ∈ C.g i,
      (pairCount C.g e f + Edge11.vmeet e f)) = 341 := by
    have hcell : ∀ e ∈ C.g i,
        (∑ f ∈ C.g i, (pairCount C.g e f + Edge11.vmeet e f)) = 31 := by
      intro e he
      rw [Finset.sum_congr rfl fun f _ => C.pairCount_add_vmeet e f,
        Finset.sum_add_distrib, Finset.sum_const, C.block_card i,
        Finset.sum_ite_eq (C.g i) e (fun _ => 9), if_pos he]
      norm_num
    rw [Finset.sum_congr rfl hcell, Finset.sum_const, C.block_card i]
    norm_num
  have hsplit : (∑ e ∈ C.g i, ∑ f ∈ C.g i, (pairCount C.g e f + Edge11.vmeet e f)) =
      (∑ e ∈ C.g i, ∑ f ∈ C.g i, pairCount C.g e f) +
        ∑ e ∈ C.g i, ∑ f ∈ C.g i, Edge11.vmeet e f := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => Finset.sum_add_distrib
  rw [hsplit, hvm] at htot
  rw [h]
  omega

/-- **The pairwise intersection.**  Two distinct members of a cherry cover
share exactly `2` edges.

The `44` numbers `x_j = |g i ∩ g j|` satisfy `∑ x_j = 88` and `∑ x_j² = 176`,
i.e. they have zero variance about their mean `2`. -/
theorem pair_meet (i j : Fin 45) (hij : i ≠ j) : ((C.g i) ∩ (C.g j)).card = 2 := by
  classical
  have hdiag : ((C.g i) ∩ (C.g i)).card = 11 := by
    rw [Finset.inter_self, C.block_card i]
  have hsum : (∑ j ∈ Finset.univ.erase i, ((C.g i) ∩ (C.g j)).card) = 88 := by
    have h := Finset.sum_erase_add Finset.univ
      (fun j => ((C.g i) ∩ (C.g j)).card) (Finset.mem_univ i)
    rw [C.sum_inter_block i, hdiag] at h
    omega
  have hsq : (∑ j ∈ Finset.univ.erase i, ((C.g i) ∩ (C.g j)).card ^ 2) = 176 := by
    have h := Finset.sum_erase_add Finset.univ
      (fun j => ((C.g i) ∩ (C.g j)).card ^ 2) (Finset.mem_univ i)
    rw [C.sum_inter_block_sq i, hdiag] at h
    omega
  have hcard : (Finset.univ.erase i).card = 44 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  have hle : ∀ k ∈ Finset.univ.erase i,
      4 * ((C.g i) ∩ (C.g k)).card ≤ ((C.g i) ∩ (C.g k)).card ^ 2 + 4 :=
    fun k _ => four_mul_le_sq_add_four _
  have heq : (∑ k ∈ Finset.univ.erase i, 4 * ((C.g i) ∩ (C.g k)).card) =
      ∑ k ∈ Finset.univ.erase i, (((C.g i) ∩ (C.g k)).card ^ 2 + 4) := by
    rw [← Finset.mul_sum, hsum, Finset.sum_add_distrib, hsq, Finset.sum_const, hcard]
    norm_num
  have hpt := (Finset.sum_eq_sum_iff_of_le hle).mp heq j
    (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
  have hz : ((((C.g i) ∩ (C.g j)).card : ℤ) - 2) ^ 2 = 0 := by
    have hcast : (4 : ℤ) * (((C.g i) ∩ (C.g j)).card : ℤ) =
        (((C.g i) ∩ (C.g j)).card : ℤ) ^ 2 + 4 := by exact_mod_cast hpt
    linear_combination -hcast
  have htwo : (((C.g i) ∩ (C.g j)).card : ℤ) = 2 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
    linarith
  exact_mod_cast htwo

/-! ### A cherry cover is a `Derived45` -/

/-- A cherry cover of `K₁₁` is a `Derived45` on its `55`
edges. -/
def toDerived45 : Derived45 Edge11 where
  block := C.g
  point_card := Edge11.card_edge11
  block_card := C.block_card
  pair_meet := C.pair_meet
  replication := fun e => by
    have h := C.edge_rep e
    rw [pairCount_self] at h
    exact h

/-! ### Relabelling a cherry cover -/

/-- Relabelling the vertices does not change the pair counts. -/
theorem pairCount_image (σ : Equiv.Perm (Fin 11)) (g : Fin 45 → Finset Edge11)
    (e f : Edge11) :
    pairCount (fun i => (g i).image (Edge11.map σ)) (Edge11.map σ e) (Edge11.map σ f) =
      pairCount g e f := by
  classical
  have hinj := Edge11.map_injective σ
  refine congrArg Finset.card (Finset.filter_congr fun i _ => ?_)
  rw [hinj.mem_finset_image, hinj.mem_finset_image]

/-- Relabelling the `11` vertices carries cherry covers to cherry
covers.  This is what transports a bound proved for a *listed* family to the
family actually at hand. -/
def relabel (σ : Equiv.Perm (Fin 11)) (C : CherryCover) : CherryCover where
  g i := (C.g i).image (Edge11.map σ)
  two_regular := by
    classical
    intro i v
    rw [Finset.filter_image,
      Finset.card_image_of_injective _ (Edge11.map_injective σ),
      Finset.filter_congr fun e _ => Edge11.mem_vertices_map (σ := σ) (v := v) (e := e),
      C.two_regular i (σ.symm v)]
  cherry_exact := by
    intro e' f' hef hvm
    obtain ⟨e, rfl⟩ := Edge11.map_surjective σ e'
    obtain ⟨f, rfl⟩ := Edge11.map_surjective σ f'
    rw [pairCount_image]
    rw [Edge11.vmeet_map] at hvm
    exact C.cherry_exact e f (fun h => hef (congrArg (Edge11.map σ) h)) hvm
  disjoint_twice := by
    intro e' f' hvm
    obtain ⟨e, rfl⟩ := Edge11.map_surjective σ e'
    obtain ⟨f, rfl⟩ := Edge11.map_surjective σ f'
    rw [pairCount_image]
    rw [Edge11.vmeet_map] at hvm
    exact C.disjoint_twice e f hvm

/-- The members of a relabelled cherry cover. -/
@[simp] theorem relabel_g (σ : Equiv.Perm (Fin 11)) (C : CherryCover) (i : Fin 45) :
    (C.relabel σ).g i = (C.g i).image (Edge11.map σ) := rfl

end CherryCover

/-- The blocks of the `Derived45` attached to a cherry cover are
the members of the cover: a cherry cover of `K₁₁` *is* a `Derived45`, in the
`K₁₁` coordinates. -/
theorem cherryCover_toDerived45 (C : CherryCover) : C.toDerived45.block = C.g := rfl

end SRG266.QuasiSymmetric
