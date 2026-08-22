/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.ArcDegree
import SRG266.QuasiSymmetric.PairMultiplicity

/-!
# Rigidity of a residual structure over a cherry cover

Fix a `SRG266.QuasiSymmetric.CherryCover` `C` of `K₁₁` and a hypothetical
`SRG266.QuasiSymmetric.Residual165` `R` of the derived design it carries. Two
facts determine the residual structure:

* every residual block is a `{12; 3}`-arc, hence a cubic graph on
  exactly `8` of the `11` vertices, the other `3` being isolated
  (`SRG266.QuasiSymmetric.IsArc.arc_is_cubic_on_eight`);
* every edge lies on `36` residual blocks, and two distinct edges lie on
  `9 − pairCount` of them (`SRG266.QuasiSymmetric.residual_pairMult`), i.e. on
  `8` for a cherry and `7` for a disjoint pair.

Writing `R.isolating v` for the residual blocks in which `v` is isolated:

| lemma | statement |
|---|---|
| `Residual165.card_isolating` | `#(R.isolating v) = 45` |
| `Residual165.card_isolating_through` | `12` blocks contain a fixed edge `e` and isolate `v ∉ e` |
| `Residual165.meet_of_isolating` | two blocks isolating a common vertex meet in `3` edges |
| `Residual165.localDesign_pairMult` | two edges off `v` lie on `3` blocks isolating `v` |
| `Residual165.card_isolating_pair` | `9` blocks isolate two given vertices |
| `Residual165.card_isolating_triple` | **exactly one** block isolates three given vertices |
| `Residual165.isolatedTriple_bijOn` | `block ↦ isolated triple` is a bijection onto the `165` triples |

The fourth line says that, for every vertex `v`, the `45` blocks isolating `v`
form a **symmetric `2-(45, 12, 3)` design** whose points are the `45` edges of
`K₁₁ − v` and whose blocks are cubic graphs on `8` of the remaining `10`
vertices; the last line is the *triple bijection*: a residual structure, if one
exists, is indexed by the `165 = C(11, 3)` triples of vertices, each block
isolating its own triple.

The proofs are finite double counts and zero-variance arguments.
-/

open scoped BigOperators

namespace SRG266.QuasiSymmetric

/-! ### Generic incidence double counts over an index `Finset`

The three identities below are the `Finset`-indexed companions of
`SRG266.QuasiSymmetric.sum_inter_card` and
`SRG266.QuasiSymmetric.sum_inter_card_sq`: they read a sum over a *subfamily*
of a family of finite sets as a sum over a fixed set of points.  All three are
proved by expanding both sides into `0/1` indicators and exchanging the order
of summation. -/

section LocalCount

variable {P ι : Type*} [DecidableEq P]

/-- Incidences between a fixed point set `t` and a subfamily `s` of the family
`g`, counted in the two possible orders. -/
theorem sum_inter_card_over (s : Finset ι) (g : ι → Finset P) (t : Finset P) :
    (∑ i ∈ s, (t ∩ g i).card) = ∑ p ∈ t, (s.filter fun i => p ∈ g i).card := by
  have hl : ∀ i : ι, (t ∩ g i).card = ∑ p ∈ t, if p ∈ g i then 1 else 0 := fun i => by
    rw [← Finset.filter_mem_eq_inter, Finset.card_filter]
  have hr : ∀ p : P, (s.filter fun i => p ∈ g i).card =
      ∑ i ∈ s, if p ∈ g i then 1 else 0 := fun p => Finset.card_filter _ _
  rw [Finset.sum_congr rfl fun i _ => hl i, Finset.sum_congr rfl fun p _ => hr p,
    Finset.sum_comm]

/-- The product of the traces of a subfamily on two fixed point sets, summed
over the subfamily, counts the pairs of points covered together. -/
theorem sum_mul_inter_card_over (s : Finset ι) (g : ι → Finset P) (t u : Finset P) :
    (∑ i ∈ s, (t ∩ g i).card * (u ∩ g i).card) =
      ∑ p ∈ t, ∑ q ∈ u, (s.filter fun i => p ∈ g i ∧ q ∈ g i).card := by
  have hl : ∀ i : ι, (t ∩ g i).card * (u ∩ g i).card =
      ∑ p ∈ t, ∑ q ∈ u, (if p ∈ g i then 1 else 0) * (if q ∈ g i then 1 else 0) := by
    intro i
    rw [← Finset.filter_mem_eq_inter, ← Finset.filter_mem_eq_inter, Finset.card_filter,
      Finset.card_filter, Finset.sum_mul_sum]
  have hr : ∀ p q : P, (s.filter fun i => p ∈ g i ∧ q ∈ g i).card =
      ∑ i ∈ s, (if p ∈ g i then 1 else 0) * (if q ∈ g i then 1 else 0) := by
    intro p q
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : p ∈ g i <;> by_cases h2 : q ∈ g i <;> simp [h1, h2]
  rw [Finset.sum_congr rfl fun i _ => hl i,
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => hr p q, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- The squared replication numbers of a subfamily `s` inside a point set `t`
containing all its members count the ordered pairs of members weighted by their
intersection. -/
theorem sum_card_filter_sq (s : Finset ι) (g : ι → Finset P) (t : Finset P)
    (hsub : ∀ i ∈ s, g i ⊆ t) :
    (∑ p ∈ t, (s.filter fun i => p ∈ g i).card ^ 2) =
      ∑ m ∈ s, ∑ n ∈ s, ((g m) ∩ (g n)).card := by
  have hl : ∀ p : P, (s.filter fun i => p ∈ g i).card ^ 2 =
      ∑ m ∈ s, ∑ n ∈ s, (if p ∈ g m then 1 else 0) * (if p ∈ g n then 1 else 0) := by
    intro p
    rw [sq, Finset.card_filter, Finset.sum_mul_sum]
  have hr : ∀ m ∈ s, ∀ n ∈ s, ((g m) ∩ (g n)).card =
      ∑ p ∈ t, (if p ∈ g m then 1 else 0) * (if p ∈ g n then 1 else 0) := by
    intro m hm n _
    have hsubset : (g m) ∩ (g n) ⊆ t := Finset.inter_subset_left.trans (hsub m hm)
    have hpt : ∀ p : P, (if p ∈ g m then (1 : ℕ) else 0) * (if p ∈ g n then 1 else 0) =
        if p ∈ (g m) ∩ (g n) then 1 else 0 := by
      intro p
      by_cases h1 : p ∈ g m <;> by_cases h2 : p ∈ g n <;> simp [h1, h2]
    rw [Finset.sum_congr rfl fun p _ => hpt p, ← Finset.card_filter,
      Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsubset]
  rw [Finset.sum_congr rfl fun p _ => hl p, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun n hn => (hr m hm n hn).symm

/-- A function taking only the values `0` and `c` on a `Finset` is determined by
its sum: the fibre over `0` has `#s − (∑ f) / c` elements. -/
theorem sum_add_mul_card_filter_eq (c : ℕ) (s : Finset ι) (f : ι → ℕ)
    (hc : ∀ i ∈ s, f i = 0 ∨ f i = c) :
    (∑ i ∈ s, f i) + c * (s.filter fun i => f i = 0).card = c * s.card := by
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun i => f i = 0) f
  have hzero : (∑ i ∈ s.filter fun i => f i = 0, f i) = 0 :=
    Finset.sum_eq_zero fun i hi => (Finset.mem_filter.mp hi).2
  have hval : ∀ i ∈ s.filter fun i => ¬ f i = 0, f i = c := by
    intro i hi
    have h := Finset.mem_filter.mp hi
    exact (hc i h.1).resolve_left h.2
  have hne : (∑ i ∈ s.filter fun i => ¬ f i = 0, f i) =
      c * (s.filter fun i => ¬ f i = 0).card := by
    rw [Finset.sum_congr rfl hval, Finset.sum_const, smul_eq_mul, mul_comm]
  have hcard := Finset.card_filter_add_card_filter_not (s := s) (p := fun i => f i = 0)
  have hsum : (∑ i ∈ s, f i) = c * (s.filter fun i => ¬ f i = 0).card := by
    rw [← hsplit, hzero, hne, zero_add]
  rw [hsum, ← Nat.mul_add]
  congr 1
  omega

end LocalCount

/-! ### Two elementary numeric facts -/

/-- For every natural number `x` one has `6 x ≤ x² + 9`, with equality exactly
at `x = 3`. -/
theorem six_mul_le_sq_add_nine (x : ℕ) : 6 * x ≤ x ^ 2 + 9 := by
  nlinarith [sq_nonneg ((x : ℤ) - 3), Int.ofNat_le.mpr (Nat.zero_le x)]

/-- The equality case of `SRG266.QuasiSymmetric.six_mul_le_sq_add_nine`. -/
theorem eq_three_of_six_mul_eq {x : ℕ} (h : 6 * x = x ^ 2 + 9) : x = 3 := by
  have hcast : (6 : ℤ) * (x : ℤ) = (x : ℤ) ^ 2 + 9 := by exact_mod_cast h
  have hz : ((x : ℤ) - 3) ^ 2 = 0 := by linear_combination -hcast
  have hroot := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
  have hx : (x : ℤ) = 3 := by linarith
  exact_mod_cast hx

/-! ### The edges of `K₁₁` missing one or two vertices -/

namespace Edge11

/-- The `45` edges of `K₁₁` missing a given vertex. -/
def off (v : Fin 11) : Finset Edge11 := Finset.univ.filter fun e => v ∉ e.vertices

/-- The `36` edges of `K₁₁` missing two given vertices. -/
def off₂ (u v : Fin 11) : Finset Edge11 :=
  Finset.univ.filter fun e => u ∉ e.vertices ∧ v ∉ e.vertices

@[simp] theorem mem_off {v : Fin 11} {e : Edge11} : e ∈ off v ↔ v ∉ e.vertices := by
  simp [off]

@[simp] theorem mem_off₂ {u v : Fin 11} {e : Edge11} :
    e ∈ off₂ u v ↔ u ∉ e.vertices ∧ v ∉ e.vertices := by
  simp [off₂]

/-- The only edge through `w` and a second prescribed vertex `a`. -/
theorem star_filter_mem {w a : Fin 11} (h : w ≠ a) :
    ((star w).filter fun e => a ∈ e.vertices) = {mk' h} := by
  ext e
  simp only [Finset.mem_filter, mem_star, Finset.mem_singleton]
  constructor
  · rintro ⟨hw, ha⟩
    exact eq_of_mem_mem h hw ha
  · rintro rfl
    rw [vertices_mk']
    simp

/-- **`45` edges miss a vertex.** -/
theorem card_off (v : Fin 11) : (off v).card = 45 := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset Edge11)) (p := fun e => v ∈ e.vertices)
  have hstar : ((Finset.univ : Finset Edge11).filter fun e => v ∈ e.vertices) = star v := rfl
  have hoff : ((Finset.univ : Finset Edge11).filter fun e => ¬ v ∈ e.vertices) = off v := rfl
  rw [hstar, hoff, card_star, Finset.card_univ, card_edge11] at hsplit
  omega

/-- The edges through `v` and missing `u` are the star of `v` minus the edge
`uv`. -/
theorem off_filter_mem {u v : Fin 11} (huv : u ≠ v) :
    ((off u).filter fun e => v ∈ e.vertices) = (star v).erase (mk' (Ne.symm huv)) := by
  ext e
  simp only [Finset.mem_filter, mem_off, Finset.mem_erase, mem_star]
  constructor
  · rintro ⟨hu, hv⟩
    refine ⟨fun hcon => hu ?_, hv⟩
    rw [hcon, vertices_mk']
    simp
  · rintro ⟨hne, hv⟩
    refine ⟨fun hu => hne ?_, hv⟩
    exact eq_of_mem_mem (Ne.symm huv) hv hu

/-- **`36` edges miss two vertices.** -/
theorem card_off₂ {u v : Fin 11} (huv : u ≠ v) : (off₂ u v).card = 36 := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := off u) (p := fun e => v ∈ e.vertices)
  have hmem : ((off u).filter fun e => v ∈ e.vertices).card = 9 := by
    rw [off_filter_mem huv, Finset.card_erase_of_mem, card_star]
    rw [mem_star, vertices_mk']
    simp
  have hnot : ((off u).filter fun e => ¬ v ∈ e.vertices) = off₂ u v := by
    ext e
    simp only [Finset.mem_filter, mem_off, mem_off₂]
  rw [hmem, hnot, card_off] at hsplit
  omega

/-- **`8` of the `10` edges through `w` miss two further vertices.** -/
theorem card_star_off₂ {w u v : Fin 11} (hwu : w ≠ u) (hwv : w ≠ v) (huv : u ≠ v) :
    ((star w).filter fun e => u ∉ e.vertices ∧ v ∉ e.vertices).card = 8 := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := star w) (p := fun e => u ∈ e.vertices ∨ v ∈ e.vertices)
  have hor : ((star w).filter fun e => u ∈ e.vertices ∨ v ∈ e.vertices) =
      ({mk' hwu} : Finset Edge11) ∪ {mk' hwv} := by
    rw [Finset.filter_or, star_filter_mem hwu, star_filter_mem hwv]
  have hne : (mk' hwu : Edge11) ≠ mk' hwv := by
    intro hcon
    have hu : u ∈ (mk' hwv : Edge11).vertices := by
      rw [← hcon, vertices_mk']
      simp
    rw [vertices_mk'] at hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with h | h
    · exact hwu h.symm
    · exact huv h
  have hcard : (({mk' hwu} : Finset Edge11) ∪ {mk' hwv}).card = 2 := by
    rw [← Finset.insert_eq, Finset.card_insert_of_notMem (by simpa using hne),
      Finset.card_singleton]
  have hnot : ((star w).filter fun e => ¬ (u ∈ e.vertices ∨ v ∈ e.vertices)) =
      ((star w).filter fun e => u ∉ e.vertices ∧ v ∉ e.vertices) := by
    ext e
    simp only [Finset.mem_filter, not_or]
  rw [hor, hcard, hnot, card_star] at hsplit
  omega

/-- Two distinct vertices lie on exactly one common edge. -/
theorem card_star_inter_star {u v : Fin 11} (huv : u ≠ v) :
    ((star u) ∩ (star v)).card = 1 := by
  have h : (star u) ∩ (star v) = {mk' huv} := by
    ext e
    simp only [Finset.mem_inter, mem_star, Finset.mem_singleton]
    constructor
    · rintro ⟨hu, hv⟩
      exact eq_of_mem_mem huv hu hv
    · rintro rfl
      rw [vertices_mk']
      simp
  rw [h, Finset.card_singleton]

end Edge11

/-! ### The cover-side star count

The `9` members of a cherry cover through a fixed edge `e` are `2`-regular, so
they carry `18` incidences with the star of *any* vertex.  This one identity is
what turns the residual pair multiplicities into constants. -/

namespace CherryCover

variable (C : CherryCover)

/-- The pair counts of a fixed edge against the star of a vertex sum to
`18 = 9 · 2`, for every edge and every vertex. -/
theorem sum_star_pairCount (e : Edge11) (v : Fin 11) :
    (∑ f ∈ Edge11.star v, pairCount C.g e f) = 18 := by
  rw [← sum_star_inter_card C.g e (Edge11.star v)]
  have hcell : ∀ i ∈ starFinset C.g e, (Edge11.star v ∩ C.g i).card = 2 := by
    intro i _
    rw [← C.two_regular i v]
    refine congrArg Finset.card ?_
    ext f
    simp only [Finset.mem_inter, Finset.mem_filter, Edge11.mem_star]
    exact and_comm
  have hstar : (starFinset C.g e).card = 9 := by
    rw [← pairCount_self, C.edge_rep e]
  rw [Finset.sum_congr rfl hcell, Finset.sum_const, hstar]
  simp

/-- The pair multiplicities of a `Derived45` coming from a cherry cover are the
pair counts of the cover. -/
theorem toDerived45_pairMult (e f : Edge11) :
    C.toDerived45.pairMult e f = pairCount C.g e f := rfl

end CherryCover

/-! ### The isolated vertices of a residual block -/

namespace Residual165

variable {C : CherryCover} (R : Residual165 C.toDerived45)

/-- **Bridge to `ArcDegree`.**  Every residual block over a cherry cover is a
`{12; 3}`-arc of the cover, hence a cubic graph on `8` of the `11` vertices. -/
theorem isArc (n : Fin 165) : IsArc C (R.res n) where
  card := R.res_card n
  meet := fun i => by
    have h := R.cross_meet i n
    rwa [Finset.inter_comm] at h

/-- The degree of a residual block at a vertex of `K₁₁`. -/
def deg (n : Fin 165) (v : Fin 11) : ℕ := arcDegree (R.res n) v

/-- The degree of a residual block at a vertex counts the edges it shares with
the star of that vertex. -/
theorem deg_eq_inter_card (n : Fin 165) (v : Fin 11) :
    R.deg n v = (Edge11.star v ∩ R.res n).card := by
  show ((R.res n).filter fun e => v ∈ e.vertices).card = _
  refine congrArg Finset.card ?_
  ext e
  simp only [Finset.mem_filter, Finset.mem_inter, Edge11.mem_star]
  exact and_comm

/-- Every residual block has degree `0` or `3` at every vertex. -/
theorem deg_cases (n : Fin 165) (v : Fin 11) : R.deg n v = 0 ∨ R.deg n v = 3 :=
  (R.isArc n).arc_degree_cases v

/-- A vertex of degree `0` lies on no edge of the block. -/
theorem not_mem_of_deg_eq_zero {n : Fin 165} {v : Fin 11} (h : R.deg n v = 0)
    {e : Edge11} (he : e ∈ R.res n) : v ∉ e.vertices := by
  intro hv
  have hmem : e ∈ (R.res n).filter fun f => v ∈ f.vertices := Finset.mem_filter.mpr ⟨he, hv⟩
  have hzero : ((R.res n).filter fun f => v ∈ f.vertices) = ∅ := by
    rw [← Finset.card_eq_zero]
    exact h
  rw [hzero] at hmem
  exact absurd hmem (Finset.notMem_empty e)

/-- The residual blocks in which a given vertex is isolated. -/
def isolating (v : Fin 11) : Finset (Fin 165) :=
  Finset.univ.filter fun n => R.deg n v = 0

@[simp] theorem mem_isolating {v : Fin 11} {n : Fin 165} :
    n ∈ R.isolating v ↔ R.deg n v = 0 := by
  simp [isolating]

/-- A block isolating `v` avoids the star of `v`. -/
theorem res_subset_off {v : Fin 11} {n : Fin 165} (hn : n ∈ R.isolating v) :
    R.res n ⊆ Edge11.off v := fun _ he =>
  Edge11.mem_off.mpr (R.not_mem_of_deg_eq_zero (R.mem_isolating.mp hn) he)

/-- A block isolating `u` and `v` avoids both stars. -/
theorem res_subset_off₂ {u v : Fin 11} {n : Fin 165} (hu : n ∈ R.isolating u)
    (hv : n ∈ R.isolating v) : R.res n ⊆ Edge11.off₂ u v := fun _ he =>
  Edge11.mem_off₂.mpr ⟨R.not_mem_of_deg_eq_zero (R.mem_isolating.mp hu) he,
    R.not_mem_of_deg_eq_zero (R.mem_isolating.mp hv) he⟩

/-! ### Every vertex is isolated in `45` blocks -/

/-- The degrees of the `165` residual blocks at a fixed vertex sum to
`360 = 10 · 36`. -/
theorem sum_deg_vertex (v : Fin 11) : (∑ n : Fin 165, R.deg n v) = 360 := by
  have hstep : (∑ n : Fin 165, R.deg n v) =
      ∑ n : Fin 165, (Edge11.star v ∩ R.res n).card :=
    Finset.sum_congr rfl fun n _ => R.deg_eq_inter_card n v
  rw [hstep, sum_inter_card_over Finset.univ R.res (Edge11.star v),
    Finset.sum_congr rfl fun e _ => R.res_rep e, Finset.sum_const, Edge11.card_star]
  simp

/-- Every vertex of `K₁₁` is isolated in exactly `45` of the `165`
residual blocks. -/
theorem card_isolating (v : Fin 11) : (R.isolating v).card = 45 := by
  have h := sum_add_mul_card_filter_eq 3 (Finset.univ : Finset (Fin 165))
    (fun n => R.deg n v) fun n _ => R.deg_cases n v
  rw [R.sum_deg_vertex v] at h
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have hset : R.isolating v = Finset.univ.filter fun n => R.deg n v = 0 := rfl
  rw [hset]
  omega

/-! ### Blocks through an edge and isolating a vertex -/

/-- The residual pair multiplicities of an edge `e` against the star of a vertex
off `e` sum to `72 = 2 · 8 + 8 · 7`. -/
theorem sum_star_pairMult {e : Edge11} {v : Fin 11} (hv : v ∉ e.vertices) :
    (∑ f ∈ Edge11.star v, R.pairMult e f) = 72 := by
  have hcell : ∀ f ∈ Edge11.star v, R.pairMult e f + pairCount C.g e f = 9 := by
    intro f hf
    have hef : e ≠ f := by
      rintro rfl
      exact hv (Edge11.mem_star.mp hf)
    have h := residual_pairMult_add R hef
    rw [C.toDerived45_pairMult] at h
    omega
  have hsum := Finset.sum_congr rfl hcell
  rw [Finset.sum_add_distrib, C.sum_star_pairCount e v, Finset.sum_const,
    Edge11.card_star, smul_eq_mul] at hsum
  omega

/-- The degrees at `v` of the `36` blocks through an edge `e` off `v` sum to
`72`. -/
theorem sum_deg_through_edge {e : Edge11} {v : Fin 11} (hv : v ∉ e.vertices) :
    (∑ n ∈ starFinset R.res e, R.deg n v) = 72 := by
  have hstep : (∑ n ∈ starFinset R.res e, R.deg n v) =
      ∑ n ∈ starFinset R.res e, (Edge11.star v ∩ R.res n).card :=
    Finset.sum_congr rfl fun n _ => R.deg_eq_inter_card n v
  have hfilter : ∀ f : Edge11,
      ((starFinset R.res e).filter fun n => f ∈ R.res n).card = R.pairMult e f := by
    intro f
    have hset : ((starFinset R.res e).filter fun n => f ∈ R.res n) =
        Finset.univ.filter fun n => e ∈ R.res n ∧ f ∈ R.res n := by
      ext n
      simp only [Finset.mem_filter, starFinset, Finset.mem_univ, true_and]
    rw [hset]
    rfl
  rw [hstep, sum_inter_card_over (starFinset R.res e) R.res (Edge11.star v),
    Finset.sum_congr rfl fun f _ => hfilter f]
  exact R.sum_star_pairMult hv

/-- For an edge `e` and a vertex `v` off `e`, exactly `12` residual
blocks contain `e` and isolate `v`. -/
theorem card_isolating_through {e : Edge11} {v : Fin 11} (hv : v ∉ e.vertices) :
    ((R.isolating v).filter fun n => e ∈ R.res n).card = 12 := by
  have h := sum_add_mul_card_filter_eq 3 (starFinset R.res e) (fun n => R.deg n v)
    fun n _ => R.deg_cases n v
  have hcard : (starFinset R.res e).card = 36 := R.res_rep e
  rw [R.sum_deg_through_edge hv, hcard] at h
  have hset : ((starFinset R.res e).filter fun n => R.deg n v = 0) =
      ((R.isolating v).filter fun n => e ∈ R.res n) := by
    ext n
    simp only [Finset.mem_filter, starFinset, Finset.mem_univ, true_and, mem_isolating]
    exact and_comm
  rw [hset] at h
  omega

/-! ### Blocks isolating a common vertex meet in three edges -/

/-- Every block isolating `v` meets the blocks isolating `v` in `144 = 12 · 12`
edges in total. -/
theorem sum_meet_isolating {v : Fin 11} {m : Fin 165} (hm : m ∈ R.isolating v) :
    (∑ n ∈ R.isolating v, ((R.res m) ∩ (R.res n)).card) = 144 := by
  have hstep : (∑ n ∈ R.isolating v, ((R.res m) ∩ (R.res n)).card) =
      ∑ e ∈ R.res m, ((R.isolating v).filter fun n => e ∈ R.res n).card :=
    sum_inter_card_over (R.isolating v) R.res (R.res m)
  have hcell : ∀ e ∈ R.res m,
      ((R.isolating v).filter fun n => e ∈ R.res n).card = 12 := fun e he =>
    R.card_isolating_through (Edge11.mem_off.mp (R.res_subset_off hm he))
  rw [hstep, Finset.sum_congr rfl hcell, Finset.sum_const, R.res_card m]
  simp

/-- Two distinct residual blocks isolating a common vertex meet in
exactly `3` edges. -/
theorem meet_of_isolating {v : Fin 11} {m n : Fin 165} (hm : m ∈ R.isolating v)
    (hn : n ∈ R.isolating v) (hmn : m ≠ n) : ((R.res m) ∩ (R.res n)).card = 3 := by
  have hsum := R.sum_meet_isolating hm
  have hdiag : ((R.res m) ∩ (R.res m)).card = 12 := by
    rw [Finset.inter_self, R.res_card m]
  have hsplit := Finset.sum_erase_add (R.isolating v)
    (fun k => ((R.res m) ∩ (R.res k)).card) hm
  have hcard : ((R.isolating v).erase m).card = 44 := by
    rw [Finset.card_erase_of_mem hm, R.card_isolating v]
  have hle : ∀ k ∈ (R.isolating v).erase m, ((R.res m) ∩ (R.res k)).card ≤ 3 := by
    intro k hk
    rcases R.res_meet m k (Ne.symm (Finset.mem_erase.mp hk).1) with h | h <;> omega
  have heq : (∑ k ∈ (R.isolating v).erase m, ((R.res m) ∩ (R.res k)).card) =
      ∑ _k ∈ (R.isolating v).erase m, 3 := by
    rw [Finset.sum_const, hcard, smul_eq_mul]
    omega
  exact (Finset.sum_eq_sum_iff_of_le hle).mp heq n
    (Finset.mem_erase.mpr ⟨Ne.symm hmn, hn⟩)

/-! ### The local symmetric `2-(45, 12, 3)` design -/

/-- Two distinct edges off `v` lie on exactly `3` residual blocks
isolating `v`.

Together with `SRG266.QuasiSymmetric.Residual165.card_isolating`,
`card_isolating_through` and `meet_of_isolating` this says that the `45` blocks
isolating `v` form a **symmetric `2-(45, 12, 3)` design** on the `45` edges of
`K₁₁ − v`. -/
theorem localDesign_pairMult {v : Fin 11} {e f : Edge11} (he : v ∉ e.vertices)
    (hf : v ∉ f.vertices) (hef : e ≠ f) :
    ((R.isolating v).filter fun n => e ∈ R.res n ∧ f ∈ R.res n).card = 3 := by
  classical
  set Ie : Finset (Fin 165) := (R.isolating v).filter fun n => e ∈ R.res n with hIe
  have hIesub : Ie ⊆ R.isolating v := Finset.filter_subset _ _
  have hIecard : Ie.card = 12 := R.card_isolating_through he
  have hsub : ∀ n ∈ Ie, R.res n ⊆ Edge11.off v := fun n hn =>
    R.res_subset_off (hIesub hn)
  set lam : Edge11 → ℕ := fun g => (Ie.filter fun n => g ∈ R.res n).card with hlam
  -- the replication numbers of `Ie` inside the `45` edges off `v`
  have hsum : (∑ g ∈ Edge11.off v, lam g) = 144 := by
    have hstep : (∑ n ∈ Ie, (Edge11.off v ∩ R.res n).card) =
        ∑ g ∈ Edge11.off v, lam g := sum_inter_card_over Ie R.res (Edge11.off v)
    have hcell : ∀ n ∈ Ie, (Edge11.off v ∩ R.res n).card = 12 := by
      intro n hn
      rw [Finset.inter_eq_right.mpr (hsub n hn), R.res_card n]
    rw [← hstep, Finset.sum_congr rfl hcell, Finset.sum_const, hIecard]
    simp
  have hsq : (∑ g ∈ Edge11.off v, lam g ^ 2) = 540 := by
    have hstep : (∑ g ∈ Edge11.off v, lam g ^ 2) =
        ∑ m ∈ Ie, ∑ n ∈ Ie, ((R.res m) ∩ (R.res n)).card :=
      sum_card_filter_sq Ie R.res (Edge11.off v) hsub
    have hcell : ∀ m ∈ Ie, (∑ n ∈ Ie, ((R.res m) ∩ (R.res n)).card) = 45 := by
      intro m hm
      have hdiag : ((R.res m) ∩ (R.res m)).card = 12 := by
        rw [Finset.inter_self, R.res_card m]
      have hsplit := Finset.sum_erase_add Ie
        (fun k => ((R.res m) ∩ (R.res k)).card) hm
      have hoff : (∑ k ∈ Ie.erase m, ((R.res m) ∩ (R.res k)).card) = 33 := by
        have hval : ∀ k ∈ Ie.erase m, ((R.res m) ∩ (R.res k)).card = 3 := by
          intro k hk
          exact R.meet_of_isolating (hIesub hm) (hIesub (Finset.mem_of_mem_erase hk))
            (Ne.symm (Finset.mem_erase.mp hk).1)
        rw [Finset.sum_congr rfl hval, Finset.sum_const,
          Finset.card_erase_of_mem hm, hIecard]
        simp
      omega
    rw [hstep, Finset.sum_congr rfl hcell, Finset.sum_const, hIecard]
    simp
  -- split off the diagonal edge `e`
  have hemem : e ∈ Edge11.off v := Edge11.mem_off.mpr he
  have hfmem : f ∈ Edge11.off v := Edge11.mem_off.mpr hf
  have hlame : lam e = 12 := by
    have hself : (Ie.filter fun n => e ∈ R.res n) = Ie := by
      refine Finset.filter_true_of_mem fun n hn => ?_
      rw [hIe] at hn
      exact (Finset.mem_filter.mp hn).2
    show (Ie.filter fun n => e ∈ R.res n).card = 12
    rw [hself, hIecard]
  have hcarderase : ((Edge11.off v).erase e).card = 44 := by
    rw [Finset.card_erase_of_mem hemem, Edge11.card_off]
  have hsumerase : (∑ g ∈ (Edge11.off v).erase e, lam g) = 132 := by
    have h := Finset.sum_erase_add (Edge11.off v) lam hemem
    omega
  have hsqerase : (∑ g ∈ (Edge11.off v).erase e, lam g ^ 2) = 396 := by
    have h := Finset.sum_erase_add (Edge11.off v) (fun g => lam g ^ 2) hemem
    rw [hlame] at h
    omega
  -- zero variance about the mean `3`
  have hle : ∀ g ∈ (Edge11.off v).erase e, 6 * lam g ≤ lam g ^ 2 + 9 :=
    fun g _ => six_mul_le_sq_add_nine _
  have heq : (∑ g ∈ (Edge11.off v).erase e, 6 * lam g) =
      ∑ g ∈ (Edge11.off v).erase e, (lam g ^ 2 + 9) := by
    rw [← Finset.mul_sum, hsumerase, Finset.sum_add_distrib, hsqerase, Finset.sum_const,
      hcarderase]
    simp
  have hpt := (Finset.sum_eq_sum_iff_of_le hle).mp heq f
    (Finset.mem_erase.mpr ⟨Ne.symm hef, hfmem⟩)
  have hval : lam f = 3 := eq_three_of_six_mul_eq hpt
  have hset : (Ie.filter fun n => f ∈ R.res n) =
      ((R.isolating v).filter fun n => e ∈ R.res n ∧ f ∈ R.res n) := by
    rw [hIe, Finset.filter_filter]
  rw [← hset]
  exact hval

/-! ### Nine blocks isolate two given vertices -/

/-- The products of the degrees at two distinct vertices sum to
`756 = 36 + 27 · 8 + 72 · 7`. -/
theorem sum_deg_mul {u v : Fin 11} (huv : u ≠ v) :
    (∑ n : Fin 165, R.deg n u * R.deg n v) = 756 := by
  have hstep : (∑ n : Fin 165, R.deg n u * R.deg n v) =
      ∑ n : Fin 165, (Edge11.star u ∩ R.res n).card * (Edge11.star v ∩ R.res n).card :=
    Finset.sum_congr rfl fun n _ => by
      rw [R.deg_eq_inter_card n u, R.deg_eq_inter_card n v]
  have hpair : (∑ n : Fin 165,
      (Edge11.star u ∩ R.res n).card * (Edge11.star v ∩ R.res n).card) =
      ∑ e ∈ Edge11.star u, ∑ f ∈ Edge11.star v, R.pairMult e f :=
    sum_mul_inter_card_over Finset.univ R.res (Edge11.star u) (Edge11.star v)
  -- the total of `R.pairMult + pairCount` over the two stars
  have hcell : ∀ e f : Edge11,
      R.pairMult e f + pairCount C.g e f = 9 + (if e = f then 36 else 0) := by
    intro e f
    by_cases hef : e = f
    · subst hef
      rw [R.pairMult_self e, C.edge_rep e, if_pos rfl]
    · have h := residual_pairMult_add R hef
      rw [C.toDerived45_pairMult] at h
      rw [if_neg hef]
      omega
  have htotal : (∑ e ∈ Edge11.star u, ∑ f ∈ Edge11.star v,
      (R.pairMult e f + pairCount C.g e f)) = 936 := by
    have hinner : ∀ e ∈ Edge11.star u,
        (∑ f ∈ Edge11.star v, (R.pairMult e f + pairCount C.g e f)) =
          90 + (if e ∈ Edge11.star v then 36 else 0) := by
      intro e _
      rw [Finset.sum_congr rfl fun f _ => hcell e f, Finset.sum_add_distrib,
        Finset.sum_const, Edge11.card_star,
        Finset.sum_ite_eq (Edge11.star v) e fun _ => 36]
      simp
    rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, Finset.sum_const,
      Edge11.card_star, Finset.sum_ite_mem, Finset.sum_const,
      Edge11.card_star_inter_star huv]
    simp
  have hcover : (∑ e ∈ Edge11.star u, ∑ f ∈ Edge11.star v, pairCount C.g e f) = 180 := by
    rw [Finset.sum_congr rfl fun e _ => C.sum_star_pairCount e v, Finset.sum_const,
      Edge11.card_star]
    simp
  have hdistrib : (∑ e ∈ Edge11.star u, ∑ f ∈ Edge11.star v,
      (R.pairMult e f + pairCount C.g e f)) =
      (∑ e ∈ Edge11.star u, ∑ f ∈ Edge11.star v, R.pairMult e f) +
        ∑ e ∈ Edge11.star u, ∑ f ∈ Edge11.star v, pairCount C.g e f := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_add_distrib
  rw [hstep, hpair]
  omega

/-- Exactly `9` residual blocks isolate two given distinct vertices. -/
theorem card_isolating_pair {u v : Fin 11} (huv : u ≠ v) :
    ((R.isolating u) ∩ (R.isolating v)).card = 9 := by
  have hcases : ∀ n ∈ (Finset.univ : Finset (Fin 165)),
      R.deg n u * R.deg n v = 0 ∨ R.deg n u * R.deg n v = 9 := by
    intro n _
    rcases R.deg_cases n u with hu | hu <;> rcases R.deg_cases n v with hv | hv <;>
      simp [hu, hv]
  have h := sum_add_mul_card_filter_eq 9 (Finset.univ : Finset (Fin 165))
    (fun n => R.deg n u * R.deg n v) hcases
  rw [R.sum_deg_mul huv] at h
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have hset : (Finset.univ.filter fun n => R.deg n u * R.deg n v = 0) =
      (R.isolating u) ∪ (R.isolating v) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      mem_isolating, Nat.mul_eq_zero]
  rw [hset] at h
  have hunion := Finset.card_union_add_card_inter (R.isolating u) (R.isolating v)
  rw [R.card_isolating u, R.card_isolating v] at hunion
  omega

/-! ### Exactly one block isolates three given vertices -/

/-- Every edge off `u` and `v` lies on exactly `3` of the `9` blocks isolating
both. -/
theorem localCount_two {u v : Fin 11} (huv : u ≠ v) {e : Edge11}
    (he : e ∈ Edge11.off₂ u v) :
    (((R.isolating u) ∩ (R.isolating v)).filter fun n => e ∈ R.res n).card = 3 := by
  classical
  set J : Finset (Fin 165) := (R.isolating u) ∩ (R.isolating v) with hJ
  have hJcard : J.card = 9 := R.card_isolating_pair huv
  have hsub : ∀ n ∈ J, R.res n ⊆ Edge11.off₂ u v := by
    intro n hn
    rw [hJ, Finset.mem_inter] at hn
    exact R.res_subset_off₂ hn.1 hn.2
  set c : Edge11 → ℕ := fun g => (J.filter fun n => g ∈ R.res n).card with hc
  have hsum : (∑ g ∈ Edge11.off₂ u v, c g) = 108 := by
    have hstep : (∑ n ∈ J, (Edge11.off₂ u v ∩ R.res n).card) =
        ∑ g ∈ Edge11.off₂ u v, c g := sum_inter_card_over J R.res (Edge11.off₂ u v)
    have hcell : ∀ n ∈ J, (Edge11.off₂ u v ∩ R.res n).card = 12 := by
      intro n hn
      rw [Finset.inter_eq_right.mpr (hsub n hn), R.res_card n]
    rw [← hstep, Finset.sum_congr rfl hcell, Finset.sum_const, hJcard]
    simp
  have hsq : (∑ g ∈ Edge11.off₂ u v, c g ^ 2) = 324 := by
    have hstep : (∑ g ∈ Edge11.off₂ u v, c g ^ 2) =
        ∑ m ∈ J, ∑ n ∈ J, ((R.res m) ∩ (R.res n)).card :=
      sum_card_filter_sq J R.res (Edge11.off₂ u v) hsub
    have hcell : ∀ m ∈ J, (∑ n ∈ J, ((R.res m) ∩ (R.res n)).card) = 36 := by
      intro m hm
      have hmu : m ∈ R.isolating u := (Finset.mem_inter.mp (hJ ▸ hm)).1
      have hdiag : ((R.res m) ∩ (R.res m)).card = 12 := by
        rw [Finset.inter_self, R.res_card m]
      have hsplit := Finset.sum_erase_add J
        (fun k => ((R.res m) ∩ (R.res k)).card) hm
      have hoff : (∑ k ∈ J.erase m, ((R.res m) ∩ (R.res k)).card) = 24 := by
        have hval : ∀ k ∈ J.erase m, ((R.res m) ∩ (R.res k)).card = 3 := by
          intro k hk
          have hku : k ∈ R.isolating u :=
            (Finset.mem_inter.mp (hJ ▸ Finset.mem_of_mem_erase hk)).1
          exact R.meet_of_isolating hmu hku (Ne.symm (Finset.mem_erase.mp hk).1)
        rw [Finset.sum_congr rfl hval, Finset.sum_const,
          Finset.card_erase_of_mem hm, hJcard]
        simp
      omega
    rw [hstep, Finset.sum_congr rfl hcell, Finset.sum_const, hJcard]
    simp
  have hcard : (Edge11.off₂ u v).card = 36 := Edge11.card_off₂ huv
  have hle : ∀ g ∈ Edge11.off₂ u v, 6 * c g ≤ c g ^ 2 + 9 :=
    fun g _ => six_mul_le_sq_add_nine _
  have heq : (∑ g ∈ Edge11.off₂ u v, 6 * c g) =
      ∑ g ∈ Edge11.off₂ u v, (c g ^ 2 + 9) := by
    rw [← Finset.mul_sum, hsum, Finset.sum_add_distrib, hsq, Finset.sum_const, hcard]
    simp
  exact eq_three_of_six_mul_eq ((Finset.sum_eq_sum_iff_of_le hle).mp heq e he)

/-- The degrees at a third vertex of the `9` blocks isolating `u` and `v` sum to
`24 = 8 · 3`. -/
theorem sum_deg_isolating_pair {u v w : Fin 11} (huv : u ≠ v) (hwu : w ≠ u)
    (hwv : w ≠ v) :
    (∑ n ∈ (R.isolating u) ∩ (R.isolating v), R.deg n w) = 24 := by
  classical
  set J : Finset (Fin 165) := (R.isolating u) ∩ (R.isolating v) with hJ
  have hsub : ∀ n ∈ J, R.res n ⊆ Edge11.off₂ u v := by
    intro n hn
    rw [hJ, Finset.mem_inter] at hn
    exact R.res_subset_off₂ hn.1 hn.2
  have hstep : (∑ n ∈ J, R.deg n w) =
      ∑ e ∈ Edge11.star w, (J.filter fun n => e ∈ R.res n).card := by
    rw [Finset.sum_congr rfl fun n _ => R.deg_eq_inter_card n w]
    exact sum_inter_card_over J R.res (Edge11.star w)
  have hsplit := Finset.sum_filter_add_sum_filter_not (Edge11.star w)
    (fun e => u ∉ e.vertices ∧ v ∉ e.vertices)
    fun e => (J.filter fun n => e ∈ R.res n).card
  have hyes : (∑ e ∈ (Edge11.star w).filter
      fun e => u ∉ e.vertices ∧ v ∉ e.vertices,
        (J.filter fun n => e ∈ R.res n).card) = 24 := by
    have hval : ∀ e ∈ (Edge11.star w).filter
        fun e => u ∉ e.vertices ∧ v ∉ e.vertices,
          (J.filter fun n => e ∈ R.res n).card = 3 := by
      intro e he
      exact R.localCount_two huv (Edge11.mem_off₂.mpr (Finset.mem_filter.mp he).2)
    rw [Finset.sum_congr rfl hval, Finset.sum_const,
      Edge11.card_star_off₂ hwu hwv huv]
    simp
  have hno : (∑ e ∈ (Edge11.star w).filter
      fun e => ¬ (u ∉ e.vertices ∧ v ∉ e.vertices),
        (J.filter fun n => e ∈ R.res n).card) = 0 := by
    refine Finset.sum_eq_zero fun e he => ?_
    have hbad := (Finset.mem_filter.mp he).2
    rw [Finset.card_eq_zero]
    refine Finset.filter_eq_empty_iff.mpr ?_
    intro n hn hmem
    exact hbad (Edge11.mem_off₂.mp (hsub n hn hmem))
  rw [hstep, ← hsplit, hyes, hno]

/-- Exactly one residual block isolates three given
distinct vertices. -/
theorem card_isolating_triple {u v w : Fin 11} (huv : u ≠ v) (hwu : w ≠ u)
    (hwv : w ≠ v) :
    (((R.isolating u) ∩ (R.isolating v)) ∩ (R.isolating w)).card = 1 := by
  have h := sum_add_mul_card_filter_eq 3 ((R.isolating u) ∩ (R.isolating v))
    (fun n => R.deg n w) fun n _ => R.deg_cases n w
  rw [R.sum_deg_isolating_pair huv hwu hwv, R.card_isolating_pair huv] at h
  have hset : (((R.isolating u) ∩ (R.isolating v)).filter fun n => R.deg n w = 0) =
      ((R.isolating u) ∩ (R.isolating v)) ∩ (R.isolating w) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_inter, mem_isolating]
  rw [hset] at h
  omega

/-! ### The triple bijection -/

/-- The three vertices isolated by a residual block. -/
def isolatedTriple (n : Fin 165) : Finset (Fin 11) :=
  Finset.univ.filter fun v => R.deg n v = 0

@[simp] theorem mem_isolatedTriple {n : Fin 165} {v : Fin 11} :
    v ∈ R.isolatedTriple n ↔ R.deg n v = 0 := by
  simp [isolatedTriple]

/-- Every residual block isolates exactly `3` of the
`11` vertices. -/
theorem card_isolatedTriple (n : Fin 165) : (R.isolatedTriple n).card = 3 := by
  have hcubic := (R.isArc n).arc_is_cubic_on_eight
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 11))) (p := fun v => arcDegree (R.res n) v ≠ 0)
  have hset : ((Finset.univ : Finset (Fin 11)).filter
      fun v => ¬ arcDegree (R.res n) v ≠ 0) = R.isolatedTriple n := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not, mem_isolatedTriple]
    rfl
  rw [hcubic.1, hset, Finset.card_univ, Fintype.card_fin] at hsplit
  omega

/-- A block isolates `v` exactly when `v` belongs to its isolated triple. -/
theorem mem_isolating_iff {n : Fin 165} {v : Fin 11} :
    n ∈ R.isolating v ↔ v ∈ R.isolatedTriple n := by
  rw [mem_isolating, mem_isolatedTriple]

/-- Distinct residual blocks isolate distinct triples. -/
theorem isolatedTriple_injective : Function.Injective R.isolatedTriple := by
  intro m n hmn
  obtain ⟨a, b, c, hab, hac, hbc, hs⟩ := Finset.card_eq_three.mp (R.card_isolatedTriple m)
  have hmem : ∀ k : Fin 165, R.isolatedTriple k = {a, b, c} →
      k ∈ ((R.isolating a) ∩ (R.isolating b)) ∩ (R.isolating c) := by
    intro k hk
    have ha : a ∈ R.isolatedTriple k := by rw [hk]; simp
    have hb : b ∈ R.isolatedTriple k := by rw [hk]; simp
    have hc : c ∈ R.isolatedTriple k := by rw [hk]; simp
    exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr
      ⟨R.mem_isolating_iff.mpr ha, R.mem_isolating_iff.mpr hb⟩,
      R.mem_isolating_iff.mpr hc⟩
  have hcard := R.card_isolating_triple hab (Ne.symm hac) (Ne.symm hbc)
  exact Finset.card_le_one.mp (le_of_eq hcard) m (hmem m hs) n (hmem n (hmn ▸ hs))

/-- Every triple of vertices is the isolated triple of a
residual block. -/
theorem isolatedTriple_surjective (s : Finset (Fin 11)) (hs : s.card = 3) :
    ∃ n : Fin 165, R.isolatedTriple n = s := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs
  obtain ⟨n, hn⟩ := Finset.card_eq_one.mp
    (R.card_isolating_triple hab (Ne.symm hac) (Ne.symm hbc))
  have hmem : n ∈ ((R.isolating a) ∩ (R.isolating b)) ∩ (R.isolating c) := by
    rw [hn]
    exact Finset.mem_singleton_self n
  have hsub : ({a, b, c} : Finset (Fin 11)) ⊆ R.isolatedTriple n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have h1 := (Finset.mem_inter.mp (Finset.mem_inter.mp hmem).1).1
    have h2 := (Finset.mem_inter.mp (Finset.mem_inter.mp hmem).1).2
    have h3 := (Finset.mem_inter.mp hmem).2
    rcases hx with rfl | rfl | rfl
    · exact R.mem_isolating_iff.mp h1
    · exact R.mem_isolating_iff.mp h2
    · exact R.mem_isolating_iff.mp h3
  refine ⟨n, (Finset.eq_of_subset_of_card_le hsub ?_).symm⟩
  rw [R.card_isolatedTriple n, hs]

/-- Sending a residual block to the three
vertices it isolates is a bijection from the `165` blocks onto the
`165 = C(11, 3)` triples of vertices of `K₁₁`. -/
theorem isolatedTriple_bijOn :
    Set.BijOn R.isolatedTriple Set.univ {s : Finset (Fin 11) | s.card = 3} := by
  refine ⟨fun n _ => R.card_isolatedTriple n, R.isolatedTriple_injective.injOn, ?_⟩
  intro s hs
  obtain ⟨n, hn⟩ := R.isolatedTriple_surjective s hs
  exact ⟨n, Set.mem_univ n, hn⟩

/-- The unique residual block isolating a given triple of vertices. -/
noncomputable def blockOf {s : Finset (Fin 11)} (hs : s.card = 3) : Fin 165 :=
  Classical.choose (R.isolatedTriple_surjective s hs)

/-- `Residual165.blockOf` does isolate the triple it is named by. -/
theorem isolatedTriple_blockOf {s : Finset (Fin 11)} (hs : s.card = 3) :
    R.isolatedTriple (R.blockOf hs) = s :=
  Classical.choose_spec (R.isolatedTriple_surjective s hs)

/-! ### The local design, bundled -/

/-- **The local symmetric `2-(45, 12, 3)` design at a vertex.**

For every vertex `v` of `K₁₁` the `45` residual blocks isolating `v`

* live on the `45` edges of `K₁₁ − v` and carry `12` edges each;
* isolate exactly three vertices, one of which is `v` — so each is a cubic graph
  on `8` of the `10` remaining vertices, indexed by the pair it omits;
* meet pairwise in exactly `3` edges;
* cover every edge of `K₁₁ − v` exactly `12` times and every pair of such edges
  exactly `3` times.

This bundles the whole rigidity chain into the object that a cover-free
refutation of `SRG266.QuasiSymmetric.NoResidualCherryCover` has to contradict:
it mentions neither the cherry cover `C` nor the `120` blocks in which `v` is
not isolated. -/
theorem localDesign (v : Fin 11) :
    (R.isolating v).card = 45 ∧
      (∀ n ∈ R.isolating v, R.res n ⊆ Edge11.off v ∧ (R.res n).card = 12 ∧
        (R.isolatedTriple n).card = 3 ∧ v ∈ R.isolatedTriple n) ∧
      (∀ m ∈ R.isolating v, ∀ n ∈ R.isolating v, m ≠ n →
        ((R.res m) ∩ (R.res n)).card = 3) ∧
      (∀ e ∈ Edge11.off v, ((R.isolating v).filter fun n => e ∈ R.res n).card = 12) ∧
      ∀ e ∈ Edge11.off v, ∀ f ∈ Edge11.off v, e ≠ f →
        ((R.isolating v).filter fun n => e ∈ R.res n ∧ f ∈ R.res n).card = 3 :=
  ⟨R.card_isolating v,
    fun n hn => ⟨R.res_subset_off hn, R.res_card n, R.card_isolatedTriple n,
      R.mem_isolating_iff.mp hn⟩,
    fun _ hm _ hn hmn => R.meet_of_isolating hm hn hmn,
    fun _ he => R.card_isolating_through (Edge11.mem_off.mp he),
    fun _ he _ hf hef => R.localDesign_pairMult (Edge11.mem_off.mp he)
      (Edge11.mem_off.mp hf) hef⟩

end Residual165

end SRG266.QuasiSymmetric
