/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.GlobalDesign

/-!
# The disjointness graph of the global residual design

`SRG266/QuasiSymmetric/GlobalDesign.lean` states the cover-free finite object
that a residual structure over a cherry cover of `K₁₁` produces: a family of
`165` twelve-edge blocks `B T`, indexed by the triples `T` of vertices they
isolate, in which two blocks meet in `3` edges as soon as their triples share a
vertex, and in `0` or `3` otherwise.

That last disjunction is the only remaining freedom, and this file shows it is
not free at all.  Writing `Z T` for the set of triples `U` with
`B T ∩ B U = ∅` — the *disjointness graph* of the object — the six theorems
below are all proved by the `Finset` double counting of
`SRG266/QuasiSymmetric/ResidualRigidity.lean`, with no eigenvalue, no rank and
no matrix polynomial anywhere:

* `GlobalDesign.card_disjointFrom` — `#(Z T) = 24`: every block is
  disjoint from exactly `24` of the other `164`;
* `GlobalDesign.card_disjointFrom_inter_triplesThrough` — for two
  vertices `v ≠ w` off `T`, `#(Z T ∩ {U : v, w ∈ U}) + [vw ∈ B T] = 3`;
* `GlobalDesign.card_disjointFrom_inter_triplesAt` — for one vertex
  `v`, `#(Z T ∩ {U : v ∈ U}) = 9 − 9 · [v ∈ T]`;
* `GlobalDesign.card_disjointFrom_inter` —
  `#(Z T ∩ Z U) = #(T ∩ U) + 3`, or `0` when `B T ∩ B U = ∅`;
* `GlobalDesign.disjointFrom_inter_eq_empty` and
  `GlobalDesign.no_three_pairwise_disjoint` — `Z` is triangle free: no three
  residual blocks are pairwise disjoint;
* `GlobalDesign.card_disjointFrom_filter_mem_block` — for an edge
  `e ∉ B T`, `#{U ∈ Z T : e ∈ B U} = 6 + #(e ∩ T)`.

The first five index the neighbourhood `Z T` by triples; the last indexes it by
edges, and is the only one that reads back from the neighbourhood to the block:
the `24` neighbouring blocks carry `24 · 12 = 288` edges with multiplicity, and
they place `8` on each of the three edges inside `T`, `7` on each of the `24`
edges from `T` to the eight vertices off it, `6` on each of the `16` edges off
`T` that `B T` misses and **none at all** on the twelve edges of `B T`.  So the
union of the blocks disjoint from `B T` is exactly the complement of `B T`
(`GlobalDesign.biUnion_disjointFrom_eq_compl`), and a block is determined by the
set of triples naming a block disjoint from it. Its proof is the degree double
count restricted to the `36` blocks through `e`: `pair_mult` evaluates
`∑_{U ∋ e} #(B T ∩ B U)` as `12 · 7 + ∑_{f ∈ B T} vmeet e f = 90 − 3 #(e ∩ T)`,
where the second summand is the sum of the degrees of `B T` at the two endpoints
of `e`, and every term of the left-hand side lies in `{0, 3}`.  The three cases
`#(e ∩ T) = 2, 1, 0` are the three ways an edge can sit against a triple; the
total `3 · 8 + 24 · 7 + 16 · 6 = 288` is the consistency check, and summing the
law over the ten edges at a vertex reproduces (Z-VERT).

(Z-DEG) is one line of double counting: `∑_U #(B T ∩ B U) = 12 · 36 = 432` and
the `164` off-diagonal terms are `0` or `3`, so `432 = 12 + 3 · (164 − 24)`.
The disjointness relation is therefore a `24`-regular graph on the `165`
triples, sitting inside the `56`-regular Kneser graph of disjoint triples — not
a disjunction to be branched on.

(Z-VERT) is (Z-PAIR) summed over the seven vertices `w` off `T` other than `v`.
Every `U ∈ Z T` through `v` has `U ∩ T = ∅`, so its two vertices besides `v` are
both among those seven and it is counted exactly twice; the correction terms
`[vw ∈ B T]` add up to `deg_{B T}(v) = 3`.  Hence
`2 · #(Z T ∩ {U : v ∈ U}) + 3 = 7 · 3`.  In matrix form it says
`(Z + 9 I) Wᵀ = 9 J` for the vertex/triple incidence `W`, i.e. that the `−9`
eigenspace of `Z` contains the image of `W` — the whole `24`-regular graph is
pinned on every one of the eleven stars at once.

(Z-MU) is the sharpest of the five.  It comes from evaluating
`S = ∑_W #(B T ∩ B W) · #(B U ∩ B W)` twice: over edges, using `pair_mult` and
`∑_x deg_{B T}(x) · deg_{B U}(x) = 9 (5 + #(T ∩ U))`
(`GlobalDesign.sum_arcDegree_mul`), it is `1053 + 9 #(T ∩ U) + 27 #(B T ∩ B U)`;
over blocks, using (Z-DEG) and the fact that all off-diagonal meets lie in
`{0, 3}`, it is `24 #(B T ∩ B U) + 9 · #{W : both meets are 3}`.  Comparing the
two gives the common-neighbour count exactly.

(Z-TRI) is the case `B T ∩ B U = ∅` of (Z-MU): two disjoint blocks have **no**
common disjointness-neighbour at all.

## Ingredients

Five facts about `K₁₁` used below are proved here rather than assumed:

* `sum_vmeet_pair` — the two ways of counting incident pairs of edges drawn
  from two sets, `∑_{e ∈ s} ∑_{f ∈ t} vmeet e f = ∑_x arcDegree s x · arcDegree t x`;
* `sum_card_filter_mem` — the two ways of counting the incidences between a set
  of vertices and a family of sets, which is what turns (Z-PAIR) into (Z-VERT);
* `card_triplesThrough` — the `9` triples through two given vertices;
* `card_triplesAt` — the `45` triples through one given vertex;
* `GlobalDesign.card_triplesThrough_filter` — every edge off `v` and `w` lies on
  exactly `3` of those `9` blocks, the zero-variance count that
  `SRG266.QuasiSymmetric.Residual165.localCount_two` performs for a residual
  structure, redone from the axioms of a `GlobalDesign`.

There is no `decide`, no design datum and no case analysis on a cover anywhere
in the file, and nothing here assumes that a `GlobalDesign` exists or fails to.
-/

open scoped BigOperators

namespace SRG266.QuasiSymmetric

/-! ### Two counts over the edges of `K₁₁` -/

/-- The degree of a set of edges at a vertex is its trace on the star of that
vertex. -/
theorem card_inter_star (s : Finset Edge11) (x : Fin 11) :
    (s ∩ Edge11.star x).card = arcDegree s x := by
  rw [arcDegree, ← Finset.filter_mem_eq_inter]
  exact congrArg Finset.card (Finset.filter_congr fun _ _ => by simp)

/-- **Incident pairs, counted twice.**  The common endpoints of the pairs drawn
from two sets of edges are counted, vertex by vertex, by the product of the two
degrees. -/
theorem sum_vmeet_pair (s t : Finset Edge11) :
    (∑ e ∈ s, ∑ f ∈ t, Edge11.vmeet e f) =
      ∑ x : Fin 11, arcDegree s x * arcDegree t x := by
  have h := sum_mul_inter_card_over (Finset.univ : Finset (Fin 11)) Edge11.star s t
  have hcell : ∀ e f : Edge11,
      ((Finset.univ : Finset (Fin 11)).filter fun x =>
        e ∈ Edge11.star x ∧ f ∈ Edge11.star x).card = Edge11.vmeet e f := by
    intro e f
    rw [Edge11.vmeet]
    refine congrArg Finset.card ?_
    ext x
    simp [Edge11.mem_star]
  have hleft : ∀ x : Fin 11,
      (s ∩ Edge11.star x).card * (t ∩ Edge11.star x).card =
        arcDegree s x * arcDegree t x := by
    intro x
    rw [card_inter_star, card_inter_star]
  rw [Finset.sum_congr rfl fun x _ => hleft x] at h
  rw [h]
  exact Finset.sum_congr rfl fun e _ =>
    Finset.sum_congr rfl fun f _ => (hcell e f).symm

/-- The edges of a set through two given distinct vertices: there is at most
one, namely the edge joining them. -/
theorem card_filter_vertices_pair {v w : Fin 11} (hvw : v ≠ w) (s : Finset Edge11) :
    (s.filter fun e => v ∈ e.vertices ∧ w ∈ e.vertices).card =
      if Edge11.mk' hvw ∈ s then 1 else 0 := by
  have hset : (s.filter fun e => v ∈ e.vertices ∧ w ∈ e.vertices) =
      s.filter fun e => e = Edge11.mk' hvw := by
    refine Finset.filter_congr fun e _ => ?_
    constructor
    · rintro ⟨hv, hw⟩
      exact Edge11.eq_of_mem_mem hvw hv hw
    · rintro rfl
      rw [Edge11.vertices_mk']
      simp
  rw [hset, Finset.filter_eq']
  split_ifs <;> simp

/-- **Incidences between a set of vertices and a family of sets, counted
twice.**  The two orders of summing the pairs `(w, i)` with `w ∈ W` and
`w ∈ f i`. -/
theorem sum_card_filter_mem {α ι : Type*} [DecidableEq α] (W : Finset α)
    (S : Finset ι) (f : ι → Finset α) :
    (∑ w ∈ W, (S.filter fun i => w ∈ f i).card) = ∑ i ∈ S, (f i ∩ W).card := by
  have hl : ∀ w : α, (S.filter fun i => w ∈ f i).card =
      ∑ i ∈ S, if w ∈ f i then 1 else 0 := fun w => Finset.card_filter _ _
  have hr : ∀ i : ι, (f i ∩ W).card = ∑ w ∈ W, if w ∈ f i then 1 else 0 := by
    intro i
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
  rw [Finset.sum_congr rfl fun w _ => hl w, Finset.sum_congr rfl fun i _ => hr i,
    Finset.sum_comm]

/-- A set of vertices avoiding `T` meets the vertices off `T` other than `v` in
everything except `v`. -/
theorem inter_erase_filter_notMem {s T : Finset (Fin 11)} {v : Fin 11}
    (h : ∀ x ∈ s, x ∉ T) :
    s ∩ ((Finset.univ.filter fun w => w ∉ T).erase v) = s.erase v := by
  ext y
  simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨hy, hyv, -⟩
    exact ⟨hyv, hy⟩
  · rintro ⟨hyv, hy⟩
    exact ⟨hy, hyv, h y hy⟩

/-! ### The nine triples through two vertices -/

/-- The triples of vertices containing two given ones. -/
def triplesThrough (v w : Fin 11) : Finset (Finset (Fin 11)) :=
  triples.filter fun U => v ∈ U ∧ w ∈ U

@[simp] theorem mem_triplesThrough {v w : Fin 11} {U : Finset (Fin 11)} :
    U ∈ triplesThrough v w ↔ U ∈ triples ∧ v ∈ U ∧ w ∈ U := Finset.mem_filter

/-- **`9` triples contain two given distinct vertices.** -/
theorem card_triplesThrough {v w : Fin 11} (hvw : v ≠ w) :
    (triplesThrough v w).card = 9 := by
  classical
  have hwuniv : w ∈ (Finset.univ : Finset (Fin 11)).erase v :=
    Finset.mem_erase.mpr ⟨Ne.symm hvw, Finset.mem_univ w⟩
  have hcard : (((Finset.univ : Finset (Fin 11)).erase v).erase w).card = 9 := by
    rw [Finset.card_erase_of_mem hwuniv, Finset.card_erase_of_mem (Finset.mem_univ v),
      Finset.card_univ, Fintype.card_fin]
  rw [← hcard]
  refine (Finset.card_bij (fun x _ => ({v, w, x} : Finset (Fin 11))) ?_ ?_ ?_).symm
  · intro x hx
    have hxw : x ≠ w := (Finset.mem_erase.mp hx).1
    have hxv : x ≠ v := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
    refine mem_triplesThrough.mpr ⟨mem_triples.mpr ?_, by simp, by simp⟩
    rw [Finset.card_insert_of_notMem (by simp [hvw, Ne.symm hxv]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hxw]), Finset.card_singleton]
  · intro x hx y _ hEq
    have hxw : x ≠ w := (Finset.mem_erase.mp hx).1
    have hxv : x ≠ v := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
    have hxmem : x ∈ ({v, w, y} : Finset (Fin 11)) := by
      rw [← hEq]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem
    rcases hxmem with h | h | h
    · exact absurd h hxv
    · exact absurd h hxw
    · exact h
  · intro U hU
    obtain ⟨hUt, hUv, hUw⟩ := mem_triplesThrough.mp hU
    have hUcard : U.card = 3 := mem_triples.mp hUt
    have hwe : w ∈ U.erase v := Finset.mem_erase.mpr ⟨Ne.symm hvw, hUw⟩
    have hc1 : ((U.erase v).erase w).card = 1 := by
      rw [Finset.card_erase_of_mem hwe, Finset.card_erase_of_mem hUv, hUcard]
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc1
    have hxmem : x ∈ (U.erase v).erase w := by
      rw [hx]
      exact Finset.mem_singleton_self x
    have hxw : x ≠ w := (Finset.mem_erase.mp hxmem).1
    have hxv : x ≠ v := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hxmem)).1
    refine ⟨x, Finset.mem_erase.mpr
      ⟨hxw, Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ x⟩⟩, ?_⟩
    show ({v, w, x} : Finset (Fin 11)) = U
    rw [← hx, Finset.insert_erase hwe, Finset.insert_erase hUv]

/-! ### The forty-five triples through one vertex -/

/-- The triples of vertices containing a given one. -/
def triplesAt (v : Fin 11) : Finset (Finset (Fin 11)) := triples.filter fun U => v ∈ U

@[simp] theorem mem_triplesAt {v : Fin 11} {U : Finset (Fin 11)} :
    U ∈ triplesAt v ↔ U ∈ triples ∧ v ∈ U := Finset.mem_filter

/-- The triples through two vertices are those through the first that also
contain the second. -/
theorem triplesThrough_eq_filter (v w : Fin 11) :
    triplesThrough v w = (triplesAt v).filter fun U => w ∈ U := by
  rw [triplesThrough, triplesAt, Finset.filter_filter]

/-- **`45` triples contain a given vertex.** -/
theorem card_triplesAt (v : Fin 11) : (triplesAt v).card = 45 := by
  classical
  have hcard : ((Finset.univ : Finset (Fin 11)).erase v).card = 10 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
  have hpc : (Finset.powersetCard 2 ((Finset.univ : Finset (Fin 11)).erase v)).card = 45 := by
    rw [Finset.card_powersetCard, hcard]
    rfl
  rw [← hpc]
  refine (Finset.card_bij (fun s _ => insert v s) ?_ ?_ ?_).symm
  · intro s hs
    rw [Finset.mem_powersetCard] at hs
    have hvs : v ∉ s := fun h => (Finset.mem_erase.mp (hs.1 h)).1 rfl
    refine mem_triplesAt.mpr ⟨mem_triples.mpr ?_, Finset.mem_insert_self _ _⟩
    rw [Finset.card_insert_of_notMem hvs, hs.2]
  · intro s hs t ht hEq
    rw [Finset.mem_powersetCard] at hs ht
    have hvs : v ∉ s := fun h => (Finset.mem_erase.mp (hs.1 h)).1 rfl
    have hvt : v ∉ t := fun h => (Finset.mem_erase.mp (ht.1 h)).1 rfl
    have herase := congrArg (fun u => Finset.erase u v) hEq
    rwa [Finset.erase_insert hvs, Finset.erase_insert hvt] at herase
  · intro U hU
    obtain ⟨hUt, hUv⟩ := mem_triplesAt.mp hU
    refine ⟨U.erase v, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, Finset.insert_erase hUv⟩
    · intro x hx
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, Finset.mem_univ x⟩
    · rw [Finset.card_erase_of_mem hUv, mem_triples.mp hUt]

namespace GlobalDesign

variable (G : GlobalDesign)

/-! ### Degrees of a block -/

/-- A block is isolated at a vertex exactly at the three vertices of its
triple. -/
theorem arcDegree_eq_zero_iff {T : Finset (Fin 11)} (hT : T ∈ triples) (x : Fin 11) :
    arcDegree (G.block T) x = 0 ↔ x ∈ T := by
  constructor
  · intro h
    by_contra hx
    rw [G.block_cubic T hT x hx] at h
    omega
  · intro hx
    exact G.block_isolates T hT x hx

/-- **The degree product law.**  The degrees of two blocks multiply to `9` off
the union of their triples and to `0` on it, so their sum over the eleven
vertices is `9 (5 + #(T ∩ U))`. -/
theorem sum_arcDegree_mul {T U : Finset (Fin 11)} (hT : T ∈ triples) (hU : U ∈ triples) :
    (∑ x : Fin 11, arcDegree (G.block T) x * arcDegree (G.block U) x) =
      45 + 9 * (T ∩ U).card := by
  have hcases : ∀ x ∈ (Finset.univ : Finset (Fin 11)),
      arcDegree (G.block T) x * arcDegree (G.block U) x = 0 ∨
        arcDegree (G.block T) x * arcDegree (G.block U) x = 9 := by
    intro x _
    by_cases hxT : x ∈ T
    · exact Or.inl (by rw [G.block_isolates T hT x hxT, Nat.zero_mul])
    · by_cases hxU : x ∈ U
      · exact Or.inl (by rw [G.block_isolates U hU x hxU, Nat.mul_zero])
      · exact Or.inr (by rw [G.block_cubic T hT x hxT, G.block_cubic U hU x hxU])
  have h := sum_add_mul_card_filter_eq 9 (Finset.univ : Finset (Fin 11))
    (fun x => arcDegree (G.block T) x * arcDegree (G.block U) x) hcases
  have hset : ((Finset.univ : Finset (Fin 11)).filter fun x =>
      arcDegree (G.block T) x * arcDegree (G.block U) x = 0) = T ∪ U := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Nat.mul_eq_zero]
    rw [G.arcDegree_eq_zero_iff hT, G.arcDegree_eq_zero_iff hU]
  rw [hset, Finset.card_univ, Fintype.card_fin] at h
  have hcu := Finset.card_union_add_card_inter T U
  rw [mem_triples.mp hT, mem_triples.mp hU] at hcu
  omega

/-! ### (Z-DEG): every block is disjoint from exactly `24` others -/

/-- **The disjointness graph.**  The triples naming a block disjoint from the
block named by `T`. -/
def disjointFrom (T : Finset (Fin 11)) : Finset (Finset (Fin 11)) :=
  triples.filter fun U => (G.block T ∩ G.block U).card = 0

@[simp] theorem mem_disjointFrom {T U : Finset (Fin 11)} :
    U ∈ G.disjointFrom T ↔ U ∈ triples ∧ (G.block T ∩ G.block U).card = 0 :=
  Finset.mem_filter

/-- Membership in the disjointness graph, as emptiness of the meet. -/
theorem mem_disjointFrom_iff {T U : Finset (Fin 11)} :
    U ∈ G.disjointFrom T ↔ U ∈ triples ∧ G.block T ∩ G.block U = ∅ := by
  rw [mem_disjointFrom, Finset.card_eq_zero]

/-- A block meets the blocks named by all `165` triples in `432 = 12 · 36`
edges. -/
theorem sum_meet_over_triples {T : Finset (Fin 11)} (hT : T ∈ triples) :
    (∑ U ∈ triples, (G.block T ∩ G.block U).card) = 432 := by
  rw [sum_inter_card_over triples G.block (G.block T),
    Finset.sum_congr rfl fun e _ => G.edge_rep e, Finset.sum_const, G.block_card T hT]
  simp

/-- Every block of a global design is disjoint from exactly `24`
of the other `164`, so the disjointness relation is a `24`-regular graph on the
`165` triples. -/
theorem card_disjointFrom {T : Finset (Fin 11)} (hT : T ∈ triples) :
    (G.disjointFrom T).card = 24 := by
  classical
  have hdiag : (G.block T ∩ G.block T).card = 12 := by
    rw [Finset.inter_self]
    exact G.block_card T hT
  have hsum := G.sum_meet_over_triples hT
  have hsplit := Finset.sum_erase_add triples
    (fun U => (G.block T ∩ G.block U).card) hT
  have hcard : (triples.erase T).card = 164 := by
    rw [Finset.card_erase_of_mem hT, card_triples]
  have hcases : ∀ U ∈ triples.erase T,
      (G.block T ∩ G.block U).card = 0 ∨ (G.block T ∩ G.block U).card = 3 :=
    fun U hU => G.block_meet T hT U (Finset.mem_of_mem_erase hU)
      (Ne.symm (Finset.mem_erase.mp hU).1)
  have h := sum_add_mul_card_filter_eq 3 (triples.erase T)
    (fun U => (G.block T ∩ G.block U).card) hcases
  rw [hcard] at h
  have hset : ((triples.erase T).filter fun U => (G.block T ∩ G.block U).card = 0) =
      G.disjointFrom T := by
    ext U
    simp only [Finset.mem_filter, Finset.mem_erase, mem_disjointFrom]
    constructor
    · rintro ⟨⟨-, hU⟩, h0⟩
      exact ⟨hU, h0⟩
    · rintro ⟨hU, h0⟩
      refine ⟨⟨?_, hU⟩, h0⟩
      intro hUT
      rw [hUT, hdiag] at h0
      omega
  rw [hset] at h
  omega

/-- A block is not disjoint from itself. -/
theorem notMem_disjointFrom_self {T : Finset (Fin 11)} (hT : T ∈ triples) :
    T ∉ G.disjointFrom T := by
  intro hmem
  have h := (G.mem_disjointFrom.mp hmem).2
  rw [Finset.inter_self, G.block_card T hT] at h
  omega

/-- Two disjoint blocks are named by disjoint triples: a shared vertex would
force a meet of three edges. -/
theorem triples_disjoint_of_block_disjoint {T U : Finset (Fin 11)} (hT : T ∈ triples)
    (hU : U ∈ triples) (hTU : T ≠ U) (h : (G.block T ∩ G.block U).card = 0) :
    (T ∩ U).card = 0 := by
  by_contra hne
  rw [G.meet_of_shared T hT U hU hTU (Finset.card_pos.mp (Nat.pos_of_ne_zero hne))] at h
  omega

/-! ### (Z-PAIR): the local pair law -/

/-- The block named by a triple through `v` and `w` lives on the `36` edges
missing both. -/
theorem block_subset_off₂ {v w : Fin 11} {U : Finset (Fin 11)}
    (hU : U ∈ triplesThrough v w) : G.block U ⊆ Edge11.off₂ v w := by
  intro e he
  obtain ⟨hUt, hv, hw⟩ := mem_triplesThrough.mp hU
  exact Edge11.mem_off₂.mpr ⟨G.notMem_vertices_of_mem_block hUt he hv,
    G.notMem_vertices_of_mem_block hUt he hw⟩

/-- **The pair replication law.**  Every edge missing `v` and `w` lies on
exactly `3` of the `9` blocks named by triples through `v` and `w`.

This is the zero-variance count that
`SRG266.QuasiSymmetric.Residual165.localCount_two` performs for a residual
structure, redone from the axioms of a `GlobalDesign`: the nine blocks are
`12`-sets inside the `36` edges off `v` and `w`, pairwise meeting in `3`, so the
`36` replication numbers have mean `3` and sum of squares `324 = 36 · 9`. -/
theorem card_triplesThrough_filter {v w : Fin 11} (hvw : v ≠ w) {e : Edge11}
    (he : e ∈ Edge11.off₂ v w) :
    ((triplesThrough v w).filter fun U => e ∈ G.block U).card = 3 := by
  classical
  have hJcard : (triplesThrough v w).card = 9 := card_triplesThrough hvw
  have hsub : ∀ U ∈ triplesThrough v w, G.block U ⊆ Edge11.off₂ v w :=
    fun U hU => G.block_subset_off₂ hU
  set c : Edge11 → ℕ :=
    fun g => ((triplesThrough v w).filter fun U => g ∈ G.block U).card with hc
  have hsum : (∑ g ∈ Edge11.off₂ v w, c g) = 108 := by
    have hstep : (∑ U ∈ triplesThrough v w, (Edge11.off₂ v w ∩ G.block U).card) =
        ∑ g ∈ Edge11.off₂ v w, c g :=
      sum_inter_card_over (triplesThrough v w) G.block (Edge11.off₂ v w)
    have hcell : ∀ U ∈ triplesThrough v w, (Edge11.off₂ v w ∩ G.block U).card = 12 := by
      intro U hU
      rw [Finset.inter_eq_right.mpr (hsub U hU)]
      exact G.block_card U (mem_triplesThrough.mp hU).1
    rw [← hstep, Finset.sum_congr rfl hcell, Finset.sum_const, hJcard]
    simp
  have hsq : (∑ g ∈ Edge11.off₂ v w, c g ^ 2) = 324 := by
    have hstep : (∑ g ∈ Edge11.off₂ v w, c g ^ 2) =
        ∑ m ∈ triplesThrough v w, ∑ n ∈ triplesThrough v w,
          ((G.block m) ∩ (G.block n)).card :=
      sum_card_filter_sq (triplesThrough v w) G.block (Edge11.off₂ v w) hsub
    have hcell : ∀ m ∈ triplesThrough v w,
        (∑ n ∈ triplesThrough v w, ((G.block m) ∩ (G.block n)).card) = 36 := by
      intro m hm
      obtain ⟨hmt, hmv, -⟩ := mem_triplesThrough.mp hm
      have hdiag : ((G.block m) ∩ (G.block m)).card = 12 := by
        rw [Finset.inter_self]
        exact G.block_card m hmt
      have hsplit := Finset.sum_erase_add (triplesThrough v w)
        (fun k => ((G.block m) ∩ (G.block k)).card) hm
      have hoff : (∑ k ∈ (triplesThrough v w).erase m,
          ((G.block m) ∩ (G.block k)).card) = 24 := by
        have hval : ∀ k ∈ (triplesThrough v w).erase m,
            ((G.block m) ∩ (G.block k)).card = 3 := by
          intro k hk
          obtain ⟨hkt, hkv, -⟩ :=
            mem_triplesThrough.mp (Finset.mem_of_mem_erase hk)
          exact G.meet_of_shared m hmt k hkt (Ne.symm (Finset.mem_erase.mp hk).1)
            ⟨v, Finset.mem_inter.mpr ⟨hmv, hkv⟩⟩
        rw [Finset.sum_congr rfl hval, Finset.sum_const,
          Finset.card_erase_of_mem hm, hJcard]
        simp
      omega
    rw [hstep, Finset.sum_congr rfl hcell, Finset.sum_const, hJcard]
    simp
  have hcard : (Edge11.off₂ v w).card = 36 := Edge11.card_off₂ hvw
  have hle : ∀ g ∈ Edge11.off₂ v w, 6 * c g ≤ c g ^ 2 + 9 :=
    fun g _ => six_mul_le_sq_add_nine _
  have heq : (∑ g ∈ Edge11.off₂ v w, 6 * c g) =
      ∑ g ∈ Edge11.off₂ v w, (c g ^ 2 + 9) := by
    rw [← Finset.mul_sum, hsum, Finset.sum_add_distrib, hsq, Finset.sum_const, hcard]
    simp
  exact eq_three_of_six_mul_eq ((Finset.sum_eq_sum_iff_of_le hle).mp heq e he)

/-- A block is a cubic graph on the eight vertices off its triple, so it has
`6` edges missing two further vertices `v` and `w`, plus the edge `vw` itself if
that edge belongs to the block. -/
theorem card_block_inter_off₂ {T : Finset (Fin 11)} (hT : T ∈ triples) {v w : Fin 11}
    (hvw : v ≠ w) (hv : v ∉ T) (hw : w ∉ T) :
    ((G.block T) ∩ Edge11.off₂ v w).card =
      6 + if Edge11.mk' hvw ∈ G.block T then 1 else 0 := by
  classical
  have hcardB : (G.block T).card = 12 := G.block_card T hT
  have hdv : ((G.block T).filter fun e => v ∈ e.vertices).card = 3 :=
    G.block_cubic T hT v hv
  have hdw : ((G.block T).filter fun e => w ∈ e.vertices).card = 3 :=
    G.block_cubic T hT w hw
  have hboth := card_filter_vertices_pair hvw (G.block T)
  have hunion := Finset.card_union_add_card_inter
    ((G.block T).filter fun e => v ∈ e.vertices)
    ((G.block T).filter fun e => w ∈ e.vertices)
  rw [← Finset.filter_or, ← Finset.filter_and, hdv, hdw, hboth] at hunion
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := G.block T) (p := fun e => v ∈ e.vertices ∨ w ∈ e.vertices)
  have hneg : ((G.block T).filter fun e => ¬ (v ∈ e.vertices ∨ w ∈ e.vertices)) =
      (G.block T) ∩ Edge11.off₂ v w := by
    rw [← Finset.filter_mem_eq_inter]
    refine Finset.filter_congr fun e _ => ?_
    simp [Edge11.mem_off₂, not_or]
  rw [hneg, hcardB] at hsplit
  split_ifs at hunion ⊢ <;> omega

/-- For a triple `T` and two vertices `v ≠ w`
off `T`, exactly `3` of the `9` triples through `v` and `w` name a block
disjoint from `B T` — or `2` of them, if the edge `vw` itself belongs to `B T`.

This is the rule that turns some of the `0`/`3` disjunctions into forced
zeroes. -/
theorem card_disjointFrom_inter_triplesThrough {T : Finset (Fin 11)} (hT : T ∈ triples)
    {v w : Fin 11} (hvw : v ≠ w) (hv : v ∉ T) (hw : w ∉ T) :
    (G.disjointFrom T ∩ triplesThrough v w).card +
      (if Edge11.mk' hvw ∈ G.block T then 1 else 0) = 3 := by
  classical
  have hJcard : (triplesThrough v w).card = 9 := card_triplesThrough hvw
  have hstep : (∑ U ∈ triplesThrough v w, (G.block T ∩ G.block U).card) =
      ∑ e ∈ G.block T, ((triplesThrough v w).filter fun U => e ∈ G.block U).card :=
    sum_inter_card_over (triplesThrough v w) G.block (G.block T)
  have hcell : ∀ e ∈ G.block T,
      ((triplesThrough v w).filter fun U => e ∈ G.block U).card =
        if e ∈ Edge11.off₂ v w then 3 else 0 := by
    intro e _
    by_cases hoff : e ∈ Edge11.off₂ v w
    · rw [if_pos hoff]
      exact G.card_triplesThrough_filter hvw hoff
    · rw [if_neg hoff, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro U hU hmem
      exact hoff (G.block_subset_off₂ hU hmem)
  have hsum : (∑ U ∈ triplesThrough v w, (G.block T ∩ G.block U).card) =
      3 * (6 + if Edge11.mk' hvw ∈ G.block T then 1 else 0) := by
    rw [hstep, Finset.sum_congr rfl hcell, Finset.sum_ite_mem, Finset.sum_const,
      G.card_block_inter_off₂ hT hvw hv hw, smul_eq_mul, Nat.mul_comm]
  have hcases : ∀ U ∈ triplesThrough v w,
      (G.block T ∩ G.block U).card = 0 ∨ (G.block T ∩ G.block U).card = 3 := by
    intro U hU
    obtain ⟨hUt, hUv, -⟩ := mem_triplesThrough.mp hU
    refine G.block_meet T hT U hUt ?_
    intro hTU
    exact hv (hTU ▸ hUv)
  have h := sum_add_mul_card_filter_eq 3 (triplesThrough v w)
    (fun U => (G.block T ∩ G.block U).card) hcases
  rw [hsum, hJcard] at h
  have hset : ((triplesThrough v w).filter fun U => (G.block T ∩ G.block U).card = 0) =
      G.disjointFrom T ∩ triplesThrough v w := by
    ext U
    simp only [Finset.mem_filter, Finset.mem_inter, mem_disjointFrom, mem_triplesThrough]
    tauto
  rw [hset] at h
  split_ifs at h ⊢ <;> omega

/-! ### (Z-VERT): the local vertex law -/

/-- No block disjoint from `B T` is named by a triple through a vertex of `T`:
sharing a vertex forces a meet of three edges. -/
theorem disjointFrom_inter_triplesAt_eq_empty {T : Finset (Fin 11)} (hT : T ∈ triples)
    {v : Fin 11} (hv : v ∈ T) : G.disjointFrom T ∩ triplesAt v = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun U hU => ?_
  rw [Finset.mem_inter, mem_disjointFrom, mem_triplesAt] at hU
  obtain ⟨⟨hUt, h0⟩, -, hUv⟩ := hU
  by_cases hTU : T = U
  · rw [← hTU, Finset.inter_self, G.block_card T hT] at h0
    omega
  · rw [G.meet_of_shared T hT U hUt hTU ⟨v, Finset.mem_inter.mpr ⟨hv, hUv⟩⟩] at h0
    omega

/-- The seven vertices off `T` other than `v`, over which the local vertex law
sums (Z-PAIR). -/
private def offVertices (T : Finset (Fin 11)) (v : Fin 11) : Finset (Fin 11) :=
  (Finset.univ.filter fun w => w ∉ T).erase v

private theorem card_offVertices {T : Finset (Fin 11)} (hT : T ∈ triples) {v : Fin 11}
    (hv : v ∉ T) : (offVertices T v).card = 7 := by
  classical
  have hfilter : ((Finset.univ : Finset (Fin 11)).filter fun w => w ∈ T) = T := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 11))) (p := fun w => w ∈ T)
  rw [hfilter, mem_triples.mp hT, Finset.card_univ, Fintype.card_fin] at hsplit
  have hvmem : v ∈ (Finset.univ : Finset (Fin 11)).filter fun w => w ∉ T :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩
  rw [offVertices, Finset.card_erase_of_mem hvmem]
  omega

/-- For a triple `T` and a vertex `v` off
`T`, exactly `9` of the `45` triples through `v` name a block disjoint from
`B T`; for `v` in `T` there are none.

Equivalently, in the notation of the disjointness graph `Z`, the vertex/triple
incidence `W` satisfies `(Z + 9 I) Wᵀ = 9 J`.  The proof sums (Z-PAIR)
(`GlobalDesign.card_disjointFrom_inter_triplesThrough`) over the seven vertices
`w` off `T` other than `v`: each disjointness-neighbour of `B T` through `v` is
counted twice, once for each of its two vertices besides `v` — all of which lie
off `T`, since disjoint blocks have disjoint triples — while the correction
terms `[vw ∈ B T]` add up to the degree `3` of `B T` at `v`.  So
`2 · #(Z T ∩ triplesAt v) + 3 = 7 · 3`. -/
theorem card_disjointFrom_inter_triplesAt {T : Finset (Fin 11)} (hT : T ∈ triples)
    (v : Fin 11) :
    (G.disjointFrom T ∩ triplesAt v).card = if v ∈ T then 0 else 9 := by
  classical
  by_cases hv : v ∈ T
  · rw [if_pos hv, G.disjointFrom_inter_triplesAt_eq_empty hT hv, Finset.card_empty]
  rw [if_neg hv]
  set W : Finset (Fin 11) := offVertices T v with hWdef
  have hWcard : W.card = 7 := card_offVertices hT hv
  have hWmem : ∀ w ∈ W, w ≠ v ∧ w ∉ T := by
    intro w hw
    rw [hWdef, offVertices, Finset.mem_erase, Finset.mem_filter] at hw
    exact ⟨hw.1, hw.2.2⟩
  -- (Z-PAIR) at every vertex of `W`, with the correction term as an edge count
  have hZP : ∀ w ∈ W, (G.disjointFrom T ∩ triplesThrough v w).card +
      ((G.block T).filter fun e => v ∈ e.vertices ∧ w ∈ e.vertices).card = 3 := by
    intro w hw
    obtain ⟨hwv, hwT⟩ := hWmem w hw
    rw [card_filter_vertices_pair (Ne.symm hwv) (G.block T)]
    exact G.card_disjointFrom_inter_triplesThrough hT (Ne.symm hwv) hv hwT
  have htotal : (∑ w ∈ W, ((G.disjointFrom T ∩ triplesThrough v w).card +
      ((G.block T).filter fun e => v ∈ e.vertices ∧ w ∈ e.vertices).card)) = 21 := by
    rw [Finset.sum_congr rfl hZP, Finset.sum_const, hWcard]
    simp
  have hsplit : (∑ w ∈ W, ((G.disjointFrom T ∩ triplesThrough v w).card +
      ((G.block T).filter fun e => v ∈ e.vertices ∧ w ∈ e.vertices).card)) =
      (∑ w ∈ W, (G.disjointFrom T ∩ triplesThrough v w).card) +
        ∑ w ∈ W, ((G.block T).filter fun e => v ∈ e.vertices ∧ w ∈ e.vertices).card :=
    Finset.sum_add_distrib
  -- the neighbours, each counted twice
  have hneighbours : (∑ w ∈ W, (G.disjointFrom T ∩ triplesThrough v w).card) =
      2 * (G.disjointFrom T ∩ triplesAt v).card := by
    have hset : ∀ w : Fin 11, G.disjointFrom T ∩ triplesThrough v w =
        (G.disjointFrom T ∩ triplesAt v).filter fun U => w ∈ U := by
      intro w
      ext U
      simp only [Finset.mem_inter, Finset.mem_filter, mem_disjointFrom, mem_triplesAt,
        mem_triplesThrough]
      tauto
    have hcell : ∀ U ∈ G.disjointFrom T ∩ triplesAt v, (U ∩ W).card = 2 := by
      intro U hU
      rw [Finset.mem_inter, mem_disjointFrom, mem_triplesAt] at hU
      obtain ⟨⟨hUt, h0⟩, -, hUv⟩ := hU
      have hTU : T ≠ U := fun h => hv (h ▸ hUv)
      have hTUcard : (T ∩ U).card = 0 :=
        G.triples_disjoint_of_block_disjoint hT hUt hTU h0
      have hoff : ∀ x ∈ U, x ∉ T := by
        intro x hx hxT
        have : x ∈ T ∩ U := Finset.mem_inter.mpr ⟨hxT, hx⟩
        rw [Finset.card_eq_zero.mp hTUcard] at this
        exact absurd this (Finset.notMem_empty x)
      rw [hWdef, offVertices, inter_erase_filter_notMem hoff,
        Finset.card_erase_of_mem hUv, mem_triples.mp hUt]
    have hbij : (∑ w ∈ W,
        ((G.disjointFrom T ∩ triplesAt v).filter fun U => w ∈ U).card) =
        ∑ U ∈ G.disjointFrom T ∩ triplesAt v, (U ∩ W).card :=
      sum_card_filter_mem W (G.disjointFrom T ∩ triplesAt v) fun U => U
    rw [Finset.sum_congr rfl fun w _ => congrArg Finset.card (hset w), hbij,
      Finset.sum_congr rfl hcell, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  -- the correction terms, adding up to the degree of `B T` at `v`
  have hdegree : (∑ w ∈ W,
      ((G.block T).filter fun e => v ∈ e.vertices ∧ w ∈ e.vertices).card) = 3 := by
    have hset : ∀ w : Fin 11,
        ((G.block T).filter fun e => v ∈ e.vertices ∧ w ∈ e.vertices) =
        (((G.block T).filter fun e => v ∈ e.vertices).filter fun e => w ∈ e.vertices) :=
      fun w => (Finset.filter_filter _ _ _).symm
    have hcell : ∀ e ∈ (G.block T).filter fun e => v ∈ e.vertices,
        (e.vertices ∩ W).card = 1 := by
      intro e he
      rw [Finset.mem_filter] at he
      have hoff : ∀ x ∈ e.vertices, x ∉ T := by
        intro x hx hxT
        exact G.notMem_vertices_of_mem_block hT he.1 hxT hx
      rw [hWdef, offVertices, inter_erase_filter_notMem hoff,
        Finset.card_erase_of_mem he.2, Edge11.card_vertices]
    rw [Finset.sum_congr rfl fun w _ => congrArg Finset.card (hset w),
      sum_card_filter_mem W ((G.block T).filter fun e => v ∈ e.vertices)
        Edge11.vertices,
      Finset.sum_congr rfl hcell, Finset.sum_const, smul_eq_mul, Nat.mul_one]
    exact G.block_cubic T hT v hv
  omega

/-! ### (Z-MU): the common-neighbour law -/

/-- **The two-block trace identity.**  Summing the product of the meets of two
fixed blocks with a varying block over all `165` triples gives
`1053 + 9 #(T ∩ U) + 27 #(B T ∩ B U)`.

This is the edge-side evaluation: it uses only `edge_rep`, `pair_mult` and the
degree product law `SRG266.QuasiSymmetric.GlobalDesign.sum_arcDegree_mul`. -/
theorem sum_meet_mul_over_triples {T U : Finset (Fin 11)} (hT : T ∈ triples)
    (hU : U ∈ triples) :
    (∑ W ∈ triples, (G.block T ∩ G.block W).card * (G.block U ∩ G.block W).card) =
      1053 + 9 * (T ∩ U).card + 27 * (G.block T ∩ G.block U).card := by
  classical
  have hstep := sum_mul_inter_card_over triples G.block (G.block T) (G.block U)
  have hcell : ∀ e f : Edge11,
      (triples.filter fun W => e ∈ G.block W ∧ f ∈ G.block W).card =
        7 + Edge11.vmeet e f + (if e = f then 27 else 0) := by
    intro e f
    by_cases hef : e = f
    · subst hef
      have hset : (triples.filter fun W => e ∈ G.block W ∧ e ∈ G.block W) =
          triples.filter fun W => e ∈ G.block W :=
        Finset.filter_congr fun _ _ => and_self_iff
      rw [hset, G.edge_rep e, Edge11.vmeet_self, if_pos rfl]
    · rw [G.pair_mult e f hef, if_neg hef, Nat.add_zero]
  have hinner : ∀ e ∈ G.block T,
      (∑ f ∈ G.block U, (7 + Edge11.vmeet e f + (if e = f then 27 else 0))) =
        (∑ f ∈ G.block U, (7 + Edge11.vmeet e f)) +
          ∑ f ∈ G.block U, (if e = f then 27 else 0) :=
    fun _ _ => Finset.sum_add_distrib
  have hseven : ∀ e ∈ G.block T,
      (∑ f ∈ G.block U, (7 + Edge11.vmeet e f)) =
        84 + ∑ f ∈ G.block U, Edge11.vmeet e f := by
    intro e _
    rw [Finset.sum_add_distrib, Finset.sum_const, G.block_card U hU, smul_eq_mul]
  have hdiagsum : (∑ e ∈ G.block T, ∑ f ∈ G.block U, (if e = f then 27 else 0)) =
      27 * (G.block T ∩ G.block U).card := by
    have hone : ∀ e ∈ G.block T, (∑ f ∈ G.block U, (if e = f then 27 else 0)) =
        if e ∈ G.block U then 27 else 0 :=
      fun e _ => Finset.sum_ite_eq (G.block U) e fun _ => 27
    rw [Finset.sum_congr rfl hone, Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul,
      Nat.mul_comm]
  have hvm : (∑ e ∈ G.block T, ∑ f ∈ G.block U, Edge11.vmeet e f) =
      45 + 9 * (T ∩ U).card := by
    rw [sum_vmeet_pair]
    exact G.sum_arcDegree_mul hT hU
  rw [hstep, Finset.sum_congr rfl fun e _ =>
      Finset.sum_congr rfl fun f _ => hcell e f,
    Finset.sum_congr rfl hinner, Finset.sum_add_distrib,
    Finset.sum_congr rfl hseven, Finset.sum_add_distrib, Finset.sum_const,
    G.block_card T hT, smul_eq_mul, hvm, hdiagsum]
  omega

/-- Two distinct blocks of a global
design have exactly `#(T ∩ U) + 3` common neighbours in the disjointness
graph — unless they are themselves disjoint, in which case they have **none**.

The proof compares the edge-side evaluation
`SRG266.QuasiSymmetric.GlobalDesign.sum_meet_mul_over_triples` of
`∑_W #(B T ∩ B W) · #(B U ∩ B W)` with the block-side one, where every
off-diagonal factor lies in `{0, 3}` and (Z-DEG) counts the zeroes. -/
theorem card_disjointFrom_inter {T U : Finset (Fin 11)} (hT : T ∈ triples)
    (hU : U ∈ triples) (hTU : T ≠ U) :
    (G.disjointFrom T ∩ G.disjointFrom U).card =
      if (G.block T ∩ G.block U).card = 0 then 0 else (T ∩ U).card + 3 := by
  classical
  -- the two evaluations of the trace sum
  have hSum := G.sum_meet_mul_over_triples hT hU
  have hpair : (triples.filter fun W => ¬ (W ≠ T ∧ W ≠ U)) =
      ({T, U} : Finset (Finset (Fin 11))) := by
    ext W
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, ne_eq,
      not_and_or, not_not]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · rintro (rfl | rfl)
      · exact ⟨hT, Or.inl rfl⟩
      · exact ⟨hU, Or.inr rfl⟩
  have hDcard : (triples.filter fun W => W ≠ T ∧ W ≠ U).card = 163 := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := triples) (p := fun W => W ≠ T ∧ W ≠ U)
    rw [hpair, Finset.card_pair hTU, card_triples] at hsplit
    omega
  have hPT : (G.block T ∩ G.block T).card * (G.block U ∩ G.block T).card =
      12 * (G.block T ∩ G.block U).card := by
    rw [Finset.inter_self, G.block_card T hT, Finset.inter_comm (G.block U)]
  have hPU : (G.block T ∩ G.block U).card * (G.block U ∩ G.block U).card =
      12 * (G.block T ∩ G.block U).card := by
    rw [Finset.inter_self, G.block_card U hU, Nat.mul_comm]
  have hsplitsum := Finset.sum_filter_add_sum_filter_not triples
    (fun W => W ≠ T ∧ W ≠ U)
    fun W => (G.block T ∩ G.block W).card * (G.block U ∩ G.block W).card
  rw [hpair, Finset.sum_pair hTU, hPT, hPU] at hsplitsum
  -- the block-side count of the zeroes
  have hcasesP : ∀ W ∈ triples.filter fun W => W ≠ T ∧ W ≠ U,
      (G.block T ∩ G.block W).card * (G.block U ∩ G.block W).card = 0 ∨
        (G.block T ∩ G.block W).card * (G.block U ∩ G.block W).card = 9 := by
    intro W hW
    obtain ⟨hWt, hWT, hWU⟩ := Finset.mem_filter.mp hW
    rcases G.block_meet T hT W hWt (Ne.symm hWT) with h1 | h1 <;>
      rcases G.block_meet U hU W hWt (Ne.symm hWU) with h2 | h2 <;>
      rw [h1, h2] <;> simp
  have hcount := sum_add_mul_card_filter_eq 9 (triples.filter fun W => W ≠ T ∧ W ≠ U)
    (fun W => (G.block T ∩ G.block W).card * (G.block U ∩ G.block W).card) hcasesP
  rw [hDcard] at hcount
  have hZ0 : ((triples.filter fun W => W ≠ T ∧ W ≠ U).filter fun W =>
        (G.block T ∩ G.block W).card * (G.block U ∩ G.block W).card = 0) =
      (G.disjointFrom T ∪ G.disjointFrom U).filter fun W => W ≠ T ∧ W ≠ U := by
    ext W
    simp only [Finset.mem_filter, Finset.mem_union, mem_disjointFrom, Nat.mul_eq_zero]
    constructor
    · rintro ⟨⟨hWt, hne⟩, h | h⟩
      · exact ⟨Or.inl ⟨hWt, h⟩, hne⟩
      · exact ⟨Or.inr ⟨hWt, h⟩, hne⟩
    · rintro ⟨h | h, hne⟩
      · exact ⟨⟨h.1, hne⟩, Or.inl h.2⟩
      · exact ⟨⟨h.1, hne⟩, Or.inr h.2⟩
  rw [hZ0] at hcount
  -- the union and intersection of the two neighbourhoods
  have hunion := Finset.card_union_add_card_inter (G.disjointFrom T) (G.disjointFrom U)
  rw [G.card_disjointFrom hT, G.card_disjointFrom hU] at hunion
  have hfilt := Finset.card_filter_add_card_filter_not
    (s := G.disjointFrom T ∪ G.disjointFrom U) (p := fun W => W ≠ T ∧ W ≠ U)
  rcases G.block_meet T hT U hU hTU with h0 | h3
  · -- the two blocks are disjoint: they have no common neighbour
    rw [if_pos h0]
    have h0' : (G.block U ∩ G.block T).card = 0 := by
      rwa [Finset.inter_comm]
    have htu : (T ∩ U).card = 0 := G.triples_disjoint_of_block_disjoint hT hU hTU h0
    have hTmem : T ∈ G.disjointFrom T ∪ G.disjointFrom U :=
      Finset.mem_union_right _ (G.mem_disjointFrom.mpr ⟨hT, h0'⟩)
    have hUmem : U ∈ G.disjointFrom T ∪ G.disjointFrom U :=
      Finset.mem_union_left _ (G.mem_disjointFrom.mpr ⟨hU, h0⟩)
    have htwo : ((G.disjointFrom T ∪ G.disjointFrom U).filter fun W =>
        ¬ (W ≠ T ∧ W ≠ U)) = ({T, U} : Finset (Finset (Fin 11))) := by
      ext W
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, ne_eq,
        not_and_or, not_not]
      constructor
      · rintro ⟨-, h⟩
        exact h
      · rintro (rfl | rfl)
        · exact ⟨hTmem, Or.inl rfl⟩
        · exact ⟨hUmem, Or.inr rfl⟩
    rw [htwo, Finset.card_pair hTU] at hfilt
    rw [h0, htu] at hSum
    rw [h0] at hsplitsum
    omega
  · -- the two blocks meet: the common neighbours are `#(T ∩ U) + 3`
    rw [if_neg (by omega)]
    have hnone : ((G.disjointFrom T ∪ G.disjointFrom U).filter fun W =>
        ¬ (W ≠ T ∧ W ≠ U)) = (∅ : Finset (Finset (Fin 11))) := by
      have h3' : (G.block U ∩ G.block T).card = 3 := by
        rwa [Finset.inter_comm]
      refine Finset.filter_eq_empty_iff.mpr ?_
      intro W hW
      simp only [ne_eq, not_and_or, not_not, not_or]
      rw [Finset.mem_union, mem_disjointFrom, mem_disjointFrom] at hW
      constructor
      · intro hWT
        subst hWT
        rcases hW with h | h
        · rw [Finset.inter_self, G.block_card W hT] at h
          omega
        · rw [h3'] at h
          omega
      · intro hWU
        subst hWU
        rcases hW with h | h
        · rw [h3] at h
          omega
        · rw [Finset.inter_self, G.block_card W hU] at h
          omega
    rw [hnone, Finset.card_empty] at hfilt
    rw [h3] at hSum hsplitsum
    omega

/-! ### (Z-TRI): the disjointness graph is triangle free -/

/-- Two disjoint blocks of a global design have no common
neighbour in the disjointness graph: the graph is triangle free. -/
theorem disjointFrom_inter_eq_empty {T U : Finset (Fin 11)} (hT : T ∈ triples)
    (hU : U ∈ triples) (hTU : T ≠ U) (h : G.block T ∩ G.block U = ∅) :
    G.disjointFrom T ∩ G.disjointFrom U = ∅ := by
  have hcard := G.card_disjointFrom_inter hT hU hTU
  rw [if_pos (Finset.card_eq_zero.mpr h)] at hcard
  exact Finset.card_eq_zero.mp hcard

/-- **No three residual blocks are pairwise disjoint.**  The sharpest of the
six laws, and the one a search uses as a global cut: the disjointness relation
of a `GlobalDesign` contains no triangle. -/
theorem no_three_pairwise_disjoint {T U W : Finset (Fin 11)} (hT : T ∈ triples)
    (hU : U ∈ triples) (hW : W ∈ triples) (hTU : T ≠ U)
    (hTUb : G.block T ∩ G.block U = ∅) (hTWb : G.block T ∩ G.block W = ∅)
    (hUWb : G.block U ∩ G.block W = ∅) : False := by
  have hempty := G.disjointFrom_inter_eq_empty hT hU hTU hTUb
  have hmem : W ∈ G.disjointFrom T ∩ G.disjointFrom U :=
    Finset.mem_inter.mpr ⟨G.mem_disjointFrom_iff.mpr ⟨hW, hTWb⟩,
      G.mem_disjointFrom_iff.mpr ⟨hW, hUWb⟩⟩
  rw [hempty] at hmem
  exact absurd hmem (Finset.notMem_empty W)

/-! ### (Z-EDGE): the neighbourhood of a block, edge by edge -/

/-- The degrees of a block at the two endpoints of an edge.  Each endpoint on
the naming triple contributes `0` and each endpoint off it contributes `3`, so
the two degrees and `3` times the number of endpoints on the triple always add
up to `6`. -/
theorem sum_arcDegree_vertices {T : Finset (Fin 11)} (hT : T ∈ triples) (e : Edge11) :
    (∑ x ∈ e.vertices, arcDegree (G.block T) x) + 3 * (e.vertices ∩ T).card = 6 := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not e.vertices (fun x => x ∈ T)
    fun x => arcDegree (G.block T) x
  have hzero : (∑ x ∈ e.vertices.filter fun x => x ∈ T, arcDegree (G.block T) x) = 0 :=
    Finset.sum_eq_zero fun x hx => G.block_isolates T hT x (Finset.mem_filter.mp hx).2
  have hthree : (∑ x ∈ e.vertices.filter fun x => ¬ x ∈ T, arcDegree (G.block T) x) =
      3 * (e.vertices.filter fun x => ¬ x ∈ T).card := by
    rw [Finset.sum_congr rfl fun x hx =>
      G.block_cubic T hT x (Finset.mem_filter.mp hx).2, Finset.sum_const, smul_eq_mul,
      Nat.mul_comm]
  have hcard := Finset.card_filter_add_card_filter_not (s := e.vertices)
    (p := fun x => x ∈ T)
  rw [Finset.filter_mem_eq_inter, Edge11.card_vertices] at hcard
  omega

/-- **The trace of a block against the blocks through an edge.**  For an edge
`e` outside `B T`, summing `#(B T ∩ B U)` over the `36` triples `U` whose block
contains `e` gives `90 − 3 · #(e ∩ T)`.

This is the edge-side evaluation: `pair_mult` turns the sum into
`12 · 7 + ∑_{f ∈ B T} vmeet e f`, and the latter is the sum of the degrees of
`B T` at the two endpoints of `e`
(`SRG266.QuasiSymmetric.GlobalDesign.sum_arcDegree_vertices`). -/
theorem sum_meet_over_triples_filter {T : Finset (Fin 11)} (hT : T ∈ triples)
    {e : Edge11} (he : e ∉ G.block T) :
    (∑ U ∈ triples.filter fun U => e ∈ G.block U, (G.block T ∩ G.block U).card) +
      3 * (e.vertices ∩ T).card = 90 := by
  classical
  have hcell : ∀ f ∈ G.block T,
      ((triples.filter fun U => e ∈ G.block U).filter fun U => f ∈ G.block U).card =
        7 + Edge11.vmeet e f := by
    intro f hf
    have hef : e ≠ f := fun h => he (h ▸ hf)
    rw [Finset.filter_filter]
    exact G.pair_mult e f hef
  rw [sum_inter_card_over (triples.filter fun U => e ∈ G.block U) G.block (G.block T),
    Finset.sum_congr rfl hcell, Finset.sum_add_distrib, Finset.sum_const,
    G.block_card T hT, smul_eq_mul, sum_vmeet_left]
  have h := G.sum_arcDegree_vertices hT e
  omega

/-- The neighbourhood of a block covers every edge it misses, with
a determined multiplicity.**  For an edge `e` outside `B T`, exactly
`6 + #(e ∩ T)` of the `24` blocks disjoint from `B T` contain `e`: `8` when both
endpoints of `e` lie on `T`, `7` when one does and `6` when neither does.

The `24` neighbouring blocks carry `24 · 12 = 288` edges with multiplicity, and
the law distributes them: `3 · 8` on the three edges inside `T`, `24 · 7` on the
edges from `T` to the eight vertices off it, `16 · 6` on the edges off `T` that
`B T` misses, and `0` on the twelve edges of `B T` itself.

Unlike the five laws above, which index the neighbourhood by triples, this one
indexes it by edges: it says the block `B T` is recovered from its
disjointness-neighbourhood as the set of edges that neighbourhood misses.  It is
proved by the same double count as (Z-DEG), restricted to the `36` blocks
through `e`: their meets with `B T` lie in `{0, 3}` and sum to `90 − 3 #(e ∩ T)`
by `SRG266.QuasiSymmetric.GlobalDesign.sum_meet_over_triples_filter`, so
`3 · (36 − d) = 90 − 3 #(e ∩ T)`. -/
theorem card_disjointFrom_filter_mem_block {T : Finset (Fin 11)} (hT : T ∈ triples)
    {e : Edge11} (he : e ∉ G.block T) :
    ((G.disjointFrom T).filter fun U => e ∈ G.block U).card = 6 + (e.vertices ∩ T).card := by
  classical
  have hcases : ∀ U ∈ triples.filter fun U => e ∈ G.block U,
      (G.block T ∩ G.block U).card = 0 ∨ (G.block T ∩ G.block U).card = 3 := by
    intro U hU
    obtain ⟨hUt, hUe⟩ := Finset.mem_filter.mp hU
    exact G.block_meet T hT U hUt fun hTU => he (hTU ▸ hUe)
  have hcount := sum_add_mul_card_filter_eq 3 (triples.filter fun U => e ∈ G.block U)
    (fun U => (G.block T ∩ G.block U).card) hcases
  rw [G.edge_rep e] at hcount
  have hset : ((triples.filter fun U => e ∈ G.block U).filter fun U =>
        (G.block T ∩ G.block U).card = 0) =
      (G.disjointFrom T).filter fun U => e ∈ G.block U := by
    ext U
    simp only [Finset.mem_filter, mem_disjointFrom]
    tauto
  rw [hset] at hcount
  have hsum := G.sum_meet_over_triples_filter hT he
  omega

/-- Every edge outside a block lies on a block disjoint from it. -/
theorem exists_mem_disjointFrom_mem_block {T : Finset (Fin 11)} (hT : T ∈ triples)
    {e : Edge11} (he : e ∉ G.block T) : ∃ U ∈ G.disjointFrom T, e ∈ G.block U := by
  classical
  have hcard := G.card_disjointFrom_filter_mem_block hT he
  obtain ⟨U, hU⟩ := Finset.card_pos.mp
    (show 0 < ((G.disjointFrom T).filter fun U => e ∈ G.block U).card by omega)
  exact ⟨U, (Finset.mem_filter.mp hU).1, (Finset.mem_filter.mp hU).2⟩

/-- **A block is the complement of the union of its disjointness-neighbours.**
The `24` blocks disjoint from `B T` cover exactly the `43` edges of `K₁₁` that
`B T` misses, so `B T` is determined by the set of triples naming a block
disjoint from it. -/
theorem biUnion_disjointFrom_eq_compl {T : Finset (Fin 11)} (hT : T ∈ triples) :
    (G.disjointFrom T).biUnion G.block = Finset.univ \ G.block T := by
  classical
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨U, hU, heU⟩ hmem
    have hinter : e ∈ G.block T ∩ G.block U := Finset.mem_inter.mpr ⟨hmem, heU⟩
    rw [(G.mem_disjointFrom_iff.mp hU).2] at hinter
    exact absurd hinter (Finset.notMem_empty e)
  · exact fun he => G.exists_mem_disjointFrom_mem_block hT he

/-- The union of the blocks disjoint from a block has `43` edges. -/
theorem card_biUnion_disjointFrom {T : Finset (Fin 11)} (hT : T ∈ triples) :
    ((G.disjointFrom T).biUnion G.block).card = 43 := by
  classical
  have h : ((Finset.univ : Finset Edge11) \ G.block T).card =
      (Finset.univ : Finset Edge11).card - (G.block T ∩ Finset.univ).card :=
    Finset.card_sdiff
  rw [Finset.inter_univ, Finset.card_univ, Edge11.card_edge11, G.block_card T hT] at h
  rw [G.biUnion_disjointFrom_eq_compl hT]
  omega

end GlobalDesign

end SRG266.QuasiSymmetric
