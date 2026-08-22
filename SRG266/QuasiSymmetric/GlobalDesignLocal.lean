/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.GlobalDesignLaws
import SRG266.QuasiSymmetric.LocalDesign

/-!
# The eleven local designs inside the global residual design

A `GlobalDesign` consists of `165` twelve-edge blocks indexed by the triples
they isolate. For each vertex `v`, the `45` triples containing `v` form a
`LocalDesign v`. The required replication and pair-multiplicity laws follow by
finite double counting.
-/

open scoped BigOperators

namespace SRG266.QuasiSymmetric

/-! ### A zero-variance pair with an arbitrary mean

`SRG266.QuasiSymmetric.six_mul_le_sq_add_nine` and
`SRG266.QuasiSymmetric.eq_three_of_six_mul_eq` are the case `c = 3` of the two
statements below; the local replication law needs the case `c = 12` as well. -/

/-- For all natural numbers `2 c x ≤ x² + c²`, with equality exactly at
`x = c`. -/
theorem two_mul_mul_le_sq_add_sq (c x : ℕ) : 2 * c * x ≤ x ^ 2 + c ^ 2 := by
  nlinarith [sq_nonneg ((x : ℤ) - (c : ℤ)), Int.ofNat_le.mpr (Nat.zero_le x),
    Int.ofNat_le.mpr (Nat.zero_le c)]

/-- The equality case of `SRG266.QuasiSymmetric.two_mul_mul_le_sq_add_sq`. -/
theorem eq_of_two_mul_mul_eq {c x : ℕ} (h : 2 * c * x = x ^ 2 + c ^ 2) : x = c := by
  have hcast : (2 : ℤ) * (c : ℤ) * (x : ℤ) = (x : ℤ) ^ 2 + (c : ℤ) ^ 2 := by
    exact_mod_cast h
  have hz : ((x : ℤ) - (c : ℤ)) ^ 2 = 0 := by linear_combination -hcast
  have hroot := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
  have hx : (x : ℤ) = (c : ℤ) := by linarith
  exact_mod_cast hx

/-! ### Edges of `K₁₁ − v` name the triples through `v` -/

/-- Adjoining a vertex to an edge missing it gives a triple. -/
theorem mem_triples_insert {v : Fin 11} {p : Edge11} (hp : v ∉ p.vertices) :
    insert v p.vertices ∈ triples :=
  mem_triples.mpr (Edge11.card_insert_vertices hp)

/-- Distinct edges off `v` name distinct triples through `v`. -/
theorem edge_of_insert_vertices_eq {v : Fin 11} {p q : Edge11} (hp : v ∉ p.vertices)
    (hq : v ∉ q.vertices) (h : insert v p.vertices = insert v q.vertices) : p = q := by
  have herase : (insert v p.vertices).erase v = (insert v q.vertices).erase v :=
    congrArg (fun s => Finset.erase s v) h
  rw [Finset.erase_insert hp, Finset.erase_insert hq] at herase
  exact Edge11.vertices_injective herase

/-- Every triple through `v` is named by an edge off `v`. -/
theorem exists_edge_insert_eq {v : Fin 11} {T : Finset (Fin 11)} (hT : T ∈ triples)
    (hv : v ∈ T) : ∃ p : Edge11, v ∉ p.vertices ∧ insert v p.vertices = T := by
  have hcard : (T.erase v).card = 2 := by
    rw [Finset.card_erase_of_mem hv, mem_triples.mp hT]
  obtain ⟨p, hp⟩ := Edge11.exists_vertices_eq hcard
  refine ⟨p, ?_, ?_⟩
  · rw [hp]
    exact Finset.notMem_erase v T
  · rw [hp, Finset.insert_erase hv]

/-- **The local naming bijection.**  Counting the triples through `v` with a
property is the same as counting the edges of `K₁₁ − v` that name them. -/
theorem card_filter_off_insert (v : Fin 11) (Q : Finset (Fin 11) → Prop)
    [DecidablePred Q] :
    ((Edge11.off v).filter fun p => Q (insert v p.vertices)).card =
      ((triplesAt v).filter Q).card := by
  refine Finset.card_bij (fun p _ => insert v p.vertices) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp
    exact Finset.mem_filter.mpr ⟨mem_triplesAt.mpr
      ⟨mem_triples_insert (Edge11.mem_off.mp hp.1), Finset.mem_insert_self _ _⟩, hp.2⟩
  · intro p hp q hq hEq
    rw [Finset.mem_filter] at hp hq
    exact edge_of_insert_vertices_eq (Edge11.mem_off.mp hp.1) (Edge11.mem_off.mp hq.1) hEq
  · intro T hT
    obtain ⟨hTat, hQ⟩ := Finset.mem_filter.mp hT
    obtain ⟨hTt, hTv⟩ := mem_triplesAt.mp hTat
    obtain ⟨p, hvp, hpT⟩ := exists_edge_insert_eq hTt hTv
    refine ⟨p, Finset.mem_filter.mpr ⟨Edge11.mem_off.mpr hvp, ?_⟩, hpT⟩
    rw [hpT]
    exact hQ

namespace GlobalDesign

variable (G : GlobalDesign)

/-! ### The `45` blocks through a vertex -/

/-- The block of the local design at `v` named by an edge `p` of `K₁₁ − v`: the
global block of the triple `{v} ∪ p`. -/
def localBlock (v : Fin 11) (p : Edge11) : Finset Edge11 := G.block (insert v p.vertices)

/-- Every block through `v` lives on the edges of `K₁₁ − v`. -/
theorem localBlock_subset {v : Fin 11} {p : Edge11} (hp : p ∈ Edge11.off v) :
    G.localBlock v p ⊆ Edge11.off v :=
  G.block_subset_off (mem_triples_insert (Edge11.mem_off.mp hp))
    (Finset.mem_insert_self _ _)

/-- Every block through `v` has `12` edges. -/
theorem card_localBlock {v : Fin 11} {p : Edge11} (hp : p ∈ Edge11.off v) :
    (G.localBlock v p).card = 12 :=
  G.block_card _ (mem_triples_insert (Edge11.mem_off.mp hp))

/-- Two distinct blocks through `v` meet in exactly `3` edges: their triples
share the vertex `v`, so `GlobalDesign.meet_of_shared` applies. -/
theorem card_localBlock_inter {v : Fin 11} {p q : Edge11} (hp : p ∈ Edge11.off v)
    (hq : q ∈ Edge11.off v) (hpq : p ≠ q) :
    (G.localBlock v p ∩ G.localBlock v q).card = 3 := by
  refine G.meet_of_shared _ (mem_triples_insert (Edge11.mem_off.mp hp)) _
    (mem_triples_insert (Edge11.mem_off.mp hq)) ?_
    ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩⟩
  intro h
  exact hpq (edge_of_insert_vertices_eq (Edge11.mem_off.mp hp) (Edge11.mem_off.mp hq) h)

/-! ### The local replication law -/

/-- Every edge of `K₁₁ − v` lies on
exactly `12` of the `45` blocks named by triples through `v`.

The `45` blocks are `12`-sets inside the `45` edges of `K₁₁ − v`, pairwise
meeting in `3`, so the `45` replication numbers have mean `12` and sum of
squares `6480 = 45 · 144`. -/
theorem card_off_filter_localBlock {v : Fin 11} {e : Edge11} (he : e ∈ Edge11.off v) :
    ((Edge11.off v).filter fun p => e ∈ G.localBlock v p).card = 12 := by
  classical
  have hcard : (Edge11.off v).card = 45 := Edge11.card_off v
  have hsub : ∀ p ∈ Edge11.off v, G.localBlock v p ⊆ Edge11.off v :=
    fun _ hp => G.localBlock_subset hp
  set r : Edge11 → ℕ :=
    fun g => ((Edge11.off v).filter fun p => g ∈ G.localBlock v p).card
  have hsum : (∑ g ∈ Edge11.off v, r g) = 540 := by
    have hstep : (∑ p ∈ Edge11.off v, (Edge11.off v ∩ G.localBlock v p).card) =
        ∑ g ∈ Edge11.off v, r g :=
      sum_inter_card_over (Edge11.off v) (G.localBlock v) (Edge11.off v)
    have hcell : ∀ p ∈ Edge11.off v, (Edge11.off v ∩ G.localBlock v p).card = 12 := by
      intro p hp
      rw [Finset.inter_eq_right.mpr (hsub p hp)]
      exact G.card_localBlock hp
    rw [← hstep, Finset.sum_congr rfl hcell, Finset.sum_const, hcard]
    simp
  have hsq : (∑ g ∈ Edge11.off v, r g ^ 2) = 6480 := by
    have hstep : (∑ g ∈ Edge11.off v, r g ^ 2) =
        ∑ m ∈ Edge11.off v, ∑ n ∈ Edge11.off v,
          (G.localBlock v m ∩ G.localBlock v n).card :=
      sum_card_filter_sq (Edge11.off v) (G.localBlock v) (Edge11.off v) hsub
    have hcell : ∀ m ∈ Edge11.off v,
        (∑ n ∈ Edge11.off v, (G.localBlock v m ∩ G.localBlock v n).card) = 144 := by
      intro m hm
      have hdiag : (G.localBlock v m ∩ G.localBlock v m).card = 12 := by
        rw [Finset.inter_self]
        exact G.card_localBlock hm
      have hsplit := Finset.sum_erase_add (Edge11.off v)
        (fun k => (G.localBlock v m ∩ G.localBlock v k).card) hm
      have hoff : (∑ k ∈ (Edge11.off v).erase m,
          (G.localBlock v m ∩ G.localBlock v k).card) = 132 := by
        have hval : ∀ k ∈ (Edge11.off v).erase m,
            (G.localBlock v m ∩ G.localBlock v k).card = 3 := by
          intro k hk
          exact G.card_localBlock_inter hm (Finset.mem_of_mem_erase hk)
            (Ne.symm (Finset.mem_erase.mp hk).1)
        rw [Finset.sum_congr rfl hval, Finset.sum_const,
          Finset.card_erase_of_mem hm, hcard]
        simp
      omega
    rw [hstep, Finset.sum_congr rfl hcell, Finset.sum_const, hcard]
    simp
  have hle : ∀ g ∈ Edge11.off v, 2 * 12 * r g ≤ r g ^ 2 + 12 ^ 2 :=
    fun g _ => two_mul_mul_le_sq_add_sq 12 (r g)
  have heq : (∑ g ∈ Edge11.off v, 2 * 12 * r g) =
      ∑ g ∈ Edge11.off v, (r g ^ 2 + 12 ^ 2) := by
    rw [← Finset.mul_sum, hsum, Finset.sum_add_distrib, hsq, Finset.sum_const, hcard]
    simp
  exact eq_of_two_mul_mul_eq ((Finset.sum_eq_sum_iff_of_le hle).mp heq e he)

/-! ### The local pair multiplicity -/

/-- Two distinct edges of `K₁₁ − v` lie
on exactly `3` of the `45` blocks named by triples through `v`.

This refines the axiom `SRG266.QuasiSymmetric.GlobalDesign.pair_mult`, which
counts the blocks through two edges only in total: summing this law over the
vertices off both edges recovers it. -/
theorem card_off_filter_localBlock_pair {v : Fin 11} {e f : Edge11}
    (he : e ∈ Edge11.off v) (hf : f ∈ Edge11.off v) (hef : e ≠ f) :
    ((Edge11.off v).filter fun p =>
      e ∈ G.localBlock v p ∧ f ∈ G.localBlock v p).card = 3 := by
  classical
  have hcard : (Edge11.off v).card = 45 := Edge11.card_off v
  set Ie : Finset Edge11 := (Edge11.off v).filter fun p => e ∈ G.localBlock v p with hIe
  have hIesub : Ie ⊆ Edge11.off v := Finset.filter_subset _ _
  have hIecard : Ie.card = 12 := G.card_off_filter_localBlock he
  have hsub : ∀ p ∈ Ie, G.localBlock v p ⊆ Edge11.off v :=
    fun _ hp => G.localBlock_subset (hIesub hp)
  set r : Edge11 → ℕ := fun g => (Ie.filter fun p => g ∈ G.localBlock v p).card
  have hsum : (∑ g ∈ Edge11.off v, r g) = 144 := by
    have hstep : (∑ p ∈ Ie, (Edge11.off v ∩ G.localBlock v p).card) =
        ∑ g ∈ Edge11.off v, r g :=
      sum_inter_card_over Ie (G.localBlock v) (Edge11.off v)
    have hcell : ∀ p ∈ Ie, (Edge11.off v ∩ G.localBlock v p).card = 12 := by
      intro p hp
      rw [Finset.inter_eq_right.mpr (hsub p hp)]
      exact G.card_localBlock (hIesub hp)
    rw [← hstep, Finset.sum_congr rfl hcell, Finset.sum_const, hIecard]
    simp
  have hsq : (∑ g ∈ Edge11.off v, r g ^ 2) = 540 := by
    have hstep : (∑ g ∈ Edge11.off v, r g ^ 2) =
        ∑ m ∈ Ie, ∑ n ∈ Ie, (G.localBlock v m ∩ G.localBlock v n).card :=
      sum_card_filter_sq Ie (G.localBlock v) (Edge11.off v) hsub
    have hcell : ∀ m ∈ Ie,
        (∑ n ∈ Ie, (G.localBlock v m ∩ G.localBlock v n).card) = 45 := by
      intro m hm
      have hdiag : (G.localBlock v m ∩ G.localBlock v m).card = 12 := by
        rw [Finset.inter_self]
        exact G.card_localBlock (hIesub hm)
      have hsplit := Finset.sum_erase_add Ie
        (fun k => (G.localBlock v m ∩ G.localBlock v k).card) hm
      have hoff : (∑ k ∈ Ie.erase m,
          (G.localBlock v m ∩ G.localBlock v k).card) = 33 := by
        have hval : ∀ k ∈ Ie.erase m,
            (G.localBlock v m ∩ G.localBlock v k).card = 3 := by
          intro k hk
          exact G.card_localBlock_inter (hIesub hm)
            (hIesub (Finset.mem_of_mem_erase hk))
            (Ne.symm (Finset.mem_erase.mp hk).1)
        rw [Finset.sum_congr rfl hval, Finset.sum_const,
          Finset.card_erase_of_mem hm, hIecard]
        simp
      omega
    rw [hstep, Finset.sum_congr rfl hcell, Finset.sum_const, hIecard]
    simp
  -- split off the diagonal edge `e`
  have hre : r e = 12 := by
    have hself : (Ie.filter fun p => e ∈ G.localBlock v p) = Ie := by
      refine Finset.filter_true_of_mem fun p hp => ?_
      rw [hIe] at hp
      exact (Finset.mem_filter.mp hp).2
    show (Ie.filter fun p => e ∈ G.localBlock v p).card = 12
    rw [hself, hIecard]
  have hcarderase : ((Edge11.off v).erase e).card = 44 := by
    rw [Finset.card_erase_of_mem he, hcard]
  have hsumerase : (∑ g ∈ (Edge11.off v).erase e, r g) = 132 := by
    have h := Finset.sum_erase_add (Edge11.off v) r he
    omega
  have hsqerase : (∑ g ∈ (Edge11.off v).erase e, r g ^ 2) = 396 := by
    have h := Finset.sum_erase_add (Edge11.off v) (fun g => r g ^ 2) he
    rw [hre] at h
    omega
  -- zero variance about the mean `3`
  have hle : ∀ g ∈ (Edge11.off v).erase e, 2 * 3 * r g ≤ r g ^ 2 + 3 ^ 2 :=
    fun g _ => two_mul_mul_le_sq_add_sq 3 (r g)
  have heq : (∑ g ∈ (Edge11.off v).erase e, 2 * 3 * r g) =
      ∑ g ∈ (Edge11.off v).erase e, (r g ^ 2 + 3 ^ 2) := by
    rw [← Finset.mul_sum, hsumerase, Finset.sum_add_distrib, hsqerase, Finset.sum_const,
      hcarderase]
    simp
  have hval : r f = 3 := eq_of_two_mul_mul_eq ((Finset.sum_eq_sum_iff_of_le hle).mp heq f
    (Finset.mem_erase.mpr ⟨Ne.symm hef, hf⟩))
  have hset : (Ie.filter fun p => f ∈ G.localBlock v p) =
      (Edge11.off v).filter fun p =>
        e ∈ G.localBlock v p ∧ f ∈ G.localBlock v p := by
    rw [hIe, Finset.filter_filter]
  rw [← hset]
  exact hval

/-! ### The blocks through a point of the local design -/

/-- **The local star law.**  For an edge `e` of `K₁₁ − v` and a vertex `u`
distinct from `v` and off `e`, exactly `3` of the `45` blocks through `v` contain
`e` and are named by an edge through `u`.

This is `SRG266.QuasiSymmetric.GlobalDesign.card_triplesThrough_filter` — the
pair replication law of `SRG266/QuasiSymmetric/GlobalDesignLaws.lean` — read
through the local naming bijection. -/
theorem card_off_filter_localBlock_star {v : Fin 11} {e : Edge11}
    (he : e ∈ Edge11.off v) {u : Fin 11} (huv : u ≠ v) (hue : u ∉ e.vertices) :
    ((Edge11.off v).filter fun p =>
      u ∈ p.vertices ∧ e ∈ G.localBlock v p).card = 3 := by
  classical
  have hpred : ((Edge11.off v).filter fun p => u ∈ p.vertices ∧ e ∈ G.localBlock v p) =
      (Edge11.off v).filter fun p =>
        (fun T => u ∈ T ∧ e ∈ G.block T) (insert v p.vertices) := by
    refine Finset.filter_congr fun p _ => ?_
    have hmem : u ∈ insert v p.vertices ↔ u ∈ p.vertices := by
      simp [Finset.mem_insert, huv]
    rw [localBlock]
    exact and_congr_left fun _ => hmem.symm
  have hbij := card_filter_off_insert v fun T => u ∈ T ∧ e ∈ G.block T
  have hset : ((triplesAt v).filter fun T => u ∈ T ∧ e ∈ G.block T) =
      (triplesThrough v u).filter fun T => e ∈ G.block T := by
    ext T
    simp only [Finset.mem_filter, mem_triplesAt, mem_triplesThrough]
    tauto
  rw [hpred, hbij, hset]
  exact G.card_triplesThrough_filter (Ne.symm huv)
    (Edge11.mem_off₂.mpr ⟨Edge11.mem_off.mp he, hue⟩)

/-! ### The local design at a vertex -/

/-- **Every global design contains eleven local designs.**

For each vertex `v` the `45` blocks of a `SRG266.QuasiSymmetric.GlobalDesign`
whose triples contain `v`, named by the `45` edges of `K₁₁ − v` they omit, form a
`SRG266.QuasiSymmetric.LocalDesign v`.  Five of the nine axioms are immediate
from the global ones; `point_rep` is
(`SRG266.QuasiSymmetric.GlobalDesign.card_off_filter_localBlock`), `point_pair`
is `GlobalDesign.card_off_filter_localBlock_pair` and `point_star` is the
pair replication law `GlobalDesign.card_triplesThrough_filter` of
`SRG266/QuasiSymmetric/GlobalDesignLaws.lean`. -/
def toLocalDesign (v : Fin 11) : LocalDesign v where
  block := G.localBlock v
  block_subset := fun _ hp => G.localBlock_subset hp
  block_card := fun _ hp => G.card_localBlock hp
  block_isolates := fun _ hp x hx =>
    G.block_isolates _ (mem_triples_insert (Edge11.mem_off.mp hp)) x
      (Finset.mem_insert_of_mem hx)
  block_cubic := by
    intro p hp x hxv hxp
    refine G.block_cubic _ (mem_triples_insert (Edge11.mem_off.mp hp)) x ?_
    rw [Finset.mem_insert]
    rintro (rfl | hmem)
    · exact hxv rfl
    · exact hxp hmem
  block_meet := fun _ hp _ hq hpq => G.card_localBlock_inter hp hq hpq
  point_rep := fun _ he => G.card_off_filter_localBlock he
  point_pair := fun _ he _ hf hef => G.card_off_filter_localBlock_pair he hf hef
  point_star := fun _ he _ huv hue => G.card_off_filter_localBlock_star he huv hue

@[simp] theorem block_toLocalDesign (v : Fin 11) (p : Edge11) :
    (G.toLocalDesign v).block p = G.localBlock v p := rfl

end GlobalDesign

/-- **The local reduction is at least as strong as the global one.**  If the
local design at a single vertex does not exist, then neither does the global
design.

Together with
`SRG266.QuasiSymmetric.noResidualCherryCover_of_isEmpty_globalDesign` this makes
precise the remark in the module docstring of
`SRG266/QuasiSymmetric/GlobalDesign.lean`: `IsEmpty (LocalDesign v)` refutes an
object of which a `GlobalDesign` contains eleven copies, so
`IsEmpty GlobalDesign` is the weaker hypothesis. -/
theorem isEmpty_globalDesign_of_isEmpty_localDesign {v : Fin 11}
    (h : IsEmpty (LocalDesign v)) : IsEmpty GlobalDesign :=
  ⟨fun G => h.elim (G.toLocalDesign v)⟩

end SRG266.QuasiSymmetric
