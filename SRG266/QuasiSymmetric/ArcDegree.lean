/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.K11

/-!
# The `{12;3}`-arc lemma

Fix a `SRG266.QuasiSymmetric.CherryCover` `C` of `K₁₁` and a set `T` of `12`
edges meeting every member of `C` in `0` or `3` edges — the shape that a
residual block of a hypothetical quasi-symmetric `2-(56, 12, 9)` design takes
in the `K₁₁` coordinates.  Then

> **`arc_is_cubic_on_eight`** — `T` is a cubic graph on exactly `8` of the `11`
> vertices: three vertices are isolated and the other eight have degree `3`.

The proof is uniform in the cover and uses no finite certificate.

## Method

The design derives the congruence inside `F₃⁵⁵`, by exhibiting `2 s_v + 𝟙` in
the span of the members of the cover.  No linear algebra is needed.  Everything
follows from `CherryCover.pairCount_add_vmeet`, i.e.

`#{i | e, f ∈ C.g i} + #(common endpoints of e and f) = 2 + 9·[e = f]`,

used twice:

* summed over `f ∈ T` for a fixed edge `e = {v, a}` it says
  `∑_{i ∋ e} |T ∩ C.g i| + (deg v + deg a) = 24 + 9·[e ∈ T]`, and the left sum
  is a sum of `0`s and `3`s, so `3 ∣ deg v + deg a` for *every* edge
  (`arc_degree_pair_dvd`); comparing three vertices gives `3 ∣ deg v`
  (`arc_degree_dvd_three`);
* summed over `e, f ∈ T` it gives `∑_v (deg v)² = 396 − 324 = 72`, which with
  `∑_v deg v = 24` and `3 ∣ deg v` forces every degree into `{0, 3}`.
-/

open scoped BigOperators

namespace SRG266.QuasiSymmetric

/-- The degree of a set of edges of `K₁₁` at a vertex. -/
def arcDegree (T : Finset Edge11) (v : Fin 11) : ℕ :=
  (T.filter fun e => v ∈ e.vertices).card

/-- **The arc hypothesis.**  A `{12; 3}`-arc of a cherry cover: `12` edges of
`K₁₁` meeting every member of the cover in `0` or `3` edges. -/
structure IsArc (C : CherryCover) (T : Finset Edge11) : Prop where
  /-- The arc has `12` edges. -/
  card : T.card = 12
  /-- The arc meets every member of the cover in `0` or `3` edges. -/
  meet : ∀ i, ((T ∩ C.g i).card = 0) ∨ ((T ∩ C.g i).card = 3)

/-! ### Elementary double counts -/

/-- The degrees of a set of edges sum to twice its size. -/
theorem sum_arcDegree (T : Finset Edge11) :
    (∑ v : Fin 11, arcDegree T v) = 2 * T.card := by
  have h := Edge11.sum_star_card T
  rw [Finset.sum_congr rfl fun e _ => Edge11.card_vertices e, Finset.sum_const,
    smul_eq_mul] at h
  rw [show (∑ v : Fin 11, arcDegree T v) =
    ∑ v : Fin 11, (T.filter fun e => v ∈ e.vertices).card from rfl, h]
  ring

/-- The sum of the squared degrees counts the ordered pairs of edges through a
common vertex. -/
theorem sum_arcDegree_sq (T : Finset Edge11) :
    (∑ v : Fin 11, arcDegree T v ^ 2) = ∑ e ∈ T, ∑ f ∈ T, Edge11.vmeet e f :=
  (Edge11.sum_vmeet T).symm

/-- The common endpoints of a fixed edge with the members of `T`, summed, are
the degrees of `T` at the two endpoints. -/
theorem sum_vmeet_left (e : Edge11) (T : Finset Edge11) :
    (∑ f ∈ T, Edge11.vmeet e f) = ∑ w ∈ e.vertices, arcDegree T w := by
  classical
  have hl : ∀ f : Edge11, Edge11.vmeet e f =
      ∑ w ∈ e.vertices, if w ∈ f.vertices then 1 else 0 := by
    intro f
    rw [Edge11.vmeet, ← Finset.filter_mem_eq_inter, Finset.card_filter]
  have hr : ∀ w : Fin 11, arcDegree T w = ∑ f ∈ T, if w ∈ f.vertices then 1 else 0 := by
    intro w
    rw [arcDegree, Finset.card_filter]
  rw [Finset.sum_congr rfl fun f _ => hl f, Finset.sum_congr rfl fun w _ => hr w,
    Finset.sum_comm]

/-- Every vertex of `K₁₁` has two other vertices distinct from it and from each
other. -/
theorem exists_two_ne (v : Fin 11) : ∃ a b : Fin 11, a ≠ v ∧ b ≠ v ∧ a ≠ b := by
  have hlt : 1 < ((Finset.univ : Finset (Fin 11)).erase v).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
    norm_num
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlt
  exact ⟨a, b, (Finset.mem_erase.mp ha).1, (Finset.mem_erase.mp hb).1, hab⟩

/-! ### The two arc identities -/

namespace IsArc

variable {C : CherryCover} {T : Finset Edge11}

/-- An arc meets the members of the cover in `108 = 12 · 9` edges in total. -/
theorem sum_inter (h : IsArc C T) : (∑ i, (T ∩ C.g i).card) = 108 := by
  have hcount := sum_inter_card C.g T
  have hstar : ∀ e ∈ T, (starFinset C.g e).card = 9 := by
    intro e _
    rw [← pairCount_self, C.edge_rep e]
  rw [Finset.sum_congr rfl hstar, Finset.sum_const, h.card] at hcount
  simpa using hcount

/-- The squared traces of an arc sum to `324 = 3 · 108`, because each trace is
`0` or `3`. -/
theorem sum_inter_sq (h : IsArc C T) : (∑ i, (T ∩ C.g i).card ^ 2) = 324 := by
  have hsq : ∀ i : Fin 45, (T ∩ C.g i).card ^ 2 = 3 * (T ∩ C.g i).card := by
    intro i
    rcases h.meet i with h' | h' <;> simp [h']
  rw [Finset.sum_congr rfl fun i _ => hsq i, ← Finset.mul_sum, h.sum_inter]
  norm_num

/-- The pair counts of an arc against itself sum to `324`. -/
theorem sum_pairCount (h : IsArc C T) :
    (∑ e ∈ T, ∑ f ∈ T, pairCount C.g e f) = 324 := by
  rw [← sum_inter_card_sq C.g T, h.sum_inter_sq]

/-- **The squared-degree identity.**  `∑_v (deg v)² = 396 − 324 = 72`. -/
theorem sum_arcDegree_sq_eq (h : IsArc C T) :
    (∑ v : Fin 11, arcDegree T v ^ 2) = 72 := by
  classical
  -- the combined sum is `2 · 12² + 9 · 12 = 396`
  have hcomb : (∑ e ∈ T, ∑ f ∈ T, (pairCount C.g e f + Edge11.vmeet e f)) = 396 := by
    have hcell : ∀ e ∈ T,
        (∑ f ∈ T, (pairCount C.g e f + Edge11.vmeet e f)) = 33 := by
      intro e he
      rw [Finset.sum_congr rfl fun f _ => C.pairCount_add_vmeet e f,
        Finset.sum_add_distrib, Finset.sum_const, h.card,
        Finset.sum_ite_eq T e (fun _ => 9), if_pos he]
      norm_num
    rw [Finset.sum_congr rfl hcell, Finset.sum_const, h.card]
    norm_num
  have hsplit : (∑ e ∈ T, ∑ f ∈ T, (pairCount C.g e f + Edge11.vmeet e f)) =
      (∑ e ∈ T, ∑ f ∈ T, pairCount C.g e f) + ∑ e ∈ T, ∑ f ∈ T, Edge11.vmeet e f := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_add_distrib
  rw [hsplit, h.sum_pairCount] at hcomb
  rw [sum_arcDegree_sq T]
  omega

/-- **The degree identity.**  `∑_v deg v = 24`. -/
theorem sum_arcDegree_eq (h : IsArc C T) : (∑ v : Fin 11, arcDegree T v) = 24 := by
  rw [sum_arcDegree T, h.card]

/-! ### The congruence -/

/-- For every edge `{v, a}` of `K₁₁` the two degrees of
an arc at its endpoints sum to a multiple of `3`.

The `9` members of the cover through `{v, a}` meet `T` in `0` or `3` edges, and
the total of those traces is `24 + 9·[{v,a} ∈ T] − (deg v + deg a)`. -/
theorem arc_degree_pair_dvd (h : IsArc C T) {v a : Fin 11} (hva : v ≠ a) :
    3 ∣ (arcDegree T v + arcDegree T a) := by
  classical
  set e : Edge11 := Edge11.mk' hva with he
  have hleft : 3 ∣ ∑ i ∈ starFinset C.g e, (T ∩ C.g i).card := by
    refine Finset.dvd_sum fun i _ => ?_
    rcases h.meet i with h' | h' <;> simp [h']
  rw [sum_star_inter_card C.g e T] at hleft
  have hcomb : (∑ f ∈ T, (pairCount C.g e f + Edge11.vmeet e f)) =
      24 + (if e ∈ T then 9 else 0) := by
    rw [Finset.sum_congr rfl fun f _ => C.pairCount_add_vmeet e f,
      Finset.sum_add_distrib, Finset.sum_const, h.card,
      Finset.sum_ite_eq T e (fun _ => 9)]
    norm_num
  have hsplit : (∑ f ∈ T, (pairCount C.g e f + Edge11.vmeet e f)) =
      (∑ f ∈ T, pairCount C.g e f) + ∑ f ∈ T, Edge11.vmeet e f :=
    Finset.sum_add_distrib
  have hdeg : (∑ f ∈ T, Edge11.vmeet e f) = arcDegree T v + arcDegree T a := by
    rw [sum_vmeet_left e T, he, Edge11.vertices_mk', Finset.sum_pair hva]
  rw [hsplit, hdeg] at hcomb
  have h9 : (3 : ℕ) ∣ (if e ∈ T then 9 else 0) := by
    by_cases hmem : e ∈ T <;> simp [hmem]
  omega

/-- Every degree of an arc is a multiple of `3`.

Comparing the three pairs formed by `v` and two further vertices gives
`3 ∣ 2 · deg v`, hence `3 ∣ deg v`. -/
theorem arc_degree_dvd_three (h : IsArc C T) (v : Fin 11) : 3 ∣ arcDegree T v := by
  obtain ⟨a, b, hav, hbv, hab⟩ := exists_two_ne v
  have h1 := h.arc_degree_pair_dvd (Ne.symm hav)
  have h2 := h.arc_degree_pair_dvd (Ne.symm hbv)
  have h3 := h.arc_degree_pair_dvd hab
  omega

/-- Every degree of an arc is `0` modulo `3`. -/
theorem arc_degree_mod_three (h : IsArc C T) (v : Fin 11) : arcDegree T v % 3 = 0 := by
  have hdvd := h.arc_degree_dvd_three v
  omega

/-! ### The conclusion -/

/-- Every degree of an arc is `0` or `3`. -/
theorem arc_degree_cases (h : IsArc C T) (v : Fin 11) :
    arcDegree T v = 0 ∨ arcDegree T v = 3 := by
  classical
  have hle : ∀ w ∈ (Finset.univ : Finset (Fin 11)),
      3 * arcDegree T w ≤ arcDegree T w ^ 2 := by
    intro w _
    rcases Nat.eq_zero_or_pos (arcDegree T w) with h0 | hpos
    · simp [h0]
    · have h3 : 3 ≤ arcDegree T w := Nat.le_of_dvd hpos (h.arc_degree_dvd_three w)
      rw [sq]
      exact Nat.mul_le_mul_right _ h3
  have heq : (∑ w : Fin 11, 3 * arcDegree T w) = ∑ w : Fin 11, arcDegree T w ^ 2 := by
    rw [← Finset.mul_sum, h.sum_arcDegree_eq, h.sum_arcDegree_sq_eq]
    norm_num
  have hpt := (Finset.sum_eq_sum_iff_of_le hle).mp heq v (Finset.mem_univ v)
  rcases Nat.eq_zero_or_pos (arcDegree T v) with h0 | hpos
  · exact Or.inl h0
  · refine Or.inr ?_
    rw [sq] at hpt
    have h' : arcDegree T v * 3 = arcDegree T v * arcDegree T v := by
      rw [mul_comm]
      exact hpt
    exact (Nat.eq_of_mul_eq_mul_left hpos h').symm

/-- A `{12; 3}`-arc of a cherry cover is a cubic graph on
exactly `8` of the `11` vertices: eight vertices have degree `3` and the other
three are isolated. -/
theorem arc_is_cubic_on_eight (h : IsArc C T) :
    (Finset.univ.filter fun v => arcDegree T v ≠ 0).card = 8 ∧
      ∀ v, arcDegree T v ≠ 0 → arcDegree T v = 3 := by
  classical
  have hthree : ∀ v, arcDegree T v ≠ 0 → arcDegree T v = 3 := fun v hv =>
    (h.arc_degree_cases v).resolve_left hv
  refine ⟨?_, hthree⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin 11))
    (fun v => arcDegree T v ≠ 0) (fun v => arcDegree T v)
  have hpos : (∑ v ∈ Finset.univ.filter fun v => arcDegree T v ≠ 0, arcDegree T v) =
      3 * (Finset.univ.filter fun v => arcDegree T v ≠ 0).card := by
    rw [Finset.sum_congr rfl fun v hv => hthree v (Finset.mem_filter.mp hv).2,
      Finset.sum_const, smul_eq_mul]
    ring
  have hzero : (∑ v ∈ Finset.univ.filter fun v => ¬ arcDegree T v ≠ 0, arcDegree T v) = 0 := by
    refine Finset.sum_eq_zero fun v hv => ?_
    simpa using (Finset.mem_filter.mp hv).2
  rw [hpos, hzero, h.sum_arcDegree_eq] at hsplit
  omega

end IsArc

/-! ### Relabelling -/

/-- The degree of a relabelled set of edges at a vertex is the degree of the
original at the preimage vertex. -/
theorem arcDegree_image (σ : Equiv.Perm (Fin 11)) (T : Finset Edge11) (v : Fin 11) :
    arcDegree (T.image (Edge11.map σ)) v = arcDegree T (σ.symm v) := by
  classical
  rw [arcDegree, arcDegree, Finset.filter_image,
    Finset.card_image_of_injective _ (Edge11.map_injective σ)]
  exact congrArg Finset.card (Finset.filter_congr fun _ _ => Edge11.mem_vertices_map)

/-- Relabelling the `11` vertices carries the arcs of a cherry
cover to the arcs of the relabelled cover. -/
theorem IsArc.relabel {C : CherryCover} {T : Finset Edge11} (h : IsArc C T)
    (σ : Equiv.Perm (Fin 11)) : IsArc (C.relabel σ) (T.image (Edge11.map σ)) where
  card := by
    rw [Finset.card_image_of_injective _ (Edge11.map_injective σ), h.card]
  meet := by
    classical
    intro i
    rw [CherryCover.relabel_g, ← Finset.image_inter _ _ (Edge11.map_injective σ),
      Finset.card_image_of_injective _ (Edge11.map_injective σ)]
    exact h.meet i

end SRG266.QuasiSymmetric
