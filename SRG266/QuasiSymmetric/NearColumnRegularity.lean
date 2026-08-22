/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.GlobalDesignLocal
import SRG266.QuasiSymmetric.NonTwoK4Root

/-!
# Regularity of the transposed near columns

Fix a root block `B T`, an edge `e` outside that block, and a vertex `a`
outside both `T` and `e`.  Among the twenty-four blocks disjoint from `B T`,
exactly three both contain `e` and are named by a triple containing `a`.

This is the nine-term column identity used by the fractional near-frame
obstruction.  Its proof is purely intrinsic.  At `a`, the forty-five blocks
form the symmetric `2-(45,12,3)` local design.  The root block has nine edges
off `a`; each of those nine edges occurs together with `e` in three local
blocks.  Hence the twelve local blocks through `e` have total intersection
`27` with the root block.  Their intersections are zero or three, so exactly
three of them are disjoint from the root block.

The final structure in this file records the identity while retaining the
non-`2K4` root chosen in `NonTwoK4Root.lean`.  It is extracted directly from a
`GlobalDesign`; the weaker `RootedCubicLift` interface is not enlarged.
-/

namespace SRG266.QuasiSymmetric

open scoped BigOperators

namespace GlobalDesign

variable (G : GlobalDesign)

/-- Twelve triples through `a` have blocks containing an edge which avoids
`a`.  This is local-design point replication, transported through the canonical
edge/triple naming bijection. -/
theorem card_triplesAt_filter_mem_block {a : Fin 11} {e : Edge11}
    (he : e ∈ Edge11.off a) :
    ((triplesAt a).filter fun U => e ∈ G.block U).card = 12 := by
  rw [← card_filter_off_insert a (fun U => e ∈ G.block U)]
  simpa only [GlobalDesign.localBlock] using G.card_off_filter_localBlock he

/-- Three triples through `a` have blocks containing two prescribed distinct
edges which both avoid `a`. -/
theorem card_triplesAt_filter_mem_block_pair {a : Fin 11} {e f : Edge11}
    (he : e ∈ Edge11.off a) (hf : f ∈ Edge11.off a) (hef : e ≠ f) :
    ((triplesAt a).filter fun U => e ∈ G.block U ∧ f ∈ G.block U).card = 3 := by
  rw [← card_filter_off_insert a
    (fun U => e ∈ G.block U ∧ f ∈ G.block U)]
  simpa only [GlobalDesign.localBlock] using
    G.card_off_filter_localBlock_pair he hf hef

/-- The root cubic graph has nine edges avoiding any fixed active vertex. -/
theorem card_block_filter_not_mem_vertices {T : Finset (Fin 11)}
    (hT : T ∈ triples) {a : Fin 11} (haT : a ∉ T) :
    ((G.block T).filter fun f => a ∉ f.vertices).card = 9 := by
  have hdegree : ((G.block T).filter fun f => a ∈ f.vertices).card = 3 := by
    simpa only [arcDegree] using G.block_cubic T hT a haT
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := G.block T) (p := fun f => a ∈ f.vertices)
  rw [hdegree, G.block_card T hT] at hsplit
  omega

/-- The twelve local blocks through `e` have total intersection `27` with a
root block which misses `e`, provided the local centre avoids both objects. -/
theorem sum_root_meet_over_triplesAt_filter_mem_block
    {T : Finset (Fin 11)} (hT : T ∈ triples) {a : Fin 11} (haT : a ∉ T)
    {e : Edge11} (hae : a ∉ e.vertices) (heT : e ∉ G.block T) :
    (∑ U ∈ (triplesAt a).filter fun U => e ∈ G.block U,
      (G.block T ∩ G.block U).card) = 27 := by
  classical
  let S := (triplesAt a).filter fun U => e ∈ G.block U
  have hdouble := sum_inter_card_over S G.block (G.block T)
  have hcell : ∀ f ∈ G.block T,
      (S.filter fun U => f ∈ G.block U).card =
        if a ∈ f.vertices then 0 else 3 := by
    intro f hf
    by_cases hfa : a ∈ f.vertices
    · rw [if_pos hfa, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro U hU hfU
      have hUt : U ∈ triples := (mem_triplesAt.mp
        (Finset.mem_filter.mp hU).1).1
      have haU : a ∈ U := (mem_triplesAt.mp
        (Finset.mem_filter.mp hU).1).2
      exact G.notMem_vertices_of_mem_block hUt hfU haU hfa
    · rw [if_neg hfa]
      have heOff : e ∈ Edge11.off a := Edge11.mem_off.mpr hae
      have hfOff : f ∈ Edge11.off a := Edge11.mem_off.mpr hfa
      have hef : e ≠ f := fun h => heT (h ▸ hf)
      have hpair := G.card_triplesAt_filter_mem_block_pair heOff hfOff hef
      have hset : S.filter (fun U => f ∈ G.block U) =
          (triplesAt a).filter fun U => e ∈ G.block U ∧ f ∈ G.block U := by
        ext U
        simp only [S, Finset.mem_filter]
        tauto
      rw [hset, hpair]
  rw [hdouble, Finset.sum_congr rfl hcell]
  calc
    (∑ f ∈ G.block T, if a ∈ f.vertices then 0 else 3) =
        ∑ f ∈ G.block T, 3 * if a ∉ f.vertices then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro f _
          by_cases hfa : a ∈ f.vertices <;> simp [hfa]
    _ = 3 * ∑ f ∈ G.block T, if a ∉ f.vertices then 1 else 0 := by
          rw [Finset.mul_sum]
    _ = 3 * ((G.block T).filter fun f => a ∉ f.vertices).card := by
          rw [Finset.sum_boole]
          norm_cast
    _ = 27 := by rw [G.card_block_filter_not_mem_vertices hT haT]

/-- **Near-column regularity.**  For a root triple `T`, an edge `e` outside
its block, and a vertex `a` outside both `T` and `e`, precisely three members
of the near family contain `a` and have blocks containing `e`. -/
theorem card_disjointFrom_inter_triplesAt_filter_mem_block
    {T : Finset (Fin 11)} (hT : T ∈ triples) {a : Fin 11} (haT : a ∉ T)
    {e : Edge11} (hae : a ∉ e.vertices) (heT : e ∉ G.block T) :
    (((G.disjointFrom T ∩ triplesAt a).filter fun U => e ∈ G.block U).card) = 3 := by
  classical
  let S := (triplesAt a).filter fun U => e ∈ G.block U
  have hScard : S.card = 12 := G.card_triplesAt_filter_mem_block
    (Edge11.mem_off.mpr hae)
  have hsum : (∑ U ∈ S, (G.block T ∩ G.block U).card) = 27 := by
    simpa only [S] using
      G.sum_root_meet_over_triplesAt_filter_mem_block hT haT hae heT
  have hcases : ∀ U ∈ S,
      (G.block T ∩ G.block U).card = 0 ∨
        (G.block T ∩ G.block U).card = 3 := by
    intro U hU
    have hUa : U ∈ triplesAt a := (Finset.mem_filter.mp hU).1
    have hUt : U ∈ triples := (mem_triplesAt.mp hUa).1
    have hTU : T ≠ U := by
      intro h
      exact haT (h ▸ (mem_triplesAt.mp hUa).2)
    exact G.block_meet T hT U hUt hTU
  have hcount := sum_add_mul_card_filter_eq 3 S
    (fun U => (G.block T ∩ G.block U).card) hcases
  have hset : (S.filter fun U => (G.block T ∩ G.block U).card = 0) =
      (G.disjointFrom T ∩ triplesAt a).filter fun U => e ∈ G.block U := by
    ext U
    simp only [S, Finset.mem_filter, Finset.mem_inter, G.mem_disjointFrom]
    constructor
    · rintro ⟨⟨hUa, heU⟩, hzero⟩
      exact ⟨⟨⟨(mem_triplesAt.mp hUa).1, hzero⟩, hUa⟩, heU⟩
    · rintro ⟨⟨⟨-, hzero⟩, hUa⟩, heU⟩
      exact ⟨⟨hUa, heU⟩, hzero⟩
  rw [hsum, hScard, hset] at hcount
  omega

end GlobalDesign

/-- A non-`2K4` rooted lift carrying the exact regularity of every transposed
edge column.  The hypotheses say that `a` is active and is not an endpoint of
`e`; root-block edges are excluded because their columns are empty. -/
structure RegularNonTwoK4RootedCubicLift extends NonTwoK4RootedCubicLift where
  near_column_point_degree : ∀ {a : Fin 11}, a ∉ root → ∀ {e : Edge11},
    a ∉ e.vertices → e ∉ block root →
    (((near ∩ triplesAt a).filter fun U => e ∈ block U).card) = 3

/-- Existence of the regular non-`2K4` rooted lift. -/
abbrev IsRegularNonTwoK4RootedCubicLift : Prop :=
  Nonempty RegularNonTwoK4RootedCubicLift

/-- The finite obstruction which the fractional certificate layer refutes. -/
abbrev NoRegularNonTwoK4RootedCubicLift : Prop :=
  IsEmpty RegularNonTwoK4RootedCubicLift

namespace GlobalDesign

/-- Root a global design at any specified non-`2K4` triple and retain the
regular transposed-column law. -/
noncomputable def toRegularNonTwoK4RootedCubicLiftAt
    (G : GlobalDesign) (T : Finset (Fin 11)) (hT : T ∈ triples)
    (hnot : ¬ IsTwoK4 T (G.block T)) :
    RegularNonTwoK4RootedCubicLift := by
  let R : NonTwoK4RootedCubicLift :=
    { G.toRootedCubicLift T hT with root_not_twoK4 := hnot }
  exact
    { R with
      near_column_point_degree := by
        intro a ha e hae heRoot
        exact G.card_disjointFrom_inter_triplesAt_filter_mem_block
          hT ha hae heRoot }

/-- Every global design admits a non-`2K4` root whose edge columns satisfy the
exact local point-degree-three law. -/
noncomputable def toRegularNonTwoK4RootedCubicLift
    (G : GlobalDesign) : RegularNonTwoK4RootedCubicLift := by
  let R := G.toNonTwoK4RootedCubicLift
  exact G.toRegularNonTwoK4RootedCubicLiftAt R.root R.root_triple
    R.root_not_twoK4

end GlobalDesign

/-- Refuting regular non-`2K4` rooted lifts refutes every global design. -/
theorem isEmpty_globalDesign_of_noRegularNonTwoK4RootedCubicLift
    (h : NoRegularNonTwoK4RootedCubicLift) : IsEmpty GlobalDesign :=
  ⟨fun G => h.elim G.toRegularNonTwoK4RootedCubicLift⟩

/-- The regular-column obstruction discharges the unique residual boundary. -/
theorem noResidualCherryCover_of_noRegularNonTwoK4RootedCubicLift
    (h : NoRegularNonTwoK4RootedCubicLift) : NoResidualCherryCover :=
  noResidualCherryCover_of_isEmpty_globalDesign
    (isEmpty_globalDesign_of_noRegularNonTwoK4RootedCubicLift h)

end SRG266.QuasiSymmetric
