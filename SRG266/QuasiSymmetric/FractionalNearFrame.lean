/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.NearColumnRegularity

/-!
# Fractional near frames

This file transposes the twenty-four cubic rows around a regular non-`2K4`
root into edge columns.  Columns with the same set of active endpoints are
averaged.  The resulting empirical probability distributions form a
`FractionalNearFrame`.

The construction is deliberately independent of normal forms and executable
certificates.  It is the semantic bridge from a hypothetical residual design
to the small rational feasibility problem checked by the certificate layer.
Only pairs of near triples meeting in one point are retained, although the
empirical construction satisfies the concurrence equation for every two
distinct rows.
-/

namespace SRG266.QuasiSymmetric

open scoped BigOperators

namespace RegularNonTwoK4RootedCubicLift

variable (R : RegularNonTwoK4RootedCubicLift)

/-- The inherited twenty-four near rows, exposed at the strengthened
regular-column interface. -/
abbrev NearRow :=
  {U : Finset (Fin 11) // U ∈ R.near}

/-- The inherited eight active vertices. -/
abbrev OffRootVertex :=
  {a : Fin 11 // a ∉ R.root}

/-- The edges outside the root block. -/
def nonRootEdges : Finset Edge11 :=
  Finset.univ.filter fun e => e ∉ R.block R.root

/-- The active endpoints of an edge, viewed as a subset of the eight vertices
outside the root triple. -/
def offRootEndpoints (e : Edge11) : Finset R.OffRootVertex :=
  Finset.univ.filter fun a => (a : Fin 11) ∈ e.vertices

@[simp] theorem mem_offRootEndpoints {a : R.OffRootVertex} {e : Edge11} :
    a ∈ R.offRootEndpoints e ↔ (a : Fin 11) ∈ e.vertices := by
  simp [offRootEndpoints]

/-- The endpoint types which actually occur among non-root edges. -/
def endpointTypes : Finset (Finset R.OffRootVertex) :=
  R.nonRootEdges.image R.offRootEndpoints

/-- One of the endpoint shells used by the fractional relaxation. -/
abbrev EndpointType := {S : Finset R.OffRootVertex // S ∈ R.endpointTypes}

/-- The non-root edges with one prescribed active endpoint set. -/
def edgeClass (E : R.EndpointType) : Finset Edge11 :=
  R.nonRootEdges.filter fun e => R.offRootEndpoints e = E

theorem edgeClass_nonempty (E : R.EndpointType) : (R.edgeClass E).Nonempty := by
  rcases Finset.mem_image.mp E.property with ⟨e, he, hE⟩
  refine ⟨e, Finset.mem_filter.mpr ⟨he, ?_⟩⟩
  exact hE

theorem edgeClass_card_pos (E : R.EndpointType) : 0 < (R.edgeClass E).card :=
  Finset.card_pos.mpr (R.edgeClass_nonempty E)

/-- The column indexed by a non-root edge. -/
def nearColumn (e : Edge11) : Finset (Finset (Fin 11)) :=
  R.near.filter fun U => e ∈ R.block U

/-- Point degree of a column on an active vertex. -/
def nearColumnPointDegree (C : Finset (Finset (Fin 11)))
    (a : R.OffRootVertex) : ℕ :=
  (C ∩ triplesAt a).card

/-- A regular column shell for one endpoint type.  Its elements are precisely
the subsets of the near family which have point degree zero on the endpoints
and point degree three everywhere else. -/
def NearColumnShell (E : R.EndpointType) :=
  {C : Finset (Finset (Fin 11)) //
    C ⊆ R.near ∧ ∀ a : R.OffRootVertex,
      R.nearColumnPointDegree C a = if a ∈ (E : Finset R.OffRootVertex) then 0 else 3}

noncomputable instance (E : R.EndpointType) : Fintype (R.NearColumnShell E) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance (E : R.EndpointType) : DecidableEq (R.NearColumnShell E) :=
  Classical.decEq _

/-- Every actual non-root edge column belongs to the shell determined by its
active endpoints. -/
theorem nearColumn_mem_shell {e : Edge11} (he : e ∈ R.nonRootEdges) :
    R.nearColumn e ⊆ R.near ∧ ∀ a : R.OffRootVertex,
      R.nearColumnPointDegree (R.nearColumn e) a =
        if a ∈ R.offRootEndpoints e then 0 else 3 := by
  classical
  constructor
  · exact Finset.filter_subset _ _
  intro a
  by_cases hae : (a : Fin 11) ∈ e.vertices
  · rw [if_pos (R.mem_offRootEndpoints.mpr hae), nearColumnPointDegree,
      Finset.card_eq_zero]
    refine Finset.eq_empty_of_forall_notMem fun U hU => ?_
    rw [Finset.mem_inter, nearColumn, Finset.mem_filter, mem_triplesAt] at hU
    have hzero := R.near_block_isolates hU.1.1 hU.2.2
    rw [arcDegree, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hzero
    exact hzero hU.1.2 hae
  · rw [if_neg (R.mem_offRootEndpoints.not.mpr hae), nearColumnPointDegree]
    have heRoot : e ∉ R.block R.root := (Finset.mem_filter.mp he).2
    have hregular := R.near_column_point_degree a.property hae heRoot
    have hset : (R.nearColumn e ∩ triplesAt a) =
        ((R.near ∩ triplesAt a).filter fun U => e ∈ R.block U) := by
      ext U
      simp only [nearColumn, Finset.mem_inter, Finset.mem_filter]
      tauto
    rw [hset, hregular]

/-- An edge of a fixed endpoint class, packaged with its membership proof. -/
abbrev ClassEdge (E : R.EndpointType) := {e : Edge11 // e ∈ R.edgeClass E}

/-- The shell element supplied by an actual edge in an endpoint class. -/
noncomputable def shellOfClassEdge (E : R.EndpointType) (e : R.ClassEdge E) :
    R.NearColumnShell E := by
  have heNonRoot : (e : Edge11) ∈ R.nonRootEdges :=
    (Finset.mem_filter.mp e.property).1
  have heEndpoints : R.offRootEndpoints e = (E : Finset R.OffRootVertex) :=
    (Finset.mem_filter.mp e.property).2
  refine ⟨R.nearColumn e, (R.nearColumn_mem_shell heNonRoot).1, ?_⟩
  intro a
  rw [← heEndpoints]
  exact (R.nearColumn_mem_shell heNonRoot).2 a

@[simp] theorem mem_shellOfClassEdge_iff (E : R.EndpointType)
    (e : R.ClassEdge E) (U : R.NearRow) :
    (U : Finset (Fin 11)) ∈ (R.shellOfClassEdge E e : R.NearColumnShell E).1 ↔
      (e : Edge11) ∈ R.block U := by
  simp [shellOfClassEdge, nearColumn, U.property]

/-- Empirical probability mass of one shell column, obtained by uniformly
averaging the actual edges in its endpoint class. -/
noncomputable def empiricalMass (E : R.EndpointType) (C : R.NearColumnShell E) : ℚ :=
  ∑ e : R.ClassEdge E,
    if R.shellOfClassEdge E e = C then ((R.edgeClass E).card : ℚ)⁻¹ else 0

theorem empiricalMass_nonneg (E : R.EndpointType) (C : R.NearColumnShell E) :
    0 ≤ R.empiricalMass E C := by
  classical
  apply Finset.sum_nonneg
  intro e _
  split_ifs
  · exact inv_nonneg.mpr (by positivity)
  · exact le_rfl

/-- Integrating a function against the empirical shell distribution is the
uniform average of that function over the actual edge class. -/
theorem sum_empiricalMass_mul (E : R.EndpointType)
    (g : R.NearColumnShell E → ℚ) :
    (∑ C : R.NearColumnShell E, R.empiricalMass E C * g C) =
      ((R.edgeClass E).card : ℚ)⁻¹ *
        ∑ e : R.ClassEdge E, g (R.shellOfClassEdge E e) := by
  classical
  calc
    (∑ C : R.NearColumnShell E, R.empiricalMass E C * g C) =
        ∑ C : R.NearColumnShell E, ∑ e : R.ClassEdge E,
          (if R.shellOfClassEdge E e = C then
            ((R.edgeClass E).card : ℚ)⁻¹ else 0) * g C := by
          apply Finset.sum_congr rfl
          intro C _
          rw [empiricalMass, Finset.sum_mul]
    _ = ∑ e : R.ClassEdge E, ∑ C : R.NearColumnShell E,
          (if R.shellOfClassEdge E e = C then
            ((R.edgeClass E).card : ℚ)⁻¹ else 0) * g C := by
          rw [Finset.sum_comm]
    _ = ∑ e : R.ClassEdge E,
          ((R.edgeClass E).card : ℚ)⁻¹ * g (R.shellOfClassEdge E e) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [Finset.sum_eq_single (R.shellOfClassEdge E e)]
          · simp
          · intro C _ hC
            simp [Ne.symm hC]
          · simp
    _ = ((R.edgeClass E).card : ℚ)⁻¹ *
          ∑ e : R.ClassEdge E, g (R.shellOfClassEdge E e) := by
          rw [Finset.mul_sum]

theorem sum_empiricalMass (E : R.EndpointType) :
    (∑ C : R.NearColumnShell E, R.empiricalMass E C) = 1 := by
  classical
  have h := R.sum_empiricalMass_mul E (fun _ => 1)
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    nsmul_eq_mul] at h
  rw [h]
  have hne : ((R.edgeClass E).card : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (R.edgeClass_card_pos E))
  exact inv_mul_cancel₀ hne

/-- Indicator that a shell column contains both prescribed near rows. -/
def shellPairIndicator {E : R.EndpointType} (C : R.NearColumnShell E)
    (U V : R.NearRow) : ℚ :=
  if (U : Finset (Fin 11)) ∈ C.1 ∧ (V : Finset (Fin 11)) ∈ C.1 then 1 else 0

/-- Weighted empirical concurrence in one endpoint class is the exact number
of actual class edges lying in both row blocks. -/
theorem card_mul_empiricalPair_eq (E : R.EndpointType) (U V : R.NearRow) :
    ((R.edgeClass E).card : ℚ) *
        (∑ C : R.NearColumnShell E,
          R.empiricalMass E C * R.shellPairIndicator C U V) =
      (((R.edgeClass E).filter fun e =>
        e ∈ R.block U ∧ e ∈ R.block V).card : ℚ) := by
  classical
  rw [R.sum_empiricalMass_mul E (fun C => R.shellPairIndicator C U V)]
  have hne : ((R.edgeClass E).card : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (R.edgeClass_card_pos E))
  rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  let g : Edge11 → ℚ := fun e =>
    if e ∈ R.block U ∧ e ∈ R.block V then 1 else 0
  have hpoint : ∀ e : R.ClassEdge E,
      R.shellPairIndicator (R.shellOfClassEdge E e) U V = g e := by
    intro e
    simp only [shellPairIndicator, R.mem_shellOfClassEdge_iff, g]
  have hattach : (∑ e : R.ClassEdge E, g e) =
      ∑ e ∈ R.edgeClass E, g e := by
    rw [Finset.univ_eq_attach (R.edgeClass E)]
    exact Finset.sum_attach (R.edgeClass E) g
  rw [Finset.sum_congr rfl fun e _ => hpoint e, hattach]
  dsimp only [g]
  rw [Finset.sum_boole]

/-- Regrouping the endpoint classes recovers a sum over all non-root edges. -/
theorem sum_card_edgeClass_filter (p : Edge11 → Prop) [DecidablePred p] :
    (∑ E : R.EndpointType, ((R.edgeClass E).filter p).card) =
      (R.nonRootEdges.filter p).card := by
  classical
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter
    (R.nonRootEdges.filter p) R.endpointTypes R.offRootEndpoints
  let g : Finset R.OffRootVertex → ℕ := fun S =>
    ((R.nonRootEdges.filter fun e => R.offRootEndpoints e = S).filter p).card
  have hattach : (∑ E : R.EndpointType, g E) =
      ∑ S ∈ R.endpointTypes, g S := by
    rw [Finset.univ_eq_attach R.endpointTypes]
    exact Finset.sum_attach R.endpointTypes g
  change (∑ E : R.EndpointType, g E) = _
  rw [hattach]
  have hrange : (R.nonRootEdges.filter p).filter
      (fun e => R.offRootEndpoints e ∈ R.endpointTypes) = R.nonRootEdges.filter p := by
    apply Finset.filter_true_of_mem
    intro e he
    exact Finset.mem_image.mpr ⟨e, (Finset.mem_filter.mp he).1, rfl⟩
  rw [hrange] at hfiber
  simpa only [g, Finset.filter_filter, and_left_comm, and_assoc,
    and_comm] using hfiber

/-- A pair of distinct near rows has exactly three common non-root edges. -/
theorem card_nonRootEdges_filter_pair (U V : R.NearRow) (hUV : U ≠ V) :
    ((R.nonRootEdges.filter fun e => e ∈ R.block U ∧ e ∈ R.block V).card) = 3 := by
  have hset : R.nonRootEdges.filter (fun e => e ∈ R.block U ∧ e ∈ R.block V) =
      R.block U ∩ R.block V := by
    ext e
    simp only [nonRootEdges, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_inter]
    constructor
    · exact fun h => h.2
    · rintro h
      refine ⟨?_, h⟩
      intro heRoot
      have hzero := R.root_near_disjoint U.property
      have hempty : R.block R.root ∩ R.block U = ∅ := Finset.card_eq_zero.mp hzero
      have heBoth : e ∈ R.block R.root ∩ R.block U :=
        Finset.mem_inter.mpr ⟨heRoot, h.1⟩
      rw [hempty] at heBoth
      exact Finset.notMem_empty e heBoth
  rw [hset]
  exact R.near_block_meet U.property V.property
    (fun h => hUV (Subtype.ext h))

end RegularNonTwoK4RootedCubicLift

/-- A rational fractional gluing of all regular endpoint shells. -/
structure FractionalNearFrame (R : RegularNonTwoK4RootedCubicLift) where
  mass : ∀ E : R.EndpointType, R.NearColumnShell E → ℚ
  mass_nonneg : ∀ E C, 0 ≤ mass E C
  mass_normalization : ∀ E, ∑ C, mass E C = 1
  concurrence : ∀ (U V : R.NearRow), U ≠ V →
    ((U : Finset (Fin 11)) ∩ (V : Finset (Fin 11))).card = 1 →
    (∑ E : R.EndpointType, ((R.edgeClass E).card : ℚ) *
      ∑ C : R.NearColumnShell E, mass E C * R.shellPairIndicator C U V) = 3

namespace RegularNonTwoK4RootedCubicLift

/-- Every actual regular rooted lift gives a fractional near frame by uniformly
averaging the edges in each endpoint shell. -/
noncomputable def toFractionalNearFrame
    (R : RegularNonTwoK4RootedCubicLift) : FractionalNearFrame R where
  mass := R.empiricalMass
  mass_nonneg := R.empiricalMass_nonneg
  mass_normalization := R.sum_empiricalMass
  concurrence := by
    intro U V hUV _
    rw [Finset.sum_congr rfl fun E _ => R.card_mul_empiricalPair_eq E U V]
    norm_cast
    rw [R.sum_card_edgeClass_filter (fun e => e ∈ R.block U ∧ e ∈ R.block V)]
    exact R.card_nonRootEdges_filter_pair U V hUV

end RegularNonTwoK4RootedCubicLift

end SRG266.QuasiSymmetric
