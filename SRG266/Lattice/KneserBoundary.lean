/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7ProfileFilter
import SRG266.Lattice.Branches.A15HostCase
import SRG266.Lattice.Branches.D12
import SRG266.Lattice.Branches.E7E7
import SRG266.Lattice.Branches.E7Profile
import SRG266.Lattice.Branches.Trichotomy
import SRG266.Lattice.Branches.Trivial
import SRG266.Lattice.CorankFourStatement
import SRG266.Lattice.CoreRank
import SRG266.Lattice.FrameCore
import SRG266.Lattice.PureCoreRoots
import SRG266.Lattice.RootedClassification

/-!
# The residual classification statement behind the normalization input

`SRG266.RootedCorankFourClassification` classifies positive-definite unimodular
lattices of rank twelve to fifteen with no norm-one vector as `D₁₂⁺`,
`(E₇ ⊕ E₇)⁺`, or `A₁₅⁺`.  Passing to the frame complement turns this
classification into `SRG266.RootedNormOneFreeClassification`, from which the
rank-15 normalization input follows.
-/

namespace SRG266

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

namespace Lattice

/-! ## Audited-host adapter for the intrinsic E7 branch -/

private theorem E7ComponentEnumerationWitness.mem
    {profile : Array ℤ} (w : E7ComponentEnumerationWitness profile) :
    profile ∈ e7EnumeratedComponentProfiles := by
  have hcanonicalPerm :=
    a15CanonicalReducedCoordinates_perm w.source w.source_bounds
  have hcanonicalEq :
      a15CanonicalReducedCoordinates w.source = w.canonical :=
    List.Perm.eq_of_pairwise'
      (a15CanonicalReducedCoordinates_pairwise w.source)
      w.canonical_sorted
      (hcanonicalPerm.trans w.canonical_perm.symm)
  have hin := e7_canonical_reduced_component_mem_enumeration
    w.parity w.source w.source_length w.source_bounds w.source_sum
      w.source_sq w.source_special
  rw [hcanonicalEq, ← w.profile_eq] at hin
  rw [e7EnumeratedComponentProfiles, List.mem_append]
  rcases w.parity_cases with hp | hp
  · rw [hp] at hin
    exact Or.inl hin
  · rw [hp] at hin
    exact Or.inr hin

/-- Reconstruct the aggregate E7 host case from its intrinsic branch payload. -/
theorem E7BranchPayload.hasHostCase (hG : IsHypothetical G) {x : V}
    (P : E7BranchPayload G x) : Nonempty (AuditedRank15HostCase G x) := by
  have hleftMem := P.left_enumeration.mem
  have hrightMem := P.right_enumeration.mem
  obtain ⟨_, n₁, hn₁, hnorm₁⟩ := P.left_mined
  obtain ⟨_, n₂, _, hnorm₂⟩ := P.right_mined
  have htotalSq := P.realization.profile_sq_sum G hG x
  have htotal : n₁ + n₂ = 300 := by omega
  have heven : (2 : ℤ) ∣ n₁ := by
    rcases hn₁ with rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hlow : 38 ≤ n₁ := by
    rcases hn₁ with rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hhigh : n₁ ≤ 262 := by
    rcases hn₁ with rfl | rfl | rfl | rfl | rfl <;> norm_num
  have htrace :
      (e7ComponentKey P.left, e7ComponentKey P.right) ∈
        e7TraceFeasibleHistogramPairs :=
    e7TraceFeasible_of_realization G hG x
      (e7EnumeratedComponentProfiles_size P.left hleftMem)
      (e7EnumeratedComponentProfiles_size P.right hrightMem)
      hleftMem hrightMem P.left_sum P.right_sum
      P.left_parity P.right_parity hnorm₁ hnorm₂ heven htotal hlow hhigh
      P.realization
  exact ⟨.e7e7Plus P.left P.right hleftMem hrightMem htrace P.realization⟩

/-- A model of `(E₇ ⊕ E₇)⁺` produces the audited host case. -/
theorem e7e7Plus_branch_of_model {x : V} (hG : IsHypothetical G)
    (E : Rank15EmbeddingWitness G x) (hpure : E.NormOneDirectionsOrthogonal G)
    {k : ℕ} {u : Fin k → E.host.carrier}
    (hu : ∀ i, E.host.pairing (u i) (u i) = 1)
    (hmodel : IsHostCoreModel E.host u e7e7PlusGram) :
    Nonempty (AuditedRank15HostCase G x) := by
  obtain ⟨c, hc⟩ := exists_integral_centroid G hG x
  obtain ⟨M⟩ := PureCoreModel.exists_of_isHostCoreModel E c hc hpure hu hmodel
  obtain ⟨P⟩ := e7BranchPayload_of_pureCoreModel hG hc M
  exact P.hasHostCase G hG

end Lattice

/-! ## The statement -/

/-- Every part of `SRG266.Rank15PreEnumerationNormalizationInput` except
`SRG266.RootedNormOneFreeClassification` follows from the pure/mixed
trichotomy. The mixed half gives `mixedNormOne`; the pure half applies the
classification and dispatches to the pure-core rows.

Note what the proof does *not* need: no enumeration audit and no design input.
The one thing it *does* need beyond the branches is the corank lemma
`SRG266.Lattice.card_normOne_le_three`, which discharges the rank hypothesis of
the classification from the rank-12 embedded Gram lattice.  `D₁₂⁺` then
produces a one-integral factorization and the two enumerator rows produce their
membership witnesses. -/
theorem rank15PreEnumerationNormalization_of_classification
    (hClass : RootedNormOneFreeClassification) :
    Rank15PreEnumerationNormalizationInput.{u} := by
  intro V _ _ G _ hG x E
  rcases Lattice.normOneDirectionsOrthogonal_or_hostCase G E with hpure | hcase
  · obtain ⟨k, u, hnorm, horth, hfree, -⟩ := E.host.exists_orthonormal_normOneFree
    obtain ⟨B⟩ := Lattice.nonempty_secondSubconstituent G hG x
    have hthree : ∃ w : E.host.carrier,
        (∀ i, E.host.pairing (u i) w = 0) ∧ E.host.pairing w w = 3 :=
      ⟨E.embeddedGenerator (G := G) B, fun i => hpure (u i) (hnorm i) B,
        E.embeddedGenerator_norm (G := G) hG B⟩
    have htwo := Lattice.exists_pureCore_norm_two G hG E hpure hnorm
    have hk : k ≤ 3 := Lattice.card_normOne_le_three G hG E hpure hnorm horth
    rcases hClass E.host k u hk hnorm horth hfree htwo hthree with
      hd12 | he7 | ha15
    · exact (Lattice.d12PlusRealization_of_model G hG E hpure hnorm hd12).map
        AuditedRank15HostCase.d12Plus
    · exact Lattice.e7e7Plus_branch_of_model G hG E hpure hnorm he7
    · exact Lattice.a15Plus_branch_of_model G hG E hpure hnorm ha15
  · exact hcase

/-! ## Corank-four classification -/

/-- Derive the rank-15 normalization input from the corank-four lattice
classification. -/
theorem rank15PreEnumerationNormalization_of_corankFour
    (hCorank : RootedCorankFourClassification) :
    Rank15PreEnumerationNormalizationInput.{u} :=
  rank15PreEnumerationNormalization_of_classification
    (rootedNormOneFreeClassification_of_corankFour hCorank)

end SRG266
