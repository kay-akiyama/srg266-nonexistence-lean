/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.ExternalLatticeInputs
import SRG266.NormOneZeroTrade
import SRG266.Hosts.E7EnumeratedElimination
import SRG266.Hosts.A15EnumerationAssembly

/-!
# Auditable rank-15 host-reduction boundary

The coordinate-reduction input returns only the final five E7 and four
A15 survivors.  That compact statement hides finite whole-search equalities
inside the same boundary as lattice classification.

This module exposes a weaker and more auditable pre-enumeration conclusion:

* a genuinely mixed norm-one/core branch, exposed rather than silently
  discharged by coordinate normalization;
* a full integral-factorization branch, eliminated by quasi-symmetric design
  nonexistence;
* a normalized `D12+` realization;
* an E7 realization together with its structural enumerator and trace
  witnesses;
* an A15 realization together with the elementary bounded-coordinate
  invariants consumed by the structurally complete reference enumerator.

The mixed-direction exclusion and four finite whole-search equalities are
separate arguments to the final theorem rather than hidden in a
theorem called “classification”.
-/

namespace SRG266

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Coordinate alternatives before the four finite enumeration audits.

The first constructor makes a *full* one-integral factorization explicit.
A norm-one host component may enter this constructor only after the
normalization argument proves that it induces such a full factorization.
Arbitrary mixed unit/core components are represented by `mixedNormOne`. A full
factorization is excluded by `NoQuasiSymmetricDesign56`. -/
inductive AuditedRank15HostCase (x : V)
  | mixedNormOne
      (embedding : Rank15EmbeddingWitness G x)
      (direction : embedding.host.carrier)
      (direction_norm : embedding.host.pairing direction direction = 1)
      (generator : SecondSubconstituent G x)
      (nonorthogonal :
        embedding.directionProfile (G := G) direction generator ≠ 0)
  | oneIntegrable (factorization : LocalGramIsOneIntegrable G x)
  | d12Plus (realization : D12PlusGramRealization G x)
  | e7e7Plus
      (left right : Array ℤ)
      (left_mem : left ∈ e7EnumeratedComponentProfiles)
      (right_mem : right ∈ e7EnumeratedComponentProfiles)
      (trace_mem :
        (e7ComponentKey left, e7ComponentKey right) ∈
          e7TraceFeasibleHistogramPairs)
      (realization :
        E7CentroidShellGramRealization G x
          (e7ComponentEnumerationProfile left)
          (e7ComponentEnumerationProfile right))
  | a15Plus
      (residue : ℤ)
      (coordinates : List ℤ)
      (residue_cases : residue = 0 ∨ residue = 2)
      (coordinate_count : coordinates.length = 16)
      (coordinate_bounds :
        ∀ z ∈ coordinates, -17 ≤ z ∧ z ≤ 17)
      (coordinate_sum :
        coordinates.sum = a15ReducedTargetSum residue)
      (coordinate_sq_sum :
        (coordinates.map (fun z : ℤ => z * z)).sum =
          a15ReducedTargetSq residue)
      (special_residue_bound :
        residue = 2 → coordinates.count 17 = 0)
      (realization :
        A15ShellGramRealization G x
          (a15EnumerationProfile
            (a15ScaleReducedProfile residue
              (a15CanonicalReducedCoordinates coordinates))))

/-- Exact graph-specific input excluding a nonorthogonal norm-one host
direction.

This is the mixed unit/core problem isolated from lattice classification.
`NormOneDirections.lean` proves natively that every putative counterexample
to this input yields a ternary 220-entry affine eigenvector with all of the
`NormOneDirectionAuditProfile` bounds.  Host-specific finite elimination of
those profiles is the only content intended to remain here. -/
abbrev MixedNormOneDirectionExclusionInput : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (_hG : IsHypothetical G) (x : V)
    (embedding : Rank15EmbeddingWitness G x),
    embedding.NormOneDirectionsOrthogonal G

/-- The sharpened mixed-direction boundary.  The local design algebra and the
quasi-symmetric-design obstruction prove that every norm-one direction has
centroid coordinate zero, so an external or host-specific argument only needs
to exclude nonorthogonal profiles in this single fibre. -/
abbrev ZeroCentroidMixedNormOneDirectionExclusionInput : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (_hG : IsHypothetical G) (x : V)
    (embedding : Rank15EmbeddingWitness G x)
    (c : IntegralGramLattice G x)
    (_hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (direction : embedding.host.carrier),
    embedding.host.pairing direction direction = 1 →
      embedding.centroidCoordinate (G := G) c direction = 0 →
        ∀ generator : SecondSubconstituent G x,
          embedding.directionProfile (G := G) direction generator = 0

/-- The zero-centroid boundary implies the blanket mixed-direction
input.  The only additional ingredient is the same named design theorem which
is already required elsewhere in the assembled nonexistence proof. -/
theorem mixedNormOneDirectionExclusionInput_of_zeroCentroid
    (hMT : NoQuasiSymmetricDesign56.{u})
    (hZero : ZeroCentroidMixedNormOneDirectionExclusionInput.{u}) :
    MixedNormOneDirectionExclusionInput.{u} := by
  intro V _ _ G _ hG x embedding direction hdirection generator
  obtain ⟨c, hc⟩ := exists_integral_centroid G hG x
  have hcentroid :=
    embedding.centroidCoordinate_eq_zero_of_noQuasiSymmetricDesign
      (G := G) hMT hG c hc direction hdirection
  exact hZero G hG x embedding c hc direction hdirection hcentroid generator

/-- The sharpened zero-centroid mixed boundary is a theorem.  Its proof is the
signed-trade counting argument of `SRG266.NormOneZeroTrade`. -/
theorem zeroCentroidMixedNormOneDirectionExclusionInput_holds :
    ZeroCentroidMixedNormOneDirectionExclusionInput.{u} := by
  intro V _ _ G _ hG x embedding c hc direction hdirection hcentroid generator
  exact embedding.directionProfile_eq_zero_of_centroid_eq_zero
    (G := G) hG c hc direction hdirection hcentroid generator

/-- Consequently the blanket mixed-direction input follows from the
quasi-symmetric-design nonexistence theorem already present in the main proof.
All host-specific mixed-shell classifications and enumerations are unnecessary
for the graph nonexistence conclusion. -/
theorem mixedNormOneDirectionExclusionInput_of_noQuasiSymmetricDesign
    (hMT : NoQuasiSymmetricDesign56.{u}) :
    MixedNormOneDirectionExclusionInput.{u} :=
  mixedNormOneDirectionExclusionInput_of_zeroCentroid hMT
    zeroCentroidMixedNormOneDirectionExclusionInput_holds

/-- Pure-core reduction to the three coordinate hosts and their structural
enumerator domains. Mixed norm-one/core embeddings are returned by
`mixedNormOne`. -/
abbrev Rank15PreEnumerationNormalizationInput : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (_hG : IsHypothetical G) (x : V),
    Rank15EmbeddingWitness G x →
      Nonempty (AuditedRank15HostCase G x)

/-- Every pre-enumeration host case is impossible once the mixed-direction
input and four exact finite audits are supplied separately. -/
theorem no_auditedRank15HostCase
    (hMT : NoQuasiSymmetricDesign56.{u})
    (hMixed : MixedNormOneDirectionExclusionInput.{u})
    [E7ScalarDPAuditInput]
    [E7ConcreteEnumerationAuditInput]
    [A15CentroidEnumerationInput]
    [A15ExactEnumerationInput]
    (hG : IsHypothetical G) (x : V) :
    IsEmpty (AuditedRank15HostCase G x) := by
  refine ⟨fun host => ?_⟩
  cases host with
  | mixedNormOne embedding direction direction_norm generator nonorthogonal =>
      exact nonorthogonal
        (hMixed G hG x embedding direction direction_norm generator)
  | oneIntegrable factorization =>
      exact
        (localGram_not_oneIntegrable_of_noQuasiSymmetricDesign
          G hMT hG x)
          factorization
  | d12Plus realization =>
      exact (no_d12PlusRealization G hMT hG x) ⟨realization⟩
  | e7e7Plus left right left_mem right_mem trace_mem realization =>
      exact
        (no_e7EnumeratedTraceRealization
          G hG x left right left_mem right_mem trace_mem).false
          realization
  | a15Plus residue coordinates residue_cases coordinate_count
      coordinate_bounds coordinate_sum coordinate_sq_sum
      special_residue_bound realization =>
      obtain ⟨finalCase⟩ :=
        a15CanonicalRealization_hasFinalShellCase
          G hG x residue coordinates residue_cases coordinate_count
          coordinate_bounds coordinate_sum coordinate_sq_sum
          special_residue_bound realization
      exact (no_a15FinalShellCase G hMT hG x).false finalCase

end SRG266
