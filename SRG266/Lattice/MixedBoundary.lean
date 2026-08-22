/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7MixedShell
import SRG266.Lattice.KneserBoundary

/-!
# Splitting the mixed norm-one branch by host

This file splits the mixed norm-one branch between the host
`ℤ ⊕ (E₇ ⊕ E₇)⁺` and the other three hosts.

* `SRG266.E7MixedNormOneCase` is the `ℤ ⊕ (E₇ ⊕ E₇)⁺` half, delivered in the
  normalized shell coordinates used by the certificate families.
* `SRG266.Rank15EmbeddingWitness.HasUnmodelledMixedHost` is the other half, and
  it names the three hosts it covers by their norm-one-free cores.
* `SRG266.MixedNormOneHostIdentificationInput` is the identification step: it
  turns a mixed direction into one of the two halves.  It is *normalization*
  content and belongs with `SRG266.RootedNormOneFreeClassification`, not with
  the finite elimination.
* `SRG266.MixedNonE7NormOneDirectionExclusionInput` is the residual named input
  for the three unmodelled hosts.
* `SRG266.mixedNormOneDirectionExclusionInput_of_recut` combines the three
  inputs into `SRG266.MixedNormOneDirectionExclusionInput`.
-/

namespace SRG266

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## The `ℤ ⊕ (E₇ ⊕ E₇)⁺` half -/

/-- **The mixed norm-one branch in the `ℤ ⊕ (E₇ ⊕ E₇)⁺` host.**  A local Gram
realization in an eligible norm-three shell of `ℤ ⊕ (E₇ ⊕ E₇)⁺`, in the
normalized centroid coordinates `(left, right, unitCentroid)` the mixed
certificate families are indexed by, together with a generator that the
norm-one direction does not annihilate.

The last field is the negation of what
`SRG266.E7MixedShellGramRealization.unit_eq_zero_of_pureOnly` and
`SRG266.e7MixedShellGramRealization_unit_eq_zero_of_dischargedKey` prove, and it
is weaker than nonexistence of the realization; keeping it in this shape is what
makes the `201` pure-only keys usable at all. -/
structure E7MixedNormOneCase (x : V) where
  /-- Twice the centroid coordinates in the left `E₇` factor. -/
  left : Fin 8 → ℤ
  /-- Twice the centroid coordinates in the right `E₇` factor. -/
  right : Fin 8 → ℤ
  /-- The centroid coordinate along the norm-one direction. -/
  unitCentroid : ℤ
  /-- The realization of the local Gram matrix inside the eligible shell. -/
  realization : E7MixedShellGramRealization G x left right unitCentroid
  /-- Some generator is not orthogonal to the norm-one direction. -/
  nonorthogonal : ∃ B, e7MixedUnit (realization.shell B).1 ≠ 0

/-- The `ℤ ⊕ (E₇ ⊕ E₇)⁺` half is empty. -/
abbrev E7MixedNormOneExclusion : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (_hG : IsHypothetical G) (x : V),
    IsEmpty (E7MixedNormOneCase G x)

/-! ## The three unmodelled hosts -/

variable {G}

/-- **A norm-one-carrying host with no mixed shell model.**  The norm-one-free
core of the host is covered by the zero lattice, by `E₈` or by `D₁₂⁺`; that is,
the host is `ℤ¹⁵`, `ℤ⁷ ⊕ E₈` or `ℤ³ ⊕ D₁₂⁺`.

`A₁₅⁺` is absent because it carries no norm-one vector, so it cannot
occur in the mixed branch.  `ℤ ⊕ (E₇ ⊕ E₇)⁺` is absent because it is the one
modelled by `SRG266.E7MixedNormOneCase`. -/
def Rank15EmbeddingWitness.HasUnmodelledMixedHost {x : V}
    (E : Rank15EmbeddingWitness G x) : Prop :=
  ∃ (k : ℕ) (u : Fin k → E.host.carrier),
    (∀ i, E.host.pairing (u i) (u i) = 1) ∧
      (Lattice.IsHostCoreModel E.host u (0 : Matrix (Fin 0) (Fin 0) ℤ) ∨
        Lattice.IsHostCoreModel E.host u Lattice.e8Gram ∨
        Lattice.IsHostCoreModel E.host u Lattice.d12PlusGram)

/-! ## Host-indexed inputs -/

/-- In `ℤ¹⁵`, `ℤ⁷ ⊕ E₈` and
`ℤ³ ⊕ D₁₂⁺`, no norm-one host direction pairs nontrivially with an embedded
local Gram generator. -/
abbrev MixedNonE7NormOneDirectionExclusionInput : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (_hG : IsHypothetical G) (x : V) (E : Rank15EmbeddingWitness G x),
    E.HasUnmodelledMixedHost → ¬E.HasMixedNormOneDirection

/-- **The host identification step of the mixed branch.**  A mixed norm-one
direction either normalizes into the `ℤ ⊕ (E₇ ⊕ E₇)⁺` shell coordinates of
`SRG266.E7MixedNormOneCase`, or lives in one of the three hosts of
`SRG266.Rank15EmbeddingWitness.HasUnmodelledMixedHost`.

This is exactly the mixed-branch counterpart of
`SRG266.RootedNormOneFreeClassification`: the orthogonal splitting `L = ℤu ⊥ u⊥`,
the identification of `u⊥`, the norm-three shell completeness for
`ℤ ⊕ (E₇ ⊕ E₇)⁺` and the Weyl/sign/factor-swap normalization into centroid
coordinates.  It is normalization content, and it is stated separately here so
that the finite elimination it feeds contains none of it. -/
abbrev MixedNormOneHostIdentificationInput : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (_hG : IsHypothetical G) (x : V) (E : Rank15EmbeddingWitness G x),
    E.HasMixedNormOneDirection →
      Nonempty (E7MixedNormOneCase G x) ∨ E.HasUnmodelledMixedHost

/-! ## Combined exclusion -/

/-- Combine host identification with the exclusions for both host classes. -/
theorem mixedNormOneDirectionExclusionInput_of_recut
    (hIdentify : MixedNormOneHostIdentificationInput.{u})
    (hOther : MixedNonE7NormOneDirectionExclusionInput.{u})
    (hE7 : E7MixedNormOneExclusion.{u}) :
    MixedNormOneDirectionExclusionInput.{u} := by
  intro V _ _ G _ hG x E direction hdirection generator
  by_contra hprofile
  have hmixed : E.HasMixedNormOneDirection :=
    ⟨direction, hdirection, generator, hprofile⟩
  rcases hIdentify G hG x E hmixed with he7 | hunmodelled
  · obtain ⟨mixedCase⟩ := he7
    exact (hE7 G hG x).false mixedCase
  · exact hOther G hG x E hunmodelled hmixed

end SRG266
