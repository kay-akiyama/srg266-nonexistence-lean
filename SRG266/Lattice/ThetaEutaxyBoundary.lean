/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.EutacticADE
import SRG266.Lattice.CorankFourStatement

/-!
# A theta-eutaxy replacement for the low-rank lattice classification

This file turns the theta-eutaxy observation into an exact replacement chain
for `SRG266.RootedCorankFourClassification`.

In ranks 12 through 15 a degree-two weighted theta identity makes the roots
strongly eutactic. After the standard ADE
decomposition, every irreducible component has Coxeter number

`2 * (23 - n)`.

The finite arithmetic in `SRG266.Lattice.EutacticADE` then forces the full-rank
root lattice to be exactly one of

* `D12` in rank 12;
* `E7 + E7` in rank 14;
* `A15` in rank 15;

and proves that rank 13 is impossible.  Only the three elementary full-rank
glue calculations remain.  They concern discriminant groups of order four,
four, and sixteen respectively; no positive-corank complement and no Kneser
neighbour enumeration remains.

The theorem `SRG266.rootedCorankFourClassification_of_thetaEutaxy_glue` is the
formal assembly of that argument.  Its conclusion is exactly
`SRG266.RootedCorankFourClassification`, without importing the
certificate-heavy final branch assembly.
-/

namespace SRG266
namespace Lattice

open scoped Matrix

/-! ## The root-lattice interface -/

/-- A concrete ADE root lattice embedded in a positive-definite unimodular
lattice.  The map is isometric and injective, and every norm-two vector of the
ambient lattice belongs to its image.

The rank equality is deliberately kept outside this definition.  This lets the
same object be reused for root systems of positive corank, while
`HasFullRankRootType` records the full-rank case needed below. -/
def IsRootADEEmbedding {n : ℕ} (L : PDUnimodularLattice n)
    (ts : List ADEType) : Prop :=
  ∃ f : (Fin (ADEType.rankSum ts) → ℤ) →ₗ[ℤ] L.carrier,
    Function.Injective f ∧
      (∀ v w, L.pairing (f v) (f w) = Matrix.toBilin' (adeGram ts).2 v w) ∧
      ∀ r : L.carrier, L.pairing r r = 2 → ∃ v, f v = r

/-- The ambient lattice has full-rank root system of the given ADE type.

The existential list makes the predicate invariant under a permutation of the
component list without constructing a block-permutation matrix. -/
def HasFullRankRootType {n : ℕ} (L : PDUnimodularLattice n)
    (ts : List ADEType) : Prop :=
  ∃ us : List ADEType, us.Perm ts ∧ ADEType.rankSum us = n ∧
    IsRootADEEmbedding L us

/-- Reordering ADE components does not change the root type. -/
theorem HasFullRankRootType.of_perm {n : ℕ} {L : PDUnimodularLattice n}
    {ts us : List ADEType} (h : HasFullRankRootType L ts) (p : ts.Perm us) :
    HasFullRankRootType L us := by
  obtain ⟨vs, hv, hrank, hmodel⟩ := h
  exact ⟨vs, hv.trans p, hrank, hmodel⟩

end Lattice

/-! ## The sharply separated inputs -/

/-- **Theta plus ADE, but no unimodular-lattice classification.**

For a norm-one-free unimodular lattice in the relevant ranks, its roots form a
full-rank ADE root lattice and every component has the Coxeter number forced by
the degree-two weighted theta identity.

This input contains precisely two standard structural theorems:

1. the weighted-theta root-eutaxy identity;
2. the classification of finite simply-laced root systems as ADE.

It contains no discriminant-group or overlattice classification. -/
abbrev ThetaEutacticADEDecompositionInput : Prop :=
  ∀ (n : ℕ), 12 ≤ n → n ≤ 15 → ∀ (L : PDUnimodularLattice n),
    (∀ v : L.carrier, L.pairing v v ≠ 1) →
      ∃ ts : List Lattice.ADEType,
        Lattice.ADEType.rankSum ts = n ∧
          Lattice.IsRootADEEmbedding L ts ∧
          ∀ t ∈ ts, t.coxeterNumber = 2 * (23 - n)

/-- The full-rank `D12` glue calculation.  Its discriminant group has order
four; excluding norm-one glue leaves a spinor glue, giving `D12+`. -/
abbrev D12FullRankGlueRigidityInput : Prop :=
  ∀ (L : PDUnimodularLattice 12),
    (∀ v : L.carrier, L.pairing v v ≠ 1) →
    Lattice.HasFullRankRootType L [.D 12] →
      Lattice.IsMatrixModel L Lattice.d12PlusGram

/-- The full-rank `E7 + E7` glue calculation.  The unique admissible
order-two diagonal glue gives `(E7 + E7)+`. -/
abbrev E7E7FullRankGlueRigidityInput : Prop :=
  ∀ (L : PDUnimodularLattice 14),
    (∀ v : L.carrier, L.pairing v v ≠ 1) →
    Lattice.HasFullRankRootType L [.E7, .E7] →
      Lattice.IsMatrixModel L Lattice.e7e7PlusGram

/-- The full-rank `A15` glue calculation.  The cyclic discriminant group has
order sixteen and its unique order-four subgroup gives `A15+`. -/
abbrev A15FullRankGlueRigidityInput : Prop :=
  ∀ (L : PDUnimodularLattice 15),
    (∀ v : L.carrier, L.pairing v v ≠ 1) →
    Lattice.HasFullRankRootType L [.A 15] →
      Lattice.IsMatrixModel L Lattice.a15PlusGram

/-! ## Assembly -/

/-- The theta/ADE structural theorem and the three full-rank glue calculations
imply the corank-four classification boundary.

The proof contains the complete rank and Coxeter-number case split.  In
particular, no external input is allowed to silently discard rank 13. -/
theorem rootedCorankFourClassification_of_thetaEutaxy_glue
    (hTheta : ThetaEutacticADEDecompositionInput)
    (hD12 : D12FullRankGlueRigidityInput)
    (hE7E7 : E7E7FullRankGlueRigidityInput)
    (hA15 : A15FullRankGlueRigidityInput) :
    RootedCorankFourClassification := by
  intro n hnlo hnhi L hfree
  obtain ⟨ts, hrank, hroot, hcox⟩ := hTheta n hnlo hnhi L hfree
  rcases Lattice.ade_eutactic_rank_cases hnlo hnhi hrank hcox with
    ⟨rfl, htype⟩ | ⟨rfl, htype⟩ | ⟨rfl, htype⟩
  · exact Or.inl (hD12 L hfree ⟨ts, htype, hrank, hroot⟩)
  · exact Or.inr (Or.inl (hE7E7 L hfree ⟨ts, htype, hrank, hroot⟩))
  · exact Or.inr (Or.inr (hA15 L hfree ⟨ts, htype, hrank, hroot⟩))

end SRG266
