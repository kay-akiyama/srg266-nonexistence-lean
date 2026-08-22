/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.NormTwoRootBasis
import SRG266.Lattice.ADEComponentAssembly
import SRG266.Lattice.ThetaEutaxyBoundary

/-!
# ADE decomposition of a full-rank norm-two root system

Starting from the finite norm-two
root set and its full-rank assertion (the data naturally supplied by the
theta/eutaxy calculation), it constructs the ADE component list, an injective
integral isometry from its standard root lattice, and proves that every
norm-two vector is in the image.

No lattice classification, finite search, `native_decide`, or `bv_decide` is
used.
-/

namespace SRG266
namespace Lattice

open Function Set

/-- The coordinate map obtained by ordering the simple roots. -/
noncomputable def coordinateRootMap
    {n m : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} (coord : Fin m ≃ simpleRootSet f) :
    (Fin m → ℤ) →ₗ[ℤ] L.carrier :=
  Fintype.linearCombination ℤ fun i => normTwoRootVal (coord i).1

/-- Ordered simple roots give an injective coordinate map. -/
theorem coordinateRootMap_injective
    {n m : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (coord : Fin m ≃ simpleRootSet f) :
    Function.Injective (coordinateRootMap coord) := by
  have hli := simpleRootSet_linearIndepOn f hf
  change LinearIndependent ℤ
    (fun r : simpleRootSet f => normTwoRootVal r.1) at hli
  have hli' : LinearIndependent ℤ
      (fun i : Fin m => normTwoRootVal (coord i).1) :=
    hli.comp coord coord.injective
  intro x y hxy
  change (Fintype.linearCombination ℤ
    (fun i : Fin m => normTwoRootVal (coord i).1)) x =
      (Fintype.linearCombination ℤ
        (fun i : Fin m => normTwoRootVal (coord i).1)) y at hxy
  exact hli'.fintypeLinearCombination_injective hxy

/-- A Gram identity for the ordered simple roots is exactly the isometry
identity for `coordinateRootMap`. -/
theorem coordinateRootMap_pairing
    {n m : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (coord : Fin m ≃ simpleRootSet f) (A : Matrix (Fin m) (Fin m) ℤ)
    (hA : ∀ i j,
      graphCartanMatrix (simpleRootGraph f) (coord i) (coord j) = A i j)
    (x y : Fin m → ℤ) :
    L.pairing (coordinateRootMap coord x) (coordinateRootMap coord y) =
      Matrix.toBilin' A x y := by
  classical
  rw [coordinateRootMap, bilinForm_fintypeLinearCombination, Matrix.toBilin'_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← hA i j, graphCartanMatrix_simpleRootGraph f hf]
  rfl

/-- Every norm-two root lies in the image of any ordering of the simple
roots. -/
theorem coordinateRootMap_covers_normTwoRoots
    {n m : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (coord : Fin m ≃ simpleRootSet f) (r : NormTwoRoot L) :
    ∃ x : Fin m → ℤ, coordinateRootMap coord x = r.1 := by
  have hr : r.1 ∈ normTwoRootSpan L :=
    Submodule.subset_span ⟨r, rfl⟩
  rw [← span_simpleRoots_eq_normTwoRootSpan f hf] at hr
  have hrange :
      Set.range (fun i : Fin m => normTwoRootVal (coord i).1) =
        Set.range (fun s : simpleRootSet f => normTwoRootVal s.1) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨i, rfl⟩
      exact ⟨coord i, rfl⟩
    · rintro _ ⟨s, rfl⟩
      exact ⟨coord.symm s, by simp⟩
  rw [← hrange, Submodule.mem_span_range_iff_exists_fun] at hr
  obtain ⟨x, hx⟩ := hr
  refine ⟨x, ?_⟩
  change (Fintype.linearCombination ℤ
    (fun i : Fin m => normTwoRootVal (coord i).1)) x = r.1
  simpa only [Fintype.linearCombination_apply] using hx

/-- The coordinate-level ADE decomposition underlying `normTwoRoots_areADE`.
Keeping the ordered simple roots and their exact Gram identity available lets
later arguments transport finite root-orbit certificates without choosing an
inverse to the resulting embedding. -/
theorem normTwoRoots_haveADECoordinates
    {n : ℕ} (hn : n ≤ 15) (L : PDUnimodularLattice n)
    [Finite (NormTwoRoot L)]
    (f : L.carrier →+ ℤ) (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (hrank : Set.finrank ℤ (Set.range (@normTwoRootVal n L)) = n) :
    ∃ ts : List ADEType,
      (∀ t ∈ ts, t.IsRegular) ∧
      ADEType.rankSum ts = n ∧
      ∃ coord : Fin (ADEType.rankSum ts) ≃ simpleRootSet f,
        ∀ i j,
          graphCartanMatrix (simpleRootGraph f) (coord i) (coord j) =
            (adeGram ts).2 i j := by
  classical
  let G := simpleRootGraph f
  have hpos : IsPositiveCartan G := simpleRootGraph_isPositiveCartan f hf
  have hcard : Fintype.card (simpleRootSet f) ≤ 15 := by
    rw [card_simpleRootSet_eq_of_fullRank f hf hrank]
    exact hn
  obtain ⟨ts, hregular, htscard, coord, hgram⟩ :=
    positiveCartan_ADECoordinates hpos hcard
  have hts : ADEType.rankSum ts = n := by
    rw [htscard, card_simpleRootSet_eq_of_fullRank f hf hrank]
  exact ⟨ts, hregular, hts, coord, hgram⟩

/-- Finite full-rank norm-two roots in rank at
most fifteen have a full-rank ADE root-lattice embedding. -/
theorem normTwoRoots_areADE
    {n : ℕ} (hn : n ≤ 15) (L : PDUnimodularLattice n)
    [Finite (NormTwoRoot L)]
    (f : L.carrier →+ ℤ) (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (hrank : Set.finrank ℤ (Set.range (@normTwoRootVal n L)) = n) :
    ∃ ts : List ADEType,
      (∀ t ∈ ts, t.IsRegular) ∧
      ADEType.rankSum ts = n ∧ IsRootADEEmbedding L ts := by
  obtain ⟨ts, hregular, hts, coord, hgram⟩ :=
    normTwoRoots_haveADECoordinates hn L f hf hrank
  refine ⟨ts, hregular, hts, ?_⟩
  refine ⟨coordinateRootMap coord,
    coordinateRootMap_injective hf coord, ?_, ?_⟩
  · intro x y
    exact coordinateRootMap_pairing hf coord (adeGram ts).2 hgram x y
  · intro r hr
    exact coordinateRootMap_covers_normTwoRoots hf coord ⟨r, hr⟩

end Lattice

/-! ## The reduced theta/eutaxy input -/

/-- The part of the theta calculation needed before the purely algebraic ADE
classification starts.

The separating functional is only an orientation device for choosing simple
roots.  It carries no classification information.  The substantial fields are
finiteness and full rank of the norm-two roots. -/
structure NormTwoRootSpanningData {n : ℕ} (L : PDUnimodularLattice n) where
  rootsFinite : Finite (Lattice.NormTwoRoot L)
  separator : L.carrier →+ ℤ
  separator_ne : ∀ r : Lattice.NormTwoRoot L, separator r.1 ≠ 0
  fullRank : Set.finrank ℤ
    (Set.range (@Lattice.normTwoRootVal n L)) = n

/-- For a norm-one-free unimodular lattice in ranks 12 through 15, the theta
calculation says that the norm-two roots are finite and full rank.  Its
degree-two eutaxy identity then fixes the Coxeter number of every component of
any ADE realization.

Unlike `ThetaEutacticADEDecompositionInput`, this proposition does not assume
that the roots are ADE or even that an ADE realization exists. -/
abbrev ThetaRootEutaxyInput : Prop :=
  ∀ (n : ℕ), 12 ≤ n → n ≤ 15 → ∀ (L : PDUnimodularLattice n),
    (∀ v : L.carrier, L.pairing v v ≠ 1) →
      ∃ _ : NormTwoRootSpanningData L,
        ∀ (ts : List Lattice.ADEType),
          Lattice.ADEType.rankSum ts = n →
          Lattice.IsRootADEEmbedding L ts →
          ∀ t ∈ ts, t.coxeterNumber = 2 * (23 - n)

/-- Root eutaxy implies the combined theta/ADE decomposition interface. -/
theorem thetaEutacticADEDecomposition_of_rootEutaxy
    (hTheta : ThetaRootEutaxyInput) :
    ThetaEutacticADEDecompositionInput := by
  intro n hnlo hnhi L hfree
  obtain ⟨data, hcox⟩ := hTheta n hnlo hnhi L hfree
  letI := data.rootsFinite
  obtain ⟨ts, _, hrank, hroot⟩ :=
    Lattice.normTwoRoots_areADE hnhi L data.separator
      data.separator_ne data.fullRank
  exact ⟨ts, hrank, hroot, hcox ts hrank hroot⟩

end SRG266
