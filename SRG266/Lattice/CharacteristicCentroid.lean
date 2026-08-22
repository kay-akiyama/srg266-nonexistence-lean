/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.ExternalLatticeInputs
import SRG266.Lattice.PositiveDefinite
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.RingTheory.Int.Basic

/-!
# The local centroid is characteristic

The integral centroid of the local Gram lattice has norm `300` and pairs to
`15` with every distinguished norm-three generator.  Since those generators
span, it follows that

`<c, z> = <z, z> (mod 2)`

for every lattice vector `z`.  This file records that observation in a form
usable by a theta-series or shadow argument.

The last lemma is the saturation fact needed at an overlattice boundary: a
characteristic congruence extends across an odd multiple.  The discriminant
of the local Gram lattice is supported only at `3` and `5`, so all saturation
indices occurring in the Yang--Yoshino construction are odd.
-/

namespace SRG266
namespace Lattice

open scoped BigOperators

universe u

variable {X : Type u} [AddCommGroup X] [Module ℤ X]

/-- A characteristic vector for an integral symmetric bilinear form, stated
as the defining congruence modulo two. -/
def IsCharacteristic (B : LinearMap.BilinForm ℤ X) (c : X) : Prop :=
  ∀ z : X, (2 : ℤ) ∣ B z z - B c z

/-- Vectors satisfying the characteristic congruence against a fixed `c`
form a submodule.  Symmetry is used only to combine the two cross terms. -/
def characteristicSubmodule (B : LinearMap.BilinForm ℤ X) (hB : B.IsSymm) (c : X) :
    Submodule ℤ X where
  carrier := {z | (2 : ℤ) ∣ B z z - B c z}
  zero_mem' := by simp
  add_mem' := by
    rintro z w ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b + B z w, ?_⟩
    simp only [map_add, LinearMap.add_apply]
    rw [hB.eq w z]
    linear_combination ha + hb
  smul_mem' := by
    rintro m z ⟨a, ha⟩
    obtain ⟨b, hb⟩ := (Int.even_mul_pred_self m).two_dvd
    refine ⟨m ^ 2 * a + b * B c z, ?_⟩
    simp only [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
    linear_combination m ^ 2 * ha + (B c z) * hb

@[simp]
theorem mem_characteristicSubmodule (B : LinearMap.BilinForm ℤ X) (hB : B.IsSymm)
    (c z : X) :
    z ∈ characteristicSubmodule B hB c ↔ (2 : ℤ) ∣ B z z - B c z :=
  Iff.rfl

/-- It is enough to check the characteristic congruence on any spanning
family. -/
theorem isCharacteristic_of_span {B : LinearMap.BilinForm ℤ X} (hB : B.IsSymm)
    (c : X) {S : Set X} (hspan : Submodule.span ℤ S = ⊤)
    (hS : ∀ z ∈ S, (2 : ℤ) ∣ B z z - B c z) :
    IsCharacteristic B c := by
  intro z
  have hle : Submodule.span ℤ S ≤ characteristicSubmodule B hB c :=
    Submodule.span_le.mpr hS
  apply hle
  rw [hspan]
  exact Submodule.mem_top

/-- Characteristic congruences are preserved by a pairing-preserving linear
map, on the image of that map. -/
theorem IsCharacteristic.map {Y : Type*} [AddCommGroup Y] [Module ℤ Y]
    {B : LinearMap.BilinForm ℤ X} {C : LinearMap.BilinForm ℤ Y} {c : X}
    (hc : IsCharacteristic B c) (f : X →ₗ[ℤ] Y)
    (hf : ∀ z w, C (f z) (f w) = B z w) (z : X) :
    (2 : ℤ) ∣ C (f z) (f z) - C (f c) (f z) := by
  simpa only [hf] using hc z

/-- **Odd saturation.**  If the characteristic congruence holds at the odd
multiple `m z`, then it already holds at `z`.

This is the exact parity mechanism by which a characteristic vector extends
from a lattice to any odd-index integral overlattice. -/
theorem characteristic_of_odd_smul
    {B : LinearMap.BilinForm ℤ X} {c z : X} {m : ℤ}
    (hm : Odd m) (h : (2 : ℤ) ∣ B (m • z) (m • z) - B c (m • z)) :
    (2 : ℤ) ∣ B z z - B c z := by
  obtain ⟨a, ha⟩ := h
  have hpred : (2 : ℤ) ∣ m * (m - 1) :=
    (Int.even_mul_pred_self m).two_dvd
  obtain ⟨b, hb⟩ := hpred
  have hmul : (2 : ℤ) ∣ m * (B z z - B c z) := by
    refine ⟨a - b * B z z, ?_⟩
    have ha' : m * (m * B z z) - m * B c z = 2 * a := by
      simpa only [map_zsmul, LinearMap.smul_apply, smul_eq_mul] using ha
    linear_combination ha' - (B z z) * hb
  exact (Int.isCoprime_two_left.mpr hm).dvd_of_dvd_mul_left hmul

end Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **The graph-specific characteristic-vector theorem.**  Every integral
centroid of the local Gram lattice is characteristic. -/
theorem integral_centroid_isCharacteristic
    (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    Lattice.IsCharacteristic (integralGramPairing G x) c := by
  apply Lattice.isCharacteristic_of_span (integralGramPairing_isSymm G x) c
    (S := Set.range (integralGramGenerator G x))
  · apply top_unique
    intro z _
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective
      (integralGramRelations G x) z
    rw [mk_eq_sum_smul_generator G x a]
    exact Submodule.sum_mem _ fun B _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨B, rfl⟩)
  · rintro _ ⟨B, rfl⟩
    rw [integralGramPairing_generator_generator G x,
      localGramMatrix_diagonal G hG x B,
      integral_centroid_pairing_generator G hG x c hc B]
    norm_num

/-- The embedded centroid remains characteristic on the embedded rank-twelve
Gram lattice inside any Yang--Yoshino host. -/
theorem Rank15EmbeddingWitness.embeddedCentroid_characteristic
    (E : Rank15EmbeddingWitness G x) (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (z : IntegralGramLattice G x) :
    (2 : ℤ) ∣
      E.host.pairing (E.embedding z) (E.embedding z) -
        E.host.pairing (E.embedding c) (E.embedding z) := by
  exact (integral_centroid_isCharacteristic G hG x c hc).map E.embedding
    (fun p q => E.preservesPairing p q) z

/-- The embedded centroid is characteristic at every host vector having an
odd multiple in the embedded Gram lattice. -/
theorem Rank15EmbeddingWitness.embeddedCentroid_characteristic_of_odd_multiple
    (E : Rank15EmbeddingWitness G x) (hG : IsHypothetical G)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (z : E.host.carrier) {m : ℤ} (hm : Odd m)
    (p : IntegralGramLattice G x) (hp : E.embedding p = m • z) :
    (2 : ℤ) ∣ E.host.pairing z z - E.host.pairing (E.embedding c) z := by
  apply Lattice.characteristic_of_odd_smul hm
  rw [← hp]
  exact E.embeddedCentroid_characteristic (G := G) hG c hc p

end SRG266
