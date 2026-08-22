/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.NormTwoRootReflectionInduction

/-!
# Finite reflection-closed families cover all norm-two roots

This module is the abstract completeness bridge for finite root-orbit
certificates.  A listed family is complete as soon as it is injective,
contains the separator-selected simple roots, and is closed under negation
and reflection in those simple roots.  The proof is the project-local
reflection induction; no bounded coordinate search is involved.
-/

namespace SRG266
namespace Lattice

/-- A finite injective family of norm-two roots containing the simple roots
and closed under their generating operations. -/
structure NormTwoRootOrbitCertificate {n : ℕ} (L : PDUnimodularLattice n)
    (f : L.carrier →+ ℤ) where
  Index : Type
  indexFintype : Fintype Index
  root : Index ↪ NormTwoRoot L
  simpleIndex : simpleRootSet f → Index
  simple_eq : ∀ s, root (simpleIndex s) = s.1
  negIndex : Index → Index
  neg_eq : ∀ a, root (negIndex a) = -(root a)
  reflectionIndex : simpleRootSet f → Index → Index
  reflection_eq : ∀ s a,
    root (reflectionIndex s a) = reflectNormTwoRoot L s.1 (root a)

namespace NormTwoRootOrbitCertificate

/-- Every norm-two root occurs in a finite reflection-closed family. -/
theorem root_surjective {n : ℕ} {L : PDUnimodularLattice n}
    {f : L.carrier →+ ℤ} (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (C : NormTwoRootOrbitCertificate L f) :
    Function.Surjective C.root := by
  letI := C.indexFintype
  let P : NormTwoRoot L → Prop := fun r ↦ ∃ a, C.root a = r
  apply normTwoRoot_reflection_induction f hf P
  · intro r hr
    obtain ⟨a, ha⟩ := hr
    refine ⟨C.negIndex a, ?_⟩
    rw [C.neg_eq, ha]
  · intro r hr
    let s : simpleRootSet f := ⟨r, hr⟩
    exact ⟨C.simpleIndex s, C.simple_eq s⟩
  · intro r s hs hr
    obtain ⟨a, ha⟩ := hr
    let simple : simpleRootSet f := ⟨s, hs⟩
    refine ⟨C.reflectionIndex simple a, ?_⟩
    rw [C.reflection_eq, ha]

/-- A finite reflection-closed root family is equivalent to the full root
type. -/
noncomputable def rootEquiv {n : ℕ} {L : PDUnimodularLattice n}
    {f : L.carrier →+ ℤ} (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (C : NormTwoRootOrbitCertificate L f) :
    C.Index ≃ NormTwoRoot L :=
  Equiv.ofBijective C.root ⟨C.root.injective, C.root_surjective hf⟩

/-- Completeness also identifies the cardinality of the norm-two shell. -/
theorem card_normTwoRoot_eq {n : ℕ} {L : PDUnimodularLattice n}
    {f : L.carrier →+ ℤ} (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (C : NormTwoRootOrbitCertificate L f) :
    @Fintype.card (NormTwoRoot L) (Fintype.ofFinite _) =
      @Fintype.card C.Index C.indexFintype := by
  letI := C.indexFintype
  exact Fintype.card_congr (C.rootEquiv hf).symm

end NormTwoRootOrbitCertificate

end Lattice
end SRG266
