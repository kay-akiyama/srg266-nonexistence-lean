/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.NormTwoRootReflectionInduction
import SRG266.Lattice.EutacticADE
import Mathlib.Data.Nat.Digits.Defs

/-!
# Finite certificates for ADE root orbits and eutaxy

An `ADERootOrbitCertificate t` is deliberately weaker than an enumeration of
all integer vectors of norm two.  It gives a finite injective family which

* contains every standard simple root;
* consists of norm-two vectors;
* is closed under negation and every standard simple reflection;
* has a checked diagonal second moment.

`normTwoRoot_reflection_induction` proves completeness after the family is
mapped into the actual lattice.  Thus the generated data never has to assert
that an unbounded coordinate search was exhaustive.
-/

namespace SRG266
namespace Lattice

/-- Reflection of a coordinate vector in standard simple root `i`. -/
def adeCoordinateReflection (t : ADEType) (i : Fin t.rank)
    (v : Fin t.rank → ℤ) : Fin t.rank → ℤ :=
  v - (Matrix.toBilin' t.gram v (Pi.single i 1)) • Pi.single i 1

/-- Coordinate reflection when the simple-root pairing has already been
computed.  Certificates store this scalar to avoid recomputing a matrix
product once per output coordinate. -/
def adeCoordinateReflectionWithPairing {n : ℕ} (i : Fin n) (p : ℤ)
    (v : Fin n → ℤ) : Fin n → ℤ :=
  v - p • Pi.single i 1

/-- Pairing with a standard simple root, evaluated as one matrix-vector sum
rather than a general double bilinear sum. -/
def adeSimplePairing (t : ADEType) (v : Fin t.rank → ℤ)
    (i : Fin t.rank) : ℤ :=
  ∑ j, v j * t.gram j i

theorem adeSimplePairing_eq_toBilin' (t : ADEType) (v : Fin t.rank → ℤ)
    (i : Fin t.rank) :
    adeSimplePairing t v i = Matrix.toBilin' t.gram v (Pi.single i 1) := by
  classical
  rw [adeSimplePairing, Matrix.toBilin'_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    simp [hki]
  · simp

/-- A cheap deterministic fingerprint for an integral coordinate vector.
Injectivity is required only on the finite certified family and is checked by
the certificate.  No global collision-freedom theorem is trusted. -/
def rootVectorFingerprint {n : ℕ} (v : Fin n → ℤ) : ℕ :=
  Nat.ofDigits 13 ((List.ofFn fun i => (v i + 6).toNat).reverse)

/-- Base-thirteen coding is injective on fixed-length vectors whose
coordinates lie between `-6` and `6`. -/
theorem rootVectorFingerprint_injective_of_bound {n : ℕ}
    {v w : Fin n → ℤ}
    (hv : ∀ i, -6 ≤ v i ∧ v i ≤ 6)
    (hw : ∀ i, -6 ≤ w i ∧ w i ≤ 6)
    (hcode : rootVectorFingerprint v = rootVectorFingerprint w) : v = w := by
  have digits_lt (x : Fin n → ℤ) (hx : ∀ i, -6 ≤ x i ∧ x i ≤ 6) :
      ∀ d ∈ (List.ofFn fun i => (x i + 6).toNat).reverse, d < 13 := by
    intro d hd
    rw [List.mem_reverse, List.mem_ofFn] at hd
    obtain ⟨i, rfl⟩ := hd
    have hi := hx i
    omega
  have hdigits :
      (List.ofFn fun i => (v i + 6).toNat).reverse =
        (List.ofFn fun i => (w i + 6).toNat).reverse := by
    apply Nat.ofDigits_inj_of_len_eq (b := 13) (by norm_num)
    · simp
    · exact digits_lt v hv
    · exact digits_lt w hw
    · exact hcode
  have hlist : (List.ofFn fun i => (v i + 6).toNat) =
      (List.ofFn fun i => (w i + 6).toNat) := by
    simpa using congrArg List.reverse hdigits
  have hfun : (fun i => (v i + 6).toNat) =
      (fun i => (w i + 6).toNat) :=
    List.ofFn_injective hlist
  funext i
  have hi := congrFun hfun i
  have hvnonneg : 0 ≤ v i + 6 := by have := (hv i).1; omega
  have hwnonneg : 0 ≤ w i + 6 := by have := (hw i).1; omega
  have hvcast : ((v i + 6).toNat : ℤ) = v i + 6 := by
    simp [Int.ofNat_toNat, max_eq_left hvnonneg]
  have hwcast : ((w i + 6).toNat : ℤ) = w i + 6 := by
    simp [Int.ofNat_toNat, max_eq_left hwnonneg]
  have : v i + 6 = w i + 6 := by rw [← hvcast, ← hwcast, hi]
  omega

/-- A finite reflection-closed root family with a checked diagonal moment. -/
structure ADERootOrbitCertificate (t : ADEType) where
  /-- Number of listed roots.  It may be zero for a rank-zero formal type. -/
  rootCount : ℕ
  /-- Listed vectors. -/
  root : Fin rootCount → Fin t.rank → ℤ
  /-- Stored fingerprints of the listed vectors. -/
  fingerprint : Fin rootCount → ℕ
  /-- Every stored fingerprint is recomputed from its vector by Lean. -/
  fingerprint_eq : ∀ a, fingerprint a = rootVectorFingerprint (root a)
  /-- Stored fingerprints distinguish the listed vectors. -/
  fingerprint_injective : Function.Injective fingerprint
  /-- Every listed coordinate is a valid base-thirteen digit after shifting. -/
  coordinate_bound : ∀ a i, -6 ≤ root a i ∧ root a i ≤ 6
  /-- Every listed vector has norm two. -/
  norm_two : ∀ a, Matrix.toBilin' t.gram (root a) (root a) = 2
  /-- Index of each standard simple root. -/
  simpleIndex : Fin t.rank → Fin rootCount
  /-- The indexed vector really is that simple root. -/
  simple_eq : ∀ i j, root (simpleIndex i) j =
    ((Pi.single i (1 : ℤ)) : Fin t.rank → ℤ) j
  /-- Index of the negative of a listed root. -/
  negIndex : Fin rootCount → Fin rootCount
  /-- Negation table check. -/
  neg_eq : ∀ a j, root (negIndex a) j = -root a j
  /-- Index of reflection in a standard simple root. -/
  reflectionIndex : Fin t.rank → Fin rootCount → Fin rootCount
  /-- Stored pairing with the reflecting simple root. -/
  reflectionPairing : Fin t.rank → Fin rootCount → ℤ
  /-- The stored pairing is recomputed once by Lean. -/
  reflectionPairing_eq : ∀ i a,
    reflectionPairing i a = adeSimplePairing t (root a) i
  /-- Reflection table check, compressed to the collision-free vector code. -/
  reflection_fingerprint : ∀ i a,
    fingerprint (reflectionIndex i a) =
      rootVectorFingerprint
        (adeCoordinateReflectionWithPairing i (reflectionPairing i a) (root a))
  /-- Only coordinate `i` changes under reflection; this check shows that the
  changed coordinate remains in the collision-free coding interval. -/
  reflection_changedCoordinate_bound : ∀ i a,
    -6 ≤ root a i - reflectionPairing i a ∧
      root a i - reflectionPairing i a ≤ 6
  /-- The checked orbit has the standard number `rank * h` of roots. -/
  rootCount_eq_rank_mul_coxeter : rootCount = t.rank * t.coxeterNumber

namespace ADERootOrbitCertificate

/-- The listed root family as an embedding. -/
def rootEmbedding {t : ADEType} (C : ADERootOrbitCertificate t) :
    Fin C.rootCount ↪ (Fin t.rank → ℤ) where
  toFun := C.root
  inj' := by
    intro a b h
    apply C.fingerprint_injective
    rw [C.fingerprint_eq, C.fingerprint_eq, h]

@[simp]
theorem rootEmbedding_apply {t : ADEType}
    (C : ADERootOrbitCertificate t) (a : Fin C.rootCount) :
    C.rootEmbedding a = C.root a :=
  rfl

/-- The certificate contains no duplicate root vectors. -/
theorem root_injective {t : ADEType} (C : ADERootOrbitCertificate t) :
    Function.Injective C.root :=
  C.rootEmbedding.injective

/-- The two compressed reflection checks imply the full vector identity. -/
theorem reflection_eq {t : ADEType} (C : ADERootOrbitCertificate t)
    (i : Fin t.rank) (a : Fin C.rootCount) :
    C.root (C.reflectionIndex i a) =
      adeCoordinateReflection t i (C.root a) := by
  rw [show adeCoordinateReflection t i (C.root a) =
      adeCoordinateReflectionWithPairing i (C.reflectionPairing i a) (C.root a) by
    rw [C.reflectionPairing_eq]
    rw [adeSimplePairing_eq_toBilin']
    rfl]
  apply rootVectorFingerprint_injective_of_bound (C.coordinate_bound _)
  · intro j
    classical
    by_cases hji : j = i
    · subst j
      simpa [adeCoordinateReflectionWithPairing] using
        C.reflection_changedCoordinate_bound i a
    · simpa [adeCoordinateReflectionWithPairing, Pi.single_apply, hji] using
        C.coordinate_bound a j
  · calc
      rootVectorFingerprint (C.root (C.reflectionIndex i a)) =
          C.fingerprint (C.reflectionIndex i a) :=
        (C.fingerprint_eq _).symm
      _ = rootVectorFingerprint
          (adeCoordinateReflectionWithPairing i (C.reflectionPairing i a) (C.root a)) :=
        C.reflection_fingerprint i a

end ADERootOrbitCertificate

end Lattice
end SRG266
