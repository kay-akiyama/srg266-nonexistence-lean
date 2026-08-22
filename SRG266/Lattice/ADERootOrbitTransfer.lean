/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.NormTwoRootOrbit
import SRG266.Lattice.ADERootOrbitCertificate
import SRG266.Lattice.NormTwoADEDecomposition

/-!
# Orthogonal sums of certified ADE root orbits

The generated certificates describe one irreducible ADE component at a time.
This module combines an arbitrary list of them in recursive block coordinates.
The resulting family has one occurrence for every root of every component,
contains all standard simple roots, and is closed under negation and all
simple reflections.  It is the coordinate-level input to
`NormTwoRootOrbitCertificate`.
-/

namespace SRG266
namespace Lattice

/-- A certificate for every occurrence in an ADE component list. -/
def ADEOrbitFamily : List ADEType → Type
  | [] => PUnit
  | t :: ts => ADERootOrbitCertificate t × ADEOrbitFamily ts

/-- Disjoint union of the listed root indices, preserving repeated component
occurrences. -/
def ADEOrbitIndex : (ts : List ADEType) → ADEOrbitFamily ts → Type
  | [], _ => Empty
  | _ :: ts, C => Fin C.1.rootCount ⊕ ADEOrbitIndex ts C.2

instance adeOrbitIndexFintype :
    ∀ (ts : List ADEType) (C : ADEOrbitFamily ts), Fintype (ADEOrbitIndex ts C)
  | [], _ => Fintype.ofEquiv Empty (Equiv.refl Empty)
  | _ :: ts, C => by
      letI := adeOrbitIndexFintype ts C.2
      exact inferInstanceAs (Fintype (Fin C.1.rootCount ⊕ ADEOrbitIndex ts C.2))

/-- A listed root in recursive block coordinates. -/
def adeOrbitBlockRoot : ∀ (ts : List ADEType) (C : ADEOrbitFamily ts),
    ADEOrbitIndex ts C → ADEBlockIndex ts → ℤ
  | [], _, a, _ => nomatch a
  | _ :: _, C, Sum.inl a, Sum.inl i => C.1.root a i
  | _ :: _, _, Sum.inl _, Sum.inr _ => 0
  | _ :: _, _, Sum.inr _, Sum.inl _ => 0
  | _ :: ts, C, Sum.inr a, Sum.inr i => adeOrbitBlockRoot ts C.2 a i

/-- A listed root in the contiguous coordinates used by `adeGram`. -/
def adeOrbitRoot (ts : List ADEType) (C : ADEOrbitFamily ts)
    (a : ADEOrbitIndex ts C) : Fin (ADEType.rankSum ts) → ℤ :=
  fun i => adeOrbitBlockRoot ts C a (finADEBlockEquiv ts i)

/-- Index of the listed standard simple root at a recursive block coordinate. -/
def adeOrbitSimpleIndex : ∀ (ts : List ADEType) (C : ADEOrbitFamily ts),
    ADEBlockIndex ts → ADEOrbitIndex ts C
  | [], _, i => nomatch i
  | _ :: _, C, Sum.inl i => Sum.inl (C.1.simpleIndex i)
  | _ :: ts, C, Sum.inr i => Sum.inr (adeOrbitSimpleIndex ts C.2 i)

/-- Certified negation on the orthogonal union. -/
def adeOrbitNegIndex : ∀ (ts : List ADEType) (C : ADEOrbitFamily ts),
    ADEOrbitIndex ts C → ADEOrbitIndex ts C
  | [], _, a => nomatch a
  | _ :: _, C, Sum.inl a => Sum.inl (C.1.negIndex a)
  | _ :: ts, C, Sum.inr a => Sum.inr (adeOrbitNegIndex ts C.2 a)

/-- Certified reflection in a standard simple root.  Roots in a different
orthogonal component are fixed. -/
def adeOrbitReflectionIndex : ∀ (ts : List ADEType) (C : ADEOrbitFamily ts),
    ADEBlockIndex ts → ADEOrbitIndex ts C → ADEOrbitIndex ts C
  | [], _, i, _ => nomatch i
  | _ :: _, C, Sum.inl i, Sum.inl a => Sum.inl (C.1.reflectionIndex i a)
  | _ :: _, _, Sum.inl _, Sum.inr a => Sum.inr a
  | _ :: _, _, Sum.inr _, Sum.inl a => Sum.inl a
  | _ :: ts, C, Sum.inr i, Sum.inr a =>
      Sum.inr (adeOrbitReflectionIndex ts C.2 i a)

/-- Pairing of a listed root with a standard simple root, evaluated in its
component.  Orthogonal components contribute zero definitionally. -/
def adeOrbitSimplePairing : ∀ (ts : List ADEType) (C : ADEOrbitFamily ts),
    ADEBlockIndex ts → ADEOrbitIndex ts C → ℤ
  | [], _, i, _ => nomatch i
  | _ :: _, C, Sum.inl i, Sum.inl a => C.1.reflectionPairing i a
  | _ :: _, _, Sum.inl _, Sum.inr _ => 0
  | _ :: _, _, Sum.inr _, Sum.inl _ => 0
  | _ :: ts, C, Sum.inr i, Sum.inr a => adeOrbitSimplePairing ts C.2 i a

@[simp]
theorem piSingle_sum_inl {t : ADEType} {ts : List ADEType}
    (i j : Fin t.rank) :
    ((Pi.single (Sum.inl i) (1 : ℤ)) :
      (Fin t.rank ⊕ ADEBlockIndex ts) → ℤ) (Sum.inl j) =
        ((Pi.single i (1 : ℤ)) : Fin t.rank → ℤ) j := by
  simp only [Pi.single_apply]
  simp only [Sum.inl.injEq]

@[simp]
theorem piSingle_sum_inr {t : ADEType} {ts : List ADEType}
    (i j : ADEBlockIndex ts) :
    ((Pi.single (Sum.inr i) (1 : ℤ)) :
      (Fin t.rank ⊕ ADEBlockIndex ts) → ℤ) (Sum.inr j) =
        ((Pi.single i (1 : ℤ)) : ADEBlockIndex ts → ℤ) j := by
  simp only [Pi.single_apply]
  simp only [Sum.inr.injEq]

@[simp]
theorem adeOrbitBlockRoot_simple :
    ∀ (ts : List ADEType) (C : ADEOrbitFamily ts) (i j : ADEBlockIndex ts),
      adeOrbitBlockRoot ts C (adeOrbitSimpleIndex ts C i) j =
        ((Pi.single i (1 : ℤ)) : ADEBlockIndex ts → ℤ) j
  | [], _, i, _ => nomatch i
  | t :: ts, C, Sum.inl i, Sum.inl j => by
      simp only [adeOrbitBlockRoot, adeOrbitSimpleIndex]
      rw [C.1.simple_eq]
      simp only [Pi.single_apply]
      change (if j = i then 1 else 0) =
        if (Sum.inl j : Fin t.rank ⊕ ADEBlockIndex ts) = Sum.inl i then 1 else 0
      simp only [Sum.inl.injEq]
  | _ :: _, _, Sum.inl _, Sum.inr _ => by
      simp [adeOrbitBlockRoot, adeOrbitSimpleIndex]
  | _ :: _, _, Sum.inr _, Sum.inl _ => by
      simp [adeOrbitBlockRoot, adeOrbitSimpleIndex]
  | t :: ts, C, Sum.inr i, Sum.inr j => by
      simp only [adeOrbitBlockRoot, adeOrbitSimpleIndex]
      rw [adeOrbitBlockRoot_simple ts C.2 i j]
      simp only [Pi.single_apply]
      change (if j = i then 1 else 0) =
        if (Sum.inr j : Fin t.rank ⊕ ADEBlockIndex ts) = Sum.inr i then 1 else 0
      simp only [Sum.inr.injEq]

@[simp]
theorem adeOrbitBlockRoot_neg :
    ∀ (ts : List ADEType) (C : ADEOrbitFamily ts)
      (a : ADEOrbitIndex ts C) (i : ADEBlockIndex ts),
      adeOrbitBlockRoot ts C (adeOrbitNegIndex ts C a) i =
        -adeOrbitBlockRoot ts C a i
  | [], _, a, _ => nomatch a
  | _ :: _, C, Sum.inl a, Sum.inl i => C.1.neg_eq a i
  | _ :: _, _, Sum.inl _, Sum.inr _ => by simp [adeOrbitBlockRoot, adeOrbitNegIndex]
  | _ :: _, _, Sum.inr _, Sum.inl _ => by simp [adeOrbitBlockRoot, adeOrbitNegIndex]
  | _ :: ts, C, Sum.inr a, Sum.inr i => adeOrbitBlockRoot_neg ts C.2 a i

@[simp]
theorem adeOrbitBlockRoot_reflection :
    ∀ (ts : List ADEType) (C : ADEOrbitFamily ts)
      (s : ADEBlockIndex ts) (a : ADEOrbitIndex ts C) (j : ADEBlockIndex ts),
      adeOrbitBlockRoot ts C (adeOrbitReflectionIndex ts C s a) j =
        adeOrbitBlockRoot ts C a j -
          adeOrbitSimplePairing ts C s a •
            ((Pi.single s (1 : ℤ)) : ADEBlockIndex ts → ℤ) j
  | [], _, s, _, _ => nomatch s
  | t :: ts, (Ct, Cs), Sum.inl s, Sum.inl a, Sum.inl j => by
      simp only [adeOrbitBlockRoot, adeOrbitReflectionIndex, adeOrbitSimplePairing]
      rw [Ct.reflection_eq]
      simp only [adeCoordinateReflection, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [← adeSimplePairing_eq_toBilin', Ct.reflectionPairing_eq]
      change Ct.root a j - adeSimplePairing _ (Ct.root a) s *
          (((Pi.single s (1 : ℤ)) : Fin t.rank → ℤ) j) =
        Ct.root a j - adeSimplePairing _ (Ct.root a) s *
          (((Pi.single (Sum.inl s) (1 : ℤ)) :
            (Fin t.rank ⊕ ADEBlockIndex ts) → ℤ) (Sum.inl j))
      rw [piSingle_sum_inl]
  | _ :: _, _, Sum.inl _, Sum.inl _, Sum.inr _ => by
      simp [adeOrbitBlockRoot, adeOrbitReflectionIndex, adeOrbitSimplePairing]
  | _ :: _, _, Sum.inl _, Sum.inr _, Sum.inl _ => by
      simp [adeOrbitBlockRoot, adeOrbitReflectionIndex, adeOrbitSimplePairing]
  | _ :: _, _, Sum.inl _, Sum.inr _, Sum.inr _ => by
      simp [adeOrbitBlockRoot, adeOrbitReflectionIndex, adeOrbitSimplePairing]
  | _ :: _, _, Sum.inr _, Sum.inl _, Sum.inl _ => by
      simp [adeOrbitBlockRoot, adeOrbitReflectionIndex, adeOrbitSimplePairing]
  | _ :: _, _, Sum.inr _, Sum.inl _, Sum.inr _ => by
      simp [adeOrbitBlockRoot, adeOrbitReflectionIndex, adeOrbitSimplePairing]
  | _ :: _, _, Sum.inr _, Sum.inr _, Sum.inl _ => by
      simp [adeOrbitBlockRoot, adeOrbitReflectionIndex, adeOrbitSimplePairing]
  | t :: ts, (Ct, Cs), Sum.inr s, Sum.inr a, Sum.inr j => by
      simp only [adeOrbitBlockRoot, adeOrbitReflectionIndex, adeOrbitSimplePairing]
      change adeOrbitBlockRoot ts Cs (adeOrbitReflectionIndex ts Cs s a) j =
        adeOrbitBlockRoot ts Cs a j - adeOrbitSimplePairing ts Cs s a *
          (((Pi.single (Sum.inr s) (1 : ℤ)) :
            (Fin t.rank ⊕ ADEBlockIndex ts) → ℤ) (Sum.inr j))
      rw [piSingle_sum_inr]
      exact adeOrbitBlockRoot_reflection ts Cs s a j

/-- Bilinear form of an ADE sum in recursive block coordinates. -/
def adeBlockBilin (ts : List ADEType)
    (x y : ADEBlockIndex ts → ℤ) : ℤ :=
  ∑ i, ∑ j, x i * (adeBlockPairing ts i j * y j)

/-- `finADEBlockEquiv` transports the matrix bilinear form to the recursive
block bilinear form. -/
theorem adeGram_toBilin'_eq_adeBlockBilin (ts : List ADEType)
    (x y : ADEBlockIndex ts → ℤ) :
    Matrix.toBilin' (adeGram ts).2
        (fun i => x (finADEBlockEquiv ts i))
        (fun i => y (finADEBlockEquiv ts i)) =
      adeBlockBilin ts x y := by
  classical
  rw [Matrix.toBilin'_apply, adeBlockBilin]
  simp_rw [mul_assoc]
  change (∑ i : Fin (ADEType.rankSum ts),
      ∑ j : Fin (ADEType.rankSum ts),
        x (finADEBlockEquiv ts i) *
          ((adeGram ts).2 i j * y (finADEBlockEquiv ts j))) =
    ∑ i : ADEBlockIndex ts, ∑ j : ADEBlockIndex ts,
      x i * (adeBlockPairing ts i j * y j)
  have hinner (i : Fin (ADEType.rankSum ts)) :
      (∑ j : Fin (ADEType.rankSum ts),
        x (finADEBlockEquiv ts i) *
          ((adeGram ts).2 i j * y (finADEBlockEquiv ts j))) =
      ∑ j : ADEBlockIndex ts,
        x (finADEBlockEquiv ts i) *
          (adeBlockPairing ts (finADEBlockEquiv ts i) j * y j) := by
    rw [← (finADEBlockEquiv ts).sum_comp]
    apply Finset.sum_congr rfl
    intro j _
    rw [adeGram_apply_eq_adeBlockPairing]
  calc
    _ = ∑ i : Fin (ADEType.rankSum ts), ∑ j : ADEBlockIndex ts,
        x (finADEBlockEquiv ts i) *
          (adeBlockPairing ts (finADEBlockEquiv ts i) j * y j) :=
      Finset.sum_congr rfl fun i _ => hinner i
    _ = _ := (finADEBlockEquiv ts).sum_comp
      (fun i => ∑ j, x i * (adeBlockPairing ts i j * y j))

/-- Recursive expansion of the block bilinear form. -/
theorem adeBlockBilin_cons (t : ADEType) (ts : List ADEType)
    (x y : ADEBlockIndex (t :: ts) → ℤ) :
    adeBlockBilin (t :: ts) x y =
      (∑ i : Fin t.rank, ∑ j : Fin t.rank,
        x (Sum.inl i) * (t.gram i j * y (Sum.inl j))) +
      adeBlockBilin ts (fun i => x (Sum.inr i)) (fun i => y (Sum.inr i)) := by
  classical
  unfold adeBlockBilin
  change (∑ i : Fin t.rank ⊕ ADEBlockIndex ts,
      ∑ j : Fin t.rank ⊕ ADEBlockIndex ts,
        x i * (adeBlockPairing (t :: ts) i j * y j)) = _
  simp only [Fintype.sum_sum_type, adeBlockPairing]
  simp

/-- Every listed orthogonal-sum vector has norm two. -/
theorem adeOrbitBlockRoot_norm_two :
    ∀ (ts : List ADEType) (C : ADEOrbitFamily ts)
      (a : ADEOrbitIndex ts C),
      adeBlockBilin ts (adeOrbitBlockRoot ts C a)
        (adeOrbitBlockRoot ts C a) = 2
  | [], _, a => nomatch a
  | t :: ts, (Ct, Cs), Sum.inl a => by
      rw [adeBlockBilin_cons]
      simpa [adeOrbitBlockRoot, adeBlockBilin, Matrix.toBilin'_apply,
        ← mul_assoc] using Ct.norm_two a
  | t :: ts, (Ct, Cs), Sum.inr a => by
      rw [adeBlockBilin_cons]
      simpa [adeOrbitBlockRoot, adeBlockBilin] using
        adeOrbitBlockRoot_norm_two ts Cs a

/-- The contiguous listed vector has norm two for `adeGram`. -/
theorem adeOrbitRoot_norm_two (ts : List ADEType) (C : ADEOrbitFamily ts)
    (a : ADEOrbitIndex ts C) :
    Matrix.toBilin' (adeGram ts).2 (adeOrbitRoot ts C a)
      (adeOrbitRoot ts C a) = 2 := by
  exact (adeGram_toBilin'_eq_adeBlockBilin ts _ _).trans
    (adeOrbitBlockRoot_norm_two ts C a)

/-- A certified norm-two coordinate vector is nonzero. -/
theorem ADERootOrbitCertificate.root_ne_zero {t : ADEType}
    (C : ADERootOrbitCertificate t) (a : Fin C.rootCount) :
    C.root a ≠ 0 := by
  intro hzero
  have hnorm := C.norm_two a
  rw [hzero] at hnorm
  simp at hnorm

/-- Distinct indices in the orthogonal union give distinct block vectors. -/
theorem adeOrbitBlockRoot_injective :
    ∀ (ts : List ADEType) (C : ADEOrbitFamily ts),
      Function.Injective (adeOrbitBlockRoot ts C)
  | [], _, a, _ => nomatch a
  | t :: ts, (Ct, Cs), a, b => by
      cases a with
      | inl a =>
          cases b with
          | inl b =>
              intro h
              apply congrArg Sum.inl
              apply Ct.root_injective
              funext i
              exact congrFun h (Sum.inl i)
          | inr b =>
              intro h
              exfalso
              apply Ct.root_ne_zero a
              funext i
              have hi := congrFun h (Sum.inl i)
              simpa [adeOrbitBlockRoot] using hi
      | inr a =>
          cases b with
          | inl b =>
              intro h
              exfalso
              apply Ct.root_ne_zero b
              funext i
              have hi := congrFun h (Sum.inl i)
              simpa [adeOrbitBlockRoot] using hi.symm
          | inr b =>
              intro h
              apply congrArg Sum.inr
              apply adeOrbitBlockRoot_injective ts Cs
              funext i
              exact congrFun h (Sum.inr i)

/-- Distinct indices also give distinct contiguous vectors. -/
theorem adeOrbitRoot_injective (ts : List ADEType) (C : ADEOrbitFamily ts) :
    Function.Injective (adeOrbitRoot ts C) := by
  intro a b h
  apply adeOrbitBlockRoot_injective ts C
  funext i
  have hi := congrFun h ((finADEBlockEquiv ts).symm i)
  simpa [adeOrbitRoot] using hi

@[simp]
theorem piSingle_equiv {I J : Type} [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (i j : I) :
    ((Pi.single (e i) (1 : ℤ)) : J → ℤ) (e j) =
      ((Pi.single i (1 : ℤ)) : I → ℤ) j := by
  by_cases hji : j = i
  · subst j
    simp
  · have he : e j ≠ e i := fun h => hji (e.injective h)
    simp [hji, he]

/-- The recursive simple-root index gives the corresponding contiguous basis
vector. -/
theorem adeOrbitRoot_simple (ts : List ADEType) (C : ADEOrbitFamily ts)
    (i : Fin (ADEType.rankSum ts)) :
    adeOrbitRoot ts C
        (adeOrbitSimpleIndex ts C (finADEBlockEquiv ts i)) =
      Pi.single i (1 : ℤ) := by
  funext j
  simp only [adeOrbitRoot, adeOrbitBlockRoot_simple]
  exact piSingle_equiv (finADEBlockEquiv ts) i j

/-- Negation of a listed contiguous vector is certified componentwise. -/
theorem adeOrbitRoot_neg (ts : List ADEType) (C : ADEOrbitFamily ts)
    (a : ADEOrbitIndex ts C) :
    adeOrbitRoot ts C (adeOrbitNegIndex ts C a) = -adeOrbitRoot ts C a := by
  funext i
  exact adeOrbitBlockRoot_neg ts C a (finADEBlockEquiv ts i)

/-- The block bilinear pairing with a standard simple root is the stored
component pairing. -/
theorem adeOrbitBlockRoot_pair_simple :
    ∀ (ts : List ADEType) (C : ADEOrbitFamily ts)
      (a : ADEOrbitIndex ts C) (s : ADEBlockIndex ts),
      adeBlockBilin ts (adeOrbitBlockRoot ts C a)
          ((Pi.single s (1 : ℤ)) : ADEBlockIndex ts → ℤ) =
        adeOrbitSimplePairing ts C s a
  | [], _, a, _ => nomatch a
  | t :: ts, (Ct, Cs), Sum.inl a, Sum.inl s => by
      rw [adeBlockBilin_cons]
      simp only [adeOrbitBlockRoot, adeOrbitSimplePairing]
      rw [Ct.reflectionPairing_eq, adeSimplePairing_eq_toBilin',
        Matrix.toBilin'_apply]
      change (∑ i : Fin t.rank, ∑ j : Fin t.rank,
          Ct.root a i * (t.gram i j *
            (((Pi.single (Sum.inl s) (1 : ℤ)) :
              (Fin t.rank ⊕ ADEBlockIndex ts) → ℤ) (Sum.inl j)))) +
          adeBlockBilin ts (fun _ => 0) (fun i =>
            (((Pi.single (Sum.inl s) (1 : ℤ)) :
              (Fin t.rank ⊕ ADEBlockIndex ts) → ℤ) (Sum.inr i))) =
        ∑ i : Fin t.rank, ∑ j : Fin t.rank,
          Ct.root a i * t.gram i j *
            (((Pi.single s (1 : ℤ)) : Fin t.rank → ℤ) j)
      simp [adeBlockBilin, ← mul_assoc]
  | t :: ts, (Ct, Cs), Sum.inl a, Sum.inr s => by
      rw [adeBlockBilin_cons]
      simp [adeOrbitBlockRoot, adeOrbitSimplePairing, adeBlockBilin]
  | t :: ts, (Ct, Cs), Sum.inr a, Sum.inl s => by
      rw [adeBlockBilin_cons]
      simp [adeOrbitBlockRoot, adeOrbitSimplePairing, adeBlockBilin]
  | t :: ts, (Ct, Cs), Sum.inr a, Sum.inr s => by
      have hy : (fun i =>
          (((Pi.single (Sum.inr s) (1 : ℤ)) :
            (Fin t.rank ⊕ ADEBlockIndex ts) → ℤ) (Sum.inr i))) =
          ((Pi.single s (1 : ℤ)) : ADEBlockIndex ts → ℤ) := by
        funext i
        exact piSingle_sum_inr s i
      rw [adeBlockBilin_cons]
      simp only [adeOrbitBlockRoot, adeOrbitSimplePairing]
      simp only [zero_mul, Finset.sum_const_zero, zero_add]
      change adeBlockBilin ts (adeOrbitBlockRoot ts Cs a)
          (fun i => (((Pi.single (Sum.inr s) (1 : ℤ)) :
            (Fin t.rank ⊕ ADEBlockIndex ts) → ℤ) (Sum.inr i))) =
        adeOrbitSimplePairing ts Cs s a
      rw [hy]
      exact adeOrbitBlockRoot_pair_simple ts Cs a s

/-- Contiguous matrix pairing with a standard simple root. -/
theorem adeOrbitRoot_pair_simple (ts : List ADEType) (C : ADEOrbitFamily ts)
    (a : ADEOrbitIndex ts C) (i : Fin (ADEType.rankSum ts)) :
    Matrix.toBilin' (adeGram ts).2 (adeOrbitRoot ts C a)
        (Pi.single i (1 : ℤ)) =
      adeOrbitSimplePairing ts C (finADEBlockEquiv ts i) a := by
  have hy : ((Pi.single i (1 : ℤ)) : Fin (ADEType.rankSum ts) → ℤ) =
      fun j => ((Pi.single (finADEBlockEquiv ts i) (1 : ℤ)) :
        ADEBlockIndex ts → ℤ) (finADEBlockEquiv ts j) := by
    funext j
    exact (piSingle_equiv (finADEBlockEquiv ts) i j).symm
  calc
    Matrix.toBilin' (adeGram ts).2 (adeOrbitRoot ts C a)
        (Pi.single i (1 : ℤ)) =
        Matrix.toBilin' (adeGram ts).2 (adeOrbitRoot ts C a)
          (fun j => ((Pi.single (finADEBlockEquiv ts i) (1 : ℤ)) :
            ADEBlockIndex ts → ℤ) (finADEBlockEquiv ts j)) :=
      congrArg (fun y : Fin (ADEType.rankSum ts) → ℤ =>
        Matrix.toBilin' (adeGram ts).2 (adeOrbitRoot ts C a) y) hy
    _ = _ := (adeGram_toBilin'_eq_adeBlockBilin ts _ _).trans
      (adeOrbitBlockRoot_pair_simple ts C a (finADEBlockEquiv ts i))

/-- Reflection of a listed contiguous vector. -/
theorem adeOrbitRoot_reflection (ts : List ADEType) (C : ADEOrbitFamily ts)
    (i : Fin (ADEType.rankSum ts)) (a : ADEOrbitIndex ts C) :
    adeOrbitRoot ts C
        (adeOrbitReflectionIndex ts C (finADEBlockEquiv ts i) a) =
      adeOrbitRoot ts C a -
        adeOrbitSimplePairing ts C (finADEBlockEquiv ts i) a •
          Pi.single i (1 : ℤ) := by
  funext j
  simp only [adeOrbitRoot, Pi.sub_apply, Pi.smul_apply]
  rw [adeOrbitBlockRoot_reflection]
  congr 1
  exact congrArg (fun z : ℤ =>
    adeOrbitSimplePairing ts C (finADEBlockEquiv ts i) a • z)
      (piSingle_equiv (finADEBlockEquiv ts) i j)

/-! ## Transfer to the actual lattice -/

/-- A standard coordinate basis vector maps to its ordered simple root. -/
theorem coordinateRootMap_piSingle
    {n m : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} (coord : Fin m ≃ simpleRootSet f) (i : Fin m) :
    coordinateRootMap coord (Pi.single i (1 : ℤ)) =
      normTwoRootVal (coord i).1 := by
  classical
  rw [coordinateRootMap, Fintype.linearCombination_apply]
  simp
  letI : MulAction ℤ L.carrier := L.carrier.isModule.toMulAction
  exact one_smul ℤ _

/-- Map one certified ADE root into the actual lattice. -/
noncomputable def adeOrbitActualRoot
    {n : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} {ts : List ADEType}
    (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (coord : Fin (ADEType.rankSum ts) ≃ simpleRootSet f)
    (hgram : ∀ i j,
      graphCartanMatrix (simpleRootGraph f) (coord i) (coord j) =
        (adeGram ts).2 i j)
    (C : ADEOrbitFamily ts) (a : ADEOrbitIndex ts C) : NormTwoRoot L :=
  ⟨coordinateRootMap coord (adeOrbitRoot ts C a), by
    rw [coordinateRootMap_pairing hf coord (adeGram ts).2 hgram]
    exact adeOrbitRoot_norm_two ts C a⟩

/-- The actual listed-root map is injective. -/
theorem adeOrbitActualRoot_injective
    {n : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} {ts : List ADEType}
    (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (coord : Fin (ADEType.rankSum ts) ≃ simpleRootSet f)
    (hgram : ∀ i j,
      graphCartanMatrix (simpleRootGraph f) (coord i) (coord j) =
        (adeGram ts).2 i j)
    (C : ADEOrbitFamily ts) :
    Function.Injective (adeOrbitActualRoot hf coord hgram C) := by
  intro a b hab
  apply adeOrbitRoot_injective ts C
  apply coordinateRootMap_injective hf coord
  exact congrArg Subtype.val hab

/-- The actual listed-root embedding. -/
noncomputable def adeOrbitActualRootEmbedding
    {n : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} {ts : List ADEType}
    (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (coord : Fin (ADEType.rankSum ts) ≃ simpleRootSet f)
    (hgram : ∀ i j,
      graphCartanMatrix (simpleRootGraph f) (coord i) (coord j) =
        (adeGram ts).2 i j)
    (C : ADEOrbitFamily ts) : ADEOrbitIndex ts C ↪ NormTwoRoot L :=
  ⟨adeOrbitActualRoot hf coord hgram C,
    adeOrbitActualRoot_injective hf coord hgram C⟩

/-- The transferred family contains every selected simple root. -/
theorem adeOrbitActualRoot_simple
    {n : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} {ts : List ADEType}
    (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (coord : Fin (ADEType.rankSum ts) ≃ simpleRootSet f)
    (hgram : ∀ i j,
      graphCartanMatrix (simpleRootGraph f) (coord i) (coord j) =
        (adeGram ts).2 i j)
    (C : ADEOrbitFamily ts) (s : simpleRootSet f) :
    adeOrbitActualRoot hf coord hgram C
        (adeOrbitSimpleIndex ts C
          (finADEBlockEquiv ts (coord.symm s))) = s.1 := by
  apply Subtype.ext
  simp only [adeOrbitActualRoot, adeOrbitRoot_simple,
    coordinateRootMap_piSingle, Equiv.apply_symm_apply]
  change s.1.1 = s.1.1
  rfl

/-- Pairing of an actual listed root with an actual simple root. -/
theorem adeOrbitActualRoot_pair_simple
    {n : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} {ts : List ADEType}
    (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (coord : Fin (ADEType.rankSum ts) ≃ simpleRootSet f)
    (hgram : ∀ i j,
      graphCartanMatrix (simpleRootGraph f) (coord i) (coord j) =
        (adeGram ts).2 i j)
    (C : ADEOrbitFamily ts) (a : ADEOrbitIndex ts C)
    (s : simpleRootSet f) :
    L.pairing (adeOrbitActualRoot hf coord hgram C a).1 s.1.1 =
      adeOrbitSimplePairing ts C
        (finADEBlockEquiv ts (coord.symm s)) a := by
  have hs : coordinateRootMap coord (Pi.single (coord.symm s) (1 : ℤ)) =
      s.1.1 := by
    rw [coordinateRootMap_piSingle, Equiv.apply_symm_apply]
    rfl
  change L.pairing (coordinateRootMap coord (adeOrbitRoot ts C a)) s.1.1 = _
  calc
    _ = L.pairing (coordinateRootMap coord (adeOrbitRoot ts C a))
        (coordinateRootMap coord (Pi.single (coord.symm s) (1 : ℤ))) := by
      rw [hs]
    _ = Matrix.toBilin' (adeGram ts).2 (adeOrbitRoot ts C a)
        (Pi.single (coord.symm s) (1 : ℤ)) :=
      coordinateRootMap_pairing hf coord (adeGram ts).2 hgram _ _
    _ = _ := adeOrbitRoot_pair_simple ts C a (coord.symm s)

/-- Transferred negation agrees with lattice negation. -/
theorem adeOrbitActualRoot_neg
    {n : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} {ts : List ADEType}
    (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (coord : Fin (ADEType.rankSum ts) ≃ simpleRootSet f)
    (hgram : ∀ i j,
      graphCartanMatrix (simpleRootGraph f) (coord i) (coord j) =
        (adeGram ts).2 i j)
    (C : ADEOrbitFamily ts) (a : ADEOrbitIndex ts C) :
    adeOrbitActualRoot hf coord hgram C (adeOrbitNegIndex ts C a) =
      -(adeOrbitActualRoot hf coord hgram C a) := by
  apply Subtype.ext
  simp [adeOrbitActualRoot, adeOrbitRoot_neg]

/-- Transferred simple reflection agrees with lattice reflection. -/
theorem adeOrbitActualRoot_reflection
    {n : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} {ts : List ADEType}
    (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (coord : Fin (ADEType.rankSum ts) ≃ simpleRootSet f)
    (hgram : ∀ i j,
      graphCartanMatrix (simpleRootGraph f) (coord i) (coord j) =
        (adeGram ts).2 i j)
    (C : ADEOrbitFamily ts) (s : simpleRootSet f)
    (a : ADEOrbitIndex ts C) :
    adeOrbitActualRoot hf coord hgram C
        (adeOrbitReflectionIndex ts C
          (finADEBlockEquiv ts (coord.symm s)) a) =
      reflectNormTwoRoot L s.1 (adeOrbitActualRoot hf coord hgram C a) := by
  apply Subtype.ext
  simp only [adeOrbitActualRoot, reflectNormTwoRoot_val]
  rw [adeOrbitRoot_reflection, map_sub, map_zsmul]
  have hp : L.pairing (coordinateRootMap coord (adeOrbitRoot ts C a)) s.1.1 =
      adeOrbitSimplePairing ts C (finADEBlockEquiv ts (coord.symm s)) a := by
    exact adeOrbitActualRoot_pair_simple hf coord hgram C a s
  have hs : coordinateRootMap coord (Pi.single (coord.symm s) (1 : ℤ)) =
      s.1.1 := by
    rw [coordinateRootMap_piSingle, Equiv.apply_symm_apply]
    rfl
  rw [hp, hs]

/-- Orthogonal ADE certificates form a complete actual root-orbit
certificate. -/
noncomputable def adeNormTwoRootOrbitCertificate
    {n : ℕ} {L : PDUnimodularLattice n} [Finite (NormTwoRoot L)]
    {f : L.carrier →+ ℤ} {ts : List ADEType}
    (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (coord : Fin (ADEType.rankSum ts) ≃ simpleRootSet f)
    (hgram : ∀ i j,
      graphCartanMatrix (simpleRootGraph f) (coord i) (coord j) =
        (adeGram ts).2 i j)
    (C : ADEOrbitFamily ts) : NormTwoRootOrbitCertificate L f where
  Index := ADEOrbitIndex ts C
  indexFintype := adeOrbitIndexFintype ts C
  root := adeOrbitActualRootEmbedding hf coord hgram C
  simpleIndex s := adeOrbitSimpleIndex ts C
    (finADEBlockEquiv ts (coord.symm s))
  simple_eq := adeOrbitActualRoot_simple hf coord hgram C
  negIndex := adeOrbitNegIndex ts C
  neg_eq := adeOrbitActualRoot_neg hf coord hgram C
  reflectionIndex s := adeOrbitReflectionIndex ts C
    (finADEBlockEquiv ts (coord.symm s))
  reflection_eq := adeOrbitActualRoot_reflection hf coord hgram C

end Lattice
end SRG266
