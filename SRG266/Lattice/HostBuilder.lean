/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.ExternalLatticeInputs
import SRG266.Lattice.Core
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Building rank-15 hosts from integer matrices

`SRG266.OddUnimodularLattice15` bundles its carrier as an object of
`ModuleCat ℤ`.  This file supplies the two services every consumer of that
structure needs.

* `SRG266.hostOfMatrix` turns a symmetric, invertible, positive-definite,
  odd integer `15 × 15` matrix into an `OddUnimodularLattice15`.  The
  positive-definiteness hypothesis is exactly the shape produced by the
  repository's `SRG266/Certificates/LDLT.lean` machinery.
  `SRG266.standardHost15` is the resulting term for the identity matrix, which
  is also the concrete witness that the universe of
  `OddUnimodularLattice15.carrier` accepts a `Type 0` carrier.
* `SRG266.OddUnimodularLattice15.exists_orthonormal_normOneFree` transports the
  abstract norm-one splitting of `SRG266/Lattice/Core.lean` onto a bundled
  host.  The transport is the `Subsingleton.elim` bridge between the bundled
  `Module ℤ` instance of the carrier and the canonical
  `AddCommGroup.toIntModule`; see the module docstring of
  `SRG266/Lattice/Core.lean`.

## The instance bridge, and why it is needed

For `L : OddUnimodularLattice15`, `Module ℤ L.carrier` is the structure
projection `L.carrier.isModule`, which is *not* definitionally
`AddCommGroup.toIntModule`.  Consequently `L.pairing` cannot be handed
directly to a lemma stated with `[AddCommGroup M]` alone.  The two instances
are however propositionally equal, because `Module ℤ M` is a subsingleton.
`normOneSplitting_of_module` therefore takes the module instance as an
ordinary explicit argument, rewrites it with `Subsingleton.elim`, and only
then applies the abstract theory.  Adding `[Module ℤ M]` to the abstract
development instead is *not* an option: with both `[AddCommGroup M]` and
`[Module ℤ M]` in scope the `•` notation resolves through
`SubNegMonoid.toZSMul` while `Submodule ℤ M` resolves through the module
instance; the two are not definitionally equal.
-/

namespace SRG266

open scoped Matrix

/-! ## The bridge from a bundled module instance to the abstract theory -/

/-- The norm-one splitting, stated for a carrier whose `Module ℤ` instance is
an explicit argument rather than the canonical one.

This is the form in which `OddUnimodularLattice15` can consume
`SRG266.Lattice.exists_normOneSplitting`. -/
theorem normOneSplitting_of_module {X : Type*} [AddCommGroup X]
    (instMod : Module ℤ X)
    (pairing : @LinearMap.BilinForm ℤ _ X _ instMod)
    (hfin : @Module.Finite ℤ X _ _ instMod)
    (hsymm : pairing.IsSymm) (hbij : Function.Bijective pairing) :
    ∃ (k : ℕ) (u : Fin k → X),
      (∀ i, pairing (u i) (u i) = 1) ∧
      (∀ i j, i ≠ j → pairing (u i) (u j) = 0) ∧
      (∀ w : X, (∀ i, pairing (u i) w = 0) → pairing w w ≠ 1) ∧
      (∀ v : X, ∀ i, pairing (u i) (v - ∑ j, pairing (u j) v • u j) = 0) := by
  have hinst : instMod = AddCommGroup.toIntModule X := Subsingleton.elim _ _
  subst hinst
  obtain ⟨S⟩ := SRG266.Lattice.exists_normOneSplitting pairing hsymm hbij
  exact ⟨S.rank, S.units, S.units_norm, fun _ _ h => S.units_orthogonal h,
    fun w hw => S.core_normOneFree w (SRG266.Lattice.mem_unitPerp.mpr hw),
    fun v i => SRG266.Lattice.mem_unitPerp.mp (S.decompose v) i⟩

namespace OddUnimodularLattice15

/-- **Norm-one splitting for a bundled host.**  A rank-15 odd unimodular host
carries a maximal orthonormal family; the vectors orthogonal to all of them
form a norm-one-free complement, and every vector decomposes accordingly. -/
theorem exists_orthonormal_normOneFree (L : OddUnimodularLattice15) :
    ∃ (k : ℕ) (u : Fin k → L.carrier),
      (∀ i, L.pairing (u i) (u i) = 1) ∧
      (∀ i j, i ≠ j → L.pairing (u i) (u j) = 0) ∧
      (∀ w : L.carrier, (∀ i, L.pairing (u i) w = 0) → L.pairing w w ≠ 1) ∧
      (∀ v : L.carrier, ∀ i,
        L.pairing (u i) (v - ∑ j, L.pairing (u j) v • u j) = 0) :=
  normOneSplitting_of_module _ L.pairing L.moduleFinite L.symmetric L.unimodular

/-- Every host vector is an integral multiple
of a norm-one vector plus a vector orthogonal to it. -/
theorem norm_one_split (L : OddUnimodularLattice15) {u : L.carrier}
    (hu : L.pairing u u = 1) (v : L.carrier) :
    ∃ (a : ℤ) (w : L.carrier), v = a • u + w ∧ L.pairing u w = 0 := by
  refine ⟨L.pairing u v, v - (L.pairing u v) • u, by abel, ?_⟩
  have hsmul : L.pairing u ((L.pairing u v) • u) = L.pairing u v := by
    simp [hu]
  rw [map_sub, hsmul, sub_self]

end OddUnimodularLattice15

/-! ## Hosts from integer matrices -/

section MatrixHost

variable {n : ℕ}

/-- The Gram form of an integer matrix, written through `Matrix.vecMul`. -/
theorem toBilin'_eq_vecMul_dotProduct (A : Matrix (Fin n) (Fin n) ℤ)
    (v w : Fin n → ℤ) :
    Matrix.toBilin' A v w = dotProduct (Matrix.vecMul v A) w := by
  rw [Matrix.toBilin'_apply, dotProduct, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.vecMul_apply_eq_sum, Finset.sum_mul]

/-- An integer matrix with a right inverse gives a unimodular form. -/
theorem toBilin'_bijective_of_mul_eq_one (A Ainv : Matrix (Fin n) (Fin n) ℤ)
    (hinv : A * Ainv = 1) : Function.Bijective (Matrix.toBilin' A) := by
  classical
  have hinv' : Ainv * A = 1 := mul_eq_one_comm.mp hinv
  have hsingle : ∀ (j : Fin n) (a : ℤ),
      (Pi.single j a : Fin n → ℤ) = a • (Pi.single j 1 : Fin n → ℤ) := by
    intro j a
    funext i
    by_cases h : i = j <;> simp [h]
  constructor
  · intro v v' hvv'
    have hrow : Matrix.vecMul v A = Matrix.vecMul v' A := by
      funext j
      have h := congrArg (fun f => f (Pi.single j (1 : ℤ))) hvv'
      simpa only [toBilin'_eq_vecMul_dotProduct, dotProduct_single, mul_one] using h
    have hcancel := congrArg (fun x => Matrix.vecMul x Ainv) hrow
    simpa only [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one] using hcancel
  · intro φ
    refine ⟨Matrix.vecMul (fun j => φ (Pi.single j 1)) Ainv, ?_⟩
    have hrow : Matrix.vecMul (Matrix.vecMul (fun j => φ (Pi.single j (1 : ℤ))) Ainv) A =
        fun j => φ (Pi.single j (1 : ℤ)) := by
      rw [Matrix.vecMul_vecMul, hinv', Matrix.vecMul_one]
    refine LinearMap.ext fun w => ?_
    rw [toBilin'_eq_vecMul_dotProduct, hrow]
    have hw : w = ∑ j, w j • (Pi.single j 1 : Fin n → ℤ) := by
      conv_lhs => rw [← Finset.univ_sum_single w]
      exact Finset.sum_congr rfl fun j _ => hsingle j (w j)
    conv_rhs => rw [hw]
    rw [map_sum, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]

/-- The Gram value of an integer matrix on the first standard basis vector. -/
theorem toBilin'_single_zero (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) :
    Matrix.toBilin' A (Pi.single 0 1) (Pi.single 0 1) = A 0 0 := by
  rw [toBilin'_eq_vecMul_dotProduct, dotProduct_single, mul_one,
    Matrix.vecMul_apply_eq_sum, Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ 0) h

/-- A symmetric matrix gives a symmetric form. -/
theorem toBilin'_isSymm (A : Matrix (Fin n) (Fin n) ℤ) (hsym : A.IsSymm) :
    (Matrix.toBilin' A).IsSymm := by
  refine ⟨fun x y => ?_⟩
  simp only [Matrix.toBilin'_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hA : A j i = A i j := congrFun (congrFun hsym i) j
  rw [hA]
  ring

end MatrixHost

/-- **Host builder (SI-2).**  A symmetric, invertible, positive-definite, odd
integer `15 × 15` matrix is the Gram matrix of an odd unimodular rank-15
lattice. -/
noncomputable def hostOfMatrix (A Ainv : Matrix (Fin 15) (Fin 15) ℤ)
    (hsym : A.IsSymm) (hinv : A * Ainv = 1)
    (hpd : ∀ v : Fin 15 → ℤ, v ≠ 0 → 0 < Matrix.toBilin' A v v)
    (hodd : ¬ Even (A 0 0)) : OddUnimodularLattice15 where
  carrier := ModuleCat.of ℤ (Fin 15 → ℤ)
  pairing := Matrix.toBilin' A
  symmetric := toBilin'_isSymm A hsym
  positiveDefinite := hpd
  odd := ⟨Pi.single 0 1, by rw [toBilin'_single_zero]; exact hodd⟩
  unimodular := toBilin'_bijective_of_mul_eq_one A Ainv hinv
  rank := Module.finrank_fin_fun ℤ

/-- The Gram form of the identity matrix is positive definite. -/
theorem toBilin'_one_posDef {n : ℕ} (v : Fin n → ℤ) (hv : v ≠ 0) :
    0 < Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) ℤ) v v := by
  classical
  rw [Matrix.toBilin'_apply]
  have hne : ∃ i, v i ≠ 0 := by
    by_contra h
    exact hv (funext fun i => not_not.mp fun hi => h ⟨i, hi⟩)
  obtain ⟨i₀, hi₀⟩ := hne
  have hterm : ∀ i : Fin n,
      (∑ j, v i * (1 : Matrix (Fin n) (Fin n) ℤ) i j * v j) = v i * v i := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · intro h
      exact absurd (Finset.mem_univ i) h
  simp_rw [hterm]
  exact Finset.sum_pos' (fun i _ => mul_self_nonneg (v i))
    ⟨i₀, Finset.mem_univ i₀, mul_self_pos.mpr hi₀⟩

/-- The standard rank-15 host `I₁₅`, built through `hostOfMatrix` on the
`Type 0` carrier `Fin 15 → ℤ`. -/
noncomputable def standardHost15 : OddUnimodularLattice15 :=
  hostOfMatrix 1 1 Matrix.isSymm_one (by simp) toBilin'_one_posDef (by decide)

end SRG266
