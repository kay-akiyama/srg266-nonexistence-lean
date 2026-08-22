/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.HostCertificate

/-!
# Root lattices of type ADE: vocabulary and certificate machinery

This file defines `ADEType`, its rank function, the block-diagonal Gram matrix
`adeGram`, and certificate machinery for the invariants of each irreducible
type.

## The Gram matrices are formulas, not data

`ADEType.gramEntry` is a closed formula on `ℕ` indices, so `adeGram` is a
*definition* of arbitrary rank, not a table.  The Dynkin diagrams are laid out
uniformly:

* `Aₙ` — the chain `0 — 1 — ⋯ — (n-1)`;
* `Dₙ` — the chain `0 — 1 — ⋯ — (n-2)` with the extra node `n-1` attached at
  `n-3`, so `D₄` is the star `K₁,₃` and `Dₙ` forks at its far end;
* `E₆`, `E₇`, `E₈` — the chain `0 — 1 — ⋯ — (n-2)` with the extra node `n-1`
  attached at node `2`, i.e. `T₂,₃,₃`, `T₂,₃,₄` and `T₂,₃,₅`.

`SRG266/Certificates/RootLatticeData.lean` therefore carries no Gram matrix at
all; it carries only certificate material.

## What a `RootLatticeCert` certifies

A `RootLatticeCert n` bundles a Gram matrix with

* a fraction-free (Bareiss) `LDLᵀ` factorization `scale • A = L * diag w * Lᵀ`
  whose lower factor is **triangular**.  Triangularity is what upgrades the
  factorization from a positive-semidefiniteness certificate to an exact
  determinant: `det L` is the product of the diagonal, so
  `scale ^ n * det A = (∏ L i i)² * ∏ w`;
* the adjugate `B` with `A * B = det A • 1`.  It makes the form nondegenerate,
  which turns semidefinite into definite, and the rational matrix `B / det A`
  is the Gram matrix of the dual basis — that is, the discriminant form written
  on the dual basis.

`SRG266.Lattice.toBilin'_posDef_of_ldlt_of_adjugate` is the non-unimodular
sibling of `SRG266.Lattice.toBilin'_posDef_of_ldlt`
(`SRG266/Lattice/HostCertificate.lean`), which assumes `A * Ainv = 1` and so
does not apply to a root lattice: `det Aₙ = n + 1`.  Both go through the same
radical argument, isolated here as
`SRG266.Lattice.vecMul_eq_zero_of_toBilin'_eq_zero`.

## Coset minima and the norm-three counter

`SRG266.Lattice.checkCosetMinima` compares closed-form coset minima with the
discriminant-form values computed from the adjugate. It checks the congruence
modulo `2ℤ` between each listed minimum and representative.

`SRG266.Lattice.normThreeRootEquiv` counts, for a norm-three vector `v`, the
norm-three vectors `w` with
`⟨v, w⟩ = 2`, and observes that the count coincides with the number of roots
`ρ` with `⟨v, ρ⟩ = 1` (`66`, `54`, `48` in `D₁₂⁺`, `(E₇⊕E₇)⁺`, `A₁₅⁺`).  The
coincidence is an involution, not an arithmetic accident: `w ↦ v - w` is a
bijection between the two sets, because `|v - w|² = 3 - 2·2 + 3 = 2`.  That
makes the counter a *root* count, which is a closed formula per glue group.
-/

namespace SRG266
namespace Lattice

open scoped Matrix

/-! ## The ADE types -/

/-- An irreducible root system of simply laced type. -/
inductive ADEType where
  /-- The type `Aₙ`, `n ≥ 1`. -/
  | A (n : ℕ)
  /-- The type `Dₙ`, `n ≥ 4`. -/
  | D (n : ℕ)
  /-- The type `E₆`. -/
  | E6
  /-- The type `E₇`. -/
  | E7
  /-- The type `E₈`. -/
  | E8
deriving DecidableEq, Repr

namespace ADEType

/-- The usual rank restrictions on irreducible simply-laced root types. -/
def IsRegular : ADEType → Prop
  | .A n => 1 ≤ n
  | .D n => 4 ≤ n
  | .E6 | .E7 | .E8 => True

instance (t : ADEType) : Decidable t.IsRegular := by
  cases t <;> simp only [IsRegular] <;> infer_instance

/-- The rank of an ADE type. -/
def rank : ADEType → ℕ
  | .A n => n
  | .D n => n
  | .E6 => 6
  | .E7 => 7
  | .E8 => 8

/-- The determinant of the Cartan matrix, i.e. the order of the discriminant
group `R*/R`.  Kernel-proved for every regular type of rank at most fifteen in
`SRG266/Lattice/RootLatticeCerts{A,D,E}.lean`. -/
def det : ADEType → ℤ
  | .A n => (n : ℤ) + 1
  | .D _ => 4
  | .E6 => 3
  | .E7 => 2
  | .E8 => 1

end ADEType

/-! ## Cartan matrices -/

/-- Entry `(i, j)` of the Cartan matrix of `Aₙ`: the chain `0 — ⋯ — (n-1)`. -/
def gramAEntry (i j : ℕ) : ℤ :=
  if i = j then 2 else if i + 1 = j ∨ j + 1 = i then -1 else 0

/-- Entry `(i, j)` of the Cartan matrix of `Dₙ`: the chain `0 — ⋯ — (n-2)`
with the extra node `n-1` attached at `n-3`. -/
def gramDEntry (n i j : ℕ) : ℤ :=
  if i = j then 2
  else if ((i + 1 = j ∨ j + 1 = i) ∧ i + 2 ≤ n ∧ j + 2 ≤ n) ∨
      (i + 3 = n ∧ j + 1 = n) ∨ (j + 3 = n ∧ i + 1 = n) then -1 else 0

/-- Entry `(i, j)` of the Cartan matrix of `Eₙ`: the chain `0 — ⋯ — (n-2)`
with the extra node `n-1` attached at node `2`. -/
def gramEEntry (n i j : ℕ) : ℤ :=
  if i = j then 2
  else if ((i + 1 = j ∨ j + 1 = i) ∧ i + 2 ≤ n ∧ j + 2 ≤ n) ∨
      (i = 2 ∧ j + 1 = n) ∨ (j = 2 ∧ i + 1 = n) then -1 else 0

/-- The Cartan matrix of `Aₙ`. -/
def gramA (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j => gramAEntry i.1 j.1

/-- The Cartan matrix of `Dₙ`. -/
def gramD (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j => gramDEntry n i.1 j.1

/-- The Cartan matrix of `Eₙ`, `n ∈ {6, 7, 8}`. -/
def gramE (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j => gramEEntry n i.1 j.1

theorem gramAEntry_symm (i j : ℕ) : gramAEntry i j = gramAEntry j i := by
  unfold gramAEntry
  split_ifs <;> omega

theorem gramDEntry_symm (n i j : ℕ) : gramDEntry n i j = gramDEntry n j i := by
  unfold gramDEntry
  split_ifs <;> omega

theorem gramEEntry_symm (n i j : ℕ) : gramEEntry n i j = gramEEntry n j i := by
  unfold gramEEntry
  split_ifs <;> omega

namespace ADEType

/-- Entry `(i, j)` of the Cartan matrix of an irreducible type. -/
def gramEntry : ADEType → ℕ → ℕ → ℤ
  | .A _, i, j => gramAEntry i j
  | .D n, i, j => gramDEntry n i j
  | .E6, i, j => gramEEntry 6 i j
  | .E7, i, j => gramEEntry 7 i j
  | .E8, i, j => gramEEntry 8 i j

/-- The Cartan matrix of an irreducible type. -/
def gram (t : ADEType) : Matrix (Fin t.rank) (Fin t.rank) ℤ :=
  fun i j => t.gramEntry i.1 j.1

theorem gramEntry_symm (t : ADEType) (i j : ℕ) : t.gramEntry i j = t.gramEntry j i := by
  cases t with
  | A _ => exact gramAEntry_symm i j
  | D n => exact gramDEntry_symm n i j
  | E6 => exact gramEEntry_symm 6 i j
  | E7 => exact gramEEntry_symm 7 i j
  | E8 => exact gramEEntry_symm 8 i j

theorem gramEntry_diag (t : ADEType) (i : ℕ) : t.gramEntry i i = 2 := by
  cases t <;> simp [gramEntry, gramAEntry, gramDEntry, gramEEntry]

/-- The rank of a list of types. -/
def rankSum (ts : List ADEType) : ℕ := (ts.map rank).sum

@[simp] theorem rankSum_nil : rankSum [] = 0 := rfl

@[simp] theorem rankSum_cons (t : ADEType) (ts : List ADEType) :
    rankSum (t :: ts) = t.rank + rankSum ts := rfl

end ADEType

/-! ## The block-diagonal Gram matrix of a list of types -/

/-- Entry `(i, j)` of the orthogonal direct sum of the Cartan matrices of a
list of types, the blocks being laid out in order. -/
def adeEntry : List ADEType → ℕ → ℕ → ℤ
  | [], _, _ => 0
  | t :: ts, i, j =>
      if i < t.rank ∧ j < t.rank then t.gramEntry i j
      else if t.rank ≤ i ∧ t.rank ≤ j then adeEntry ts (i - t.rank) (j - t.rank)
      else 0

/-- **The Gram matrix of a list of ADE types**, together with its rank.  This
is the `adeGram` of the residual input `RootLatticeIsADE`. -/
def adeGram (ts : List ADEType) : (n : ℕ) × Matrix (Fin n) (Fin n) ℤ :=
  ⟨ADEType.rankSum ts, fun i j => adeEntry ts i.1 j.1⟩

theorem adeEntry_symm : ∀ (ts : List ADEType) (i j : ℕ), adeEntry ts i j = adeEntry ts j i
  | [], _, _ => rfl
  | t :: ts, i, j => by
      by_cases h₁ : i < t.rank ∧ j < t.rank
      · have h₁' : j < t.rank ∧ i < t.rank := ⟨h₁.2, h₁.1⟩
        simp only [adeEntry, if_pos h₁, if_pos h₁']
        exact t.gramEntry_symm i j
      · have h₁' : ¬ (j < t.rank ∧ i < t.rank) := fun h => h₁ ⟨h.2, h.1⟩
        by_cases h₂ : t.rank ≤ i ∧ t.rank ≤ j
        · have h₂' : t.rank ≤ j ∧ t.rank ≤ i := ⟨h₂.2, h₂.1⟩
          simp only [adeEntry, if_neg h₁, if_neg h₁', if_pos h₂, if_pos h₂']
          exact adeEntry_symm ts (i - t.rank) (j - t.rank)
        · have h₂' : ¬ (t.rank ≤ j ∧ t.rank ≤ i) := fun h => h₂ ⟨h.2, h.1⟩
          simp only [adeEntry, if_neg h₁, if_neg h₁', if_neg h₂, if_neg h₂']

theorem adeGram_isSymm (ts : List ADEType) : (adeGram ts).2.IsSymm := by
  ext i j
  exact adeEntry_symm ts j.1 i.1

/-- A one-element list reproduces the Cartan matrix of the type. -/
theorem adeEntry_singleton (t : ADEType) {i j : ℕ} (hi : i < t.rank) (hj : j < t.rank) :
    adeEntry [t] i j = t.gramEntry i j := by
  have h : i < t.rank ∧ j < t.rank := ⟨hi, hj⟩
  simp only [adeEntry, if_pos h]

/-! ## Reading generated data -/

/-- A square matrix read off a generated array of rows. -/
def matrixOfData {n : ℕ} (d : Array (Array ℤ)) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => (d.getD i.1 #[]).getD j.1 0

/-- A vector read off a generated array. -/
def vectorOfData {n : ℕ} (d : Array ℤ) : Fin n → ℤ := fun i => d.getD i.1 0

/-! ## Nondegeneracy from an adjugate -/

variable {n : ℕ}

/-- **The radical of a checked semidefinite form.**  If an integer-scaled
`LDLᵀ` certificate makes the Gram form of `A` nonnegative and the form vanishes
at `v`, then `v` is orthogonal to everything: `v ᵥ* A = 0`.  This is the
Cauchy--Schwarz step shared by
`SRG266.Lattice.toBilin'_posDef_of_ldlt` and
`SRG266.Lattice.toBilin'_posDef_of_ldlt_of_adjugate`. -/
theorem vecMul_eq_zero_of_toBilin'_eq_zero (A L : Matrix (Fin n) (Fin n) ℤ)
    (weight : Fin n → ℤ) (scale : ℤ) (hsym : A.IsSymm)
    (hcheck : checkIntegerScaledGram A L weight scale = true)
    (v : Fin n → ℤ) (hv : Matrix.toBilin' A v v = 0) :
    Matrix.vecMul v A = 0 := by
  have hnn := toBilin'_nonneg_of_ldlt A L weight scale hcheck
  have horth : ∀ j : Fin n, Matrix.vecMul v A j = 0 := by
    intro j
    set u : Fin n → ℤ := Pi.single j 1 with hu
    have hvu : Matrix.toBilin' A v u = Matrix.vecMul v A j := by
      rw [toBilin'_eq_vecMul_dotProduct, hu, dotProduct_single, mul_one]
    have hline : ∀ t : ℤ,
        0 ≤ 2 * t * Matrix.toBilin' A v u + Matrix.toBilin' A u u := by
      intro t
      have h := hnn (t • v + u)
      rwa [toBilin'_add_smul A hsym v u t, hv, mul_zero, zero_add] at h
    rw [← hvu]
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 := hline (Matrix.toBilin' A u u + 1)
      nlinarith [hline 0]
    · have h1 := hline (-(Matrix.toBilin' A u u + 1))
      nlinarith [hline 0]
  exact funext horth

/-- **Strict positive definiteness from a Gram certificate and an adjugate.**
A symmetric integer matrix with an exact integer-scaled `LDLᵀ` certificate and
a *scaled* right inverse `A * B = d • 1`, `d ≠ 0`, has a positive-definite Gram
form.  Root lattices are the intended application: they are never unimodular,
so `SRG266.Lattice.toBilin'_posDef_of_ldlt` does not apply. -/
theorem toBilin'_posDef_of_ldlt_of_adjugate (A B L : Matrix (Fin n) (Fin n) ℤ)
    (weight : Fin n → ℤ) (scale d : ℤ) (hd : d ≠ 0) (hsym : A.IsSymm)
    (hinv : A * B = d • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hcheck : checkIntegerScaledGram A L weight scale = true) :
    ∀ v : Fin n → ℤ, v ≠ 0 → 0 < Matrix.toBilin' A v v := by
  intro v hv
  rcases lt_or_eq_of_le (toBilin'_nonneg_of_ldlt A L weight scale hcheck v) with hpos | hzero
  · exact hpos
  refine absurd ?_ hv
  have hrad := vecMul_eq_zero_of_toBilin'_eq_zero A L weight scale hsym hcheck v hzero.symm
  have hstep : Matrix.vecMul (Matrix.vecMul v A) B = Matrix.vecMul v (A * B) :=
    Matrix.vecMul_vecMul v A B
  rw [hrad, hinv, Matrix.zero_vecMul] at hstep
  have hsmul : Matrix.vecMul v (d • (1 : Matrix (Fin n) (Fin n) ℤ)) = d • v := by
    rw [Matrix.vecMul_smul, Matrix.vecMul_one]
  rw [hsmul] at hstep
  refine funext fun i => ?_
  have hi := congrFun hstep.symm i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
  exact (mul_eq_zero.mp hi).resolve_left hd

/-- Contents of a checked integer-scaled Gram certificate.  Stated for a
general index type so that the `Decidable` instances of the checker and of the
conclusion agree; at `ι = Fin n` they do not. -/
theorem checkIntegerScaledGram_spec {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (D : Matrix ι ι ℤ) (L : Matrix ι κ ℤ)
    (weight : κ → ℤ) (scale : ℤ)
    (h : checkIntegerScaledGram D L weight scale = true) :
    0 < scale ∧ (∀ k, 0 ≤ weight k) ∧
      ∀ i j, scale * D i j = ∑ k, L i k * weight k * L j k :=
  of_decide_eq_true (by simpa only [checkIntegerScaledGram] using h)

/-! ## Root-lattice certificates -/

/-- **A kernel certificate for an irreducible root lattice.**  Every field is
checked by `decide +kernel` against the generated data of
`SRG266/Certificates/RootLatticeData.lean`. -/
structure RootLatticeCert (n : ℕ) where
  /-- The Cartan matrix under certification. -/
  gram : Matrix (Fin n) (Fin n) ℤ
  /-- Lower factor of the fraction-free `LDLᵀ` factorization. -/
  ldlt : Matrix (Fin n) (Fin n) ℤ
  /-- Weights of the fraction-free `LDLᵀ` factorization. -/
  weight : Fin n → ℤ
  /-- Scale of the fraction-free `LDLᵀ` factorization. -/
  scale : ℤ
  /-- The claimed determinant. -/
  det : ℤ
  /-- The adjugate `det • gram⁻¹`. -/
  adjugate : Matrix (Fin n) (Fin n) ℤ
  /-- The Cartan matrix is symmetric. -/
  symm : ∀ i j, gram i j = gram j i
  /-- The `LDLᵀ` factor is lower triangular. -/
  lower : ∀ i j : Fin n, i < j → ldlt i j = 0
  /-- `scale • gram = ldlt * diag weight * ldltᵀ`. -/
  ldlt_check : checkIntegerScaledGram gram ldlt weight scale = true
  /-- The scale is positive. -/
  scale_pos : 0 < scale
  /-- The determinant is positive. -/
  det_pos : 0 < det
  /-- `gram * adjugate = det • 1`. -/
  adjugate_check : ∀ i j, (gram * adjugate) i j = if i = j then det else 0
  /-- The determinant identity read off the triangular factorization. -/
  det_check : scale ^ n * det = (∏ i, ldlt i i) ^ 2 * ∏ i, weight i

namespace RootLatticeCert

variable (c : RootLatticeCert n)

theorem isSymm : c.gram.IsSymm := isSymm_of_entries c.gram c.symm

theorem gram_mul_adjugate :
    c.gram * c.adjugate = c.det • (1 : Matrix (Fin n) (Fin n) ℤ) := by
  refine funext fun i => funext fun j => ?_
  rw [c.adjugate_check i j]
  by_cases h : i = j <;> simp [h]

/-- The factorization, as a matrix identity. -/
theorem smul_gram_eq :
    c.scale • c.gram = c.ldlt * Matrix.diagonal c.weight * c.ldlt.transpose := by
  have hdata := checkIntegerScaledGram_spec c.gram c.ldlt c.weight c.scale c.ldlt_check
  refine funext fun i => funext fun j => ?_
  rw [Matrix.smul_apply, smul_eq_mul, hdata.2.2 i j, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => by
    rw [Matrix.mul_diagonal, Matrix.transpose_apply]

/-- **The determinant of a certified Cartan matrix.** -/
theorem det_gram : c.gram.det = c.det := by
  have hlow : c.ldlt.BlockTriangular OrderDual.toDual := by
    intro i j h
    exact c.lower i j (by simpa using h)
  have hdetL : c.ldlt.det = ∏ i, c.ldlt i i := Matrix.det_of_lowerTriangular _ hlow
  have hsmul : (c.scale • c.gram).det = c.scale ^ n * c.gram.det := by
    rw [Matrix.det_smul, Fintype.card_fin]
  have hprod : (c.ldlt * Matrix.diagonal c.weight * c.ldlt.transpose).det =
      (∏ i, c.ldlt i i) ^ 2 * ∏ i, c.weight i := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose, hdetL]
    ring
  have hkey : c.scale ^ n * c.gram.det = c.scale ^ n * c.det := by
    rw [← hsmul, c.smul_gram_eq, hprod, c.det_check]
  exact mul_left_cancel₀ (pow_ne_zero n (ne_of_gt c.scale_pos)) hkey

/-- **The certified Cartan form is positive definite.** -/
theorem posDef : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < Matrix.toBilin' c.gram v v :=
  toBilin'_posDef_of_ldlt_of_adjugate c.gram c.adjugate c.ldlt c.weight c.scale c.det
    (ne_of_gt c.det_pos) c.isSymm c.gram_mul_adjugate c.ldlt_check

end RootLatticeCert

/-! ## Coset minima -/

/-- `det A` times the discriminant form value of the coset whose dual
coordinates are `y`: the value itself is `yᵀ B y / det A` for `B` the
adjugate, since `B / det A` is the Gram matrix of the dual basis. -/
def cosetFormNum (n : ℕ) (B : Array (Array ℤ)) (y : Array ℤ) : ℤ :=
  ((List.range n).map fun i =>
    ((List.range n).map fun j =>
      y.getD i 0 * (B.getD i #[]).getD j 0 * y.getD j 0).sum).sum

/-- **The coset-minimum check.**  For each listed coset the discriminant form
value `yᵀ B y / det` must agree with the listed minimum `p / q` modulo `2ℤ`.
Clearing denominators, `2 * det * q` must divide `q * yᵀ B y - p * det`. -/
def checkCosetMinima (n : ℕ) (B : Array (Array ℤ)) (det : ℤ)
    (cosets minima : Array (Array ℤ)) : Bool :=
  (cosets.size == minima.size) &&
    (List.range cosets.size).all fun t =>
      let y := cosets.getD t #[]
      let m := minima.getD t #[]
      let p := m.getD 0 0
      let q := m.getD 1 1
      decide (0 < q) &&
        ((q * cosetFormNum n B y - p * det) % (2 * det * q) == 0)

/-- **What the coset-minimum check says at one coset.**  Writing the `t`-th
listed minimum as `p / q` and the discriminant form value of the `t`-th listed
coset as `yᵀ B y / det`, the two differ by an even integer.  Denominators are
cleared, so this is a statement about integers only. -/
def CosetMinAgrees (n : ℕ) (B : Array (Array ℤ)) (det : ℤ)
    (cosets minima : Array (Array ℤ)) (t : ℕ) : Prop :=
  ∃ k : ℤ,
    ((minima.getD t #[]).getD 1 1) * cosetFormNum n B (cosets.getD t #[]) =
      ((minima.getD t #[]).getD 0 0) * det +
        2 * det * ((minima.getD t #[]).getD 1 1) * k

/-- **What the coset-minimum check means.**  Every listed coset minimum agrees
with the discriminant form value of its listed representative modulo `2ℤ`. -/
theorem cosetMinAgrees_of_check {n : ℕ} {B : Array (Array ℤ)} {det : ℤ}
    {cosets minima : Array (Array ℤ)}
    (h : checkCosetMinima n B det cosets minima = true) :
    ∀ t < cosets.size, CosetMinAgrees n B det cosets minima t := by
  intro t ht
  rw [checkCosetMinima, Bool.and_eq_true] at h
  have hall := List.all_eq_true.mp h.2 t (List.mem_range.mpr ht)
  simp only [Bool.and_eq_true, beq_iff_eq] at hall
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero hall.2
  exact ⟨k, by linarith⟩

/-! ## The norm-three shell counter -/

/-- Expansion of the Gram form on a difference. -/
theorem toBilin'_sub (A : Matrix (Fin n) (Fin n) ℤ) (hsym : A.IsSymm) (v w : Fin n → ℤ) :
    Matrix.toBilin' A (v - w) (v - w) =
      Matrix.toBilin' A v v - 2 * Matrix.toBilin' A v w + Matrix.toBilin' A w w := by
  have h := toBilin'_add_smul A hsym w v (-1)
  have hvw : ((-1 : ℤ) • w + v) = v - w := by
    rw [neg_one_smul, neg_add_eq_sub]
  rw [hvw] at h
  have hswap : Matrix.toBilin' A w v = Matrix.toBilin' A v w :=
    (toBilin'_isSymm A hsym).eq w v
  rw [hswap] at h
  rw [h]
  ring

/-- Linearity of the Gram form on a difference in the second slot. -/
theorem toBilin'_sub_right (A : Matrix (Fin n) (Fin n) ℤ) (v w u : Fin n → ℤ) :
    Matrix.toBilin' A v (w - u) = Matrix.toBilin' A v w - Matrix.toBilin' A v u :=
  map_sub (Matrix.toBilin' A v) w u

/-- For a norm-three vector `v`, the norm-three vectors
at inner product `2` from `v` are in bijection with the roots at inner product
`1` from `v`, by the involution `w ↦ v - w`.  The design's shell counters
`66`, `54`, `48` for `D₁₂⁺`, `(E₇⊕E₇)⁺`, `A₁₅⁺` are therefore root counts, and
a root count is a closed formula per glue group rather than a shell search. -/
def normThreeRootEquiv (A : Matrix (Fin n) (Fin n) ℤ) (hsym : A.IsSymm) (v : Fin n → ℤ)
    (hv : Matrix.toBilin' A v v = 3) :
    {w : Fin n → ℤ // Matrix.toBilin' A w w = 3 ∧ Matrix.toBilin' A v w = 2} ≃
      {r : Fin n → ℤ // Matrix.toBilin' A r r = 2 ∧ Matrix.toBilin' A v r = 1} where
  toFun w := ⟨v - w.1, by
    refine ⟨?_, ?_⟩
    · rw [toBilin'_sub A hsym, hv, w.2.1, w.2.2]; ring
    · rw [toBilin'_sub_right A, hv, w.2.2]; ring⟩
  invFun r := ⟨v - r.1, by
    refine ⟨?_, ?_⟩
    · rw [toBilin'_sub A hsym, hv, r.2.1, r.2.2]; ring
    · rw [toBilin'_sub_right A, hv, r.2.2]; ring⟩
  left_inv w := Subtype.ext (by simp)
  right_inv r := Subtype.ext (by simp)

end Lattice
end SRG266
