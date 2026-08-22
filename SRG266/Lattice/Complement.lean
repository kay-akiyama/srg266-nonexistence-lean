/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Core
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic.LinearCombination

/-!
# Rank-3 complement certificates

`SRG266/Lattice/Discriminant.lean` reduces the discriminant datum of a maximal
integral overlattice `Λ̃` of the local Gram lattice to an *orthogonal glue
basis* at each of the two primes `3` and `5`: at most two vectors `y_i` of the
`p`-torsion part, pairwise integrally paired, independent modulo `Λ̃`, and with
`⟨y_i, y_i⟩ = u_i / p` for a unit `u_i` of `ZMod p`
(`SRG266.Lattice.GlueBasis`).  Since `a₃, a₅ ≤ 2` there are exactly
`(1 + 2 + 4) · (1 + 4 + 16) = 147` possible tuples `(u₃, u₅)`.

To glue `Λ̃` up to an odd unimodular rank-15 lattice one needs, for each such
tuple, a rank-3 positive-definite integral lattice `M` whose discriminant form
is the *negative* of the tuple.  This module fixes the certificate format for
`M` and the Boolean validator the kernel runs on it; the 147 certified rows
themselves are generated data
(`SRG266/Certificates/Rank15ComplementData.lean`, produced by
`scripts/generate_rank15_complement_data.py`), and the table-level interface is
`SRG266/Lattice/ComplementTable.lean`.

## The certificate format

A row carries

* `u3`, `u5` — the discriminant diagonal it is responsible for;
* `g00 … g22` — a symmetric positive-definite `3 × 3` integer Gram matrix `M`;
* `a00 … a22` — the adjugate of that matrix, shipped explicitly so that the
  identity `adj · M = det M · 1` is a checked equation rather than a theorem
  about `Matrix.adjugate`;
* `w3`, `w5` — integer triples with `m_i := w_i / p_i ∈ M^∨`;
* `coeff` — for each of the three columns of the adjugate, the coefficients
  expressing it in terms of the glue vectors modulo `det M`.

`rank15RowValid` checks the following conditions:

1. `M` symmetric with positive leading principal minors, `det M = 3^a₃ · 5^a₅`,
   and `adj · M = det M · 1`;
2. `M *ᵥ w ≡ 0 (mod p)` and `w ≢ 0 (mod p)`, i.e. `m = w / p` has exact order
   `p` in `M^∨ / M`;
3. `wᵀ M w ≡ −u · p (mod p²)`, i.e. `q(m) ≡ −u / p (mod ℤ)` — the sign that
   makes the glued form integral;
4. same-prime glue vectors are orthogonal (`w₁ᵀ M w₂ ≡ 0 (mod p²)`) and
   independent modulo `p`;
5. every column of the adjugate lies in `M + ∑ ℤ · wᵢ · (det M / pᵢ)` modulo
   `det M`, which says exactly `M^∨ = M + ∑ ℤ · mᵢ`.

Condition 3 uses the negative sign convention of
`Rank15ComplementRow.glueValid`.

## Soundness

The second half of the file turns a validated row into mathematics.  `M` is
realised as the standard `ℤ`-lattice `integerCube` inside `Fin 3 → ℚ` carrying
the form `Rank15ComplementRow.form r`, and a valid row yields:

* `Rank15ComplementRow.form_isSymm`, `Rank15ComplementRow.form_posDef`,
  `Rank15ComplementRow.form_nondegenerate` — the rank-3 lattice is a
  positive-definite quadratic space.  Positive definiteness comes from the
  leading minors through the completed-square identity
  `Rank15ComplementRow.form_sos`, with no analysis and no `Matrix.det`.
* `integerCube_isLattice`, `Rank15ComplementRow.integerCube_isIntegral` — `ℤ³`
  is an integral lattice for that form.
* `Rank15ComplementRow.glueVec_mem_dual`, `…glueVec_diag`,
  `…glueVec_not_mem`, `…glueVec_ortho`, `…glueVec_sub_smul_not_mem` — the glue
  vectors are a `SRG266.Lattice.GlueBasis`-shaped datum for `M`, with diagonal
  `−u / p`.
* `Rank15ComplementRow.dual_integerCube_eq` — `M^∨ = M + ∑ ℤ · mᵢ`.

These are exactly the hypotheses consumed by the glue construction.
-/

namespace SRG266

/-! ## Integer triples

Glue vectors are triples of integers.  Writing them as `ℤ × ℤ × ℤ` rather than
`Fin 3 → ℤ` keeps the kernel check on the 147 rows to plain integer arithmetic:
there is no `Matrix` and no `Finset.sum` anywhere in the validator. -/

/-- Every coordinate of `w` is divisible by `m`. -/
def tripleZeroMod (m : ℤ) (w : ℤ × ℤ × ℤ) : Bool :=
  (w.1 % m == 0) && (w.2.1 % m == 0) && (w.2.2 % m == 0)

/-- Componentwise difference of integer triples. -/
def tripleSub (v w : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (v.1 - w.1, v.2.1 - w.2.1, v.2.2 - w.2.2)

/-- `w - k • v`, componentwise. -/
def tripleSubSmul (k : ℤ) (w v : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (w.1 - k * v.1, w.2.1 - k * v.2.1, w.2.2 - k * v.2.2)

/-- Componentwise scaling of an integer triple. -/
def scaleTriple (k : ℤ) (w : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (k * w.1, k * w.2.1, k * w.2.2)

/-! ## The certificate row -/

/-- A rank-3 complement certificate: a positive-definite integral Gram matrix
together with glue data realising a prescribed discriminant diagonal.  See the
module docstring for the meaning of each field. -/
structure Rank15ComplementRow where
  /-- The diagonal of the discriminant pairing at the prime `3`. -/
  u3 : List ℤ
  /-- The diagonal of the discriminant pairing at the prime `5`. -/
  u5 : List ℤ
  /-- Gram entry `(0, 0)`. -/
  g00 : ℤ
  /-- Gram entry `(0, 1)`. -/
  g01 : ℤ
  /-- Gram entry `(0, 2)`. -/
  g02 : ℤ
  /-- Gram entry `(1, 0)`. -/
  g10 : ℤ
  /-- Gram entry `(1, 1)`. -/
  g11 : ℤ
  /-- Gram entry `(1, 2)`. -/
  g12 : ℤ
  /-- Gram entry `(2, 0)`. -/
  g20 : ℤ
  /-- Gram entry `(2, 1)`. -/
  g21 : ℤ
  /-- Gram entry `(2, 2)`. -/
  g22 : ℤ
  /-- Adjugate entry `(0, 0)`. -/
  a00 : ℤ
  /-- Adjugate entry `(0, 1)`. -/
  a01 : ℤ
  /-- Adjugate entry `(0, 2)`. -/
  a02 : ℤ
  /-- Adjugate entry `(1, 0)`. -/
  a10 : ℤ
  /-- Adjugate entry `(1, 1)`. -/
  a11 : ℤ
  /-- Adjugate entry `(1, 2)`. -/
  a12 : ℤ
  /-- Adjugate entry `(2, 0)`. -/
  a20 : ℤ
  /-- Adjugate entry `(2, 1)`. -/
  a21 : ℤ
  /-- Adjugate entry `(2, 2)`. -/
  a22 : ℤ
  /-- Numerators of the glue vectors at the prime `3`. -/
  w3 : List (ℤ × ℤ × ℤ)
  /-- Numerators of the glue vectors at the prime `5`. -/
  w5 : List (ℤ × ℤ × ℤ)
  /-- Generation coefficients, one list per adjugate column. -/
  coeff : List (List ℤ)

namespace Rank15ComplementRow

variable (r : Rank15ComplementRow)

/-- The Gram matrix applied to an integer triple. -/
def gramMulVec (w : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (r.g00 * w.1 + r.g01 * w.2.1 + r.g02 * w.2.2,
   r.g10 * w.1 + r.g11 * w.2.1 + r.g12 * w.2.2,
   r.g20 * w.1 + r.g21 * w.2.1 + r.g22 * w.2.2)

/-- The Gram pairing `vᵀ M w` of two integer triples. -/
def gramPair (v w : ℤ × ℤ × ℤ) : ℤ :=
  v.1 * (r.g00 * w.1 + r.g01 * w.2.1 + r.g02 * w.2.2)
    + v.2.1 * (r.g10 * w.1 + r.g11 * w.2.1 + r.g12 * w.2.2)
    + v.2.2 * (r.g20 * w.1 + r.g21 * w.2.1 + r.g22 * w.2.2)

/-- The upper-left `1 × 1` minor of the Gram matrix. -/
def minor1 : ℤ := r.g00

/-- The upper-left `2 × 2` minor of the Gram matrix. -/
def minor2 : ℤ := r.g00 * r.g11 - r.g01 * r.g10

/-- The determinant of the Gram matrix, expanded by hand along the first row. -/
def detGram : ℤ :=
  r.g00 * (r.g11 * r.g22 - r.g12 * r.g21)
    - r.g01 * (r.g10 * r.g22 - r.g12 * r.g20)
    + r.g02 * (r.g10 * r.g21 - r.g11 * r.g20)

/-- The `j`-th column of the shipped adjugate. -/
def adjColumn : ℕ → ℤ × ℤ × ℤ
  | 0 => (r.a00, r.a10, r.a20)
  | 1 => (r.a01, r.a11, r.a21)
  | _ => (r.a02, r.a12, r.a22)

/-- The glue data of the row, flattened to triples `(p, u, w)`. -/
def glueData : List (ℤ × ℤ × (ℤ × ℤ × ℤ)) :=
  (r.u3.zip r.w3).map (fun x => ((3 : ℤ), x.1, x.2)) ++
    (r.u5.zip r.w5).map (fun x => ((5 : ℤ), x.1, x.2))

/-- Lengths, and the ranges of the discriminant diagonals. -/
def shapeValid : Bool :=
  decide (r.u3.length ≤ 2) && decide (r.u5.length ≤ 2) &&
    (r.w3.length == r.u3.length) && (r.w5.length == r.u5.length) &&
    r.u3.all (fun u => (u == 1) || (u == 2)) &&
    r.u5.all (fun u => (u == 1) || (u == 2) || (u == 3) || (u == 4)) &&
    r.coeff.all (fun c => c.length == r.u3.length + r.u5.length)

/-- The Gram matrix is symmetric. -/
def symmValid : Bool :=
  (r.g01 == r.g10) && (r.g02 == r.g20) && (r.g12 == r.g21)

/-- Sylvester's criterion: all three leading principal minors are positive. -/
def posDefValid : Bool :=
  decide (0 < r.minor1) && decide (0 < r.minor2) && decide (0 < r.detGram)

/-- The determinant realises the prescribed discriminant order, and the shipped
adjugate satisfies `adj · M = det M · 1`. -/
def detValid : Bool :=
  (r.detGram == 3 ^ r.u3.length * 5 ^ r.u5.length) &&
    (r.a00 * r.g00 + r.a01 * r.g10 + r.a02 * r.g20 == r.detGram) &&
    (r.a00 * r.g01 + r.a01 * r.g11 + r.a02 * r.g21 == 0) &&
    (r.a00 * r.g02 + r.a01 * r.g12 + r.a02 * r.g22 == 0) &&
    (r.a10 * r.g00 + r.a11 * r.g10 + r.a12 * r.g20 == 0) &&
    (r.a10 * r.g01 + r.a11 * r.g11 + r.a12 * r.g21 == r.detGram) &&
    (r.a10 * r.g02 + r.a11 * r.g12 + r.a12 * r.g22 == 0) &&
    (r.a20 * r.g00 + r.a21 * r.g10 + r.a22 * r.g20 == 0) &&
    (r.a20 * r.g01 + r.a21 * r.g11 + r.a22 * r.g21 == 0) &&
    (r.a20 * r.g02 + r.a21 * r.g12 + r.a22 * r.g22 == r.detGram)

/-- Each glue vector lies in `M^∨`, has exact order `p` there, and has the
prescribed diagonal `−u / p`. -/
def glueValid : Bool :=
  r.glueData.all fun x =>
    match x with
    | (p, u, w) =>
        (p * (r.detGram / p) == r.detGram) &&
          tripleZeroMod p (r.gramMulVec w) &&
          (!tripleZeroMod p w) &&
          ((r.gramPair w w + u * p) % (p * p) == 0)

/-- Two glue vectors at the same prime are orthogonal and independent. -/
def primePairValid (p : ℤ) (ws : List (ℤ × ℤ × ℤ)) : Bool :=
  match ws with
  | a :: b :: _ =>
      ((r.gramPair a b) % (p * p) == 0) &&
        (List.range p.toNat).all
          (fun k => !tripleZeroMod p (tripleSubSmul (k : ℤ) b a))
  | _ => true

/-- The combination of glue vectors prescribed by one row of `coeff`.  The
coefficient of the `k`-th glue vector is scaled by `det M / p_k`, so that the
whole sum is `det M` times an element of `∑ ℤ · m_k`. -/
def genColumn (c : List ℤ) : ℤ × ℤ × ℤ :=
  ((c.zip r.glueData).map
    (fun x => scaleTriple (x.1 * (r.detGram / x.2.1)) x.2.2.2)).sum

/-- Condition 5: every adjugate column is a combination of glue vectors modulo
`det M`, so the glue vectors generate `M^∨` over `M`. -/
def genValid : Bool :=
  (r.coeff.length == 3) &&
    tripleZeroMod r.detGram
      (tripleSub (r.adjColumn 0) (r.genColumn (r.coeff.getD 0 []))) &&
    tripleZeroMod r.detGram
      (tripleSub (r.adjColumn 1) (r.genColumn (r.coeff.getD 1 []))) &&
    tripleZeroMod r.detGram
      (tripleSub (r.adjColumn 2) (r.genColumn (r.coeff.getD 2 [])))

end Rank15ComplementRow

/-- The complement certificate validator as a single `Bool`. -/
def rank15RowValid (r : Rank15ComplementRow) : Bool :=
  r.shapeValid && r.symmValid && r.posDefValid && r.detValid && r.glueValid &&
    r.primePairValid 3 r.w3 && r.primePairValid 5 r.w5 && r.genValid

/-! ## The admissible discriminant tuples -/

/-- All lists of length at most two over `us`, ordered `[]`, singletons, pairs.
This is the order in which the certificate table is generated. -/
def rank15UnitTuples (us : List ℤ) : List (List ℤ) :=
  [[]] ++ us.map (fun a => [a]) ++ us.flatMap (fun a => us.map (fun b => [a, b]))

/-- The 147 admissible discriminant tuples `(u₃, u₅)` of a maximal integral
overlattice: at most two glue vectors at each prime, with unit diagonals. -/
def rank15AdmissibleKeys : List (List ℤ × List ℤ) :=
  (rank15UnitTuples [1, 2]).flatMap fun t3 =>
    (rank15UnitTuples [1, 2, 3, 4]).map fun t5 => (t3, t5)

/-- The abstract admissibility condition on a discriminant diagonal: at most two
glue vectors at each prime, and unit diagonal entries. -/
def Rank15Admissible (u3 u5 : List ℤ) : Prop :=
  u3.length ≤ 2 ∧ (∀ u ∈ u3, u = 1 ∨ u = 2) ∧
    u5.length ≤ 2 ∧ (∀ u ∈ u5, u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4)

theorem mem_rank15UnitTuples {us l : List ℤ} (hlen : l.length ≤ 2)
    (hmem : ∀ u ∈ l, u ∈ us) : l ∈ rank15UnitTuples us := by
  match l with
  | [] => simp [rank15UnitTuples]
  | [a] =>
      have ha : a ∈ us := hmem a (by simp)
      simp only [rank15UnitTuples, List.append_assoc, List.mem_append,
        List.mem_singleton, List.mem_map, List.mem_flatMap]
      exact Or.inr (Or.inl ⟨a, ha, rfl⟩)
  | [a, b] =>
      have ha : a ∈ us := hmem a (by simp)
      have hb : b ∈ us := hmem b (by simp)
      simp only [rank15UnitTuples, List.append_assoc, List.mem_append,
        List.mem_singleton, List.mem_map, List.mem_flatMap]
      exact Or.inr (Or.inr ⟨a, ha, b, hb, rfl⟩)
  | _ :: _ :: _ :: _ => simp at hlen

/-- **Every admissible discriminant tuple is a key of the table.** -/
theorem mem_rank15AdmissibleKeys {u3 u5 : List ℤ} (h : Rank15Admissible u3 u5) :
    (u3, u5) ∈ rank15AdmissibleKeys := by
  obtain ⟨h3len, h3, h5len, h5⟩ := h
  refine List.mem_flatMap.mpr ⟨u3, mem_rank15UnitTuples h3len ?_,
    List.mem_map.mpr ⟨u5, mem_rank15UnitTuples h5len ?_, rfl⟩⟩
  · intro u hu
    rcases h3 u hu with rfl | rfl <;> simp
  · intro u hu
    rcases h5 u hu with rfl | rfl | rfl | rfl <;> simp

/-! ## Soundness: a valid row is a rank-3 integral lattice

The certificate is realised on the standard lattice `ℤ³ ⊆ ℚ³`; `integerCube` is
that lattice and `Rank15ComplementRow.form` is the quadratic form of the row's
Gram matrix. -/

section Soundness

/-- The componentwise inclusion `ℤ³ ↪ ℚ³`. -/
def cubeEmbedding : (Fin 3 → ℤ) →ₗ[ℤ] (Fin 3 → ℚ) where
  toFun n := fun i => (n i : ℚ)
  map_add' n m := by
    funext i
    show ((n i + m i : ℤ) : ℚ) = (n i : ℚ) + (m i : ℚ)
    push_cast
    ring
  map_smul' c n := by
    funext i
    show ((c * n i : ℤ) : ℚ) = c • ((n i : ℚ))
    rw [zsmul_eq_mul]
    push_cast
    ring

@[simp]
theorem cubeEmbedding_apply (n : Fin 3 → ℤ) (i : Fin 3) :
    cubeEmbedding n i = (n i : ℚ) := rfl

/-- The standard lattice `ℤ³` inside `ℚ³`. -/
def integerCube : Submodule ℤ (Fin 3 → ℚ) := LinearMap.range cubeEmbedding

theorem mem_integerCube {v : Fin 3 → ℚ} :
    v ∈ integerCube ↔ ∃ n : Fin 3 → ℤ, ∀ i, (n i : ℚ) = v i := by
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, fun _ => rfl⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, funext fun i => hn i⟩

theorem cubeEmbedding_mem (n : Fin 3 → ℤ) : cubeEmbedding n ∈ integerCube :=
  ⟨n, rfl⟩

/-- `ℤ³` is a lattice in `ℚ³`. -/
theorem integerCube_isLattice : Lattice.IsLattice ℚ integerCube := by
  constructor
  · have htop : (⊤ : Submodule ℤ (Fin 3 → ℤ)).FG := Module.Finite.fg_top
    have := htop.map cubeEmbedding
    rwa [Submodule.map_top] at this
  · refine top_unique ?_
    rw [← (Pi.basisFun ℚ (Fin 3)).span_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span ?_
    refine ⟨fun j => if j = i then 1 else 0, funext fun j => ?_⟩
    by_cases hj : j = i <;> simp [hj]

namespace Rank15ComplementRow

variable (r : Rank15ComplementRow)

/-- The rank-3 complement Gram matrix, over `ℚ`. -/
def gramQ : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(r.g00 : ℚ), (r.g01 : ℚ), (r.g02 : ℚ);
     (r.g10 : ℚ), (r.g11 : ℚ), (r.g12 : ℚ);
     (r.g20 : ℚ), (r.g21 : ℚ), (r.g22 : ℚ)]

/-- The rank-3 complement form on `ℚ³`. -/
def form : LinearMap.BilinForm ℚ (Fin 3 → ℚ) := Matrix.toBilin' r.gramQ

theorem form_apply (v w : Fin 3 → ℚ) :
    r.form v w =
      v 0 * ((r.g00 : ℚ) * w 0 + (r.g01 : ℚ) * w 1 + (r.g02 : ℚ) * w 2)
        + v 1 * ((r.g10 : ℚ) * w 0 + (r.g11 : ℚ) * w 1 + (r.g12 : ℚ) * w 2)
        + v 2 * ((r.g20 : ℚ) * w 0 + (r.g21 : ℚ) * w 1 + (r.g22 : ℚ) * w 2) := by
  simp only [form, gramQ, Matrix.toBilin'_apply, Fin.sum_univ_three,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
  ring

theorem symmValid_iff :
    r.symmValid = true ↔ r.g01 = r.g10 ∧ r.g02 = r.g20 ∧ r.g12 = r.g21 := by
  simp [symmValid, and_assoc]

/-- A row whose Gram matrix is symmetric has a symmetric form. -/
theorem form_isSymm (h : r.symmValid = true) : (r.form).IsSymm := by
  obtain ⟨h1, h2, h3⟩ := r.symmValid_iff.mp h
  refine ⟨fun x y => ?_⟩
  show r.form x y = r.form y x
  rw [form_apply, form_apply, h1, h2, h3]
  ring

/-- **The completed-square identity.**  Writing `d₁, d₂, d₃` for the leading
principal minors of a symmetric `3 × 3` Gram matrix,

`d₁ d₂ q(v) = d₂ (g₀₀v₀ + g₀₁v₁ + g₀₂v₂)² + (d₂v₁ + (g₀₀g₁₂ − g₀₁g₀₂)v₂)² + d₁d₃v₂²`.

The last coefficient uses the Desnanot–Jacobi identity, so `ring` closes it. -/
theorem form_sos (h : r.symmValid = true) (v : Fin 3 → ℚ) :
    ((r.minor1 : ℚ) * (r.minor2 : ℚ)) * r.form v v =
      (r.minor2 : ℚ) *
          ((r.g00 : ℚ) * v 0 + (r.g01 : ℚ) * v 1 + (r.g02 : ℚ) * v 2) ^ 2
        + ((r.minor2 : ℚ) * v 1
            + ((r.g00 : ℚ) * (r.g12 : ℚ) - (r.g01 : ℚ) * (r.g02 : ℚ)) * v 2) ^ 2
        + (r.minor1 : ℚ) * (r.detGram : ℚ) * v 2 ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := r.symmValid_iff.mp h
  rw [form_apply]
  simp only [minor1, minor2, detGram, ← h1, ← h2, ← h3]
  push_cast
  ring

theorem posDefValid_minors (h : r.posDefValid = true) :
    0 < r.minor1 ∧ 0 < r.minor2 ∧ 0 < r.detGram := by
  simp only [posDefValid, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **The complement form is positive definite.**  Proved from the leading
principal minors through `form_sos`; no `Matrix.det`, no analysis. -/
theorem form_posDef (hsym : r.symmValid = true) (hpd : r.posDefValid = true)
    (v : Fin 3 → ℚ) (hv : v ≠ 0) : 0 < r.form v v := by
  obtain ⟨hd1, hd2, hd3⟩ := r.posDefValid_minors hpd
  have hd1' : (0 : ℚ) < (r.minor1 : ℚ) := by exact_mod_cast hd1
  have hd2' : (0 : ℚ) < (r.minor2 : ℚ) := by exact_mod_cast hd2
  have hd3' : (0 : ℚ) < (r.detGram : ℚ) := by exact_mod_cast hd3
  have hsos := r.form_sos hsym v
  set S1 : ℚ := (r.g00 : ℚ) * v 0 + (r.g01 : ℚ) * v 1 + (r.g02 : ℚ) * v 2 with hS1
  set S2 : ℚ := (r.minor2 : ℚ) * v 1
      + ((r.g00 : ℚ) * (r.g12 : ℚ) - (r.g01 : ℚ) * (r.g02 : ℚ)) * v 2 with hS2
  have hnn1 : 0 ≤ (r.minor2 : ℚ) * S1 ^ 2 := mul_nonneg hd2'.le (sq_nonneg _)
  have hnn2 : (0 : ℚ) ≤ S2 ^ 2 := sq_nonneg _
  have hnn3 : 0 ≤ (r.minor1 : ℚ) * (r.detGram : ℚ) * v 2 ^ 2 :=
    mul_nonneg (mul_pos hd1' hd3').le (sq_nonneg _)
  have hrhs : 0 < (r.minor2 : ℚ) * S1 ^ 2 + S2 ^ 2
      + (r.minor1 : ℚ) * (r.detGram : ℚ) * v 2 ^ 2 := by
    by_cases hv2 : v 2 = 0
    · by_cases hv1 : v 1 = 0
      · have hv0 : v 0 ≠ 0 := by
          intro h0
          refine hv (funext fun i => ?_)
          fin_cases i
          · simpa using h0
          · simpa using hv1
          · simpa using hv2
        have hg00 : (r.g00 : ℚ) ≠ 0 := by
          have : (0 : ℚ) < (r.g00 : ℚ) := by simpa [minor1] using hd1'
          exact ne_of_gt this
        have hS1ne : S1 ≠ 0 := by
          rw [hS1, hv1, hv2, mul_zero, mul_zero, add_zero, add_zero]
          exact mul_ne_zero hg00 hv0
        have h1 : 0 < (r.minor2 : ℚ) * S1 ^ 2 :=
          mul_pos hd2' (pow_pos (abs_pos.mpr hS1ne) 2 |>.trans_le (le_of_eq (sq_abs S1)))
        linarith
      · have hS2ne : S2 ≠ 0 := by
          rw [hS2, hv2, mul_zero, add_zero]
          exact mul_ne_zero (ne_of_gt hd2') hv1
        have h2 : (0 : ℚ) < S2 ^ 2 :=
          pow_pos (abs_pos.mpr hS2ne) 2 |>.trans_le (le_of_eq (sq_abs S2))
        linarith
    · have h3 : 0 < (r.minor1 : ℚ) * (r.detGram : ℚ) * v 2 ^ 2 :=
        mul_pos (mul_pos hd1' hd3')
          (pow_pos (abs_pos.mpr hv2) 2 |>.trans_le (le_of_eq (sq_abs (v 2))))
      linarith
  have hprod : (0 : ℚ) < ((r.minor1 : ℚ) * (r.minor2 : ℚ)) * r.form v v := by
    rw [hsos]
    exact hrhs
  nlinarith [hprod, mul_pos hd1' hd2']

/-- The complement form is nondegenerate. -/
theorem form_nondegenerate (hsym : r.symmValid = true) (hpd : r.posDefValid = true) :
    (r.form).Nondegenerate := by
  have hleft : (r.form).SeparatingLeft := by
    intro v hv
    by_contra hne
    exact absurd (hv v) (ne_of_gt (r.form_posDef hsym hpd v hne))
  refine ⟨hleft, fun v hv => hleft v fun w => ?_⟩
  rw [(r.form_isSymm hsym).eq v w]
  exact hv w

/-- The form is integral on `ℤ³`. -/
theorem integerCube_isIntegral : Lattice.IsIntegral r.form integerCube := by
  rw [Lattice.isIntegral_iff_forall]
  rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩
  refine Submodule.mem_one.mpr ⟨n 0 * (r.g00 * m 0 + r.g01 * m 1 + r.g02 * m 2)
    + n 1 * (r.g10 * m 0 + r.g11 * m 1 + r.g12 * m 2)
    + n 2 * (r.g20 * m 0 + r.g21 * m 1 + r.g22 * m 2), ?_⟩
  rw [form_apply]
  simp only [cubeEmbedding_apply, algebraMap_int_eq, eq_intCast]
  push_cast
  ring

end Rank15ComplementRow

/-! ### Integer triples as rational vectors -/

/-- The coordinates of an integer triple. -/
def tripleCoord (w : ℤ × ℤ × ℤ) : Fin 3 → ℤ := ![w.1, w.2.1, w.2.2]

/-- An integer triple, read as a vector of `ℚ³`. -/
def tripleToQ (w : ℤ × ℤ × ℤ) : Fin 3 → ℚ := cubeEmbedding (tripleCoord w)

theorem tripleToQ_mem (w : ℤ × ℤ × ℤ) : tripleToQ w ∈ integerCube :=
  cubeEmbedding_mem _

@[simp]
theorem tripleToQ_apply_zero (w : ℤ × ℤ × ℤ) : tripleToQ w 0 = (w.1 : ℚ) := rfl

@[simp]
theorem tripleToQ_apply_one (w : ℤ × ℤ × ℤ) : tripleToQ w 1 = (w.2.1 : ℚ) := rfl

@[simp]
theorem tripleToQ_apply_two (w : ℤ × ℤ × ℤ) : tripleToQ w 2 = (w.2.2 : ℚ) := rfl

theorem tripleSub_eq (v w : ℤ × ℤ × ℤ) : tripleSub v w = v - w := rfl

theorem tripleToQ_zero : tripleToQ 0 = 0 := by
  funext i
  fin_cases i <;> simp [tripleToQ, tripleCoord]

theorem tripleToQ_add (v w : ℤ × ℤ × ℤ) :
    tripleToQ (v + w) = tripleToQ v + tripleToQ w := by
  funext i
  fin_cases i <;> simp [tripleToQ, tripleCoord]

theorem tripleToQ_scaleTriple (m : ℤ) (w : ℤ × ℤ × ℤ) :
    tripleToQ (scaleTriple m w) = (m : ℚ) • tripleToQ w := by
  funext i
  fin_cases i <;> simp [tripleToQ, tripleCoord, scaleTriple]

theorem cubeEmbedding_eq_tripleToQ (n : Fin 3 → ℤ) :
    cubeEmbedding n = tripleToQ (n 0, n 1, n 2) := by
  funext i
  fin_cases i <;> simp [tripleToQ, tripleCoord]

theorem tripleZeroMod_iff {m : ℤ} {w : ℤ × ℤ × ℤ} :
    tripleZeroMod m w = true ↔ m ∣ w.1 ∧ m ∣ w.2.1 ∧ m ∣ w.2.2 := by
  simp only [tripleZeroMod, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨Int.dvd_of_emod_eq_zero h1, Int.dvd_of_emod_eq_zero h2,
      Int.dvd_of_emod_eq_zero h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨Int.emod_eq_zero_of_dvd h1, Int.emod_eq_zero_of_dvd h2⟩,
      Int.emod_eq_zero_of_dvd h3⟩

theorem exists_scaleTriple_of_tripleZeroMod {m : ℤ} {w : ℤ × ℤ × ℤ}
    (h : tripleZeroMod m w = true) : ∃ t : ℤ × ℤ × ℤ, w = scaleTriple m t := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := tripleZeroMod_iff.mp h
  exact ⟨(a, b, c), by
    apply Prod.ext ha
    exact Prod.ext hb hc⟩

/-- The glue vector `w / p` of `ℚ³`. -/
def glueVec (p : ℤ) (w : ℤ × ℤ × ℤ) : Fin 3 → ℚ := ((p : ℚ))⁻¹ • tripleToQ w

namespace Rank15ComplementRow

variable (r : Rank15ComplementRow)

/-- The glue vectors of a row. -/
def glueVecs : List (Fin 3 → ℚ) := r.glueData.map fun x => glueVec x.1 x.2.2

/-- The `ℤ`-module generated by the glue vectors of a row. -/
def glueSpan : Submodule ℤ (Fin 3 → ℚ) := Submodule.span ℤ {v | v ∈ r.glueVecs}

theorem glueVec_mem_glueSpan {p u : ℤ} {w : ℤ × ℤ × ℤ}
    (hx : (p, u, w) ∈ r.glueData) : glueVec p w ∈ r.glueSpan :=
  Submodule.subset_span (List.mem_map.mpr ⟨(p, u, w), hx, rfl⟩)

/-- The only primes occurring in the glue data are `3` and `5`. -/
theorem glueData_prime {x : ℤ × ℤ × (ℤ × ℤ × ℤ)} (hx : x ∈ r.glueData) :
    x.1 = 3 ∨ x.1 = 5 := by
  rcases List.mem_append.mp hx with h | h <;>
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp h
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ### Reading the validator -/

theorem rank15RowValid_parts (h : rank15RowValid r = true) :
    r.shapeValid = true ∧ r.symmValid = true ∧ r.posDefValid = true ∧
      r.detValid = true ∧ r.glueValid = true ∧ r.primePairValid 3 r.w3 = true ∧
      r.primePairValid 5 r.w5 = true ∧ r.genValid = true := by
  simpa [rank15RowValid, and_assoc] using h

theorem detValid_parts (h : r.detValid = true) :
    r.detGram = 3 ^ r.u3.length * 5 ^ r.u5.length ∧
      r.a00 * r.g00 + r.a01 * r.g10 + r.a02 * r.g20 = r.detGram ∧
      r.a00 * r.g01 + r.a01 * r.g11 + r.a02 * r.g21 = 0 ∧
      r.a00 * r.g02 + r.a01 * r.g12 + r.a02 * r.g22 = 0 ∧
      r.a10 * r.g00 + r.a11 * r.g10 + r.a12 * r.g20 = 0 ∧
      r.a10 * r.g01 + r.a11 * r.g11 + r.a12 * r.g21 = r.detGram ∧
      r.a10 * r.g02 + r.a11 * r.g12 + r.a12 * r.g22 = 0 ∧
      r.a20 * r.g00 + r.a21 * r.g10 + r.a22 * r.g20 = 0 ∧
      r.a20 * r.g01 + r.a21 * r.g11 + r.a22 * r.g21 = 0 ∧
      r.a20 * r.g02 + r.a21 * r.g12 + r.a22 * r.g22 = r.detGram := by
  simpa [detValid, and_assoc] using h

theorem glueValid_of_mem (h : r.glueValid = true) {p u : ℤ} {w : ℤ × ℤ × ℤ}
    (hx : (p, u, w) ∈ r.glueData) :
    p * (r.detGram / p) = r.detGram ∧
      tripleZeroMod p (r.gramMulVec w) = true ∧
      tripleZeroMod p w = false ∧
      (r.gramPair w w + u * p) % (p * p) = 0 := by
  have hall := (List.all_eq_true.mp h) (p, u, w) hx
  simpa [Bool.and_eq_true, and_assoc] using hall

theorem primePairValid_cons {p : ℤ} {a b : ℤ × ℤ × ℤ} {t : List (ℤ × ℤ × ℤ)}
    (h : r.primePairValid p (a :: b :: t) = true) :
    (r.gramPair a b) % (p * p) = 0 ∧
      ∀ k ∈ List.range p.toNat,
        tripleZeroMod p (tripleSubSmul (k : ℤ) b a) = false := by
  rw [primePairValid] at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_true'] at h
  exact h

theorem genValid_parts (h : r.genValid = true) {j : ℕ} (hj : j < 3) :
    tripleZeroMod r.detGram
      (tripleSub (r.adjColumn j) (r.genColumn (r.coeff.getD j []))) = true := by
  simp only [genValid, Bool.and_eq_true] at h
  match j, hj with
  | 0, _ => exact h.1.1.2
  | 1, _ => exact h.1.2
  | 2, _ => exact h.2

/-! ### The pairing in terms of the certificate -/

theorem form_tripleToQ (v w : ℤ × ℤ × ℤ) :
    r.form (tripleToQ v) (tripleToQ w) = ((r.gramPair v w : ℤ) : ℚ) := by
  rw [form_apply]
  simp only [tripleToQ_apply_zero, tripleToQ_apply_one, tripleToQ_apply_two, gramPair]
  push_cast
  ring

theorem gramPair_eq_gramMulVec (hsym : r.symmValid = true) (v w : ℤ × ℤ × ℤ) :
    r.gramPair v w = (r.gramMulVec v).1 * w.1 + (r.gramMulVec v).2.1 * w.2.1
      + (r.gramMulVec v).2.2 * w.2.2 := by
  obtain ⟨h1, h2, h3⟩ := r.symmValid_iff.mp hsym
  simp only [gramPair, gramMulVec, ← h1, ← h2, ← h3]
  ring

/-! ### The glue vectors of a validated row -/

theorem smul_glueVec {p : ℤ} (hp : ((p : ℚ)) ≠ 0) (w : ℤ × ℤ × ℤ) :
    ((p : ℚ)) • glueVec p w = tripleToQ w := by
  rw [glueVec, smul_smul, mul_inv_cancel₀ hp, one_smul]

theorem glueVec_zsmul_mem (p : ℤ) (w : ℤ × ℤ × ℤ) (hp : ((p : ℚ)) ≠ 0) :
    (p : ℤ) • glueVec p w ∈ integerCube := by
  rw [← Int.cast_smul_eq_zsmul ℚ, smul_glueVec hp]
  exact tripleToQ_mem w

/-- **The glue vectors lie in the dual lattice.**  Condition 2 of §2.6. -/
theorem glueVec_mem_dual (hsym : r.symmValid = true) (hg : r.glueValid = true)
    {p u : ℤ} {w : ℤ × ℤ × ℤ} (hp : p ≠ 0) (hx : (p, u, w) ∈ r.glueData) :
    glueVec p w ∈ (r.form).dualSubmodule integerCube := by
  obtain ⟨-, hdvd, -, -⟩ := r.glueValid_of_mem hg hx
  obtain ⟨⟨k0, hk0⟩, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := tripleZeroMod_iff.mp hdvd
  have hpQ : ((p : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr hp
  rintro _ ⟨n, rfl⟩
  refine Submodule.mem_one.mpr ⟨k0 * n 0 + k1 * n 1 + k2 * n 2, ?_⟩
  rw [cubeEmbedding_eq_tripleToQ, glueVec]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, form_tripleToQ,
    r.gramPair_eq_gramMulVec hsym, hk0, hk1, hk2, algebraMap_int_eq, eq_intCast]
  field_simp
  push_cast
  ring

/-- **The diagonal of a glue vector.**  Condition 3 of §2.6: `q(w/p) ≡ −u/p`. -/
theorem glueVec_diag (hg : r.glueValid = true) {p u : ℤ} {w : ℤ × ℤ × ℤ} (hp : p ≠ 0)
    (hx : (p, u, w) ∈ r.glueData) :
    ∃ k : ℤ, ((p : ℚ)) * r.form (glueVec p w) (glueVec p w)
      = -(u : ℚ) + (p : ℚ) * (k : ℚ) := by
  obtain ⟨-, -, -, hmod⟩ := r.glueValid_of_mem hg hx
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero hmod
  have hpQ : ((p : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr hp
  have hkQ : ((r.gramPair w w : ℤ) : ℚ) = -(u : ℚ) * (p : ℚ) + (p : ℚ) * (p : ℚ) * (k : ℚ) := by
    have hcast := congrArg (fun x : ℤ => (x : ℚ)) hk
    push_cast at hcast
    linarith
  refine ⟨k, ?_⟩
  rw [glueVec]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, form_tripleToQ, hkQ]
  field_simp

/-- A glue vector is not in the lattice: it has exact order `p`. -/
theorem glueVec_not_mem (hg : r.glueValid = true) {p u : ℤ} {w : ℤ × ℤ × ℤ} (hp : p ≠ 0)
    (hx : (p, u, w) ∈ r.glueData) : glueVec p w ∉ integerCube := by
  obtain ⟨-, -, hnz, -⟩ := r.glueValid_of_mem hg hx
  have hpQ : ((p : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr hp
  intro hmem
  obtain ⟨n, hn⟩ := mem_integerCube.mp hmem
  have hcoord : ∀ i : Fin 3, ((p : ℚ)) * (n i : ℚ) = tripleToQ w i := by
    intro i
    rw [hn i]
    have hs := congrFun (smul_glueVec (p := p) hpQ w) i
    simpa [Pi.smul_apply, smul_eq_mul] using hs
  have hc0 : ((p : ℚ)) * (n 0 : ℚ) = (w.1 : ℚ) := by simpa using hcoord 0
  have hc1 : ((p : ℚ)) * (n 1 : ℚ) = (w.2.1 : ℚ) := by simpa using hcoord 1
  have hc2 : ((p : ℚ)) * (n 2 : ℚ) = (w.2.2 : ℚ) := by simpa using hcoord 2
  have hzero : tripleZeroMod p w = true := by
    refine tripleZeroMod_iff.mpr ⟨⟨n 0, ?_⟩, ⟨n 1, ?_⟩, ⟨n 2, ?_⟩⟩
    · exact_mod_cast hc0.symm
    · exact_mod_cast hc1.symm
    · exact_mod_cast hc2.symm
  rw [hzero] at hnz
  exact absurd hnz (by simp)

/-- **Same-prime glue vectors are orthogonal.**  Condition 4 of §2.6. -/
theorem glueVec_ortho {p : ℤ} (hp : p ≠ 0) {a b : ℤ × ℤ × ℤ} {t : List (ℤ × ℤ × ℤ)}
    (h : r.primePairValid p (a :: b :: t) = true) :
    r.form (glueVec p a) (glueVec p b) ∈ (1 : Submodule ℤ ℚ) := by
  obtain ⟨hmod, -⟩ := r.primePairValid_cons h
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero hmod
  have hpQ : ((p : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr hp
  refine Submodule.mem_one.mpr ⟨k, ?_⟩
  rw [glueVec, glueVec]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, form_tripleToQ, hk,
    algebraMap_int_eq, eq_intCast]
  field_simp
  push_cast
  ring

/-- **Same-prime glue vectors are independent modulo the lattice.**  Condition 4
of §2.6, in the form the glue construction consumes. -/
theorem glueVec_sub_smul_not_mem {p : ℤ} (hp : 0 < p) {a b : ℤ × ℤ × ℤ}
    {t : List (ℤ × ℤ × ℤ)} (h : r.primePairValid p (a :: b :: t) = true) (k : ℤ) :
    glueVec p b - ((k : ℚ)) • glueVec p a ∉ integerCube := by
  obtain ⟨-, hindep⟩ := r.primePairValid_cons h
  have hpne : p ≠ 0 := ne_of_gt hp
  have hpQ : ((p : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr hpne
  intro hmem
  obtain ⟨n, hn⟩ := mem_integerCube.mp hmem
  -- the numerators satisfy `b - k a ≡ 0 (mod p)`
  have hcoord : ∀ i : Fin 3,
      tripleToQ b i - (k : ℚ) * tripleToQ a i = ((p : ℚ)) * (n i : ℚ) := by
    intro i
    have hval := hn i
    have hb := congrFun (smul_glueVec (p := p) hpQ b) i
    have ha := congrFun (smul_glueVec (p := p) hpQ a) i
    have hexp : glueVec p b i - (k : ℚ) * glueVec p a i = (n i : ℚ) := by
      simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hval.symm
    have hb' : tripleToQ b i = (p : ℚ) * glueVec p b i := by
      simpa [Pi.smul_apply, smul_eq_mul] using hb.symm
    have ha' : tripleToQ a i = (p : ℚ) * glueVec p a i := by
      simpa [Pi.smul_apply, smul_eq_mul] using ha.symm
    rw [hb', ha', ← hexp]
    ring
  have hc0 : (b.1 : ℚ) - (k : ℚ) * (a.1 : ℚ) = ((p : ℚ)) * (n 0 : ℚ) := by
    simpa using hcoord 0
  have hc1 : (b.2.1 : ℚ) - (k : ℚ) * (a.2.1 : ℚ) = ((p : ℚ)) * (n 1 : ℚ) := by
    simpa using hcoord 1
  have hc2 : (b.2.2 : ℚ) - (k : ℚ) * (a.2.2 : ℚ) = ((p : ℚ)) * (n 2 : ℚ) := by
    simpa using hcoord 2
  have hdvdk : tripleZeroMod p (tripleSubSmul k b a) = true := by
    refine tripleZeroMod_iff.mpr ⟨⟨n 0, ?_⟩, ⟨n 1, ?_⟩, ⟨n 2, ?_⟩⟩
    · simp only [tripleSubSmul]
      exact_mod_cast hc0
    · simp only [tripleSubSmul]
      exact_mod_cast hc1
    · simp only [tripleSubSmul]
      exact_mod_cast hc2
  -- reduce the coefficient modulo `p`
  have hshift : tripleZeroMod p (tripleSubSmul (k % p) b a) = true := by
    obtain ⟨⟨c0, hc0⟩, ⟨c1, hc1⟩, ⟨c2, hc2⟩⟩ := tripleZeroMod_iff.mp hdvdk
    have hkey : k % p = k - p * (k / p) := Int.emod_def k p
    refine tripleZeroMod_iff.mpr ⟨⟨c0 + (k / p) * a.1, ?_⟩, ⟨c1 + (k / p) * a.2.1, ?_⟩,
      ⟨c2 + (k / p) * a.2.2, ?_⟩⟩
    · simp only [tripleSubSmul] at hc0 ⊢
      rw [hkey]
      linear_combination hc0
    · simp only [tripleSubSmul] at hc1 ⊢
      rw [hkey]
      linear_combination hc1
    · simp only [tripleSubSmul] at hc2 ⊢
      rw [hkey]
      linear_combination hc2
  have hrange : (k % p).toNat ∈ List.range p.toNat := by
    refine List.mem_range.mpr ?_
    have h1 : 0 ≤ k % p := Int.emod_nonneg k hpne
    have h2 : k % p < p := Int.emod_lt_of_pos k hp
    omega
  have hfalse := hindep _ hrange
  rw [Int.toNat_of_nonneg (Int.emod_nonneg k hpne), hshift] at hfalse
  exact absurd hfalse (by simp)

/-! ### The dual lattice is generated by the glue vectors -/

theorem smul_tripleToQ_listSum_mem (hg : r.glueValid = true) (hd : r.detGram ≠ 0) :
    ∀ L : List (ℤ × ℤ × ℤ × (ℤ × ℤ × ℤ)), (∀ x ∈ L, x.2 ∈ r.glueData) →
      ((r.detGram : ℚ))⁻¹ •
          tripleToQ ((L.map fun x => scaleTriple (x.1 * (r.detGram / x.2.1)) x.2.2.2).sum)
        ∈ r.glueSpan := by
  have hdQ : ((r.detGram : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr hd
  intro L
  induction L with
  | nil =>
      intro _
      simp only [List.map_nil, List.sum_nil, tripleToQ_zero, smul_zero]
      exact Submodule.zero_mem _
  | cons x t ih =>
      intro hmem
      have hx : (x.2.1, x.2.2.1, x.2.2.2) ∈ r.glueData := hmem x (List.mem_cons_self ..)
      have ht : ∀ y ∈ t, y.2 ∈ r.glueData := fun y hy => hmem y (List.mem_cons_of_mem _ hy)
      obtain ⟨hq, -, -, -⟩ := r.glueValid_of_mem hg hx
      have hpne : x.2.1 ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hq
        exact hd hq.symm
      have hpQ : ((x.2.1 : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr hpne
      have hqQ : ((x.2.1 : ℚ)) * ((r.detGram / x.2.1 : ℤ) : ℚ) = ((r.detGram : ℚ)) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hq
      simp only [List.map_cons, List.sum_cons, tripleToQ_add, smul_add]
      refine Submodule.add_mem _ ?_ (ih ht)
      have hhead : ((r.detGram : ℚ))⁻¹ •
          tripleToQ (scaleTriple (x.1 * (r.detGram / x.2.1)) x.2.2.2)
          = (x.1 : ℤ) • glueVec x.2.1 x.2.2.2 := by
        rw [tripleToQ_scaleTriple, smul_smul, ← Int.cast_smul_eq_zsmul ℚ, glueVec, smul_smul]
        congr 1
        field_simp
        push_cast
        linear_combination (x.1 : ℚ) * hqQ
      rw [hhead]
      exact Submodule.smul_mem _ _ (r.glueVec_mem_glueSpan hx)

theorem genColumn_smul_mem (hg : r.glueValid = true) (hd : r.detGram ≠ 0) (c : List ℤ) :
    ((r.detGram : ℚ))⁻¹ • tripleToQ (r.genColumn c) ∈ r.glueSpan :=
  r.smul_tripleToQ_listSum_mem hg hd (c.zip r.glueData)
    (fun _ hx => (List.of_mem_zip hx).2)

theorem adjColumn_smul_mem (hg : r.glueValid = true) (hgen : r.genValid = true)
    (hd : r.detGram ≠ 0) {j : ℕ} (hj : j < 3) :
    ((r.detGram : ℚ))⁻¹ • tripleToQ (r.adjColumn j) ∈ integerCube ⊔ r.glueSpan := by
  have hdQ : ((r.detGram : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr hd
  obtain ⟨s, hs⟩ := exists_scaleTriple_of_tripleZeroMod (r.genValid_parts hgen hj)
  have hsplit : r.adjColumn j = scaleTriple r.detGram s + r.genColumn (r.coeff.getD j []) := by
    have hcong := congrArg (fun z => z + r.genColumn (r.coeff.getD j [])) hs
    simpa [tripleSub_eq, sub_add_cancel] using hcong
  rw [hsplit, tripleToQ_add, smul_add]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_)
    (Submodule.mem_sup_right (r.genColumn_smul_mem hg hd _))
  rw [tripleToQ_scaleTriple, smul_smul, inv_mul_cancel₀ hdQ, one_smul]
  exact tripleToQ_mem s

/-- **Condition 5, semantically.**  For a validated row the dual of `ℤ³` is
generated over `ℤ³` by the glue vectors: `M^∨ = M + ∑ ℤ · mᵢ`. -/
theorem dual_integerCube_eq (h : rank15RowValid r = true) :
    (r.form).dualSubmodule integerCube = integerCube ⊔ r.glueSpan := by
  obtain ⟨-, hsym, hpd, hdet, hglue, -, -, hgen⟩ := r.rank15RowValid_parts h
  obtain ⟨-, -, hd3⟩ := r.posDefValid_minors hpd
  have hdne : r.detGram ≠ 0 := ne_of_gt hd3
  have hdQ : ((r.detGram : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr hdne
  obtain ⟨-, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := r.detValid_parts hdet
  refine le_antisymm ?_ (sup_le r.integerCube_isIntegral ?_)
  · intro v hv
    obtain ⟨n0, hn0⟩ := Submodule.mem_one.mp (hv _ (tripleToQ_mem (1, 0, 0)))
    obtain ⟨n1, hn1⟩ := Submodule.mem_one.mp (hv _ (tripleToQ_mem (0, 1, 0)))
    obtain ⟨n2, hn2⟩ := Submodule.mem_one.mp (hv _ (tripleToQ_mem (0, 0, 1)))
    have hsymm := r.form_isSymm hsym
    have hN0 : (n0 : ℚ) = (r.g00 : ℚ) * v 0 + (r.g01 : ℚ) * v 1 + (r.g02 : ℚ) * v 2 := by
      have := hn0.trans (hsymm.eq v (tripleToQ (1, 0, 0)))
      rw [form_apply] at this
      simpa using this
    have hN1 : (n1 : ℚ) = (r.g10 : ℚ) * v 0 + (r.g11 : ℚ) * v 1 + (r.g12 : ℚ) * v 2 := by
      have := hn1.trans (hsymm.eq v (tripleToQ (0, 1, 0)))
      rw [form_apply] at this
      simpa using this
    have hN2 : (n2 : ℚ) = (r.g20 : ℚ) * v 0 + (r.g21 : ℚ) * v 1 + (r.g22 : ℚ) * v 2 := by
      have := hn2.trans (hsymm.eq v (tripleToQ (0, 0, 1)))
      rw [form_apply] at this
      simpa using this
    have E1 : (r.a00 : ℚ) * (r.g00 : ℚ) + (r.a01 : ℚ) * (r.g10 : ℚ)
        + (r.a02 : ℚ) * (r.g20 : ℚ) = (r.detGram : ℚ) := by exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) e1
    have E2 : (r.a00 : ℚ) * (r.g01 : ℚ) + (r.a01 : ℚ) * (r.g11 : ℚ)
        + (r.a02 : ℚ) * (r.g21 : ℚ) = 0 := by exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) e2
    have E3 : (r.a00 : ℚ) * (r.g02 : ℚ) + (r.a01 : ℚ) * (r.g12 : ℚ)
        + (r.a02 : ℚ) * (r.g22 : ℚ) = 0 := by exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) e3
    have E4 : (r.a10 : ℚ) * (r.g00 : ℚ) + (r.a11 : ℚ) * (r.g10 : ℚ)
        + (r.a12 : ℚ) * (r.g20 : ℚ) = 0 := by exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) e4
    have E5 : (r.a10 : ℚ) * (r.g01 : ℚ) + (r.a11 : ℚ) * (r.g11 : ℚ)
        + (r.a12 : ℚ) * (r.g21 : ℚ) = (r.detGram : ℚ) := by exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) e5
    have E6 : (r.a10 : ℚ) * (r.g02 : ℚ) + (r.a11 : ℚ) * (r.g12 : ℚ)
        + (r.a12 : ℚ) * (r.g22 : ℚ) = 0 := by exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) e6
    have E7 : (r.a20 : ℚ) * (r.g00 : ℚ) + (r.a21 : ℚ) * (r.g10 : ℚ)
        + (r.a22 : ℚ) * (r.g20 : ℚ) = 0 := by exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) e7
    have E8 : (r.a20 : ℚ) * (r.g01 : ℚ) + (r.a21 : ℚ) * (r.g11 : ℚ)
        + (r.a22 : ℚ) * (r.g21 : ℚ) = 0 := by exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) e8
    have E9 : (r.a20 : ℚ) * (r.g02 : ℚ) + (r.a21 : ℚ) * (r.g12 : ℚ)
        + (r.a22 : ℚ) * (r.g22 : ℚ) = (r.detGram : ℚ) := by exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) e9
    have hdecomp : v = (n0 : ℤ) • (((r.detGram : ℚ))⁻¹ • tripleToQ (r.adjColumn 0))
        + (n1 : ℤ) • (((r.detGram : ℚ))⁻¹ • tripleToQ (r.adjColumn 1))
        + (n2 : ℤ) • (((r.detGram : ℚ))⁻¹ • tripleToQ (r.adjColumn 2)) := by
      have hcases : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
      funext i
      rcases hcases i with rfl | rfl | rfl
      · simp only [← Int.cast_smul_eq_zsmul ℚ, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          adjColumn, tripleToQ_apply_zero]
        field_simp
        rw [hN0, hN1, hN2]
        linear_combination (-(v 0)) * E1 + (-(v 1)) * E2 + (-(v 2)) * E3
      · simp only [← Int.cast_smul_eq_zsmul ℚ, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          adjColumn, tripleToQ_apply_one]
        field_simp
        rw [hN0, hN1, hN2]
        linear_combination (-(v 0)) * E4 + (-(v 1)) * E5 + (-(v 2)) * E6
      · simp only [← Int.cast_smul_eq_zsmul ℚ, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          adjColumn, tripleToQ_apply_two]
        field_simp
        rw [hN0, hN1, hN2]
        linear_combination (-(v 0)) * E7 + (-(v 1)) * E8 + (-(v 2)) * E9
    rw [hdecomp]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
      exact Submodule.smul_mem _ _ (r.adjColumn_smul_mem hglue hgen hdne (by omega))
  · rw [glueSpan, Submodule.span_le]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have hx' : (x.1, x.2.1, x.2.2) ∈ r.glueData := hx
    have hp : x.1 ≠ 0 := by
      rcases r.glueData_prime hx with h | h <;> rw [h] <;> norm_num
    exact r.glueVec_mem_dual hsym hglue hp hx'

end Rank15ComplementRow

end Soundness

end SRG266
