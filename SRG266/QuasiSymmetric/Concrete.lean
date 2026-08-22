/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.CocliqueDesign

/-!
# Universe collapse for the forbidden quasi-symmetric design

`SRG266.NoQuasiSymmetricDesign56` is stated for the universe-polymorphic
structure `SRG266.QuasiSymmetricDesign56`, whose point and block types are
arbitrary.  The finite argument uses a fixed `56 × 210` integer matrix, so the
structure is transported to the concrete subtype `ConcreteQSD56`.

This file defines `ConcreteQSD56`, its four field accessors, and

* `SRG266.QuasiSymmetric.noQuasiSymmetricDesign56_of_concrete` —
  `IsEmpty ConcreteQSD56` implies `NoQuasiSymmetricDesign56` in every universe.

The transport uses `Fintype.equivFinOfCardEq` on both index types.
-/

open scoped BigOperators Matrix

namespace SRG266.QuasiSymmetric

/-- A concrete presentation of a quasi-symmetric `2-(56, 12, 9)` design with
intersection numbers `0` and `3`: a binary `56 × 210` integer matrix whose
point Gram matrix has diagonal `45` and off-diagonal `9`, whose columns sum to
`12`, and whose off-diagonal block Gram entries are `0` or `3`.

This is the universe-free form of `SRG266.QuasiSymmetricDesign56`. -/
def ConcreteQSD56 : Type :=
  { M : Matrix (Fin 56) (Fin 210) ℤ //
      (∀ p B, M p B * M p B = M p B) ∧
      (∀ p q, (M * M.transpose) p q = if p = q then 45 else 9) ∧
      (∀ B, incidenceColumnSum M B = 12) ∧
      (∀ B D, B ≠ D → (M.transpose * M) B D = 0 ∨ (M.transpose * M) B D = 3) }

namespace ConcreteQSD56

variable (Q : ConcreteQSD56)

/-- The underlying incidence matrix. -/
def matrix : Matrix (Fin 56) (Fin 210) ℤ := Q.1

/-- Every entry of the incidence matrix is idempotent, hence `0` or `1`. -/
theorem binary (p : Fin 56) (B : Fin 210) :
    Q.matrix p B * Q.matrix p B = Q.matrix p B := Q.2.1 p B

/-- The point Gram matrix has diagonal `45` and off-diagonal `9`. -/
theorem point_gram (p q : Fin 56) :
    (Q.matrix * Q.matrix.transpose) p q = if p = q then 45 else 9 := Q.2.2.1 p q

/-- Every block has size `12`. -/
theorem block_size (B : Fin 210) : incidenceColumnSum Q.matrix B = 12 :=
  Q.2.2.2.1 B

/-- Distinct blocks meet in `0` or `3` points. -/
theorem block_intersections {B D : Fin 210} (h : B ≠ D) :
    (Q.matrix.transpose * Q.matrix) B D = 0 ∨
      (Q.matrix.transpose * Q.matrix) B D = 3 := Q.2.2.2.2 B D h

/-- Every entry of the incidence matrix is `0` or `1`. -/
theorem entry_cases (p : Fin 56) (B : Fin 210) :
    Q.matrix p B = 0 ∨ Q.matrix p B = 1 := by
  have h := Q.binary p B
  have hfactor : Q.matrix p B * (Q.matrix p B - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfactor with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linarith)

/-- Every point lies on exactly `45` blocks (as an integer row sum). -/
theorem row_sum (p : Fin 56) : ∑ B, Q.matrix p B = 45 :=
  incidence_row_sum_eq_forty_five Q.matrix Q.binary Q.point_gram p

end ConcreteQSD56

universe u

/-- If no concrete `56 × 210` incidence matrix satisfies
the quasi-symmetric constraints, then the universe-polymorphic external input
`SRG266.NoQuasiSymmetricDesign56` holds.

The proof transports a hypothetical design along the equivalences
`Point ≃ Fin 56` and `Block ≃ Fin 210` supplied by its cardinality fields. -/
theorem noQuasiSymmetricDesign56_of_concrete (h : IsEmpty ConcreteQSD56) :
    NoQuasiSymmetricDesign56.{u} := by
  refine ⟨fun design => h.false ?_⟩
  letI : Fintype design.Point := design.pointFintype
  letI : Fintype design.Block := design.blockFintype
  letI : DecidableEq design.Point := design.pointDecidableEq
  letI : DecidableEq design.Block := design.blockDecidableEq
  classical
  set ep : design.Point ≃ Fin 56 := Fintype.equivFinOfCardEq design.point_card with hep
  set eb : design.Block ≃ Fin 210 := Fintype.equivFinOfCardEq design.block_card with heb
  clear_value ep eb
  clear hep heb
  refine ⟨fun p B => design.incidence (ep.symm p) (eb.symm B), ?_, ?_, ?_, ?_⟩
  · intro p B
    exact design.binary (ep.symm p) (eb.symm B)
  · intro p q
    have hsum :
        (∑ B : Fin 210,
            design.incidence (ep.symm p) (eb.symm B) *
              design.incidence (ep.symm q) (eb.symm B)) =
          ∑ D : design.Block,
            design.incidence (ep.symm p) D * design.incidence (ep.symm q) D :=
      Equiv.sum_comp eb.symm
        (fun D => design.incidence (ep.symm p) D * design.incidence (ep.symm q) D)
    have hgram := design.point_gram (ep.symm p) (ep.symm q)
    rw [Matrix.mul_apply] at hgram ⊢
    simp only [Matrix.transpose_apply] at hgram ⊢
    rw [hsum, hgram]
    by_cases hpq : p = q
    · subst hpq
      simp
    · rw [if_neg hpq, if_neg fun hcontra => hpq (ep.symm.injective hcontra)]
  · intro B
    have hsum :
        (∑ p : Fin 56, design.incidence (ep.symm p) (eb.symm B)) =
          ∑ P : design.Point, design.incidence P (eb.symm B) :=
      Equiv.sum_comp ep.symm (fun P => design.incidence P (eb.symm B))
    have hcol := design.block_size (eb.symm B)
    simp only [incidenceColumnSum] at hcol ⊢
    rw [hsum, hcol]
  · intro B D hBD
    have hne : eb.symm B ≠ eb.symm D := fun hcontra => hBD (eb.symm.injective hcontra)
    have hsum :
        (∑ p : Fin 56,
            design.incidence (ep.symm p) (eb.symm B) *
              design.incidence (ep.symm p) (eb.symm D)) =
          ∑ P : design.Point,
            design.incidence P (eb.symm B) * design.incidence P (eb.symm D) :=
      Equiv.sum_comp ep.symm
        (fun P => design.incidence P (eb.symm B) * design.incidence P (eb.symm D))
    have hinter := design.block_intersections hne
    rw [Matrix.mul_apply] at hinter ⊢
    simp only [Matrix.transpose_apply] at hinter ⊢
    rw [hsum]
    exact hinter

end SRG266.QuasiSymmetric
