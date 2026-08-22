/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.CherryRecut

/-!
# Semantic bridge for the residual cherry-cover obstruction

This file proves that the finite obstruction used at the audit boundary has
exactly the advertised design-theoretic meaning.  A cherry cover together with
a `Residual165` is completed to a quasi-symmetric `2-(56, 12, 9)` design by
putting back the deleted point.  Conversely, the existing deletion and
recoordinatisation construction extracts such a residual cherry cover from
any quasi-symmetric design.
-/

open scoped BigOperators Matrix

namespace SRG266

universe u

/-- **Semantic audit bridge.**  The project-local hypothetical-graph predicate
is exactly mathlib's standard strongly regular graph predicate with parameters
`(266, 45, 0, 9)`. -/
theorem isHypothetical_iff {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsHypothetical G ↔ G.IsSRGWith 266 45 0 9 :=
  Iff.rfl

end SRG266

namespace SRG266.QuasiSymmetric

private theorem sum_indicator {ι P : Type*} [Fintype ι] [DecidableEq P]
    (f : ι → Finset P) (p : P) :
    (∑ i, if p ∈ f i then (1 : ℤ) else 0) = pairCount f p p := by
  calc
    _ = ∑ i, if p ∈ f i ∧ p ∈ f i then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simp
    _ = ((Finset.univ.filter fun i => p ∈ f i ∧ p ∈ f i).card : ℤ) := by simp
    _ = _ := rfl

private theorem sum_double_indicator {ι P : Type*} [Fintype ι] [DecidableEq P]
    (f : ι → Finset P) (p q : P) :
    (∑ i, (if p ∈ f i then (1 : ℤ) else 0) *
      (if q ∈ f i then (1 : ℤ) else 0)) = pairCount f p q := by
  calc
    _ = ∑ i, if p ∈ f i ∧ q ∈ f i then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hp : p ∈ f i <;> by_cases hq : q ∈ f i <;> simp [hp, hq]
    _ = ((Finset.univ.filter fun i => p ∈ f i ∧ q ∈ f i).card : ℤ) := by simp
    _ = _ := rfl

private theorem sum_double_indicator_eq_inter_card {P : Type*} [Fintype P]
    [DecidableEq P] (s t : Finset P) :
    (∑ p, (if p ∈ s then (1 : ℤ) else 0) *
      (if p ∈ t then (1 : ℤ) else 0)) = (s ∩ t).card := by
  calc
    _ = ∑ p, if p ∈ s ∩ t then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hs : p ∈ s <;> by_cases ht : p ∈ t <;> simp [hs, ht]
    _ = _ := by
      have hfilter :
          (Finset.univ.filter fun p : P => p ∈ s ∩ t) = s ∩ t := by
        ext p
        simp
      rw [← hfilter]
      simp

namespace Residual165

variable {C : CherryCover} (R : Residual165 C.toDerived45)

/-- The `210 = 45 + 165` completed blocks on the `56 = 1 + 55` points.
The new point lies on every derived block and on no residual block. -/
def completedBlock : (Fin 45 ⊕ Fin 165) → Finset (Option Edge11)
  | Sum.inl i => insert none ((C.g i).image some)
  | Sum.inr n => (R.res n).image some

/-- The binary incidence matrix of the completed design. -/
def completedIncidence : Matrix (Option Edge11) (Fin 45 ⊕ Fin 165) ℤ :=
  fun p B => if p ∈ R.completedBlock B then 1 else 0

@[simp] theorem none_mem_completedBlock_derived (i : Fin 45) :
    none ∈ R.completedBlock (Sum.inl i) := by
  simp [completedBlock]

@[simp] theorem none_not_mem_completedBlock_residual (n : Fin 165) :
    none ∉ R.completedBlock (Sum.inr n) := by
  simp [completedBlock]

@[simp] theorem some_mem_completedBlock_derived (e : Edge11) (i : Fin 45) :
    some e ∈ R.completedBlock (Sum.inl i) ↔ e ∈ C.g i := by
  simp [completedBlock]

@[simp] theorem some_mem_completedBlock_residual (e : Edge11) (n : Fin 165) :
    some e ∈ R.completedBlock (Sum.inr n) ↔ e ∈ R.res n := by
  simp [completedBlock]

private theorem completedBlock_derived_inter_derived (i j : Fin 45) :
    R.completedBlock (Sum.inl i) ∩ R.completedBlock (Sum.inl j) =
      insert none (((C.g i) ∩ (C.g j)).image some) := by
  ext p
  cases p <;> simp

private theorem completedBlock_derived_inter_residual (i : Fin 45) (n : Fin 165) :
    R.completedBlock (Sum.inl i) ∩ R.completedBlock (Sum.inr n) =
      ((C.g i) ∩ (R.res n)).image some := by
  ext p
  cases p <;> simp

private theorem completedBlock_residual_inter_derived (m : Fin 165) (j : Fin 45) :
    R.completedBlock (Sum.inr m) ∩ R.completedBlock (Sum.inl j) =
      ((R.res m) ∩ (C.g j)).image some := by
  ext p
  cases p <;> simp

private theorem completedBlock_residual_inter_residual (m n : Fin 165) :
    R.completedBlock (Sum.inr m) ∩ R.completedBlock (Sum.inr n) =
      ((R.res m) ∩ (R.res n)).image some := by
  ext p
  cases p <;> simp

private theorem completed_point_gram (p q : Option Edge11) :
    (R.completedIncidence * R.completedIncidence.transpose) p q =
      if p = q then 45 else 9 := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [Matrix.transpose_apply]
  cases p with
  | none =>
      cases q with
      | none => simp [completedIncidence]
      | some q =>
          simp only [completedIncidence, none_mem_completedBlock_derived,
            none_not_mem_completedBlock_residual,
            some_mem_completedBlock_derived, some_mem_completedBlock_residual,
            one_mul, zero_mul, Finset.sum_const_zero, add_zero,
            reduceCtorEq, ↓reduceIte]
          rw [sum_indicator C.g q, C.edge_rep]
          norm_num
  | some p =>
      cases q with
      | none =>
          simp only [completedIncidence, none_mem_completedBlock_derived,
            none_not_mem_completedBlock_residual,
            some_mem_completedBlock_derived, some_mem_completedBlock_residual,
            mul_one, mul_zero, Finset.sum_const_zero, add_zero,
            reduceCtorEq, ↓reduceIte]
          rw [sum_indicator C.g p, C.edge_rep]
          norm_num
      | some q =>
          by_cases hpq : p = q
          · subst q
            simp only [completedIncidence, some_mem_completedBlock_derived,
              some_mem_completedBlock_residual, ↓reduceIte]
            rw [sum_double_indicator C.g p p, sum_double_indicator R.res p p]
            change (pairCount C.g p p : ℤ) + (R.pairMult p p : ℤ) = 45
            rw [C.edge_rep, R.pairMult_self]
            norm_num
          · have hsome : some p ≠ some q := fun h => hpq (Option.some.inj h)
            simp only [completedIncidence, some_mem_completedBlock_derived,
              some_mem_completedBlock_residual, hsome, ↓reduceIte]
            rw [sum_double_indicator C.g p q, sum_double_indicator R.res p q]
            change (C.toDerived45.pairMult p q : ℤ) +
              (R.pairMult p q : ℤ) = 9
            exact_mod_cast residual_pairMult_add R hpq

private theorem completed_block_size (B : Fin 45 ⊕ Fin 165) :
    incidenceColumnSum R.completedIncidence B = 12 := by
  cases B with
  | inl i =>
      rw [incidenceColumnSum, Fintype.sum_option]
      simp [completedIncidence, C.block_card i]
  | inr n =>
      rw [incidenceColumnSum, Fintype.sum_option]
      simp [completedIncidence, R.res_card n]

private theorem completed_block_intersections {B D : Fin 45 ⊕ Fin 165}
    (hBD : B ≠ D) :
    (R.completedIncidence.transpose * R.completedIncidence) B D = 0 ∨
      (R.completedIncidence.transpose * R.completedIncidence) B D = 3 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, completedIncidence,
    sum_double_indicator_eq_inter_card]
  cases B with
  | inl i =>
      cases D with
      | inl j =>
          have hij : i ≠ j := fun h => hBD (congrArg Sum.inl h)
          rw [R.completedBlock_derived_inter_derived i j]
          have hnone : none ∉ ((C.g i ∩ C.g j).image some) := by simp
          rw [Finset.card_insert_of_notMem hnone,
            Finset.card_image_of_injective _ (Option.some_injective _),
            C.pair_meet i j hij]
          exact Or.inr rfl
      | inr n =>
          rw [R.completedBlock_derived_inter_residual i n,
            Finset.card_image_of_injective _ (Option.some_injective _)]
          exact_mod_cast R.cross_meet i n
  | inr m =>
      cases D with
      | inl j =>
          rw [R.completedBlock_residual_inter_derived m j,
            Finset.card_image_of_injective _ (Option.some_injective _),
            Finset.inter_comm]
          exact_mod_cast R.cross_meet j m
      | inr n =>
          have hmn : m ≠ n := fun h => hBD (congrArg Sum.inr h)
          rw [R.completedBlock_residual_inter_residual m n,
            Finset.card_image_of_injective _ (Option.some_injective _)]
          exact_mod_cast R.res_meet m n hmn

/-- Put the deleted point back into a cherry cover carrying a residual
structure.  The result is a quasi-symmetric `2-(56, 12, 9)` design with block
intersection numbers `0` and `3`. -/
def toQuasiSymmetricDesign56 : QuasiSymmetricDesign56 where
  Point := Option Edge11
  Block := Fin 45 ⊕ Fin 165
  pointFintype := inferInstance
  blockFintype := inferInstance
  pointDecidableEq := inferInstance
  blockDecidableEq := inferInstance
  incidence := R.completedIncidence
  point_card := by rw [Fintype.card_option, Edge11.card_edge11]
  block_card := by simp
  binary := by
    intro p B
    simp only [completedIncidence]
    split <;> simp_all
  point_gram := R.completed_point_gram
  block_size := R.completed_block_size
  block_intersections := R.completed_block_intersections

end Residual165

/-- Existence of a residual structure on a cherry cover is equivalent to
existence of a quasi-symmetric `2-(56, 12, 9)` design with intersection
numbers `0` and `3`. -/
theorem exists_residualCherryCover_iff_nonempty_quasiSymmetricDesign56 :
    (∃ C : CherryCover, Nonempty (Residual165 C.toDerived45)) ↔
      Nonempty QuasiSymmetricDesign56.{0} := by
  constructor
  · rintro ⟨C, ⟨R⟩⟩
    exact ⟨R.toQuasiSymmetricDesign56⟩
  · rintro ⟨Q⟩
    classical
    by_contra hExists
    have hNoResidual : NoResidualCherryCover := fun C =>
      ⟨fun R => hExists ⟨C, ⟨R⟩⟩⟩
    exact (noQuasiSymmetricDesign56_of_noResidualCherryCover hNoResidual).false Q

/-- The cherry-cover obstruction is equivalent to quasi-symmetric design
nonexistence. -/
theorem noResidualCherryCover_iff_noQuasiSymmetricDesign56 :
    NoResidualCherryCover ↔ NoQuasiSymmetricDesign56.{0} := by
  constructor
  · exact noQuasiSymmetricDesign56_of_noResidualCherryCover
  · intro h C
    exact ⟨fun R => h.false R.toQuasiSymmetricDesign56⟩

end SRG266.QuasiSymmetric
