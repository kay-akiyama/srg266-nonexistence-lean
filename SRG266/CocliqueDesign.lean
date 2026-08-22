/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.NotOneIntegrable
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# The design induced by a Delsarte coclique

This file develops the graph-specific passage from an independent set of
size 56 in a hypothetical `srg(266,45,0,9)` to the quasi-symmetric design
used in the one-integrability obstruction.

The first ingredient is an elementary matrix lemma: a binary `56 × 210`
incidence matrix whose point Gram matrix has diagonal 45 and off-diagonal 9
has constant column sum 12.  The proof is the exact integral
sum-of-squares form of equality in the Delsarte bound.
-/

open scoped BigOperators Matrix

namespace SRG266

/-- The sum of a column of a finite integer matrix. -/
def incidenceColumnSum
    {P B : Type*} [Fintype P]
    (M : Matrix P B ℤ) (b : B) : ℤ :=
  ∑ p, M p b

section ConstantColumnSum

variable {P B : Type*} [Fintype P] [Fintype B]
variable [DecidableEq P]

omit [Fintype P] in
theorem incidence_row_sum_eq_forty_five
    (M : Matrix P B ℤ)
    (hbinary : ∀ p b, M p b * M p b = M p b)
    (hgram : ∀ p q, (M * M.transpose) p q =
      if p = q then 45 else 9)
    (p : P) :
    ∑ b, M p b = 45 := by
  calc
    (∑ b, M p b) = ∑ b, M p b * M p b := by
      apply Finset.sum_congr rfl
      intro b _
      exact (hbinary p b).symm
    _ = (M * M.transpose) p p := by
      rw [Matrix.mul_apply]
      rfl
    _ = 45 := by simp [hgram]

theorem incidence_total_column_sum
    (M : Matrix P B ℤ)
    (hbinary : ∀ p b, M p b * M p b = M p b)
    (hgram : ∀ p q, (M * M.transpose) p q =
      if p = q then 45 else 9)
    (hPcard : Fintype.card P = 56) :
    ∑ b, incidenceColumnSum M b = 2520 := by
  calc
    (∑ b, incidenceColumnSum M b) =
        ∑ p, ∑ b, M p b := by
      simp only [incidenceColumnSum]
      rw [Finset.sum_comm]
    _ = ∑ _p : P, (45 : ℤ) := by
      apply Finset.sum_congr rfl
      intro p _
      exact incidence_row_sum_eq_forty_five M hbinary hgram p
    _ = 2520 := by simp [hPcard]

theorem incidence_total_column_sum_sq
    (M : Matrix P B ℤ)
    (hgram : ∀ p q, (M * M.transpose) p q =
      if p = q then 45 else 9)
    (hPcard : Fintype.card P = 56) :
    ∑ b, incidenceColumnSum M b * incidenceColumnSum M b = 30240 := by
  calc
    (∑ b, incidenceColumnSum M b * incidenceColumnSum M b) =
        ∑ p, ∑ q, ∑ b, M p b * M q b := by
      simp only [incidenceColumnSum]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
    _ = ∑ p, ∑ q, (M * M.transpose) p q := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      rw [Matrix.mul_apply]
      rfl
    _ = ∑ p, ∑ q, (if p = q then (45 : ℤ) else 9) := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      exact hgram p q
    _ = 30240 := by
      have hrow :
          ∀ p : P, ∑ q : P, (if p = q then (45 : ℤ) else 9) = 540 := by
        intro p
        calc
          (∑ q : P, (if p = q then (45 : ℤ) else 9)) =
              ∑ q : P, (9 + if p = q then (36 : ℤ) else 0) := by
            apply Finset.sum_congr rfl
            intro q _
            by_cases hpq : p = q <;> simp [hpq]
          _ = 9 * Fintype.card P + 36 := by
            rw [Finset.sum_add_distrib]
            simp
            ring
          _ = 540 := by rw [hPcard]; norm_num
      simp_rw [hrow]
      simp [hPcard]

/-- Exact equality in the two incidence moments forces every block to have
size 12. -/
theorem incidence_column_sum_eq_twelve
    (M : Matrix P B ℤ)
    (hbinary : ∀ p b, M p b * M p b = M p b)
    (hgram : ∀ p q, (M * M.transpose) p q =
      if p = q then 45 else 9)
    (hPcard : Fintype.card P = 56)
    (hBcard : Fintype.card B = 210)
    (b : B) :
    incidenceColumnSum M b = 12 := by
  have hsum :=
    incidence_total_column_sum M hbinary hgram hPcard
  have hsumsq :=
    incidence_total_column_sum_sq M hgram hPcard
  have hzero :
      ∑ c : B,
        (incidenceColumnSum M c - 12) *
          (incidenceColumnSum M c - 12) = 0 := by
    calc
      (∑ c : B,
          (incidenceColumnSum M c - 12) *
            (incidenceColumnSum M c - 12)) =
          (∑ c, incidenceColumnSum M c * incidenceColumnSum M c) -
            24 * (∑ c, incidenceColumnSum M c) +
              144 * Fintype.card B := by
        have hright :
            (∑ c : B, incidenceColumnSum M c * 12) =
              (∑ c : B, incidenceColumnSum M c) * 12 :=
          (Finset.sum_mul (Finset.univ : Finset B)
            (fun c => incidenceColumnSum M c) (12 : ℤ)).symm
        have hleft :
            (∑ c : B, 12 * incidenceColumnSum M c) =
              12 * ∑ c : B, incidenceColumnSum M c :=
          (Finset.mul_sum (Finset.univ : Finset B)
            (fun c => incidenceColumnSum M c) (12 : ℤ)).symm
        have hconst :
            (∑ _c : B, (12 : ℤ) * 12) =
              144 * Fintype.card B := by
          simp
          ring
        simp_rw [sub_mul, mul_sub]
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          Finset.sum_sub_distrib, hright, hleft, hconst]
        ring
      _ = 0 := by rw [hsum, hsumsq, hBcard]; norm_num
  have hbzero :
      (incidenceColumnSum M b - 12) *
        (incidenceColumnSum M b - 12) = 0 := by
    exact
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun c _ => mul_self_nonneg (incidenceColumnSum M c - 12))).mp
          hzero b (Finset.mem_univ b)
  nlinarith

end ConstantColumnSum

section CocliqueIncidence

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Points of the design induced by a coclique. -/
abbrev CocliquePoint (C : Finset V) := ↥C

/-- Vertices outside the coclique, used as block occurrences. -/
abbrev CocliqueOutside (C : Finset V) := ↥Cᶜ

omit [Fintype V] [DecidableEq V] in
theorem cocliquePoint_card
    (C : Finset V) (hCcard : C.card = 56) :
    Fintype.card (CocliquePoint C) = 56 := by
  simpa using hCcard

theorem cocliqueOutside_card
    (hG : IsHypothetical G)
    (C : Finset V) (hCcard : C.card = 56) :
    Fintype.card (CocliqueOutside C) = 210 := by
  rw [Fintype.card_coe, Finset.card_compl, hG.card, hCcard]

omit [Fintype V] [DecidableRel G.Adj] in
theorem not_adj_of_mem_indepSet
    {C : Finset V}
    (hC : G.IsIndepSet (C : Set V))
    {u v : V} (hu : u ∈ C) (hv : v ∈ C) :
    ¬G.Adj u v := by
  by_cases huv : u = v
  · subst v
    exact G.loopless.irrefl u
  · rw [SimpleGraph.isIndepSet_iff] at hC
    exact hC hu hv huv

/-- The incidence matrix between coclique points and outside vertices. -/
def cocliqueIncidenceMatrix (C : Finset V) :
    Matrix (CocliquePoint C) (CocliqueOutside C) ℤ :=
  fun p B => if G.Adj (p : V) (B : V) then 1 else 0

theorem cocliqueIncidenceMatrix_binary
    (C : Finset V)
    (p : CocliquePoint C) (B : CocliqueOutside C) :
    cocliqueIncidenceMatrix G C p B *
        cocliqueIncidenceMatrix G C p B =
      cocliqueIncidenceMatrix G C p B := by
  simp [cocliqueIncidenceMatrix]

/-- Outside vertices adjacent to both of two coclique points. -/
def cocliqueCommonOutside
    (C : Finset V) (p q : CocliquePoint C) :
    Finset (CocliqueOutside C) :=
  Finset.univ.filter fun B =>
    G.Adj (p : V) (B : V) ∧ G.Adj (q : V) (B : V)

/-- Every common neighbor of two coclique points lies outside the coclique. -/
def commonNeighborsEquivCocliqueCommonOutside
    {C : Finset V}
    (hC : G.IsIndepSet (C : Set V))
    (p q : CocliquePoint C) :
    G.commonNeighbors (p : V) (q : V) ≃
      ↥(cocliqueCommonOutside G C p q) where
  toFun z := by
    have hznot : (z : V) ∉ C := by
      intro hz
      exact
        (not_adj_of_mem_indepSet G hC p.property hz) z.property.1
    let B : CocliqueOutside C := ⟨z, by simpa using hznot⟩
    refine ⟨B, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact z.property
  invFun B := by
    have hB := Finset.mem_filter.mp B.property
    exact ⟨B.1, hB.2⟩
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv B := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem cocliqueIncidence_mul_transpose_apply_card
    {C : Finset V}
    (hC : G.IsIndepSet (C : Set V))
    (p q : CocliquePoint C) :
    (cocliqueIncidenceMatrix G C *
        (cocliqueIncidenceMatrix G C).transpose) p q =
      Fintype.card (G.commonNeighbors (p : V) (q : V)) := by
  rw [Matrix.mul_apply]
  calc
    (∑ B,
        cocliqueIncidenceMatrix G C p B *
          (cocliqueIncidenceMatrix G C).transpose B q) =
        ((cocliqueCommonOutside G C p q).card : ℤ) := by
      simp only [Matrix.transpose_apply, cocliqueIncidenceMatrix,
        ite_zero_mul_ite_zero, one_mul, Finset.sum_boole]
      norm_cast
    _ = Fintype.card (G.commonNeighbors (p : V) (q : V)) := by
      norm_cast
      rw [← Fintype.card_coe]
      exact
        (Fintype.card_congr
          (commonNeighborsEquivCocliqueCommonOutside G hC p q)).symm

/-- The point Gram matrix of the coclique incidence structure has diagonal
45 and off-diagonal 9. -/
theorem cocliqueIncidence_mul_transpose_apply
    (hG : IsHypothetical G)
    {C : Finset V}
    (hC : G.IsIndepSet (C : Set V))
    (p q : CocliquePoint C) :
    (cocliqueIncidenceMatrix G C *
        (cocliqueIncidenceMatrix G C).transpose) p q =
      if p = q then 45 else 9 := by
  rw [cocliqueIncidence_mul_transpose_apply_card G hC p q]
  by_cases hpq : p = q
  · subst q
    rw [if_pos rfl]
    have hdiag :
        Fintype.card (G.commonNeighbors (p : V) (p : V)) = 45 := by
      have hn :
          Fintype.card (G.neighborSet (p : V)) = 45 := by
        rw [G.card_neighborSet_eq_degree, hG.regular]
      simpa only [G.commonNeighbors_eq, Set.inter_self] using hn
    exact_mod_cast hdiag
  · rw [if_neg hpq]
    have hpqv : (p : V) ≠ (q : V) := by
      intro h
      exact hpq (Subtype.ext h)
    have hnot :
        ¬G.Adj (p : V) (q : V) :=
      not_adj_of_mem_indepSet G hC p.property q.property
    exact_mod_cast hG.of_not_adj hpqv hnot

theorem cocliqueIncidenceMatrix_column_sum
    (hG : IsHypothetical G)
    {C : Finset V}
    (hCcard : C.card = 56)
    (hC : G.IsIndepSet (C : Set V))
    (B : CocliqueOutside C) :
    incidenceColumnSum (cocliqueIncidenceMatrix G C) B = 12 := by
  apply incidence_column_sum_eq_twelve
    (cocliqueIncidenceMatrix G C)
    (cocliqueIncidenceMatrix_binary G C)
    (cocliqueIncidence_mul_transpose_apply G hG hC)
  · exact cocliquePoint_card C hCcard
  · exact cocliqueOutside_card G hG C hCcard

/-- Split a finite sum into a finset and its complement, expressed as sums
over the corresponding subtypes. -/
theorem sum_cocliquePoint_add_sum_cocliqueOutside
    (C : Finset V) (f : V → ℤ) :
    (∑ p : CocliquePoint C, f p) +
        (∑ B : CocliqueOutside C, f B) =
      ∑ v : V, f v := by
  have hC :
      (∑ p : CocliquePoint C, f p) = ∑ v ∈ C, f v := by
    rw [Finset.univ_eq_attach C, Finset.sum_attach]
  have houtside :
      (∑ B : CocliqueOutside C, f B) = ∑ v ∈ Cᶜ, f v := by
    rw [Finset.univ_eq_attach Cᶜ, Finset.sum_attach]
  rw [hC, houtside]
  exact Finset.sum_add_sum_compl C f

/-- The adjacency matrix induced on the vertices outside the coclique. -/
def cocliqueOutsideAdjacencyMatrix (C : Finset V) :
    Matrix (CocliqueOutside C) (CocliqueOutside C) ℤ :=
  fun B D => if G.Adj (B : V) (D : V) then 1 else 0

/-- Every outside vertex has 33 neighbors outside a size-56 coclique. -/
theorem cocliqueOutsideAdjacencyMatrix_row_sum
    (hG : IsHypothetical G)
    {C : Finset V}
    (hCcard : C.card = 56)
    (hC : G.IsIndepSet (C : Set V))
    (B : CocliqueOutside C) :
    ∑ D, cocliqueOutsideAdjacencyMatrix G C B D = 33 := by
  have htotal :
      (∑ p : CocliquePoint C,
          cocliqueIncidenceMatrix G C p B) +
        (∑ D : CocliqueOutside C,
          cocliqueOutsideAdjacencyMatrix G C B D) = 45 := by
    calc
      (∑ p : CocliquePoint C,
          cocliqueIncidenceMatrix G C p B) +
          (∑ D : CocliqueOutside C,
            cocliqueOutsideAdjacencyMatrix G C B D) =
          ∑ v : V, if G.Adj (B : V) v then (1 : ℤ) else 0 := by
        simpa [cocliqueIncidenceMatrix,
          cocliqueOutsideAdjacencyMatrix, G.adj_comm] using
            (sum_cocliquePoint_add_sum_cocliqueOutside
              C (fun v => if G.Adj (B : V) v then (1 : ℤ) else 0))
      _ = 45 := by
        calc
          (∑ v : V, if G.Adj (B : V) v then (1 : ℤ) else 0) =
              (G.degree (B : V) : ℤ) := by
            exact (G.degree_eq_sum_if_adj (R := ℤ) (B : V)).symm
          _ = 45 := by rw [hG.regular]; norm_num
  have hcolumn :=
    cocliqueIncidenceMatrix_column_sum G hG hCcard hC B
  change
    (∑ p : CocliquePoint C, cocliqueIncidenceMatrix G C p B) = 12
      at hcolumn
  omega

/-- Common neighbors of a coclique point and an arbitrary vertex, restricted
to the outside vertices. -/
def cocliquePointVertexCommonOutside
    (C : Finset V) (p : CocliquePoint C) (v : V) :
    Finset (CocliqueOutside C) :=
  Finset.univ.filter fun B =>
    G.Adj (p : V) (B : V) ∧ G.Adj v (B : V)

def commonNeighborsEquivCocliquePointVertexCommonOutside
    {C : Finset V}
    (hC : G.IsIndepSet (C : Set V))
    (p : CocliquePoint C) (v : V) :
    G.commonNeighbors (p : V) v ≃
      ↥(cocliquePointVertexCommonOutside G C p v) where
  toFun z := by
    have hznot : (z : V) ∉ C := by
      intro hz
      exact
        (not_adj_of_mem_indepSet G hC p.property hz) z.property.1
    let B : CocliqueOutside C := ⟨z, by simpa using hznot⟩
    refine ⟨B, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact z.property
  invFun B := by
    have hB := Finset.mem_filter.mp B.property
    exact ⟨B.1, hB.2⟩
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv B := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem cocliqueIncidence_mul_outsideAdjacency_apply
    (hG : IsHypothetical G)
    {C : Finset V}
    (hC : G.IsIndepSet (C : Set V))
    (p : CocliquePoint C) (B : CocliqueOutside C) :
    (cocliqueIncidenceMatrix G C *
        cocliqueOutsideAdjacencyMatrix G C) p B =
      if G.Adj (p : V) (B : V) then 0 else 9 := by
  rw [Matrix.mul_apply]
  have hcount :
      (∑ D,
          cocliqueIncidenceMatrix G C p D *
            cocliqueOutsideAdjacencyMatrix G C D B) =
        (Fintype.card (G.commonNeighbors (p : V) (B : V)) : ℤ) := by
    calc
      (∑ D,
          cocliqueIncidenceMatrix G C p D *
            cocliqueOutsideAdjacencyMatrix G C D B) =
          ((cocliquePointVertexCommonOutside G C p B).card : ℤ) := by
        simp only [cocliqueIncidenceMatrix,
          cocliqueOutsideAdjacencyMatrix, ite_zero_mul_ite_zero, one_mul,
          Finset.sum_boole]
        apply congrArg
        apply congrArg Finset.card
        ext D
        simp [cocliquePointVertexCommonOutside, G.adj_comm]
      _ = (Fintype.card
          (G.commonNeighbors (p : V) (B : V)) : ℤ) := by
        norm_cast
        rw [← Fintype.card_coe]
        exact
          (Fintype.card_congr
            (commonNeighborsEquivCocliquePointVertexCommonOutside
              G hC p B)).symm
  rw [hcount]
  have hpB : (p : V) ≠ (B : V) := by
    intro hpB
    have hBout : (B : V) ∉ C := Finset.mem_compl.mp B.property
    exact hBout (hpB ▸ p.property)
  by_cases hadj : G.Adj (p : V) (B : V)
  · rw [if_pos hadj]
    exact_mod_cast hG.of_adj p B hadj
  · rw [if_neg hadj]
    exact_mod_cast hG.of_not_adj hpB hadj

/-- The block-intersection matrix of the coclique incidence structure. -/
def cocliqueBlockIntersectionMatrix (C : Finset V) :
    Matrix (CocliqueOutside C) (CocliqueOutside C) ℤ :=
  (cocliqueIncidenceMatrix G C).transpose *
    cocliqueIncidenceMatrix G C

theorem cocliquePointGram
    (hG : IsHypothetical G)
    {C : Finset V}
    (hC : G.IsIndepSet (C : Set V)) :
    cocliqueIncidenceMatrix G C *
        (cocliqueIncidenceMatrix G C).transpose =
      (36 : ℤ) • (1 : Matrix (CocliquePoint C) (CocliquePoint C) ℤ) +
        (9 : ℤ) • allOnesMatrix := by
  ext p q
  rw [cocliqueIncidence_mul_transpose_apply G hG hC p q]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    allOnesMatrix_apply]
  by_cases hpq : p = q
  · subst q
    simp
  · simp [hpq]

theorem cocliqueIncidence_mul_outsideAdjacency
    (hG : IsHypothetical G)
    {C : Finset V}
    (hC : G.IsIndepSet (C : Set V)) :
    cocliqueIncidenceMatrix G C *
        cocliqueOutsideAdjacencyMatrix G C =
      (9 : ℤ) • allOnesMatrix -
        (9 : ℤ) • cocliqueIncidenceMatrix G C := by
  ext p B
  rw [cocliqueIncidence_mul_outsideAdjacency_apply G hG hC p B]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    allOnesMatrix_apply]
  by_cases hadj : G.Adj (p : V) (B : V)
  · simp [cocliqueIncidenceMatrix, hadj]
  · simp [cocliqueIncidenceMatrix, hadj]

theorem cocliqueOutsideAdjacency_isSymm
    (C : Finset V) :
    (cocliqueOutsideAdjacencyMatrix G C).IsSymm := by
  apply Matrix.IsSymm.ext
  intro B D
  simp [cocliqueOutsideAdjacencyMatrix, G.adj_comm]

theorem cocliqueBlockIntersection_isSymm
    (C : Finset V) :
    (cocliqueBlockIntersectionMatrix G C).IsSymm := by
  apply Matrix.IsSymm.ext
  intro B D
  simp [cocliqueBlockIntersectionMatrix, Matrix.mul_apply, mul_comm]

theorem cocliqueBlockIntersection_diagonal
    (hG : IsHypothetical G)
    {C : Finset V}
    (hCcard : C.card = 56)
    (hC : G.IsIndepSet (C : Set V))
    (B : CocliqueOutside C) :
    cocliqueBlockIntersectionMatrix G C B B = 12 := by
  change ∑ p,
    cocliqueIncidenceMatrix G C p B *
      cocliqueIncidenceMatrix G C p B = 12
  calc
    (∑ p,
        cocliqueIncidenceMatrix G C p B *
          cocliqueIncidenceMatrix G C p B) =
        ∑ p, cocliqueIncidenceMatrix G C p B := by
      apply Finset.sum_congr rfl
      intro p _
      exact cocliqueIncidenceMatrix_binary G C p B
    _ = 12 :=
      cocliqueIncidenceMatrix_column_sum G hG hCcard hC B

theorem cocliqueBlockIntersection_row_sum
    (hG : IsHypothetical G)
    {C : Finset V}
    (hCcard : C.card = 56)
    (hC : G.IsIndepSet (C : Set V))
    (B : CocliqueOutside C) :
    ∑ D, cocliqueBlockIntersectionMatrix G C B D = 540 := by
  let M := cocliqueIncidenceMatrix G C
  have hrow : ∀ p : CocliquePoint C, ∑ D, M p D = 45 := by
    intro p
    exact incidence_row_sum_eq_forty_five M
      (cocliqueIncidenceMatrix_binary G C)
      (cocliqueIncidence_mul_transpose_apply G hG hC) p
  have hcolumn : ∑ p, M p B = 12 :=
    cocliqueIncidenceMatrix_column_sum G hG hCcard hC B
  change ∑ D, ∑ p, M p B * M p D = 540
  calc
    (∑ D, ∑ p, M p B * M p D) =
        ∑ p, M p B * ∑ D, M p D := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
    _ = ∑ p, M p B * 45 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [hrow p]
    _ = (∑ p, M p B) * 45 := by
      exact
        (Finset.sum_mul (Finset.univ : Finset (CocliquePoint C))
          (fun p => M p B) (45 : ℤ)).symm
    _ = 540 := by rw [hcolumn]; norm_num

theorem cocliqueBlockIntersection_mul_outsideAdjacency
    (hG : IsHypothetical G)
    {C : Finset V}
    (hCcard : C.card = 56)
    (hC : G.IsIndepSet (C : Set V)) :
    cocliqueBlockIntersectionMatrix G C *
        cocliqueOutsideAdjacencyMatrix G C =
      (108 : ℤ) • allOnesMatrix -
        (9 : ℤ) • cocliqueBlockIntersectionMatrix G C := by
  let M := cocliqueIncidenceMatrix G C
  let H := cocliqueOutsideAdjacencyMatrix G C
  let S := cocliqueBlockIntersectionMatrix G C
  have hMH :
      M * H = (9 : ℤ) • allOnesMatrix - (9 : ℤ) • M := by
    simpa [M, H] using
      cocliqueIncidence_mul_outsideAdjacency G hG hC
  have hcolumn : ∀ B : CocliqueOutside C, ∑ p, M p B = 12 := by
    intro B
    exact cocliqueIncidenceMatrix_column_sum G hG hCcard hC B
  change
    (M.transpose * M) * H =
      (108 : ℤ) • allOnesMatrix -
        (9 : ℤ) • (M.transpose * M)
  rw [Matrix.mul_assoc]
  ext B D
  rw [Matrix.mul_apply]
  rw [hMH]
  simp only [Matrix.transpose_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, allOnesMatrix_apply, Matrix.mul_apply]
  change
    (∑ p, M p B * (9 - 9 * M p D)) =
      108 - 9 * (∑ p, M p B * M p D)
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hfirst : (∑ p, M p B * 9) = 108 := by
    calc
      (∑ p, M p B * 9) = (∑ p, M p B) * 9 := by
        exact
          (Finset.sum_mul (Finset.univ : Finset (CocliquePoint C))
            (fun p => M p B) (9 : ℤ)).symm
      _ = 108 := by rw [hcolumn B]; norm_num
  rw [hfirst]
  congr 1
  calc
    (∑ p, M p B * (9 * M p D)) =
        ∑ p, 9 * (M p B * M p D) := by
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = 9 * ∑ p, M p B * M p D := by
      exact
        (Finset.mul_sum (Finset.univ : Finset (CocliquePoint C))
          (fun p => M p B * M p D) (9 : ℤ)).symm

/-- Common neighbors of two outside vertices split into coclique points and
outside vertices. -/
theorem cocliqueBlockIntersection_add_outsideAdjacency_sq_apply_card
    {C : Finset V}
    (B D : CocliqueOutside C) :
    cocliqueBlockIntersectionMatrix G C B D +
        (cocliqueOutsideAdjacencyMatrix G C *
          cocliqueOutsideAdjacencyMatrix G C) B D =
      (Fintype.card (G.commonNeighbors (B : V) (D : V)) : ℤ) := by
  rw [cocliqueBlockIntersectionMatrix, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  calc
    (∑ p,
          cocliqueIncidenceMatrix G C p B *
            cocliqueIncidenceMatrix G C p D) +
        (∑ E,
          cocliqueOutsideAdjacencyMatrix G C B E *
            cocliqueOutsideAdjacencyMatrix G C E D) =
        ∑ v : V,
          if G.Adj (B : V) v ∧ G.Adj (D : V) v then (1 : ℤ) else 0 := by
      simpa only [cocliqueIncidenceMatrix,
        cocliqueOutsideAdjacencyMatrix, G.adj_comm,
        ite_zero_mul_ite_zero, one_mul] using
          (sum_cocliquePoint_add_sum_cocliqueOutside C
            (fun v =>
              if G.Adj (B : V) v ∧ G.Adj (D : V) v then
                (1 : ℤ) else 0))
    _ = (Fintype.card
        (G.commonNeighbors (B : V) (D : V)) : ℤ) := by
      simp only [Finset.sum_boole]
      norm_cast
      rw [← Set.toFinset_card]
      apply congrArg Finset.card
      ext v
      simp [SimpleGraph.mem_commonNeighbors, G.adj_comm]

theorem cocliqueBlockIntersection_add_outsideAdjacency_sq_apply
    (hG : IsHypothetical G)
    {C : Finset V}
    (B D : CocliqueOutside C) :
    cocliqueBlockIntersectionMatrix G C B D +
        (cocliqueOutsideAdjacencyMatrix G C *
          cocliqueOutsideAdjacencyMatrix G C) B D =
      if B = D then 45
      else if G.Adj (B : V) (D : V) then 0 else 9 := by
  rw [cocliqueBlockIntersection_add_outsideAdjacency_sq_apply_card G B D]
  by_cases hBD : B = D
  · subst D
    rw [if_pos rfl]
    have hdiag :
        Fintype.card (G.commonNeighbors (B : V) (B : V)) = 45 := by
      have hn :
          Fintype.card (G.neighborSet (B : V)) = 45 := by
        rw [G.card_neighborSet_eq_degree, hG.regular]
      simpa only [G.commonNeighbors_eq, Set.inter_self] using hn
    exact_mod_cast hdiag
  · rw [if_neg hBD]
    have hBDv : (B : V) ≠ (D : V) := by
      intro h
      exact hBD (Subtype.ext h)
    by_cases hadj : G.Adj (B : V) (D : V)
    · rw [if_pos hadj]
      exact_mod_cast hG.of_adj B D hadj
    · rw [if_neg hadj]
      exact_mod_cast hG.of_not_adj hBDv hadj

theorem cocliqueBlockIntersection_add_outsideAdjacency_sq
    (hG : IsHypothetical G)
    {C : Finset V} :
    cocliqueBlockIntersectionMatrix G C +
        cocliqueOutsideAdjacencyMatrix G C *
          cocliqueOutsideAdjacencyMatrix G C =
      (36 : ℤ) •
          (1 : Matrix (CocliqueOutside C) (CocliqueOutside C) ℤ) -
        (9 : ℤ) • cocliqueOutsideAdjacencyMatrix G C +
          (9 : ℤ) • allOnesMatrix := by
  ext B D
  rw [Matrix.add_apply,
    cocliqueBlockIntersection_add_outsideAdjacency_sq_apply G hG B D]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, allOnesMatrix_apply]
  by_cases hBD : B = D
  · subst D
    simp [cocliqueOutsideAdjacencyMatrix]
  · by_cases hadj : G.Adj (B : V) (D : V)
    · simp [cocliqueOutsideAdjacencyMatrix, hBD, hadj]
    · simp [cocliqueOutsideAdjacencyMatrix, hBD, hadj]

theorem cocliqueIncidence_transpose_mul_ones_mul_incidence
    (hG : IsHypothetical G)
    {C : Finset V}
    (hCcard : C.card = 56)
    (hC : G.IsIndepSet (C : Set V)) :
    (cocliqueIncidenceMatrix G C).transpose *
        (allOnesMatrix :
          Matrix (CocliquePoint C) (CocliquePoint C) ℤ) *
          cocliqueIncidenceMatrix G C =
      (144 : ℤ) •
        (allOnesMatrix :
          Matrix (CocliqueOutside C) (CocliqueOutside C) ℤ) := by
  let M := cocliqueIncidenceMatrix G C
  have hcolumn : ∀ B : CocliqueOutside C, ∑ p, M p B = 12 := by
    intro B
    exact cocliqueIncidenceMatrix_column_sum G hG hCcard hC B
  change M.transpose * allOnesMatrix * M = (144 : ℤ) • allOnesMatrix
  ext B D
  simp only [Matrix.mul_apply, Matrix.transpose_apply, allOnesMatrix_apply,
    mul_one, Matrix.smul_apply, smul_eq_mul]
  change (∑ p, (∑ q, M q B) * M p D) = 144
  simp_rw [hcolumn]
  calc
    (∑ p, 12 * M p D) = 12 * ∑ p, M p D := by
      exact
        (Finset.mul_sum (Finset.univ : Finset (CocliquePoint C))
          (fun p => M p D) (12 : ℤ)).symm
    _ = 144 := by rw [hcolumn D]; norm_num

theorem cocliqueBlockIntersection_sq
    (hG : IsHypothetical G)
    {C : Finset V}
    (hCcard : C.card = 56)
    (hC : G.IsIndepSet (C : Set V)) :
    cocliqueBlockIntersectionMatrix G C *
        cocliqueBlockIntersectionMatrix G C =
      (36 : ℤ) • cocliqueBlockIntersectionMatrix G C +
        (1296 : ℤ) •
          (allOnesMatrix :
            Matrix (CocliqueOutside C) (CocliqueOutside C) ℤ) := by
  let M := cocliqueIncidenceMatrix G C
  let Jp : Matrix (CocliquePoint C) (CocliquePoint C) ℤ :=
    allOnesMatrix
  let Jb : Matrix (CocliqueOutside C) (CocliqueOutside C) ℤ :=
    allOnesMatrix
  have hpoint :
      M * M.transpose =
        (36 : ℤ) •
            (1 : Matrix (CocliquePoint C) (CocliquePoint C) ℤ) +
          (9 : ℤ) • Jp := by
    simpa [M, Jp] using cocliquePointGram G hG hC
  have houter :
      M.transpose * Jp * M = (144 : ℤ) • Jb := by
    simpa [M, Jp, Jb] using
      cocliqueIncidence_transpose_mul_ones_mul_incidence
        G hG hCcard hC
  change
    (M.transpose * M) * (M.transpose * M) =
      (36 : ℤ) • (M.transpose * M) + (1296 : ℤ) • Jb
  calc
    (M.transpose * M) * (M.transpose * M) =
        M.transpose * (M * M.transpose) * M := by
      simp [Matrix.mul_assoc]
    _ = M.transpose *
          ((36 : ℤ) •
              (1 : Matrix (CocliquePoint C) (CocliquePoint C) ℤ) +
            (9 : ℤ) • Jp) * M := by rw [hpoint]
    _ = (36 : ℤ) • (M.transpose * M) +
        (9 : ℤ) • (M.transpose * Jp * M) := by
      rw [Matrix.mul_add, Matrix.add_mul]
      rw [Matrix.mul_smul]
      rw [Matrix.smul_mul]
      rw [Matrix.mul_smul]
      simp [Matrix.mul_assoc]
    _ = (36 : ℤ) • (M.transpose * M) +
        (1296 : ℤ) • Jb := by rw [houter]; module

theorem cocliqueOutsideOnes_sq
    (hG : IsHypothetical G)
    {C : Finset V}
    (hCcard : C.card = 56) :
    (allOnesMatrix :
        Matrix (CocliqueOutside C) (CocliqueOutside C) ℤ) *
        allOnesMatrix =
      (210 : ℤ) • allOnesMatrix := by
  ext B D
  simp only [Matrix.mul_apply, allOnesMatrix_apply, one_mul,
    Matrix.smul_apply, smul_eq_mul]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact_mod_cast cocliqueOutside_card G hG C hCcard

theorem cocliqueOutsideAdjacency_mul_ones
    (hG : IsHypothetical G)
    {C : Finset V}
    (hCcard : C.card = 56)
    (hC : G.IsIndepSet (C : Set V)) :
    cocliqueOutsideAdjacencyMatrix G C *
        (allOnesMatrix :
          Matrix (CocliqueOutside C) (CocliqueOutside C) ℤ) =
      (33 : ℤ) • allOnesMatrix := by
  ext B D
  simp only [Matrix.mul_apply, allOnesMatrix_apply, mul_one,
    Matrix.smul_apply, smul_eq_mul]
  exact cocliqueOutsideAdjacencyMatrix_row_sum G hG hCcard hC B

theorem cocliqueOnes_mul_outsideAdjacency
    (hG : IsHypothetical G)
    {C : Finset V}
    (hCcard : C.card = 56)
    (hC : G.IsIndepSet (C : Set V)) :
    (allOnesMatrix :
        Matrix (CocliqueOutside C) (CocliqueOutside C) ℤ) *
        cocliqueOutsideAdjacencyMatrix G C =
      (33 : ℤ) • allOnesMatrix := by
  ext B D
  simp only [Matrix.mul_apply, allOnesMatrix_apply, one_mul,
    Matrix.smul_apply, smul_eq_mul]
  calc
    (∑ E, cocliqueOutsideAdjacencyMatrix G C E D) =
        ∑ E, cocliqueOutsideAdjacencyMatrix G C D E := by
      apply Finset.sum_congr rfl
      intro E _
      exact (cocliqueOutsideAdjacency_isSymm G C).apply D E
    _ = 33 :=
      cocliqueOutsideAdjacencyMatrix_row_sum G hG hCcard hC D

theorem cocliqueBlockIntersection_mul_ones
    (hG : IsHypothetical G)
    {C : Finset V}
    (hCcard : C.card = 56)
    (hC : G.IsIndepSet (C : Set V)) :
    cocliqueBlockIntersectionMatrix G C *
        (allOnesMatrix :
          Matrix (CocliqueOutside C) (CocliqueOutside C) ℤ) =
      (540 : ℤ) • allOnesMatrix := by
  ext B D
  simp only [Matrix.mul_apply, allOnesMatrix_apply, mul_one,
    Matrix.smul_apply, smul_eq_mul]
  exact cocliqueBlockIntersection_row_sum G hG hCcard hC B

theorem cocliqueOnes_mul_blockIntersection
    (hG : IsHypothetical G)
    {C : Finset V}
    (hCcard : C.card = 56)
    (hC : G.IsIndepSet (C : Set V)) :
    (allOnesMatrix :
        Matrix (CocliqueOutside C) (CocliqueOutside C) ℤ) *
        cocliqueBlockIntersectionMatrix G C =
      (540 : ℤ) • allOnesMatrix := by
  ext B D
  simp only [Matrix.mul_apply, allOnesMatrix_apply, one_mul,
    Matrix.smul_apply, smul_eq_mul]
  calc
    (∑ E, cocliqueBlockIntersectionMatrix G C E D) =
        ∑ E, cocliqueBlockIntersectionMatrix G C D E := by
      apply Finset.sum_congr rfl
      intro E _
      exact (cocliqueBlockIntersection_isSymm G C).apply D E
    _ = 540 := cocliqueBlockIntersection_row_sum G hG hCcard hC D

theorem cocliqueOutsideAdjacency_mul_blockIntersection
    (hG : IsHypothetical G)
    {C : Finset V}
    (hCcard : C.card = 56)
    (hC : G.IsIndepSet (C : Set V)) :
    cocliqueOutsideAdjacencyMatrix G C *
        cocliqueBlockIntersectionMatrix G C =
      (108 : ℤ) • allOnesMatrix -
        (9 : ℤ) • cocliqueBlockIntersectionMatrix G C := by
  let S := cocliqueBlockIntersectionMatrix G C
  let H := cocliqueOutsideAdjacencyMatrix G C
  let J : Matrix (CocliqueOutside C) (CocliqueOutside C) ℤ :=
    allOnesMatrix
  have hSH : S * H = (108 : ℤ) • J - (9 : ℤ) • S := by
    simpa [S, H, J] using
      cocliqueBlockIntersection_mul_outsideAdjacency G hG hCcard hC
  change H * S = (108 : ℤ) • J - (9 : ℤ) • S
  ext B D
  calc
    (H * S) B D = (S * H) D B := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro E _
      have hHEB :=
        (cocliqueOutsideAdjacency_isSymm G C).apply E B
      have hSDE :=
        (cocliqueBlockIntersection_isSymm G C).apply D E
      change H B E = H E B at hHEB
      change S E D = S D E at hSDE
      rw [hHEB, hSDE]
      ring
    _ = ((108 : ℤ) • J - (9 : ℤ) • S) D B := by
      rw [hSH]
    _ = ((108 : ℤ) • J - (9 : ℤ) • S) B D := by
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        J, allOnesMatrix_apply, S]
      rw [(cocliqueBlockIntersection_isSymm G C).apply B D]

/-- The matrix predicted by the quasi-symmetric block intersections. -/
def cocliqueTargetIntersectionMatrix (C : Finset V) :
    Matrix (CocliqueOutside C) (CocliqueOutside C) ℤ :=
  (9 : ℤ) •
      (1 : Matrix (CocliqueOutside C) (CocliqueOutside C) ℤ) +
    (3 : ℤ) • allOnesMatrix -
      (3 : ℤ) • cocliqueOutsideAdjacencyMatrix G C

/-- Difference between the actual and predicted block-intersection
matrices. -/
def cocliqueIntersectionDefect (C : Finset V) :
    Matrix (CocliqueOutside C) (CocliqueOutside C) ℤ :=
  cocliqueBlockIntersectionMatrix G C -
    cocliqueTargetIntersectionMatrix G C

theorem cocliqueIntersectionDefect_sq
    (hG : IsHypothetical G)
    {C : Finset V}
    (hCcard : C.card = 56)
    (hC : G.IsIndepSet (C : Set V)) :
    cocliqueIntersectionDefect G C *
        cocliqueIntersectionDefect G C =
      (-45 : ℤ) • cocliqueIntersectionDefect G C := by
  let S := cocliqueBlockIntersectionMatrix G C
  let H := cocliqueOutsideAdjacencyMatrix G C
  let J : Matrix (CocliqueOutside C) (CocliqueOutside C) ℤ :=
    allOnesMatrix
  have hSS : S * S = (36 : ℤ) • S + (1296 : ℤ) • J := by
    simpa [S, J] using cocliqueBlockIntersection_sq G hG hCcard hC
  have hSH : S * H = (108 : ℤ) • J - (9 : ℤ) • S := by
    simpa [S, H, J] using
      cocliqueBlockIntersection_mul_outsideAdjacency G hG hCcard hC
  have hHS : H * S = (108 : ℤ) • J - (9 : ℤ) • S := by
    simpa [S, H, J] using
      cocliqueOutsideAdjacency_mul_blockIntersection G hG hCcard hC
  have hH2 :
      S + H * H =
        (36 : ℤ) •
            (1 : Matrix (CocliqueOutside C) (CocliqueOutside C) ℤ) -
          (9 : ℤ) • H + (9 : ℤ) • J := by
    simpa [S, H, J] using
      cocliqueBlockIntersection_add_outsideAdjacency_sq G hG
  have hHH :
      H * H =
        -(S) + (36 : ℤ) •
            (1 : Matrix (CocliqueOutside C) (CocliqueOutside C) ℤ) -
          (9 : ℤ) • H + (9 : ℤ) • J := by
    calc
      H * H = (S + H * H) - S := by abel
      _ = ((36 : ℤ) •
            (1 : Matrix (CocliqueOutside C) (CocliqueOutside C) ℤ) -
          (9 : ℤ) • H + (9 : ℤ) • J) - S := by rw [hH2]
      _ = -(S) + (36 : ℤ) •
            (1 : Matrix (CocliqueOutside C) (CocliqueOutside C) ℤ) -
          (9 : ℤ) • H + (9 : ℤ) • J := by abel
  have hSJ : S * J = (540 : ℤ) • J := by
    simpa [S, J] using
      cocliqueBlockIntersection_mul_ones G hG hCcard hC
  have hJS : J * S = (540 : ℤ) • J := by
    simpa [S, J] using
      cocliqueOnes_mul_blockIntersection G hG hCcard hC
  have hHJ : H * J = (33 : ℤ) • J := by
    simpa [H, J] using
      cocliqueOutsideAdjacency_mul_ones G hG hCcard hC
  have hJH : J * H = (33 : ℤ) • J := by
    simpa [H, J] using
      cocliqueOnes_mul_outsideAdjacency G hG hCcard hC
  have hJJ : J * J = (210 : ℤ) • J := by
    simpa [J] using cocliqueOutsideOnes_sq G hG hCcard
  change
    (S - ((9 : ℤ) • 1 + (3 : ℤ) • J - (3 : ℤ) • H)) *
        (S - ((9 : ℤ) • 1 + (3 : ℤ) • J - (3 : ℤ) • H)) =
      (-45 : ℤ) •
        (S - ((9 : ℤ) • 1 + (3 : ℤ) • J - (3 : ℤ) • H))
  noncomm_ring [hSS, hSH, hHS, hHH, hSJ, hJS, hHJ, hJH, hJJ]

theorem cocliqueIntersectionDefect_isSymm
    (C : Finset V) :
    (cocliqueIntersectionDefect G C).IsSymm := by
  apply Matrix.IsSymm.ext
  intro B D
  simp only [cocliqueIntersectionDefect,
    cocliqueTargetIntersectionMatrix, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, allOnesMatrix_apply]
  rw [(cocliqueBlockIntersection_isSymm G C).apply B D,
    (cocliqueOutsideAdjacency_isSymm G C).apply B D]
  by_cases hBD : B = D
  · subst D
    simp
  · have hDB : D ≠ B := Ne.symm hBD
    simp [hBD, hDB]

theorem cocliqueIntersectionDefect_diagonal
    (hG : IsHypothetical G)
    {C : Finset V}
    (hCcard : C.card = 56)
    (hC : G.IsIndepSet (C : Set V))
    (B : CocliqueOutside C) :
    cocliqueIntersectionDefect G C B B = 0 := by
  rw [cocliqueIntersectionDefect, Matrix.sub_apply,
    cocliqueBlockIntersection_diagonal G hG hCcard hC B]
  rw [cocliqueTargetIntersectionMatrix]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, allOnesMatrix_apply]
  simp [cocliqueOutsideAdjacencyMatrix]

/-- The defect has zero diagonal and satisfies `K² = -45K`; symmetry turns
each diagonal equation into a sum of integer squares, hence the defect
vanishes. -/
theorem cocliqueIntersectionDefect_eq_zero
    (hG : IsHypothetical G)
    {C : Finset V}
    (hCcard : C.card = 56)
    (hC : G.IsIndepSet (C : Set V)) :
    cocliqueIntersectionDefect G C = 0 := by
  let K := cocliqueIntersectionDefect G C
  have hKsq : K * K = (-45 : ℤ) • K := by
    simpa [K] using cocliqueIntersectionDefect_sq G hG hCcard hC
  have hKsymm : K.IsSymm := by
    simpa [K] using cocliqueIntersectionDefect_isSymm G C
  have hKdiag : ∀ B : CocliqueOutside C, K B B = 0 := by
    intro B
    exact cocliqueIntersectionDefect_diagonal G hG hCcard hC B
  ext B D
  have hsquares : ∑ E, K B E * K B E = 0 := by
    calc
      (∑ E, K B E * K B E) = (K * K) B B := by
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro E _
        rw [hKsymm.apply B E]
      _ = ((-45 : ℤ) • K) B B := by rw [hKsq]
      _ = 0 := by
        simp only [Matrix.smul_apply, smul_eq_mul, hKdiag, mul_zero]
  have hterm : K B D * K B D = 0 := by
    exact
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun E _ => mul_self_nonneg (K B E))).mp
          hsquares D (Finset.mem_univ D)
  have : K B D = 0 := by nlinarith
  simpa [Matrix.zero_apply] using this

theorem cocliqueBlockIntersection_eq_target
    (hG : IsHypothetical G)
    {C : Finset V}
    (hCcard : C.card = 56)
    (hC : G.IsIndepSet (C : Set V)) :
    cocliqueBlockIntersectionMatrix G C =
      cocliqueTargetIntersectionMatrix G C := by
  have hzero :=
    cocliqueIntersectionDefect_eq_zero G hG hCcard hC
  rw [cocliqueIntersectionDefect, sub_eq_zero] at hzero
  exact hzero

theorem cocliqueBlockIntersection_offDiagonal
    (hG : IsHypothetical G)
    {C : Finset V}
    (hCcard : C.card = 56)
    (hC : G.IsIndepSet (C : Set V))
    {B D : CocliqueOutside C}
    (hBD : B ≠ D) :
    cocliqueBlockIntersectionMatrix G C B D = 0 ∨
      cocliqueBlockIntersectionMatrix G C B D = 3 := by
  have htarget :=
    congrFun
      (congrFun
        (cocliqueBlockIntersection_eq_target G hG hCcard hC) B) D
  rw [cocliqueTargetIntersectionMatrix] at htarget
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, allOnesMatrix_apply] at htarget
  simp only [Matrix.one_apply, hBD, if_false, mul_zero, zero_add] at htarget
  by_cases hadj : G.Adj (B : V) (D : V)
  · left
    rw [htarget]
    simp [cocliqueOutsideAdjacencyMatrix, hadj]
  · right
    rw [htarget]
    simp [cocliqueOutsideAdjacencyMatrix, hadj]

end CocliqueIncidence

universe u

/-- A compact incidence-matrix interface for the forbidden
quasi-symmetric `2-(56,12,9)` design.  Blocks are occurrences, so repeated
blocks are represented by distinct elements of `Block`. -/
structure QuasiSymmetricDesign56 where
  Point : Type u
  Block : Type u
  [pointFintype : Fintype Point]
  [blockFintype : Fintype Block]
  [pointDecidableEq : DecidableEq Point]
  [blockDecidableEq : DecidableEq Block]
  incidence : Matrix Point Block ℤ
  point_card : Fintype.card Point = 56
  block_card : Fintype.card Block = 210
  binary : ∀ p B, incidence p B * incidence p B = incidence p B
  point_gram : ∀ p q, (incidence * incidence.transpose) p q =
    if p = q then 45 else 9
  block_size : ∀ B, incidenceColumnSum incidence B = 12
  block_intersections :
    ∀ {B D}, B ≠ D →
      (incidence.transpose * incidence) B D = 0 ∨
        (incidence.transpose * incidence) B D = 3

namespace QuasiSymmetricDesign56

variable (design : QuasiSymmetricDesign56.{u})

local instance : Fintype design.Point := design.pointFintype
local instance : Fintype design.Block := design.blockFintype
local instance : DecidableEq design.Point := design.pointDecidableEq
local instance : DecidableEq design.Block := design.blockDecidableEq

/-- The total intersection of a fixed block with all other block occurrences
is `12 * (45 - 1) = 528`. -/
theorem offDiagonalIntersectionSum (B : design.Block) :
    ∑ D ∈ Finset.univ.erase B,
        (design.incidence.transpose * design.incidence) B D = 528 := by
  let gram := design.incidence.transpose * design.incidence
  have hrow : ∀ p : design.Point, ∑ D, design.incidence p D = 45 :=
    fun p =>
      incidence_row_sum_eq_forty_five
        design.incidence design.binary design.point_gram p
  have hdiag : gram B B = 12 := by
    calc
      gram B B = ∑ p, design.incidence p B * design.incidence p B := by
        simp only [gram, Matrix.mul_apply, Matrix.transpose_apply]
      _ = ∑ p, design.incidence p B := by
        apply Finset.sum_congr rfl
        intro p _
        exact design.binary p B
      _ = 12 := design.block_size B
  have htotal : ∑ D, gram B D = 540 := by
    calc
      (∑ D, gram B D) =
          ∑ p, design.incidence p B * (∑ D, design.incidence p D) := by
        simp only [gram, Matrix.mul_apply, Matrix.transpose_apply]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = ∑ p, design.incidence p B * 45 := by
        apply Finset.sum_congr rfl
        intro p _
        rw [hrow p]
      _ = 45 * incidenceColumnSum design.incidence B := by
        simp only [incidenceColumnSum]
        rw [← Finset.sum_mul]
        ring
      _ = 540 := by rw [design.block_size B]; norm_num
  have herase :=
    Finset.sum_erase_add (s := Finset.univ) (f := fun D => gram B D)
      (Finset.mem_univ B)
  change
    (∑ D ∈ Finset.univ.erase B, gram B D) = 528
  change (∑ D ∈ Finset.univ.erase B, gram B D) + gram B B =
    ∑ D, gram B D at herase
  rw [hdiag, htotal] at herase
  omega

/-- Every block meets some other block in exactly three points. -/
theorem exists_intersection_three (B : design.Block) :
    ∃ D : design.Block, D ≠ B ∧
      (design.incidence.transpose * design.incidence) B D = 3 := by
  by_contra h
  push Not at h
  have hzero :
      ∀ D ∈ Finset.univ.erase B,
        (design.incidence.transpose * design.incidence) B D = 0 := by
    intro D hD
    have hDB : D ≠ B := (Finset.mem_erase.mp hD).1
    have hBD : B ≠ D := Ne.symm hDB
    rcases design.block_intersections hBD with hinter | hinter
    · exact hinter
    · exact (h D hDB hinter).elim
  have hsum :
      ∑ D ∈ Finset.univ.erase B,
          (design.incidence.transpose * design.incidence) B D = 0 := by
    apply Finset.sum_eq_zero
    intro D hD
    exact hzero D hD
  rw [design.offDiagonalIntersectionSum B] at hsum
  omega

/-- Every block is disjoint from some other block.  Thus the interface's
intersection set is genuinely the two-element set `{0, 3}`, as in the
standard definition of a quasi-symmetric design. -/
theorem exists_intersection_zero (B : design.Block) :
    ∃ D : design.Block, D ≠ B ∧
      (design.incidence.transpose * design.incidence) B D = 0 := by
  by_contra h
  push Not at h
  have hthree :
      ∀ D ∈ Finset.univ.erase B,
        (design.incidence.transpose * design.incidence) B D = 3 := by
    intro D hD
    have hDB : D ≠ B := (Finset.mem_erase.mp hD).1
    have hBD : B ≠ D := Ne.symm hDB
    rcases design.block_intersections hBD with hinter | hinter
    · exact (h D hDB hinter).elim
    · exact hinter
  have hsum :
      ∑ D ∈ Finset.univ.erase B,
          (design.incidence.transpose * design.incidence) B D = 627 := by
    calc
      _ = ∑ _D ∈ Finset.univ.erase B, (3 : ℤ) := by
        apply Finset.sum_congr rfl
        intro D hD
        exact hthree D hD
      _ = 627 := by simp [design.block_card]
  rw [design.offDiagonalIntersectionSum B] at hsum
  omega

/-- Distinct block occurrences have distinct incidence columns.  Hence the
occurrence-based interface automatically represents a simple design. -/
theorem incidenceColumn_injective :
    Function.Injective
      (fun B : design.Block => fun p => design.incidence p B) := by
  intro B D hcolumns
  by_contra hBD
  have hinter := design.block_intersections hBD
  have hvalue :
      (design.incidence.transpose * design.incidence) B D = 12 := by
    calc
      _ = ∑ p, design.incidence p B * design.incidence p D := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply]
      _ = ∑ p, design.incidence p B * design.incidence p B := by
        apply Finset.sum_congr rfl
        intro p _
        have hp := congrFun hcolumns p
        change design.incidence p B = design.incidence p D at hp
        rw [← hp]
      _ = ∑ p, design.incidence p B := by
        apply Finset.sum_congr rfl
        intro p _
        exact design.binary p B
      _ = 12 := design.block_size B
  rcases hinter with hinter | hinter <;> omega

end QuasiSymmetricDesign56

/-- Nonexistence of a quasi-symmetric `2-(56, 12, 9)` design with block
intersections `0` and `3`. -/
abbrev NoQuasiSymmetricDesign56 : Prop :=
  IsEmpty (QuasiSymmetricDesign56.{u})

section DesignConstruction

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A size-56 coclique in the hypothetical SRG produces the forbidden
quasi-symmetric design. -/
noncomputable def cocliqueQuasiSymmetricDesign
    (hG : IsHypothetical G)
    (C : Finset V)
    (hCcard : C.card = 56)
    (hC : G.IsIndepSet (C : Set V)) :
    QuasiSymmetricDesign56 where
  Point := CocliquePoint C
  Block := CocliqueOutside C
  pointFintype := inferInstance
  blockFintype := inferInstance
  pointDecidableEq := inferInstance
  blockDecidableEq := inferInstance
  incidence := cocliqueIncidenceMatrix G C
  point_card := cocliquePoint_card C hCcard
  block_card := cocliqueOutside_card G hG C hCcard
  binary := cocliqueIncidenceMatrix_binary G C
  point_gram :=
    cocliqueIncidence_mul_transpose_apply G hG hC
  block_size :=
    cocliqueIncidenceMatrix_column_sum G hG hCcard hC
  block_intersections := by
    intro B D hBD
    exact cocliqueBlockIntersection_offDiagonal G hG hCcard hC hBD

/-- Conditional on the precisely stated design nonexistence input, the local
Gram matrix is not one-integrable. -/
theorem localGram_not_oneIntegrable_of_noQuasiSymmetricDesign
    (hMT : NoQuasiSymmetricDesign56.{u})
    (hG : IsHypothetical G) (x : V) :
    ¬LocalGramIsOneIntegrable G x := by
  intro hInt
  obtain ⟨C, hCcard, hC⟩ :=
    exists_global_coclique_of_oneIntegrable G hG x hInt
  exact
    hMT.false
      (cocliqueQuasiSymmetricDesign G hG C hCcard hC)

end DesignConstruction

end SRG266
