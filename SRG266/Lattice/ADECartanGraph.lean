/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Positive simply-laced Cartan graphs

This file isolates the graph-theoretic input to the ADE classification.  A
simple graph `G` has Cartan matrix `2I - A(G)`.  Its quadratic form is
positive precisely when every nonzero integer weighting of the vertices has
positive Cartan energy.

The antitonicity lemma below is the useful elementary observation: adding
edges can only decrease the Cartan energy of a nonnegative weighting.  It lets
the ADE proof exclude a cycle, a four-star, and a double fork by displaying a
single weighting of the corresponding subgraph.
-/

namespace SRG266
namespace Lattice

open scoped Matrix

variable {V : Type*}

/-- The simply-laced Cartan matrix `2I - A(G)` of a simple graph. -/
noncomputable def graphCartanMatrix (G : SimpleGraph V) : Matrix V V ℤ := by
  classical
  exact fun i j => if i = j then 2 else if G.Adj i j then -1 else 0

theorem graphCartanMatrix_apply_same (G : SimpleGraph V) (i : V) :
    graphCartanMatrix G i i = 2 := by
  classical
  simp [graphCartanMatrix]

theorem graphCartanMatrix_apply_of_adj {G : SimpleGraph V} {i j : V}
    (hij : G.Adj i j) : graphCartanMatrix G i j = -1 := by
  classical
  simp [graphCartanMatrix, hij.ne, hij]

theorem graphCartanMatrix_apply_of_not_adj {G : SimpleGraph V} {i j : V}
    (hij : i ≠ j) (hadj : ¬ G.Adj i j) : graphCartanMatrix G i j = 0 := by
  classical
  simp [graphCartanMatrix, hij, hadj]

theorem graphCartanMatrix_isSymm (G : SimpleGraph V) :
    (graphCartanMatrix G).IsSymm := by
  classical
  ext i j
  change graphCartanMatrix G j i = graphCartanMatrix G i j
  by_cases hij : i = j
  · subst j
    rw [graphCartanMatrix_apply_same]
  · by_cases hadj : G.Adj i j
    · rw [graphCartanMatrix_apply_of_adj hadj.symm,
        graphCartanMatrix_apply_of_adj hadj]
    · have hadj' : ¬ G.Adj j i := fun h ↦ hadj h.symm
      rw [graphCartanMatrix_apply_of_not_adj (Ne.symm hij) hadj',
        graphCartanMatrix_apply_of_not_adj hij hadj]

/-- A graph isomorphism transports the simply-laced Cartan matrix by the
underlying vertex equivalence. -/
theorem graphCartanMatrix_apply_iso {W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (e : G ≃g H) (i j : V) :
    graphCartanMatrix H (e i) (e j) = graphCartanMatrix G i j := by
  classical
  by_cases hij : i = j
  · subst j
    rw [graphCartanMatrix_apply_same, graphCartanMatrix_apply_same]
  · have heij : e i ≠ e j := fun h ↦ hij (e.injective h)
    by_cases hadj : G.Adj i j
    · have hHadj : H.Adj (e i) (e j) := e.map_rel_iff.mpr hadj
      rw [graphCartanMatrix_apply_of_adj hHadj,
        graphCartanMatrix_apply_of_adj hadj]
    · have hHnot : ¬ H.Adj (e i) (e j) := fun h ↦ hadj (e.map_rel_iff.mp h)
      rw [graphCartanMatrix_apply_of_not_adj heij hHnot,
        graphCartanMatrix_apply_of_not_adj hij hadj]

/-- The entrywise definition agrees with the conventional matrix expression
`2I - A(G)`. -/
theorem graphCartanMatrix_eq_two_sub_adjMatrix [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    graphCartanMatrix G = Matrix.diagonal (fun _ ↦ (2 : ℤ)) - G.adjMatrix ℤ := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [graphCartanMatrix_apply_same]
  · by_cases hadj : G.Adj i j
    · simp [graphCartanMatrix_apply_of_adj hadj, hij, hadj]
    · simp [graphCartanMatrix_apply_of_not_adj hij hadj, hij, hadj]

/-- The integer Cartan energy of a vertex weighting. -/
noncomputable def graphCartanEnergy [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x : V → ℤ) : ℤ :=
  Matrix.toBilin' (graphCartanMatrix G) x x

/-- Positive definiteness in the exact function-valued form used in the ADE
argument.  This avoids introducing coordinates or a real completion. -/
def IsPositiveCartan [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∀ x : V → ℤ, x ≠ 0 → 0 < graphCartanEnergy G x

/-- Function-valued Cartan positivity is equivalent to mathlib's matrix
positive-definiteness predicate. -/
theorem isPositiveCartan_iff_posDef [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    IsPositiveCartan G ↔ (graphCartanMatrix G).PosDef := by
  constructor
  · intro h
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · simpa [Matrix.isHermitian_iff_isSymm] using graphCartanMatrix_isSymm G
    · intro x hx
      simpa [graphCartanEnergy, Matrix.toBilin'_apply'] using h x hx
  · intro h x hx
    simpa [graphCartanEnergy, Matrix.toBilin'_apply'] using h.dotProduct_mulVec_pos hx

/-- Pulling a graph back along an embedding pulls back its Cartan matrix as a
principal submatrix. -/
theorem graphCartanMatrix_comap {W : Type*} [DecidableEq W] [DecidableEq V]
    (G : SimpleGraph V) (f : W ↪ V) :
    graphCartanMatrix (G.comap f) =
      (graphCartanMatrix G).submatrix f f := by
  classical
  ext i j
  simp only [Matrix.submatrix_apply]
  by_cases hij : i = j
  · subst j
    simp [graphCartanMatrix_apply_same]
  · by_cases hadj : (G.comap f).Adj i j
    · have hGadj : G.Adj (f i) (f j) := by simpa using hadj
      rw [graphCartanMatrix_apply_of_adj hadj,
        graphCartanMatrix_apply_of_adj hGadj]
    · have hGnot : ¬ G.Adj (f i) (f j) := by simpa using hadj
      rw [graphCartanMatrix_apply_of_not_adj hij hadj,
        graphCartanMatrix_apply_of_not_adj (fun h ↦ hij (f.injective h)) hGnot]

/-- Cartan positivity is inherited by pullback along an embedding. -/
theorem IsPositiveCartan.comap {W : Type*} [Fintype W] [DecidableEq W]
    [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : IsPositiveCartan G) (f : W ↪ V) :
    IsPositiveCartan (G.comap f) := by
  rw [isPositiveCartan_iff_posDef, graphCartanMatrix_comap]
  exact (isPositiveCartan_iff_posDef G).mp hG |>.submatrix f.injective

/-- Adding edges decreases Cartan energy on nonnegative weightings. -/
theorem graphCartanEnergy_antitone [Fintype V] [DecidableEq V]
    {H G : SimpleGraph V} (hHG : H ≤ G) {x : V → ℤ}
    (hx : ∀ i, 0 ≤ x i) :
    graphCartanEnergy G x ≤ graphCartanEnergy H x := by
  classical
  simp only [graphCartanEnergy, Matrix.toBilin'_apply]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i = j
  · simp [graphCartanMatrix, hij]
  · by_cases hHij : H.Adj i j
    · have hGij : G.Adj i j := hHG hHij
      simp [graphCartanMatrix, hij, hHij, hGij]
    · by_cases hGij : G.Adj i j
      · simp only [graphCartanMatrix, if_neg hij, if_pos hGij, if_neg hHij]
        nlinarith [hx i, hx j]
      · simp [graphCartanMatrix, hij, hHij, hGij]

/-- A nonzero nonnegative weighting of a subgraph with nonpositive energy
contradicts positive definiteness of the ambient Cartan graph. -/
theorem not_isPositiveCartan_of_nonpositive_subgraph [Fintype V] [DecidableEq V]
    {H G : SimpleGraph V} (hHG : H ≤ G) {x : V → ℤ}
    (hx0 : x ≠ 0) (hx : ∀ i, 0 ≤ x i)
    (henergy : graphCartanEnergy H x ≤ 0) :
    ¬ IsPositiveCartan G := by
  intro hpos
  have hGpos : 0 < graphCartanEnergy G x := hpos x hx0
  have hmono := graphCartanEnergy_antitone hHG hx
  omega

/-- The all-one weighting has energy `2|V| - 2|E|`. -/
theorem graphCartanEnergy_one [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    graphCartanEnergy G (fun _ ↦ 1) =
      2 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) := by
  rw [graphCartanEnergy, graphCartanMatrix_eq_two_sub_adjMatrix,
    Matrix.toBilin'_apply']
  simp only [Matrix.sub_mulVec, Matrix.mulVec_diagonal, Pi.sub_apply,
    dotProduct, one_mul]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hrow (i : V) :
      (G.adjMatrix ℤ *ᵥ (fun _ ↦ (1 : ℤ))) i = (G.degree i : ℤ) := by
    convert SimpleGraph.adjMatrix_mulVec_const_apply
      (G := G) (α := ℤ) (a := (1 : ℤ)) (v := i) using 1 <;> simp
  rw [show ∑ i : V, (G.adjMatrix ℤ *ᵥ (fun _ ↦ (1 : ℤ))) i =
      ∑ i : V, (G.degree i : ℤ) by
        exact Finset.sum_congr rfl (fun i _ ↦ hrow i)]
  rw [← Nat.cast_sum, G.sum_degrees_eq_twice_card_edges]
  push_cast
  ring

/-- A cycle on `k + 3` vertices has exactly `k + 3` edges. -/
theorem card_edgeFinset_cycleGraph (k : ℕ) :
    (SimpleGraph.cycleGraph (k + 3)).edgeFinset.card = k + 3 := by
  have hhand :=
    (SimpleGraph.cycleGraph (k + 3)).sum_degrees_eq_twice_card_edges
  simp only [SimpleGraph.cycleGraph_degree_three_le, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hhand
  apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
  calc
    2 * (SimpleGraph.cycleGraph (k + 3)).edgeFinset.card = (k + 3) * 2 := hhand.symm
    _ = 2 * (k + 3) := Nat.mul_comm _ _

/-- Every positive simply-laced Cartan graph is acyclic.  A copied cycle has
the all-one weighting of energy zero; positivity passes to the pullback and
edge monotonicity supplies the contradiction even when the copy has chords in
the ambient graph. -/
theorem IsPositiveCartan.isAcyclic [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : IsPositiveCartan G) : G.IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_free_cycleGraph]
  intro n hn hcopy
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := by
    exact ⟨n - 3, by omega⟩
  rcases hcopy with ⟨f⟩
  let e : Fin (k + 3) ↪ V := f.toEmbedding
  let K : SimpleGraph (Fin (k + 3)) := G.comap e
  have hcycle_le : SimpleGraph.cycleGraph (k + 3) ≤ K := by
    intro i j hij
    exact f.toHom.map_rel' hij
  have hK : IsPositiveCartan K := hG.comap e
  have henergy :
      graphCartanEnergy (SimpleGraph.cycleGraph (k + 3)) (fun _ ↦ (1 : ℤ)) = 0 := by
    rw [graphCartanEnergy_one, card_edgeFinset_cycleGraph]
    simp
  exact (not_isPositiveCartan_of_nonpositive_subgraph hcycle_le
    (by
      intro hzero
      have hvalue := congrFun hzero (0 : Fin (k + 3))
      norm_num at hvalue)
    (fun _ ↦ by norm_num) henergy.le) hK

/-! ### The four-star obstruction -/

/-- The affine `D4` star has a null Cartan vector: weight two at the centre
and weight one at its four leaves. -/
theorem fourStar_cartanEnergy :
    graphCartanEnergy (SimpleGraph.starGraph (none : Option (Fin 4)))
      (fun i ↦ match i with | none => (2 : ℤ) | some _ => 1) = 0 := by
  norm_num [graphCartanEnergy, Matrix.toBilin'_apply, graphCartanMatrix,
    SimpleGraph.starGraph_adj, Fin.sum_univ_succ]
  decide

/-- Every vertex of a positive simply-laced Cartan graph has degree at most
three.  Four chosen neighbours pull back the affine `D4` obstruction. -/
theorem IsPositiveCartan.degree_le_three [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : IsPositiveCartan G) (v : V) : G.degree v ≤ 3 := by
  by_contra hdeg
  have hfour : 4 ≤ G.degree v := by omega
  obtain ⟨leaf, hleaf⟩ :=
    Function.Embedding.exists_of_card_le_finset
      (α := Fin 4) (s := G.neighborFinset v) hfour
  have hadj (i : Fin 4) : G.Adj v (leaf i) := by
    have hm : leaf i ∈ G.neighborFinset v := hleaf (Set.mem_range_self i)
    simpa using hm
  let e : Option (Fin 4) ↪ V :=
    ⟨fun i ↦ match i with | none => v | some j => leaf j, by
      intro i j hij
      cases i with
      | none =>
          cases j with
          | none => rfl
          | some j =>
              exfalso
              exact (hadj j).ne hij
      | some i =>
          cases j with
          | none =>
              exfalso
              exact (hadj i).ne hij.symm
          | some j =>
              simp only [Option.some.injEq]
              exact leaf.injective hij⟩
  let K : SimpleGraph (Option (Fin 4)) := G.comap e
  have hstar_le : SimpleGraph.starGraph (none : Option (Fin 4)) ≤ K := by
    intro i j hij
    rw [SimpleGraph.starGraph_adj] at hij
    rcases hij.2 with hi | hj
    · subst i
      cases j with
      | none => exact (hij.1 rfl).elim
      | some j => exact hadj j
    · subst j
      cases i with
      | none => exact (hij.1 rfl).elim
      | some i => exact (hadj i).symm
  have hK : IsPositiveCartan K := hG.comap e
  exact (not_isPositiveCartan_of_nonpositive_subgraph hstar_le
    (by
      intro hzero
      have hvalue := congrFun hzero (none : Option (Fin 4))
      norm_num at hvalue)
    (by intro i; cases i <;> norm_num) fourStar_cartanEnergy.le) hK

end Lattice
end SRG266
