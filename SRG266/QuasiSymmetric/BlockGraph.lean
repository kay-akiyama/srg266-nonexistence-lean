/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.PairMultiplicity

/-!
# The block graph of a `Derived45` is `srg(55, 18, 9, 4)`

Two points of a `SRG266.QuasiSymmetric.Derived45` lie on one or two
common blocks (`Derived45.pairMult_cases`), so declaring the pairs with a
*single* common block adjacent defines a graph, `Derived45.blockGraph`.

One double count sums the product of the two pair multiplicities based at `p`
and at `q` over all points:

`∑_r t p r · t q r = 162 + 9 · t p q`  (`Derived45.sum_pairMult_mul`),

because the pairs `(i, j)` of derived blocks with `p ∈ block i`, `q ∈ block j`
number `9 · 9 = 81`, of which the `t p q` diagonal ones contribute `11` and the
rest contribute `2`.  Subtracting the two terms `r = p` and `r = q` and reading
`2 − t p r` as the adjacency indicator turns this into

`#(common neighbours of p and q) = 14 − 5 · t p q`,

i.e. `9` for adjacent and `4` for non-adjacent pairs.  Together with the
`18`-regularity already available as `Derived45.card_pairMult_eq_one` this is
`Derived45.blockGraph_isSRGWith : (blockGraph E).IsSRGWith 55 18 9 4`, and the
matrix form `A² = 5 A + 4 J + 14 I` is `Derived45.blockGraph_srg`.

Nothing here uses `decide` or any external datum.
-/

open scoped BigOperators Matrix

namespace SRG266.QuasiSymmetric

namespace Derived45

variable {P : Type*} [Fintype P] [DecidableEq P] (E : Derived45 P)

/-! ### The graph -/

/-- The block graph of a `Derived45`: two distinct points are
adjacent when they lie on exactly one common derived block. -/
def blockGraph : SimpleGraph P where
  Adj p q := p ≠ q ∧ E.pairMult p q = 1
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [E.pairMult_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Adjacency in the block graph. -/
theorem blockGraph_adj {p q : P} :
    E.blockGraph.Adj p q ↔ p ≠ q ∧ E.pairMult p q = 1 := Iff.rfl

instance : DecidableRel E.blockGraph.Adj := fun _ _ =>
  decidable_of_iff _ E.blockGraph_adj.symm

/-- Distinct points that are *not* adjacent lie on exactly two common blocks. -/
theorem pairMult_of_not_adj {p q : P} (hne : p ≠ q) (h : ¬ E.blockGraph.Adj p q) :
    E.pairMult p q = 2 :=
  (E.pairMult_cases hne).resolve_left fun h1 => h ⟨hne, h1⟩

/-! ### Regularity -/

/-- The block graph is `18`-regular. -/
theorem blockGraph_degree (p : P) : E.blockGraph.degree p = 18 := by
  have hset : E.blockGraph.neighborFinset p =
      (Finset.univ.erase p).filter fun q => E.pairMult p q = 1 := by
    ext q
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_erase,
      E.blockGraph_adj]
    exact ⟨fun h => ⟨⟨Ne.symm h.1, Finset.mem_univ q⟩, h.2⟩,
      fun h => ⟨Ne.symm h.1.1, h.2⟩⟩
  rw [SimpleGraph.degree, hset, E.card_pairMult_eq_one p]

/-- The block graph is regular of degree `18`. -/
theorem blockGraph_isRegular : E.blockGraph.IsRegularOfDegree 18 :=
  E.blockGraph_degree

/-! ### The two-point double count -/

/-- The derived blocks through `p` and those through `q` meet in
`pairMult p q` common indices. -/
theorem card_star_inter (p q : P) :
    ((starFinset E.block p) ∩ (starFinset E.block q)).card = E.pairMult p q := by
  have hset : (starFinset E.block p) ∩ (starFinset E.block q) =
      Finset.univ.filter fun i => p ∈ E.block i ∧ q ∈ E.block i := by
    ext i
    simp [starFinset]
  rw [hset]
  rfl

/-- `∑_r t p r · t q r = 162 + 9 · t p q`.

The `81` pairs `(i, j)` of derived blocks with `p ∈ block i` and `q ∈ block j`
contribute `|block i ∩ block j|`, which is `11` on the `t p q` diagonal pairs
and `2` elsewhere. -/
theorem sum_pairMult_mul (p q : P) :
    (∑ r : P, E.pairMult p r * E.pairMult q r) = 162 + 9 * E.pairMult p q := by
  have h : (∑ r : P, pairCount E.block p r * pairCount E.block q r) =
      ∑ i ∈ starFinset E.block p, ∑ j ∈ starFinset E.block q,
        ((E.block i) ∩ (E.block j)).card :=
    sum_pairCount_mul_univ₂ E.block E.block p q
  rw [show (∑ r : P, E.pairMult p r * E.pairMult q r) =
      ∑ r : P, pairCount E.block p r * pairCount E.block q r from rfl, h]
  have hcell : ∀ i : Fin 45, ∀ j : Fin 45,
      ((E.block i) ∩ (E.block j)).card = 2 + (if i = j then 9 else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [Finset.inter_self, E.block_card i]
      simp
    · rw [E.pair_meet i j hij]
      simp [hij]
  have hinner : ∀ i : Fin 45,
      (∑ j ∈ starFinset E.block q, ((E.block i) ∩ (E.block j)).card) =
        18 + (if i ∈ starFinset E.block q then 9 else 0) := by
    intro i
    rw [Finset.sum_congr rfl fun j _ => hcell i j, Finset.sum_add_distrib,
      Finset.sum_const, E.card_star q, Finset.sum_ite_eq]
    norm_num
  rw [Finset.sum_congr rfl fun i _ => hinner i, Finset.sum_add_distrib,
    Finset.sum_const, E.card_star p, ← Finset.sum_filter, Finset.sum_const,
    Finset.filter_mem_eq_inter, E.card_star_inter p q, smul_eq_mul, smul_eq_mul]
  ring

/-! ### Common neighbours -/

/-- The number of common neighbours of two distinct points, in the `Finset`
form used below. -/
theorem card_commonNeighbors_finset {p q : P} (hne : p ≠ q) :
    ((Finset.univ.filter fun r => E.blockGraph.Adj p r ∧ E.blockGraph.Adj q r).card : ℤ)
      + 5 * E.pairMult p q = 14 := by
  classical
  -- the integral weight `(t p r − 2)(t q r − 2)`
  set w : P → ℤ := fun r => ((E.pairMult p r : ℤ) - 2) * ((E.pairMult q r : ℤ) - 2)
    with hw
  have hp1 : (∑ r : P, ((E.pairMult p r : ℕ) : ℤ)) = 99 := by
    rw [← Nat.cast_sum, E.sum_pairMult_univ p]
    norm_num
  have hq1 : (∑ r : P, ((E.pairMult q r : ℕ) : ℤ)) = 99 := by
    rw [← Nat.cast_sum, E.sum_pairMult_univ q]
    norm_num
  have hpq : (∑ r : P, ((E.pairMult p r * E.pairMult q r : ℕ) : ℤ)) =
      162 + 9 * (E.pairMult p q : ℤ) := by
    rw [← Nat.cast_sum, E.sum_pairMult_mul p q]
    push_cast
    ring
  have hcard : (Finset.univ : Finset P).card = 55 := by
    rw [Finset.card_univ, E.point_card]
  -- the total sum
  have htotal : (∑ r : P, w r) = 9 * (E.pairMult p q : ℤ) - 14 := by
    have hexp : ∀ r : P, w r = ((E.pairMult p r * E.pairMult q r : ℕ) : ℤ)
        - 2 * ((E.pairMult p r : ℕ) : ℤ) - 2 * ((E.pairMult q r : ℕ) : ℤ) + 4 := by
      intro r
      simp only [hw]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun r _ => hexp r, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hp1, hq1, hpq, Finset.sum_const, hcard]
    push_cast
    ring
  -- the two diagonal terms
  have hwp : w p = 7 * (E.pairMult p q : ℤ) - 14 := by
    simp only [hw, E.pairMult_self p, E.pairMult_comm q p]
    push_cast
    ring
  have hwq : w q = 7 * (E.pairMult p q : ℤ) - 14 := by
    simp only [hw, E.pairMult_self q]
    push_cast
    ring
  -- strip them off
  have hstep1 := Finset.sum_erase_add (Finset.univ : Finset P) w (Finset.mem_univ p)
  have hqmem : q ∈ (Finset.univ : Finset P).erase p :=
    Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ q⟩
  have hstep2 := Finset.sum_erase_add ((Finset.univ : Finset P).erase p) w hqmem
  have hrest : (∑ r ∈ ((Finset.univ : Finset P).erase p).erase q, w r) =
      14 - 5 * (E.pairMult p q : ℤ) := by
    rw [htotal] at hstep1
    rw [hwp] at hstep1
    rw [hwq] at hstep2
    linarith
  -- on the remaining points the weight is the common-neighbour indicator
  have hind : ∀ r ∈ ((Finset.univ : Finset P).erase p).erase q,
      w r = if E.blockGraph.Adj p r ∧ E.blockGraph.Adj q r then 1 else 0 := by
    intro r hr
    have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
    have hrp : r ≠ p := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hr)).1
    have hpr : p ≠ r := Ne.symm hrp
    have hqr : q ≠ r := Ne.symm hrq
    rcases E.pairMult_cases hpr with h1 | h1 <;> rcases E.pairMult_cases hqr with h2 | h2 <;>
      simp [hw, h1, h2, E.blockGraph_adj, hpr, hqr]
  rw [Finset.sum_congr rfl hind, Finset.sum_boole] at hrest
  have hfilter : (((Finset.univ : Finset P).erase p).erase q).filter
      (fun r => E.blockGraph.Adj p r ∧ E.blockGraph.Adj q r) =
      Finset.univ.filter fun r => E.blockGraph.Adj p r ∧ E.blockGraph.Adj q r := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    constructor
    · rintro ⟨-, hadj⟩
      exact hadj
    · intro hadj
      exact ⟨⟨hadj.2.ne', hadj.1.ne'⟩, hadj⟩
  rw [hfilter] at hrest
  linarith

/-- The common neighbours of two points, as a `Finset` cardinality. -/
theorem card_commonNeighbors_eq (p q : P) :
    Fintype.card (E.blockGraph.commonNeighbors p q) =
      (Finset.univ.filter fun r => E.blockGraph.Adj p r ∧ E.blockGraph.Adj q r).card := by
  classical
  rw [← Set.toFinset_card]
  congr 1
  ext r
  simp [SimpleGraph.mem_commonNeighbors]

/-- Two adjacent points of the block graph have `9` common neighbours. -/
theorem card_commonNeighbors_of_adj {p q : P} (h : E.blockGraph.Adj p q) :
    Fintype.card (E.blockGraph.commonNeighbors p q) = 9 := by
  have hcount := E.card_commonNeighbors_finset h.ne
  rw [h.2] at hcount
  push_cast at hcount
  have hz : ((Finset.univ.filter fun r =>
      E.blockGraph.Adj p r ∧ E.blockGraph.Adj q r).card : ℤ) = 9 := by linarith
  rw [E.card_commonNeighbors_eq p q]
  exact_mod_cast hz

/-- Two distinct non-adjacent points of the block graph have `4` common
neighbours. -/
theorem card_commonNeighbors_of_not_adj {p q : P} (hne : p ≠ q)
    (h : ¬ E.blockGraph.Adj p q) :
    Fintype.card (E.blockGraph.commonNeighbors p q) = 4 := by
  have hcount := E.card_commonNeighbors_finset hne
  rw [E.pairMult_of_not_adj hne h] at hcount
  push_cast at hcount
  have hz : ((Finset.univ.filter fun r =>
      E.blockGraph.Adj p r ∧ E.blockGraph.Adj q r).card : ℤ) = 4 := by linarith
  rw [E.card_commonNeighbors_eq p q]
  exact_mod_cast hz

/-! ### The strong regularity -/

/-- The block graph of a `Derived45` is strongly regular with
parameters `(55, 18, 9, 4)`. -/
theorem blockGraph_isSRGWith : E.blockGraph.IsSRGWith 55 18 9 4 where
  card := E.point_card
  regular := E.blockGraph_isRegular
  of_adj := fun _ _ h => E.card_commonNeighbors_of_adj h
  of_not_adj := fun {_ _} hne h => E.card_commonNeighbors_of_not_adj hne h

/-- The complement adjacency matrix is `J − I − A`. -/
theorem compl_adjMatrix :
    (E.blockGraph)ᶜ.adjMatrix ℤ =
      (allOnesMatrix : Matrix P P ℤ) - 1 - E.blockGraph.adjMatrix ℤ := by
  ext p q
  by_cases hpq : p = q
  · subst hpq
    simp [SimpleGraph.adjMatrix_apply]
  · by_cases hadj : E.blockGraph.Adj p q <;>
      simp [SimpleGraph.adjMatrix_apply, SimpleGraph.compl_adj, hpq, hadj,
        Matrix.one_apply_ne hpq]

/-- `A² = 5 A + 4 J + 14 I` for the block graph of a
`Derived45`.  This is the entrywise reading of `blockGraph_isSRGWith`: the
diagonal is the degree `18 = 4 + 14`, adjacent pairs have `9 = 5 + 4` common
neighbours, non-adjacent distinct pairs have `4`. -/
theorem blockGraph_srg :
    (E.blockGraph.adjMatrix ℤ) ^ 2 =
      5 • E.blockGraph.adjMatrix ℤ + 4 • (allOnesMatrix : Matrix P P ℤ) +
        14 • (1 : Matrix P P ℤ) := by
  have h := E.blockGraph_isSRGWith.matrix_eq (α := ℤ)
  rw [E.compl_adjMatrix] at h
  rw [h]
  ext p q
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    allOnesMatrix_apply, SimpleGraph.adjMatrix_apply]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  by_cases hpq : p = q
  · subst hpq
    simp
  · by_cases hadj : E.blockGraph.Adj p q <;> simp [hpq, hadj]

end Derived45

end SRG266.QuasiSymmetric
