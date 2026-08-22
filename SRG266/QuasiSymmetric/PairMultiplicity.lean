/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.DerivedResidual

/-!
# Pair multiplicities in the derived and residual structures

Everything here is a statement about a `SRG266.QuasiSymmetric.Derived45` and its
`SRG266.QuasiSymmetric.Residual165`; the `56 × 210` incidence matrix has
already been discarded.

Fix a point `p`.  For `q ≠ p` write `t p q` for the number of derived blocks
containing both (`Derived45.pairMult`) and `b p q` for the number of residual
blocks containing both (`Residual165.pairMult`).  Two double counts,

* `∑_{q ≠ p} t p q = 90` and `∑_{q ≠ p} (t p q)² = 162`,

force `t p q ∈ {1, 2}` — this is `Derived45.pairMult_cases`, the fact that
turns the derived structure into a graph and identifies its parameters as
`srg(55, 18, 9, 4)`.  Three further double counts,

* `∑_{q ≠ p} b p q = 396`, `∑_{q ≠ p} (b p q)² = 2916` and
  `∑_{q ≠ p} t p q · b p q = 648`,

pin the *sum* pointwise: `t p q + b p q = 9` for every `q ≠ p`
(`residual_pairMult_add`), hence `b p q = 9 − t p q ∈ {7, 8}`
(`residual_pairMult`, `residual_pairMult_cases`).

The last statement shrinks the clique target from `165` to `8`. It follows
inside the `Derived45`/`Residual165` interface; no additional design field is
needed because the five double counts above have zero variance.

## Method

Both pointwise conclusions come from the same mechanism: an inequality
`f r ≤ g r` valid for every natural number, whose two sums over the `54` points
`r ≠ p` agree.  `Finset.sum_eq_sum_iff_of_le` then upgrades the equality of
sums to a pointwise equality.  For `pairMult_cases` the inequality is
`3 t ≤ t² + 2`, for `residual_pairMult_add` it is `18 x ≤ x² + 81`.

## Generic double counts

The `PairCount` section states five double counts for an *arbitrary* family
`f : ι → Finset P` of finite sets.  `sum_pairCount_univ` and
`sum_pairCount_mul_univ₂` are what the counting facts of this file and the
block graph of `SRG266/QuasiSymmetric/BlockGraph.lean` instantiate;
`sum_inter_card`, `sum_inter_card_sq` and `sum_star_inter_card` read a sum over
the family index as a sum over a fixed set of points, and are what the `K₁₁`
recoordinatisation and the arc-degree lemma consume.
-/

open scoped BigOperators

namespace SRG266.QuasiSymmetric

/-! ### Generic pair counting for a family of finite sets -/

section PairCount

variable {P : Type*} [DecidableEq P]

/-- The number of members of the family `f` containing both `p`
and `q`. -/
def pairCount {ι : Type*} [Fintype ι] (f : ι → Finset P) (p q : P) : ℕ :=
  (Finset.univ.filter fun i => p ∈ f i ∧ q ∈ f i).card

/-- The indices of the members of the family `f` containing `p`. -/
def starFinset {ι : Type*} [Fintype ι] (f : ι → Finset P) (p : P) : Finset ι :=
  Finset.univ.filter fun i => p ∈ f i

/-- The diagonal value of the pair count is the number of members through the
point. -/
theorem pairCount_self {ι : Type*} [Fintype ι] (f : ι → Finset P) (p : P) :
    pairCount f p p = (starFinset f p).card := by
  simp [pairCount, starFinset]

/-- The number of members of `f` containing `p` and `q` is the number of
members containing `q` and `p`. -/
theorem pairCount_comm {ι : Type*} [Fintype ι] (f : ι → Finset P) (p q : P) :
    pairCount f p q = pairCount f q p := by
  simp only [pairCount]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_comm

/-- Summing the pair count over all points recovers
the total size of the members through `p`. -/
theorem sum_pairCount_univ [Fintype P] {ι : Type*} [Fintype ι] (f : ι → Finset P)
    (p : P) :
    (∑ q : P, pairCount f p q) = ∑ i ∈ starFinset f p, (f i).card := by
  have hterm : ∀ q : P,
      pairCount f p q = ∑ i : ι, if p ∈ f i ∧ q ∈ f i then 1 else 0 := fun q =>
    Finset.card_filter _ _
  rw [Finset.sum_congr rfl fun q _ => hterm q, Finset.sum_comm]
  simp only [starFinset, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hpi : p ∈ f i <;> simp [hpi]

/-- Summing over all points the
product of the pair count of `f` based at `p` with the pair count of `g` based
at `q` recovers the total size of the pairwise intersections of the members of
`f` through `p` with the members of `g` through `q`.

This is the two-point generalisation used by
`SRG266.QuasiSymmetric.Derived45.sum_pairMult_mul`; the diagonal case `q = p`
is `sum_pairCount_mul_univ` below. -/
theorem sum_pairCount_mul_univ₂ [Fintype P] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → Finset P) (g : κ → Finset P) (p q : P) :
    (∑ r : P, pairCount f p r * pairCount g q r) =
      ∑ i ∈ starFinset f p, ∑ n ∈ starFinset g q, ((f i) ∩ (g n)).card := by
  have hterm : ∀ r : P, pairCount f p r * pairCount g q r =
      ∑ i : ι, ∑ n : κ, (if p ∈ f i ∧ r ∈ f i then 1 else 0) *
        (if q ∈ g n ∧ r ∈ g n then 1 else 0) := by
    intro r
    rw [pairCount, pairCount, Finset.card_filter, Finset.card_filter,
      Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun r _ => hterm r, Finset.sum_comm]
  have hswap : ∀ i : ι,
      (∑ r : P, ∑ n : κ, (if p ∈ f i ∧ r ∈ f i then 1 else 0) *
          (if q ∈ g n ∧ r ∈ g n then 1 else 0)) =
        ∑ n : κ, ∑ r : P, (if p ∈ f i ∧ r ∈ f i then 1 else 0) *
          (if q ∈ g n ∧ r ∈ g n then 1 else 0) := fun _ => Finset.sum_comm
  rw [Finset.sum_congr rfl fun i _ => hswap i]
  have hcell : ∀ (i : ι) (n : κ),
      (∑ r : P, (if p ∈ f i ∧ r ∈ f i then 1 else 0) *
          (if q ∈ g n ∧ r ∈ g n then 1 else 0)) =
        if p ∈ f i ∧ q ∈ g n then ((f i) ∩ (g n)).card else 0 := by
    intro i n
    by_cases hA : p ∈ f i
    · by_cases hB : q ∈ g n
      · simp only [hA, hB, true_and, and_true, if_true]
        have hpt : ∀ r : P, (if r ∈ f i then (1 : ℕ) else 0) *
            (if r ∈ g n then (1 : ℕ) else 0) =
              if r ∈ f i ∧ r ∈ g n then 1 else 0 := by
          intro r
          by_cases h1 : r ∈ f i <;> by_cases h2 : r ∈ g n <;> simp [h1, h2]
        rw [Finset.sum_congr rfl fun r _ => hpt r, ← Finset.card_filter]
        congr 1
        ext r
        simp
      · simp [hB]
    · simp [hA]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun n _ => hcell i n]
  simp only [starFinset, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hA : p ∈ f i
  · simp only [hA, true_and, if_true]
  · simp [hA]

/-- Summing the product of two pair counts over all
points recovers the total size of the pairwise intersections of the members
through `p`.  Taking `f = g` gives the sum of squares; taking `f` derived and
`g` residual gives the mixed sum. -/
theorem sum_pairCount_mul_univ [Fintype P] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → Finset P) (g : κ → Finset P) (p : P) :
    (∑ q : P, pairCount f p q * pairCount g p q) =
      ∑ i ∈ starFinset f p, ∑ n ∈ starFinset g p, ((f i) ∩ (g n)).card :=
  sum_pairCount_mul_univ₂ f g p p

/-! ### Incidences between a fixed set and the family

The three double counts below all read a sum over the *family index* as a sum
over a fixed finite set `s` of points, and are what the `K₁₁` recoordinatisation
and the arc-degree lemma consume. -/

variable {ι : Type*} [Fintype ι]

/-- The trace of the family `g` on `s`, summed over the family, counts the
incidences between `s` and `g`. -/
theorem sum_inter_card (g : ι → Finset P) (s : Finset P) :
    (∑ i, (s ∩ g i).card) = ∑ e ∈ s, (starFinset g e).card := by
  have hleft : ∀ i : ι, (s ∩ g i).card = ∑ e ∈ s, if e ∈ g i then 1 else 0 := by
    intro i
    rw [← Finset.filter_mem_eq_inter, Finset.card_filter]
  have hright : ∀ e : P, (starFinset g e).card = ∑ i : ι, if e ∈ g i then 1 else 0 := by
    intro e
    rw [starFinset, Finset.card_filter]
  rw [Finset.sum_congr rfl fun i _ => hleft i,
    Finset.sum_congr rfl fun e _ => hright e, Finset.sum_comm]

/-- The squared trace of the family `g` on `s`, summed over the family, counts
the pairs of points of `s` weighted by their pair count. -/
theorem sum_inter_card_sq (g : ι → Finset P) (s : Finset P) :
    (∑ i, (s ∩ g i).card ^ 2) = ∑ e ∈ s, ∑ f ∈ s, pairCount g e f := by
  have hleft : ∀ i : ι, (s ∩ g i).card ^ 2 =
      ∑ e ∈ s, ∑ f ∈ s, (if e ∈ g i then 1 else 0) * (if f ∈ g i then 1 else 0) := by
    intro i
    rw [sq, ← Finset.filter_mem_eq_inter, Finset.card_filter, Finset.sum_mul_sum]
  have hright : ∀ e f : P, pairCount g e f =
      ∑ i : ι, (if e ∈ g i then 1 else 0) * (if f ∈ g i then 1 else 0) := by
    intro e f
    rw [pairCount, Finset.card_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : e ∈ g i <;> by_cases h2 : f ∈ g i <;> simp [h1, h2]
  rw [Finset.sum_congr rfl fun i _ => hleft i,
    Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => hright e f,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_comm

/-- The trace of the family `g` on `s`, summed over the members through a fixed
point `e`, is the pair count of `e` against `s`. -/
theorem sum_star_inter_card (g : ι → Finset P) (e : P) (s : Finset P) :
    (∑ i ∈ starFinset g e, (s ∩ g i).card) = ∑ f ∈ s, pairCount g e f := by
  have hleft : ∀ i : ι, (s ∩ g i).card = ∑ f ∈ s, if f ∈ g i then 1 else 0 := by
    intro i
    rw [← Finset.filter_mem_eq_inter, Finset.card_filter]
  have hright : ∀ f : P, pairCount g e f = ∑ i ∈ starFinset g e,
      if f ∈ g i then 1 else 0 := by
    intro f
    rw [pairCount, starFinset, Finset.sum_filter, Finset.card_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : e ∈ g i <;> simp [h1]
  rw [Finset.sum_congr rfl fun i _ => hleft i,
    Finset.sum_congr rfl fun f _ => hright f, Finset.sum_comm]

end PairCount

/-! ### Elementary numeric inequalities -/

/-- For every natural number `t` one has `3 t ≤ t² + 2`, with equality exactly
at `t = 1` and `t = 2`. -/
theorem three_mul_le_sq_add_two (t : ℕ) : 3 * t ≤ t ^ 2 + 2 := by
  rcases Nat.lt_or_ge t 3 with h | h
  · interval_cases t <;> norm_num
  · nlinarith

/-- For every natural number `x` one has `4 x ≤ x² + 4`, with equality exactly
at `x = 2`. -/
theorem four_mul_le_sq_add_four (x : ℕ) : 4 * x ≤ x ^ 2 + 4 := by
  nlinarith [sq_nonneg ((x : ℤ) - 2), Int.ofNat_le.mpr (Nat.zero_le x)]

/-- For every natural number `x` one has `18 x ≤ x² + 81`, with equality
exactly at `x = 9`. -/
theorem eighteen_mul_le_sq_add (x : ℕ) : 18 * x ≤ x ^ 2 + 81 := by
  nlinarith [sq_nonneg ((x : ℤ) - 9), Int.ofNat_le.mpr (Nat.zero_le x)]

/-- `2 * C(n, 2) + n = n²`: the identity turning a sum of binomial
coefficients into a sum of squares. -/
theorem two_mul_choose_two_add (n : ℕ) : 2 * n.choose 2 + n = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    have hexp : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    rw [hexp, ← ih]
    ring

/-! ### Pair multiplicities of a `Derived45` -/

namespace Derived45

variable {P : Type*} [Fintype P] [DecidableEq P] (E : Derived45 P)

/-- `E.pairMult p q` is the number of derived blocks containing
both `p` and `q`. -/
def pairMult (p q : P) : ℕ := pairCount E.block p q

/-- The derived pair multiplicity is symmetric. -/
theorem pairMult_comm (p q : P) : E.pairMult p q = E.pairMult q p :=
  pairCount_comm E.block p q

/-- Each point lies on `9` derived blocks. -/
theorem card_star (p : P) : (starFinset E.block p).card = 9 := E.replication p

/-- The diagonal value of the pair multiplicity is the replication number. -/
theorem pairMult_self (p : P) : E.pairMult p p = 9 := by
  rw [pairMult, pairCount_self, E.card_star p]

include E in
/-- There are `54` points other than a given one. -/
theorem card_erase_univ (p : P) : (Finset.univ.erase p).card = 54 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, E.point_card]

/-- Summed over all points, the pair multiplicity at `p` is `9 · 11 = 99`. -/
theorem sum_pairMult_univ (p : P) : (∑ q : P, E.pairMult p q) = 99 := by
  have h : (∑ q : P, E.pairMult p q) = ∑ i ∈ starFinset E.block p, (E.block i).card :=
    sum_pairCount_univ E.block p
  rw [h, Finset.sum_congr rfl fun i _ => E.block_card i, Finset.sum_const,
    E.card_star p]
  norm_num [nsmul_eq_mul]

/-- `∑_{q ≠ p} t p q = 90`. -/
theorem sum_pairMult (p : P) :
    (∑ q ∈ Finset.univ.erase p, E.pairMult p q) = 90 := by
  have hsplit :=
    Finset.sum_erase_add Finset.univ (fun q => E.pairMult p q) (Finset.mem_univ p)
  rw [E.sum_pairMult_univ p, E.pairMult_self p] at hsplit
  omega

/-- Summed over all points, the squared pair multiplicity at `p` is
`9 · (11 + 8 · 2) = 243`. -/
theorem sum_pairMult_sq_univ (p : P) : (∑ q : P, E.pairMult p q ^ 2) = 243 := by
  have hsq : ∀ q : P, E.pairMult p q ^ 2 = E.pairMult p q * E.pairMult p q :=
    fun q => sq (E.pairMult p q)
  rw [Finset.sum_congr rfl fun q _ => hsq q]
  have h : (∑ q : P, pairCount E.block p q * pairCount E.block p q) =
      ∑ i ∈ starFinset E.block p, ∑ j ∈ starFinset E.block p,
        ((E.block i) ∩ (E.block j)).card :=
    sum_pairCount_mul_univ E.block E.block p
  rw [show (∑ q : P, E.pairMult p q * E.pairMult p q) =
      ∑ q : P, pairCount E.block p q * pairCount E.block p q from rfl, h]
  have hinner : ∀ i ∈ starFinset E.block p,
      (∑ j ∈ starFinset E.block p, ((E.block i) ∩ (E.block j)).card) = 27 := by
    intro i hi
    rw [← Finset.sum_erase_add _ _ hi]
    have hoff : ∀ j ∈ (starFinset E.block p).erase i,
        ((E.block i) ∩ (E.block j)).card = 2 := fun j hj =>
      E.pair_meet i j (Ne.symm (Finset.mem_erase.mp hj).1)
    rw [Finset.sum_congr rfl hoff, Finset.sum_const,
      Finset.card_erase_of_mem hi, E.card_star p, Finset.inter_self, E.block_card i]
    norm_num [nsmul_eq_mul]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, E.card_star p]
  norm_num [nsmul_eq_mul]

/-- `∑_{q ≠ p} (t p q)² = 162`. -/
theorem sum_pairMult_sq (p : P) :
    (∑ q ∈ Finset.univ.erase p, E.pairMult p q ^ 2) = 162 := by
  have hsplit :=
    Finset.sum_erase_add Finset.univ (fun q => E.pairMult p q ^ 2) (Finset.mem_univ p)
  rw [E.sum_pairMult_sq_univ p, E.pairMult_self p] at hsplit
  omega

/-- Two distinct points of a `Derived45` lie on exactly one or
exactly two common blocks.

The proof is the classical `∑ (t − 1)(t − 2) = 0` argument in the equivalent
form `∑ 3t = ∑ (t² + 2)`, both sides being `270`. -/
theorem pairMult_cases {p q : P} (h : p ≠ q) :
    E.pairMult p q = 1 ∨ E.pairMult p q = 2 := by
  have hle : ∀ r ∈ Finset.univ.erase p, 3 * E.pairMult p r ≤ E.pairMult p r ^ 2 + 2 :=
    fun r _ => three_mul_le_sq_add_two _
  have hsum : (∑ r ∈ Finset.univ.erase p, 3 * E.pairMult p r) =
      ∑ r ∈ Finset.univ.erase p, (E.pairMult p r ^ 2 + 2) := by
    rw [← Finset.mul_sum, E.sum_pairMult p, Finset.sum_add_distrib,
      E.sum_pairMult_sq p, Finset.sum_const, E.card_erase_univ p]
    norm_num [nsmul_eq_mul]
  have hpt := (Finset.sum_eq_sum_iff_of_le hle).mp hsum q
    (Finset.mem_erase.mpr ⟨Ne.symm h, Finset.mem_univ q⟩)
  have hz : ((E.pairMult p q : ℤ) - 1) * ((E.pairMult p q : ℤ) - 2) = 0 := by
    have hcast : (3 : ℤ) * (E.pairMult p q : ℤ) = (E.pairMult p q : ℤ) ^ 2 + 2 := by
      exact_mod_cast hpt
    linear_combination -hcast
  rcases mul_eq_zero.mp hz with hone | htwo
  · left
    have : (E.pairMult p q : ℤ) = 1 := by linarith
    exact_mod_cast this
  · right
    have : (E.pairMult p q : ℤ) = 2 := by linarith
    exact_mod_cast this

/-- The pair multiplicity of distinct points is positive. -/
theorem pairMult_pos {p q : P} (h : p ≠ q) : 0 < E.pairMult p q := by
  rcases E.pairMult_cases h with h' | h' <;> omega

/-- The pair multiplicity of distinct points is at most `2`. -/
theorem pairMult_le_two {p q : P} (h : p ≠ q) : E.pairMult p q ≤ 2 := by
  rcases E.pairMult_cases h with h' | h' <;> omega

/-- `∑_{q ≠ p} C(t p q, 2) = 36`: the `C(9, 2) = 36` pairs of derived
blocks through `p` each contribute their unique second common point. -/
theorem sum_pairMult_choose (p : P) :
    (∑ q ∈ Finset.univ.erase p, (E.pairMult p q).choose 2) = 36 := by
  have hid : ∀ r ∈ Finset.univ.erase p,
      E.pairMult p r ^ 2 = 2 * (E.pairMult p r).choose 2 + E.pairMult p r :=
    fun r _ => (two_mul_choose_two_add (E.pairMult p r)).symm
  have hsum := E.sum_pairMult_sq p
  rw [Finset.sum_congr rfl hid, Finset.sum_add_distrib, ← Finset.mul_sum,
    E.sum_pairMult p] at hsum
  omega

/-- Exactly `18` of the `54` other points meet `p` in
a single block: this is the `18`-regularity of the block graph, before any
graph is introduced. -/
theorem card_pairMult_eq_one (p : P) :
    ((Finset.univ.erase p).filter fun q => E.pairMult p q = 1).card = 18 := by
  classical
  set s : Finset P := Finset.univ.erase p with hs
  set n₁ : ℕ := (s.filter fun q => E.pairMult p q = 1).card with hn₁
  set n₂ : ℕ := (s.filter fun q => E.pairMult p q = 2).card with hn₂
  have hpartition : n₁ + n₂ = 54 := by
    have hnot : (s.filter fun q => ¬ E.pairMult p q = 1) =
        s.filter fun q => E.pairMult p q = 2 := by
      refine Finset.filter_congr fun q hq => ?_
      have hne : p ≠ q := Ne.symm (Finset.mem_erase.mp (hs ▸ hq)).1
      rcases E.pairMult_cases hne with h | h <;> simp [h]
    have hsplit := Finset.card_filter_add_card_filter_not (s := s)
      (p := fun q => E.pairMult p q = 1)
    rw [hnot, ← hn₁, ← hn₂, E.card_erase_univ p] at hsplit
    exact hsplit
  have hweighted : n₁ + 2 * n₂ = 90 := by
    have hsum := E.sum_pairMult p
    have hsplit :
        (∑ q ∈ s, E.pairMult p q) =
          (∑ q ∈ s.filter fun q => E.pairMult p q = 1, E.pairMult p q) +
            ∑ q ∈ s.filter fun q => ¬ E.pairMult p q = 1, E.pairMult p q :=
      (Finset.sum_filter_add_sum_filter_not s _ _).symm
    have hone : (∑ q ∈ s.filter fun q => E.pairMult p q = 1, E.pairMult p q) = n₁ := by
      rw [Finset.sum_congr rfl fun q hq => (Finset.mem_filter.mp hq).2,
        Finset.sum_const, ← hn₁]
      simp
    have htwo :
        (∑ q ∈ s.filter fun q => ¬ E.pairMult p q = 1, E.pairMult p q) = 2 * n₂ := by
      have hnot : (s.filter fun q => ¬ E.pairMult p q = 1) =
          s.filter fun q => E.pairMult p q = 2 := by
        refine Finset.filter_congr fun q hq => ?_
        have hne : p ≠ q := Ne.symm (Finset.mem_erase.mp (hs ▸ hq)).1
        rcases E.pairMult_cases hne with h | h <;> simp [h]
      rw [hnot, Finset.sum_congr rfl fun q hq => (Finset.mem_filter.mp hq).2,
        Finset.sum_const, hn₂]
      ring
    rw [hone, htwo, hsum] at hsplit
    omega
  omega

end Derived45

/-! ### Pair multiplicities of a `Residual165` -/

namespace Residual165

variable {P : Type*} [Fintype P] [DecidableEq P] {E : Derived45 P} (R : Residual165 E)

/-- `R.pairMult p q` is the number of residual blocks containing
both `p` and `q`. -/
def pairMult (p q : P) : ℕ := pairCount R.res p q

/-- The residual pair multiplicity is symmetric. -/
theorem pairMult_comm (p q : P) : R.pairMult p q = R.pairMult q p :=
  pairCount_comm R.res p q

/-- Each point lies on `36` residual blocks. -/
theorem card_star (p : P) : (starFinset R.res p).card = 36 := R.res_rep p

/-- The diagonal value of the residual pair multiplicity. -/
theorem pairMult_self (p : P) : R.pairMult p p = 36 := by
  rw [pairMult, pairCount_self, R.card_star p]

/-- Two distinct residual blocks with a common point meet in `3` points. -/
theorem res_meet_of_common {m n : Fin 165} (hmn : m ≠ n) {p : P}
    (hm : p ∈ R.res m) (hn : p ∈ R.res n) : ((R.res m) ∩ (R.res n)).card = 3 := by
  rcases R.res_meet m n hmn with h | h
  · exact absurd (Finset.card_ne_zero_of_mem (Finset.mem_inter.mpr ⟨hm, hn⟩)) (by simp [h])
  · exact h

/-- A derived block and a residual block with a common point meet in `3`
points. -/
theorem cross_meet_of_common (i : Fin 45) (n : Fin 165) {p : P}
    (hi : p ∈ E.block i) (hn : p ∈ R.res n) : ((E.block i) ∩ (R.res n)).card = 3 := by
  rcases R.cross_meet i n with h | h
  · exact absurd (Finset.card_ne_zero_of_mem (Finset.mem_inter.mpr ⟨hi, hn⟩)) (by simp [h])
  · exact h

/-- Summed over all points, the residual pair multiplicity at `p` is
`36 · 12 = 432`. -/
theorem sum_pairMult_univ (p : P) : (∑ q : P, R.pairMult p q) = 432 := by
  have h : (∑ q : P, R.pairMult p q) = ∑ n ∈ starFinset R.res p, (R.res n).card :=
    sum_pairCount_univ R.res p
  rw [h, Finset.sum_congr rfl fun n _ => R.res_card n, Finset.sum_const, R.card_star p]
  norm_num [nsmul_eq_mul]

/-- `∑_{q ≠ p} b p q = 396`. -/
theorem sum_pairMult (p : P) :
    (∑ q ∈ Finset.univ.erase p, R.pairMult p q) = 396 := by
  have hsplit :=
    Finset.sum_erase_add Finset.univ (fun q => R.pairMult p q) (Finset.mem_univ p)
  rw [R.sum_pairMult_univ p, R.pairMult_self p] at hsplit
  omega

/-- Summed over all points, the squared residual pair multiplicity at `p` is
`36 · (12 + 35 · 3) = 4212`. -/
theorem sum_pairMult_sq_univ (p : P) : (∑ q : P, R.pairMult p q ^ 2) = 4212 := by
  have hsq : ∀ q : P, R.pairMult p q ^ 2 = R.pairMult p q * R.pairMult p q :=
    fun q => sq (R.pairMult p q)
  rw [Finset.sum_congr rfl fun q _ => hsq q]
  have h : (∑ q : P, pairCount R.res p q * pairCount R.res p q) =
      ∑ m ∈ starFinset R.res p, ∑ n ∈ starFinset R.res p,
        ((R.res m) ∩ (R.res n)).card :=
    sum_pairCount_mul_univ R.res R.res p
  rw [show (∑ q : P, R.pairMult p q * R.pairMult p q) =
      ∑ q : P, pairCount R.res p q * pairCount R.res p q from rfl, h]
  have hmem : ∀ n ∈ starFinset R.res p, p ∈ R.res n := by
    intro n hn
    simpa [starFinset] using hn
  have hinner : ∀ m ∈ starFinset R.res p,
      (∑ n ∈ starFinset R.res p, ((R.res m) ∩ (R.res n)).card) = 117 := by
    intro m hm
    rw [← Finset.sum_erase_add _ _ hm]
    have hoff : ∀ n ∈ (starFinset R.res p).erase m,
        ((R.res m) ∩ (R.res n)).card = 3 := by
      intro n hn
      have hnm : m ≠ n := Ne.symm (Finset.mem_erase.mp hn).1
      exact R.res_meet_of_common hnm (hmem m hm)
        (hmem n (Finset.mem_of_mem_erase hn))
    rw [Finset.sum_congr rfl hoff, Finset.sum_const,
      Finset.card_erase_of_mem hm, R.card_star p, Finset.inter_self, R.res_card m]
    norm_num [nsmul_eq_mul]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, R.card_star p]
  norm_num [nsmul_eq_mul]

/-- `∑_{q ≠ p} (b p q)² = 2916`. -/
theorem sum_pairMult_sq (p : P) :
    (∑ q ∈ Finset.univ.erase p, R.pairMult p q ^ 2) = 2916 := by
  have hsplit :=
    Finset.sum_erase_add Finset.univ (fun q => R.pairMult p q ^ 2) (Finset.mem_univ p)
  rw [R.sum_pairMult_sq_univ p, R.pairMult_self p] at hsplit
  omega

/-- Summed over all points, the mixed product of the derived and residual pair
multiplicities at `p` is `9 · 36 · 3 = 972`. -/
theorem sum_cross_univ (p : P) :
    (∑ q : P, E.pairMult p q * R.pairMult p q) = 972 := by
  have h : (∑ q : P, pairCount E.block p q * pairCount R.res p q) =
      ∑ i ∈ starFinset E.block p, ∑ n ∈ starFinset R.res p,
        ((E.block i) ∩ (R.res n)).card :=
    sum_pairCount_mul_univ E.block R.res p
  rw [show (∑ q : P, E.pairMult p q * R.pairMult p q) =
      ∑ q : P, pairCount E.block p q * pairCount R.res p q from rfl, h]
  have hmemE : ∀ i ∈ starFinset E.block p, p ∈ E.block i := by
    intro i hi
    simpa [starFinset] using hi
  have hmemR : ∀ n ∈ starFinset R.res p, p ∈ R.res n := by
    intro n hn
    simpa [starFinset] using hn
  have hinner : ∀ i ∈ starFinset E.block p,
      (∑ n ∈ starFinset R.res p, ((E.block i) ∩ (R.res n)).card) = 108 := by
    intro i hi
    have hcell : ∀ n ∈ starFinset R.res p, ((E.block i) ∩ (R.res n)).card = 3 :=
      fun n hn => R.cross_meet_of_common i n (hmemE i hi) (hmemR n hn)
    rw [Finset.sum_congr rfl hcell, Finset.sum_const, R.card_star p]
    norm_num [nsmul_eq_mul]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, E.card_star p]
  norm_num [nsmul_eq_mul]

/-- `∑_{q ≠ p} t p q · b p q = 648`. -/
theorem sum_cross (p : P) :
    (∑ q ∈ Finset.univ.erase p, E.pairMult p q * R.pairMult p q) = 648 := by
  have hsplit :=
    Finset.sum_erase_add Finset.univ
      (fun q => E.pairMult p q * R.pairMult p q) (Finset.mem_univ p)
  rw [R.sum_cross_univ p, E.pairMult_self p, R.pairMult_self p] at hsplit
  omega

end Residual165

/-! ### The residual pair multiplicity is `9 − t` -/

section ResidualPairMult

variable {P : Type*} [Fintype P] [DecidableEq P] {E : Derived45 P} (R : Residual165 E)

/-- The total pair multiplicity `t + b`, summed over the points other than `p`,
is `90 + 396 = 486`. -/
theorem sum_total_pairMult (p : P) :
    (∑ q ∈ Finset.univ.erase p, (E.pairMult p q + R.pairMult p q)) = 486 := by
  rw [Finset.sum_add_distrib, E.sum_pairMult p, R.sum_pairMult p]

/-- The squared total pair multiplicity, summed over the points other than `p`,
is `162 + 2 · 648 + 2916 = 4374`. -/
theorem sum_total_pairMult_sq (p : P) :
    (∑ q ∈ Finset.univ.erase p, (E.pairMult p q + R.pairMult p q) ^ 2) = 4374 := by
  have hexp : ∀ q ∈ Finset.univ.erase p,
      (E.pairMult p q + R.pairMult p q) ^ 2 =
        E.pairMult p q ^ 2 + 2 * (E.pairMult p q * R.pairMult p q) +
          R.pairMult p q ^ 2 := fun q _ => by ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, E.sum_pairMult_sq p, R.sum_cross p, R.sum_pairMult_sq p]
  norm_num

/-- For distinct points `p` and `q`, the number of derived
blocks through both plus the number of residual blocks through both is exactly
`9` — the replication number of a pair in the original design.

Both sums `∑ 18(t + b)` and `∑ ((t + b)² + 81)` over the `54` points `q ≠ p`
equal `8748`, and `18 x ≤ x² + 81` pointwise, so `t + b = 9` everywhere. -/
theorem residual_pairMult_add {p q : P} (h : p ≠ q) :
    E.pairMult p q + R.pairMult p q = 9 := by
  have hle : ∀ r ∈ Finset.univ.erase p,
      18 * (E.pairMult p r + R.pairMult p r) ≤
        (E.pairMult p r + R.pairMult p r) ^ 2 + 81 :=
    fun r _ => eighteen_mul_le_sq_add _
  have hsum : (∑ r ∈ Finset.univ.erase p, 18 * (E.pairMult p r + R.pairMult p r)) =
      ∑ r ∈ Finset.univ.erase p, ((E.pairMult p r + R.pairMult p r) ^ 2 + 81) := by
    rw [← Finset.mul_sum, sum_total_pairMult R p, Finset.sum_add_distrib,
      sum_total_pairMult_sq R p, Finset.sum_const, E.card_erase_univ p]
    norm_num [nsmul_eq_mul]
  have hpt := (Finset.sum_eq_sum_iff_of_le hle).mp hsum q
    (Finset.mem_erase.mpr ⟨Ne.symm h, Finset.mem_univ q⟩)
  have hcast : (18 : ℤ) * ((E.pairMult p q : ℤ) + (R.pairMult p q : ℤ)) =
      ((E.pairMult p q : ℤ) + (R.pairMult p q : ℤ)) ^ 2 + 81 := by
    exact_mod_cast hpt
  have hz : ((E.pairMult p q : ℤ) + (R.pairMult p q : ℤ) - 9) ^ 2 = 0 := by
    linear_combination -hcast
  have hnine : (E.pairMult p q : ℤ) + (R.pairMult p q : ℤ) = 9 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
    linarith
  exact_mod_cast hnine

/-- The residual pair multiplicity is `9 − t`. -/
theorem residual_pairMult {p q : P} (h : p ≠ q) :
    R.pairMult p q = 9 - E.pairMult p q := by
  have := residual_pairMult_add R h
  omega

/-- Two distinct points lie on exactly `7` or exactly `8` common residual
blocks. -/
theorem residual_pairMult_cases {p q : P} (h : p ≠ q) :
    R.pairMult p q = 7 ∨ R.pairMult p q = 8 := by
  have hsum := residual_pairMult_add R h
  rcases E.pairMult_cases h with hone | htwo
  · right
    omega
  · left
    omega

end ResidualPairMult

end SRG266.QuasiSymmetric
