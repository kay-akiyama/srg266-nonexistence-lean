/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7ResidualCore
import SRG266.Lattice.Hosts.Model

/-!
# Minuscule weights as coordinate patterns

The `56` minimal vectors of `E₇* ∖ E₇` are represented by the abstract pattern
`SRG266.Lattice.IsE7Minimal` — two coordinates `-3` and six coordinates `1`, or
the negative — and by the indexed family `SRG266.e7Weight4` used by the finite
enumerators.  The `(E₇ ⊕ E₇)⁺` branch moves between the two descriptions.

* `SRG266.Lattice.isE7Minimal_e7Weight4` — every indexed weight has the
  pattern;
* `SRG266.Lattice.exists_e7Weight4_of_isE7Minimal` — every pattern is an
  indexed weight.  The only finite check is that the `28` listed coordinate
  pairs realize every two-element subset of `Fin 8`;
* `SRG266.Lattice.IsE7Minimal.comp_perm` — the pattern is stable under
  reindexing, which is what lets the branch sort the centroid coordinates of
  each `E₇` factor independently;
* `SRG266.Lattice.sumZeroCongruent_dot_dvd_eight` — two vectors of the `4 • E₇*`
  model on eight coordinates pair to a multiple of eight.  This is what makes
  the divisions in `SRG266.e7WeightPairing2` and `SRG266.e7ComponentEvaluation`
  exact, and it is used for the generator/generator, centroid/generator and
  centroid/centroid pairings alike.
-/

namespace SRG266
namespace Lattice

open scoped BigOperators

/-! ## Pairing in the `4 • E₇*` model -/

/-- **Pairings in the eight-coordinate model are multiples of eight.**  Writing
`y = r + 4 a` and `z = s + 4 b`, the sum conditions give `∑ a = -2 r` and
`∑ b = -2 s`, so `⟨y, z⟩ = 8 (2 ⟨a, b⟩ - r s)`. -/
theorem sumZeroCongruent_dot_dvd_eight {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι = 8) {y z : ι → ℤ} {r s : ℤ}
    (hy : ∑ i, y i = 0) (hcy : ∀ i, (4 : ℤ) ∣ (y i - r))
    (hz : ∑ i, z i = 0) (hcz : ∀ i, (4 : ℤ) ∣ (z i - s)) :
    (8 : ℤ) ∣ ∑ i, y i * z i := by
  obtain ⟨a, ha⟩ := exists_shift hcy
  obtain ⟨b, hb⟩ := exists_shift hcz
  have hsa : (8 : ℤ) * r + 4 * ∑ i, a i = 0 := by
    have hstep : ∑ i, y i = (Fintype.card ι : ℤ) * r + 4 * ∑ i, a i := by
      rw [← sum_shift r a]
      exact Finset.sum_congr rfl fun i _ => ha i
    rw [hy, hcard] at hstep
    push_cast at hstep
    omega
  have hsb : (8 : ℤ) * s + 4 * ∑ i, b i = 0 := by
    have hstep : ∑ i, z i = (Fintype.card ι : ℤ) * s + 4 * ∑ i, b i := by
      rw [← sum_shift s b]
      exact Finset.sum_congr rfl fun i _ => hb i
    rw [hz, hcard] at hstep
    push_cast at hstep
    omega
  have hexp : ∀ i, y i * z i =
      r * s + (4 * r) * b i + (4 * s) * a i + 16 * (a i * b i) := by
    intro i
    rw [ha i, hb i]
    ring
  have hsum : ∑ i, y i * z i =
      (Fintype.card ι : ℤ) * (r * s) + (4 * r) * (∑ i, b i) + (4 * s) * (∑ i, a i) +
        16 * ∑ i, a i * b i := by
    rw [Finset.sum_congr rfl fun i _ => hexp i, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hcard] at hsum
  refine ⟨2 * (∑ i, a i * b i) - r * s, ?_⟩
  have hra : (4 : ℤ) * ∑ i, a i = -(8 * r) := by linarith
  have hrb : (4 : ℤ) * ∑ i, b i = -(8 * s) := by linarith
  have hra' : (4 * s) * ∑ i, a i = s * (4 * ∑ i, a i) := by ring
  have hrb' : (4 * r) * ∑ i, b i = r * (4 * ∑ i, b i) := by ring
  rw [hsum, hra', hrb', hra, hrb]
  push_cast
  ring

/-! ## The pattern of a minimal vector -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A minimal vector has coordinate sum zero. -/
theorem IsE7Minimal.sum_eq_zero (hcard : Fintype.card ι = 8) {y : ι → ℤ}
    (hy : IsE7Minimal y) : ∑ i, y i = 0 := by
  obtain ⟨S, hS, hpattern⟩ := hy
  rcases hpattern with hp | hp
  · rw [Finset.sum_congr rfl fun i _ => hp i, sum_ite_mem_const S (-3) 1, hS, hcard]
    norm_num
  · rw [Finset.sum_congr rfl fun i _ => hp i, sum_ite_mem_const S 3 (-1), hS, hcard]
    norm_num

omit [Fintype ι] in
/-- A minimal vector lies in the `4 • E₇*` model: all its coordinates are
congruent modulo four. -/
theorem IsE7Minimal.congruent {y : ι → ℤ} (hy : IsE7Minimal y) :
    ∃ r : ℤ, ∀ i, (4 : ℤ) ∣ (y i - r) := by
  obtain ⟨S, -, hpattern⟩ := hy
  rcases hpattern with hp | hp
  · refine ⟨1, fun i => ?_⟩
    rw [hp i]
    by_cases hi : i ∈ S
    · rw [if_pos hi]
      exact ⟨-1, by norm_num⟩
    · rw [if_neg hi]
      exact ⟨0, by norm_num⟩
  · refine ⟨-1, fun i => ?_⟩
    rw [hp i]
    by_cases hi : i ∈ S
    · rw [if_pos hi]
      exact ⟨1, by norm_num⟩
    · rw [if_neg hi]
      exact ⟨0, by norm_num⟩

omit [Fintype ι] in
/-- **Reindexing preserves the pattern.**  This is how the branch sorts the
coordinates of one `E₇` factor without leaving the shell. -/
theorem IsE7Minimal.comp_perm {y : ι → ℤ} (hy : IsE7Minimal y) (σ : Equiv.Perm ι) :
    IsE7Minimal fun i => y (σ i) := by
  obtain ⟨S, hS, hpattern⟩ := hy
  refine ⟨S.map σ.symm.toEmbedding, by rw [Finset.card_map]; exact hS, ?_⟩
  have hmem : ∀ i, i ∈ S.map σ.symm.toEmbedding ↔ σ i ∈ S := by
    intro i
    rw [Finset.mem_map_equiv, Equiv.symm_symm]
  rcases hpattern with hp | hp
  · refine Or.inl fun i => ?_
    show y (σ i) = _
    rw [hp (σ i)]
    by_cases hi : σ i ∈ S
    · rw [if_pos hi, if_pos ((hmem i).mpr hi)]
    · rw [if_neg hi, if_neg fun hc => hi ((hmem i).mp hc)]
  · refine Or.inr fun i => ?_
    show y (σ i) = _
    rw [hp (σ i)]
    by_cases hi : σ i ∈ S
    · rw [if_pos hi, if_pos ((hmem i).mpr hi)]
    · rw [if_neg hi, if_neg fun hc => hi ((hmem i).mp hc)]

/-! ## The indexed minuscule weights -/

/-- The two coordinates carried by one of the `28` listed pairs. -/
def e7PairSet (t : E7PairIndex) : Finset (Fin 8) :=
  {(e7Pairs.get t).1, (e7Pairs.get t).2}

theorem e7Pairs_get_ne (t : E7PairIndex) : (e7Pairs.get t).1 ≠ (e7Pairs.get t).2 := by
  revert t
  decide

theorem mem_e7PairSet (t : E7PairIndex) (i : Fin 8) :
    i ∈ e7PairSet t ↔ (i = (e7Pairs.get t).1 ∨ i = (e7Pairs.get t).2) := by
  simp [e7PairSet]

theorem e7PairSet_card (t : E7PairIndex) : (e7PairSet t).card = 2 :=
  Finset.card_pair (e7Pairs_get_ne t)

/-- The value of a listed weight, read off its coordinate pair. -/
theorem e7Weight4_apply (w : E7WeightIndex) (i : Fin 8) :
    e7Weight4 w i =
      if i ∈ e7PairSet w.2 then (if w.1 then -3 else 3) else (if w.1 then 1 else -1) := by
  have hdef : e7Weight4 w i =
      if w.1 then -(if i = (e7Pairs.get w.2).1 ∨ i = (e7Pairs.get w.2).2 then (3 : ℤ) else -1)
      else (if i = (e7Pairs.get w.2).1 ∨ i = (e7Pairs.get w.2).2 then (3 : ℤ) else -1) := rfl
  rw [hdef]
  by_cases hi : i ∈ e7PairSet w.2
  · rw [if_pos hi, if_pos ((mem_e7PairSet w.2 i).mp hi)]
  · rw [if_neg hi, if_neg fun hc => hi ((mem_e7PairSet w.2 i).mpr hc)]
    cases w.1 <;> norm_num

/-- Every listed weight has the minimal-vector pattern. -/
theorem isE7Minimal_e7Weight4 (w : E7WeightIndex) : IsE7Minimal (e7Weight4 w) := by
  refine ⟨e7PairSet w.2, e7PairSet_card w.2, ?_⟩
  have hvalue : ∀ i, e7Weight4 w i =
      if i ∈ e7PairSet w.2 then (if w.1 then -3 else 3)
      else (if w.1 then 1 else -1) := e7Weight4_apply w
  cases hw : w.1 with
  | true =>
      refine Or.inl fun i => ?_
      rw [hvalue i, hw]
      by_cases hi : i ∈ e7PairSet w.2 <;> simp [hi]
  | false =>
      refine Or.inr fun i => ?_
      rw [hvalue i, hw]
      by_cases hi : i ∈ e7PairSet w.2 <;> simp [hi]

/-- The `28` listed coordinate pairs realize every two-element subset. -/
theorem exists_e7PairIndex (a b : Fin 8) (hab : a ≠ b) :
    ∃ t : E7PairIndex, e7PairSet t = ({a, b} : Finset (Fin 8)) := by
  have hkey : ∀ a b : Fin 8, a ≠ b → ∃ t : E7PairIndex,
      ((e7Pairs.get t).1 = a ∧ (e7Pairs.get t).2 = b) ∨
        ((e7Pairs.get t).1 = b ∧ (e7Pairs.get t).2 = a) := by
    decide
  obtain ⟨t, ht⟩ := hkey a b hab
  refine ⟨t, ?_⟩
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [e7PairSet, h1, h2]
  · rw [e7PairSet, h1, h2, Finset.pair_comm]

/-- **Every minimal pattern is a listed weight.**  This is the direction the
branch uses: the norm-three shell theorem of `(E₇ ⊕ E₇)⁺` delivers patterns,
while `SRG266.E7CentroidShellGramRealization` consumes indices. -/
theorem exists_e7Weight4_of_isE7Minimal {y : Fin 8 → ℤ} (hy : IsE7Minimal y) :
    ∃ w : E7WeightIndex, ∀ i, y i = e7Weight4 w i := by
  obtain ⟨S, hS, hpattern⟩ := hy
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
  obtain ⟨t, ht⟩ := exists_e7PairIndex a b hab
  have hvalue : ∀ i, e7Weight4 (true, t) i = if i ∈ e7PairSet t then -3 else 1 := by
    intro i
    rw [e7Weight4_apply]
    by_cases hi : i ∈ e7PairSet t <;> simp [hi]
  have hvalue' : ∀ i, e7Weight4 (false, t) i = if i ∈ e7PairSet t then 3 else -1 := by
    intro i
    rw [e7Weight4_apply]
    by_cases hi : i ∈ e7PairSet t <;> simp [hi]
  rcases hpattern with hp | hp
  · exact ⟨(true, t), fun i => by rw [hp i, hvalue i, ht]⟩
  · exact ⟨(false, t), fun i => by rw [hp i, hvalue' i, ht]⟩

/-! ## Exactness of the shell divisions -/

/-- Two listed weights pair to a multiple of eight. -/
theorem dvd_eight_dot_e7Weight4 (u v : E7WeightIndex) :
    (8 : ℤ) ∣ ∑ i, e7Weight4 u i * e7Weight4 v i := by
  obtain ⟨r, hr⟩ := (isE7Minimal_e7Weight4 u).congruent
  obtain ⟨s, hs⟩ := (isE7Minimal_e7Weight4 v).congruent
  exact sumZeroCongruent_dot_dvd_eight (by simp)
    ((isE7Minimal_e7Weight4 u).sum_eq_zero (by simp)) hr
    ((isE7Minimal_e7Weight4 v).sum_eq_zero (by simp)) hs

/-- The doubled weight pairing, cleared of its division. -/
theorem e7WeightPairing2_mul_eight (u v : E7WeightIndex) :
    8 * e7WeightPairing2 u v = integerDot (e7Weight4 u) (e7Weight4 v) := by
  obtain ⟨k, hk⟩ := dvd_eight_dot_e7Weight4 u v
  have hdot : integerDot (e7Weight4 u) (e7Weight4 v) = 8 * k := hk
  rw [e7WeightPairing2, hdot, Int.mul_ediv_cancel_left _ (by norm_num)]

/-- **The shell inner product is the model pairing.**  If two paired weights
have the pairing values of two lattice vectors, scaled by `16`, the shell inner
product of `SRG266.e7ShellInner` is the lattice pairing itself. -/
theorem e7ShellInner_of_dot (u v : E7ShellIndex) (m : ℤ)
    (hdot : (∑ i, e7Weight4 u.1 i * e7Weight4 v.1 i) +
      ∑ i, e7Weight4 u.2 i * e7Weight4 v.2 i = 16 * m) :
    e7ShellInner u v = m := by
  have hleft := e7WeightPairing2_mul_eight u.1 v.1
  have hright := e7WeightPairing2_mul_eight u.2 v.2
  unfold integerDot at hleft hright
  have hsum : e7WeightPairing2 u.1 v.1 + e7WeightPairing2 u.2 v.2 = 2 * m := by omega
  rw [e7ShellInner, hsum, Int.mul_ediv_cancel_left _ (by norm_num)]

end Lattice
end SRG266
