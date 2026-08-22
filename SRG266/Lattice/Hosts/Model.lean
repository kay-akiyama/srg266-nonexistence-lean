/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Coordinate models for the standard rank-15 hosts

Each of the five standard hosts is presented by *scaled* integer coordinates:
a lattice vector `x` is recorded
as the integer vector `scale • x`, and the pairing is
`⟨x, y⟩ = (scale • x) ⬝ (scale • y) / scale ^ 2`.  In those coordinates each
model is cut out by a congruence, and — this is the point of the design — every
norm-three shell is then determined by *arithmetic*, with no search:

* `SRG266.Lattice.SumZeroCongruent` is `4 • A₁₅⁺` in dimension 16 and `4 • E₇*`
  in dimension 8: sum zero, all entries congruent modulo `4`.  Writing
  `y i = r + 4 * t i` turns the two constraints into
  `∑ t = -(card / 4) * r` and `∑ y ^ 2 = 16 * ∑ t ^ 2 - card * r ^ 2`
  (`sum_shift`, `sum_shift_sq`), after which the shell is read off from
  `∑ t ^ 2 = -∑ t`, whose solutions are exactly the vectors with entries `0` and `-1`
  (`eq_zero_or_neg_one_of_sum_sq_eq_neg_sum`).
* `SRG266.Lattice.SameParitySumFour` is `2 • D_n⁺`: all entries of one parity,
  entry sum divisible by `4`.  Its two branches are separated by
  `sum_sq_dvd_eight_of_even` and `sum_sq_sub_card_dvd_eight`, which say that
  `D_n` is even and that a half-integral vector has square sum `≡ n (mod 8)`.

Nothing here mentions a Gram matrix; the per-host files
`SRG266/Lattice/Hosts/*.lean` connect these models to the generated data of
`SRG266/Certificates/Rank15HostGramData.lean`.
-/

namespace SRG266
namespace Lattice

open Finset

section Arithmetic

variable {ι : Type*} [Fintype ι]

/-- For integers, the absolute value is at most the square. -/
theorem abs_le_sq (a : ℤ) : |a| ≤ a ^ 2 := by
  rcases eq_or_ne a 0 with h | h
  · simp [h]
  · have h1 : 1 ≤ |a| := Int.one_le_abs h
    nlinarith [sq_abs a]

/-- The square sum dominates the absolute value of the sum. -/
theorem abs_sum_le_sum_sq (t : ι → ℤ) : |∑ i, t i| ≤ ∑ i, (t i) ^ 2 :=
  (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => abs_le_sq (t i))

/-- Square sums and sums agree modulo `2`. -/
theorem two_dvd_sum_sq_sub_sum (t : ι → ℤ) :
    (2 : ℤ) ∣ (∑ i, (t i) ^ 2 - ∑ i, t i) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun i _ => ?_
  have : (t i) ^ 2 - t i = t i * (t i - 1) := by ring
  rw [this]
  exact Int.even_mul_pred_self (t i) |>.two_dvd

/-- An odd square is `1` modulo `8`. -/
theorem eight_dvd_sq_sub_one {a : ℤ} (ha : ¬ (2 : ℤ) ∣ a) : (8 : ℤ) ∣ (a ^ 2 - 1) := by
  obtain ⟨k, hk⟩ : ∃ k, a = 2 * k + 1 := by
    rcases Int.even_or_odd a with h | h
    · exact absurd h.two_dvd ha
    · obtain ⟨k, hk⟩ := h
      exact ⟨k, hk⟩
  subst hk
  have hstep : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by ring
  obtain ⟨j, hj⟩ := (Int.even_mul_succ_self k).two_dvd
  exact ⟨j, by rw [hstep, hj]; ring⟩

/-- A vector with `∑ t = -m` and `∑ t ^ 2 = m` has all entries in `{0, -1}`. -/
theorem eq_zero_or_neg_one_of_sum_sq_eq_neg_sum (t : ι → ℤ) (m : ℤ)
    (hsum : ∑ i, t i = -m) (hsq : ∑ i, (t i) ^ 2 = m) (i : ι) :
    t i = 0 ∨ t i = -1 := by
  have hzero : ∑ j, ((t j) ^ 2 + t j) = 0 := by
    rw [Finset.sum_add_distrib, hsum, hsq]
    ring
  have hnonneg : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ (t j) ^ 2 + t j := by
    intro j _
    rcases le_or_gt 0 (t j) with h | h
    · positivity
    · have h1 : t j ≤ -1 := by omega
      nlinarith
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero i (Finset.mem_univ i)
  have hprod : t i * (t i + 1) = 0 := by nlinarith [hterm]
  rcases mul_eq_zero.mp hprod with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

/-- A vector with entries `0` and `-1` sums to minus the size of its `-1`
support. -/
theorem sum_eq_neg_card_filter (t : ι → ℤ) (h : ∀ i, t i = 0 ∨ t i = -1) :
    ∑ i, t i = -((Finset.univ.filter fun i => t i = -1).card : ℤ) := by
  have hpoint : ∀ i, t i = if t i = -1 then (-1 : ℤ) else 0 := by
    intro i
    rcases h i with h0 | h0 <;> simp [h0]
  calc ∑ i, t i = ∑ i, if t i = -1 then (-1 : ℤ) else 0 :=
        Finset.sum_congr rfl fun i _ => hpoint i
    _ = ∑ _i ∈ Finset.univ.filter fun i => t i = -1, (-1 : ℤ) :=
        (Finset.sum_filter _ _).symm
    _ = -((Finset.univ.filter fun i => t i = -1).card : ℤ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- Entries of a `c`-divisible vector of square sum below `4 * c ^ 2` lie in
`{-c, 0, c}`. -/
theorem eq_zero_or_abs_scale_of_sum_sq_lt {c : ℤ} (_hc : 0 < c) (v : ι → ℤ) (k : ℤ)
    (hk : k < 4 * c ^ 2) (hdvd : ∀ i, c ∣ v i) (h : ∑ i, (v i) ^ 2 = k) (i : ι) :
    v i = 0 ∨ v i = c ∨ v i = -c := by
  have hle : (v i) ^ 2 ≤ k := by
    rw [← h]
    exact Finset.single_le_sum (f := fun j => (v j) ^ 2)
      (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  obtain ⟨u, hu⟩ := hdvd i
  have hlt : (c * u) ^ 2 < 4 * c ^ 2 := by
    rw [← hu]
    exact lt_of_le_of_lt hle hk
  have hu2 : u ^ 2 < 4 := by nlinarith [sq_nonneg u, sq_nonneg c]
  have hlow : -2 < u := by nlinarith
  have hhigh : u < 2 := by nlinarith
  have : u = 0 ∨ u = 1 ∨ u = -1 := by omega
  rcases this with h0 | h1 | h2
  · exact Or.inl (by rw [hu, h0, mul_zero])
  · exact Or.inr (Or.inl (by rw [hu, h1, mul_one]))
  · exact Or.inr (Or.inr (by rw [hu, h2]; ring))

/-- Entries of a vector of square sum below `4` lie in `{-1, 0, 1}`. -/
theorem eq_zero_or_abs_one_of_sum_sq_lt_four (v : ι → ℤ) (k : ℤ) (hk : k < 4)
    (h : ∑ i, (v i) ^ 2 = k) (i : ι) : v i = 0 ∨ v i = 1 ∨ v i = -1 :=
  eq_zero_or_abs_scale_of_sum_sq_lt one_pos v k (by simpa using hk) (fun _ => one_dvd _) h i

/-- For a `0/±c` vector the square sum counts the support with weight
`c ^ 2`. -/
theorem sum_sq_eq_sq_mul_card_support {c : ℤ} (v : ι → ℤ)
    (h : ∀ i, v i = 0 ∨ v i = c ∨ v i = -c) :
    ∑ i, (v i) ^ 2 = c ^ 2 * ((Finset.univ.filter fun i => v i ≠ 0).card : ℤ) := by
  have hpoint : ∀ i, (v i) ^ 2 = if v i ≠ 0 then c ^ 2 else 0 := by
    intro i
    rcases h i with h0 | h0 | h0
    · simp [h0]
    · by_cases hc : c = 0
      · simp [h0, hc]
      · simp [h0, hc]
    · by_cases hc : c = 0
      · simp [h0, hc]
      · have hne : v i ≠ 0 := by
          rw [h0]
          simpa using hc
        rw [if_pos hne, h0]
        ring
  calc ∑ i, (v i) ^ 2 = ∑ i, if v i ≠ 0 then c ^ 2 else 0 :=
        Finset.sum_congr rfl fun i _ => hpoint i
    _ = ∑ _i ∈ Finset.univ.filter fun i => v i ≠ 0, c ^ 2 :=
        (Finset.sum_filter _ _).symm
    _ = c ^ 2 * ((Finset.univ.filter fun i => v i ≠ 0).card : ℤ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- A vanishing square sum means a vanishing vector. -/
theorem eq_zero_of_sum_sq_eq_zero (v : ι → ℤ) (h : ∑ i, (v i) ^ 2 = 0) (i : ι) : v i = 0 := by
  have hnn : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ (v j) ^ 2 := fun j _ => sq_nonneg (v j)
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h i (Finset.mem_univ i)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

/-- A vector with no zero entry has square sum at least the dimension. -/
theorem card_le_sum_sq (v : ι → ℤ) (h : ∀ i, v i ≠ 0) :
    (Fintype.card ι : ℤ) ≤ ∑ i, (v i) ^ 2 := by
  have hone : ∀ i ∈ (Finset.univ : Finset ι), (1 : ℤ) ≤ (v i) ^ 2 := by
    intro i _
    have := Int.one_le_abs (h i)
    nlinarith [sq_abs (v i)]
  calc (Fintype.card ι : ℤ) = ∑ _i : ι, (1 : ℤ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    _ ≤ ∑ i, (v i) ^ 2 := Finset.sum_le_sum hone

/-- A two-valued sum splits into the two constant blocks. -/
theorem sum_ite_mem_const [DecidableEq ι] (S : Finset ι) (a b : ℤ) :
    ∑ j, (if j ∈ S then a else b) =
      (S.card : ℤ) * a + ((Fintype.card ι - S.card : ℕ) : ℤ) * b := by
  have hcompl : (Finset.univ.filter fun j => j ∉ S) = Sᶜ := by
    ext j
    simp
  rw [Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter, hcompl,
    Finset.sum_const, Finset.sum_const, Finset.card_compl, nsmul_eq_mul, nsmul_eq_mul]

/-- For a `0/±1` vector the square sum is the size of the support. -/
theorem sum_sq_eq_card_support (v : ι → ℤ) (h : ∀ i, v i = 0 ∨ v i = 1 ∨ v i = -1) :
    ∑ i, (v i) ^ 2 = ((Finset.univ.filter fun i => v i ≠ 0).card : ℤ) := by
  have hpoint : ∀ i, (v i) ^ 2 = if v i ≠ 0 then (1 : ℤ) else 0 := by
    intro i
    rcases h i with h0 | h0 | h0 <;> simp [h0]
  calc ∑ i, (v i) ^ 2 = ∑ i, if v i ≠ 0 then (1 : ℤ) else 0 :=
        Finset.sum_congr rfl fun i _ => hpoint i
    _ = ∑ _i ∈ Finset.univ.filter fun i => v i ≠ 0, (1 : ℤ) :=
        (Finset.sum_filter _ _).symm
    _ = ((Finset.univ.filter fun i => v i ≠ 0).card : ℤ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]

end Arithmetic

section Shift

variable {ι : Type*} [Fintype ι]

/-- Sum of a vector written as `r + 4 t`. -/
theorem sum_shift (r : ℤ) (t : ι → ℤ) :
    ∑ i, (r + 4 * t i) = (Fintype.card ι : ℤ) * r + 4 * ∑ i, t i := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum]

/-- Square sum of a vector written as `r + 4 t`. -/
theorem sum_shift_sq (r : ℤ) (t : ι → ℤ) :
    ∑ i, (r + 4 * t i) ^ 2 =
      (Fintype.card ι : ℤ) * r ^ 2 + 8 * r * (∑ i, t i) + 16 * ∑ i, (t i) ^ 2 := by
  have hpoint : ∀ i, (r + 4 * t i) ^ 2 = r ^ 2 + (8 * r) * t i + 16 * (t i) ^ 2 :=
    fun i => by ring
  calc ∑ i, (r + 4 * t i) ^ 2
      = ∑ i, (r ^ 2 + (8 * r) * t i + 16 * (t i) ^ 2) :=
        Finset.sum_congr rfl fun i _ => hpoint i
    _ = (Fintype.card ι : ℤ) * r ^ 2 + 8 * r * (∑ i, t i) + 16 * ∑ i, (t i) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum]

end Shift

section SumZeroCongruent

variable {ι : Type*} [Fintype ι]

/-- **The sum-zero mod-4 model.**  In dimension 16 this is `4 • A₁₅⁺`; in
dimension 8 it is `4 • E₇*`, whose two even residues cut out `4 • E₇`. -/
def SumZeroCongruent (y : ι → ℤ) : Prop :=
  (∑ i, y i = 0) ∧ ∃ r : ℤ, ∀ i, (4 : ℤ) ∣ (y i - r)

/-- The sum-zero mod-4 model is a `ℤ`-submodule of the ambient coordinates. -/
def sumZeroCongruentSubmodule (ι : Type*) [Fintype ι] : Submodule ℤ (ι → ℤ) where
  carrier := {y | (∑ i, y i = 0) ∧ ∃ r : ℤ, ∀ i, (4 : ℤ) ∣ (y i - r)}
  zero_mem' := ⟨by simp, 0, by simp⟩
  add_mem' := by
    rintro y z ⟨hy, r, hr⟩ ⟨hz, s, hs⟩
    refine ⟨?_, r + s, fun i => ?_⟩
    · simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, hy, hz, add_zero]
    · have hstep : (y + z) i - (r + s) = (y i - r) + (z i - s) := by
        simp only [Pi.add_apply]
        ring
      rw [hstep]
      exact dvd_add (hr i) (hs i)
  smul_mem' := by
    rintro c y ⟨hy, r, hr⟩
    refine ⟨?_, c * r, fun i => ?_⟩
    · have hstep : ∑ i, (c • y) i = c * ∑ i, y i := by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [hstep, hy, mul_zero]
    · have hstep : (c • y) i - c * r = c * (y i - r) := by
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [hstep]
      exact Dvd.dvd.mul_left (hr i) c

@[simp] theorem mem_sumZeroCongruentSubmodule {y : ι → ℤ} :
    y ∈ sumZeroCongruentSubmodule ι ↔ SumZeroCongruent y := Iff.rfl

/-- The residue of a model vector may be normalised into `{0, 1, 2, 3}`. -/
theorem SumZeroCongruent.residue_normalised {y : ι → ℤ} (hy : SumZeroCongruent y) :
    ∃ r : ℤ, (r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) ∧ ∀ i, (4 : ℤ) ∣ (y i - r) := by
  obtain ⟨-, r, hr⟩ := hy
  refine ⟨r % 4, by omega, fun i => ?_⟩
  have hmod : (4 : ℤ) ∣ (r - r % 4) := ⟨r / 4, by omega⟩
  have hstep : y i - r % 4 = (y i - r) + (r - r % 4) := by ring
  rw [hstep]
  exact dvd_add (hr i) hmod

omit [Fintype ι] in
/-- The shift of a model vector by its residue. -/
theorem exists_shift {y : ι → ℤ} {r : ℤ} (hcong : ∀ i, (4 : ℤ) ∣ (y i - r)) :
    ∃ t : ι → ℤ, ∀ i, y i = r + 4 * t i := by
  refine ⟨fun i => (y i - r) / 4, fun i => ?_⟩
  have hcancel := Int.mul_ediv_cancel' (hcong i)
  show y i = r + 4 * ((y i - r) / 4)
  omega

/-- **Odd residue: the shell bound and its equality case.**  In the sum-zero
mod-4 model on `4 * m` coordinates, a vector with odd residue has square sum at
least `12 * m`, and the vectors attaining the bound are exactly those equal to
`-3` on a subset of size `m` and `1` off it, or `3` on such a subset and `-1`
off it. -/
theorem sumZeroCongruent_odd_bound {m : ℕ} (hcard : Fintype.card ι = 4 * m) {r : ℤ}
    (hr : r = 1 ∨ r = 3) {y : ι → ℤ} (hsum : ∑ i, y i = 0)
    (hcong : ∀ i, (4 : ℤ) ∣ (y i - r)) :
    (12 * m : ℤ) ≤ ∑ i, (y i) ^ 2 := by
  obtain ⟨t, ht⟩ := exists_shift hcong
  have hy : ∀ i, y i = r + 4 * t i := ht
  have hsum' : (Fintype.card ι : ℤ) * r + 4 * ∑ i, t i = 0 := by
    rw [← sum_shift r t, ← hsum]
    exact Finset.sum_congr rfl fun i _ => (hy i).symm
  have hsq : ∑ i, (y i) ^ 2 =
      (Fintype.card ι : ℤ) * r ^ 2 + 8 * r * (∑ i, t i) + 16 * ∑ i, (t i) ^ 2 := by
    rw [← sum_shift_sq r t]
    exact Finset.sum_congr rfl fun i _ => by rw [hy i]
  rw [hcard] at hsum' hsq
  push_cast at hsum' hsq
  have hst : ∑ i, t i = -(m * r) := by linarith
  have habs := abs_sum_le_sum_sq t
  rw [hst] at habs
  have hmr : |(-(m * r) : ℤ)| = m * r := by
    rcases hr with h | h <;> subst h <;> simp [abs_of_nonneg]
  rw [hmr] at habs
  rcases hr with h | h <;> subst h <;> nlinarith [habs, hsq, hst]

/-- The equality case of `sumZeroCongruent_odd_bound`. -/
theorem sumZeroCongruent_odd_shell [DecidableEq ι] {m : ℕ}
    (hcard : Fintype.card ι = 4 * m) {r : ℤ}
    (hr : r = 1 ∨ r = 3) {y : ι → ℤ} (hsum : ∑ i, y i = 0)
    (hcong : ∀ i, (4 : ℤ) ∣ (y i - r)) (hnorm : ∑ i, (y i) ^ 2 = 12 * m) :
    ∃ S : Finset ι, S.card = m ∧
      ((∀ i, y i = if i ∈ S then -3 else 1) ∨ (∀ i, y i = if i ∈ S then 3 else -1)) := by
  classical
  obtain ⟨t, ht⟩ := exists_shift hcong
  have hy : ∀ i, y i = r + 4 * t i := ht
  have hsum' : (Fintype.card ι : ℤ) * r + 4 * ∑ i, t i = 0 := by
    rw [← sum_shift r t, ← hsum]
    exact Finset.sum_congr rfl fun i _ => (hy i).symm
  have hsq : ∑ i, (y i) ^ 2 =
      (Fintype.card ι : ℤ) * r ^ 2 + 8 * r * (∑ i, t i) + 16 * ∑ i, (t i) ^ 2 := by
    rw [← sum_shift_sq r t]
    exact Finset.sum_congr rfl fun i _ => by rw [hy i]
  rw [hcard] at hsum' hsq
  push_cast at hsum' hsq
  have hst : ∑ i, t i = -(m * r) := by linarith
  have hsqt : ∑ i, (t i) ^ 2 = m * r := by
    rcases hr with h | h <;> subst h <;> nlinarith [hnorm, hsq, hst]
  have hcases : ∀ i, t i = 0 ∨ t i = -1 :=
    fun i => eq_zero_or_neg_one_of_sum_sq_eq_neg_sum t (m * r) hst hsqt i
  have hcount := sum_eq_neg_card_filter t hcases
  rw [hst] at hcount
  have hcard' : ((Finset.univ.filter fun i => t i = -1).card : ℤ) = m * r := by
    omega
  rcases hr with h | h
  · subst h
    have hone : ((Finset.univ.filter fun i => t i = -1).card : ℤ) = m := by
      rw [hcard']
      ring
    refine ⟨Finset.univ.filter fun i => t i = -1, by exact_mod_cast hone, Or.inl fun i => ?_⟩
    · by_cases hi : t i = -1
      · simp [hy i, hi, Finset.mem_filter]
      · rcases hcases i with h0 | h1
        · simp [hy i, h0, Finset.mem_filter]
        · exact absurd h1 hi
  · subst h
    have hfilter : ((Finset.univ.filter fun i => t i = 0).card : ℤ) = m := by
      have hsplit : (Finset.univ.filter fun i => t i = 0).card +
          (Finset.univ.filter fun i => t i = -1).card = Fintype.card ι := by
        rw [← Finset.card_union_of_disjoint]
        · congr 1
          apply Finset.eq_univ_of_forall
          intro i
          rcases hcases i with h0 | h1
          · exact Finset.mem_union_left _ (by simp [h0])
          · exact Finset.mem_union_right _ (by simp [h1])
        · refine Finset.disjoint_filter.mpr fun i _ h0 h1 => ?_
          rw [h0] at h1
          exact absurd h1 (by norm_num)
      have : ((Finset.univ.filter fun i => t i = 0).card : ℤ) +
          ((Finset.univ.filter fun i => t i = -1).card : ℤ) = (Fintype.card ι : ℤ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hsplit
      rw [hcard] at this
      push_cast at this
      omega
    refine ⟨Finset.univ.filter fun i => t i = 0, by exact_mod_cast hfilter,
      Or.inr fun i => ?_⟩
    by_cases hi : t i = 0
    · simp [hy i, hi, Finset.mem_filter]
    · rcases hcases i with h0 | h1
      · exact absurd h0 hi
      · simp [hy i, h1, Finset.mem_filter]

/-- **Odd residue: the square sum modulo `32`.**  On eight coordinates — the
`4 • E₇*` model — a sum-zero vector with odd residue has square sum congruent to
`24` modulo `32`, that is norm in `3/2 + 2ℤ`.  Two such norms therefore never
add up to an even integer. -/
theorem sumZeroCongruent_odd_mod_thirtyTwo (hcard : Fintype.card ι = 8) {r : ℤ}
    (hr : r = 1 ∨ r = 3) {y : ι → ℤ} (hsum : ∑ i, y i = 0)
    (hcong : ∀ i, (4 : ℤ) ∣ (y i - r)) :
    (32 : ℤ) ∣ (∑ i, (y i) ^ 2 - 24) := by
  obtain ⟨t, ht⟩ := exists_shift hcong
  have hy : ∀ i, y i = r + 4 * t i := ht
  have hsum' : (Fintype.card ι : ℤ) * r + 4 * ∑ i, t i = 0 := by
    rw [← sum_shift r t, ← hsum]
    exact Finset.sum_congr rfl fun i _ => (hy i).symm
  have hsq : ∑ i, (y i) ^ 2 =
      (Fintype.card ι : ℤ) * r ^ 2 + 8 * r * (∑ i, t i) + 16 * ∑ i, (t i) ^ 2 := by
    rw [← sum_shift_sq r t]
    exact Finset.sum_congr rfl fun i _ => by rw [hy i]
  rw [hcard] at hsum' hsq
  push_cast at hsum' hsq
  obtain ⟨u, hu⟩ := two_dvd_sum_sq_sub_sum t
  rcases hr with h | h <;> subst h
  · exact ⟨u - 2, by omega⟩
  · exact ⟨u - 6, by omega⟩

/-- **Norm and residue have the same parity.**  On sixteen coordinates — the
`4 • A₁₅⁺` model — the norm `∑ y ^ 2 / 16` of a model vector is congruent to its
residue modulo `2`.  With norm `300` this gives `r ∈ {0, 2}`. -/
theorem sumZeroCongruent_norm_residue_parity (hcard : Fintype.card ι = 16) {r : ℤ}
    {y : ι → ℤ} (hsum : ∑ i, y i = 0) (hcong : ∀ i, (4 : ℤ) ∣ (y i - r)) (N : ℤ)
    (hnorm : ∑ i, (y i) ^ 2 = 16 * N) : (2 : ℤ) ∣ (N - r) := by
  obtain ⟨t, ht⟩ := exists_shift hcong
  have hy : ∀ i, y i = r + 4 * t i := ht
  have hsum' : (Fintype.card ι : ℤ) * r + 4 * ∑ i, t i = 0 := by
    rw [← sum_shift r t, ← hsum]
    exact Finset.sum_congr rfl fun i _ => (hy i).symm
  have hsq : ∑ i, (y i) ^ 2 =
      (Fintype.card ι : ℤ) * r ^ 2 + 8 * r * (∑ i, t i) + 16 * ∑ i, (t i) ^ 2 := by
    rw [← sum_shift_sq r t]
    exact Finset.sum_congr rfl fun i _ => by rw [hy i]
  rw [hcard] at hsum' hsq
  push_cast at hsum' hsq
  obtain ⟨u, hu⟩ := two_dvd_sum_sq_sub_sum t
  obtain ⟨w, hw⟩ := (Int.even_mul_succ_self r).two_dvd
  refine ⟨u - 2 * r - w, ?_⟩
  have hst : ∑ i, t i = -(4 * r) := by linarith
  have hsqt : ∑ i, (t i) ^ 2 = 2 * u + ∑ i, t i := by omega
  rw [hnorm, hsqt, hst] at hsq
  nlinarith [hsq, hw]

/-- **Even residue.**  In the sum-zero mod-4 model on `4 * m` coordinates with
`m` even, a vector with even residue has square sum divisible by `32`; in
particular it can be neither `48` nor a sum of two square sums equal to `48`. -/
theorem sumZeroCongruent_even_dvd {m : ℕ} (hcard : Fintype.card ι = 4 * m)
    (hm : (2 : ℤ) ∣ (m : ℤ)) {r : ℤ} (hr : (2 : ℤ) ∣ r) {y : ι → ℤ}
    (hsum : ∑ i, y i = 0) (hcong : ∀ i, (4 : ℤ) ∣ (y i - r)) :
    (32 : ℤ) ∣ ∑ i, (y i) ^ 2 := by
  obtain ⟨t, ht⟩ := exists_shift hcong
  have hy : ∀ i, y i = r + 4 * t i := ht
  have hsum' : (Fintype.card ι : ℤ) * r + 4 * ∑ i, t i = 0 := by
    rw [← sum_shift r t, ← hsum]
    exact Finset.sum_congr rfl fun i _ => (hy i).symm
  have hsq : ∑ i, (y i) ^ 2 =
      (Fintype.card ι : ℤ) * r ^ 2 + 8 * r * (∑ i, t i) + 16 * ∑ i, (t i) ^ 2 := by
    rw [← sum_shift_sq r t]
    exact Finset.sum_congr rfl fun i _ => by rw [hy i]
  rw [hcard] at hsum' hsq
  push_cast at hsum' hsq
  obtain ⟨s, hs⟩ := hr
  obtain ⟨m', hm'⟩ := hm
  have hst : ∑ i, t i = -(m * r) := by linarith
  obtain ⟨u, hu⟩ := two_dvd_sum_sq_sub_sum t
  have hsqt : ∑ i, (t i) ^ 2 = 2 * u + ∑ i, t i := by omega
  rw [hsqt, hst, hs, hm'] at hsq
  refine ⟨u - m' * s ^ 2 - 2 * m' * s, ?_⟩
  rw [hsq]
  ring

end SumZeroCongruent

section Blocks

variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]

/-- Coordinates divisible by `c`: the model of a `ℤ`-summand presented with
scale `c`. -/
def scaleSubmodule (c : ℤ) (ι : Type*) : Submodule ℤ (ι → ℤ) where
  carrier := {v | ∀ i, c ∣ v i}
  zero_mem' := fun _ => dvd_zero _
  add_mem' := fun hv hw i => dvd_add (hv i) (hw i)
  smul_mem' := fun a _ hv i => Dvd.dvd.mul_left (hv i) a

omit [Fintype ι] in
@[simp] theorem mem_scaleSubmodule {c : ℤ} {v : ι → ℤ} :
    v ∈ scaleSubmodule c ι ↔ ∀ i, c ∣ v i := Iff.rfl

/-- **The glued pair model.**  Both blocks lie in the sum-zero mod-4 model and
their residues have the same parity: this is `4 • (E₇ ⊕ E₇)⁺`, whose glue coset
pairs a nontrivial class of `E₇*/E₇` with a nontrivial class. -/
def gluedPairSubmodule (ι κ : Type*) [Fintype ι] [Fintype κ] :
    Submodule ℤ ((ι ⊕ κ) → ℤ) where
  carrier := {y | (∑ i, y (Sum.inl i) = 0) ∧ (∑ i, y (Sum.inr i) = 0) ∧
    ∃ r s : ℤ, (∀ i, (4 : ℤ) ∣ (y (Sum.inl i) - r)) ∧
      (∀ i, (4 : ℤ) ∣ (y (Sum.inr i) - s)) ∧ (2 : ℤ) ∣ (r - s)}
  zero_mem' := ⟨by simp, by simp, 0, 0, by simp, by simp, by simp⟩
  add_mem' := by
    rintro y z ⟨hyl, hyr, r, s, hrl, hrr, hrs⟩ ⟨hzl, hzr, p, q, hpl, hpr, hpq⟩
    refine ⟨?_, ?_, r + p, s + q, fun i => ?_, fun i => ?_, ?_⟩
    · simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, hyl, hzl, add_zero]
    · simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, hyr, hzr, add_zero]
    · have hstep : (y + z) (Sum.inl i) - (r + p) =
          (y (Sum.inl i) - r) + (z (Sum.inl i) - p) := by
        simp only [Pi.add_apply]
        ring
      rw [hstep]
      exact dvd_add (hrl i) (hpl i)
    · have hstep : (y + z) (Sum.inr i) - (s + q) =
          (y (Sum.inr i) - s) + (z (Sum.inr i) - q) := by
        simp only [Pi.add_apply]
        ring
      rw [hstep]
      exact dvd_add (hrr i) (hpr i)
    · have hstep : r + p - (s + q) = (r - s) + (p - q) := by ring
      rw [hstep]
      exact dvd_add hrs hpq
  smul_mem' := by
    rintro c y ⟨hyl, hyr, r, s, hrl, hrr, hrs⟩
    refine ⟨?_, ?_, c * r, c * s, fun i => ?_, fun i => ?_, ?_⟩
    · have hstep : ∑ i, (c • y) (Sum.inl i) = c * ∑ i, y (Sum.inl i) := by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [hstep, hyl, mul_zero]
    · have hstep : ∑ i, (c • y) (Sum.inr i) = c * ∑ i, y (Sum.inr i) := by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [hstep, hyr, mul_zero]
    · have hstep : (c • y) (Sum.inl i) - c * r = c * (y (Sum.inl i) - r) := by
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [hstep]
      exact Dvd.dvd.mul_left (hrl i) c
    · have hstep : (c • y) (Sum.inr i) - c * s = c * (y (Sum.inr i) - s) := by
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [hstep]
      exact Dvd.dvd.mul_left (hrr i) c
    · have hstep : c * r - c * s = c * (r - s) := by ring
      rw [hstep]
      exact Dvd.dvd.mul_left hrs c

@[simp] theorem mem_gluedPairSubmodule {y : (ι ⊕ κ) → ℤ} :
    y ∈ gluedPairSubmodule ι κ ↔
      (∑ i, y (Sum.inl i) = 0) ∧ (∑ i, y (Sum.inr i) = 0) ∧
        ∃ r s : ℤ, (∀ i, (4 : ℤ) ∣ (y (Sum.inl i) - r)) ∧
          (∀ i, (4 : ℤ) ∣ (y (Sum.inr i) - s)) ∧ (2 : ℤ) ∣ (r - s) := Iff.rfl

/-- Residues of a glued pair may be normalised into `{0, 1, 2, 3}` while
keeping their parities matched. -/
theorem gluedPair_residues_normalised {y : (ι ⊕ κ) → ℤ} (hy : y ∈ gluedPairSubmodule ι κ) :
    ∃ r s : ℤ, (r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) ∧ (s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3) ∧
      (∀ i, (4 : ℤ) ∣ (y (Sum.inl i) - r)) ∧ (∀ i, (4 : ℤ) ∣ (y (Sum.inr i) - s)) ∧
      (2 : ℤ) ∣ (r - s) := by
  obtain ⟨-, -, r, s, hrl, hrr, hrs⟩ := hy
  refine ⟨r % 4, s % 4, by omega, by omega, fun i => ?_, fun i => ?_, ?_⟩
  · have hmod : (4 : ℤ) ∣ (r - r % 4) := ⟨r / 4, by omega⟩
    have hstep : y (Sum.inl i) - r % 4 = (y (Sum.inl i) - r) + (r - r % 4) := by ring
    rw [hstep]
    exact dvd_add (hrl i) hmod
  · have hmod : (4 : ℤ) ∣ (s - s % 4) := ⟨s / 4, by omega⟩
    have hstep : y (Sum.inr i) - s % 4 = (y (Sum.inr i) - s) + (s - s % 4) := by ring
    rw [hstep]
    exact dvd_add (hrr i) hmod
  · obtain ⟨k, hk⟩ := hrs
    omega

/-- Minimal vectors of `E₇* ∖ E₇` in 4-scaled coordinates: two coordinates
`-3` and six coordinates `1`, or the negative of such a vector. There are
`2 * Nat.choose 8 2 = 56` of them. -/
def IsE7Minimal [DecidableEq ι] (y : ι → ℤ) : Prop :=
  ∃ S : Finset ι, S.card = 2 ∧
    ((∀ i, y i = if i ∈ S then -3 else 1) ∨ (∀ i, y i = if i ∈ S then 3 else -1))

/-- A minimal vector has square sum `24`, that is norm `3 / 2`. -/
theorem IsE7Minimal.sum_sq [DecidableEq ι] (hcard : Fintype.card ι = 8) {y : ι → ℤ}
    (hy : IsE7Minimal y) : ∑ i, (y i) ^ 2 = 24 := by
  obtain ⟨S, hS, hpattern⟩ := hy
  have hvalue : ∀ i, (y i) ^ 2 = if i ∈ S then (9 : ℤ) else 1 := by
    intro i
    rcases hpattern with hp | hp <;> rw [hp i] <;> by_cases hi : i ∈ S <;> simp [hi]
  calc ∑ i, (y i) ^ 2 = ∑ i, (if i ∈ S then (9 : ℤ) else 1) :=
        Finset.sum_congr rfl fun i _ => hvalue i
    _ = 24 := by
        rw [sum_ite_mem_const S 9 1, hS, hcard]
        norm_num

/-- A vector
of the glued pair model on `8 + 8` coordinates with square sum `48` — that is,
of norm three — has both blocks minimal in `E₇* ∖ E₇`.  There are `56 ^ 2 = 3136`
of them. -/
theorem gluedPair_norm_three [DecidableEq ι] [DecidableEq κ]
    (hcardl : Fintype.card ι = 8) (hcardr : Fintype.card κ = 8) {y : (ι ⊕ κ) → ℤ}
    (hy : y ∈ gluedPairSubmodule ι κ)
    (hnorm : (∑ i, (y (Sum.inl i)) ^ 2) + (∑ i, (y (Sum.inr i)) ^ 2) = 48) :
    IsE7Minimal (fun i => y (Sum.inl i)) ∧ IsE7Minimal (fun i => y (Sum.inr i)) := by
  have hsuml : ∑ i, y (Sum.inl i) = 0 := hy.1
  have hsumr : ∑ i, y (Sum.inr i) = 0 := hy.2.1
  obtain ⟨r, s, hr, hs, hrl, hrr, hrs⟩ := gluedPair_residues_normalised hy
  have hcardl' : Fintype.card ι = 4 * 2 := by omega
  have hcardr' : Fintype.card κ = 4 * 2 := by omega
  have heven : r = 0 ∨ r = 2 → False := by
    intro hre
    have hse : s = 0 ∨ s = 2 := by omega
    obtain ⟨kl, hkl⟩ := sumZeroCongruent_even_dvd (m := 2) hcardl' (by norm_num)
      (r := r) (by omega) hsuml hrl
    obtain ⟨kr, hkr⟩ := sumZeroCongruent_even_dvd (m := 2) hcardr' (by norm_num)
      (r := s) (by omega) hsumr hrr
    omega
  have hrodd : r = 1 ∨ r = 3 := by
    rcases hr with h | h | h | h
    · exact absurd (Or.inl h) heven
    · exact Or.inl h
    · exact absurd (Or.inr h) heven
    · exact Or.inr h
  have hsodd : s = 1 ∨ s = 3 := by
    obtain ⟨k, hk⟩ := hrs
    omega
  have hodd : (r = 1 ∨ r = 3) ∧ (s = 1 ∨ s = 3) := ⟨hrodd, hsodd⟩
  have hboundl := sumZeroCongruent_odd_bound (m := 2) hcardl' hodd.1 hsuml hrl
  have hboundr := sumZeroCongruent_odd_bound (m := 2) hcardr' hodd.2 hsumr hrr
  push_cast at hboundl hboundr
  have hexactl : ∑ i, (y (Sum.inl i)) ^ 2 = 24 := by omega
  have hexactr : ∑ i, (y (Sum.inr i)) ^ 2 = 24 := by omega
  constructor
  · exact sumZeroCongruent_odd_shell (m := 2) hcardl' hodd.1 hsuml hrl (by push_cast; omega)
  · exact sumZeroCongruent_odd_shell (m := 2) hcardr' hodd.2 hsumr hrr (by push_cast; omega)

end Blocks

section SameParity

variable {ι : Type*} [Fintype ι]

/-- **The same-parity model.**  In dimension `n` divisible by `4` this is
`2 • Dₙ⁺`: all coordinates of one parity, coordinate sum divisible by `4`.
Dimension 8 gives `2 • E₈` and dimension 12 gives `2 • D₁₂⁺`. -/
def SameParitySumFour (z : ι → ℤ) : Prop :=
  (∃ p : ℤ, ∀ i, (2 : ℤ) ∣ (z i - p)) ∧ (4 : ℤ) ∣ ∑ i, z i

/-- The same-parity model is a `ℤ`-submodule of the ambient coordinates. -/
def sameParitySubmodule (ι : Type*) [Fintype ι] : Submodule ℤ (ι → ℤ) where
  carrier := {z | (∃ p : ℤ, ∀ i, (2 : ℤ) ∣ (z i - p)) ∧ (4 : ℤ) ∣ ∑ i, z i}
  zero_mem' := ⟨⟨0, by simp⟩, by simp⟩
  add_mem' := by
    rintro y z ⟨⟨p, hp⟩, hy⟩ ⟨⟨q, hq⟩, hz⟩
    refine ⟨⟨p + q, fun i => ?_⟩, ?_⟩
    · have hstep : (y + z) i - (p + q) = (y i - p) + (z i - q) := by
        simp only [Pi.add_apply]
        ring
      rw [hstep]
      exact dvd_add (hp i) (hq i)
    · simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib]
      exact dvd_add hy hz
  smul_mem' := by
    rintro c y ⟨⟨p, hp⟩, hy⟩
    refine ⟨⟨c * p, fun i => ?_⟩, ?_⟩
    · have hstep : (c • y) i - c * p = c * (y i - p) := by
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [hstep]
      exact Dvd.dvd.mul_left (hp i) c
    · have hstep : ∑ i, (c • y) i = c * ∑ i, y i := by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [hstep]
      exact Dvd.dvd.mul_left hy c

@[simp] theorem mem_sameParitySubmodule {z : ι → ℤ} :
    z ∈ sameParitySubmodule ι ↔ SameParitySumFour z := Iff.rfl

/-- Every coordinate is even, or every coordinate is odd. -/
theorem SameParitySumFour.parity_cases {z : ι → ℤ} (hz : SameParitySumFour z) :
    (∀ i, (2 : ℤ) ∣ z i) ∨ (∀ i, ¬ (2 : ℤ) ∣ z i) := by
  obtain ⟨⟨p, hp⟩, -⟩ := hz
  rcases Int.even_or_odd p with hpar | hpar
  · refine Or.inl fun i => ?_
    obtain ⟨k, hk⟩ := hp i
    obtain ⟨j, hj⟩ := hpar
    exact ⟨j + k, by omega⟩
  · refine Or.inr fun i hdvd => ?_
    obtain ⟨k, hk⟩ := hp i
    obtain ⟨j, hj⟩ := hdvd
    obtain ⟨l, hl⟩ := hpar
    omega

/-- **`Dₙ` is even.**  An all-even model vector has square sum divisible by
`8`, i.e. even norm after dividing by the square of the scale. -/
theorem sum_sq_dvd_eight_of_even {z : ι → ℤ} (heven : ∀ i, (2 : ℤ) ∣ z i)
    (hsum : (4 : ℤ) ∣ ∑ i, z i) : (8 : ℤ) ∣ ∑ i, (z i) ^ 2 := by
  choose w hw using heven
  have hz : ∀ i, z i = 2 * w i := fun i => by rw [hw i]
  have hsumw : ∑ i, z i = 2 * ∑ i, w i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hz i
  have hw2 : (2 : ℤ) ∣ ∑ i, w i := by
    obtain ⟨k, hk⟩ := hsum
    omega
  have hsq : ∑ i, (z i) ^ 2 = 4 * ∑ i, (w i) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hz i]; ring
  obtain ⟨u, hu⟩ := two_dvd_sum_sq_sub_sum w
  obtain ⟨v, hv⟩ := hw2
  exact ⟨u + v, by rw [hsq]; omega⟩

/-- A half-integral model vector has square sum congruent to the dimension
modulo `8`. -/
theorem sum_sq_sub_card_dvd_eight {z : ι → ℤ} (hodd : ∀ i, ¬ (2 : ℤ) ∣ z i) :
    (8 : ℤ) ∣ (∑ i, (z i) ^ 2 - (Fintype.card ι : ℤ)) := by
  have hcard : (Fintype.card ι : ℤ) = ∑ _i : ι, (1 : ℤ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [hcard, ← Finset.sum_sub_distrib]
  exact Finset.dvd_sum fun i _ => eight_dvd_sq_sub_one (hodd i)

/-- On twelve
coordinates a same-parity model vector whose square sum is divisible by `8` —
that is, of even norm after dividing by the square of the scale — has all
coordinates even, so it lies in `2 • D₁₂` and not in the half-integral coset. -/
theorem sameParity_even_of_dvd_eight (hcard : Fintype.card ι = 12) {z : ι → ℤ}
    (hz : SameParitySumFour z) (hdvd : (8 : ℤ) ∣ ∑ i, (z i) ^ 2) :
    ∀ i, (2 : ℤ) ∣ z i := by
  rcases hz.parity_cases with heven | hodd
  · exact heven
  · exfalso
    obtain ⟨k, hk⟩ := sum_sq_sub_card_dvd_eight hodd
    obtain ⟨l, hl⟩ := hdvd
    rw [hcard] at hk
    omega

/-- A model vector of `2 • D₁₂⁺` with
square sum `12` — that is, of norm three — is half-integral with all
coordinates `±1`. -/
theorem sameParity_norm_three {z : ι → ℤ} (hcard : Fintype.card ι = 12)
    (hz : SameParitySumFour z) (hnorm : ∑ i, (z i) ^ 2 = 12) :
    ∀ i, z i = 1 ∨ z i = -1 := by
  rcases hz.parity_cases with heven | hodd
  · exfalso
    obtain ⟨k, hk⟩ := sum_sq_dvd_eight_of_even heven hz.2
    omega
  · intro i
    have hone : ∀ j, 1 ≤ (z j) ^ 2 := by
      intro j
      rcases eq_or_ne (z j) 0 with h | h
      · exact absurd ⟨0, by simp [h]⟩ (hodd j)
      · nlinarith [sq_nonneg (z j), Int.one_le_abs h, sq_abs (z j)]
    have hsum : ∑ j, ((z j) ^ 2 - 1) = 0 := by
      rw [Finset.sum_sub_distrib, hnorm, Finset.sum_const, Finset.card_univ, hcard]
      norm_num
    have hnn : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ (z j) ^ 2 - 1 :=
      fun j _ => by linarith [hone j]
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i (Finset.mem_univ i)
    have hsq : (z i) ^ 2 = 1 := by linarith
    rcases eq_or_ne (z i) 1 with h | h
    · exact Or.inl h
    · right
      have hfac : (z i - 1) * (z i + 1) = 0 := by nlinarith [hsq]
      rcases mul_eq_zero.mp hfac with hh | hh
      · exact absurd (by omega : z i = 1) h
      · omega

/-- Every vector of the `2 • E₈` model has
square sum divisible by `8`; in particular none has norm three. -/
theorem sameParity_dvd_eight {z : ι → ℤ} (hcard : Fintype.card ι = 8)
    (hz : SameParitySumFour z) : (8 : ℤ) ∣ ∑ i, (z i) ^ 2 := by
  rcases hz.parity_cases with heven | hodd
  · exact sum_sq_dvd_eight_of_even heven hz.2
  · obtain ⟨k, hk⟩ := sum_sq_sub_card_dvd_eight hodd
    rw [hcard] at hk
    exact ⟨k + 1, by omega⟩

end SameParity

end Lattice
end SRG266
