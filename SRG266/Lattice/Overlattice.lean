/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Factorization.Basic
import SRG266.Lattice.Core

/-!
# Maximal integral overlattices

Let `B` be a nondegenerate symmetric bilinear form on a `ℚ`-vector space `W` and
let `N ⊆ W` be an integral lattice, that is, a finitely generated `ℤ`-submodule
spanning `W` on which `B` takes integer values.  An *integral overlattice* of
`N` is a `ℤ`-submodule `N ≤ P ⊆ W` on which `B` is still integral; every such
`P` is squeezed between `N` and the dual lattice `N^∨`.

This file builds the first half of the abstract overlattice theory:

* `exists_maximal_integral_overlattice` — a maximal integral overlattice exists.
  The dual lattice `N^∨` is finitely generated, hence Noetherian over `ℤ`, so the
  nonempty family of integral overlattices, transported inside `N^∨`, has a
  maximal member.
* `IsMaximalIntegral.smul_mem_of_sq_smul_mem` — *Lemma E, exponent halving*: if
  `Ñ` is maximal, `y ∈ Ñ^∨` and `a² • y ∈ Ñ`, then already `a • y ∈ Ñ`.  Indeed
  `z = a • y` pairs integrally with `Ñ` and `B z z = B (a² • y) y ∈ ℤ`, so
  `Ñ + ℤ z` is an integral overlattice and maximality forces `z ∈ Ñ`.
* `IsMaximalIntegral.dual_smul_mem_of_dvd_pow` — iterating Lemma E: a
  denominator bound `k • Ñ^∨ ⊆ Ñ` with `k ∣ m ^ j` improves to `m • Ñ^∨ ⊆ Ñ`.
  Taking `m = rad k` gives `exists_maximal_integral_overlattice_radical`: the
  dual quotient of a maximal overlattice has exponent dividing the radical of
  `k`, so it is `p`-elementary at every prime.
* `torsionPart` and `dual_eq_torsionPart_sup` — the CRT splitting
  `Ñ^∨ = T_a + T_b` for coprime `a`, `b` with `(a * b) • Ñ^∨ ⊆ Ñ`, obtained by
  Bézout at the level of elements (`1 = u a + v b`, `y = (u a) • y + (v b) • y`)
  rather than through any group-decomposition API.

For the local Gram lattice of a hypothetical `srg(266, 45, 0, 9)` the input is
`k = 225` (`SRG266.gram_dual_denominator`), whence `15 • Ñ^∨ ⊆ Ñ` and
`Ñ^∨ = T₃ + T₅`; that instantiation is
`SRG266/Lattice/GramOverlattice.lean`.

Everything here is stated for an abstract `(W, B)`; nothing refers to a graph.

The main results are `exists_maximal_integral_overlattice` and
`maximal_exponent_squarefree`, whose key lemma
`IsMaximalIntegral.smul_mem_of_sq_smul_mem` is proved for an arbitrary integer
`a`, not only for a prime, which is what makes the iteration
`IsMaximalIntegral.smul_mem_of_pow_smul_mem` possible — and the splitting
`Λ̃^∨ = Λ̃ + T₃ + T₅` is `dual_eq_torsionPart_sup` together with
`le_torsionPart`.
-/

namespace SRG266.Lattice

section Overlattice

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable (B : LinearMap.BilinForm ℚ W)

/-! ### Elementary dual-lattice bookkeeping -/

/-- The dual submodule is antitone. -/
theorem dualSubmodule_antitone {N P : Submodule ℤ W} (h : N ≤ P) :
    B.dualSubmodule P ≤ B.dualSubmodule N := fun _ hx y hy => hx y (h hy)

/-- An integral submodule is contained in the dual of any submodule it
contains. -/
theorem le_dual_of_le {N P : Submodule ℤ W} (h : N ≤ P) (hP : IsIntegral B P) :
    P ≤ B.dualSubmodule N :=
  le_trans hP (dualSubmodule_antitone B h)

/-- A submodule of an integral submodule is integral. -/
theorem IsIntegral.mono {N P : Submodule ℤ W} (hP : IsIntegral B P) (h : N ≤ P) :
    IsIntegral B N :=
  le_trans h (le_dual_of_le B h hP)

/-- Adjoining a vector that pairs integrally with an integral submodule and with
itself keeps the submodule integral. -/
theorem isIntegral_sup_span_singleton (hsymm : B.IsSymm) {P : Submodule ℤ W}
    (hP : IsIntegral B P) {z : W}
    (hz : ∀ v ∈ P, B z v ∈ (1 : Submodule ℤ ℚ))
    (hzz : B z z ∈ (1 : Submodule ℤ ℚ)) :
    IsIntegral B (P ⊔ Submodule.span ℤ {z}) := by
  rw [isIntegral_iff_forall]
  rintro u hu v hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
  obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨m, rfl⟩ := Submodule.mem_span_singleton.mp hb
  obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hd
  obtain ⟨i₁, hi₁⟩ := Submodule.mem_one.mp (hP ha c hc)
  obtain ⟨i₂, hi₂⟩ := Submodule.mem_one.mp (hz a ha)
  obtain ⟨i₃, hi₃⟩ := Submodule.mem_one.mp (hz c hc)
  obtain ⟨i₄, hi₄⟩ := Submodule.mem_one.mp hzz
  have e₁ : (i₁ : ℚ) = B a c := by simpa using hi₁
  have e₂ : (i₂ : ℚ) = B z a := by simpa using hi₂
  have e₃ : (i₃ : ℚ) = B z c := by simpa using hi₃
  have e₄ : (i₄ : ℚ) = B z z := by simpa using hi₄
  have hsw : B a z = B z a := (hsymm.eq a z)
  have hgoal : B (a + m • z) (c + n • z) =
      ((i₁ + n * i₂ + m * i₃ + m * n * i₄ : ℤ) : ℚ) := by
    simp only [map_add, LinearMap.add_apply, map_zsmul, LinearMap.smul_apply,
      zsmul_eq_mul, hsw, ← e₁, ← e₂, ← e₃, ← e₄]
    push_cast
    ring
  rw [hgoal]
  exact Submodule.mem_one.mpr ⟨i₁ + n * i₂ + m * i₃ + m * n * i₄, by simp⟩

/-! ### Existence of a maximal integral overlattice -/

/-- `Ñ` is *maximal integral*: the form is integral on `Ñ`, and no strictly
larger `ℤ`-submodule of `W` has that property. -/
structure IsMaximalIntegral (B : LinearMap.BilinForm ℚ W) (Ñ : Submodule ℤ W) : Prop where
  /-- The form is integral on `Ñ`. -/
  integral : IsIntegral B Ñ
  /-- No larger submodule is integral. -/
  maximal : ∀ P : Submodule ℤ W, Ñ ≤ P → IsIntegral B P → P = Ñ

/-- **Lemma M.**  An integral lattice admits a maximal integral overlattice.

Every integral overlattice `P` of `N` satisfies `N ≤ P ≤ N^∨`, and `N^∨` is a
finitely generated `ℤ`-module, hence Noetherian; so the family of integral
overlattices, transported into `N^∨`, has a maximal member. -/
theorem exists_maximal_integral_overlattice (hnd : B.Nondegenerate)
    {N : Submodule ℤ W} (hN : IsLattice ℚ N) (hint : IsIntegral B N) :
    ∃ Ñ : Submodule ℤ W, N ≤ Ñ ∧ IsLattice ℚ Ñ ∧ IsMaximalIntegral B Ñ := by
  classical
  set D : Submodule ℤ W := B.dualSubmodule N
  have hNle : N ≤ D := hint
  have hDfg : D.FG := (dual_isLattice B hN hnd).fg
  haveI : IsNoetherian ℤ D := isNoetherian_of_fg_of_noetherian D hDfg
  have hmapcomap : ∀ P : Submodule ℤ W, P ≤ D →
      (P.comap D.subtype).map D.subtype = P := by
    intro P hP
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hP]
  set 𝒜 : Set (Submodule ℤ D) :=
    {Q | N ≤ Q.map D.subtype ∧ IsIntegral B (Q.map D.subtype)} with h𝒜
  have hne : 𝒜.Nonempty := by
    refine ⟨N.comap D.subtype, ?_⟩
    rw [h𝒜, Set.mem_setOf_eq, hmapcomap N hNle]
    exact ⟨le_rfl, hint⟩
  obtain ⟨Q₀, hQ₀, hQmax⟩ := set_has_maximal_iff_noetherian.mpr inferInstance 𝒜 hne
  rw [h𝒜, Set.mem_setOf_eq] at hQ₀
  refine ⟨Q₀.map D.subtype, hQ₀.1, ⟨(IsNoetherian.noetherian Q₀).map _, ?_⟩, hQ₀.2, ?_⟩
  · refine top_unique ?_
    rw [← hN.spans]
    exact Submodule.span_mono (fun x hx => hQ₀.1 hx)
  · intro P hP hPint
    have hPD : P ≤ D := le_dual_of_le B (le_trans hQ₀.1 hP) hPint
    have hQle : Q₀ ≤ P.comap D.subtype := by
      intro q hq
      exact hP ⟨q, hq, rfl⟩
    have hmem : P.comap D.subtype ∈ 𝒜 := by
      rw [h𝒜, Set.mem_setOf_eq, hmapcomap P hPD]
      exact ⟨le_trans hQ₀.1 hP, hPint⟩
    have hQeq : Q₀ = P.comap D.subtype :=
      eq_of_le_of_not_lt hQle (hQmax _ hmem)
    rw [hQeq, hmapcomap P hPD]

/-! ### Lemma E: exponent halving at a maximal overlattice -/

variable {B}

/-- **Lemma E (exponent halving).**  If `Ñ` is a maximal integral submodule,
`y` lies in its dual and `a² • y ∈ Ñ`, then `a • y ∈ Ñ`.

The vector `z = a • y` pairs integrally with `Ñ` because `y` does, and
`B z z = a² * B y y = B (a² • y) y` is an integer because `a² • y ∈ Ñ`.  Hence
`Ñ + ℤ z` is an integral overlattice of `Ñ`, which maximality collapses. -/
theorem IsMaximalIntegral.smul_mem_of_sq_smul_mem (hsymm : B.IsSymm)
    {Ñ : Submodule ℤ W} (hmax : IsMaximalIntegral B Ñ) {a : ℤ} {y : W}
    (hy : y ∈ B.dualSubmodule Ñ) (h : (a ^ 2) • y ∈ Ñ) : a • y ∈ Ñ := by
  have hzv : ∀ v ∈ Ñ, B (a • y) v ∈ (1 : Submodule ℤ ℚ) := by
    intro v hv
    rw [map_zsmul, LinearMap.smul_apply]
    exact Submodule.smul_mem _ a (hy v hv)
  have hzz : B (a • y) (a • y) ∈ (1 : Submodule ℤ ℚ) := by
    have hrw : B (a • y) (a • y) = B y ((a ^ 2) • y) := by
      simp only [map_zsmul, LinearMap.smul_apply, hsymm.eq y]
      rw [← hsymm.eq y y]
      ring
    rw [hrw]
    exact hy _ h
  have hsup := hmax.maximal (Ñ ⊔ Submodule.span ℤ {a • y}) le_sup_left
    (isIntegral_sup_span_singleton B hsymm hmax.integral hzv hzz)
  have hmem : a • y ∈ Ñ ⊔ Submodule.span ℤ {a • y} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  rwa [hsup] at hmem

/-- **Lemma E, iterated.**  At a maximal integral submodule a denominator is
squarefree: if some power `a ^ (j + 1) • y` lies in `Ñ` for `y` in the dual,
then already `a • y` does. -/
theorem IsMaximalIntegral.smul_mem_of_pow_smul_mem (hsymm : B.IsSymm)
    {Ñ : Submodule ℤ W} (hmax : IsMaximalIntegral B Ñ) {a : ℤ} {y : W}
    (hy : y ∈ B.dualSubmodule Ñ) :
    ∀ {j : ℕ}, (a ^ (j + 1)) • y ∈ Ñ → a • y ∈ Ñ := by
  intro j
  induction j with
  | zero => intro h; simpa using h
  | succ j ih =>
    intro h
    refine ih ?_
    have hy' : (a ^ j) • y ∈ B.dualSubmodule Ñ := Submodule.smul_mem _ _ hy
    have hsq : (a ^ 2) • ((a ^ j) • y) ∈ Ñ := by
      rw [smul_smul]
      convert h using 2
      ring
    have := hmax.smul_mem_of_sq_smul_mem hsymm hy' hsq
    rwa [smul_smul, ← pow_succ'] at this

/-- **The denominator of a maximal overlattice is squarefree.**  If
`k • Ñ^∨ ⊆ Ñ` and `k ∣ m ^ j`, then already `m • Ñ^∨ ⊆ Ñ`. -/
theorem IsMaximalIntegral.dual_smul_mem_of_dvd_pow (hsymm : B.IsSymm)
    {Ñ : Submodule ℤ W} (hmax : IsMaximalIntegral B Ñ) {k m : ℤ} {j : ℕ}
    (hk : ∀ y ∈ B.dualSubmodule Ñ, k • y ∈ Ñ) (hdvd : k ∣ m ^ j)
    {y : W} (hy : y ∈ B.dualSubmodule Ñ) : m • y ∈ Ñ := by
  obtain ⟨t, ht⟩ := hdvd
  refine hmax.smul_mem_of_pow_smul_mem hsymm hy (j := j) ?_
  have hpow : (m ^ (j + 1)) • y = (m * t) • (k • y) := by
    rw [smul_smul]
    congr 1
    calc m ^ (j + 1) = m * m ^ j := by ring
      _ = m * (k * t) := by rw [ht]
      _ = m * t * k := by ring
  rw [hpow]
  exact Submodule.smul_mem _ _ (hk y hy)

/-! ### The maximal overlattice with a squarefree denominator -/

variable (B)

/-- **Lemma M + Lemma E.**  An integral lattice `N` whose dual has denominator
`k` admits a maximal integral overlattice `Ñ` whose dual has denominator `m`,
for any `m` with `k ∣ m ^ j`. -/
theorem exists_maximal_integral_overlattice_denominator (hnd : B.Nondegenerate)
    (hsymm : B.IsSymm) {N : Submodule ℤ W} (hN : IsLattice ℚ N)
    (hint : IsIntegral B N) {k m : ℤ} {j : ℕ}
    (hk : ∀ y ∈ B.dualSubmodule N, k • y ∈ N) (hdvd : k ∣ m ^ j) :
    ∃ Ñ : Submodule ℤ W, N ≤ Ñ ∧ IsLattice ℚ Ñ ∧ IsMaximalIntegral B Ñ ∧
      ∀ y ∈ B.dualSubmodule Ñ, m • y ∈ Ñ := by
  obtain ⟨Ñ, hle, hlat, hmax⟩ := exists_maximal_integral_overlattice B hnd hN hint
  refine ⟨Ñ, hle, hlat, hmax, ?_⟩
  have hkÑ : ∀ y ∈ B.dualSubmodule Ñ, k • y ∈ Ñ := by
    intro y hy
    exact hle (hk y (dualSubmodule_antitone B hle hy))
  intro y hy
  exact hmax.dual_smul_mem_of_dvd_pow hsymm hkÑ hdvd hy

/-- The radical of a natural number: the product of its prime factors. -/
def natRadical (k : ℕ) : ℕ := ∏ p ∈ k.primeFactors, p

theorem natRadical_dvd (k : ℕ) : natRadical k ∣ k := Nat.prod_primeFactors_dvd k

theorem dvd_natRadical_pow {k : ℕ} (hk : k ≠ 0) : k ∣ natRadical k ^ k :=
  Nat.dvd_prod_primeFactors_pow_self hk

theorem squarefree_natRadical (k : ℕ) : Squarefree (natRadical k) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).prime.squarefree

/-- An integral lattice `N` with a denominator bound
`k • N^∨ ⊆ N` admits a maximal integral overlattice `Ñ` whose dual quotient has
exponent dividing the radical of `k`: only the primes dividing `k` occur, each
to the first power. -/
theorem exists_maximal_integral_overlattice_radical (hnd : B.Nondegenerate)
    (hsymm : B.IsSymm) {N : Submodule ℤ W} (hN : IsLattice ℚ N)
    (hint : IsIntegral B N) {k : ℕ} (hk0 : k ≠ 0)
    (hk : ∀ y ∈ B.dualSubmodule N, (k : ℤ) • y ∈ N) :
    ∃ Ñ : Submodule ℤ W, N ≤ Ñ ∧ IsLattice ℚ Ñ ∧ IsMaximalIntegral B Ñ ∧
      (∀ y ∈ B.dualSubmodule Ñ, ((natRadical k : ℕ) : ℤ) • y ∈ Ñ) ∧
      ∀ q : B.dualSubmodule Ñ ⧸ Ñ.comap (B.dualSubmodule Ñ).subtype,
        natRadical k • q = 0 := by
  obtain ⟨Ñ, hle, hlat, hmax, hden⟩ :=
    exists_maximal_integral_overlattice_denominator B hnd hsymm hN hint
      (k := (k : ℤ)) (m := ((natRadical k : ℕ) : ℤ)) (j := k) hk
      (by exact_mod_cast Int.natCast_dvd_natCast.mpr (dvd_natRadical_pow hk0))
  exact ⟨Ñ, hle, hlat, hmax, hden, fun q => quotient_nsmul_eq_zero hden q⟩

/-! ### The `p`-torsion parts of the dual quotient -/

/-- The vectors of the dual lattice whose `p`-th multiple already lies in `Ñ`:
the preimage in `Ñ^∨` of the `p`-torsion of `Ñ^∨/Ñ`. -/
def torsionPart (Ñ : Submodule ℤ W) (p : ℕ) : Submodule ℤ W :=
  B.dualSubmodule Ñ ⊓ Ñ.comap (LinearMap.lsmul ℤ W (p : ℤ))

variable {B}

@[simp]
theorem mem_torsionPart {Ñ : Submodule ℤ W} {p : ℕ} {y : W} :
    y ∈ torsionPart B Ñ p ↔ y ∈ B.dualSubmodule Ñ ∧ (p : ℤ) • y ∈ Ñ := by
  simp [torsionPart, LinearMap.lsmul_apply]

theorem torsionPart_le_dual (Ñ : Submodule ℤ W) (p : ℕ) :
    torsionPart B Ñ p ≤ B.dualSubmodule Ñ := inf_le_left

theorem le_torsionPart {Ñ : Submodule ℤ W} (hint : IsIntegral B Ñ) (p : ℕ) :
    Ñ ≤ torsionPart B Ñ p := by
  intro y hy
  exact mem_torsionPart.mpr ⟨hint hy, Submodule.smul_mem _ _ hy⟩

/-- **CRT splitting by Bézout.**  If `a` and `b` are coprime and `(a * b)` is a
denominator bound for `Ñ^∨`, then `Ñ^∨ = T_a + T_b`; since `Ñ ≤ T_a`, this is
the decomposition `Ñ^∨ = Ñ + T_a + T_b`.

The proof is elementwise: writing `1 = u a + v b`, the vector `y` splits as
`(u a) • y + (v b) • y`, whose two halves are killed by `b` and by `a`. -/
theorem dual_eq_torsionPart_sup {Ñ : Submodule ℤ W} {a b : ℕ}
    (hab : Nat.Coprime a b)
    (h : ∀ y ∈ B.dualSubmodule Ñ, ((a * b : ℕ) : ℤ) • y ∈ Ñ) :
    B.dualSubmodule Ñ = torsionPart B Ñ a ⊔ torsionPart B Ñ b := by
  refine le_antisymm ?_ (sup_le (torsionPart_le_dual Ñ a) (torsionPart_le_dual Ñ b))
  intro y hy
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * (a : ℤ) + v * (b : ℤ) = 1 := by
    have : IsCoprime (a : ℤ) (b : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (by simpa using hab)
    obtain ⟨u, v, huv⟩ := this
    exact ⟨u, v, huv⟩
  have hab' : ((a * b : ℕ) : ℤ) • y ∈ Ñ := h y hy
  have hsplit : (u * (a : ℤ)) • y + (v * (b : ℤ)) • y = y := by
    rw [← add_smul, huv, one_smul]
  refine hsplit ▸ Submodule.add_mem _ ?_ ?_
  · refine Submodule.mem_sup_right (mem_torsionPart.mpr ⟨Submodule.smul_mem _ _ hy, ?_⟩)
    have hswap : (b : ℤ) • ((u * (a : ℤ)) • y) = u • (((a * b : ℕ) : ℤ) • y) := by
      rw [smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    rw [hswap]
    exact Submodule.smul_mem _ _ hab'
  · refine Submodule.mem_sup_left (mem_torsionPart.mpr ⟨Submodule.smul_mem _ _ hy, ?_⟩)
    have hswap : (a : ℤ) • ((v * (b : ℤ)) • y) = v • (((a * b : ℕ) : ℤ) • y) := by
      rw [smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    rw [hswap]
    exact Submodule.smul_mem _ _ hab'

/-! ### The dual quotient of a maximal overlattice -/

/-- The dual quotient `Ñ^∨/Ñ` has exponent dividing any denominator bound. -/
theorem dualQuotient_nsmul_eq_zero {Ñ : Submodule ℤ W} {n : ℕ}
    (hn : ∀ y ∈ B.dualSubmodule Ñ, (n : ℤ) • y ∈ Ñ)
    (q : B.dualSubmodule Ñ ⧸ Ñ.comap (B.dualSubmodule Ñ).subtype) : n • q = 0 :=
  quotient_nsmul_eq_zero hn q

end Overlattice

end SRG266.Lattice
