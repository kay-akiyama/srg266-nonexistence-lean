/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15PackingReduction

/-!
# Building an `A₁₅⁺` shell realization from coordinate data

`SRG266.A15ShellGramRealization` is stated over the indexed four-subset table
`SRG266.A15FourSubsetIndex`, but nothing about the table index is mathematical
content: a realization is determined by a *four-subset* `S B ⊆ Fin 16` for every
embedded generator, together with the sign that orients it.

This file supplies the two pieces needed by the `a15Plus` branch and keeps the
table index out of both.

* `SRG266.Lattice.a15ShellGramRealization_of_data` — the builder.  Given the
  centroid coordinate vector `d`, the scaled generator coordinates `y B` and
  their supporting four-subsets, together with the four numeric facts
  `∑ d = 0`, `⟨d, y B⟩ = 240`, `⟨y B, y C⟩ = 16 L_BC` and `∑_B y B = 11 d`, it
  produces the realization.  Eligibility and the orientation convention of
  `SRG266.a15ShellCoordinate4` come out of `⟨d, y B⟩ = 240` on the nose, and
  `eq_of_inner_eq_three` is the elementary statement that two four-sets meeting
  in four points coincide.
* `SRG266.Lattice.exists_perm_comp_of_ofFn_perm` — two tuples with the same
  value list differ by a permutation of the index set.  This is what turns the
  count-based canonical reordering `SRG266.a15CanonicalReducedCoordinates` into
  a permutation of `Fin 16`, along which the whole data package above is simply
  reindexed.

Sending a permutation through the *data* rather than through a built
realization keeps the proof short: `Equiv.sum_comp` transports
every hypothesis of the builder in one line each.
-/

namespace SRG266
namespace Lattice

open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Unoriented four-subset vectors -/

/-- Four times the unoriented norm-three shell vector of a four-subset: `-3` on
the subset and `1` off it. -/
def a15RawVector (S : Finset (Fin 16)) (i : Fin 16) : ℤ :=
  if i ∈ S then -3 else 1

variable {G}

/-- Pairing a coordinate vector against an unoriented shell vector sees only the
subset sum. -/
theorem dot_a15RawVector (d : Fin 16 → ℤ) (S : Finset (Fin 16)) :
    ∑ i, d i * a15RawVector S i = (∑ i, d i) - 4 * ∑ i ∈ S, d i := by
  have hexp : ∀ i : Fin 16,
      d i * a15RawVector S i = d i - 4 * (if i ∈ S then d i else 0) := by
    intro i
    by_cases hs : i ∈ S
    · simp [a15RawVector, hs]
      ring
    · simp [a15RawVector, hs]
  rw [Finset.sum_congr rfl fun i _ => hexp i, Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 2
  rw [Finset.sum_ite_mem]
  congr 1
  exact Finset.univ_inter S

/-- The Gram law of the unoriented shell: two four-subset vectors pair to
`16 (|S ∩ T| - 1)`. -/
theorem a15RawVector_dot (S T : Finset (Fin 16)) (hS : S.card = 4) (hT : T.card = 4) :
    ∑ i, a15RawVector S i * a15RawVector T i = 16 * (((S ∩ T).card : ℤ) - 1) := by
  have hexp : ∀ i : Fin 16, a15RawVector S i * a15RawVector T i =
      1 - 4 * (if i ∈ S then (1 : ℤ) else 0) - 4 * (if i ∈ T then (1 : ℤ) else 0) +
        16 * ((if i ∈ S then (1 : ℤ) else 0) * (if i ∈ T then (1 : ℤ) else 0)) := by
    intro i
    by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;> simp [a15RawVector, hs, ht]
  have hcross : ∀ i : Fin 16,
      (if i ∈ S then (1 : ℤ) else 0) * (if i ∈ T then (1 : ℤ) else 0) =
        if i ∈ S ∩ T then (1 : ℤ) else 0 := by
    intro i
    by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;> simp [hs, ht]
  have hind : ∀ U : Finset (Fin 16),
      (∑ i, if i ∈ U then (1 : ℤ) else 0) = (U.card : ℤ) := by
    intro U
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    simp
  rw [Finset.sum_congr rfl fun i _ => hexp i]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_congr rfl fun i _ => hcross i, hind S, hind T, hind (S ∩ T), hS, hT]
  simp
  ring

/-! ## The table index of a four-subset -/

/-- Every four-subset of `Fin 16` occurs in the checked `1820`-entry table. -/
theorem exists_a15FourSubsetIndex (S : Finset (Fin 16)) (hS : S.card = 4) :
    ∃ s : A15FourSubsetIndex, a15FourSubsetAsFinset s = S := by
  have hmem : S ∈ (Finset.univ : Finset (Fin 16)).powersetCard 4 :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hS⟩
  rw [← a15FourSubsetUniverse_complete] at hmem
  obtain ⟨s, -, hs⟩ := Finset.mem_image.mp hmem
  exact ⟨s, hs⟩

/-- Every table entry is a four-subset. -/
theorem a15FourSubsetAsFinset_card_eq (s : A15FourSubsetIndex) :
    (a15FourSubsetAsFinset s).card = 4 := by
  unfold a15FourSubsetAsFinset A15FourSubset.asFinset
  rw [List.toFinset_card_of_nodup (a15FourSubsetAt_coordinates_nodup s)]
  rfl

/-- The subset sum of the table entry is the `Finset` sum of its members. -/
theorem a15SubsetSum_eq_sum (d : Fin 16 → ℤ) (s : A15FourSubsetIndex) :
    a15SubsetSum d s = ∑ i ∈ a15FourSubsetAsFinset s, d i :=
  a15FourSubset_valueSum_eq_finset_sum d s

/-! ## Oriented shell vectors -/

/-- The oriented shell vector is the unoriented one up to the sign fixed by the
subset sum. -/
theorem a15ShellVector4_eq_sign_smul (d : Fin 16 → ℤ) (s : A15EligibleIndex d)
    (i : Fin 16) :
    a15ShellVector4 d s i =
      (if a15SubsetSum d s.1 = 60 then -1 else 1) *
        a15RawVector (a15FourSubsetAsFinset s.1) i := by
  have hdef : a15ShellVector4 d s i =
      if a15SubsetSum d s.1 = 60 then
        -(if i ∈ a15FourSubsetAsFinset s.1 then (-3 : ℤ) else 1)
      else if i ∈ a15FourSubsetAsFinset s.1 then (-3 : ℤ) else 1 := rfl
  rw [hdef, a15RawVector]
  by_cases hsum : a15SubsetSum d s.1 = 60
  · rw [if_pos hsum, if_pos hsum]
    ring
  · rw [if_neg hsum, if_neg hsum]
    ring

/-- **The Gram law of the oriented shell.**  The inner product of two shell
vectors is `|S ∩ T| - 1`, signed by the two orientations. -/
theorem a15ShellInner_eq_sign_mul (d : Fin 16 → ℤ) (s t : A15EligibleIndex d) :
    a15ShellInner d s t =
      (if a15SubsetSum d s.1 = 60 then -1 else 1) *
        (if a15SubsetSum d t.1 = 60 then -1 else 1) *
        (((a15FourSubsetAsFinset s.1 ∩ a15FourSubsetAsFinset t.1).card : ℤ) - 1) := by
  have hdot := a15ShellVector4_dot_eq d s t
  have hexpand : integerDot (a15ShellVector4 d s) (a15ShellVector4 d t) =
      (if a15SubsetSum d s.1 = 60 then -1 else 1) *
        (if a15SubsetSum d t.1 = 60 then -1 else 1) *
        (16 * (((a15FourSubsetAsFinset s.1 ∩ a15FourSubsetAsFinset t.1).card : ℤ) - 1)) := by
    rw [← a15RawVector_dot (a15FourSubsetAsFinset s.1) (a15FourSubsetAsFinset t.1)
      (a15FourSubsetAsFinset_card_eq s.1) (a15FourSubsetAsFinset_card_eq t.1)]
    unfold integerDot
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [a15ShellVector4_eq_sign_smul d s i, a15ShellVector4_eq_sign_smul d t i]
    ring
  rw [hexpand] at hdot
  by_cases hs : a15SubsetSum d s.1 = 60 <;> by_cases ht : a15SubsetSum d t.1 = 60 <;>
    simp only [hs, ht, if_true, if_false] at hdot ⊢ <;> omega

/-- **Distinct shell vectors never pair to three.**  This is the field
`eq_of_inner_eq_three` of `SRG266.A15ShellGramRealization`: with both signs
equal the intersection has four elements, so the four-sets agree, and with
opposite signs the intersection would have to be negative. -/
theorem a15EligibleIndex_eq_of_shellInner_eq_three (d : Fin 16 → ℤ)
    (s t : A15EligibleIndex d) (h : a15ShellInner d s t = 3) : s = t := by
  have hformula := a15ShellInner_eq_sign_mul d s t
  set S := a15FourSubsetAsFinset s.1 with hS
  set T := a15FourSubsetAsFinset t.1 with hT
  have hScard : S.card = 4 := a15FourSubsetAsFinset_card_eq s.1
  have hTcard : T.card = 4 := a15FourSubsetAsFinset_card_eq t.1
  have hinter : ((S ∩ T).card : ℤ) = 4 := by
    by_cases hs : a15SubsetSum d s.1 = 60 <;> by_cases ht : a15SubsetSum d t.1 = 60 <;>
      rw [h] at hformula <;>
      simp only [hs, ht, if_true, if_false] at hformula <;>
      omega
  have hsubset : S ∩ T = S := by
    refine Finset.eq_of_subset_of_card_le Finset.inter_subset_left ?_
    omega
  have hST : S = T := by
    refine Finset.eq_of_subset_of_card_le ?_ (by omega)
    rw [← hsubset]
    exact Finset.inter_subset_right
  exact Subtype.ext (a15FourSubsetAsFinset_injective hST)

/-! ## The builder -/

/-- **From coordinate data to an `A₁₅⁺` shell realization.**  The hypotheses are
exactly the four identities the pure branch reads off its coordinate model:
the centroid has coordinate sum zero, it pairs to `240` with every scaled
generator, the scaled generators have the local Gram matrix as their Gram
matrix up to the factor `16`, and they sum to `11` times the centroid. -/
theorem a15ShellGramRealization_of_data {x : V} (d : Fin 16 → ℤ)
    (hsum : ∑ i, d i = 0)
    (y : SecondSubconstituent G x → Fin 16 → ℤ)
    (S : SecondSubconstituent G x → Finset (Fin 16))
    (hcard : ∀ B, (S B).card = 4)
    (hshell : ∀ B, (∀ i, y B i = a15RawVector (S B) i) ∨
      (∀ i, y B i = -a15RawVector (S B) i))
    (hpair : ∀ B, ∑ i, d i * y B i = 240)
    (hgram : ∀ B C, ∑ i, y B i * y C i = 16 * localGramMatrix G x B C)
    (hcentroid : ∀ i, ∑ B, y B i = 11 * d i) :
    Nonempty (A15ShellGramRealization G x d) := by
  classical
  choose idx hidx using fun B => exists_a15FourSubsetIndex (S B) (hcard B)
  have hsub : ∀ B, a15SubsetSum d (idx B) = ∑ i ∈ S B, d i := fun B => by
    rw [a15SubsetSum_eq_sum, hidx B]
  have hraw : ∀ B, ∑ i, d i * a15RawVector (S B) i = -(4 * ∑ i ∈ S B, d i) := fun B => by
    rw [dot_a15RawVector, hsum]
    ring
  -- The orientation convention of `a15ShellCoordinate4` is forced by `⟨d, v⟩ = 15`.
  have hsign : ∀ B,
      (a15SubsetSum d (idx B) = -60 ∧ ∀ i, y B i = a15RawVector (S B) i) ∨
        (a15SubsetSum d (idx B) = 60 ∧ ∀ i, y B i = -a15RawVector (S B) i) := by
    intro B
    have hp := hpair B
    rcases hshell B with hy | hy
    · refine Or.inl ⟨?_, hy⟩
      rw [Finset.sum_congr rfl fun i _ => by rw [hy i], hraw B] at hp
      rw [hsub B]
      omega
    · refine Or.inr ⟨?_, hy⟩
      have hstep : ∑ i, d i * y B i = 4 * ∑ i ∈ S B, d i := by
        rw [Finset.sum_congr rfl fun i _ => by rw [hy i, mul_neg],
          Finset.sum_neg_distrib, hraw B]
        ring
      rw [hstep] at hp
      rw [hsub B]
      omega
  have helig : ∀ B, a15Eligible d (idx B) := by
    intro B
    rcases hsign B with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  set shell : SecondSubconstituent G x → A15EligibleIndex d :=
    fun B => ⟨idx B, helig B⟩
  have hvec : ∀ B i, a15ShellVector4 d (shell B) i = y B i := by
    intro B i
    rw [a15ShellVector4_eq_sign_smul d (shell B) i]
    have hidx' : (shell B).1 = idx B := rfl
    rw [hidx', hidx B]
    rcases hsign B with ⟨hs, hy⟩ | ⟨hs, hy⟩
    · rw [hs, hy i]
      norm_num
    · rw [hs, hy i]
      norm_num
  refine ⟨{ shell := shell
            gram := ?_
            eq_of_inner_eq_three := a15EligibleIndex_eq_of_shellInner_eq_three d
            centroid := ?_ }⟩
  · intro B C
    have hdot := a15ShellVector4_dot_eq d (shell B) (shell C)
    unfold integerDot at hdot
    rw [Finset.sum_congr rfl fun i _ => by rw [hvec B i, hvec C i], hgram B C] at hdot
    omega
  · intro i
    rw [Finset.sum_congr rfl fun B _ => hvec B i]
    exact hcentroid i

/-! ## Reindexing a tuple -/

private theorem list_count_ofFn {n : ℕ} {α : Type*} [DecidableEq α] (u : Fin n → α)
    (z : α) : (List.ofFn u).count z = ∑ i, if u i = z then 1 else 0 := by
  have hlist : ∀ l : List α,
      l.count z = (l.map (fun w => if w = z then 1 else 0)).sum := by
    intro l
    induction l with
    | nil => rfl
    | cons w l ih =>
        rw [List.count_cons, List.map_cons, List.sum_cons, ih]
        by_cases hw : w = z
        · simp [hw]
          omega
        · simp [hw]
  rw [hlist, List.map_ofFn, List.sum_ofFn]
  rfl

/-- **Two tuples with the same value list differ by a permutation.**  This turns
the count-based canonical reordering of
`SRG266.a15CanonicalReducedCoordinates` into a permutation of the sixteen
coordinates of `A₁₅⁺`. -/
theorem exists_perm_comp_of_ofFn_perm {n : ℕ} {α : Type*} [DecidableEq α]
    {f g : Fin n → α} (h : (List.ofFn f).Perm (List.ofFn g)) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, g (σ i) = f i := by
  have hfiber : ∀ z : α,
      Fintype.card {i : Fin n // f i = z} = Fintype.card {i : Fin n // g i = z} := by
    intro z
    have hcount : (List.ofFn f).count z = (List.ofFn g).count z := h.count_eq z
    rw [list_count_ofFn f z, list_count_ofFn g z] at hcount
    rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card_filter,
      Finset.card_filter]
    exact hcount
  exact ⟨Equiv.ofFiberEquiv fun z => Fintype.equivOfCardEq (hfiber z),
    fun i => Equiv.ofFiberEquiv_map _ i⟩

/-- The unoriented shell vector of a reindexed four-subset. -/
theorem a15RawVector_map (σ : Equiv.Perm (Fin 16)) (S : Finset (Fin 16)) (i : Fin 16) :
    a15RawVector (S.map σ.symm.toEmbedding) i = a15RawVector S (σ i) := by
  unfold a15RawVector
  have hmem : i ∈ S.map σ.symm.toEmbedding ↔ σ i ∈ S := by
    rw [Finset.mem_map_equiv, Equiv.symm_symm]
  by_cases hi : σ i ∈ S
  · rw [if_pos (hmem.mpr hi), if_pos hi]
  · rw [if_neg (fun hc => hi (hmem.mp hc)), if_neg hi]

end Lattice
end SRG266
