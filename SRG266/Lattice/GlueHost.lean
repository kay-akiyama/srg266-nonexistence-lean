/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.ComplementTable
import SRG266.Lattice.Transport
import Mathlib.Data.List.GetD

/-!
# From a glue basis and a certificate row to a rank-15 host

This module feeds two inputs into the abstract glue construction of
`SRG266/Lattice/Glue.lean` and the basis transport of
`SRG266/Lattice/Transport.lean`:

* the *`W`-side* datum is an orthogonal glue basis at `3` and one at `5`
  (`SRG266.Lattice.GlueBasis`) for a rank-12 integral lattice `Λ̃`
  which is its own denominator-bounded overlattice;
* the *`U`-side* datum is a validated row of the 147-row complement certificate
  table, whose discriminant diagonal is the *negative* of the
  glue basis's.

`SRG266.glueUnit` names the normalized discriminant unit `uᵢ ∈ {1, …, p-1}` of a
glue vector; `SRG266.glueUnits` collects them into the list that indexes the
certificate table.  The matching condition is then literally
`r.u3 = glueUnits S` and `r.u5 = glueUnits T`.

The two exported theorems are

* `SRG266.exists_host_of_glueBases_row` — a glue basis
  plus a *matching validated row* produces an `SRG266.OddUnimodularLattice15`
  together with an injective pairing-preserving embedding of `Λ̃`;
* `SRG266.exists_host_of_glueBases` — the same with the row selected from the
  table by `SRG266.exists_rank15ComplementRow`, so that only the glue bases are
  needed.
-/

namespace SRG266

open Lattice

/-! ## Reading a list as a family indexed by `Fin` -/

theorem setOf_mem_map_eq_range {α β : Type*} (l : List α) (d : α) (f : α → β) {n : ℕ}
    (hn : l.length = n) :
    {v | v ∈ l.map f} = Set.range (fun i : Fin n => f (l.getD i d)) := by
  subst hn
  ext v
  simp only [Set.mem_setOf_eq, List.mem_map, Set.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    exact ⟨⟨i, hi⟩, by rw [List.getD_eq_getElem _ _ hi]⟩
  · rintro ⟨i, rfl⟩
    refine ⟨l.getD i d, ?_, rfl⟩
    rw [List.getD_eq_getElem _ _ i.isLt]
    exact List.getElem_mem i.isLt

theorem setOf_mem_append {α : Type*} (l₁ l₂ : List α) :
    {v | v ∈ l₁ ++ l₂} = {v | v ∈ l₁} ∪ {v | v ∈ l₂} := by
  ext v
  simp [List.mem_append]

/-! ## The shape of a validated row -/

theorem shapeValid_lengths {r : Rank15ComplementRow} (h : r.shapeValid = true) :
    r.w3.length = r.u3.length ∧ r.w5.length = r.u5.length := by
  simp only [Rank15ComplementRow.shapeValid, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1.1.2, h.1.1.1.2⟩

/-- The glue vectors of a row, listed prime by prime. -/
theorem glueVecs_eq_append {r : Rank15ComplementRow} (h3 : r.w3.length ≤ r.u3.length)
    (h5 : r.w5.length ≤ r.u5.length) :
    r.glueVecs = r.w3.map (glueVec 3) ++ r.w5.map (glueVec 5) := by
  simp only [Rank15ComplementRow.glueVecs, Rank15ComplementRow.glueData, List.map_append,
    List.map_map]
  congr 1
  · rw [show ((fun x : ℤ × ℤ × (ℤ × ℤ × ℤ) => glueVec x.1 x.2.2) ∘
      (fun x : ℤ × (ℤ × ℤ × ℤ) => ((3 : ℤ), x.1, x.2))) = glueVec 3 ∘ Prod.snd from rfl,
      ← List.map_map, List.map_snd_zip h3]
  · rw [show ((fun x : ℤ × ℤ × (ℤ × ℤ × ℤ) => glueVec x.1 x.2.2) ∘
      (fun x : ℤ × (ℤ × ℤ × ℤ) => ((5 : ℤ), x.1, x.2))) = glueVec 5 ∘ Prod.snd from rfl,
      ← List.map_map, List.map_snd_zip h5]

theorem mem_glueData_three {r : Rank15ComplementRow} (h3 : r.w3.length = r.u3.length)
    {i : ℕ} (hi : i < r.u3.length) :
    ((3 : ℤ), r.u3.getD i 0, r.w3.getD i 0) ∈ r.glueData := by
  have hlen : i < (r.u3.zip r.w3).length := by
    rw [List.length_zip, h3]
    omega
  have hget : (r.u3.zip r.w3)[i] = (r.u3[i]'hi, r.w3[i]'(by omega)) := List.getElem_zip
  have hmem : (r.u3.getD i 0, r.w3.getD i 0) ∈ r.u3.zip r.w3 := by
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by omega : i < r.w3.length),
      ← hget]
    exact List.getElem_mem hlen
  exact List.mem_append_left _ (List.mem_map.mpr ⟨_, hmem, rfl⟩)

theorem mem_glueData_five {r : Rank15ComplementRow} (h5 : r.w5.length = r.u5.length)
    {i : ℕ} (hi : i < r.u5.length) :
    ((5 : ℤ), r.u5.getD i 0, r.w5.getD i 0) ∈ r.glueData := by
  have hlen : i < (r.u5.zip r.w5).length := by
    rw [List.length_zip, h5]
    omega
  have hget : (r.u5.zip r.w5)[i] = (r.u5[i]'hi, r.w5[i]'(by omega)) := List.getElem_zip
  have hmem : (r.u5.getD i 0, r.w5.getD i 0) ∈ r.u5.zip r.w5 := by
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by omega : i < r.w5.length),
      ← hget]
    exact List.getElem_mem hlen
  exact List.mem_append_right _ (List.mem_map.mpr ⟨_, hmem, rfl⟩)

/-! ## The normalized discriminant unit of a glue vector -/

section GlueUnit

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable {B : LinearMap.BilinForm ℚ W} {Ñ : Submodule ℤ W} {p : ℕ}

/-- The **normalized discriminant unit** of the `i`-th glue vector: the
representative in `{1, …, p-1}` of `p ⟨yᵢ, yᵢ⟩` modulo `p`, in the
normalization used by the certificate table. -/
def glueUnit (S : Lattice.GlueBasis B Ñ p) (i : Fin S.rank) : ℤ :=
  Lattice.discNum B p (S.vec i) (S.vec i) % (p : ℤ)

/-- The list of normalized discriminant units of a glue basis. -/
def glueUnits (S : Lattice.GlueBasis B Ñ p) : List ℤ := List.ofFn (glueUnit S)

theorem glueUnits_length (S : Lattice.GlueBasis B Ñ p) :
    (glueUnits S).length = S.rank := List.length_ofFn

theorem glueUnits_getD (S : Lattice.GlueBasis B Ñ p) (i : Fin S.rank) :
    (glueUnits S).getD (i : ℕ) 0 = glueUnit S i := by
  rw [List.getD_eq_getElem _ _ (by rw [glueUnits_length]; exact i.isLt)]
  simp [glueUnits, List.getElem_ofFn]

theorem glueUnit_spec (hp : 0 < p) (S : Lattice.GlueBasis B Ñ p) (i : Fin S.rank) :
    ¬ ((p : ℤ) ∣ glueUnit S i) ∧ 0 ≤ glueUnit S i ∧ glueUnit S i < (p : ℤ) ∧
      ∃ k : ℤ, ((p : ℚ)) * B (S.vec i) (S.vec i) = (glueUnit S i : ℚ) + (p : ℚ) * (k : ℚ) := by
  obtain ⟨m, hdvd, hm⟩ := S.diag i
  have hnum : Lattice.discNum B p (S.vec i) (S.vec i) = m :=
    Lattice.discNum_eq_of_cast hm.symm
  have hpz : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    refine hdvd ?_
    rw [glueUnit, hnum] at h
    have hsplit := Int.mul_ediv_add_emod m (p : ℤ)
    exact hsplit ▸ dvd_add (dvd_mul_right _ _) h
  · rw [glueUnit]
    exact Int.emod_nonneg _ (ne_of_gt hpz)
  · rw [glueUnit]
    exact Int.emod_lt_of_pos _ hpz
  · refine ⟨m / (p : ℤ), ?_⟩
    rw [glueUnit, hnum, hm]
    have hz : (p : ℤ) * (m / (p : ℤ)) + m % (p : ℤ) = m := Int.mul_ediv_add_emod m (p : ℤ)
    have hcast := congrArg (fun z : ℤ => (z : ℚ)) hz
    push_cast at hcast
    linarith

theorem glueUnit_mem_one_two (S : Lattice.GlueBasis B Ñ 3) (i : Fin S.rank) :
    glueUnit S i = 1 ∨ glueUnit S i = 2 := by
  obtain ⟨hdvd, hge, hlt, -⟩ := glueUnit_spec (by norm_num) S i
  have hne : glueUnit S i ≠ 0 := by
    intro h
    exact hdvd (h ▸ dvd_zero _)
  have hlt' : glueUnit S i < 3 := by exact_mod_cast hlt
  omega

theorem glueUnit_mem_one_four (S : Lattice.GlueBasis B Ñ 5) (i : Fin S.rank) :
    glueUnit S i = 1 ∨ glueUnit S i = 2 ∨ glueUnit S i = 3 ∨ glueUnit S i = 4 := by
  obtain ⟨hdvd, hge, hlt, -⟩ := glueUnit_spec (by norm_num) S i
  have hne : glueUnit S i ≠ 0 := by
    intro h
    exact hdvd (h ▸ dvd_zero _)
  have hlt' : glueUnit S i < 5 := by exact_mod_cast hlt
  omega

/-- The discriminant data of a pair of glue bases is admissible, so the
certificate table has a row for it. -/
theorem rank15Admissible_glueUnits (S : Lattice.GlueBasis B Ñ 3)
    (T : Lattice.GlueBasis B Ñ 5) : Rank15Admissible (glueUnits S) (glueUnits T) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [glueUnits_length]; exact S.rank_le
  · intro u hu
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
    exact glueUnit_mem_one_two S i
  · rw [glueUnits_length]; exact T.rank_le
  · intro u hu
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
    exact glueUnit_mem_one_four T i

end GlueUnit

/-! ## Matching diagonals -/

/-- **The cancellation lemma.**  If `p x ≡ u` and `p y ≡ -u` modulo `p` with `u`
prime to `p`, then `x + y` is an integer and `a x + b y` is an integer only when
`p ∣ a - b`.  These are exactly the `diag` and `unit` fields of a
`SRG266.Lattice.GlueSystem`. -/
theorem glue_diag_unit {p : ℤ} (hp : Prime p) {x y : ℚ} {u : ℤ} (hu : ¬ p ∣ u)
    (hx : ∃ k : ℤ, (p : ℚ) * x = (u : ℚ) + (p : ℚ) * (k : ℚ))
    (hy : ∃ k : ℤ, (p : ℚ) * y = -(u : ℚ) + (p : ℚ) * (k : ℚ)) :
    (x + y ∈ (1 : Submodule ℤ ℚ)) ∧
      ∀ a b : ℤ, ((a : ℚ) * x + (b : ℚ) * y) ∈ (1 : Submodule ℤ ℚ) → p ∣ a - b := by
  obtain ⟨k₁, hk₁⟩ := hx
  obtain ⟨k₂, hk₂⟩ := hy
  have hp0 : ((p : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr hp.ne_zero
  constructor
  · refine Lattice.mem_one_iff.mpr ⟨k₁ + k₂, ?_⟩
    have : ((p : ℚ)) * (x + y) = (p : ℚ) * ((k₁ + k₂ : ℤ) : ℚ) := by
      push_cast
      linarith
    exact (mul_left_cancel₀ hp0 this).symm
  · intro a b hab
    obtain ⟨N, hN⟩ := Lattice.mem_one_iff.mp hab
    have hq : ((a - b) * u : ℤ) = (p * (N - a * k₁ - b * k₂) : ℤ) := by
      have hcast : (((a - b) * u : ℤ) : ℚ) = ((p * (N - a * k₁ - b * k₂) : ℤ) : ℚ) := by
        push_cast
        linear_combination (-(a : ℚ)) * hk₁ - (b : ℚ) * hk₂ - (p : ℚ) * hN
      exact_mod_cast hcast
    have hdvd : p ∣ (a - b) * u := ⟨_, hq⟩
    exact (hp.dvd_mul.mp hdvd).resolve_right hu

/-! ## The glue system attached to a glue basis and a matching row -/

section Assembly

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable {B : LinearMap.BilinForm ℚ W} {Ñ : Submodule ℤ W}

/-- A rank-12 positive-definite integral lattice carrying
orthogonal glue bases at `3` and `5`, together with a validated complement
certificate row whose discriminant diagonal is the negative of the glue bases',
glues up to a positive-definite odd unimodular lattice of rank 15 in which the
original lattice embeds isometrically. -/
theorem exists_host_of_glueBases_row
    (hsymm : B.IsSymm) (hpd : ∀ v : W, v ≠ 0 → 0 < B v v)
    (hrankW : Module.finrank ℚ W = 12)
    (hlat : Lattice.IsLattice ℚ Ñ) (hint : Lattice.IsIntegral B Ñ)
    (S : Lattice.GlueBasis B Ñ 3) (T : Lattice.GlueBasis B Ñ 5)
    (hsplit : B.dualSubmodule Ñ =
      Ñ ⊔ Submodule.span ℤ (Set.range S.vec ∪ Set.range T.vec))
    (hodd : ∃ z ∈ Ñ, ∃ k : ℤ, ¬ Even k ∧ (k : ℚ) = B z z)
    {r : Rank15ComplementRow} (hr : r ∈ rank15ComplementTable)
    (h3 : r.u3 = glueUnits S) (h5 : r.u5 = glueUnits T) :
    ∃ (L : OddUnimodularLattice15) (e : Ñ →ₗ[ℤ] L.carrier), Function.Injective e ∧
      ∀ u v : Ñ, ((L.pairing (e u) (e v) : ℤ) : ℚ) = B (u : W) (v : W) := by
  classical
  have hvalid : rank15RowValid r = true := rank15ComplementTable_rowValid hr
  obtain ⟨hshape, hsym3, hposd, hdet, hglue, hpp3, hpp5, hgen⟩ :=
    r.rank15RowValid_parts hvalid
  obtain ⟨hw3len, hw5len⟩ := shapeValid_lengths hshape
  have hu3len : r.u3.length = S.rank := by rw [h3, glueUnits_length]
  have hu5len : r.u5.length = T.rank := by rw [h5, glueUnits_length]
  have hformSymm : (r.form).IsSymm := r.form_isSymm hsym3
  -- the two glue families
  set yv : Fin S.rank ⊕ Fin T.rank → W := Sum.elim S.vec T.vec with hyv
  set mv : Fin S.rank ⊕ Fin T.rank → (Fin 3 → ℚ) :=
    Sum.elim (fun i : Fin S.rank => glueVec 3 (r.w3.getD (i : ℕ) 0))
      (fun j : Fin T.rank => glueVec 5 (r.w5.getD (j : ℕ) 0)) with hmv
  set pv : Fin S.rank ⊕ Fin T.rank → ℤ :=
    Sum.elim (fun _ => (3 : ℤ)) (fun _ => (5 : ℤ)) with hpv
  -- the `W`-side dual
  have hdualN : B.dualSubmodule Ñ = Ñ ⊔ Submodule.span ℤ (Set.range yv) := by
    rw [hsplit, hyv, Set.Sum.elim_range]
  have hydual : ∀ i, yv i ∈ B.dualSubmodule Ñ := by
    intro i
    rw [hdualN]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)
  have hysmul : ∀ i, pv i • yv i ∈ Ñ := by
    rintro (i | j)
    · simpa [hyv, hpv] using (Lattice.mem_torsionPart.mp (S.mem i)).2
    · simpa [hyv, hpv] using (Lattice.mem_torsionPart.mp (T.mem j)).2
  -- the `U`-side dual
  have hglueVecs : r.glueVecs = r.w3.map (glueVec 3) ++ r.w5.map (glueVec 5) :=
    glueVecs_eq_append (le_of_eq hw3len) (le_of_eq hw5len)
  have hrange : {v | v ∈ r.glueVecs} = Set.range mv := by
    rw [hglueVecs, setOf_mem_append,
      setOf_mem_map_eq_range r.w3 0 (glueVec 3) (by rw [hw3len, hu3len]),
      setOf_mem_map_eq_range r.w5 0 (glueVec 5) (by rw [hw5len, hu5len]),
      hmv, Set.Sum.elim_range]
  have hdualM : (r.form).dualSubmodule integerCube =
      integerCube ⊔ Submodule.span ℤ (Set.range mv) := by
    rw [rank15Complement_dual_eq hr, Rank15ComplementRow.glueSpan, hrange]
  have hmdual : ∀ i, mv i ∈ (r.form).dualSubmodule integerCube := by
    intro i
    rw [hdualM]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)
  have hmsmul : ∀ i, pv i • mv i ∈ integerCube := by
    rintro (i | j)
    · simpa [hmv, hpv] using
        Rank15ComplementRow.glueVec_zsmul_mem 3 (r.w3.getD (i : ℕ) 0) (by norm_num)
    · simpa [hmv, hpv] using
        Rank15ComplementRow.glueVec_zsmul_mem 5 (r.w5.getD (j : ℕ) 0) (by norm_num)
  -- cross pairings on the `W` side
  have hcop35 : IsCoprime (3 : ℤ) (5 : ℤ) := ⟨2, -1, by norm_num⟩
  have hcop53 : IsCoprime (5 : ℤ) (3 : ℤ) := ⟨-1, 2, by norm_num⟩
  have hcrossW : ∀ i j, i ≠ j → B (yv i) (yv j) ∈ (1 : Submodule ℤ ℚ) := by
    rintro (i | i) (j | j) hij
    · exact S.ortho i j (fun h => hij (by rw [h]))
    · refine Lattice.inner_mem_one_of_coprime hsymm hcop35 (hydual (Sum.inl i)) ?_
        (hydual (Sum.inr j)) ?_
      · simpa [hpv] using hysmul (Sum.inl i)
      · simpa [hpv] using hysmul (Sum.inr j)
    · refine Lattice.inner_mem_one_of_coprime hsymm hcop53 (hydual (Sum.inr i)) ?_
        (hydual (Sum.inl j)) ?_
      · simpa [hpv] using hysmul (Sum.inr i)
      · simpa [hpv] using hysmul (Sum.inl j)
    · exact T.ortho i j (fun h => hij (by rw [h]))
  -- cross pairings on the `U` side
  have hcrossU3 : ∀ i j : Fin S.rank, i ≠ j →
      r.form (glueVec 3 (r.w3.getD (i : ℕ) 0)) (glueVec 3 (r.w3.getD (j : ℕ) 0))
        ∈ (1 : Submodule ℤ ℚ) := by
    intro i j hij
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    have hi := i.isLt
    have hj := j.isLt
    have hle := S.rank_le
    have hlen : r.w3.length = 2 := by rw [hw3len, hu3len]; omega
    obtain ⟨a, c, hac⟩ := List.length_eq_two.mp hlen
    have hortho : r.form (glueVec 3 a) (glueVec 3 c) ∈ (1 : Submodule ℤ ℚ) := by
      refine r.glueVec_ortho (p := 3) (a := a) (b := c) (t := []) (by norm_num) ?_
      rw [← hac]
      exact hpp3
    have hga : r.w3.getD 0 0 = a := by rw [hac]; rfl
    have hgc : r.w3.getD 1 0 = c := by rw [hac]; rfl
    have hcases : ((i : ℕ) = 0 ∧ (j : ℕ) = 1) ∨ ((i : ℕ) = 1 ∧ (j : ℕ) = 0) := by omega
    rcases hcases with ⟨hi0, hj1⟩ | ⟨hi1, hj0⟩
    · rw [hi0, hj1, hga, hgc]
      exact hortho
    · rw [hi1, hj0, hga, hgc, hformSymm.eq]
      exact hortho
  have hcrossU5 : ∀ i j : Fin T.rank, i ≠ j →
      r.form (glueVec 5 (r.w5.getD (i : ℕ) 0)) (glueVec 5 (r.w5.getD (j : ℕ) 0))
        ∈ (1 : Submodule ℤ ℚ) := by
    intro i j hij
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    have hi := i.isLt
    have hj := j.isLt
    have hle := T.rank_le
    have hlen : r.w5.length = 2 := by rw [hw5len, hu5len]; omega
    obtain ⟨a, c, hac⟩ := List.length_eq_two.mp hlen
    have hortho : r.form (glueVec 5 a) (glueVec 5 c) ∈ (1 : Submodule ℤ ℚ) := by
      refine r.glueVec_ortho (p := 5) (a := a) (b := c) (t := []) (by norm_num) ?_
      rw [← hac]
      exact hpp5
    have hga : r.w5.getD 0 0 = a := by rw [hac]; rfl
    have hgc : r.w5.getD 1 0 = c := by rw [hac]; rfl
    have hcases : ((i : ℕ) = 0 ∧ (j : ℕ) = 1) ∨ ((i : ℕ) = 1 ∧ (j : ℕ) = 0) := by omega
    rcases hcases with ⟨hi0, hj1⟩ | ⟨hi1, hj0⟩
    · rw [hi0, hj1, hga, hgc]
      exact hortho
    · rw [hi1, hj0, hga, hgc, hformSymm.eq]
      exact hortho
  have hcrossU : ∀ i j, i ≠ j → r.form (mv i) (mv j) ∈ (1 : Submodule ℤ ℚ) := by
    rintro (i | i) (j | j) hij
    · simpa [hmv] using hcrossU3 i j (fun h => hij (by rw [h]))
    · refine Lattice.inner_mem_one_of_coprime hformSymm hcop35 (hmdual (Sum.inl i)) ?_
        (hmdual (Sum.inr j)) ?_
      · simpa [hpv] using hmsmul (Sum.inl i)
      · simpa [hpv] using hmsmul (Sum.inr j)
    · refine Lattice.inner_mem_one_of_coprime hformSymm hcop53 (hmdual (Sum.inr i)) ?_
        (hmdual (Sum.inl j)) ?_
      · simpa [hpv] using hmsmul (Sum.inr i)
      · simpa [hpv] using hmsmul (Sum.inl j)
    · simpa [hmv] using hcrossU5 i j (fun h => hij (by rw [h]))
  -- matching diagonals
  have hdiagUnit : ∀ i,
      (B (yv i) (yv i) + r.form (mv i) (mv i) ∈ (1 : Submodule ℤ ℚ)) ∧
        ∀ a b : ℤ,
          ((a : ℚ) * B (yv i) (yv i) + (b : ℚ) * r.form (mv i) (mv i))
            ∈ (1 : Submodule ℤ ℚ) → pv i ∣ a - b := by
    rintro (i | j)
    · obtain ⟨hnd, -, -, kW, hkW⟩ := glueUnit_spec (p := 3) (by norm_num) S i
      have hu3i : r.u3.getD (i : ℕ) 0 = glueUnit S i := by rw [h3, glueUnits_getD]
      have hmem3 : ((3 : ℤ), r.u3.getD (i : ℕ) 0, r.w3.getD (i : ℕ) 0) ∈ r.glueData :=
        mem_glueData_three hw3len (by rw [hu3len]; exact i.isLt)
      obtain ⟨kU, hkU⟩ := r.glueVec_diag hglue (by norm_num) hmem3
      rw [hu3i] at hkU
      have hnd' : ¬ ((3 : ℤ) ∣ glueUnit S i) := by simpa using hnd
      have hxW : ∃ k : ℤ, ((3 : ℤ) : ℚ) * B (yv (Sum.inl i)) (yv (Sum.inl i))
          = (glueUnit S i : ℚ) + ((3 : ℤ) : ℚ) * (k : ℚ) := by
        refine ⟨kW, ?_⟩
        simp only [hyv, Sum.elim_inl]
        push_cast at hkW ⊢
        linarith
      have hxU : ∃ k : ℤ, ((3 : ℤ) : ℚ) * r.form (mv (Sum.inl i)) (mv (Sum.inl i))
          = -(glueUnit S i : ℚ) + ((3 : ℤ) : ℚ) * (k : ℚ) := by
        refine ⟨kU, ?_⟩
        simp only [hmv, Sum.elim_inl]
        push_cast at hkU ⊢
        linarith
      have hres := glue_diag_unit (p := 3) (by norm_num) hnd' hxW hxU
      refine ⟨hres.1, ?_⟩
      intro a b hab
      simpa [hpv] using hres.2 a b hab
    · obtain ⟨hnd, -, -, kW, hkW⟩ := glueUnit_spec (p := 5) (by norm_num) T j
      have hu5j : r.u5.getD (j : ℕ) 0 = glueUnit T j := by rw [h5, glueUnits_getD]
      have hmem5 : ((5 : ℤ), r.u5.getD (j : ℕ) 0, r.w5.getD (j : ℕ) 0) ∈ r.glueData :=
        mem_glueData_five hw5len (by rw [hu5len]; exact j.isLt)
      obtain ⟨kU, hkU⟩ := r.glueVec_diag hglue (by norm_num) hmem5
      rw [hu5j] at hkU
      have hnd' : ¬ ((5 : ℤ) ∣ glueUnit T j) := by simpa using hnd
      have hxW : ∃ k : ℤ, ((5 : ℤ) : ℚ) * B (yv (Sum.inr j)) (yv (Sum.inr j))
          = (glueUnit T j : ℚ) + ((5 : ℤ) : ℚ) * (k : ℚ) := by
        refine ⟨kW, ?_⟩
        simp only [hyv, Sum.elim_inr]
        push_cast at hkW ⊢
        linarith
      have hxU : ∃ k : ℤ, ((5 : ℤ) : ℚ) * r.form (mv (Sum.inr j)) (mv (Sum.inr j))
          = -(glueUnit T j : ℚ) + ((5 : ℤ) : ℚ) * (k : ℚ) := by
        refine ⟨kU, ?_⟩
        simp only [hmv, Sum.elim_inr]
        push_cast at hkU ⊢
        linarith
      have hres := glue_diag_unit (p := 5) (by norm_num) hnd' hxW hxU
      refine ⟨hres.1, ?_⟩
      intro a b hab
      simpa [hpv] using hres.2 a b hab
  -- the glue system
  obtain ⟨Sys⟩ : Nonempty
      (Lattice.GlueSystem B r.form Ñ integerCube (Fin S.rank ⊕ Fin T.rank)) :=
    ⟨{ y := yv
       m := mv
       pr := pv
       symmB := hsymm
       symmC := hformSymm
       intN := hint
       intM := r.integerCube_isIntegral
       dualN := hdualN
       dualM := hdualM
       smul_mem := hmsmul
       crossW := hcrossW
       crossU := hcrossU
       diag := fun i => (hdiagUnit i).1
       unit := fun i => (hdiagUnit i).2 }⟩
  -- the glued lattice is unimodular of rank 15
  obtain ⟨nW, bW, -⟩ := Lattice.exists_basis_of_isLattice hlat
  haveI : Module.Finite ℚ W := Module.Finite.of_basis bW
  have hrank15 : Module.finrank ℚ (W × (Fin 3 → ℚ)) = 15 := by
    rw [Module.finrank_prod, hrankW, Module.finrank_fin_fun]
  exact Sys.exists_host hpd (rank15Complement_posDef hr) hlat integerCube_isLattice
    hrank15 hodd

/-- The certificate row is supplied by the
147-row complement table, so only the two glue bases are needed. -/
theorem exists_host_of_glueBases
    (hsymm : B.IsSymm) (hpd : ∀ v : W, v ≠ 0 → 0 < B v v)
    (hrankW : Module.finrank ℚ W = 12)
    (hlat : Lattice.IsLattice ℚ Ñ) (hint : Lattice.IsIntegral B Ñ)
    (S : Lattice.GlueBasis B Ñ 3) (T : Lattice.GlueBasis B Ñ 5)
    (hsplit : B.dualSubmodule Ñ =
      Ñ ⊔ Submodule.span ℤ (Set.range S.vec ∪ Set.range T.vec))
    (hodd : ∃ z ∈ Ñ, ∃ k : ℤ, ¬ Even k ∧ (k : ℚ) = B z z) :
    ∃ (L : OddUnimodularLattice15) (e : Ñ →ₗ[ℤ] L.carrier), Function.Injective e ∧
      ∀ u v : Ñ, ((L.pairing (e u) (e v) : ℤ) : ℚ) = B (u : W) (v : W) := by
  obtain ⟨r, hr, h3, h5, -⟩ :=
    exists_rank15ComplementRow (rank15Admissible_glueUnits S T)
  exact exists_host_of_glueBases_row hsymm hpd hrankW hlat hint S T hsplit hodd hr h3 h5

end Assembly

end SRG266
