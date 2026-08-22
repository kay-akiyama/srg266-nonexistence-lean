/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.ProjectorClasses

/-!
# Finite shell realizations of the local Gram configuration

This module extracts the host-independent counting consequences of a map from
the 220 local Gram occurrences into a finite norm-three shell.

If shell inner product three detects equality, the fibers of the shell map
are exactly the Gram-equivalence classes.  The native local theory therefore
gives:

* total multiplicity 220;
* multiplicity at most three;
* the weighted inner-product-two equation
  `count₂(u) + 3 multiplicity(u) = 30`;
* nonnegative inner products between selected shell vectors.

These facts are the common input expected by the E7 and A15 residual
eliminations.
-/

open scoped BigOperators

namespace SRG266

set_option maxRecDepth 100000

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A realization of the local Gram occurrences in a finite shell. -/
structure FiniteShellGramRealization
    (x : V) (S : Type v) [Fintype S] [DecidableEq S]
    (inner : S → S → ℤ) where
  shell : SecondSubconstituent G x → S
  gram :
    ∀ B C, inner (shell B) (shell C) =
      localGramMatrix G x B C
  eq_of_inner_eq_three :
    ∀ s t, inner s t = 3 → s = t

variable {S : Type v} [Fintype S] [DecidableEq S]
variable {inner : S → S → ℤ}

/-- Multiplicity of one shell vector among the 220 local occurrences. -/
def FiniteShellGramRealization.multiplicity
    {x : V}
    (realization : FiniteShellGramRealization G x S inner)
    (s : S) : ℕ :=
  (Finset.univ.filter fun B => realization.shell B = s).card

theorem FiniteShellGramRealization.multiplicity_eq_card_fiber
    {x : V}
    (realization : FiniteShellGramRealization G x S inner)
    (s : S) :
    realization.multiplicity G s =
      (Finset.univ.filter fun B => realization.shell B = s).card := by
  rfl

/-- Every local occurrence belongs to exactly one shell fiber. -/
theorem FiniteShellGramRealization.sum_multiplicity
    {x : V}
    (realization : FiniteShellGramRealization G x S inner) :
    ∑ s, realization.multiplicity G s =
      Fintype.card (SecondSubconstituent G x) := by
  have hfibers :=
    Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (SecondSubconstituent G x)))
      (t := (Finset.univ : Finset S))
      (f := realization.shell)
      (by simp)
  change
    (∑ s : S,
      (Finset.univ.filter fun B => realization.shell B = s).card) =
      (Finset.univ :
        Finset (SecondSubconstituent G x)).card
  simpa only [Finset.sum_filter, Finset.mem_univ, if_true] using
    hfibers.symm

/-- Regroup a weighted sum over local occurrences by shell fibers. -/
theorem FiniteShellGramRealization.sum_multiplicity_mul
    {x : V}
    (realization : FiniteShellGramRealization G x S inner)
    (f : S → ℤ) :
    (∑ s, (realization.multiplicity G s : ℤ) * f s) =
      ∑ B, f (realization.shell B) := by
  calc
    _ = ∑ s : S,
        ∑ B ∈ Finset.univ.filter
          (fun B => realization.shell B = s), f s := by
      apply Finset.sum_congr rfl
      intro s _
      simp only [FiniteShellGramRealization.multiplicity,
        Finset.sum_const, nsmul_eq_mul]
    _ = _ := by
      simpa only [Finset.filter_eq', Finset.mem_univ, ↓reduceIte] using
        (Finset.sum_fiberwise'
          (Finset.univ : Finset (SecondSubconstituent G x))
          realization.shell f)

/-- A shell fiber through `B` is exactly its Gram-equivalence class. -/
theorem FiniteShellGramRealization.fiber_eq_gramClass
    (hG : IsHypothetical G) (x : V)
    (realization : FiniteShellGramRealization G x S inner)
    (B : SecondSubconstituent G x) :
    (Finset.univ.filter fun C =>
      realization.shell C = realization.shell B) =
      gramClass G x B := by
  classical
  ext C
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    mem_gramClass, gramEquivalent_iff_entry_eq_three G hG x B C]
  constructor
  · intro hshell
    rw [← realization.gram B C, hshell]
    exact realization.gram B B |>.trans
      (localGramMatrix_diagonal G hG x B)
  · intro hthree
    apply realization.eq_of_inner_eq_three
    rw [realization.gram C B, localGramMatrix_comm G x C B]
    exact hthree

/-- Positive multiplicity provides a local occurrence in that fiber. -/
theorem FiniteShellGramRealization.exists_shell_eq_of_pos
    {x : V}
    (realization : FiniteShellGramRealization G x S inner)
    {s : S} (hpos : 0 < realization.multiplicity G s) :
    ∃ B, realization.shell B = s := by
  rw [FiniteShellGramRealization.multiplicity,
    Finset.card_pos] at hpos
  obtain ⟨B, hB⟩ := hpos
  exact ⟨B, (Finset.mem_filter.mp hB).2⟩

/-- Shell multiplicities are the local Gram-class sizes and hence at most
three. -/
theorem FiniteShellGramRealization.multiplicity_le_three
    (hG : IsHypothetical G) (x : V)
    (realization : FiniteShellGramRealization G x S inner)
    (s : S) :
    realization.multiplicity G s ≤ 3 := by
  by_cases hzero : realization.multiplicity G s = 0
  · simp [hzero]
  · obtain ⟨B, hshell⟩ :=
      realization.exists_shell_eq_of_pos G (Nat.pos_of_ne_zero hzero)
    rw [FiniteShellGramRealization.multiplicity, ← hshell,
      realization.fiber_eq_gramClass G hG x B]
    exact gramClass_card_le_three G hG x B

/-- The support of a shell realization has at least 74 distinct vectors.

There are 220 local occurrences and every shell fiber has size at most
three, so `220 ≤ 3 * #support`.  This is the host-independent source of the
threshold used by both centroid enumerations. -/
theorem FiniteShellGramRealization.seventyFour_le_support_card
    (hG : IsHypothetical G) (x : V)
    (realization : FiniteShellGramRealization G x S inner) :
    74 ≤
      (Finset.univ.filter
        (fun s => 0 < realization.multiplicity G s)).card := by
  let support :=
    Finset.univ.filter
      (fun s => 0 < realization.multiplicity G s)
  have hsumSupport :
      ∑ s ∈ support, realization.multiplicity G s =
        Fintype.card (SecondSubconstituent G x) := by
    rw [← realization.sum_multiplicity G]
    apply Finset.sum_subset (Finset.subset_univ support)
    intro s _ hs
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    exact (Nat.not_lt.mp hs).antisymm (Nat.zero_le _)
  have hsumLe :
      ∑ s ∈ support, realization.multiplicity G s ≤
        ∑ _s ∈ support, 3 := by
    apply Finset.sum_le_sum
    intro s hs
    exact realization.multiplicity_le_three G hG x s
  have hcard :
      Fintype.card (SecondSubconstituent G x) ≤ 3 * support.card := by
    rw [← hsumSupport]
    calc
      _ ≤ ∑ _s ∈ support, 3 := hsumLe
      _ = 3 * support.card := by simp [Nat.mul_comm]
  rw [secondSubconstituent_card G hG x] at hcard
  have hsupport : 74 ≤ support.card := by omega
  simpa only [support] using hsupport

private theorem FiniteShellGramRealization.sum_multiplicity_filter
    {x : V}
    (realization : FiniteShellGramRealization G x S inner)
    (t : Finset S) :
    (∑ s ∈ t, realization.multiplicity G s) =
      ((Finset.univ.filter fun B => realization.shell B ∈ t).card) := by
  exact
    Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (SecondSubconstituent G x))
      t realization.shell

/-- The weighted number of shell vectors with inner product two is the
corresponding local Gram-row count. -/
theorem FiniteShellGramRealization.sum_inner_two
    (x : V)
    (realization : FiniteShellGramRealization G x S inner)
    (B : SecondSubconstituent G x) :
    (∑ s ∈ Finset.univ.filter
        (fun s => inner (realization.shell B) s = 2),
        realization.multiplicity G s) =
      (gramEntryIndices G x B 2).card := by
  rw [realization.sum_multiplicity_filter G]
  congr 1
  ext C
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    mem_gramEntryIndices]
  rw [realization.gram B C]

/-- The shell form of the local weighted inner-product profile. -/
theorem FiniteShellGramRealization.twoProfile
    (hG : IsHypothetical G) (x : V)
    (realization : FiniteShellGramRealization G x S inner)
    (s : S) (hpos : 0 < realization.multiplicity G s) :
    (∑ t ∈ Finset.univ.filter (fun t => inner s t = 2),
        realization.multiplicity G t) +
      3 * realization.multiplicity G s = 30 := by
  obtain ⟨B, hshell⟩ :=
    realization.exists_shell_eq_of_pos G hpos
  rw [← hshell, realization.sum_inner_two G x B,
    FiniteShellGramRealization.multiplicity,
    realization.fiber_eq_gramClass G hG x B]
  exact gramEntryTwo_card_add_three_mul_class_card G hG x B

/-- Selected shell vectors have nonnegative inner product. -/
theorem FiniteShellGramRealization.nonnegative
    (hG : IsHypothetical G) (x : V)
    (realization : FiniteShellGramRealization G x S inner)
    (s t : S)
    (hs : 0 < realization.multiplicity G s)
    (ht : 0 < realization.multiplicity G t) :
    0 ≤ inner s t := by
  obtain ⟨B, hB⟩ := realization.exists_shell_eq_of_pos G hs
  obtain ⟨C, hC⟩ := realization.exists_shell_eq_of_pos G ht
  rw [← hB, ← hC, realization.gram B C]
  exact (localGramMatrix_bounds G hG x B C).1

end SRG266
