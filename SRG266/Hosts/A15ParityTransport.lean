/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.A15Residual

/-!
# Transport of the two sign-paired A15 survivors

The projector survivors at indices 1 and 8 each contain a distinguished
56-element orbit of total multiplicity 55.  `A15PackingReduction` identifies
that orbit with the triples of an eight-set and proves that:

* the triple pair kernel is exactly the shell inner-product-two relation,
  with coefficient three on the diagonal;
* no shell vector in the other 120-element orbit has inner product two with
  a distinguished vector.

This module first proves an abstract transport theorem for any finite shell
with those properties.  The two concrete profiles then instantiate only that
small interface, avoiding large dependent proof terms over the 1,820-subset
universe.
-/

open scoped BigOperators

namespace SRG266

set_option maxRecDepth 100000

universe u v

private def a15LocalPairKernel
    {S : Type v} [DecidableEq S]
    (inner : S → S → ℤ) (s t : S) : ℕ :=
  if s = t then 3 else if inner s t = 2 then 1 else 0

private theorem a15LocalPairKernel_sum
    {S : Type v} [Fintype S] [DecidableEq S]
    (inner : S → S → ℤ) (m : S → ℕ) (s : S)
    (hself : inner s s ≠ 2) :
    (∑ t, a15LocalPairKernel inner s t * m t) =
      (∑ t ∈ Finset.univ.filter (fun t => inner s t = 2), m t) +
        3 * m s := by
  calc
    _ = ∑ t : S, (
        (if inner s t = 2 then m t else 0) +
          (if t = s then 3 * m t else 0)) := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases hst : s = t
      · subst t
        simp [a15LocalPairKernel, hself]
      · have hts : t ≠ s := fun h => hst h.symm
        by_cases hinner : inner s t = 2 <;>
          simp [a15LocalPairKernel, hst, hts, hinner]
    _ = (∑ t : S, if inner s t = 2 then m t else 0) +
        ∑ t : S, if t = s then 3 * m t else 0 := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp

/-- Abstract shell-to-triple transport used by both sign-paired profiles. -/
private noncomputable def a15ParityPackingOfShell
    {S : Type v} [Fintype S] [DecidableEq S]
    (inner : S → S → ℤ) (m : S → ℕ)
    (P : S → Prop) [DecidablePred P]
    (e : A15ParityTriple ≃ {s : S // P s})
    (hkernel :
      ∀ s t : {s : S // P s},
        a15ParityPairKernel (e.symm s) (e.symm t) =
          a15LocalPairKernel inner s.1 t.1)
    (hcross :
      ∀ (s : {s : S // P s}) (t : S), ¬P t → inner s.1 t ≠ 2)
    (htotal : ∑ s : {s : S // P s}, m s.1 = 55)
    (hself :
      ∀ s : {s : S // P s}, 0 < m s.1 → inner s.1 s.1 ≠ 2)
    (hprofile :
      ∀ s : {s : S // P s}, 0 < m s.1 →
        (∑ t ∈ Finset.univ.filter (fun t => inner s.1 t = 2), m t) +
          3 * m s.1 = 30) :
    A15ParityPacking := by
  let multiplicity : A15ParityTriple → ℕ :=
    fun t => m (e t).1
  refine
    { multiplicity := multiplicity
      total := ?_
      frame := ?_ }
  · exact (e.sum_comp (fun s : {s : S // P s} => m s.1)).trans htotal
  · intro t ht
    let s : {s : S // P s} := e t
    have hspos : 0 < m s.1 := by
      simpa only [multiplicity, s] using ht
    rw [a15ParityTriplePairSum_eq_kernel_sum]
    calc
      (∑ u, a15ParityPairKernel t u * multiplicity u) =
          ∑ r : {s : S // P s},
            a15ParityPairKernel (e.symm s) (e.symm r) * m r.1 := by
        have hequiv :=
          e.sum_comp (fun r : {s : S // P s} =>
            a15ParityPairKernel (e.symm s) (e.symm r) * m r.1)
        simpa only [multiplicity, s, e.symm_apply_apply] using hequiv
      _ = ∑ r : {s : S // P s},
          a15LocalPairKernel inner s.1 r.1 * m r.1 := by
        apply Finset.sum_congr rfl
        intro r _
        rw [hkernel s r]
      _ = ∑ r : S, a15LocalPairKernel inner s.1 r * m r := by
        symm
        calc
          _ = ∑ r : S,
              if P r then a15LocalPairKernel inner s.1 r * m r else 0 := by
            apply Finset.sum_congr rfl
            intro r _
            by_cases hr : P r
            · simp [hr]
            · have hne : s.1 ≠ r := by
                intro hsr
                subst r
                exact hr s.2
              have hnotTwo := hcross s r hr
              simp [hr, a15LocalPairKernel, hne, hnotTwo]
          _ = ∑ r ∈ Finset.univ.filter P,
              a15LocalPairKernel inner s.1 r * m r := by
            rw [Finset.sum_filter]
          _ = _ := by
            apply Finset.sum_subtype
            intro r
            simp
      _ = (∑ r ∈ Finset.univ.filter (fun r => inner s.1 r = 2), m r) +
          3 * m s.1 :=
        a15LocalPairKernel_sum inner m s.1 (hself s hspos)
      _ = 30 := hprofile s hspos

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The profile-1 55-orbit produces the weighted-triple endpoint. -/
noncomputable def A15ShellGramRealization.profile1_parityPacking
    (hG : IsHypothetical G) (x : V)
    (realization :
      A15ShellGramRealization G x a15ParityProfile1)
    (hBtotal :
      ∑ s : A15ParityBIndex1,
        (realization.toFiniteShell G).multiplicity G s.1 = 55) :
    A15ParityPacking := by
  let finite := realization.toFiniteShell G
  apply a15ParityPackingOfShell
    (a15ShellInner a15ParityProfile1) (finite.multiplicity G)
    (fun s => a15SubsetContains s 15) a15ParityShellEquiv1
  · intro s t
    change
      a15ParityPairKernel (a15ParityTriple1 s) (a15ParityTriple1 t) =
        a15LocalPairKernel (a15ShellInner a15ParityProfile1) s.1 t.1
    simpa only [a15LocalPairKernel, Subtype.ext_iff] using
      a15ParityProfile1_kernel s t
  · exact a15ParityProfile1_no_cross_two
  · exact hBtotal
  · intro s hspos
    obtain ⟨B, hB⟩ := finite.exists_shell_eq_of_pos G hspos
    have hdiag :
        a15ShellInner a15ParityProfile1 s.1 s.1 = 3 := by
      rw [← hB, finite.gram B B,
        localGramMatrix_diagonal G hG x B]
    omega
  · intro s hspos
    exact finite.twoProfile G hG x s.1 hspos

/-- The profile-8 55-orbit produces the same weighted-triple endpoint. -/
noncomputable def A15ShellGramRealization.profile8_parityPacking
    (hG : IsHypothetical G) (x : V)
    (realization :
      A15ShellGramRealization G x a15ParityProfile8)
    (hBtotal :
      ∑ s : A15ParityBIndex8,
        (realization.toFiniteShell G).multiplicity G s.1 = 55) :
    A15ParityPacking := by
  let finite := realization.toFiniteShell G
  apply a15ParityPackingOfShell
    (a15ShellInner a15ParityProfile8) (finite.multiplicity G)
    (fun s => a15SubsetContains s 0) a15ParityShellEquiv8
  · intro s t
    change
      a15ParityPairKernel (a15ParityTriple8 s) (a15ParityTriple8 t) =
        a15LocalPairKernel (a15ShellInner a15ParityProfile8) s.1 t.1
    simpa only [a15LocalPairKernel, Subtype.ext_iff] using
      a15ParityProfile8_kernel s t
  · exact a15ParityProfile8_no_cross_two
  · exact hBtotal
  · intro s hspos
    obtain ⟨B, hB⟩ := finite.exists_shell_eq_of_pos G hspos
    have hdiag :
        a15ShellInner a15ParityProfile8 s.1 s.1 = 3 := by
      rw [← hB, finite.gram B B,
        localGramMatrix_diagonal G hG x B]
    omega
  · intro s hspos
    exact finite.twoProfile G hG x s.1 hspos

/-- Package profile 1 directly as the parity branch of the assembled A15
residual endpoint. -/
noncomputable def A15ShellGramRealization.profile1_residualCase
    (hG : IsHypothetical G) (x : V)
    (realization :
      A15ShellGramRealization G x a15ParityProfile1)
    (hBtotal :
      ∑ s : A15ParityBIndex1,
        (realization.toFiniteShell G).multiplicity G s.1 = 55) :
    A15ResidualCase G x :=
  .parity (realization.profile1_parityPacking G hG x hBtotal)

/-- Package profile 8 directly as the parity branch of the assembled A15
residual endpoint. -/
noncomputable def A15ShellGramRealization.profile8_residualCase
    (hG : IsHypothetical G) (x : V)
    (realization :
      A15ShellGramRealization G x a15ParityProfile8)
    (hBtotal :
      ∑ s : A15ParityBIndex8,
        (realization.toFiniteShell G).multiplicity G s.1 = 55) :
    A15ResidualCase G x :=
  .parity (realization.profile8_parityPacking G hG x hBtotal)

/-- The four concrete A15 shell cases, carrying the direct host realization
and selected-orbit conclusion. -/
inductive A15FinalShellCase (x : V)
  | profile0
      (realization :
        A15ShellGramRealization G x a15BinaryProfile0)
      (selected :
        ∀ B, a15SubsetContains (realization.shell B) 0)
  | profile1
      (realization :
        A15ShellGramRealization G x a15ParityProfile1)
      (orbitTotal :
        ∑ s : A15ParityBIndex1,
          (realization.toFiniteShell G).multiplicity G s.1 = 55)
  | profile8
      (realization :
        A15ShellGramRealization G x a15ParityProfile8)
      (orbitTotal :
        ∑ s : A15ParityBIndex8,
          (realization.toFiniteShell G).multiplicity G s.1 = 55)
  | profile12
      (realization :
        A15ShellGramRealization G x a15BinaryProfile12)
      (selected :
        ∀ B, a15SubsetContains (realization.shell B) 15)

/-- Transport any of the four concrete final shell cases to its native
binary/parity endpoint. -/
noncomputable def A15FinalShellCase.toResidualCase
    (hG : IsHypothetical G) (x : V)
    (finalCase : A15FinalShellCase G x) :
    A15ResidualCase G x := by
  cases finalCase with
  | profile0 realization selected =>
      exact realization.profile0_residualCase G selected
  | profile1 realization orbitTotal =>
      exact realization.profile1_residualCase G hG x orbitTotal
  | profile8 realization orbitTotal =>
      exact realization.profile8_residualCase G hG x orbitTotal
  | profile12 realization selected =>
      exact realization.profile12_residualCase G selected

/-- All four coordinate-level final A15 shell cases are impossible. -/
theorem no_a15FinalShellCase
    (hMT : NoQuasiSymmetricDesign56.{u})
    (hG : IsHypothetical G) (x : V) :
    IsEmpty (A15FinalShellCase G x) := by
  refine ⟨fun finalCase => ?_⟩
  exact
    (no_a15ResidualCase G hMT hG x).false
      (finalCase.toResidualCase G hG x)

end SRG266
