/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15FinalTransportTheory

/-!
# Transport from checked A15 projector survivors

The projector checker leaves four exact `(centroid index, orbit totals)`
pairs.  This module identifies those four certificate profiles with the
coordinate models consumed by the binary and parity endpoints, and derives
the selected-orbit hypotheses from the direct shell multiplicities.

The profile equalities are coordinatewise, while the orbit-predicate
identifications use the checked unique-orbit property and the singleton
coordinate classes of the four surviving profiles.
-/

open scoped BigOperators

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem A15ShellGramRealization.shell_multiplicity_pos
    {x : V} {d : Fin 16 → ℤ}
    (realization : A15ShellGramRealization G x d)
    (B : SecondSubconstituent G x) :
    0 <
      (realization.toFiniteShell G).multiplicity G
        (realization.shell B) := by
  change
    0 <
      (Finset.univ.filter fun C =>
        realization.shell C = realization.shell B).card
  rw [Finset.card_pos]
  exact ⟨B, by simp⟩

private theorem A15ShellGramRealization.cast_shell
    {x : V} {d e : Fin 16 → ℤ}
    (h : d = e) (realization : A15ShellGramRealization G x d)
    (B : SecondSubconstituent G x) :
    (h ▸ realization).shell B = h ▸ realization.shell B := by
  subst e
  rfl

private theorem A15ShellGramRealization.cast_multiplicity
    {x : V} {d e : Fin 16 → ℤ}
    (h : d = e) (realization : A15ShellGramRealization G x d)
    (s : A15EligibleIndex d) :
    ((h ▸ realization).toFiniteShell G).multiplicity G
        (Equiv.cast (congrArg A15EligibleIndex h) s) =
      (realization.toFiniteShell G).multiplicity G s := by
  subst e
  rfl

private theorem A15ShellGramRealization.projectorOrbitTotal_eq
    {x : V} (profile : A15ProjectorProfile)
    (realization :
      A15ShellGramRealization G x profile.centroidVector)
    (k : Fin profile.orbits.size) :
    (realization.projectorOrbitTotals G profile).getD k.1 0 =
      ∑ s ∈ profile.orbitIndexFinset k.1,
        (realization.toFiniteShell G).multiplicity G s := by
  simp [A15ShellGramRealization.projectorOrbitTotals, k.isLt]

def a15ProjectorProfile01_orbitEquiv :
    {s : A15EligibleIndex
        a15ProjectorProfile01.profile.centroidVector //
      a15ProjectorProfile01.profile.indexMatches 0 s.1} ≃
      A15ParityBIndex1 :=
  (Equiv.cast (congrArg A15EligibleIndex
    a15ProjectorProfile01_centroidVector)).subtypeEquiv
      a15ProjectorProfile01_orbit0_cast_iff

def a15ProjectorProfile08_orbitEquiv :
    {s : A15EligibleIndex
        a15ProjectorProfile08.profile.centroidVector //
      a15ProjectorProfile08.profile.indexMatches 1 s.1} ≃
      A15ParityBIndex8 :=
  (Equiv.cast (congrArg A15EligibleIndex
    a15ProjectorProfile08_centroidVector)).subtypeEquiv
      a15ProjectorProfile08_orbit1_cast_iff

/-- The zero first orbit of survivor 0 forces every selected shell vector
to contain coordinate zero. -/
theorem A15ShellGramRealization.profile00_selected
    {x : V}
    (realization :
      A15ShellGramRealization G x
        a15ProjectorProfile00.profile.centroidVector)
    (htotals :
      realization.projectorOrbitTotals G a15ProjectorProfile00.profile =
        #[0, 220]) :
    ∀ B,
      a15SubsetContains
        ((a15ProjectorProfile00_centroidVector ▸ realization).shell B) 0 := by
  intro B
  let finite := realization.toFiniteShell G
  let s :
      A15EligibleIndex
        a15ProjectorProfile00.profile.centroidVector :=
    realization.shell B
  by_contra hselected
  have horbit :
      a15ProjectorProfile00.profile.indexMatches 0 s.1 := by
    rw [a15ProjectorProfile00_orbit0_iff s]
    rw [← realization.cast_shell G
      a15ProjectorProfile00_centroidVector B]
    exact hselected
  have hmem :
      s ∈ a15ProjectorProfile00.profile.orbitIndexFinset 0 := by
    simp [A15ProjectorProfile.orbitIndexFinset, horbit]
  have hzero :
      ∑ t ∈ a15ProjectorProfile00.profile.orbitIndexFinset 0,
        finite.multiplicity G t = 0 := by
    have hentry :
        (realization.projectorOrbitTotals G
          a15ProjectorProfile00.profile).getD 0 0 = 0 := by
      rw [htotals]
      decide
    have hi :
        0 <
          (realization.projectorOrbitTotals G
            a15ProjectorProfile00.profile).size := by
      rw [realization.projectorOrbitTotals_size G]
      decide
    rw [← Array.getElem_eq_getD (h := hi) 0] at hentry
    simpa only [A15ShellGramRealization.projectorOrbitTotals,
      Array.getElem_ofFn, finite] using hentry
  have hle :
      finite.multiplicity G s ≤
        ∑ t ∈ a15ProjectorProfile00.profile.orbitIndexFinset 0,
          finite.multiplicity G t :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
  have hpos : 0 < finite.multiplicity G s := by
    exact realization.shell_multiplicity_pos G B
  omega

/-- The zero second orbit of survivor 12 forces every selected shell vector
to contain coordinate 15. -/
theorem A15ShellGramRealization.profile12_selected
    {x : V}
    (realization :
      A15ShellGramRealization G x
        a15ProjectorProfile12.profile.centroidVector)
    (htotals :
      realization.projectorOrbitTotals G a15ProjectorProfile12.profile =
        #[220, 0]) :
    ∀ B,
      a15SubsetContains
        ((a15ProjectorProfile12_centroidVector ▸ realization).shell B) 15 := by
  intro B
  let finite := realization.toFiniteShell G
  let s :
      A15EligibleIndex
        a15ProjectorProfile12.profile.centroidVector :=
    realization.shell B
  by_contra hselected
  have horbit :
      a15ProjectorProfile12.profile.indexMatches 1 s.1 := by
    rw [a15ProjectorProfile12_orbit1_iff s]
    rw [← realization.cast_shell G
      a15ProjectorProfile12_centroidVector B]
    exact hselected
  have hmem :
      s ∈ a15ProjectorProfile12.profile.orbitIndexFinset 1 := by
    simp [A15ProjectorProfile.orbitIndexFinset, horbit]
  have hzero :
      ∑ t ∈ a15ProjectorProfile12.profile.orbitIndexFinset 1,
        finite.multiplicity G t = 0 := by
    have hentry :
        (realization.projectorOrbitTotals G
          a15ProjectorProfile12.profile).getD 1 0 = 0 := by
      rw [htotals]
      decide
    have hi :
        1 <
          (realization.projectorOrbitTotals G
            a15ProjectorProfile12.profile).size := by
      rw [realization.projectorOrbitTotals_size G]
      decide
    rw [← Array.getElem_eq_getD (h := hi) 0] at hentry
    simpa only [A15ShellGramRealization.projectorOrbitTotals,
      Array.getElem_ofFn, finite] using hentry
  have hle :
      finite.multiplicity G s ≤
        ∑ t ∈ a15ProjectorProfile12.profile.orbitIndexFinset 1,
          finite.multiplicity G t :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
  have hpos : 0 < finite.multiplicity G s := by
    exact realization.shell_multiplicity_pos G B
  omega

/-- Survivor 1's first projector orbit is exactly the parity orbit through
coordinate 15, so its checked orbit total becomes the required weighted
triple total. -/
theorem A15ShellGramRealization.profile01_orbitTotal
    {x : V}
    (realization :
      A15ShellGramRealization G x
        a15ProjectorProfile01.profile.centroidVector)
    (htotals :
      realization.projectorOrbitTotals G a15ProjectorProfile01.profile =
        #[55, 165]) :
    ∑ s : A15ParityBIndex1,
      ((a15ProjectorProfile01_centroidVector ▸
          realization).toFiniteShell G).multiplicity G s.1 = 55 := by
  let finite := realization.toFiniteShell G
  let castRealization :=
    a15ProjectorProfile01_centroidVector ▸ realization
  have horbit :
      (∑ s : {s : A15EligibleIndex
            a15ProjectorProfile01.profile.centroidVector //
          a15ProjectorProfile01.profile.indexMatches 0 s.1},
        finite.multiplicity G s.1) = 55 := by
    have hentry :
        (realization.projectorOrbitTotals G
          a15ProjectorProfile01.profile).getD 0 0 = 55 := by
      rw [htotals]
      decide
    rw [realization.projectorOrbitTotal_eq G
      a15ProjectorProfile01.profile ⟨0, by decide⟩] at hentry
    calc
      _ = ∑ s ∈
          a15ProjectorProfile01.profile.orbitIndexFinset 0,
            finite.multiplicity G s := by
        symm
        apply Finset.sum_subtype
        intro s
        simp [A15ProjectorProfile.orbitIndexFinset]
      _ = 55 := hentry
  calc
    _ = ∑ s : {s : A15EligibleIndex
          a15ProjectorProfile01.profile.centroidVector //
        a15ProjectorProfile01.profile.indexMatches 0 s.1},
        (castRealization.toFiniteShell G).multiplicity G
          (a15ProjectorProfile01_orbitEquiv s).1 := by
      exact
        (a15ProjectorProfile01_orbitEquiv.sum_comp
          (fun s : A15ParityBIndex1 =>
            (castRealization.toFiniteShell G).multiplicity G s.1)).symm
    _ = ∑ s : {s : A15EligibleIndex
          a15ProjectorProfile01.profile.centroidVector //
        a15ProjectorProfile01.profile.indexMatches 0 s.1},
        finite.multiplicity G s.1 := by
      apply Finset.sum_congr rfl
      intro s _
      exact realization.cast_multiplicity G
        a15ProjectorProfile01_centroidVector s.1
    _ = 55 := horbit

/-- Survivor 8's second projector orbit is exactly the parity orbit through
coordinate zero. -/
theorem A15ShellGramRealization.profile08_orbitTotal
    {x : V}
    (realization :
      A15ShellGramRealization G x
        a15ProjectorProfile08.profile.centroidVector)
    (htotals :
      realization.projectorOrbitTotals G a15ProjectorProfile08.profile =
        #[165, 55]) :
    ∑ s : A15ParityBIndex8,
      ((a15ProjectorProfile08_centroidVector ▸
          realization).toFiniteShell G).multiplicity G s.1 = 55 := by
  let finite := realization.toFiniteShell G
  let castRealization :=
    a15ProjectorProfile08_centroidVector ▸ realization
  have horbit :
      (∑ s : {s : A15EligibleIndex
            a15ProjectorProfile08.profile.centroidVector //
          a15ProjectorProfile08.profile.indexMatches 1 s.1},
        finite.multiplicity G s.1) = 55 := by
    have hentry :
        (realization.projectorOrbitTotals G
          a15ProjectorProfile08.profile).getD 1 0 = 55 := by
      rw [htotals]
      decide
    rw [realization.projectorOrbitTotal_eq G
      a15ProjectorProfile08.profile ⟨1, by decide⟩] at hentry
    calc
      _ = ∑ s ∈
          a15ProjectorProfile08.profile.orbitIndexFinset 1,
            finite.multiplicity G s := by
        symm
        apply Finset.sum_subtype
        intro s
        simp [A15ProjectorProfile.orbitIndexFinset]
      _ = 55 := hentry
  calc
    _ = ∑ s : {s : A15EligibleIndex
          a15ProjectorProfile08.profile.centroidVector //
        a15ProjectorProfile08.profile.indexMatches 1 s.1},
        (castRealization.toFiniteShell G).multiplicity G
          (a15ProjectorProfile08_orbitEquiv s).1 := by
      exact
        (a15ProjectorProfile08_orbitEquiv.sum_comp
          (fun s : A15ParityBIndex8 =>
            (castRealization.toFiniteShell G).multiplicity G s.1)).symm
    _ = ∑ s : {s : A15EligibleIndex
          a15ProjectorProfile08.profile.centroidVector //
        a15ProjectorProfile08.profile.indexMatches 1 s.1},
        finite.multiplicity G s.1 := by
      apply Finset.sum_congr rfl
      intro s _
      exact realization.cast_multiplicity G
        a15ProjectorProfile08_centroidVector s.1
    _ = 55 := horbit

/-- Projector profile 0 supplies the first binary final case. -/
theorem A15ShellGramRealization.profile00_hasFinalShellCase
    (hG : IsHypothetical G) (x : V)
    (realization :
      A15ShellGramRealization G x
        a15ProjectorProfile00.profile.centroidVector) :
    Nonempty (A15FinalShellCase G x) := by
  have hsurvivor :
      realization.projectorOrbitTotals G a15ProjectorProfile00.profile ∈
        a15ProjectorProfile00.survivors :=
    by
      have hvalid := realization.projectorOrbitTotals_valid G hG x
        a15ProjectorProfile00.profile a15ProjectorProfile00_bridgeValid
      rcases a15ProjectorProfile00.orbitTotals_complete
          a15ProjectorProfile00_checked _ hvalid with hrejected | hsurvivor
      · simp [a15ProjectorProfile00_rejections] at hrejected
      · exact hsurvivor
  have htotals :
      realization.projectorOrbitTotals G a15ProjectorProfile00.profile =
        #[0, 220] := by
    simpa [a15ProjectorProfile00] using hsurvivor
  exact ⟨.profile0
    (a15ProjectorProfile00_centroidVector ▸ realization)
    (realization.profile00_selected G htotals)⟩

/-- Projector profile 1 supplies the first parity final case. -/
theorem A15ShellGramRealization.profile01_hasFinalShellCase
    (hG : IsHypothetical G) (x : V)
    (realization :
      A15ShellGramRealization G x
        a15ProjectorProfile01.profile.centroidVector) :
    Nonempty (A15FinalShellCase G x) := by
  have hsurvivor :
      realization.projectorOrbitTotals G a15ProjectorProfile01.profile ∈
        a15ProjectorProfile01.survivors :=
    by
      have hvalid := realization.projectorOrbitTotals_valid G hG x
        a15ProjectorProfile01.profile a15ProjectorProfile01_bridgeValid
      rcases a15ProjectorProfile01.orbitTotals_complete
          a15ProjectorProfile01_checked _ hvalid with hrejected | hsurvivor
      · simp [a15ProjectorProfile01_rejections] at hrejected
      · exact hsurvivor
  have htotals :
      realization.projectorOrbitTotals G a15ProjectorProfile01.profile =
        #[55, 165] := by
    simpa [a15ProjectorProfile01] using hsurvivor
  exact ⟨.profile1
    (a15ProjectorProfile01_centroidVector ▸ realization)
    (realization.profile01_orbitTotal G htotals)⟩

/-- Projector profile 8 supplies the second parity final case. -/
theorem A15ShellGramRealization.profile08_hasFinalShellCase
    (hG : IsHypothetical G) (x : V)
    (realization :
      A15ShellGramRealization G x
        a15ProjectorProfile08.profile.centroidVector) :
    Nonempty (A15FinalShellCase G x) := by
  have hsurvivor :
      realization.projectorOrbitTotals G a15ProjectorProfile08.profile ∈
        a15ProjectorProfile08.survivors :=
    by
      have hvalid := realization.projectorOrbitTotals_valid G hG x
        a15ProjectorProfile08.profile a15ProjectorProfile08_bridgeValid
      rcases a15ProjectorProfile08.orbitTotals_complete
          a15ProjectorProfile08_checked _ hvalid with hrejected | hsurvivor
      · simp [a15ProjectorProfile08_rejections] at hrejected
      · exact hsurvivor
  have htotals :
      realization.projectorOrbitTotals G a15ProjectorProfile08.profile =
        #[165, 55] := by
    simpa [a15ProjectorProfile08] using hsurvivor
  exact ⟨.profile8
    (a15ProjectorProfile08_centroidVector ▸ realization)
    (realization.profile08_orbitTotal G htotals)⟩

/-- Projector profile 12 supplies the second binary final case. -/
theorem A15ShellGramRealization.profile12_hasFinalShellCase
    (hG : IsHypothetical G) (x : V)
    (realization :
      A15ShellGramRealization G x
        a15ProjectorProfile12.profile.centroidVector) :
    Nonempty (A15FinalShellCase G x) := by
  have hsurvivor :
      realization.projectorOrbitTotals G a15ProjectorProfile12.profile ∈
        a15ProjectorProfile12.survivors :=
    by
      have hvalid := realization.projectorOrbitTotals_valid G hG x
        a15ProjectorProfile12.profile a15ProjectorProfile12_bridgeValid
      rcases a15ProjectorProfile12.orbitTotals_complete
          a15ProjectorProfile12_checked _ hvalid with hrejected | hsurvivor
      · simp [a15ProjectorProfile12_rejections] at hrejected
      · exact hsurvivor
  have htotals :
      realization.projectorOrbitTotals G a15ProjectorProfile12.profile =
        #[220, 0] := by
    simpa [a15ProjectorProfile12] using hsurvivor
  exact ⟨.profile12
    (a15ProjectorProfile12_centroidVector ▸ realization)
    (realization.profile12_selected G htotals)⟩

end SRG266
