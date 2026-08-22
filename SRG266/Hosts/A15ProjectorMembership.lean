/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.A15FarkasKernel
import SRG266.Hosts.A15StandardAverageTheory

/-!
# Compact orbit-membership certificates for A15 projector profiles

The direct orbit bridge reconstructs every orbit by filtering the
complete 1,820-subset universe inside one large decision.  A membership
certificate instead lists only the eligible indices, grouped by orbit.  Lean
checks the list locally and proves completeness from its cardinality and the
independently checked fast eligible-shell count.
-/

open scoped BigOperators

namespace SRG266

set_option maxRecDepth 100000

/-- Compact checked literal constructor for indices in the fixed 1,820-entry
four-subset table. -/
def a15FourSubsetIndexLiteral (i : Fin 1820) : A15FourSubsetIndex :=
  ⟨i.1, by simpa only [a15FourSubsetData_size] using i.2⟩

def A15ProjectorProfile.bridgeStaticValid
    (profile : A15ProjectorProfile) : Prop :=
  profile.d.size = 16 ∧
  profile.classValues.size = profile.classSizes.size ∧
  profile.classSizes.toList.sum = 16 ∧
  profile.expandedClasses = profile.d.toList ∧
  (∑ i, profile.centroidVector i) = 0 ∧
  (∀ c : Fin profile.classSizes.size,
    0 < profile.classSizes.getD c.1 0 ∧
    (profile.classFinset c.1).card =
      profile.classSizes.getD c.1 0 ∧
    ∀ i, profile.inClass c.1 i →
      profile.centroidVector i = profile.classValues.getD c.1 0) ∧
  (∀ i, profile.classIndexCount i = 1) ∧
  ∀ k : Fin profile.orbits.size,
    0 < profile.orbitSize k.1 ∧
    (∀ c : Fin profile.classSizes.size,
      ∀ i, profile.inClass c.1 i →
        (profile.classSizes.getD c.1 0 : ℤ) *
            profile.orbitFirstMoment k.1 i =
          (profile.orbitSize k.1 : ℤ) *
            profile.orbitClassSum k.1 c.1) ∧
    (∀ c e : Fin profile.classSizes.size,
      profile.orbitBlockSecondMoment k.1 c.1 e.1 =
        (profile.orbitSize k.1 : ℤ) *
          profile.orbitClassSum k.1 c.1 *
          profile.orbitClassSum k.1 e.1) ∧
    ∀ c : Fin profile.classSizes.size,
      ∀ i j, profile.inClass c.1 i → profile.inClass c.1 j →
        i ≠ j → profile.standardMomentEquation k.1 c.1 i j

instance (profile : A15ProjectorProfile) :
    Decidable profile.bridgeStaticValid := by
  unfold A15ProjectorProfile.bridgeStaticValid
  infer_instance

structure A15ProjectorMembershipCertificate where
  profile : A15ProjectorProfile
  centroid : A15CentroidRawSurvivor
  entries : List (ℕ × A15FourSubsetIndex)

def A15ProjectorMembershipCertificate.flatMembers
    (certificate : A15ProjectorMembershipCertificate) :
    List A15FourSubsetIndex :=
  certificate.entries.map Prod.snd

def A15ProjectorMembershipCertificate.BaseValid
    (certificate : A15ProjectorMembershipCertificate) : Prop :=
  certificate.centroid.d = certificate.profile.d ∧
  certificate.centroid.reportedEligible =
    certificate.profile.reportedEligible ∧
  certificate.centroid.fastCheck = true ∧
  certificate.flatMembers.Nodup ∧
  certificate.flatMembers.length = certificate.profile.reportedEligible ∧
  ∀ k : Fin certificate.profile.orbits.size,
    (certificate.entries.filter fun entry => entry.1 = k.1).length =
      certificate.profile.orbitSize k.1

instance (certificate : A15ProjectorMembershipCertificate) :
    Decidable certificate.BaseValid := by
  unfold A15ProjectorMembershipCertificate.BaseValid
  infer_instance

def A15ProjectorMembershipCertificate.EntryValid
    (certificate : A15ProjectorMembershipCertificate)
    (entry : ℕ × A15FourSubsetIndex) : Prop :=
  entry.1 < certificate.profile.orbits.size ∧
  a15Eligible certificate.profile.centroidVector entry.2 ∧
  (∀ k : Fin certificate.profile.orbits.size,
    certificate.profile.indexMatches k.1 entry.2 ↔ k.1 = entry.1) ∧
  ∀ c : Fin certificate.profile.classSizes.size,
    (∑ i ∈ certificate.profile.classFinset c.1,
      a15ProjectorShellCoordinate certificate.profile.d
        (a15FourSubsetAt entry.2) i) =
      certificate.profile.orbitClassSum entry.1 c.1

instance (certificate : A15ProjectorMembershipCertificate)
    (entry : ℕ × A15FourSubsetIndex) :
    Decidable (certificate.EntryValid entry) := by
  unfold A15ProjectorMembershipCertificate.EntryValid
  infer_instance

def A15ProjectorMembershipCertificate.checkEntry
    (certificate : A15ProjectorMembershipCertificate)
    (entry : ℕ × A15FourSubsetIndex) : Bool :=
  decide (certificate.EntryValid entry)

def A15ProjectorMembershipCertificate.Valid
    (certificate : A15ProjectorMembershipCertificate) : Prop :=
  certificate.BaseValid ∧
  ∀ entry ∈ certificate.entries, certificate.EntryValid entry

instance (certificate : A15ProjectorMembershipCertificate) :
    Decidable certificate.Valid := by
  unfold A15ProjectorMembershipCertificate.Valid
  infer_instance

def A15ProjectorMembershipCertificate.check
    (certificate : A15ProjectorMembershipCertificate) : Bool :=
  decide certificate.Valid

theorem A15ProjectorMembershipCertificate.valid_of_checks
    (certificate : A15ProjectorMembershipCertificate)
    (hbase : decide certificate.BaseValid = true)
    (hentries : certificate.entries.all certificate.checkEntry = true) :
    certificate.Valid := by
  refine ⟨of_decide_eq_true hbase, ?_⟩
  intro entry hentry
  exact of_decide_eq_true
    ((List.all_eq_true.mp hentries) entry hentry)

theorem a15EligibleCount_eq_card (d : Fin 16 → ℤ) :
    a15EligibleCount d = Fintype.card (A15EligibleIndex d) := by
  rw [a15EligibleCount_eq_sum, Fintype.card_subtype,
    Finset.card_eq_sum_ones, Finset.sum_filter]

theorem A15ProjectorMembershipCertificate.eligible_card
    (certificate : A15ProjectorMembershipCertificate)
    (hvalid : certificate.Valid) :
    Fintype.card
        (A15EligibleIndex certificate.profile.centroidVector) =
      certificate.profile.reportedEligible := by
  rcases hvalid.1 with
    ⟨hd, heligible, hfast, _, _, _⟩
  have hchecked := certificate.centroid.fastCheck_implies_check hfast
  have hprofileValid :
      A15CentroidProfileValid certificate.centroid.toSurvivor.d
        certificate.centroid.reportedResidue
        certificate.centroid.reportedEligible := by
    have hparts :
        decide (certificate.centroid.d.size = 16) = true ∧
          certificate.centroid.toSurvivor.check = true := by
      simpa only [A15CentroidRawSurvivor.check, Bool.and_eq_true] using
        hchecked
    have hdecide :
        decide (A15CentroidProfileValid
          certificate.centroid.toSurvivor.d
          certificate.centroid.toSurvivor.reportedResidue
          certificate.centroid.toSurvivor.reportedEligible) = true := by
      simpa only [A15CentroidSurvivor.check] using hparts.2
    simpa only [A15CentroidRawSurvivor.toSurvivor] using
      (of_decide_eq_true hdecide)
  have hcount :
      a15EligibleCount certificate.centroid.toSurvivor.d =
        certificate.centroid.reportedEligible := by
    exact hprofileValid.2.2.2
  have hfunctions :
      certificate.centroid.toSurvivor.d =
        certificate.profile.centroidVector := by
    funext i
    simp [A15CentroidRawSurvivor.toSurvivor,
      A15ProjectorProfile.centroidVector, hd]
  rw [← a15EligibleCount_eq_card, ← hfunctions, hcount, heligible]

def A15ProjectorMembershipCertificate.listedFinset
    (certificate : A15ProjectorMembershipCertificate) :
    Finset A15FourSubsetIndex :=
  certificate.flatMembers.toFinset

def A15ProjectorMembershipCertificate.orbitMemberFinset
    (certificate : A15ProjectorMembershipCertificate)
    (k : Fin certificate.profile.orbits.size) :
    Finset A15FourSubsetIndex :=
  ((certificate.entries.filter fun entry => entry.1 = k.1).map
    Prod.snd).toFinset

theorem A15ProjectorMembershipCertificate.listedFinset_eq_eligible
    (certificate : A15ProjectorMembershipCertificate)
    (hvalid : certificate.Valid) :
    certificate.listedFinset =
      Finset.univ.filter
        (a15Eligible certificate.profile.centroidVector) := by
  rcases hvalid.1 with
    ⟨_, _, _, hnodup, hlength, _⟩
  apply Finset.eq_of_subset_of_card_le
  · intro s hs
    have hsflat : s ∈ certificate.flatMembers := by
      simpa [A15ProjectorMembershipCertificate.listedFinset] using hs
    obtain ⟨entry, hentry, hentryValue⟩ :=
      List.mem_map.mp hsflat
    have heligible := (hvalid.2 entry hentry).2.1
    rw [← hentryValue]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heligible⟩
  · have hlistedCard :
        certificate.listedFinset.card =
          certificate.profile.reportedEligible := by
      rw [A15ProjectorMembershipCertificate.listedFinset,
        List.toFinset_card_of_nodup hnodup, hlength]
    have heligibleCard :
        (Finset.univ.filter
          (a15Eligible certificate.profile.centroidVector)).card =
            certificate.profile.reportedEligible := by
      rw [← Fintype.card_subtype]
      exact certificate.eligible_card hvalid
    omega

theorem A15ProjectorMembershipCertificate.exists_entry_of_eligible
    (certificate : A15ProjectorMembershipCertificate)
    (hvalid : certificate.Valid)
    (s : A15FourSubsetIndex)
    (hs : a15Eligible certificate.profile.centroidVector s) :
    ∃ e, (e, s) ∈ certificate.entries := by
  have hslisted : s ∈ certificate.listedFinset := by
    rw [certificate.listedFinset_eq_eligible hvalid]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
  have hsflat : s ∈ certificate.flatMembers := by
    simpa [A15ProjectorMembershipCertificate.listedFinset] using hslisted
  obtain ⟨entry, hentry, hvalue⟩ := List.mem_map.mp hsflat
  rcases entry with ⟨e, t⟩
  simp only at hvalue
  subst t
  exact ⟨e, hentry⟩

theorem A15ProjectorMembershipCertificate.orbitMemberFinset_card
    (certificate : A15ProjectorMembershipCertificate)
    (hvalid : certificate.Valid)
    (k : Fin certificate.profile.orbits.size) :
    (certificate.orbitMemberFinset k).card =
      certificate.profile.orbitSize k.1 := by
  rcases hvalid.1 with
    ⟨_, _, _, hnodup, _, hcounts⟩
  rw [A15ProjectorMembershipCertificate.orbitMemberFinset,
    List.toFinset_card_of_nodup]
  · simpa using hcounts k
  · apply List.Nodup.sublist
      (List.Sublist.map Prod.snd List.filter_sublist)
    exact hnodup

theorem A15ProjectorMembershipCertificate.unique_index_match
    (certificate : A15ProjectorMembershipCertificate)
    (hvalid : certificate.Valid)
    (s : A15FourSubsetIndex)
    (hs : a15Eligible certificate.profile.centroidVector s) :
    certificate.profile.indexMatchCount s = 1 := by
  obtain ⟨e, hentry⟩ :=
    certificate.exists_entry_of_eligible hvalid s hs
  have hentryValid := hvalid.2 (e, s) hentry
  let eFin : Fin certificate.profile.orbits.size :=
    ⟨e, hentryValid.1⟩
  have hfilter :
      Finset.univ.filter (fun k : Fin certificate.profile.orbits.size =>
        certificate.profile.indexMatches k.1 s) = {eFin} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    rw [hentryValid.2.2.1 k]
    simp [eFin, Fin.ext_iff]
  unfold A15ProjectorProfile.indexMatchCount
  rw [hfilter]
  simp

theorem A15ProjectorMembershipCertificate.orbitIndexCard_eq
    (certificate : A15ProjectorMembershipCertificate)
    (hvalid : certificate.Valid)
    (k : Fin certificate.profile.orbits.size) :
    certificate.profile.orbitIndexCard k.1 =
      certificate.profile.orbitSize k.1 := by
  rw [A15ProjectorProfile.orbitIndexCard,
    ← certificate.orbitMemberFinset_card hvalid k]
  apply Finset.card_bij
      (fun s _ => s.1)
  · intro s hs
    have hmatch : certificate.profile.indexMatches k.1 s.1 :=
      (Finset.mem_filter.mp hs).2
    obtain ⟨e, hentry⟩ := certificate.exists_entry_of_eligible
      hvalid s.1 s.2
    have hentryValid := hvalid.2 (e, s.1) hentry
    have heq : e = k.1 := (hentryValid.2.2.1 k).mp hmatch |>.symm
    subst e
    simp [A15ProjectorMembershipCertificate.orbitMemberFinset,
      hentry]
  · intro s₁ hs₁ s₂ hs₂ heq
    exact Subtype.ext heq
  · intro s hs
    simp only [A15ProjectorMembershipCertificate.orbitMemberFinset,
      List.mem_toFinset, List.mem_map, List.mem_filter] at hs
    obtain ⟨entry, ⟨hentry, horbit⟩, hvalue⟩ := hs
    have hentryValid := hvalid.2 entry hentry
    let t : A15EligibleIndex certificate.profile.centroidVector :=
      ⟨entry.2, hentryValid.2.1⟩
    refine ⟨t, ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,
          (hentryValid.2.2.1 k).mpr
            (of_decide_eq_true horbit).symm⟩
    · exact hvalue

theorem A15ProjectorMembershipCertificate.shellClassSum_eq
    (certificate : A15ProjectorMembershipCertificate)
    (hvalid : certificate.Valid)
    (k : Fin certificate.profile.orbits.size)
    (s : A15EligibleIndex certificate.profile.centroidVector)
    (hmatch : certificate.profile.indexMatches k.1 s.1)
    (c : Fin certificate.profile.classSizes.size) :
    (∑ i ∈ certificate.profile.classFinset c.1,
      a15ProjectorShellCoordinate certificate.profile.d
        (a15FourSubsetAt s.1) i) =
      certificate.profile.orbitClassSum k.1 c.1 := by
  obtain ⟨e, hentry⟩ := certificate.exists_entry_of_eligible
    hvalid s.1 s.2
  have hentryValid := hvalid.2 (e, s.1) hentry
  have heq : e = k.1 := (hentryValid.2.2.1 k).mp hmatch |>.symm
  subst e
  exact hentryValid.2.2.2 c

theorem A15ProjectorMembershipCertificate.bridgeValid
    (certificate : A15ProjectorMembershipCertificate)
    (hmembership : certificate.Valid)
    (hstatic : certificate.profile.bridgeStaticValid) :
    certificate.profile.bridgeValid := by
  rcases hstatic with
    ⟨hdSize, hclassCount, hclassTotal, hexpanded, hdSum,
      hclasses, hcoordinateClasses, horbits⟩
  refine
    ⟨hdSize, hclassCount, hclassTotal, hexpanded, hdSum,
      hclasses, hcoordinateClasses, ?_, ?_⟩
  · intro s hs
    exact certificate.unique_index_match hmembership s hs
  · intro k
    have hk := horbits k
    exact
      ⟨hk.1, certificate.orbitIndexCard_eq hmembership k,
        hk.2.1, hk.2.2.1,
        fun s hmatch c =>
          certificate.shellClassSum_eq hmembership k s hmatch c,
        hk.2.2.2⟩

end SRG266
