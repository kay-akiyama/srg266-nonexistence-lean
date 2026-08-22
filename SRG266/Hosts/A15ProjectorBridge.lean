/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.A15SupportProjector
import SRG266.Hosts.A15Projector

/-!
# Bridge from direct A15 realizations to orbit projector certificates

The projector certificates use multiplicity totals on the orbits of the
coordinate stabilizer of a centroid profile.  A direct shell realization need
not have stabilizer-invariant multiplicities.  The required equations arise by
averaging within the equal-coordinate classes.

This module records the small finite audit needed for that averaging:

* every eligible four-subset belongs to exactly one reported orbit;
* every reported orbit size is recomputed from the complete shell;
* first moments are constant inside each coordinate class;
* sums of second moments over class blocks have the expected rank-one form;
* the second moment of a difference of two coordinates in one class has the
  expected hypergeometric average.

The later soundness proofs use these identities rather than trusting an orbit
label or enumerating a large permutation group.
-/

open scoped BigOperators Matrix

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The centroid profile represented by the compact projector array. -/
def A15ProjectorProfile.centroidVector
    (profile : A15ProjectorProfile) : Fin 16 → ℤ :=
  fun i => profile.d.getD i.1 0

/-- Membership of a coordinate in one of the contiguous equal-value classes
stored by the certificate. -/
def A15ProjectorProfile.inClass
    (profile : A15ProjectorProfile) (k : ℕ) (i : Fin 16) : Prop :=
  a15ProjectorClassStart profile.classSizes k ≤ i.1 ∧
    i.1 < a15ProjectorClassStart profile.classSizes k +
      profile.classSizes.getD k 0

instance (profile : A15ProjectorProfile) (k : ℕ) (i : Fin 16) :
    Decidable (profile.inClass k i) := by
  unfold A15ProjectorProfile.inClass
  infer_instance

def A15ProjectorProfile.classFinset
    (profile : A15ProjectorProfile) (k : ℕ) : Finset (Fin 16) :=
  Finset.univ.filter (profile.inClass k)

def A15ProjectorProfile.classIndexCount
    (profile : A15ProjectorProfile) (i : Fin 16) : ℕ :=
  (Finset.univ.filter fun c : Fin profile.classSizes.size =>
    profile.inClass c.1 i).card

/-- Matching predicate on the indexed complete four-subset universe. -/
def A15ProjectorProfile.indexMatches
    (profile : A15ProjectorProfile) (k : ℕ)
    (s : A15FourSubsetIndex) : Prop :=
  (profile.orbits.getD k
    { sign := 0, classCounts := #[], reportedSize := 0,
      firstMoment := #[], secondMoment := #[] }).matches
        profile.classSizes profile.d (a15FourSubsetAt s)

instance (profile : A15ProjectorProfile) (k : ℕ)
    (s : A15FourSubsetIndex) :
    Decidable (profile.indexMatches k s) := by
  unfold A15ProjectorProfile.indexMatches A15ProjectorOrbit.matches
  infer_instance

def A15ProjectorProfile.orbitIndexFinset
    (profile : A15ProjectorProfile) (k : ℕ) :
    Finset (A15EligibleIndex profile.centroidVector) :=
  Finset.univ.filter fun s => profile.indexMatches k s.1

def A15ProjectorProfile.orbitIndexCard
    (profile : A15ProjectorProfile) (k : ℕ) : ℕ :=
  (profile.orbitIndexFinset k).card

def A15ProjectorProfile.indexMatchCount
    (profile : A15ProjectorProfile) (s : A15FourSubsetIndex) : ℕ :=
  (Finset.univ.filter fun k : Fin profile.orbits.size =>
    profile.indexMatches k.1 s).card

def A15ProjectorProfile.orbitSign
    (profile : A15ProjectorProfile) (k : ℕ) : ℤ :=
  (profile.orbits.getD k
    { sign := 0, classCounts := #[], reportedSize := 0,
      firstMoment := #[], secondMoment := #[] }).sign

def A15ProjectorProfile.orbitClassCount
    (profile : A15ProjectorProfile) (k c : ℕ) : ℕ :=
  (profile.orbits.getD k
    { sign := 0, classCounts := #[], reportedSize := 0,
      firstMoment := #[], secondMoment := #[] }).classCounts.getD c 0

/-- Sum of shell coordinates in class `c`, determined by the orbit
signature. -/
def A15ProjectorProfile.orbitClassSum
    (profile : A15ProjectorProfile) (k c : ℕ) : ℤ :=
  profile.orbitSign k *
    ((profile.classSizes.getD c 0 : ℤ) -
      4 * profile.orbitClassCount k c)

def A15ProjectorProfile.orbitBlockSecondMoment
    (profile : A15ProjectorProfile) (k c e : ℕ) : ℤ :=
  ∑ i ∈ profile.classFinset c,
    ∑ j ∈ profile.classFinset e,
      profile.orbitSecondMoment k i j

/-- Cleared standard-difference second moment for coordinates in a common
class. -/
def A15ProjectorProfile.standardMomentEquation
    (profile : A15ProjectorProfile) (k c : ℕ)
    (i j : Fin 16) : Prop :=
  let n := profile.classSizes.getD c 0
  let r := profile.orbitClassCount k c
  (n * (n - 1) : ℤ) *
      (profile.orbitSecondMoment k i i -
        profile.orbitSecondMoment k i j -
        profile.orbitSecondMoment k j i +
        profile.orbitSecondMoment k j j) =
    (profile.orbitSize k : ℤ) *
      (32 * (r : ℤ) * ((n : ℤ) - r))

instance (profile : A15ProjectorProfile) (k c : ℕ)
    (i j : Fin 16) :
    Decidable (profile.standardMomentEquation k c i j) := by
  unfold A15ProjectorProfile.standardMomentEquation
  infer_instance

/-- Declarative bridge conditions checked independently of the Python orbit
conclusions. -/
def A15ProjectorProfile.bridgeValid
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
  (∀ s : A15FourSubsetIndex,
    a15Eligible profile.centroidVector s →
      profile.indexMatchCount s = 1) ∧
  ∀ k : Fin profile.orbits.size,
    0 < profile.orbitSize k.1 ∧
    profile.orbitIndexCard k.1 = profile.orbitSize k.1 ∧
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
    (∀ s : A15EligibleIndex profile.centroidVector,
      profile.indexMatches k.1 s.1 →
        ∀ c : Fin profile.classSizes.size,
          (∑ i ∈ profile.classFinset c.1,
            a15ProjectorShellCoordinate profile.d
              (a15FourSubsetAt s.1) i) =
            profile.orbitClassSum k.1 c.1) ∧
    ∀ c : Fin profile.classSizes.size,
      ∀ i j, profile.inClass c.1 i → profile.inClass c.1 j →
        i ≠ j → profile.standardMomentEquation k.1 c.1 i j

instance (profile : A15ProjectorProfile) :
    Decidable profile.bridgeValid := by
  unfold A15ProjectorProfile.bridgeValid
  infer_instance

def A15ProjectorProfile.checkBridge
    (profile : A15ProjectorProfile) : Bool :=
  decide profile.bridgeValid

/-- The two coordinate implementations of an oriented shell vector agree. -/
theorem a15ProjectorShellCoordinate_eq_shellVector4
    (profile : A15ProjectorProfile)
    (s : A15EligibleIndex profile.centroidVector) (i : Fin 16) :
    a15ProjectorShellCoordinate profile.d (a15FourSubsetAt s.1) i =
      a15ShellVector4 profile.centroidVector s i := by
  have hcoordinates :
      a15ProjectorProfileCoordinate profile.d =
        profile.centroidVector := rfl
  have hsum :
      (a15FourSubsetAt s.1).valueSum
          (a15ProjectorProfileCoordinate profile.d) =
        a15SubsetSum profile.centroidVector s.1 := by
    rw [hcoordinates]
    rfl
  have hmem :
      i ∈ (a15FourSubsetAt s.1).coordinates ↔
        i ∈ a15FourSubsetAsFinset s.1 := by
    simp [a15FourSubsetAsFinset, A15FourSubset.asFinset]
  rcases s.2 with hneg | hpos
  · have hneg' :
        a15SubsetSum profile.centroidVector s.1 = -60 := by
      simpa only [a15Eligible, a15DataEligible, a15SubsetSum] using hneg
    by_cases hi : i ∈ a15FourSubsetAsFinset s.1
    · have hi' : i ∈ (a15FourSubsetAt s.1).coordinates := hmem.mpr hi
      simp [a15ProjectorShellCoordinate, a15ProjectorSubsetSign,
        a15ShellVector4, a15ShellCoordinate4, hsum, hneg', hi, hi']
    · have hi' : i ∉ (a15FourSubsetAt s.1).coordinates :=
        fun h => hi (hmem.mp h)
      simp [a15ProjectorShellCoordinate, a15ProjectorSubsetSign,
        a15ShellVector4, a15ShellCoordinate4, hsum, hneg', hi, hi']
  · have hpos' :
        a15SubsetSum profile.centroidVector s.1 = 60 := by
      simpa only [a15Eligible, a15DataEligible, a15SubsetSum] using hpos
    by_cases hi : i ∈ a15FourSubsetAsFinset s.1
    · have hi' : i ∈ (a15FourSubsetAt s.1).coordinates := hmem.mpr hi
      simp [a15ProjectorShellCoordinate, a15ProjectorSubsetSign,
        a15ShellVector4, a15ShellCoordinate4, hsum, hpos', hi, hi']
    · have hi' : i ∉ (a15FourSubsetAt s.1).coordinates :=
        fun h => hi (hmem.mp h)
      simp [a15ProjectorShellCoordinate, a15ProjectorSubsetSign,
        a15ShellVector4, a15ShellCoordinate4, hsum, hpos', hi, hi']

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Orbit totals obtained from the multiplicities of a direct shell
realization. -/
def A15ShellGramRealization.projectorOrbitTotals
    {x : V} (profile : A15ProjectorProfile)
    (realization :
      A15ShellGramRealization G x profile.centroidVector) :
    Array ℕ :=
  let finite := realization.toFiniteShell G
  Array.ofFn fun k : Fin profile.orbits.size =>
    ∑ s ∈ profile.orbitIndexFinset k.1, finite.multiplicity G s

theorem A15ShellGramRealization.projectorOrbitTotals_size
    {x : V} (profile : A15ProjectorProfile)
    (realization :
      A15ShellGramRealization G x profile.centroidVector) :
    (realization.projectorOrbitTotals G profile).size =
      profile.orbits.size := by
  simp [A15ShellGramRealization.projectorOrbitTotals]

private theorem a15_sum_over_unique_orbit
    (profile : A15ProjectorProfile)
    (hunique :
      ∀ s : A15FourSubsetIndex,
        a15Eligible profile.centroidVector s →
          profile.indexMatchCount s = 1)
    (m : A15EligibleIndex profile.centroidVector → ℕ) :
    (∑ k : Fin profile.orbits.size,
      ∑ s ∈ profile.orbitIndexFinset k.1, m s) =
      ∑ s, m s := by
  simp only [A15ProjectorProfile.orbitIndexFinset, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hsCount := hunique s.1 s.2
  have hindicator :
      (∑ k : Fin profile.orbits.size,
        if profile.indexMatches k.1 s.1 then 1 else 0) = 1 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact hsCount
  calc
    (∑ k : Fin profile.orbits.size,
      if profile.indexMatches k.1 s.1 then m s else 0) =
        ∑ k : Fin profile.orbits.size,
          (if profile.indexMatches k.1 s.1 then 1 else 0) * m s := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : profile.indexMatches k.1 s.1 <;> simp [hk]
    _ = (∑ k : Fin profile.orbits.size,
        if profile.indexMatches k.1 s.1 then 1 else 0) * m s := by
      rw [Finset.sum_mul]
    _ = m s := by rw [hindicator]; simp

/-- The direct orbit totals have the correct size, capacities, and total
cardinality. -/
theorem A15ShellGramRealization.projectorOrbitTotals_basic
    (hG : IsHypothetical G) (x : V)
    (profile : A15ProjectorProfile)
    (hbridge : profile.bridgeValid)
    (realization :
      A15ShellGramRealization G x profile.centroidVector) :
    (realization.projectorOrbitTotals G profile).size =
        profile.orbits.size ∧
      (∀ k : Fin profile.orbits.size,
        (realization.projectorOrbitTotals G profile).getD k.1 0 ≤
          3 * profile.orbitSize k.1) ∧
      (∑ k : Fin profile.orbits.size,
        (realization.projectorOrbitTotals G profile).getD k.1 0) = 220 := by
  let finite := realization.toFiniteShell G
  rcases hbridge with
    ⟨hdSize, hclassCount, hclassTotal, hexpanded, hdSum,
      hclasses, hcoordinateClasses, hunique, horbits⟩
  have hget (k : Fin profile.orbits.size) :
      (realization.projectorOrbitTotals G profile).getD k.1 0 =
        ∑ s ∈ profile.orbitIndexFinset k.1,
          finite.multiplicity G s := by
    simp [A15ShellGramRealization.projectorOrbitTotals, finite, k.isLt]
  refine ⟨realization.projectorOrbitTotals_size G profile, ?_, ?_⟩
  · intro k
    have horbit := horbits k
    rw [hget k]
    calc
      _ ≤ ∑ _s ∈ profile.orbitIndexFinset k.1, 3 := by
        apply Finset.sum_le_sum
        intro s hs
        exact finite.multiplicity_le_three G hG x s
      _ = 3 * (profile.orbitIndexFinset k.1).card := by
        simp [mul_comm]
      _ = 3 * profile.orbitSize k.1 := by
        rw [← A15ProjectorProfile.orbitIndexCard, horbit.2.1]
  · simp_rw [hget]
    rw [a15_sum_over_unique_orbit profile hunique
      (finite.multiplicity G), finite.sum_multiplicity G,
      secondSubconstituent_card G hG x]

private theorem a15_sum_unique_index_match
    (profile : A15ProjectorProfile)
    (hunique :
      ∀ s : A15FourSubsetIndex,
        a15Eligible profile.centroidVector s →
          profile.indexMatchCount s = 1)
    (s : A15EligibleIndex profile.centroidVector)
    (f : Fin profile.orbits.size → ℤ) (z : ℤ)
    (hvalue :
      ∀ k : Fin profile.orbits.size,
        profile.indexMatches k.1 s.1 → f k = z) :
    (∑ k : Fin profile.orbits.size,
      if profile.indexMatches k.1 s.1 then f k else 0) = z := by
  let matchedSet :=
    Finset.univ.filter fun k : Fin profile.orbits.size =>
      profile.indexMatches k.1 s.1
  have hcard : matchedSet.card = 1 := hunique s.1 s.2
  obtain ⟨k₀, hk₀⟩ := Finset.card_eq_one.mp hcard
  have hk₀mem : k₀ ∈ matchedSet := by rw [hk₀]; simp
  have hk₀match : profile.indexMatches k₀.1 s.1 :=
    (Finset.mem_filter.mp hk₀mem).2
  have hother :
      ∀ k : Fin profile.orbits.size, k ≠ k₀ →
        ¬profile.indexMatches k.1 s.1 := by
    intro k hk hmatch
    have hkmem : k ∈ matchedSet :=
      Finset.mem_filter.mpr ⟨by simp, hmatch⟩
    rw [hk₀] at hkmem
    exact hk (Finset.mem_singleton.mp hkmem)
  rw [Finset.sum_eq_single k₀]
  · simp [hk₀match, hvalue k₀ hk₀match]
  · intro k hk hkne
    simp [hother k hkne]
  · intro hknot
    exact (hknot (by simp)).elim

/-- The weighted sum of one orbit signature statistic can be regrouped over
the actual shell multiplicities. -/
private theorem A15ShellGramRealization.projectorOrbitTotals_classSum
    {x : V} (profile : A15ProjectorProfile)
    (hbridge : profile.bridgeValid)
    (realization :
      A15ShellGramRealization G x profile.centroidVector)
    (c : Fin profile.classSizes.size) :
    (∑ k : Fin profile.orbits.size,
      ((realization.projectorOrbitTotals G profile).getD k.1 0 : ℤ) *
        profile.orbitClassSum k.1 c.1) =
      ∑ s : A15EligibleIndex profile.centroidVector,
        ((realization.toFiniteShell G).multiplicity G s : ℤ) *
          (∑ i ∈ profile.classFinset c.1,
            a15ShellVector4 profile.centroidVector s i) := by
  let finite := realization.toFiniteShell G
  rcases hbridge with
    ⟨hdSize, hclassCount, hclassTotal, hexpanded, hdSum,
      hclasses, hcoordinateClasses, hunique, horbits⟩
  have hget (k : Fin profile.orbits.size) :
      (realization.projectorOrbitTotals G profile).getD k.1 0 =
        ∑ s ∈ profile.orbitIndexFinset k.1,
          finite.multiplicity G s := by
    simp [A15ShellGramRealization.projectorOrbitTotals, finite, k.isLt]
  simp_rw [hget]
  calc
    (∑ k : Fin profile.orbits.size,
      ((∑ s ∈ profile.orbitIndexFinset k.1,
          finite.multiplicity G s : ℕ) : ℤ) *
        profile.orbitClassSum k.1 c.1) =
        ∑ k : Fin profile.orbits.size,
          ∑ s ∈ profile.orbitIndexFinset k.1,
            (finite.multiplicity G s : ℤ) *
              profile.orbitClassSum k.1 c.1 := by
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      rw [Finset.sum_mul]
    _ = ∑ s : A15EligibleIndex profile.centroidVector,
        ∑ k : Fin profile.orbits.size,
          if profile.indexMatches k.1 s.1 then
            (finite.multiplicity G s : ℤ) *
              profile.orbitClassSum k.1 c.1
          else 0 := by
      simp only [A15ProjectorProfile.orbitIndexFinset, Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ s : A15EligibleIndex profile.centroidVector,
        (finite.multiplicity G s : ℤ) *
          (∑ i ∈ profile.classFinset c.1,
            a15ShellVector4 profile.centroidVector s i) := by
      apply Finset.sum_congr rfl
      intro s _
      apply a15_sum_unique_index_match profile hunique s
      intro k hmatch
      have hshell := (horbits k).2.2.2.2.1 s hmatch c
      calc
        (finite.multiplicity G s : ℤ) *
            profile.orbitClassSum k.1 c.1 =
          (finite.multiplicity G s : ℤ) *
            (∑ i ∈ profile.classFinset c.1,
              a15ProjectorShellCoordinate profile.d
                (a15FourSubsetAt s.1) i) := by rw [hshell]
        _ = _ := by
          apply congrArg ((finite.multiplicity G s : ℤ) * ·)
          apply Finset.sum_congr rfl
          intro i _
          rw [a15ProjectorShellCoordinate_eq_shellVector4]

/-- Orbit class sums reproduce the class-averaged direct centroid equation. -/
theorem A15ShellGramRealization.projectorOrbitTotals_classCentroid
    {x : V} (profile : A15ProjectorProfile)
    (hbridge : profile.bridgeValid)
    (realization :
      A15ShellGramRealization G x profile.centroidVector)
    (c : Fin profile.classSizes.size) (i : Fin 16)
    (hi : profile.inClass c.1 i) :
    (∑ k : Fin profile.orbits.size,
      ((realization.projectorOrbitTotals G profile).getD k.1 0 : ℤ) *
        profile.orbitClassSum k.1 c.1) =
      (profile.classSizes.getD c.1 0 : ℤ) *
        (11 * profile.centroidVector i) := by
  let finite := realization.toFiniteShell G
  have hweighted :=
    realization.projectorOrbitTotals_classSum G profile hbridge c
  rw [hweighted]
  calc
    (∑ s : A15EligibleIndex profile.centroidVector,
      (finite.multiplicity G s : ℤ) *
        (∑ j ∈ profile.classFinset c.1,
          a15ShellVector4 profile.centroidVector s j)) =
        ∑ j ∈ profile.classFinset c.1,
          ∑ s : A15EligibleIndex profile.centroidVector,
            (finite.multiplicity G s : ℤ) *
              a15ShellVector4 profile.centroidVector s j := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ j ∈ profile.classFinset c.1,
        ∑ B, a15ShellVector4 profile.centroidVector
          (realization.shell B) j := by
      apply Finset.sum_congr rfl
      intro j _
      exact finite.sum_multiplicity_mul G
        (fun s => a15ShellVector4 profile.centroidVector s j)
    _ = ∑ _j ∈ profile.classFinset c.1,
        11 * profile.centroidVector i := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjClass :
          profile.inClass c.1 j :=
        (Finset.mem_filter.mp hj).2
      have hdEqual :
          profile.centroidVector j = profile.centroidVector i := by
        have hc := hbridge.2.2.2.2.2.1 c
        exact (hc.2.2 j hjClass).trans (hc.2.2 i hi).symm
      rw [realization.centroid j, hdEqual]
    _ = (profile.classSizes.getD c.1 0 : ℤ) *
        (11 * profile.centroidVector i) := by
      rw [Finset.sum_const, nsmul_eq_mul,
        (hbridge.2.2.2.2.2.1 c).2.1]

private theorem A15ProjectorProfile.exists_coordinate_class
    (profile : A15ProjectorProfile)
    (hclasses : ∀ i, profile.classIndexCount i = 1)
    (i : Fin 16) :
    ∃ c : Fin profile.classSizes.size, profile.inClass c.1 i := by
  let classSet :=
    Finset.univ.filter fun c : Fin profile.classSizes.size =>
      profile.inClass c.1 i
  have hcard : classSet.card = 1 := hclasses i
  have hpos : 0 < classSet.card := by rw [hcard]; norm_num
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
  exact ⟨c, (Finset.mem_filter.mp hc).2⟩

/-- The averaged orbit totals satisfy every coordinate centroid equation. -/
theorem A15ShellGramRealization.projectorOrbitTotals_centroid
    {x : V} (profile : A15ProjectorProfile)
    (hbridge : profile.bridgeValid)
    (realization :
      A15ShellGramRealization G x profile.centroidVector)
    (i : Fin 16) :
    (∑ k : Fin profile.orbits.size,
      ((realization.projectorOrbitTotals G profile).getD k.1 0 *
        profile.orbitFirstMoment k.1 i : ℚ) /
          (profile.orbitSize k.1 : ℚ)) =
      11 * profile.d.getD i.1 0 := by
  rcases hbridge with
    ⟨hdSize, hclassCount, hclassTotal, hexpanded, hdSum,
      hclasses, hcoordinateClasses, hunique, horbits⟩
  obtain ⟨c, hic⟩ :=
    profile.exists_coordinate_class hcoordinateClasses i
  have hnPos : 0 < profile.classSizes.getD c.1 0 :=
    (hclasses c).1
  have hnQ :
      (profile.classSizes.getD c.1 0 : ℚ) ≠ 0 := by
    positivity
  have hterm (k : Fin profile.orbits.size) :
      ((realization.projectorOrbitTotals G profile).getD k.1 0 *
        profile.orbitFirstMoment k.1 i : ℚ) /
          (profile.orbitSize k.1 : ℚ) =
        ((realization.projectorOrbitTotals G profile).getD k.1 0 : ℚ) *
          profile.orbitClassSum k.1 c.1 /
            (profile.classSizes.getD c.1 0 : ℚ) := by
    have hk := horbits k
    have hsizeQ : (profile.orbitSize k.1 : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hk.1)
    apply (div_eq_div_iff hsizeQ hnQ).2
    have hfirst := hk.2.2.1 c i hic
    have hfirstQ :
        (profile.classSizes.getD c.1 0 : ℚ) *
            profile.orbitFirstMoment k.1 i =
          (profile.orbitSize k.1 : ℚ) *
            profile.orbitClassSum k.1 c.1 := by
      exact_mod_cast hfirst
    calc
      ((realization.projectorOrbitTotals G profile).getD k.1 0 : ℚ) *
          profile.orbitFirstMoment k.1 i *
          (profile.classSizes.getD c.1 0 : ℚ) =
        ((realization.projectorOrbitTotals G profile).getD k.1 0 : ℚ) *
          ((profile.classSizes.getD c.1 0 : ℚ) *
            profile.orbitFirstMoment k.1 i) := by ring
      _ = ((realization.projectorOrbitTotals G profile).getD k.1 0 : ℚ) *
          ((profile.orbitSize k.1 : ℚ) *
            profile.orbitClassSum k.1 c.1) := by rw [hfirstQ]
      _ = ((realization.projectorOrbitTotals G profile).getD k.1 0 : ℚ) *
          profile.orbitClassSum k.1 c.1 *
            (profile.orbitSize k.1 : ℚ) := by ring
  simp_rw [hterm]
  rw [← Finset.sum_div]
  have hclass :=
    realization.projectorOrbitTotals_classCentroid
      G profile
      ⟨hdSize, hclassCount, hclassTotal, hexpanded, hdSum,
        hclasses, hcoordinateClasses, hunique, horbits⟩ c i hic
  have hclassQ :
      (∑ k : Fin profile.orbits.size,
        ((realization.projectorOrbitTotals G profile).getD k.1 0 : ℚ) *
          profile.orbitClassSum k.1 c.1) =
        (profile.classSizes.getD c.1 0 : ℚ) *
          (11 * profile.centroidVector i) := by
    exact_mod_cast hclass
  rw [hclassQ]
  have hd :
      (profile.centroidVector i : ℚ) =
        profile.d.getD i.1 0 := rfl
  rw [hd]
  field_simp

/-- A direct A15 shell realization supplies a valid orbit-total vector for
the checked projector certificate. -/
theorem A15ShellGramRealization.projectorOrbitTotals_valid
    (hG : IsHypothetical G) (x : V)
    (profile : A15ProjectorProfile)
    (hbridge : profile.bridgeValid)
    (realization :
      A15ShellGramRealization G x profile.centroidVector) :
    profile.orbitTotalsValid
      (realization.projectorOrbitTotals G profile) := by
  have hbasic :=
    realization.projectorOrbitTotals_basic G hG x profile hbridge
  exact
    ⟨hbasic.1, hbasic.2.1, hbasic.2.2,
      realization.projectorOrbitTotals_centroid G profile hbridge⟩

def A15ProjectorProfile.shellDot
    (profile : A15ProjectorProfile) (x : Array ℤ)
    (s : A15EligibleIndex profile.centroidVector) : ℤ :=
  ∑ i : Fin 16, x.getD i.1 0 *
    a15ProjectorShellCoordinate profile.d (a15FourSubsetAt s.1) i

def A15ProjectorProfile.orbitSecondBilinear
    (profile : A15ProjectorProfile) (k : ℕ)
    (x y : Array ℤ) : ℤ :=
  ∑ i : Fin 16, ∑ j : Fin 16,
    x.getD i.1 0 * profile.orbitSecondMoment k i j *
      y.getD j.1 0

/-- A bilinear form on two fixed vectors is constant on every reported shell
orbit and agrees with the reported second moment. -/
def A15ProjectorProfile.bilinearCompatible
    (profile : A15ProjectorProfile) (x y : Array ℤ) : Prop :=
  x.size = 16 ∧ y.size = 16 ∧
  ∀ k : Fin profile.orbits.size,
    ∀ s : A15EligibleIndex profile.centroidVector,
      profile.indexMatches k.1 s.1 →
        (profile.orbitSize k.1 : ℤ) *
            profile.shellDot x s * profile.shellDot y s =
          profile.orbitSecondBilinear k.1 x y

instance (profile : A15ProjectorProfile) (x y : Array ℤ) :
    Decidable (profile.bilinearCompatible x y) := by
  unfold A15ProjectorProfile.bilinearCompatible
  infer_instance

/-- The exact standard difference of two coordinates in one reported
coordinate class. -/
def A15ProjectorProfile.isStandardDifference
    (profile : A15ProjectorProfile) (x : Array ℤ) : Prop :=
  x.size = 16 ∧
  ∃ (c : Fin profile.classSizes.size) (i j : Fin 16),
    profile.inClass c.1 i ∧ profile.inClass c.1 j ∧ i ≠ j ∧
    ∀ l : Fin 16,
      x.getD l.1 0 =
        if l = i then 1 else if l = j then -1 else 0

instance (profile : A15ProjectorProfile) (x : Array ℤ) :
    Decidable (profile.isStandardDifference x) := by
  unfold A15ProjectorProfile.isStandardDifference
  infer_instance

def A15ProjectorWitness.bridgeCompatible
    (profile : A15ProjectorProfile) :
    A15ProjectorWitness → Prop
  | .negativeVector x _ =>
      profile.bilinearCompatible x x ∨
        profile.isStandardDifference x
  | .negativeMinor x y _ =>
      profile.bilinearCompatible x x ∧
      profile.bilinearCompatible x y ∧
      profile.bilinearCompatible y x ∧
      profile.bilinearCompatible y y

instance (profile : A15ProjectorProfile)
    (witness : A15ProjectorWitness) :
    Decidable (witness.bridgeCompatible profile) := by
  cases witness <;>
    simp only [A15ProjectorWitness.bridgeCompatible] <;>
    infer_instance

/-- Entrywise formula for the unaveraged direct complement projector,
regrouped by shell multiplicities. -/
theorem A15ShellGramRealization.complementProjector_apply
    {x : V} (profile : A15ProjectorProfile)
    (realization :
      A15ShellGramRealization G x profile.centroidVector)
    (i j : Fin 16) :
    realization.complementProjector G i j =
      (if i = j then 1 else 0) - 1 / 16 +
        (profile.d.getD i.1 0 * profile.d.getD j.1 0 : ℚ) / 1800 -
        (∑ s : A15EligibleIndex profile.centroidVector,
          ((realization.toFiniteShell G).multiplicity G s : ℚ) *
            a15ProjectorShellCoordinate profile.d
              (a15FourSubsetAt s.1) i *
            a15ProjectorShellCoordinate profile.d
              (a15FourSubsetAt s.1) j) / 720 := by
  let finite := realization.toFiniteShell G
  have hframe :
      realization.frame G i j =
        ∑ s : A15EligibleIndex profile.centroidVector,
          (finite.multiplicity G s : ℤ) *
            (a15ShellVector4 profile.centroidVector s i *
              a15ShellVector4 profile.centroidVector s j) := by
    change
      (∑ B, a15ShellVector4 profile.centroidVector
          (realization.shell B) i *
        a15ShellVector4 profile.centroidVector
          (realization.shell B) j) = _
    exact
      (finite.sum_multiplicity_mul G
        (fun s =>
          a15ShellVector4 profile.centroidVector s i *
            a15ShellVector4 profile.centroidVector s j)).symm
  have hframeQ :
      (realization.frame G i j : ℚ) =
        ∑ s : A15EligibleIndex profile.centroidVector,
          (finite.multiplicity G s : ℚ) *
            a15ProjectorShellCoordinate profile.d
              (a15FourSubsetAt s.1) i *
            a15ProjectorShellCoordinate profile.d
              (a15FourSubsetAt s.1) j := by
    rw [hframe]
    push_cast
    apply Finset.sum_congr rfl
    intro s _
    rw [a15ProjectorShellCoordinate_eq_shellVector4,
      a15ProjectorShellCoordinate_eq_shellVector4]
    ring
  have hframeQ' :
      (realization.frame G i j : ℚ) =
        ∑ s : A15EligibleIndex profile.centroidVector,
          ((realization.toFiniteShell G).multiplicity G s : ℚ) *
            a15ProjectorShellCoordinate profile.d
              (a15FourSubsetAt s.1) i *
            a15ProjectorShellCoordinate profile.d
              (a15FourSubsetAt s.1) j := by
    simpa [finite] using hframeQ
  simp only [A15ShellGramRealization.complementProjector,
    Matrix.sub_apply, a15AmbientProjector,
    A15ShellGramRealization.supportProjector,
    A15ShellGramRealization.supportNumerator,
    Matrix.sub_apply, nsmulMatrix_apply,
    a15CentroidOuter, Matrix.vecMulVec_apply,
    A15ProjectorProfile.centroidVector]
  push_cast
  rw [hframeQ']
  ring

theorem a15_sum_unique_index_match_rat
    (profile : A15ProjectorProfile)
    (hunique :
      ∀ s : A15FourSubsetIndex,
        a15Eligible profile.centroidVector s →
          profile.indexMatchCount s = 1)
    (s : A15EligibleIndex profile.centroidVector)
    (f : Fin profile.orbits.size → ℚ) (z : ℚ)
    (hvalue :
      ∀ k : Fin profile.orbits.size,
        profile.indexMatches k.1 s.1 → f k = z) :
    (∑ k : Fin profile.orbits.size,
      if profile.indexMatches k.1 s.1 then f k else 0) = z := by
  let matchedSet :=
    Finset.univ.filter fun k : Fin profile.orbits.size =>
      profile.indexMatches k.1 s.1
  have hcard : matchedSet.card = 1 := hunique s.1 s.2
  obtain ⟨k₀, hk₀⟩ := Finset.card_eq_one.mp hcard
  have hk₀mem : k₀ ∈ matchedSet := by rw [hk₀]; simp
  have hk₀match : profile.indexMatches k₀.1 s.1 :=
    (Finset.mem_filter.mp hk₀mem).2
  have hother :
      ∀ k : Fin profile.orbits.size, k ≠ k₀ →
        ¬profile.indexMatches k.1 s.1 := by
    intro k hk hmatch
    have hkmem : k ∈ matchedSet :=
      Finset.mem_filter.mpr ⟨by simp, hmatch⟩
    rw [hk₀] at hkmem
    exact hk (Finset.mem_singleton.mp hkmem)
  rw [Finset.sum_eq_single k₀]
  · simp [hk₀match, hvalue k₀ hk₀match]
  · intro k hk hkne
    simp [hother k hkne]
  · intro hknot
    exact (hknot (by simp)).elim

/-- A compatible reported second moment equals the corresponding weighted
bilinear form of the direct shell realization. -/
theorem A15ShellGramRealization.orbitSecondBilinear_average
    {x : V} (profile : A15ProjectorProfile)
    (hbridge : profile.bridgeValid)
    (realization :
      A15ShellGramRealization G x profile.centroidVector)
    (a b : Array ℤ) (hcompatible : profile.bilinearCompatible a b) :
    (∑ k : Fin profile.orbits.size,
      ((realization.projectorOrbitTotals G profile).getD k.1 0 : ℚ) *
        profile.orbitSecondBilinear k.1 a b /
          (profile.orbitSize k.1 : ℚ)) =
      ∑ s : A15EligibleIndex profile.centroidVector,
        ((realization.toFiniteShell G).multiplicity G s : ℚ) *
          profile.shellDot a s * profile.shellDot b s := by
  let finite := realization.toFiniteShell G
  rcases hbridge with
    ⟨hdSize, hclassCount, hclassTotal, hexpanded, hdSum,
      hclasses, hcoordinateClasses, hunique, horbits⟩
  have hget (k : Fin profile.orbits.size) :
      (realization.projectorOrbitTotals G profile).getD k.1 0 =
        ∑ s ∈ profile.orbitIndexFinset k.1,
          finite.multiplicity G s := by
    simp [A15ShellGramRealization.projectorOrbitTotals, finite, k.isLt]
  simp_rw [hget]
  calc
    (∑ k : Fin profile.orbits.size,
      ((∑ s ∈ profile.orbitIndexFinset k.1,
          finite.multiplicity G s : ℕ) : ℚ) *
        profile.orbitSecondBilinear k.1 a b /
          (profile.orbitSize k.1 : ℚ)) =
        ∑ k : Fin profile.orbits.size,
          ∑ s ∈ profile.orbitIndexFinset k.1,
            (finite.multiplicity G s : ℚ) *
              profile.orbitSecondBilinear k.1 a b /
                (profile.orbitSize k.1 : ℚ) := by
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      rw [Finset.sum_mul, Finset.sum_div]
    _ = ∑ s : A15EligibleIndex profile.centroidVector,
        ∑ k : Fin profile.orbits.size,
          if profile.indexMatches k.1 s.1 then
            (finite.multiplicity G s : ℚ) *
              profile.orbitSecondBilinear k.1 a b /
                (profile.orbitSize k.1 : ℚ)
          else 0 := by
      simp only [A15ProjectorProfile.orbitIndexFinset, Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ s : A15EligibleIndex profile.centroidVector,
        (finite.multiplicity G s : ℚ) *
          profile.shellDot a s * profile.shellDot b s := by
      apply Finset.sum_congr rfl
      intro s _
      apply a15_sum_unique_index_match_rat profile hunique s
      intro k hmatch
      have hmoment := hcompatible.2.2 k s hmatch
      have hsize : (profile.orbitSize k.1 : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (horbits k).1)
      have hmomentQ :
          (profile.orbitSize k.1 : ℚ) *
              profile.shellDot a s * profile.shellDot b s =
            profile.orbitSecondBilinear k.1 a b := by
        exact_mod_cast hmoment
      rw [← hmomentQ]
      field_simp

private theorem a15_list_range_sum_eq_fin_sum
    (n : ℕ) (f : ℕ → ℚ) :
    ((List.range n).map f).sum = ∑ k : Fin n, f k.1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      rw [Fin.sum_univ_castSucc]
      simp

def A15ProjectorProfile.baseEntry
    (profile : A15ProjectorProfile) (i j : Fin 16) : ℚ :=
  (if i = j then 1 else 0) - 1 / 16 +
    (profile.d.getD i.1 0 * profile.d.getD j.1 0 : ℚ) / 1800

def A15ProjectorProfile.baseQForm
    (profile : A15ProjectorProfile) (a b : Array ℤ) : ℚ :=
  ∑ i : Fin 16, ∑ j : Fin 16,
    (a.getD i.1 0 : ℚ) * profile.baseEntry i j *
      (b.getD j.1 0 : ℚ)

theorem a15ProjectorQForm_expand
    (profile : A15ProjectorProfile) (totals : Array ℕ)
    (a b : Array ℤ) :
    a15ProjectorQForm profile totals a b =
      profile.baseQForm a b -
        (∑ k : Fin profile.orbits.size,
          (totals.getD k.1 0 : ℚ) *
            profile.orbitSecondBilinear k.1 a b /
              (profile.orbitSize k.1 : ℚ)) / 720 := by
  have hlist (i j : Fin 16) :
      a15ProjectorListSumRat
          ((List.range profile.orbits.size).map fun k =>
            (totals.getD k 0 * profile.orbitSecondMoment k i j : ℚ) /
              (720 * profile.orbitSize k : ℚ)) =
        ∑ k : Fin profile.orbits.size,
          (totals.getD k.1 0 *
            profile.orbitSecondMoment k.1 i j : ℚ) /
              (720 * profile.orbitSize k.1 : ℚ) := by
    exact a15_list_range_sum_eq_fin_sum profile.orbits.size _
  unfold a15ProjectorQForm A15ProjectorProfile.projectorEntry
  simp_rw [hlist]
  change
    (∑ i : Fin 16, ∑ j : Fin 16,
      (a.getD i.1 0 : ℚ) *
        (profile.baseEntry i j -
          ∑ k : Fin profile.orbits.size,
            (totals.getD k.1 0 *
              profile.orbitSecondMoment k.1 i j : ℚ) /
                (720 * profile.orbitSize k.1 : ℚ)) *
        (b.getD j.1 0 : ℚ)) = _
  simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib]
  apply congrArg₂ (· - ·)
  · rfl
  calc
    (∑ i : Fin 16, ∑ j : Fin 16,
      (a.getD i.1 0 : ℚ) *
          (∑ k : Fin profile.orbits.size,
            (totals.getD k.1 0 *
              profile.orbitSecondMoment k.1 i j : ℚ) /
                (720 * profile.orbitSize k.1 : ℚ)) *
        (b.getD j.1 0 : ℚ)) =
        ∑ i : Fin 16, ∑ j : Fin 16,
          ∑ k : Fin profile.orbits.size,
            (a.getD i.1 0 : ℚ) *
              ((totals.getD k.1 0 *
                profile.orbitSecondMoment k.1 i j : ℚ) /
                  (720 * profile.orbitSize k.1 : ℚ)) *
              (b.getD j.1 0 : ℚ) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i : Fin 16,
        ∑ k : Fin profile.orbits.size, ∑ j : Fin 16,
          (a.getD i.1 0 : ℚ) *
            ((totals.getD k.1 0 *
              profile.orbitSecondMoment k.1 i j : ℚ) /
                (720 * profile.orbitSize k.1 : ℚ)) *
            (b.getD j.1 0 : ℚ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k : Fin profile.orbits.size,
        ∑ i : Fin 16, ∑ j : Fin 16,
          (a.getD i.1 0 : ℚ) *
            ((totals.getD k.1 0 *
              profile.orbitSecondMoment k.1 i j : ℚ) /
                (720 * profile.orbitSize k.1 : ℚ)) *
            (b.getD j.1 0 : ℚ) := by
      rw [Finset.sum_comm]
    _ = (∑ k : Fin profile.orbits.size,
        (totals.getD k.1 0 : ℚ) *
          profile.orbitSecondBilinear k.1 a b /
            (profile.orbitSize k.1 : ℚ)) / 720 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      calc
        (∑ i : Fin 16, ∑ j : Fin 16,
          (a.getD i.1 0 : ℚ) *
              ((totals.getD k.1 0 *
                profile.orbitSecondMoment k.1 i j : ℚ) /
                  (720 * profile.orbitSize k.1 : ℚ)) *
            (b.getD j.1 0 : ℚ)) =
            ((totals.getD k.1 0 : ℚ) /
                (720 * profile.orbitSize k.1 : ℚ)) *
              (profile.orbitSecondBilinear k.1 a b : ℚ) := by
          unfold A15ProjectorProfile.orbitSecondBilinear
          push_cast
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = (totals.getD k.1 0 : ℚ) *
              (profile.orbitSecondBilinear k.1 a b : ℚ) /
                (profile.orbitSize k.1 : ℚ) / 720 := by
          ring

theorem a15DirectQForm_expand
    {x : V} (profile : A15ProjectorProfile)
    (realization :
      A15ShellGramRealization G x profile.centroidVector)
    (a b : Array ℤ) :
    a15RationalMatrixQForm (realization.complementProjector G)
        (a15ProjectorArrayVector a) (a15ProjectorArrayVector b) =
      profile.baseQForm a b -
        (∑ s : A15EligibleIndex profile.centroidVector,
          ((realization.toFiniteShell G).multiplicity G s : ℚ) *
            profile.shellDot a s * profile.shellDot b s) / 720 := by
  unfold a15RationalMatrixQForm a15ProjectorArrayVector
  simp_rw [realization.complementProjector_apply G profile]
  change
    (∑ i : Fin 16, ∑ j : Fin 16,
      (a.getD i.1 0 : ℚ) *
        (profile.baseEntry i j -
          (∑ s : A15EligibleIndex profile.centroidVector,
            ((realization.toFiniteShell G).multiplicity G s : ℚ) *
              a15ProjectorShellCoordinate profile.d
                (a15FourSubsetAt s.1) i *
              a15ProjectorShellCoordinate profile.d
                (a15FourSubsetAt s.1) j) / 720) *
        (b.getD j.1 0 : ℚ)) = _
  simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib]
  apply congrArg₂ (· - ·)
  · rfl
  calc
    (∑ i : Fin 16, ∑ j : Fin 16,
      (a.getD i.1 0 : ℚ) *
          ((∑ s : A15EligibleIndex profile.centroidVector,
            ((realization.toFiniteShell G).multiplicity G s : ℚ) *
              a15ProjectorShellCoordinate profile.d
                (a15FourSubsetAt s.1) i *
              a15ProjectorShellCoordinate profile.d
                (a15FourSubsetAt s.1) j) / 720) *
        (b.getD j.1 0 : ℚ)) =
        (∑ i : Fin 16, ∑ j : Fin 16,
          (a.getD i.1 0 : ℚ) *
            (∑ s : A15EligibleIndex profile.centroidVector,
              ((realization.toFiniteShell G).multiplicity G s : ℚ) *
                a15ProjectorShellCoordinate profile.d
                  (a15FourSubsetAt s.1) i *
                a15ProjectorShellCoordinate profile.d
                  (a15FourSubsetAt s.1) j) *
            (b.getD j.1 0 : ℚ)) / 720 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ s : A15EligibleIndex profile.centroidVector,
          ((realization.toFiniteShell G).multiplicity G s : ℚ) *
            profile.shellDot a s * profile.shellDot b s) / 720 := by
      apply congrArg (· / 720)
      unfold A15ProjectorProfile.shellDot
      push_cast
      calc
        (∑ i : Fin 16, ∑ j : Fin 16,
          (a.getD i.1 0 : ℚ) *
            (∑ s : A15EligibleIndex profile.centroidVector,
              ((realization.toFiniteShell G).multiplicity G s : ℚ) *
                a15ProjectorShellCoordinate profile.d
                  (a15FourSubsetAt s.1) i *
                a15ProjectorShellCoordinate profile.d
                  (a15FourSubsetAt s.1) j) *
            (b.getD j.1 0 : ℚ)) =
            ∑ i : Fin 16,
              ∑ s : A15EligibleIndex profile.centroidVector,
                ∑ j : Fin 16,
                  (a.getD i.1 0 : ℚ) *
                    (((realization.toFiniteShell G).multiplicity G s : ℚ) *
                      a15ProjectorShellCoordinate profile.d
                        (a15FourSubsetAt s.1) i *
                      a15ProjectorShellCoordinate profile.d
                        (a15FourSubsetAt s.1) j) *
                    (b.getD j.1 0 : ℚ) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.mul_sum, Finset.sum_mul]
        _ = ∑ s : A15EligibleIndex profile.centroidVector,
              ∑ i : Fin 16, ∑ j : Fin 16,
                (a.getD i.1 0 : ℚ) *
                  (((realization.toFiniteShell G).multiplicity G s : ℚ) *
                    a15ProjectorShellCoordinate profile.d
                      (a15FourSubsetAt s.1) i *
                    a15ProjectorShellCoordinate profile.d
                      (a15FourSubsetAt s.1) j) *
                  (b.getD j.1 0 : ℚ) := by
          rw [Finset.sum_comm]
        _ = ∑ s : A15EligibleIndex profile.centroidVector,
              ((realization.toFiniteShell G).multiplicity G s : ℚ) *
                (∑ i : Fin 16,
                  (a.getD i.1 0 : ℚ) *
                    a15ProjectorShellCoordinate profile.d
                      (a15FourSubsetAt s.1) i) *
                (∑ j : Fin 16,
                  (b.getD j.1 0 : ℚ) *
                    a15ProjectorShellCoordinate profile.d
                      (a15FourSubsetAt s.1) j) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.mul_sum, Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring

/-- On every bilinear-compatible pair, the checked averaged projector form is
exactly the form of the direct positive-semidefinite complement projector. -/
theorem A15ShellGramRealization.projectorQForm_eq_direct
    {x : V} (profile : A15ProjectorProfile)
    (hbridge : profile.bridgeValid)
    (realization :
      A15ShellGramRealization G x profile.centroidVector)
    (a b : Array ℤ) (hcompatible : profile.bilinearCompatible a b) :
    a15ProjectorQForm profile
        (realization.projectorOrbitTotals G profile) a b =
      a15RationalMatrixQForm (realization.complementProjector G)
        (a15ProjectorArrayVector a) (a15ProjectorArrayVector b) := by
  rw [a15ProjectorQForm_expand, a15DirectQForm_expand]
  rw [realization.orbitSecondBilinear_average
    G profile hbridge a b hcompatible]

end SRG266
