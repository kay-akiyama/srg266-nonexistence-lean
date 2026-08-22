/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Mathlib.Data.List.MinMax
import Mathlib.Tactic

/-!
# A reflective bounded profile-CSP solver

Residual shell arguments use multiplicities in `{0,1,2,3}` satisfying

`mᵢ > 0 → ∑_{j ∼ i} mⱼ + 3mᵢ = 30`.

This module implements domain propagation and finite branching.  The solver
returns a superset of all possible total multiplicities, and the soundness
theorem is independent of the concrete graph. Consequently, a bounded kernel
evaluation of the solver is a checked completeness proof, not a trusted
Python enumeration.
-/

open scoped BigOperators

namespace SRG266

/-- A bounded profile value. -/
abbrev ProfileValue := Fin 4

/-- Boolean domains keep the reflective transition system compact. -/
abbrev ProfileDomains (ι : Type*) := ι → ProfileValue → Bool

def profileDomainMin (d : ProfileValue → Bool) : ℕ :=
  if d 0 then 0 else if d 1 then 1 else if d 2 then 2 else 3

def profileDomainMax (d : ProfileValue → Bool) : ℕ :=
  if d 3 then 3 else if d 2 then 2 else if d 1 then 1 else 0

theorem profileDomainMin_le
    (d : ProfileValue → Bool) (x : ProfileValue)
    (hx : d x = true) :
    profileDomainMin d ≤ x.1 := by
  fin_cases x <;>
    by_cases h0 : d 0 = true <;>
    by_cases h1 : d 1 = true <;>
    by_cases h2 : d 2 = true <;>
    simp [profileDomainMin, h0, h1, h2] at *

theorem le_profileDomainMax
    (d : ProfileValue → Bool) (x : ProfileValue)
    (hx : d x = true) :
    x.1 ≤ profileDomainMax d := by
  fin_cases x <;>
    by_cases h1 : d 1 = true <;>
    by_cases h2 : d 2 = true <;>
    by_cases h3 : d 3 = true <;>
    simp [profileDomainMax, h1, h2, h3] at *

def profileDomainValues
    (d : ProfileValue → Bool) : Finset ProfileValue :=
  Finset.univ.filter fun x => d x = true

@[simp] theorem mem_profileDomainValues
    (d : ProfileValue → Bool) (x : ProfileValue) :
    x ∈ profileDomainValues d ↔ d x = true := by
  simp [profileDomainValues]

def profileNeighbours
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (adjacent : ι → ι → Bool) (i : ι) : Finset ι :=
  Finset.univ.filter fun j => adjacent i j = true

def profileNeighbourSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (adjacent : ι → ι → Bool) (m : ι → ProfileValue)
    (i : ι) : ℕ :=
  ∑ j ∈ profileNeighbours adjacent i, (m j).1

def profileDomainLower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (adjacent : ι → ι → Bool) (domains : ProfileDomains ι)
    (i : ι) : ℕ :=
  ∑ j ∈ profileNeighbours adjacent i, profileDomainMin (domains j)

def profileDomainUpper
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (adjacent : ι → ι → Bool) (domains : ProfileDomains ι)
    (i : ι) : ℕ :=
  ∑ j ∈ profileNeighbours adjacent i, profileDomainMax (domains j)

def ProfileRespects
    {ι : Type*} (domains : ProfileDomains ι)
    (m : ι → ProfileValue) : Prop :=
  ∀ i, domains i (m i) = true

def ProfileSatisfies
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (adjacent : ι → ι → Bool) (m : ι → ProfileValue) : Prop :=
  ∀ i, (m i).1 ≠ 0 →
    profileNeighbourSum adjacent m i + 3 * (m i).1 = 30

theorem profileDomainLower_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (adjacent : ι → ι → Bool) (domains : ProfileDomains ι)
    (m : ι → ProfileValue) (hrespects : ProfileRespects domains m)
    (i : ι) :
    profileDomainLower adjacent domains i ≤
      profileNeighbourSum adjacent m i := by
  apply Finset.sum_le_sum
  intro j hj
  exact profileDomainMin_le (domains j) (m j) (hrespects j)

theorem profileNeighbourSum_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (adjacent : ι → ι → Bool) (domains : ProfileDomains ι)
    (m : ι → ProfileValue) (hrespects : ProfileRespects domains m)
    (i : ι) :
    profileNeighbourSum adjacent m i ≤
      profileDomainUpper adjacent domains i := by
  apply Finset.sum_le_sum
  intro j hj
  exact le_profileDomainMax (domains j) (m j) (hrespects j)

/-- Replace one variable domain by a singleton. -/
def profileOverride
    {ι : Type*} [DecidableEq ι]
    (domains : ProfileDomains ι) (i : ι) (x : ProfileValue) :
    ProfileDomains ι :=
  fun j y => if j = i then decide (y = x) else domains j y

theorem profileRespects_override
    {ι : Type*} [DecidableEq ι]
    {domains : ProfileDomains ι} {m : ι → ProfileValue}
    (hrespects : ProfileRespects domains m) (i : ι) :
    ProfileRespects (profileOverride domains i (m i)) m := by
  intro j
  by_cases hji : j = i
  · subst j
    simp [profileOverride]
  · simp [profileOverride, hji, hrespects j]

def ProfileFixedPositive
    (domain : ProfileValue → Bool) (x : ProfileValue) : Prop :=
  0 < x.1 ∧ domain x = true ∧
    ∀ y, domain y = true → y = x

/-- A candidate survives when its own positive constraint and every already
fixed positive constraint remain feasible by interval bounds. -/
def ProfileCandidateAllowed
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (adjacent : ι → ι → Bool) (domains : ProfileDomains ι)
    (i : ι) (x : ProfileValue) : Prop :=
  let narrowed := profileOverride domains i x
  (x.1 = 0 ∨
    (profileDomainLower adjacent narrowed i ≤ 30 - 3 * x.1 ∧
      30 - 3 * x.1 ≤ profileDomainUpper adjacent narrowed i)) ∧
  ∀ j y, adjacent j i = true →
    ProfileFixedPositive (domains j) y →
    profileDomainLower adjacent narrowed j ≤ 30 - 3 * y.1 ∧
      30 - 3 * y.1 ≤ profileDomainUpper adjacent narrowed j

instance profileCandidateAllowedDecidable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (adjacent : ι → ι → Bool) (domains : ProfileDomains ι)
    (i : ι) (x : ProfileValue) :
    Decidable (ProfileCandidateAllowed adjacent domains i x) := by
  unfold ProfileCandidateAllowed ProfileFixedPositive
  infer_instance

def profilePrune
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (adjacent : ι → ι → Bool) (domains : ProfileDomains ι) :
    ProfileDomains ι :=
  fun i x =>
    domains i x && decide (ProfileCandidateAllowed adjacent domains i x)

theorem profilePrune_sound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (adjacent : ι → ι → Bool) (domains : ProfileDomains ι)
    (m : ι → ProfileValue)
    (hsatisfies : ProfileSatisfies adjacent m)
    (hrespects : ProfileRespects domains m) :
    ProfileRespects (profilePrune adjacent domains) m := by
  intro i
  have hoverride :=
    profileRespects_override (domains := domains) hrespects i
  have hallowed : ProfileCandidateAllowed adjacent domains i (m i) := by
    dsimp only [ProfileCandidateAllowed]
    constructor
    · by_cases hzero : (m i).1 = 0
      · exact Or.inl hzero
      · right
        have heq := hsatisfies i hzero
        constructor
        · calc
            profileDomainLower adjacent
                (profileOverride domains i (m i)) i ≤
                profileNeighbourSum adjacent m i :=
              profileDomainLower_le adjacent _ m hoverride i
            _ = 30 - 3 * (m i).1 := by omega
        · calc
            30 - 3 * (m i).1 =
                profileNeighbourSum adjacent m i := by omega
            _ ≤ profileDomainUpper adjacent
                (profileOverride domains i (m i)) i :=
              profileNeighbourSum_le adjacent _ m hoverride i
    · intro j y _hji hfixed
      have hmy : m j = y :=
        hfixed.2.2 (m j) (hrespects j)
      have hpositive : (m j).1 ≠ 0 := by
        rw [hmy]
        exact Nat.ne_of_gt hfixed.1
      have heq := hsatisfies j hpositive
      constructor
      · calc
          profileDomainLower adjacent
              (profileOverride domains i (m i)) j ≤
              profileNeighbourSum adjacent m j :=
            profileDomainLower_le adjacent _ m hoverride j
          _ = 30 - 3 * y.1 := by
            rw [hmy] at heq
            omega
      · calc
          30 - 3 * y.1 =
              profileNeighbourSum adjacent m j := by
            rw [hmy] at heq
            omega
          _ ≤ profileDomainUpper adjacent
              (profileOverride domains i (m i)) j :=
            profileNeighbourSum_le adjacent _ m hoverride j
  simp [profilePrune, hrespects i, hallowed]

def profilePropagate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (adjacent : ι → ι → Bool) :
    ℕ → ProfileDomains ι → ProfileDomains ι
  | 0, domains => domains
  | fuel + 1, domains =>
      let pruned := profilePrune adjacent domains
      if pruned = domains then domains
      else profilePropagate adjacent fuel pruned

theorem profilePropagate_sound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (adjacent : ι → ι → Bool) (fuel : ℕ)
    (domains : ProfileDomains ι) (m : ι → ProfileValue)
    (hsatisfies : ProfileSatisfies adjacent m)
    (hrespects : ProfileRespects domains m) :
    ProfileRespects (profilePropagate adjacent fuel domains) m := by
  induction fuel generalizing domains with
  | zero => exact hrespects
  | succ fuel ih =>
      simp only [profilePropagate]
      split
      · exact hrespects
      · exact ih (profilePrune adjacent domains)
          (profilePrune_sound adjacent domains m hsatisfies hrespects)

def profileBadVariables
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (domains : ProfileDomains ι) : Finset ι :=
  Finset.univ.filter fun i =>
    (profileDomainValues (domains i)).card ≠ 1

def profileUnresolvedDegree
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (adjacent : ι → ι → Bool) (domains : ProfileDomains ι)
    (i : ι) : ℕ :=
  ((profileNeighbours adjacent i).filter fun j =>
    (profileDomainValues (domains j)).card ≠ 1).card

def profileBranchScore
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (adjacent : ι → ι → Bool) (domains : ProfileDomains ι)
    (i : ι) : ℕ :=
  (profileDomainValues (domains i)).card * (Fintype.card ι + 1) +
    (Fintype.card ι - profileUnresolvedDegree adjacent domains i)

def profileChooseVariable
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (adjacent : ι → ι → Bool) (domains : ProfileDomains ι) :
    Option ι :=
  ((profileBadVariables domains).sort (· ≤ ·)).argmin
    (profileBranchScore adjacent domains)

def profileTotal
    {ι : Type*} [Fintype ι] (m : ι → ProfileValue) : ℕ :=
  ∑ i, (m i).1

def profileLeafTotal
    {ι : Type*} [Fintype ι]
    (domains : ProfileDomains ι) : ℕ :=
  ∑ i, profileDomainMin (domains i)

/-- Fuel-bounded complete search. At zero depth it deliberately returns every
numerically possible total, preserving soundness even with insufficient fuel. -/
def profilePossibleTotals
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (adjacent : ι → ι → Bool) (propagationFuel : ℕ) :
    ℕ → ProfileDomains ι → Finset ℕ
  | 0, _ => Finset.range (3 * Fintype.card ι + 1)
  | depth + 1, domains =>
      let propagated :=
        profilePropagate adjacent propagationFuel domains
      match profileChooseVariable adjacent propagated with
      | none => {profileLeafTotal propagated}
      | some i =>
          (profileDomainValues (propagated i)).biUnion fun x =>
            profilePossibleTotals adjacent propagationFuel depth
              (profileOverride propagated i x)

theorem profileDomainMin_eq_of_unique
    (d : ProfileValue → Bool) (x : ProfileValue)
    (hx : d x = true)
    (hunique : ∀ y, d y = true → y = x) :
    profileDomainMin d = x.1 := by
  have hfalse (y : ProfileValue) (hyx : y ≠ x) : d y = false := by
    cases hy : d y with
    | false => rfl
    | true => exact (hyx (hunique y hy)).elim
  fin_cases x
  · have hx0 : d 0 = true := by simpa using hx
    simp [profileDomainMin, hx0]
  · have h0 := hfalse 0 (by decide)
    have hx1 : d 1 = true := by simpa using hx
    simp [profileDomainMin, h0, hx1]
  · have h0 := hfalse 0 (by decide)
    have h1 := hfalse 1 (by decide)
    have hx2 : d 2 = true := by simpa using hx
    simp [profileDomainMin, h0, h1, hx2]
  · have h0 := hfalse 0 (by decide)
    have h1 := hfalse 1 (by decide)
    have h2 := hfalse 2 (by decide)
    simp [profileDomainMin, h0, h1, h2]

theorem profilePossibleTotals_sound
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (adjacent : ι → ι → Bool) (propagationFuel depth : ℕ)
    (domains : ProfileDomains ι) (m : ι → ProfileValue)
    (hsatisfies : ProfileSatisfies adjacent m)
    (hrespects : ProfileRespects domains m) :
    profileTotal m ∈
      profilePossibleTotals adjacent propagationFuel depth domains := by
  induction depth generalizing domains with
  | zero =>
      simp only [profilePossibleTotals, Finset.mem_range]
      have hle :
          profileTotal m ≤ 3 * Fintype.card ι := by
        calc
          profileTotal m = ∑ i, (m i).1 := rfl
          _ ≤ ∑ _i : ι, 3 := by
            apply Finset.sum_le_sum
            intro i hi
            exact Nat.le_of_lt_succ (m i).2
          _ = 3 * Fintype.card ι := by
            simp [mul_comm]
      omega
  | succ depth ih =>
      let propagated :=
        profilePropagate adjacent propagationFuel domains
      have hpropagated : ProfileRespects propagated m :=
        profilePropagate_sound adjacent propagationFuel domains m
          hsatisfies hrespects
      cases hchoose :
          profileChooseVariable adjacent propagated with
      | none =>
          simp only [profilePossibleTotals, propagated, hchoose,
            Finset.mem_singleton]
          apply Finset.sum_congr rfl
          intro i hi
          have hnotbad :
              (profileDomainValues (propagated i)).card = 1 := by
            by_contra hcard
            have himem : i ∈ profileBadVariables propagated := by
              simp [profileBadVariables, hcard]
            have hargmin :
                ((profileBadVariables propagated).sort (· ≤ ·)).argmin
                    (profileBranchScore adjacent propagated) = none := by
              simpa only [profileChooseVariable] using hchoose
            have hsorted :
                (profileBadVariables propagated).sort (· ≤ ·) = [] :=
              List.argmin_eq_none.mp hargmin
            have himemsort :
                i ∈ (profileBadVariables propagated).sort (· ≤ ·) := by
              simpa using himem
            rw [hsorted] at himemsort
            simp at himemsort
          obtain ⟨x, hxvalues⟩ :=
            Finset.card_eq_one.mp hnotbad
          have hmvalues :
              m i ∈ profileDomainValues (propagated i) :=
            (mem_profileDomainValues _ _).2 (hpropagated i)
          have hmx : m i = x := by
            rw [hxvalues] at hmvalues
            simpa using hmvalues
          symm
          apply profileDomainMin_eq_of_unique
          · exact hpropagated i
          · intro y hy
            have hyvalues :
                y ∈ profileDomainValues (propagated i) :=
              (mem_profileDomainValues _ _).2 hy
            rw [hxvalues] at hyvalues
            have hyx : y = x := by simpa using hyvalues
            exact hyx.trans hmx.symm
      | some i =>
          simp only [profilePossibleTotals, propagated, hchoose,
            Finset.mem_biUnion]
          refine ⟨m i, ?_, ?_⟩
          · exact (mem_profileDomainValues _ _).2 (hpropagated i)
          · exact ih (profileOverride propagated i (m i))
              (profileRespects_override hpropagated i)

def fullProfileDomains (ι : Type*) : ProfileDomains ι :=
  fun _ _ => true

theorem profileRespects_full
    {ι : Type*} (m : ι → ProfileValue) :
    ProfileRespects (fullProfileDomains ι) m := by
  simp [ProfileRespects, fullProfileDomains]

end SRG266
