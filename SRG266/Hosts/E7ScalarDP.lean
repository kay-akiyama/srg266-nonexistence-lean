/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.E7HistogramEnumeration

/-!
# Exact scalar dynamic programming for E7 histogram pairs

For an eligible histogram pair, bin `t` contains
`h₁(t) h₂(15-t)` shell columns.  Since every column has multiplicity at
most three, its aggregate usage is bounded by three times that number.

The dynamic program records the total usage and the left scalar moment.  It
accepts only the exact target `(220, 11 * norm₁)`.  A generic witness theorem
below proves that any list of category usages satisfying the capacities and
the target equations is retained by the executable checker.
-/

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

structure E7ScalarState where
  used : ℕ
  value : ℤ
  deriving DecidableEq, BEq, Ord

/-- Category `(evaluation, capacity)` for one left evaluation bin. -/
def e7ScalarCategories
    (left right : E7ComponentKey) : List (ℤ × ℕ) :=
  (List.range 43).map fun (k : ℕ) =>
    ((k : ℤ) - 21,
      3 * left.histogram.getD k 0 *
        right.histogram.getD (57 - k) 0)

def e7ScalarStateLe (a b : E7ScalarState) : Bool :=
  (compare a b).isLE

/-- Extend all current states by one category and discard usages above 220. -/
def e7ScalarStep
    (category : ℤ × ℕ) (states : List E7ScalarState) :
    List E7ScalarState :=
  e7DedupAdjacent <|
    (states.flatMap fun state =>
      (List.range
        (min category.2 (220 - state.used) + 1)).map fun x =>
          { used := state.used + x
            value := state.value + category.1 * x }).mergeSort
      e7ScalarStateLe

def e7ScalarRun
    (categories : List (ℤ × ℕ))
    (states : List E7ScalarState := [{ used := 0, value := 0 }]) :
    List E7ScalarState :=
  categories.foldl (fun current category =>
    e7ScalarStep category current) states

def e7ScalarTarget (left : E7ComponentKey) : E7ScalarState where
  used := 220
  value := 11 * left.norm

def e7ScalarDPFeasible
    (pair : E7ComponentKey × E7ComponentKey) : Bool :=
  (e7ScalarRun (e7ScalarCategories pair.1 pair.2)).any fun state =>
    decide (state = e7ScalarTarget pair.1)

def e7ScalarFeasibleHistogramPairs :
    List (E7ComponentKey × E7ComponentKey) :=
  e7EligibleHistogramPairs.filter e7ScalarDPFeasible

def e7TraceFeasibleHistogramPairs :
    List (E7ComponentKey × E7ComponentKey) :=
  e7ScalarFeasibleHistogramPairs.filter fun pair =>
    decide (38 ≤ pair.1.norm ∧ pair.1.norm ≤ 262)

theorem mem_e7ScalarStep
    (category : ℤ × ℕ) (states : List E7ScalarState)
    (state : E7ScalarState) (x : ℕ)
    (hstate : state ∈ states)
    (hxcap : x ≤ category.2)
    (hused : state.used + x ≤ 220) :
    { used := state.used + x
      value := state.value + category.1 * x } ∈
        e7ScalarStep category states := by
  apply e7DedupAdjacent_mem_of_mem
  simp only [List.mem_mergeSort, List.mem_flatMap, List.mem_map]
  refine ⟨state, hstate, x, ?_, rfl⟩
  simp only [List.mem_range]
  omega

/-- Apply a category-choice witness to an initial state. -/
def e7ScalarApplyChoices :
    E7ScalarState → List (ℤ × ℕ) → List ℕ → E7ScalarState
  | state, [], _ => state
  | state, _, [] => state
  | state, category :: categories, x :: choices =>
      e7ScalarApplyChoices
        { used := state.used + x
          value := state.value + category.1 * x }
        categories choices

theorem mem_e7ScalarRun_of_choices
    (categories : List (ℤ × ℕ))
    (choices : List ℕ)
    (state : E7ScalarState)
    (states : List E7ScalarState)
    (hstate : state ∈ states)
    (hchoices :
      List.Forall₂ (fun category x => x ≤ category.2)
        categories choices)
    (hused : state.used + choices.sum ≤ 220) :
    e7ScalarApplyChoices state categories choices ∈
      e7ScalarRun categories states := by
  induction hchoices generalizing state states with
  | nil =>
      simpa [e7ScalarApplyChoices, e7ScalarRun] using hstate
  | cons hx htail ih =>
      simp only [List.sum_cons] at hused
      simp only [e7ScalarRun, List.foldl_cons]
      apply ih
      · apply mem_e7ScalarStep _ states state _ hstate hx
        omega
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hused

theorem e7ScalarDPFeasible_of_choices
    (left right : E7ComponentKey)
    (choices : List ℕ)
    (hchoices :
      List.Forall₂ (fun category x => x ≤ category.2)
        (e7ScalarCategories left right) choices)
    (hsum : choices.sum = 220)
    (hresult :
      e7ScalarApplyChoices { used := 0, value := 0 }
          (e7ScalarCategories left right) choices =
        e7ScalarTarget left) :
    e7ScalarDPFeasible (left, right) = true := by
  unfold e7ScalarDPFeasible
  rw [List.any_eq_true]
  refine ⟨e7ScalarTarget left, ?_, by simp⟩
  rw [← hresult]
  apply mem_e7ScalarRun_of_choices
  · simp
  · exact hchoices
  · simp [hsum]

theorem pair_mem_e7ScalarFeasibleHistogramPairs
    (pair : E7ComponentKey × E7ComponentKey)
    (hpair : pair ∈ e7EligibleHistogramPairs)
    (hfeasible : e7ScalarDPFeasible pair = true) :
    pair ∈ e7ScalarFeasibleHistogramPairs := by
  simp [e7ScalarFeasibleHistogramPairs, hpair, hfeasible]

theorem pair_mem_e7TraceFeasibleHistogramPairs
    (pair : E7ComponentKey × E7ComponentKey)
    (hpair : pair ∈ e7ScalarFeasibleHistogramPairs)
    (hlower : 38 ≤ pair.1.norm)
    (hupper : pair.1.norm ≤ 262) :
    pair ∈ e7TraceFeasibleHistogramPairs := by
  simp [e7TraceFeasibleHistogramPairs, hpair, hlower, hupper]

end SRG266
