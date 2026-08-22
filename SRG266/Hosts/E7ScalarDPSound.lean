/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7ScalarDP

/-!
# Soundness of the bounded scalar dynamic program

`SRG266/Hosts/E7ScalarDP.lean` proves that every admissible list of category
usages is retained by `e7ScalarDPFeasible`.  Refuting a histogram pair needs
the converse: an accepted pair must come from an actual list of usages.

Every state produced by `e7ScalarStep` is a sorted, deduplicated repackaging
of one extension of an earlier state, so `List.mem_mergeSort` and
`e7DedupAdjacent_subset` invert the step without ever evaluating the sort.
-/

namespace SRG266

set_option maxRecDepth 100000

theorem mem_e7ScalarStep_inv
    (category : ℤ × ℕ) (states : List E7ScalarState)
    (state : E7ScalarState)
    (hstate : state ∈ e7ScalarStep category states) :
    ∃ previous ∈ states, ∃ x : ℕ, x ≤ category.2 ∧
      state =
        { used := previous.used + x
          value := previous.value + category.1 * x } := by
  have hsorted := e7DedupAdjacent_subset _ _ hstate
  rw [List.mem_mergeSort] at hsorted
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hsorted
  obtain ⟨previous, hprevious, x, hx, heq⟩ := hsorted
  refine ⟨previous, hprevious, x, ?_, heq.symm⟩
  have := Nat.le_of_lt_succ hx
  exact le_trans this (Nat.min_le_left _ _)

theorem e7ScalarRun_sound :
    ∀ (categories : List (ℤ × ℕ)) (states : List E7ScalarState)
      (state : E7ScalarState),
      state ∈ e7ScalarRun categories states →
      ∃ start ∈ states, ∃ choices : List ℕ,
        List.Forall₂ (fun category x => x ≤ category.2) categories choices ∧
        state = e7ScalarApplyChoices start categories choices := by
  intro categories
  induction categories with
  | nil =>
      intro states state hstate
      exact ⟨state, by simpa only [e7ScalarRun, List.foldl_nil] using hstate,
        [], List.Forall₂.nil, rfl⟩
  | cons category categories ih =>
      intro states state hstate
      simp only [e7ScalarRun, List.foldl_cons] at hstate
      obtain ⟨middle, hmiddle, choices, hchoices, heq⟩ := ih _ state hstate
      obtain ⟨start, hstart, x, hx, hmiddleEq⟩ :=
        mem_e7ScalarStep_inv category states middle hmiddle
      refine ⟨start, hstart, x :: choices,
        List.Forall₂.cons hx hchoices, ?_⟩
      rw [heq, hmiddleEq]
      rfl

/-- The weighted scalar moment of one list of category usages. -/
def e7ScalarWeighted : List (ℤ × ℕ) → List ℕ → ℤ
  | [], _ => 0
  | _, [] => 0
  | category :: categories, x :: choices =>
      category.1 * (x : ℤ) + e7ScalarWeighted categories choices

theorem e7ScalarApplyChoices_eq :
    ∀ (categories : List (ℤ × ℕ)) (choices : List ℕ),
      List.Forall₂ (fun category x => x ≤ category.2) categories choices →
      ∀ state : E7ScalarState,
        e7ScalarApplyChoices state categories choices =
          { used := state.used + choices.sum
            value := state.value + e7ScalarWeighted categories choices } := by
  intro categories choices hchoices
  induction hchoices with
  | nil => intro state; simp [e7ScalarApplyChoices, e7ScalarWeighted]
  | cons _ _ ih =>
      intro state
      simp only [e7ScalarApplyChoices, ih, List.sum_cons, e7ScalarWeighted,
        E7ScalarState.mk.injEq]
      constructor
      · omega
      · ring

/-- An accepted histogram pair really has a list of category usages meeting
both target equations. -/
theorem e7ScalarDPFeasible_sound
    (left right : E7ComponentKey)
    (hfeasible : e7ScalarDPFeasible (left, right) = true) :
    ∃ choices : List ℕ,
      List.Forall₂ (fun category x => x ≤ category.2)
        (e7ScalarCategories left right) choices ∧
      choices.sum = 220 ∧
      e7ScalarWeighted (e7ScalarCategories left right) choices =
        11 * left.norm := by
  rw [e7ScalarDPFeasible, List.any_eq_true] at hfeasible
  obtain ⟨state, hstate, htarget⟩ := hfeasible
  rw [decide_eq_true_eq] at htarget
  obtain ⟨start, hstart, choices, hchoices, hstateEq⟩ :=
    e7ScalarRun_sound _ _ _ hstate
  simp only [List.mem_singleton] at hstart
  subst hstart
  rw [e7ScalarApplyChoices_eq _ _ hchoices] at hstateEq
  rw [hstateEq] at htarget
  simp only [e7ScalarTarget, E7ScalarState.mk.injEq, zero_add] at htarget
  exact ⟨choices, hchoices, htarget.1, htarget.2⟩

end SRG266
