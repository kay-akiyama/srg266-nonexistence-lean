/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.E7ScalarDPSound

/-!
# A pruned refutation search for the scalar target equations

`e7ScalarDPFeasible` cannot be evaluated by the kernel: it sorts its state
list.  To refute a histogram pair the kernel therefore runs `e7ScalarSearch`,
a plain structural depth-first search for a list of category usages meeting
`∑ xᵢ = total` and `∑ vᵢ xᵢ = target`.

Only the completeness direction is proved: if usages exist then the search
accepts.  A kernel evaluation returning `false` therefore refutes the pair,
and no property of the two prunings has to be believed -- an unsound pruning
would only make the completeness proof fail.

Two prunings keep the search small.  Capacities bound the total usage, and
the smallest and largest category values bound the attainable moment.  The
zero-capacity categories are dropped first, which turns the 43-entry category
list into at most four entries.
-/

namespace SRG266

set_option maxRecDepth 100000

/-- Total capacity of a list of categories. -/
def e7ScalarCapacitySum : List (ℤ × ℕ) → ℕ
  | [] => 0
  | category :: categories => category.2 + e7ScalarCapacitySum categories

/-- Smallest category value, starting from an accumulator. -/
def e7ScalarLoFrom : ℤ → List (ℤ × ℕ) → ℤ
  | accumulator, [] => accumulator
  | accumulator, category :: categories =>
      e7ScalarLoFrom (min accumulator category.1) categories

/-- Largest category value, starting from an accumulator. -/
def e7ScalarHiFrom : ℤ → List (ℤ × ℕ) → ℤ
  | accumulator, [] => accumulator
  | accumulator, category :: categories =>
      e7ScalarHiFrom (max accumulator category.1) categories

/-- Drop the categories that cannot be used at all. -/
def e7ScalarCompress : List (ℤ × ℕ) → List (ℤ × ℕ)
  | [] => []
  | category :: categories =>
      if category.2 = 0 then e7ScalarCompress categories
      else category :: e7ScalarCompress categories

/-- Depth-first search for category usages meeting both target equations. -/
def e7ScalarSearch : List (ℤ × ℕ) → ℕ → ℤ → Bool
  | [], total, target => decide (total = 0) && decide (target = 0)
  | category :: categories, total, target =>
      if decide (e7ScalarCapacitySum (category :: categories) < total) then
        false
      else if decide
          (target < e7ScalarLoFrom category.1 categories * (total : ℤ)) then
        false
      else if decide
          (e7ScalarHiFrom category.1 categories * (total : ℤ) < target) then
        false
      else
        (List.range (min category.2 total + 1)).any fun x =>
          e7ScalarSearch categories (total - x) (target - category.1 * x)

theorem e7ScalarSum_le_capacity
    (categories : List (ℤ × ℕ)) (choices : List ℕ)
    (hchoices : List.Forall₂ (fun category x => x ≤ category.2)
      categories choices) :
    choices.sum ≤ e7ScalarCapacitySum categories := by
  induction hchoices with
  | nil => simp [e7ScalarCapacitySum]
  | cons hx _ ih =>
      simp only [List.sum_cons, e7ScalarCapacitySum]
      omega

theorem e7ScalarLoFrom_le
    (accumulator : ℤ) (categories : List (ℤ × ℕ)) :
    e7ScalarLoFrom accumulator categories ≤ accumulator := by
  induction categories generalizing accumulator with
  | nil => exact le_rfl
  | cons category categories ih =>
      exact le_trans (ih _) (min_le_left _ _)

theorem e7ScalarLoFrom_le_mem
    (accumulator : ℤ) (categories : List (ℤ × ℕ))
    (category : ℤ × ℕ) (hcategory : category ∈ categories) :
    e7ScalarLoFrom accumulator categories ≤ category.1 := by
  induction categories generalizing accumulator with
  | nil => simp at hcategory
  | cons head categories ih =>
      rcases List.mem_cons.mp hcategory with h | h
      · rw [h]
        show e7ScalarLoFrom (min accumulator head.1) categories ≤ head.1
        exact le_trans (e7ScalarLoFrom_le _ _) (min_le_right _ _)
      · exact ih _ h

theorem e7ScalarHiFrom_ge
    (accumulator : ℤ) (categories : List (ℤ × ℕ)) :
    accumulator ≤ e7ScalarHiFrom accumulator categories := by
  induction categories generalizing accumulator with
  | nil => exact le_rfl
  | cons category categories ih =>
      exact le_trans (le_max_left _ _) (ih _)

theorem e7ScalarHiFrom_ge_mem
    (accumulator : ℤ) (categories : List (ℤ × ℕ))
    (category : ℤ × ℕ) (hcategory : category ∈ categories) :
    category.1 ≤ e7ScalarHiFrom accumulator categories := by
  induction categories generalizing accumulator with
  | nil => simp at hcategory
  | cons head categories ih =>
      rcases List.mem_cons.mp hcategory with h | h
      · rw [h]
        show head.1 ≤ e7ScalarHiFrom (max accumulator head.1) categories
        exact le_trans (le_max_right _ _) (e7ScalarHiFrom_ge _ _)
      · exact ih _ h

theorem e7ScalarWeighted_lower_bound (bound : ℤ) :
    ∀ (categories : List (ℤ × ℕ)) (choices : List ℕ),
      List.Forall₂ (fun category x => x ≤ category.2) categories choices →
      (∀ category ∈ categories, bound ≤ category.1) →
      bound * (choices.sum : ℤ) ≤ e7ScalarWeighted categories choices := by
  intro categories choices hchoices
  induction hchoices with
  | nil => intro _; simp [e7ScalarWeighted]
  | cons _ _ ih =>
      rename_i category x categories choices _ _
      intro hbound
      have hhead : bound ≤ category.1 := hbound category List.mem_cons_self
      have htail := ih fun c hc => hbound c (List.mem_cons_of_mem _ hc)
      have hx : bound * (x : ℤ) ≤ category.1 * (x : ℤ) :=
        mul_le_mul_of_nonneg_right hhead (Int.natCast_nonneg x)
      simp only [List.sum_cons, e7ScalarWeighted, Nat.cast_add]
      linarith

theorem e7ScalarWeighted_upper_bound (bound : ℤ) :
    ∀ (categories : List (ℤ × ℕ)) (choices : List ℕ),
      List.Forall₂ (fun category x => x ≤ category.2) categories choices →
      (∀ category ∈ categories, category.1 ≤ bound) →
      e7ScalarWeighted categories choices ≤ bound * (choices.sum : ℤ) := by
  intro categories choices hchoices
  induction hchoices with
  | nil => intro _; simp [e7ScalarWeighted]
  | cons _ _ ih =>
      rename_i category x categories choices _ _
      intro hbound
      have hhead : category.1 ≤ bound := hbound category List.mem_cons_self
      have htail := ih fun c hc => hbound c (List.mem_cons_of_mem _ hc)
      have hx : category.1 * (x : ℤ) ≤ bound * (x : ℤ) :=
        mul_le_mul_of_nonneg_right hhead (Int.natCast_nonneg x)
      simp only [List.sum_cons, e7ScalarWeighted, Nat.cast_add]
      linarith

/-- The search accepts every list of category usages. -/
theorem e7ScalarSearch_complete :
    ∀ (categories : List (ℤ × ℕ)) (choices : List ℕ),
      List.Forall₂ (fun category x => x ≤ category.2) categories choices →
      e7ScalarSearch categories choices.sum
        (e7ScalarWeighted categories choices) = true := by
  intro categories choices hchoices
  induction hchoices with
  | nil => simp [e7ScalarSearch, e7ScalarWeighted]
  | cons hx htail ih =>
      rename_i category x categories choices
      have hcapacity :
          ¬ (e7ScalarCapacitySum (category :: categories) < (x :: choices).sum) := by
        have := e7ScalarSum_le_capacity categories choices htail
        simp only [e7ScalarCapacitySum, List.sum_cons]
        omega
      have hlo :
          ¬ (e7ScalarWeighted (category :: categories) (x :: choices) <
            e7ScalarLoFrom category.1 categories * ((x :: choices).sum : ℤ)) := by
        have := e7ScalarWeighted_lower_bound
          (e7ScalarLoFrom category.1 categories)
          (category :: categories) (x :: choices)
          (List.Forall₂.cons hx htail)
          (by
            intro c hc
            rcases List.mem_cons.mp hc with h | h
            · subst h; exact e7ScalarLoFrom_le _ _
            · exact e7ScalarLoFrom_le_mem _ _ _ h)
        omega
      have hhi :
          ¬ (e7ScalarHiFrom category.1 categories * ((x :: choices).sum : ℤ) <
            e7ScalarWeighted (category :: categories) (x :: choices)) := by
        have := e7ScalarWeighted_upper_bound
          (e7ScalarHiFrom category.1 categories)
          (category :: categories) (x :: choices)
          (List.Forall₂.cons hx htail)
          (by
            intro c hc
            rcases List.mem_cons.mp hc with h | h
            · subst h; exact e7ScalarHiFrom_ge _ _
            · exact e7ScalarHiFrom_ge_mem _ _ _ h)
        omega
      rw [e7ScalarSearch]
      simp only [decide_eq_true_eq, hcapacity, if_false, hlo, hhi,
        List.any_eq_true, List.mem_range]
      refine ⟨x, ?_, ?_⟩
      · simp only [List.sum_cons]
        have : x ≤ min category.2 (x + choices.sum) := by
          simp only [le_min_iff]
          exact ⟨hx, by omega⟩
        omega
      · have hsum : (x :: choices).sum - x = choices.sum := by
          simp only [List.sum_cons]; omega
        have hweight :
            e7ScalarWeighted (category :: categories) (x :: choices) -
                category.1 * x =
              e7ScalarWeighted categories choices := by
          simp only [e7ScalarWeighted]; ring
        rw [hsum, hweight]
        exact ih

theorem e7ScalarCompress_choices :
    ∀ (categories : List (ℤ × ℕ)) (choices : List ℕ),
      List.Forall₂ (fun category x => x ≤ category.2) categories choices →
      ∃ compressed : List ℕ,
        List.Forall₂ (fun category x => x ≤ category.2)
          (e7ScalarCompress categories) compressed ∧
        compressed.sum = choices.sum ∧
        e7ScalarWeighted (e7ScalarCompress categories) compressed =
          e7ScalarWeighted categories choices := by
  intro categories choices hchoices
  induction hchoices with
  | nil => exact ⟨[], List.Forall₂.nil, rfl, rfl⟩
  | cons hx _ ih =>
      rename_i category x categories choices _
      obtain ⟨compressed, hcompressed, hsum, hweight⟩ := ih
      by_cases hzero : category.2 = 0
      · have hx0 : x = 0 := by omega
        refine ⟨compressed, ?_, ?_, ?_⟩
        · simpa only [e7ScalarCompress, hzero, if_pos] using hcompressed
        · simp only [List.sum_cons, hsum, hx0, Nat.zero_add]
        · simp only [e7ScalarCompress, hzero, if_pos, hweight, e7ScalarWeighted,
            hx0, Nat.cast_zero, mul_zero, zero_add]
      · refine ⟨x :: compressed, ?_, ?_, ?_⟩
        · have hcons :
              List.Forall₂ (fun (c : ℤ × ℕ) (y : ℕ) => y ≤ c.2)
                (category :: e7ScalarCompress categories) (x :: compressed) :=
            List.Forall₂.cons hx hcompressed
          simpa only [e7ScalarCompress, if_neg hzero] using hcons
        · simp only [List.sum_cons, hsum]
        · simp only [e7ScalarCompress, hzero, if_neg, not_false_iff,
            e7ScalarWeighted, hweight]

/-- A search that fails refutes the scalar dynamic program. -/
theorem e7ScalarDPFeasible_eq_false_of_search
    (left right : E7ComponentKey)
    (hsearch :
      e7ScalarSearch (e7ScalarCompress (e7ScalarCategories left right))
        220 (11 * (left.norm : ℤ)) = false) :
    e7ScalarDPFeasible (left, right) = false := by
  by_cases hfeasible : e7ScalarDPFeasible (left, right) = true
  · exfalso
    obtain ⟨choices, hchoices, hsum, hweight⟩ :=
      e7ScalarDPFeasible_sound left right hfeasible
    obtain ⟨compressed, hcompressed, hcsum, hcweight⟩ :=
      e7ScalarCompress_choices _ _ hchoices
    have := e7ScalarSearch_complete _ _ hcompressed
    rw [hcsum, hsum, hcweight, hweight] at this
    rw [this] at hsearch
    exact Bool.noConfusion hsearch
  · simpa only [Bool.not_eq_true] using hfeasible

end SRG266
