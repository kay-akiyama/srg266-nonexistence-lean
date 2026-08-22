/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7ComponentEnumeration
import SRG266.Hosts.E7WeightCore

/-!
# Histogram reduction for E7 component profiles

Each one-factor profile is replaced by its squared norm and the histogram of
its 56 minuscule-weight evaluations.  The histogram has 43 bins indexed by
the values `-21,...,21`.  Sorting and adjacent deduplication reduce the
120,036 profiles to the finite component-key universe used by the pair
filters.
-/

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Minuscule evaluation `y · W4 / 8`. -/
def e7ComponentEvaluation
    (profile : Array ℤ) (w : E7WeightIndex) : ℤ :=
  integerDot (e7ComponentEnumerationProfile profile) (e7Weight4 w) / 8

/-- The 43-bin evaluation histogram, with bin zero representing `-21`. -/
def e7ComponentHistogram (profile : Array ℤ) : Array ℕ :=
  ([false, true].flatMap fun sign =>
      (List.finRange e7Pairs.length).map fun pair => (sign, pair)).foldl
    (fun counts w =>
      let index := (e7ComponentEvaluation profile w + 21).toNat
      counts.set! index (counts.getD index 0 + 1))
    (Array.replicate 43 0)

def e7ComponentNorm (profile : Array ℤ) : ℕ :=
  ((profile.foldl (fun total z => total + z * z) 0).toNat) / 4

structure E7ComponentKey where
  norm : ℕ
  histogram : Array ℕ
  deriving DecidableEq, BEq, Ord

def e7ComponentKey (profile : Array ℤ) : E7ComponentKey where
  norm := e7ComponentNorm profile
  histogram := e7ComponentHistogram profile

def e7DedupAdjacentGo [DecidableEq α] :
    α → List α → List α
  | _, [] => []
  | previous, x :: xs =>
      if previous = x then
        e7DedupAdjacentGo previous xs
      else
        x :: e7DedupAdjacentGo x xs

/-- Linear deduplication for an already sorted list. -/
def e7DedupAdjacent [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => x :: e7DedupAdjacentGo x xs

private theorem e7DedupAdjacentGo_mem_of_mem
    [DecidableEq α]
    (previous a : α) (xs : List α)
    (ha : a = previous ∨ a ∈ xs) :
    a = previous ∨ a ∈ e7DedupAdjacentGo previous xs := by
  induction xs generalizing previous with
  | nil => exact ha
  | cons x xs ih =>
      simp only [List.mem_cons] at ha
      by_cases heq : previous = x
      · simp only [e7DedupAdjacentGo, heq, ↓reduceIte]
        apply ih x
        rcases ha with h | h | h
        · exact Or.inl (h.trans heq)
        · exact Or.inl h
        · exact Or.inr h
      · simp only [e7DedupAdjacentGo, heq, ↓reduceIte, List.mem_cons]
        rcases ha with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · rcases ih x (Or.inr h) with hax | htail
          · exact Or.inr (Or.inl hax)
          · exact Or.inr (Or.inr htail)

theorem e7DedupAdjacent_mem_of_mem
    [DecidableEq α]
    (a : α) (xs : List α) (ha : a ∈ xs) :
    a ∈ e7DedupAdjacent xs := by
  cases xs with
  | nil => simp at ha
  | cons x xs =>
      simp only [e7DedupAdjacent, List.mem_cons]
      rcases e7DedupAdjacentGo_mem_of_mem x a xs (by
        simpa only [List.mem_cons] using ha) with h | h
      · exact Or.inl h
      · exact Or.inr h

theorem e7DedupAdjacentGo_subset
    [DecidableEq α]
    (previous a : α) (xs : List α)
    (ha : a ∈ e7DedupAdjacentGo previous xs) :
    a ∈ xs := by
  induction xs generalizing previous with
  | nil => simpa only [e7DedupAdjacentGo] using ha
  | cons x xs ih =>
      by_cases heq : previous = x
      · simp only [e7DedupAdjacentGo, heq, ↓reduceIte] at ha
        exact List.mem_cons_of_mem _ (ih x ha)
      · simp only [e7DedupAdjacentGo, heq, ↓reduceIte, List.mem_cons] at ha
        rcases ha with h | h
        · rw [h]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih x h)

/-- Adjacent deduplication only removes entries. -/
theorem e7DedupAdjacent_subset
    [DecidableEq α]
    (a : α) (xs : List α) (ha : a ∈ e7DedupAdjacent xs) :
    a ∈ xs := by
  cases xs with
  | nil => simpa only [e7DedupAdjacent] using ha
  | cons x xs =>
      simp only [e7DedupAdjacent, List.mem_cons] at ha
      rcases ha with h | h
      · rw [h]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (e7DedupAdjacentGo_subset x a xs h)

def e7ComponentKeyLe (a b : E7ComponentKey) : Bool :=
  (compare a b).isLE

def e7EnumeratedComponentKeys : List E7ComponentKey :=
  e7DedupAdjacent
    ((e7EnumeratedComponentProfiles.map e7ComponentKey).mergeSort
      e7ComponentKeyLe)

theorem e7ComponentKey_mem_of_profile_mem
    (profile : Array ℤ)
    (hprofile : profile ∈ e7EnumeratedComponentProfiles) :
    e7ComponentKey profile ∈ e7EnumeratedComponentKeys := by
  apply e7DedupAdjacent_mem_of_mem
  simp only [List.mem_mergeSort, List.mem_map]
  exact ⟨profile, hprofile, rfl⟩

/-- The enumerated component keys of one squared norm. -/
def e7ComponentKeysAtNorm (norm : ℕ) : List E7ComponentKey :=
  e7EnumeratedComponentKeys.filter fun key => key.norm = norm

theorem mem_e7ComponentKeysAtNorm
    (key : E7ComponentKey) (norm : ℕ) :
    key ∈ e7ComponentKeysAtNorm norm ↔
      key ∈ e7EnumeratedComponentKeys ∧ key.norm = norm := by
  simp [e7ComponentKeysAtNorm]

/-- Eligible paired-shell cardinality from the two evaluation histograms. -/
def e7HistogramEligibleCount
    (left right : E7ComponentKey) : ℕ :=
  (List.range 43).foldl (fun total k =>
    total +
      left.histogram.getD k 0 *
        right.histogram.getD (57 - k) 0) 0

/-- The 87,624 norm-complementary oriented histogram pairs are generated
without a quadratic scan over all 5,253 keys. -/
def e7NormComplementaryHistogramPairs :
    List (E7ComponentKey × E7ComponentKey) :=
  (List.range 151).flatMap fun halfNorm =>
    let norm := 2 * halfNorm
    let left := e7ComponentKeysAtNorm norm
    let right := e7ComponentKeysAtNorm (300 - norm)
    left.flatMap fun leftKey =>
      right.map fun rightKey => (leftKey, rightKey)

theorem pair_mem_e7NormComplementaryHistogramPairs
    (left right : E7ComponentKey)
    (hleft : left ∈ e7EnumeratedComponentKeys)
    (hright : right ∈ e7EnumeratedComponentKeys)
    (heven : Even left.norm)
    (hnorm : left.norm + right.norm = 300) :
    (left, right) ∈ e7NormComplementaryHistogramPairs := by
  obtain ⟨halfNorm, hhalfNorm⟩ := heven
  have hhalfRange : halfNorm ∈ List.range 151 := by
    simp only [List.mem_range]
    omega
  simp only [e7NormComplementaryHistogramPairs, List.mem_flatMap]
  refine ⟨halfNorm, hhalfRange, ?_⟩
  simp only [List.mem_map]
  refine ⟨left, ?_, right, ?_, rfl⟩
  · rw [mem_e7ComponentKeysAtNorm]
    constructor
    · exact hleft
    · omega
  · rw [mem_e7ComponentKeysAtNorm]
    constructor
    · exact hright
    · omega

def e7EligibleHistogramPairs :
    List (E7ComponentKey × E7ComponentKey) :=
  e7NormComplementaryHistogramPairs.filter
    (fun pair => 74 ≤ e7HistogramEligibleCount pair.1 pair.2)

theorem pair_mem_e7EligibleHistogramPairs
    (left right : E7ComponentKey)
    (hpair : (left, right) ∈ e7NormComplementaryHistogramPairs)
    (hcount : 74 ≤ e7HistogramEligibleCount left right) :
    (left, right) ∈ e7EligibleHistogramPairs := by
  simp [e7EligibleHistogramPairs, hpair, hcount]

end SRG266
