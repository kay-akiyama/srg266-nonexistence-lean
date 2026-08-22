/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7ComponentCode

/-!
# A packed-code reformulation of the E7 component key

`e7ComponentHistogram` evaluates 56 minuscule weights through `Finset` sums
over `Fin 8` and a 28-element index list.  That is far too slow for a kernel
sweep over the 120,036 enumerated component profiles.

Every minuscule weight is `±(3, 3, -1, -1, -1, -1, -1, -1)` up to a
coordinate permutation, so the evaluation at the weight indexed by the
coordinate pair `(i, j)` equals `(4 * (yᵢ + yⱼ) - ∑ y) / 8`.  Feeding those
28 differences through `e7PairCode` reproduces the whole histogram as the
base-`2^18` digits of a single natural number, and eight-way pattern matching
on the coordinate list removes the remaining list indexing.

The resulting `e7ComponentKey_eq_ofCode` is the bridge that lets the coverage
sweep recognise a profile with a handful of `Nat` operations.
-/

namespace SRG266

open scoped BigOperators

set_option maxRecDepth 40000

/-- Every minuscule weight is `3` on two coordinates and `-1` elsewhere. -/
theorem e7Weight_sum (y : Fin 8 → ℤ) (i j : Fin 8) (hij : i ≠ j) :
    ∑ k, y k * (if k = i ∨ k = j then (3 : ℤ) else -1) =
      4 * (y i + y j) - ∑ k, y k := by
  have h1 : ∀ k : Fin 8, y k * (if k = i ∨ k = j then (3 : ℤ) else -1)
      = 4 * (if k = i then y i else 0) + 4 * (if k = j then y j else 0) - y k := by
    intro k
    by_cases hki : k = i
    · subst hki
      have hkj : k ≠ j := hij
      simp [hkj]; ring
    · by_cases hkj : k = j
      · subst hkj; simp [hki]; ring
      · simp [hki, hkj]
  rw [Finset.sum_congr rfl (fun k _ => h1 k)]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  simp
  ring

/-- The minuscule evaluation of a component profile at the weight indexed by
one coordinate pair. -/
theorem e7ComponentEvaluation_pair
    (profile : Array ℤ) (sign : Bool) (t : Fin e7Pairs.length) :
    e7ComponentEvaluation profile (sign, t) =
      (let y := e7ComponentEnumerationProfile profile
       let d := 4 * (y (e7Pairs.get t).1 + y (e7Pairs.get t).2) - ∑ k, y k
       (if sign then -d else d) / 8) := by
  have hne : (e7Pairs.get t).1 ≠ (e7Pairs.get t).2 := by
    revert t; decide
  simp only [e7ComponentEvaluation, integerDot, e7Weight4]
  cases sign with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      rw [e7Weight_sum _ _ _ hne]
  | true =>
      simp only [if_true]
      rw [show (∑ k, e7ComponentEnumerationProfile profile k *
          -(if k = (e7Pairs.get t).1 ∨ k = (e7Pairs.get t).2 then (3 : ℤ) else -1)) =
          -(∑ k, e7ComponentEnumerationProfile profile k *
          (if k = (e7Pairs.get t).1 ∨ k = (e7Pairs.get t).2 then (3 : ℤ) else -1)) by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring]
      rw [e7Weight_sum _ _ _ hne]

/-- Signed evaluation bin of a coordinate-pair difference. -/
def e7BinOfDiff (d : ℤ) : ℕ := (d / 8 + 21).toNat

/-- Packed contribution of one coordinate pair: the weight and its negative. -/
def e7PairCode (d : ℤ) : ℕ :=
  e7BinWeight (e7BinOfDiff d) + e7BinWeight (e7BinOfDiff (-d))

theorem e7BinWeight_foldl (bins : List ℕ) (c : ℕ) :
    bins.foldl (fun code i => code + e7BinWeight i) c =
      c + (bins.map e7BinWeight).sum := by
  induction bins generalizing c with
  | nil => simp
  | cons i bins ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]; omega

theorem e7SumMapAdd {α : Type _} (L : List α) (f g : α → ℕ) :
    (L.map f).sum + (L.map g).sum = (L.map (fun a => f a + g a)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ← ih]; omega

/-- The packed histogram code assembled from the 28 coordinate pairs. -/
def e7PairCodeSum (profile : Array ℤ) : ℕ :=
  (e7Pairs.map fun q =>
    e7PairCode
      (4 * (e7ComponentEnumerationProfile profile q.1 +
            e7ComponentEnumerationProfile profile q.2) -
        ∑ k, e7ComponentEnumerationProfile profile k)).sum

/-- The evaluation histogram of a profile is the decoded pair-code sum. -/
theorem e7ComponentHistogram_eq_ofCode (profile : Array ℤ) :
    e7ComponentHistogram profile = e7HistogramOfCode (e7PairCodeSum profile) := by
  set y := e7ComponentEnumerationProfile profile with hy
  set D : Fin 8 × Fin 8 → ℤ := fun q => 4 * (y q.1 + y q.2) - ∑ k, y k with hD
  set idx : E7WeightIndex → ℕ :=
    fun w => (e7ComponentEvaluation profile w + 21).toNat with hidx
  have key : ∀ sign : Bool,
      ((List.finRange e7Pairs.length).map fun t => idx (sign, t))
        = e7Pairs.map (fun q => e7BinOfDiff (if sign then -(D q) else D q)) := by
    intro sign
    conv_rhs => rw [← List.map_get_finRange e7Pairs]
    rw [List.map_map]
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_def, hidx, e7ComponentEvaluation_pair profile sign t,
      e7BinOfDiff, hD, hy]
  have hlist :
      ([false, true].flatMap fun sign =>
          (List.finRange e7Pairs.length).map fun pair => (sign, pair)).map idx
        = e7Pairs.map (fun q => e7BinOfDiff (D q)) ++
            e7Pairs.map (fun q => e7BinOfDiff (-(D q))) := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.map_append, List.map_map]
    rw [show ((List.finRange e7Pairs.length).map
          ((fun w => idx w) ∘ fun pair => (false, pair)))
        = ((List.finRange e7Pairs.length).map fun t => idx (false, t)) from rfl,
      show ((List.finRange e7Pairs.length).map
          ((fun w => idx w) ∘ fun pair => (true, pair)))
        = ((List.finRange e7Pairs.length).map fun t => idx (true, t)) from rfl,
      key false, key true]
    simp
  have hbound : ∀ k : ℕ,
      0 / e7CodeBase ^ k % e7CodeBase +
        (([false, true].flatMap fun sign =>
          (List.finRange e7Pairs.length).map fun pair => (sign, pair)).map idx).length
        < e7CodeBase := by
    intro k
    rw [hlist]
    simp only [List.length_append, List.length_map, Nat.zero_div, Nat.zero_mod,
      Nat.zero_add, e7CodeBase]
    decide
  have h1 : e7ComponentHistogram profile
      = (([false, true].flatMap fun sign =>
          (List.finRange e7Pairs.length).map fun pair => (sign, pair)).map idx).foldl
          (fun counts i => counts.set! i (counts.getD i 0 + 1))
          (Array.replicate 43 0) := by
    simp only [e7ComponentHistogram, List.foldl_map, hidx]
  rw [h1, ← e7HistogramOfCode_zero, e7HistogramOfCode_foldl _ 0 hbound]
  refine congrArg e7HistogramOfCode ?_
  rw [hlist, e7BinWeight_foldl, Nat.zero_add, List.map_append, List.map_map,
    List.map_map, List.sum_append, e7SumMapAdd]
  rfl

/-- The packed histogram code of eight explicit coordinates. -/
def e7FastHistogramCodeOf (a0 a1 a2 a3 a4 a5 a6 a7 : ℤ) : ℕ :=
  let s := a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7
  e7PairCode (4 * (a0 + a1) - s) +
    e7PairCode (4 * (a0 + a2) - s) +
    e7PairCode (4 * (a0 + a3) - s) +
    e7PairCode (4 * (a0 + a4) - s) +
    e7PairCode (4 * (a0 + a5) - s) +
    e7PairCode (4 * (a0 + a6) - s) +
    e7PairCode (4 * (a0 + a7) - s) +
    e7PairCode (4 * (a1 + a2) - s) +
    e7PairCode (4 * (a1 + a3) - s) +
    e7PairCode (4 * (a1 + a4) - s) +
    e7PairCode (4 * (a1 + a5) - s) +
    e7PairCode (4 * (a1 + a6) - s) +
    e7PairCode (4 * (a1 + a7) - s) +
    e7PairCode (4 * (a2 + a3) - s) +
    e7PairCode (4 * (a2 + a4) - s) +
    e7PairCode (4 * (a2 + a5) - s) +
    e7PairCode (4 * (a2 + a6) - s) +
    e7PairCode (4 * (a2 + a7) - s) +
    e7PairCode (4 * (a3 + a4) - s) +
    e7PairCode (4 * (a3 + a5) - s) +
    e7PairCode (4 * (a3 + a6) - s) +
    e7PairCode (4 * (a3 + a7) - s) +
    e7PairCode (4 * (a4 + a5) - s) +
    e7PairCode (4 * (a4 + a6) - s) +
    e7PairCode (4 * (a4 + a7) - s) +
    e7PairCode (4 * (a5 + a6) - s) +
    e7PairCode (4 * (a5 + a7) - s) +
    e7PairCode (4 * (a6 + a7) - s)

/-- The squared norm of eight explicit coordinates. -/
def e7FastNormOf (a0 a1 a2 a3 a4 a5 a6 a7 : ℤ) : ℕ :=
  (a0 * a0 + a1 * a1 + a2 * a2 + a3 * a3 + a4 * a4 + a5 * a5 + a6 * a6 +
    a7 * a7).toNat / 4

/-- The packed component code of eight explicit coordinates: the squared norm
below `e7NormBase`, the evaluation histogram in the quotient. -/
def e7FastComponentCodeOf (a0 a1 a2 a3 a4 a5 a6 a7 : ℤ) : ℕ :=
  e7FastNormOf a0 a1 a2 a3 a4 a5 a6 a7 +
    e7NormBase * e7FastHistogramCodeOf a0 a1 a2 a3 a4 a5 a6 a7

/-- The packed histogram code of a profile carrying eight coordinates. -/
def e7FastHistogramCode (profile : Array ℤ) : ℕ :=
  match profile.toList with
  | [a0, a1, a2, a3, a4, a5, a6, a7] =>
      e7FastHistogramCodeOf a0 a1 a2 a3 a4 a5 a6 a7
  | _ => 0

/-- The squared norm of a profile carrying eight coordinates. -/
def e7FastNorm (profile : Array ℤ) : ℕ :=
  match profile.toList with
  | [a0, a1, a2, a3, a4, a5, a6, a7] => e7FastNormOf a0 a1 a2 a3 a4 a5 a6 a7
  | _ => 0

/-- The packed component code of a profile carrying eight coordinates. -/
def e7FastComponentCode (profile : Array ℤ) : ℕ :=
  match profile.toList with
  | [a0, a1, a2, a3, a4, a5, a6, a7] =>
      e7FastComponentCodeOf a0 a1 a2 a3 a4 a5 a6 a7
  | _ => 0

theorem e7ComponentNorm_eq_of_coordinates (a0 a1 a2 a3 a4 a5 a6 a7 : ℤ) :
    e7ComponentNorm ([a0, a1, a2, a3, a4, a5, a6, a7] : List ℤ).toArray
      = e7FastNormOf a0 a1 a2 a3 a4 a5 a6 a7 := by
  simp only [e7ComponentNorm, e7FastNormOf]
  norm_num

theorem e7PairCodeSum_eq_of_coordinates (a0 a1 a2 a3 a4 a5 a6 a7 : ℤ) :
    e7PairCodeSum ([a0, a1, a2, a3, a4, a5, a6, a7] : List ℤ).toArray
      = e7FastHistogramCodeOf a0 a1 a2 a3 a4 a5 a6 a7 := by
  have h0 : e7ComponentEnumerationProfile
      ([a0, a1, a2, a3, a4, a5, a6, a7] : List ℤ).toArray 0 = a0 := rfl
  have h1 : e7ComponentEnumerationProfile
      ([a0, a1, a2, a3, a4, a5, a6, a7] : List ℤ).toArray 1 = a1 := rfl
  have h2 : e7ComponentEnumerationProfile
      ([a0, a1, a2, a3, a4, a5, a6, a7] : List ℤ).toArray 2 = a2 := rfl
  have h3 : e7ComponentEnumerationProfile
      ([a0, a1, a2, a3, a4, a5, a6, a7] : List ℤ).toArray 3 = a3 := rfl
  have h4 : e7ComponentEnumerationProfile
      ([a0, a1, a2, a3, a4, a5, a6, a7] : List ℤ).toArray 4 = a4 := rfl
  have h5 : e7ComponentEnumerationProfile
      ([a0, a1, a2, a3, a4, a5, a6, a7] : List ℤ).toArray 5 = a5 := rfl
  have h6 : e7ComponentEnumerationProfile
      ([a0, a1, a2, a3, a4, a5, a6, a7] : List ℤ).toArray 6 = a6 := rfl
  have h7 : e7ComponentEnumerationProfile
      ([a0, a1, a2, a3, a4, a5, a6, a7] : List ℤ).toArray 7 = a7 := rfl
  simp only [e7PairCodeSum, e7Pairs, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Fin.sum_univ_eight, h0, h1, h2, h3, h4, h5, h6, h7,
    e7FastHistogramCodeOf]
  ring

theorem e7List_length_eight {α : Type _} (l : List α) (h : l.length = 8) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 : α, l = [a0, a1, a2, a3, a4, a5, a6, a7] := by
  rcases l with _ | ⟨a0, l⟩; · simp at h
  rcases l with _ | ⟨a1, l⟩; · simp at h
  rcases l with _ | ⟨a2, l⟩; · simp at h
  rcases l with _ | ⟨a3, l⟩; · simp at h
  rcases l with _ | ⟨a4, l⟩; · simp at h
  rcases l with _ | ⟨a5, l⟩; · simp at h
  rcases l with _ | ⟨a6, l⟩; · simp at h
  rcases l with _ | ⟨a7, l⟩; · simp at h
  rcases l with _ | ⟨a8, l⟩
  · exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩
  · simp at h

theorem e7Profile_eq_toArray (profile : Array ℤ) (hsize : profile.size = 8) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 : ℤ,
      profile = ([a0, a1, a2, a3, a4, a5, a6, a7] : List ℤ).toArray := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, hl⟩ :=
    e7List_length_eight profile.toList (by simpa using hsize)
  exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, by rw [← hl]⟩

/-- The bridge used by the coverage sweep: an eight-coordinate profile whose
squared norm fits below `e7NormBase` has the component key of its packed code. -/
theorem e7ComponentKey_eq_ofCode (profile : Array ℤ)
    (hsize : profile.size = 8)
    (hnorm : e7FastNorm profile < e7NormBase) :
    e7ComponentKey profile = e7KeyOfCode (e7FastComponentCode profile) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ := e7Profile_eq_toArray profile hsize
  have hnorm' : e7FastNormOf a0 a1 a2 a3 a4 a5 a6 a7 < e7NormBase := by
    simpa only [e7FastNorm, List.toList_toArray] using hnorm
  simp only [e7ComponentKey, e7KeyOfCode, e7FastComponentCode,
    e7FastComponentCodeOf, e7ComponentNorm_eq_of_coordinates,
    e7ComponentHistogram_eq_ofCode, e7PairCodeSum_eq_of_coordinates,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hnorm',
    Nat.add_mul_div_left _ _ e7NormBase_pos, Nat.div_eq_of_lt hnorm',
    Nat.zero_add]

/-- The squared norm of an eight-coordinate profile agrees with the packed
computation. -/
theorem e7ComponentNorm_eq_fast (profile : Array ℤ) (hsize : profile.size = 8) :
    e7ComponentNorm profile = e7FastNorm profile := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ := e7Profile_eq_toArray profile hsize
  simp only [e7FastNorm, e7ComponentNorm_eq_of_coordinates]

end SRG266
