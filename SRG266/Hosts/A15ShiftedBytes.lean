/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.A15ExactEnumeration
import SRG266.Hosts.A15ByteArrayLemmas
import Mathlib.Data.List.GetD

/-!
# Shifted coordinate bytes and the reference count as a list count

Two elementary bridges are needed before the fast and reference A15
eligible-shell counters can be compared.

* `a15ShiftedReducedCoordinateBytes` is a plain `List.map` in disguise:
  position `i` holds the byte `a_i + 17`, which is in `[0,34]` whenever the
  reduced coordinate `a_i` lies in `[-17,17]`.
* `a15ExactEligibleCardReduced` is an `Array.foldl` accumulating a Boolean
  indicator; it therefore equals a `List.countP` over the table.  This
  rewriting must never be replaced by evaluation: unfolding the fold over the
  1,820-entry array literal is far beyond the kernel's budget.

Finally the eligibility disjunction splits into two disjoint counts, since the
two target sums `15 - r` and `-15 - r` differ by thirty.
-/

namespace SRG266

/-- The shifted-byte encoder is a plain `map` on the underlying array. -/
theorem a15ShiftedReducedCoordinateBytes_toList (coordinates : List ℤ) :
    (a15ShiftedReducedCoordinateBytes coordinates).data.toList =
      coordinates.map (fun z => (z + 17).toNat.toUInt8) := by
  unfold a15ShiftedReducedCoordinateBytes
  suffices h : ∀ (l : List ℤ) (b : ByteArray),
      (l.foldl (fun bytes z => bytes.push (z + 17).toNat.toUInt8) b).data.toList =
        b.data.toList ++ l.map (fun z => (z + 17).toNat.toUInt8) by
    have hz := h coordinates (ByteArray.emptyWithCapacity 16)
    rw [show (ByteArray.emptyWithCapacity 16).data.toList = [] from rfl,
      List.nil_append] at hz
    exact hz
  intro l
  induction l with
  | nil => intro b; simp
  | cons z zs ih =>
      intro b
      simp only [List.foldl_cons, List.map_cons, ih]
      show (b.push _).data.toList ++ _ = _
      simp

theorem a15ShiftedReducedCoordinateBytes_size (coordinates : List ℤ) :
    (a15ShiftedReducedCoordinateBytes coordinates).size = coordinates.length := by
  show (a15ShiftedReducedCoordinateBytes coordinates).data.size = coordinates.length
  rw [← Array.length_toList, a15ShiftedReducedCoordinateBytes_toList]
  simp

/-- Reading a shifted coordinate byte recovers `a_i + 17` as a natural
number, provided the reduced coordinates are bounded by seventeen. -/
theorem a15ShiftedReducedCoordinateBytes_get (coordinates : List ℤ) (i : ℕ)
    (hi : i < coordinates.length)
    (hb : ∀ z ∈ coordinates, -17 ≤ z ∧ z ≤ 17) :
    ((a15ShiftedReducedCoordinateBytes coordinates).get! i).toNat =
      (coordinates.getD i 0 + 17).toNat := by
  have hdata : (a15ShiftedReducedCoordinateBytes coordinates).data =
      (coordinates.map (fun z => (z + 17).toNat.toUInt8)).toArray := by
    apply Array.ext'
    rw [a15ShiftedReducedCoordinateBytes_toList]
  show ((a15ShiftedReducedCoordinateBytes coordinates).data[i]!).toNat = _
  rw [hdata, getElem!_pos _ _ (by simpa using hi)]
  rw [List.getElem_toArray, List.getElem_map]
  rw [List.getD_eq_getElem coordinates 0 hi]
  have hz := hb coordinates[i] (List.getElem_mem hi)
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']
  rw [Nat.mod_eq_of_lt]
  omega

/-- The reference eligible-shell count is a `List.countP` over the checked
four-subset table.  This is a pure rewriting step: the fold is never run. -/
theorem a15ExactEligibleCardReduced_eq_countP (residue : ℤ) (coordinates : List ℤ) :
    a15ExactEligibleCardReduced residue coordinates =
      a15FourSubsetData.toList.countP
        (fun s => a15ReducedDataEligible residue coordinates s) := by
  unfold a15ExactEligibleCardReduced
  rw [← Array.foldl_toList]
  suffices h : ∀ (l : List A15FourSubset) (n : ℕ),
      l.foldl (fun count s =>
          count + if a15ReducedDataEligible residue coordinates s then 1 else 0) n =
        n + l.countP (fun s => a15ReducedDataEligible residue coordinates s) by
    simpa using h a15FourSubsetData.toList 0
  intro l
  induction l with
  | nil => intro n; simp
  | cons s ss ih =>
      intro n
      simp only [List.foldl_cons, List.countP_cons, ih]
      by_cases h : a15ReducedDataEligible residue coordinates s = true
      · simp only [h, if_true]
        omega
      · simp [h]

/-- Counting a disjoint disjunction splits into a sum of counts. -/
theorem a15_countP_or_disjoint {α : Type*} (l : List α) (p q : α → Bool)
    (hdisj : ∀ a ∈ l, ¬ (p a = true ∧ q a = true)) :
    l.countP (fun a => p a || q a) = l.countP p + l.countP q := by
  induction l with
  | nil => simp
  | cons a as ih =>
      have hd : ∀ b ∈ as, ¬ (p b = true ∧ q b = true) := fun b hb =>
        hdisj b (List.mem_cons_of_mem a hb)
      have ha := hdisj a (List.mem_cons_self ..)
      simp only [List.countP_cons, ih hd]
      by_cases hp : p a = true <;> by_cases hq : q a = true <;>
        simp_all <;> try omega

end SRG266
