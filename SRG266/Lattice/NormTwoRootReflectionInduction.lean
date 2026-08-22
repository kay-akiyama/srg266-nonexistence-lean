/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.NormTwoRootSeparator

/-!
# Reflection induction for norm-two roots

The simple roots selected by a separating integral functional generate every
norm-two root under simple reflections and negation.  This is the exact
completeness principle needed by the finite ADE eutaxy certificates.

The proof is elementary.  A positive root is in the additive closure of the
simple roots.  Pairing that expression with the root shows that some simple
root has positive inner product.  Subtracting it gives a positive root of
strictly smaller separator value; reflection recovers the original root.

Packaging this directly avoids any dependency on a general root-system or
Weyl-group API, and in particular avoids the two competing `ℤ` scalar-action
instances that arise when a bundled `ModuleCat` is coerced to Mathlib's
`RootPairing`.
-/

namespace SRG266
namespace Lattice

/-- Reflection of one norm-two root in another, using canonical additive
integer scalar multiplication. -/
noncomputable def reflectNormTwoRoot {n : ℕ} (L : PDUnimodularLattice n)
    (a b : NormTwoRoot L) : NormTwoRoot L :=
  ⟨b.1 - (L.pairing b.1 a.1) • a.1, by
    have hsym : L.pairing a.1 b.1 = L.pairing b.1 a.1 :=
      L.symmetric.eq _ _
    simp only [map_sub, LinearMap.sub_apply, map_zsmul,
      LinearMap.smul_apply, zsmul_eq_mul, Int.cast_id]
    rw [a.2, b.2, hsym]
    ring⟩

@[simp]
theorem reflectNormTwoRoot_val {n : ℕ} (L : PDUnimodularLattice n)
    (a b : NormTwoRoot L) :
    (reflectNormTwoRoot L a b).1 =
      b.1 - (L.pairing b.1 a.1) • a.1 :=
  rfl

/-- A positive root is in the additive closure of the selected simple roots. -/
theorem positiveRoot_mem_simpleRootClosure {n : ℕ}
    {L : PDUnimodularLattice n} (f : L.carrier →+ ℤ)
    {r : NormTwoRoot L} (hr : 0 < f r.1) :
    r.1 ∈ AddSubmonoid.closure (normTwoRootVal '' simpleRootSet f) := by
  rw [simpleRootSet,
    AddSubmonoid.closure_image_isAddIndecomposable_baseOf]
  exact AddSubmonoid.subset_closure ⟨r, hr, rfl⟩

/-- A positive root has positive inner product with at least one simple root. -/
theorem exists_simpleRoot_pairing_pos {n : ℕ}
    {L : PDUnimodularLattice n} (f : L.carrier →+ ℤ)
    {r : NormTwoRoot L} (hr : 0 < f r.1) :
    ∃ s : NormTwoRoot L, s ∈ simpleRootSet f ∧
      0 < L.pairing r.1 s.1 := by
  have hrmem := positiveRoot_mem_simpleRootClosure f hr
  by_contra hnot
  push Not at hnot
  have hnonpos : L.pairing r.1 r.1 ≤ 0 := by
    have hclosure : ∀ x,
        x ∈ AddSubmonoid.closure (normTwoRootVal '' simpleRootSet f) →
          L.pairing x r.1 ≤ 0 := by
      intro x hx
      induction hx using AddSubmonoid.closure_induction with
      | mem x hx =>
          obtain ⟨s, hs, rfl⟩ := hx
          rw [L.symmetric.eq]
          exact hnot s hs
      | zero => simp
      | add x y _ _ hx hy =>
          simpa only [map_add, LinearMap.add_apply] using add_nonpos hx hy
    exact hclosure r.1 hrmem
  rw [r.2] at hnonpos
  omega

/-- Subtracting a positively paired simple root from a positive nonsimple root
leaves a positive root. -/
theorem sub_simpleRoot_positive {n : ℕ}
    {L : PDUnimodularLattice n} (f : L.carrier →+ ℤ)
    (hf : ∀ u : NormTwoRoot L, f u.1 ≠ 0)
    {r s t : NormTwoRoot L} (hr : 0 < f r.1)
    (hs : s ∈ simpleRootSet f)
    (ht : r.1 - s.1 = t.1) :
    0 < f t.1 := by
  have hspos : 0 < f s.1 :=
    (IsAddIndecomposable.baseOf_subset_pos normTwoRootVal f hs)
  have hft : f t.1 = f r.1 - f s.1 := by
    rw [← ht]
    exact map_sub f r.1 s.1
  rcases lt_or_gt_of_ne (hf t) with hneg | hpos
  · exfalso
    have hnegr : 0 < f (-t).1 := by simpa using neg_pos.mpr hneg
    have hsind := hs
    change IsAddIndecomposable normTwoRootVal
      {u | 0 < f (normTwoRootVal u)} s at hsind
    have hsum : s.1 = r.1 + (-t).1 := by
      rw [NormTwoRoot.coe_neg, ← ht]
      abel
    rcases hsind.2 r hr (-t) hnegr hsum with hzero | hzero
    · exact normTwoRootVal_ne_zero r hzero
    · exact normTwoRootVal_ne_zero (-t) hzero
  · exact hpos

/-- If a simple root pairs positively with a distinct root, the pairing is
exactly one. -/
theorem pairing_eq_one_of_simple_step {n : ℕ}
    {L : PDUnimodularLattice n} {r s : NormTwoRoot L}
    (hrs : r ≠ s) (hpair : 0 < L.pairing r.1 s.1) :
    L.pairing r.1 s.1 = 1 := by
  have hne : r.1 - s.1 ≠ 0 := by
    intro h
    exact hrs (Subtype.ext (sub_eq_zero.mp h))
  have hpos := L.positiveDefinite (r.1 - s.1) hne
  have hsym : L.pairing s.1 r.1 = L.pairing r.1 s.1 :=
    L.symmetric.eq _ _
  simp only [map_sub, LinearMap.sub_apply] at hpos
  rw [r.2, s.2, hsym] at hpos
  omega

/-- The subtraction step is recovered by reflecting the smaller root in the
chosen simple root. -/
theorem reflect_sub_simpleRoot {n : ℕ}
    {L : PDUnimodularLattice n} {r s t : NormTwoRoot L}
    (hpair : L.pairing r.1 s.1 = 1) (ht : r.1 - s.1 = t.1) :
    reflectNormTwoRoot L s t = r := by
  apply Subtype.ext
  simp only [reflectNormTwoRoot_val, ← ht, map_sub,
    LinearMap.sub_apply, hpair, s.2]
  norm_num

/-- **Reflection induction.**  A property of norm-two roots holds everywhere
if it is preserved by negation, holds on every selected simple root, and is
preserved by reflection in a selected simple root. -/
theorem normTwoRoot_reflection_induction {n : ℕ}
    {L : PDUnimodularLattice n} (f : L.carrier →+ ℤ)
    (hf : ∀ r : NormTwoRoot L, f r.1 ≠ 0)
    (P : NormTwoRoot L → Prop)
    (hneg : ∀ r, P r → P (-r))
    (hsimple : ∀ r, r ∈ simpleRootSet f → P r)
    (hreflect : ∀ r s, s ∈ simpleRootSet f →
      P r → P (reflectNormTwoRoot L s r)) :
    ∀ r, P r := by
  let rec positive (r : NormTwoRoot L) (hr : 0 < f r.1) : P r := by
    by_cases hrsimple : r ∈ simpleRootSet f
    · exact hsimple r hrsimple
    · obtain ⟨s, hs, hpair⟩ := exists_simpleRoot_pairing_pos f hr
      have hrs : r ≠ s := fun h => hrsimple (h ▸ hs)
      obtain ⟨t, ht⟩ := sub_mem_normTwoRoots_of_pairing_pos hrs hpair
      have htpos : 0 < f t.1 :=
        sub_simpleRoot_positive f hf hr hs ht
      have hspos : 0 < f s.1 :=
        IsAddIndecomposable.baseOf_subset_pos normTwoRootVal f hs
      have hdecrease : (f (normTwoRootVal t)).toNat <
          (f (normTwoRootVal r)).toNat := by
        have hr' : 0 < f (normTwoRootVal r) := by
          simpa only [normTwoRootVal] using hr
        have hspos' : 0 < f (normTwoRootVal s) := by
          simpa only [normTwoRootVal] using hspos
        have hft : f (normTwoRootVal t) =
            f (normTwoRootVal r) - f (normTwoRootVal s) := by
          have hmap := congrArg f ht
          simpa only [map_sub] using hmap.symm
        omega
      have hrec : P t := positive t htpos
      have hpone := pairing_eq_one_of_simple_step hrs hpair
      rw [← reflect_sub_simpleRoot hpone ht]
      exact hreflect t s hs hrec
    termination_by (f (normTwoRootVal r)).toNat
  intro r
  rcases lt_or_gt_of_ne (hf r) with hnegf | hposf
  · have hp : P (-r) := positive (-r) (by simpa using neg_pos.mpr hnegf)
    simpa using hneg (-r) hp
  · exact positive r hposf

end Lattice
end SRG266
