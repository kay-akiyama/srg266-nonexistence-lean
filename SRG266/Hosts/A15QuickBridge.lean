/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.A15ProjectorBridge

/-!
# Shape certificates for A15 projector witnesses

The generated negative witnesses use only coordinate-class indicators and
standard coordinate differences. Class indicators are bilinearly compatible
with the reported orbit moments as a formal consequence of the bridge
identities, so checking these shapes avoids another traversal of the shell.
-/

open scoped BigOperators

namespace SRG266

def a15ClassIndicator
    (profile : A15ProjectorProfile) (c : ℕ) : Array ℤ :=
  Array.ofFn fun i : Fin 16 => if profile.inClass c i then 1 else 0

def A15ProjectorProfile.isClassIndicator
    (profile : A15ProjectorProfile) (x : Array ℤ) : Prop :=
  ∃ c : Fin profile.classSizes.size,
    x = a15ClassIndicator profile c.1

theorem a15_getD_ofFn (f : Fin 16 → ℤ) (i : Fin 16) :
    (Array.ofFn f).getD i.1 0 = f i := by
  simp [Array.getD, i.isLt]

theorem A15ProjectorProfile.shellDot_classIndicator
    (profile : A15ProjectorProfile) (c : ℕ)
    (s : A15EligibleIndex profile.centroidVector) :
    profile.shellDot (a15ClassIndicator profile c) s =
      ∑ i ∈ profile.classFinset c,
        a15ProjectorShellCoordinate profile.d (a15FourSubsetAt s.1) i := by
  unfold A15ProjectorProfile.shellDot a15ClassIndicator
    A15ProjectorProfile.classFinset
  simp_rw [a15_getD_ofFn]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hc : profile.inClass c i <;> simp [hc]

theorem A15ProjectorProfile.orbitSecondBilinear_classIndicator
    (profile : A15ProjectorProfile) (k c e : ℕ) :
    profile.orbitSecondBilinear k
        (a15ClassIndicator profile c)
        (a15ClassIndicator profile e) =
      profile.orbitBlockSecondMoment k c e := by
  unfold A15ProjectorProfile.orbitSecondBilinear
    a15ClassIndicator A15ProjectorProfile.orbitBlockSecondMoment
    A15ProjectorProfile.classFinset
  simp_rw [a15_getD_ofFn]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hci : profile.inClass c i
  · simp only [hci, if_true, one_mul]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hej : profile.inClass e j <;> simp [hej]
  · simp [hci]

theorem A15ProjectorProfile.classIndicators_bilinearCompatible
    (profile : A15ProjectorProfile) (hbridge : profile.bridgeValid)
    (c e : Fin profile.classSizes.size) :
    profile.bilinearCompatible
      (a15ClassIndicator profile c.1)
      (a15ClassIndicator profile e.1) := by
  unfold A15ProjectorProfile.bilinearCompatible
  constructor
  · simp [a15ClassIndicator]
  constructor
  · simp [a15ClassIndicator]
  intro k s hmatch
  rw [A15ProjectorProfile.shellDot_classIndicator,
    A15ProjectorProfile.shellDot_classIndicator,
    A15ProjectorProfile.orbitSecondBilinear_classIndicator]
  rcases hbridge with ⟨_, _, _, _, _, _, _, _, horbits⟩
  have hk := horbits k
  rw [hk.2.2.2.1 c e]
  rw [hk.2.2.2.2.1 s hmatch c,
    hk.2.2.2.2.1 s hmatch e]

def A15ProjectorWitness.quickBridgeCompatible
    (profile : A15ProjectorProfile) : A15ProjectorWitness → Prop
  | .negativeVector x _ =>
      A15ProjectorProfile.isClassIndicator profile x ∨ profile.isStandardDifference x
  | .negativeMinor x y _ =>
      A15ProjectorProfile.isClassIndicator profile x ∧ A15ProjectorProfile.isClassIndicator profile y

instance (profile : A15ProjectorProfile) (w : A15ProjectorWitness) :
    Decidable (A15ProjectorWitness.quickBridgeCompatible profile w) := by
  cases w <;> unfold A15ProjectorWitness.quickBridgeCompatible A15ProjectorProfile.isClassIndicator <;>
    infer_instance

def A15ProjectorWitness.quickCheckBridge
    (profile : A15ProjectorProfile) (w : A15ProjectorWitness) : Bool :=
  decide (A15ProjectorWitness.quickBridgeCompatible profile w)

theorem A15ProjectorWitness.quickBridgeCompatible_sound
    (profile : A15ProjectorProfile) (hbridge : profile.bridgeValid)
    (w : A15ProjectorWitness)
    (hquick : A15ProjectorWitness.quickCheckBridge profile w = true) :
    w.bridgeCompatible profile := by
  have h := of_decide_eq_true hquick
  cases w with
  | negativeVector x value =>
      rcases h with ⟨c, rfl⟩ | hstandard
      · exact Or.inl
          (A15ProjectorProfile.classIndicators_bilinearCompatible profile hbridge c c)
      · exact Or.inr hstandard
  | negativeMinor x y determinant =>
      rcases h with ⟨⟨c, rfl⟩, ⟨e, rfl⟩⟩
      exact
        ⟨A15ProjectorProfile.classIndicators_bilinearCompatible profile hbridge c c,
          A15ProjectorProfile.classIndicators_bilinearCompatible profile hbridge c e,
          A15ProjectorProfile.classIndicators_bilinearCompatible profile hbridge e c,
          A15ProjectorProfile.classIndicators_bilinearCompatible profile hbridge e e⟩

end SRG266
