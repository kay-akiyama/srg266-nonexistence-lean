/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.E7ConcreteEnumerationAssembly
import SRG266.Hosts.E7CentroidAssembly

/-!
# Elimination of every enumerated E7 centroid realization

Concrete enumeration identifies an admissible array pair with one of the
956 checked centroid profiles, modulo exchange of the two E7 factors.  This
module supplies the exact factor-exchange transport and invokes the existing
902 Farkas and 54 residual eliminations.
-/

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Exchange the two E7 factors of a direct centroid realization. -/
def E7CentroidShellGramRealization.swap
    {x : V} {y₁ y₂ : Fin 8 → ℤ}
    (realization : E7CentroidShellGramRealization G x y₁ y₂) :
    E7CentroidShellGramRealization G x y₂ y₁ where
  shell B :=
    ⟨((realization.shell B).1.2, (realization.shell B).1.1), by
      have heligible := (realization.shell B).2
      unfold e7Eligible at heligible ⊢
      change
        integerDot y₂ (e7Weight4 (realization.shell B).1.2) +
          integerDot y₁ (e7Weight4 (realization.shell B).1.1) = 120
      change
        integerDot y₁ (e7Weight4 (realization.shell B).1.1) +
          integerDot y₂ (e7Weight4 (realization.shell B).1.2) = 120
        at heligible
      omega⟩
  gram B C := by
    simpa only [e7ShellInner, add_comm] using realization.gram B C
  leftCentroid := realization.rightCentroid
  rightCentroid := realization.leftCentroid

theorem e7EnumerationProfile_eq_of_array_eq_ofFn
    (profile : Array ℤ) (y : Fin 8 → ℤ)
    (hprofile : profile = Array.ofFn y) :
    e7ComponentEnumerationProfile profile = y := by
  subst profile
  funext i
  simp [e7ComponentEnumerationProfile]

/-- Every direct realization whose enumerated component profiles pass the trace
filter is one of the already excluded 956 concrete cases. -/
theorem no_e7EnumeratedTraceRealization
    [E7ScalarDPAuditInput] [E7ConcreteEnumerationAuditInput]
    (hG : IsHypothetical G) (x : V)
    (left right : Array ℤ)
    (hleft : left ∈ e7EnumeratedComponentProfiles)
    (hright : right ∈ e7EnumeratedComponentProfiles)
    (htrace :
      (e7ComponentKey left, e7ComponentKey right) ∈
        e7TraceFeasibleHistogramPairs) :
    IsEmpty
      (E7CentroidShellGramRealization G x
        (e7ComponentEnumerationProfile left)
        (e7ComponentEnumerationProfile right)) := by
  obtain ⟨y₁, y₂, hlisted, hcoordinates⟩ :=
    enumerated_trace_pair_has_listed_profile
      left right hleft hright htrace
  refine ⟨fun realization => ?_⟩
  rcases hcoordinates with hdirect | hswapped
  · have hleftProfile :
        e7ComponentEnumerationProfile left = y₁ :=
      e7EnumerationProfile_eq_of_array_eq_ofFn left y₁ hdirect.1
    have hrightProfile :
        e7ComponentEnumerationProfile right = y₂ :=
      e7EnumerationProfile_eq_of_array_eq_ofFn right y₂ hdirect.2
    rw [hleftProfile, hrightProfile] at realization
    exact
      (e7ListedCentroidProfile_no_realization
        G hG x y₁ y₂ hlisted).false realization
  · have hleftProfile :
        e7ComponentEnumerationProfile left = y₂ :=
      e7EnumerationProfile_eq_of_array_eq_ofFn left y₂ hswapped.1
    have hrightProfile :
        e7ComponentEnumerationProfile right = y₁ :=
      e7EnumerationProfile_eq_of_array_eq_ofFn right y₁ hswapped.2
    rw [hleftProfile, hrightProfile] at realization
    exact
      (e7ListedCentroidProfile_no_realization
        G hG x y₁ y₂ hlisted).false
        (realization.swap G)

end SRG266
