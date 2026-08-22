/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.E7ConcreteEnumerationData

/-!
# Assembly API for concrete E7 profile completeness

The explicit audit input is exposed here as an equality of finite sets and as
a membership theorem sending any expanded canonical array pair to one of the
956 checked centroid profiles.
-/

namespace SRG266

theorem e7ExpandedConcreteProfilePairs_toFinset
    [E7ConcreteEnumerationAuditInput] :
    e7ExpandedConcreteProfilePairs.toFinset =
      e7ListedCanonicalArrayPairs.toFinset := by
  have h :=
    congrArg E7ConcreteEnumerationAudit.sameProfiles
      e7ConcreteEnumerationAudit_checked
  have hcheck :
      decide (
        e7ExpandedConcreteProfilePairs.toFinset =
          e7ListedCanonicalArrayPairs.toFinset) = true := by
    simpa [e7ConcreteEnumerationAudit] using h
  exact of_decide_eq_true hcheck

theorem e7ExpandedConcreteProfilePairs_card
    [E7ConcreteEnumerationAuditInput] :
    e7ExpandedConcreteProfilePairs.toFinset.card = 956 := by
  have h :=
    congrArg E7ConcreteEnumerationAudit.expandedCount
      e7ConcreteEnumerationAudit_checked
  simpa [e7ConcreteEnumerationAudit] using h

theorem canonical_component_pair_eq_cases
    (a b c d : Array ℤ)
    (h :
      e7CanonicalComponentArrayPair a b =
        e7CanonicalComponentArrayPair c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  by_cases hab : (compare a b).isLE
  · by_cases hcd : (compare c d).isLE
    · left
      simpa [e7CanonicalComponentArrayPair, hab, hcd,
        Prod.ext_iff] using h
    · right
      simpa [e7CanonicalComponentArrayPair, hab, hcd,
        Prod.ext_iff] using h
  · by_cases hcd : (compare c d).isLE
    · right
      have h' : (b, a) = (c, d) := by
        simpa [e7CanonicalComponentArrayPair, hab, hcd] using h
      exact ⟨congrArg Prod.snd h', congrArg Prod.fst h'⟩
    · left
      have h' : (b, a) = (d, c) := by
        simpa [e7CanonicalComponentArrayPair, hab, hcd] using h
      exact ⟨congrArg Prod.snd h', congrArg Prod.fst h'⟩

theorem expanded_pair_has_listed_profile
    [E7ConcreteEnumerationAuditInput]
    (left right : Array ℤ)
    (hexpanded :
      e7CanonicalComponentArrayPair left right ∈
        e7ExpandedConcreteProfilePairs) :
    ∃ y₁ y₂ : Fin 8 → ℤ,
      (y₁, y₂) ∈ e7ListedCentroidProfiles ∧
      ((left = Array.ofFn y₁ ∧ right = Array.ofFn y₂) ∨
        (left = Array.ofFn y₂ ∧ right = Array.ofFn y₁)) := by
  have hfin :
      e7CanonicalComponentArrayPair left right ∈
        e7ExpandedConcreteProfilePairs.toFinset := by
    simpa using hexpanded
  rw [e7ExpandedConcreteProfilePairs_toFinset] at hfin
  have hlisted :
      e7CanonicalComponentArrayPair left right ∈
        e7ListedCanonicalArrayPairs := by
    simpa using hfin
  obtain ⟨pair, hpair, heq⟩ := List.mem_map.mp hlisted
  refine ⟨pair.1, pair.2, hpair, ?_⟩
  exact
    canonical_component_pair_eq_cases left right
      (Array.ofFn pair.1) (Array.ofFn pair.2) heq.symm

theorem enumerated_trace_pair_has_listed_profile
    [E7ScalarDPAuditInput] [E7ConcreteEnumerationAuditInput]
    (left right : Array ℤ)
    (hleft : left ∈ e7EnumeratedComponentProfiles)
    (hright : right ∈ e7EnumeratedComponentProfiles)
    (htrace :
      (e7ComponentKey left, e7ComponentKey right) ∈
        e7TraceFeasibleHistogramPairs) :
    ∃ y₁ y₂ : Fin 8 → ℤ,
      (y₁, y₂) ∈ e7ListedCentroidProfiles ∧
      ((left = Array.ofFn y₁ ∧ right = Array.ofFn y₂) ∨
        (left = Array.ofFn y₂ ∧ right = Array.ofFn y₁)) := by
  apply expanded_pair_has_listed_profile
  apply canonical_pair_mem_expansion left right hleft hright
  exact trace_pair_mem_listed_keys _ htrace

end SRG266
