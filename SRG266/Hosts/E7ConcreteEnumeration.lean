/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.E7ScalarDPAssembly

/-!
# Concrete expansion of the surviving E7 histogram keys

The scalar-DP audit leaves 43 oriented histogram-key pairs.  This module
expands each key to all native component profiles, identifies exchange of
the two E7 factors, and compares the result with the 956 concrete centroid
profiles whose Farkas or residual certificates are already checked.

The keyed profile list is shared by all filters, so every one of the 120,036
component histograms is computed only once during native evaluation.
-/

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev E7ComponentArrayPair := Array ℤ × Array ℤ

def e7CanonicalComponentArrayPair
    (left right : Array ℤ) : E7ComponentArrayPair :=
  if (compare left right).isLE then (left, right) else (right, left)

def e7KeyedComponentProfiles :
    List (E7ComponentKey × Array ℤ) :=
  e7EnumeratedComponentProfiles.map fun profile =>
    (e7ComponentKey profile, profile)

/-- Expansion of all 43 oriented trace keys, canonicalized under factor
exchange.  Duplicates are intentionally left for `toFinset` to remove. -/
def e7ExpandedConcreteProfilePairs : List E7ComponentArrayPair :=
  let keyed := e7KeyedComponentProfiles
  e7ListedCentroidHistogramPairsUpToSwap.flatMap fun keys =>
    (keyed.filter fun item => item.1 = keys.1).flatMap fun left =>
      (keyed.filter fun item => item.1 = keys.2).map fun right =>
        e7CanonicalComponentArrayPair left.2 right.2

def e7ListedCanonicalArrayPairs : List E7ComponentArrayPair :=
  e7ListedCentroidProfiles.map fun pair =>
    e7CanonicalComponentArrayPair
      (Array.ofFn pair.1) (Array.ofFn pair.2)

theorem keyed_profile_mem
    (profile : Array ℤ)
    (hprofile : profile ∈ e7EnumeratedComponentProfiles) :
    (e7ComponentKey profile, profile) ∈ e7KeyedComponentProfiles := by
  simp [e7KeyedComponentProfiles, hprofile]

theorem canonical_pair_mem_expansion
    (left right : Array ℤ)
    (hleft : left ∈ e7EnumeratedComponentProfiles)
    (hright : right ∈ e7EnumeratedComponentProfiles)
    (hkeys :
      (e7ComponentKey left, e7ComponentKey right) ∈
        e7ListedCentroidHistogramPairsUpToSwap) :
    e7CanonicalComponentArrayPair left right ∈
      e7ExpandedConcreteProfilePairs := by
  let leftItem := (e7ComponentKey left, left)
  let rightItem := (e7ComponentKey right, right)
  have hleftItem : leftItem ∈ e7KeyedComponentProfiles := by
    exact keyed_profile_mem left hleft
  have hrightItem : rightItem ∈ e7KeyedComponentProfiles := by
    exact keyed_profile_mem right hright
  unfold e7ExpandedConcreteProfilePairs
  apply List.mem_flatMap.mpr
  refine ⟨(e7ComponentKey left, e7ComponentKey right), hkeys, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨leftItem, ?_, ?_⟩
  · exact List.mem_filter.mpr ⟨hleftItem, by simp [leftItem]⟩
  apply List.mem_map.mpr
  refine ⟨rightItem, ?_, ?_⟩
  · exact List.mem_filter.mpr ⟨hrightItem, by simp [rightItem]⟩
  · rfl

end SRG266
