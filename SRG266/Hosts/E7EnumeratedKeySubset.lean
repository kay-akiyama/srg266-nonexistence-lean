/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.E7HistogramEnumeration

/-!
# The enumerated component keys really come from enumerated profiles

`e7EnumeratedComponentKeys` sorts and deduplicates the component keys of the
120,036 enumerated profiles.  `List.mem_mergeSort` and
`e7DedupAdjacent_subset` invert both steps without evaluating the sort, which
is what lets the coverage sweep transfer to keys.
-/

namespace SRG266

theorem e7EnumeratedComponentKeys_subset
    (key : E7ComponentKey) (hkey : key ∈ e7EnumeratedComponentKeys) :
    ∃ profile ∈ e7EnumeratedComponentProfiles, e7ComponentKey profile = key := by
  have hsorted := e7DedupAdjacent_subset _ _ hkey
  rw [List.mem_mergeSort, List.mem_map] at hsorted
  exact hsorted

end SRG266
