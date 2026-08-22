/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.E7ConcreteCodeData

/-!
# The expanded E7 pairs are listed

One kernel sweep over the 1,908 expanded canonical profile pairs: each is
encoded by one of the 956 listed encodings, and survives the decoding round
trip.  Together with `e7ConcreteListedCodes_eq` and the round trip of the
listed pairs this gives the forward inclusion of the expansion.
-/

namespace SRG266

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

/-- Every expanded canonical pair is encoded by a listed encoding, and
survives the decoding round trip. -/
theorem e7ConcreteExpansion_checked :
    e7ConcreteExpansion.all (fun pair =>
      e7ConcreteListedCodeTree.contains (e7PairEncode pair) &&
        decide (e7PairDecode (e7PairEncode pair) = pair)) = true := by
  decide +kernel

/-- The search tree stores 956 encodings. -/
theorem e7ConcreteListedCodeTree_length :
    e7ConcreteListedCodeTree.toList.length = 956 := by
  decide +kernel

/-- Every listed encoding is found by the search tree. -/
theorem e7ConcreteListedCodeList_mem_tree :
    e7ConcreteListedCodeList.all
      (fun code => e7ConcreteListedCodeTree.contains code) = true := by
  decide +kernel

end SRG266
