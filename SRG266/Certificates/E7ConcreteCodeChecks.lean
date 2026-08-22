/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.E7ConcreteCodeData

/-!
# Packed encodings of the listed canonical E7 profile pairs

Comparing the 1,908 expanded canonical profile pairs with the 956 listed ones
through `List.toFinset` would need a quadratic deduplication over *structural*
array pairs, far beyond one kernel evaluation.  Comparing packed encodings
instead keeps every comparison a single `Nat` test.

No property of the encoding is assumed anywhere.  The forward inclusion is
read off a lookup among the encodings together with the decoding round trip of
both elements involved, so a bad encoding could only make these evaluations
fail.
-/

namespace SRG266

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

/-- The listed encodings are the encodings of the listed canonical pairs. -/
theorem e7ConcreteListedCodes_eq :
    e7ConcreteListedCodes = e7ConcreteListedCodeList := by
  decide +kernel

/-- The listed canonical pairs have pairwise distinct encodings. -/
theorem e7ConcreteListedCodeList_distinct :
    e7NatDistinct e7ConcreteListedCodeList = true := by
  decide +kernel

/-- Every listed canonical pair survives the decoding round trip. -/
theorem e7ConcreteListed_roundTrip :
    e7ListedCanonicalArrayPairs.all
      (fun pair => decide (e7PairDecode (e7PairEncode pair) = pair)) = true := by
  decide +kernel

/-- There are 956 listed canonical pairs. -/
theorem e7ListedCanonicalArrayPairs_length :
    e7ListedCanonicalArrayPairs.length = 956 := by
  decide +kernel

end SRG266
