import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0299`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0299Mask : ℕ := 5387214965607000

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0299Witness : Array ℤ :=
  #[211, 12, 3, 321, 121, -56, -31, 93, 125, 107, -227, -204, -69, -106, 73,
  -67, -61, 146, 47, 58, -2, -36, -72, -57, 91, -42, 177, 274, 36, 138, 131,
  185, -97, -261, -30, 107, 106, 26, -173, 121, -178, 168, -98, -141, 52,
  30, 281, 16, -28, -80, 10, 106, 234, 9, 76, -219, -257, -108, 129, 159,
  93, 84, 246, -96, 0, 114, 209, -15, -203, -217, 239, 59, 58, 68, 34, 20,
  58, -52, 25, -93, -1, 37, -31, 8, 0, -219, -114, 123, 100, 59, 91, 87,
  -20, -79, 146, -151, -102, 355, -94, 115, -178, 34, 258, 60, 231, -115, 9,
  -86, 102, 5, 51, -63, 129, 458, -89, -61, -15, 224, 165, -168, -42, -153,
  363, 61, -63, -56, -182, 33, -31, 118, -121, 36, 30, -149, 111, 91, 94,
  -205, -44, 48, -142, -67, -46, 27, -68, -18, 43, -183, 153, -76, 23, -75,
  170, -7, -164, 206, 72, -132, 218, -80, -126, 60, 53, 202, -6, -73, -272,
  -270]

theorem fractionalNearFrameSubtreeG2R0299_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0299Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0299Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0299Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0299_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0299LowerBoundTable : List ℤ :=
  [36, 2, -57, 2, 157, 165, 345, 2, 284, 10, 449, 8, -84, 10, 365, 255, 483,
  301, 40, 430, 730, 528, 508, 724, 252]

def fractionalNearFrameSubtreeG2R0299LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0299Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0299LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
