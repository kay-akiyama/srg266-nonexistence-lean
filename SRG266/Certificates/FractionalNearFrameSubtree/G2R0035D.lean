import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0035`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0035Mask : ℕ := 883693583045123

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0035Witness : Array ℤ :=
  #[73, 25, 149, 86, 0, 180, 168, 23, -20, 44, -92, 72, -169, -17, -92,
  -304, -268, -192, 34, 58, 42, 118, 141, 153, -129, 27, -32, -240, 189,
  -58, -187, -3, -304, 385, 94, 68, -29, -85, -180, -119, -61, -69, 226,
  307, 195, 78, 124, -2, -6, 53, 78, 22, -114, 191, -36, -28, -50, -54,
  -190, 4, -97, 199, -36, -86, 47, 55, -185, -117, -64, -38, 114, 4, 6, 98,
  -44, 1, -51, -69, -2, 93, -80, 25, -7, 24, 169, -17, -100, -1, 142, 41,
  146, 31, 67, -67, -14, 20, -97, 93, -25, 40, 30, 14, -18, 9, -20, 73, -91,
  267, -24, 91, -23, -55, 71, -161, -46, 316, -5, 66, -22, -63, 4, 14, 104,
  -120, -29, -97, -184, 26, -106, 81, 220, -49, -132, 123, 71, -166, 168,
  -145, 122, 139, 48, 49, 191, 96, 18, 122, -72, 108, -62, -21, 109, -146,
  -10, 298, 96, 204, -214, -11, -47, 250, -76, 243, -9, 269, 147, 246, 201,
  -212]

theorem fractionalNearFrameSubtreeG2R0035_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0035Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0035Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0035Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0035_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0035LowerBoundTable : List ℤ :=
  [136, 674, 338, -80, -125, 513, 2, -193, 153, 611, 796, -17, 171, -118,
  510, 37, 780, 199, 477, -18, 249, 24, 9, 299, 237]

def fractionalNearFrameSubtreeG2R0035LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0035Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0035LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
