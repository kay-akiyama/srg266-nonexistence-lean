import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0518`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0518Mask : ℕ := 5824745414300264

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0518Witness : Array ℤ :=
  #[98, 478, 354, -140, 531, -816, 283, 509, -354, -240, -335, 299, -132,
  -413, -257, 45, 454, -498, 29, 30, -211, 211, 608, 361, -117, -435, -324,
  12, -344, -73, -454, 27, -54, 332, -127, -286, 175, -134, -764, -26, 397,
  -232, 533, -429, -259, 546, 122, 756, -496, -907, 312, -485, 91, 1225,
  219, 274, 728, 195, 1005, 379, -1023, -932, -997, -509, 390, -119, -30,
  37, 439, -121, 163, 140, 834, -82, 0, 541, -281, 242, -483, -267, 319,
  261, -62, 947, 486, 333, -123, 43, -501, -395, 0, -424, -70, -579, -267,
  -293, -231, -243, 547, 372, -124, 258, 336, -702, -133, -301, 21, -539,
  -594, 316, 0, 428, 123, -624, 796, 512, -234, 693, 92, -379, 623, 454,
  -468, 78, -485, 680, 147, -550, 438, -452, -590, -119, 25, 188, -408, 57,
  -467, -633, 478, -367, 379, 897, 57, 0, -18, -629, -504, -1032, 446, 1223,
  528, -500, 307, -646, 120, -67, -372, -92, 312, 646, -196, -324, 1048,
  -202, -111, 1053, 634, -237]

theorem fractionalNearFrameSubtreeG2R0518_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0518Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0518Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0518Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0518_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0518LowerBoundTable : List ℤ :=
  [-480, 701, -35, 33, 1452, 445, 32, -1951, 358, 690, -267, -1468, -188,
  2021, -626, -2153, 1502, -1869, 2817, 2537, 1609, 590, 1962, -1027, -334]

def fractionalNearFrameSubtreeG2R0518LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0518Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0518LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
