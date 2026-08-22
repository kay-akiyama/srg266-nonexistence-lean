import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0562`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0562Mask : ℕ := 6846330124833418

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0562Witness : Array ℤ :=
  #[269, 57, 116, 224, -126, 188, -41, 62, 26, -171, -149, 257, 52, 84, 111,
  -151, 37, -15, -104, 143, 148, -84, 175, -139, 46, -22, 159, 151, 26, 41,
  88, 157, -3, 45, -95, 54, -17, -61, 21, -70, 131, -212, 14, -7, 51, -96,
  62, 23, 55, -29, -48, -108, -26, 5, -98, 179, 173, -43, 100, -11, -84,
  114, -19, 146, -211, 124, -50, 40, 229, 62, 277, -50, 103, 90, 235, -82,
  -67, 72, -98, 152, -44, 24, 230, 50, -72, -122, -123, 76, -124, 128, 241,
  25, 66, -37, 190, -20, -92, 118, -66, -3, 61, -5, -173, -7, 48, 228, 104,
  17, -85, -64, -113, -78, -9, 113, 70, 52, 234, -117, 49, 25, 117, -43,
  -49, 249, -70, -3, 59, -8, 191, 182, 211, 204, 3, -58, 71, -102, -6, 81,
  -26, 141, -43, 40, 223, 43, 34, 320, 68, -68, -54, 196, -194, 130, -262,
  158, -214, -35, -148, -64, -72, 58, -7, 114, 1, -9, 97, 88, -64, 135]

theorem fractionalNearFrameSubtreeG2R0562_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0562Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0562Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0562Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0562_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0562LowerBoundTable : List ℤ :=
  [217, 392, 189, 532, 282, 191, 505, 456, 225, 440, 1013, -65, 9, 11, 509,
  931, 10, 518, 475, 740, 553, 149, 88, 264, 599]

def fractionalNearFrameSubtreeG2R0562LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0562Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0562LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
