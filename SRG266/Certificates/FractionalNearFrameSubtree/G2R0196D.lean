import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0196`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0196Mask : ℕ := 2338372832969219

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0196Witness : Array ℤ :=
  #[4, -20, -70, -26, -53, -52, 15, -141, 19, -77, 35, 80, 0, 70, 139, 55,
  101, 54, -121, -67, 19, -18, 38, -16, 53, 106, 55, 216, 274, -166, -130,
  -67, -14, -282, 24, 68, 1, -31, -7, -20, 89, -117, 98, 60, 27, 55, 81, 0,
  77, 58, 0, 47, 45, -57, -92, -1, -20, -45, 64, -8, 19, -6, 100, 35, 29,
  82, 39, -94, -10, 79, -81, 114, -23, -82, 55, 41, 0, 69, 46, -107, -40,
  38, 14, 29, 38, -48, 198, -4, 21, -124, 70, 22, -31, 2, -27, 81, 4, 89,
  -11, -114, 74, 13, 62, 110, 76, 37, 165, 118, -117, 120, -123, 6, 75, -12,
  -39, 229, -52, 68, 22, -15, -18, -104, -65, -54, 54, 44, 70, 2, 26, 51,
  53, 104, -41, 78, 42, -80, -7, -36, -4, 118, -12, 68, 105, -28, -57, 40,
  87, 61, -5, -81, -23, -1, -72, -112, 26, 1, -129, -13, 1, -41, -28, -2,
  39, -70, 117, 18, 0, -221]

theorem fractionalNearFrameSubtreeG2R0196_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0196Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0196Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0196Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0196_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0196LowerBoundTable : List ℤ :=
  [61, 3, 130, 78, 106, 180, -12, 210, 1, 198, 56, 68, 51, 236, 339, 253,
  410, -95, 175, 342, 236, 10, 229, 9, 347]

def fractionalNearFrameSubtreeG2R0196LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0196Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0196LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
