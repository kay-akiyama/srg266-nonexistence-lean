import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0426`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0426Mask : ℕ := 5778806165511700

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0426Witness : Array ℤ :=
  #[-197, -162, -71, -209, -394, 50, 346, 206, 114, 46, 140, 116, 124, 112,
  187, 321, -81, 75, 277, 225, -62, -103, 87, 153, 0, -54, -39, -175, -23,
  99, -32, 88, 84, -45, -110, 9, 185, -26, 112, 103, 52, 213, 221, -4, 259,
  56, 160, 221, -7, 129, -184, 91, 200, 196, -16, -134, -97, -100, -32,
  -179, 82, -115, -158, 117, 171, 140, -101, 316, 249, 34, -221, 82, -14,
  61, -53, -153, 16, -331, -107, 145, 104, -13, 244, -167, 54, -45, -69,
  229, 14, 119, 255, 273, -123, 124, 163, -74, -99, 99, 147, 53, 7, 92,
  -166, -119, -41, 134, -10, 37, -147, 44, 158, 235, 300, -12, 103, 112, 0,
  177, -49, -7, 178, 114, -56, -91, -40, -1, -111, -23, 30, -133, -114,
  -157, -4, -77, -165, -320, 188, 9, -83, -194, 73, -70, 40, 61, 16, 16, 50,
  -29, 38, -32, -48, 0, -44, -130, 34, 153, 128, -1, 14, 56, -38, -116, -54,
  -5, -71, 92, -87, -344]

theorem fractionalNearFrameSubtreeG2R0426_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0426Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0426Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0426Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0426_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0426LowerBoundTable : List ℤ :=
  [111, -208, 86, -152, 527, 379, 2, 647, 449, 248, 239, 545, 63, 284, 10,
  -15, 285, -7, 768, 114, 584, -110, 1013, 90, 988]

def fractionalNearFrameSubtreeG2R0426LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0426Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0426LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
