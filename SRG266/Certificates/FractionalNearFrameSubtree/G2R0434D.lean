import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0434`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0434Mask : ℕ := 5785393596865176

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0434Witness : Array ℤ :=
  #[-84, 10, 1, 17, 8, -32, -30, -12, -18, 40, 58, 16, 2, 68, -67, 24, -81,
  -11, -4, 34, -24, 104, 24, -25, -23, 53, -50, -36, -122, -85, -71, 69, 45,
  15, -17, 152, 71, -16, 87, 52, 102, 36, 2, 38, 0, -68, -22, -112, 31, 8,
  -81, 55, -22, -32, 0, 60, 58, 60, -124, -117, 159, 49, -141, -63, 30, 0,
  -149, -52, -65, -42, 90, 52, 1, 204, 175, -27, 174, 39, 44, 11, -40, 103,
  -5, -110, -30, 77, 14, -4, -48, 1, 37, 60, 15, 54, -41, 53, 25, -13, 16,
  -42, -34, 49, -38, 95, -53, 58, -40, -7, 15, -43, 56, 32, -59, -24, -42,
  36, 41, -4, -31, 8, -98, 45, 80, 136, 14, -54, 71, -92, 1, 91, 197, -21,
  -56, 19, -94, 67, 126, 39, 21, -29, 11, -30, 111, 148, -115, -20, -68,
  -47, -55, 150, -20, 73, -42, 38, 58, 23, -72, -56, 45, 38, -48, 117, -21,
  44, 229, -26, -30, 78]

theorem fractionalNearFrameSubtreeG2R0434_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0434Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0434Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0434Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0434_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0434LowerBoundTable : List ℤ :=
  [67, 205, 257, 30, 3, -7, 1, 18, 269, 10, 9, 369, 439, -70, 110, 22, 684,
  221, 315, 204, 261, -120, 43, 154, -115]

def fractionalNearFrameSubtreeG2R0434LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0434Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0434LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
