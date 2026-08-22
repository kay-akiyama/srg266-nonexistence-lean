import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0020`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0020Mask : ℕ := 437523639479301

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0020Witness : Array ℤ :=
  #[83, 7, 128, -36, -184, -103, -300, -123, -29, -92, -64, 43, 3, 221, 159,
  253, 219, 81, 118, -87, -58, -76, -204, 22, -101, -124, 62, 68, 124, 229,
  -126, -48, 145, -57, 50, 49, 44, 211, 32, 23, -206, -62, -145, -157, 32,
  43, -190, -266, 99, -136, -60, -71, 107, 107, -60, 93, 152, 156, -35, 132,
  11, -190, -43, 76, 4, -139, 212, -110, -141, -69, -45, 4, -8, 29, 176,
  -175, -79, -42, -53, 54, -121, 132, 7, 42, 5, -3, 15, -74, 71, -47, -2,
  44, 92, 41, 19, 91, 4, 156, 98, 17, -38, 70, 179, 26, 145, 98, -136, -111,
  -95, -124, 24, 13, 71, 49, -50, 23, -63, 144, 99, 58, -59, -49, 135, 202,
  103, 39, -91, -39, 111, -136, 91, 29, 138, -57, -24, -78, 108, -131, 12,
  82, -37, 106, 0, -92, -118, -271, 100, -125, 43, -139, -234, -3, 0, -275,
  -68, 41, 206, 52, -16, 4, 10, -43, -49, -30, -26, -266, 15, 117]

theorem fractionalNearFrameSubtreeG1R0020_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0020Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0020Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0020Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0020_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0020LowerBoundTable : List ℤ :=
  [-222, -257, -66, -247, 2, 2, 40, 72, 137, 10, 11, 361, 10, 432, 269, 105,
  796, -127, -728, -294, -234, 207, 234, 103, 152]

def fractionalNearFrameSubtreeG1R0020LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0020Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0020LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
