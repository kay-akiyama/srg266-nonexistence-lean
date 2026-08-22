import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0065`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0065Mask : ℕ := 970030480540298

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0065Witness : Array ℤ :=
  #[32, 51, -17, 99, 1, 158, 70, 6, 85, 48, 65, -124, -106, -195, 18, -140,
  13, 5, -13, -56, -18, -32, 49, -36, -14, 18, -9, 58, 15, -19, 0, -63, -44,
  -23, 53, 28, 23, -99, -56, -33, 20, -20, 15, -27, -26, -7, 91, 73, 59, 31,
  -20, -120, -66, -40, -2, -24, 79, -95, 151, -62, 100, 20, -69, -197, -57,
  -32, 5, -40, 23, -1, -29, -31, 23, -14, 0, -21, -57, -88, -2, 50, -49, 30,
  -18, 3, -102, -32, 46, 60, 19, 62, -8, 62, -54, 28, 3, 47, 28, -124, 70,
  19, -13, 35, -141, 42, 29, -62, -53, 7, -22, -86, 18, -40, -15, 60, 63,
  -40, 21, 0, 56, 46, 0, -166, -154, -63, 10, 36, -103, -38, -11, 29, -118,
  -44, 102, 36, 167, -42, 0, -7, -97, -25, -26, -100, -38, 53, 89, -29, -95,
  -22, -125, 3, -80, -14, 83, 15, 67, 51, 26, 150, 112, 26, -7, 42, 99, -57,
  44, -71, 18, 118]

theorem fractionalNearFrameSubtreeG3R0065_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0065Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0065Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0065Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0065_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0065LowerBoundTable : List ℤ :=
  [-167, -1, -72, -39, -33, -21, 2, -101, -181, 75, -427, 23, 55, 11, 85,
  -395, -8, 14, 9, -198, 10, 254, 223, 213, -201]

def fractionalNearFrameSubtreeG3R0065LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0065Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0065LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
