import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0002`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0002Mask : ℕ := 242835045077509

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0002Witness : Array ℤ :=
  #[-112, -72, 41, 15, -34, 0, 59, -23, -77, 44, 45, -32, -5, 130, 32, 0,
  65, 7, 42, -50, -58, -23, 17, 63, -47, 64, 9, -108, -43, -23, -11, -110,
  -79, -59, -58, -116, 155, 127, 72, 102, -27, -21, -139, -131, 95, 19, 42,
  -89, -24, 13, 73, 13, 99, -12, 8, 0, 100, 86, 62, -41, 54, -52, 69, 13,
  54, -19, -95, 125, 93, -19, -122, 38, -75, 26, 59, -99, 53, -78, -40, -20,
  -9, -89, -71, -128, 7, -17, -62, -19, 61, -90, 44, 87, 10, -17, 65, 39,
  62, -49, 61, -7, 63, -97, -81, -58, 33, -66, -28, -32, 62, 11, 7, 89, 25,
  35, 71, 48, 57, -122, -114, 18, -8, -13, 59, -89, 4, 62, -46, -12, -33,
  -14, -57, -1, -183, -66, 18, 51, 138, -76, 71, -29, -65, -18, 54, -163,
  -28, 73, -104, -38, 59, 33, 80, 88, -23, -54, 10, 57, -23, -32, -15, 11,
  -26, 50, -13, 101, -111, -90, 34, 41]

theorem fractionalNearFrameSubtreeG1R0002_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0002Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0002Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0002Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0002_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0002LowerBoundTable : List ℤ :=
  [-133, -89, -31, -103, -116, 142, -127, 2, 2, 178, 97, -3, -102, -61,
  -214, 293, -19, -236, -290, 105, -314, 10, 154, 283, 216]

def fractionalNearFrameSubtreeG1R0002LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0002Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0002LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
