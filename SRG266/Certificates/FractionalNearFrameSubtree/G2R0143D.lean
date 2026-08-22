import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0143`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0143Mask : ℕ := 1362066748641954

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0143Witness : Array ℤ :=
  #[100, 63, 3, 66, -103, 53, 14, 41, 4, -8, -12, 14, 25, -131, -47, -88,
  -45, 0, -26, -3, -5, -3, -107, -35, -53, -10, 35, 1, 33, 76, 69, -102,
  -52, 52, 120, 103, 92, -21, 63, 1, 24, 34, 74, 27, -75, 30, 105, 96, 13,
  -77, -40, -81, 133, -89, 46, 56, -13, 105, -22, -27, -109, 70, 109, -21,
  -46, 75, 47, -67, -32, 6, 56, -15, -11, 40, -112, 40, 75, 9, 99, 76, -124,
  -104, 20, 60, 80, 120, -39, -64, -97, 20, 32, 172, 108, -109, 125, -40,
  17, 77, 22, -43, -79, -136, -58, -29, 58, 29, -30, 53, -73, 131, 23, 84,
  -57, 11, -89, -148, -50, -104, 3, 57, 92, -4, 69, -2, -43, -36, -35, 31,
  10, 13, 8, 68, 26, 54, 82, -142, 40, -69, 69, 32, -66, 57, 98, -77, -39,
  -36, -29, -28, 83, -117, 59, 0, -34, 87, -96, 44, -11, -19, -58, 18, 19,
  137, 29, 101, 122, 11, 46, -37]

theorem fractionalNearFrameSubtreeG2R0143_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0143Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0143Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0143Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0143_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0143LowerBoundTable : List ℤ :=
  [-8, 37, 31, -76, -25, 155, 45, 136, 186, 10, 200, 150, 344, 190, 129,
  347, 195, 320, 10, 35, -350, 24, 351, 9, 224]

def fractionalNearFrameSubtreeG2R0143LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0143Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0143LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
