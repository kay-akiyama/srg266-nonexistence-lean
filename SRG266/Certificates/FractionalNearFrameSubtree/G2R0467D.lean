import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0467`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0467Mask : ℕ := 5808391013966226

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0467Witness : Array ℤ :=
  #[-84, 49, -108, -129, -112, 43, -13, 7, -41, -145, -70, 109, 85, 90, 134,
  46, -33, 10, -91, -35, -76, 78, 41, 32, 18, -8, -21, 1, 36, -12, -65, -14,
  -70, -25, -73, 7, 29, 27, -17, -40, 51, 47, -116, 62, 44, -35, 55, 17, 57,
  -61, -25, 3, -54, -80, -42, -57, -46, 106, -69, 0, -3, 53, 31, -21, -156,
  -25, 18, 31, 8, 43, -40, 22, -3, -10, 23, 40, -23, 47, 13, -89, 49, -137,
  -57, -3, -12, 66, 0, 17, 65, 72, 10, 16, -36, -3, 59, 21, -17, 36, 57,
  -87, 91, 21, 49, -11, 25, -49, 61, 51, -20, 25, 74, 47, -13, 30, 36, 21,
  -52, -62, -16, 72, 35, -72, 78, -51, 11, -67, -29, 3, -60, -5, -104, 69,
  -3, -102, 45, -52, 10, 154, 27, 100, 12, -30, 5, -8, 67, 67, 110, 13, 84,
  -29, 25, 43, -17, 48, -27, 20, -45, 1, -27, -68, -62, 22, -52, -47, 8, 31,
  -38, -17]

theorem fractionalNearFrameSubtreeG2R0467_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0467Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0467Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0467Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0467_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0467LowerBoundTable : List ℤ :=
  [-91, 18, -32, 66, 4, 1, -25, -66, -71, 148, 117, 303, 210, 114, 4, 7,
  -357, 53, 171, -382, 4, 9, -65, 152, 161]

def fractionalNearFrameSubtreeG2R0467LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0467Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0467LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
