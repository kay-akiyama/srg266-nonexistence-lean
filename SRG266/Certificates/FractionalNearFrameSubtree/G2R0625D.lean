import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0625`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0625Mask : ℕ := 9750100524647000

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0625Witness : Array ℤ :=
  #[-52, -27, 117, -14, -4, -74, 16, -21, 32, 99, -71, -30, -33, 11, 5, 25,
  20, -36, 101, -189, -77, -109, -24, -27, -3, 23, 0, 137, 18, 51, 8, -47,
  30, 0, 55, -92, -31, 150, 19, -41, 35, 0, -42, -45, -90, -47, -49, 0, 43,
  40, -24, -13, 134, -23, 0, 47, 20, -94, 97, 1, -37, -22, -48, 102, 100,
  -43, 26, -1, 26, -1, 22, -28, 31, 8, 0, 1, -50, -54, -56, -2, 16, 19, -17,
  78, -15, 30, 39, -22, 65, 102, 22, 6, 52, -8, 14, 60, 51, 87, -76, 14, 10,
  34, -37, 12, 17, -97, -44, 59, 75, 9, 63, 138, 76, 75, 44, 15, 26, -17,
  38, -104, -65, 89, 67, -77, -29, 57, -39, 43, -84, -75, -43, 47, -5, -11,
  6, -36, -2, -32, 25, -118, -1, 58, -74, 35, -6, -32, -123, -17, -31, 18,
  -25, 51, 95, 53, 31, 10, -46, 72, 47, -30, -152, -6, 55, -75, -60, 41,
  -39, -58]

theorem fractionalNearFrameSubtreeG2R0625_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0625Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0625Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0625Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0625_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0625LowerBoundTable : List ℤ :=
  [-45, 147, 1, 2, 77, 2, -64, 229, -140, -13, -89, 179, 11, 10, 80, 267,
  121, -53, 393, 168, 83, -184, -287, -32, -173]

def fractionalNearFrameSubtreeG2R0625LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0625Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0625LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
