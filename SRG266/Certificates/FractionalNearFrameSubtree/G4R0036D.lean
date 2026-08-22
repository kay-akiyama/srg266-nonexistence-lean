import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G4R0036`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0036Mask : ℕ := 5440781384271110

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0036Witness : Array ℤ :=
  #[-44, 166, -90, 40, 56, 92, -26, 90, 70, -9, 35, -33, -19, -141, -75,
  -109, -41, 22, -121, 118, -42, -101, -52, -68, -140, -41, -98, -96, 51,
  105, 6, 210, 29, 66, 55, 0, 14, -13, -33, -20, 3, 6, 0, -42, -8, 89, 135,
  9, -67, 27, -56, -76, -30, 5, 102, -102, -8, 33, 74, -37, 58, -12, 43, 85,
  -61, 23, 67, 60, 50, 39, 5, 4, -19, -22, -42, 29, -7, 10, 69, -99, 29, 3,
  -97, -3, 4, 58, -30, -53, 38, 15, -49, -75, 110, -86, 59, -32, 96, 50,
  -43, 46, 9, 82, 64, 46, -34, 9, 49, 46, -32, -14, 9, -36, -35, -61, -20,
  -61, -20, 131, 26, -14, 16, 0, -48, 51, 80, 12, 16, 26, 79, 119, 12, 25,
  -3, 59, -87, -24, 88, 83, -53, 42, -11, -65, 54, 52, 32, 14, 136, -20, 43,
  24, 127, 103, 95, 116, -57, 87, 56, -19, 50, -11, -35, -12, -27, 3, -11,
  -97, 45, 71]

theorem fractionalNearFrameSubtreeG4R0036_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0036Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0036Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0036Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0036_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0036LowerBoundTable : List ℤ :=
  [45, 223, 202, 167, 2, 277, 100, -230, -115, 388, 574, 86, 36, 395, 43,
  120, -106, 360, 223, 92, 80, 99, 550, -29, 10]

def fractionalNearFrameSubtreeG4R0036LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0036Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0036LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
