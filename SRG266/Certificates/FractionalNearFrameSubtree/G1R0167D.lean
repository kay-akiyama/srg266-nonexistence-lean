import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0167`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0167Mask : ℕ := 2371053616483345

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0167Witness : Array ℤ :=
  #[-119, -93, -145, 19, -109, -93, 31, 56, 2, 70, 30, 0, 150, 25, 150, 152,
  43, 159, 123, 101, 63, 31, 5, -15, 78, 125, 69, -5, -55, -37, -86, -21,
  44, 6, 103, 66, -86, -71, 15, -52, 90, -6, 55, -61, 76, 38, -79, -11, 8,
  87, -5, 3, -22, 65, 25, 6, -22, 57, 105, 22, -49, -8, -17, 16, 100, 7, 44,
  -50, 102, -34, -30, 43, -13, 89, 8, -17, 70, -2, -71, 11, -19, -75, 75,
  -6, 6, 2, -55, 99, 44, -65, -47, -65, 52, 34, 13, -107, 1, 83, 2, -66, 9,
  58, 60, -23, 62, -90, 26, -26, -6, -19, -11, -65, -35, -100, 19, 89, 42,
  -77, -27, -14, 51, 97, -11, 25, 71, 14, 4, -31, 23, -42, -24, -36, 10, 12,
  -4, -41, 34, 2, -50, 44, 66, 6, 81, -14, 9, 9, 101, -5, 37, 54, -13, -1,
  -30, 33, -8, 56, -41, -97, -100, 27, -37, -17, -84, 94, 22, -25, 119, -88]

theorem fractionalNearFrameSubtreeG1R0167_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0167Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0167Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0167Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0167_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0167LowerBoundTable : List ℤ :=
  [37, 61, 58, -50, 106, 182, 320, 2, 117, -22, 35, -39, 203, 384, 266, -13,
  34, 12, 148, 179, 279, 10, 64, 79, 414]

def fractionalNearFrameSubtreeG1R0167LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0167Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0167LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
