import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0489`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0489Mask : ℕ := 5811173046478348

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0489Witness : Array ℤ :=
  #[36, 74, 226, 127, -66, -80, 34, 135, 9, 2, 48, -160, 32, -117, 0, 47,
  -15, 117, 109, -71, 60, -5, 47, 20, 39, 114, 28, -30, 69, 155, 7, 82,
  -123, -105, 249, 113, -96, -55, -56, -5, 206, 232, 92, 58, 80, 147, 143,
  -120, -177, -141, 73, 151, 57, -199, 162, -13, 17, -217, 41, 10, -42,
  -129, 39, -93, -131, 53, -32, 80, -13, -86, -82, 72, 58, -46, -164, 49,
  170, -116, -13, 50, 86, -37, 10, -69, 17, -42, -1, -25, 50, 145, 32, 8,
  -77, -38, 31, -28, 0, -11, 86, 60, 99, 29, 31, 101, 46, 27, -77, 40, 129,
  106, -74, 18, 240, 73, -99, -44, 31, 174, 126, 104, 11, 10, -5, 23, 25,
  54, 31, 21, -179, 77, 109, 67, -23, -39, -129, 81, 83, -15, -83, -67, -75,
  52, 33, 115, 88, -38, -44, -76, -150, -102, -51, 172, -14, 132, 30, -69,
  36, -56, 56, -1, -175, 2, -85, -17, -45, 0, -2, -96]

theorem fractionalNearFrameSubtreeG2R0489_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0489Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0489Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0489Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0489_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0489LowerBoundTable : List ℤ :=
  [37, -48, 2, 3, 306, 151, 2, 190, 264, 93, -171, 440, 528, 210, 18, 85,
  234, 367, -27, 255, 733, 150, 618, -76, 546]

def fractionalNearFrameSubtreeG2R0489LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0489Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0489LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
