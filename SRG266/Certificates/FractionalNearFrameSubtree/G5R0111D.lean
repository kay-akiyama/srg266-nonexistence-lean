import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0111`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0111Mask : ℕ := 5792748852317187

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0111Witness : Array ℤ :=
  #[80, 105, 10, -13, 86, 60, -191, -151, -38, -222, -205, 101, 106, 50,
  254, 144, 99, 129, 100, 5, 224, 154, 42, -35, 255, 0, 38, -196, -179,
  -289, -127, -9, 42, 20, -13, -109, -219, -164, 285, 354, 147, -117, -64,
  -179, 222, -162, 81, 153, -8, 92, 88, 123, -149, -176, -9, 3, 128, -45,
  101, 110, 45, 44, -48, 43, -116, 60, -97, -52, -74, 80, 117, 71, 21, -51,
  -16, 142, -12, -9, -19, 132, 21, 29, 90, 53, 67, 245, 212, -48, 146, -17,
  53, -115, -17, 27, -7, 245, 187, -47, -106, -124, 170, -80, -109, 22, -62,
  -218, 5, -103, -45, 20, 43, 96, -32, 54, -125, -7, 63, 87, 2, 87, -3, 151,
  -105, 45, 56, 86, -90, -35, -112, -65, -53, 12, 74, 32, 53, 45, -115, -74,
  -146, 16, -54, -63, 93, 3, 73, -9, 51, -16, 8, 22, 11, -55, 20, 19, 109,
  130, -56, 18, 147, 74, 52, 57, -25, -54, -53, -23, -125, -19]

theorem fractionalNearFrameSubtreeG5R0111_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0111Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0111Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0111Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0111_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0111LowerBoundTable : List ℤ :=
  [65, 2, -14, 325, 2, 233, 89, 392, 1, 226, 48, -355, 287, 185, -124, 197,
  109, 418, 723, 338, 150, 463, 11, 504, -98]

def fractionalNearFrameSubtreeG5R0111LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0111Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0111LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
