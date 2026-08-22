import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0045`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0045Mask : ℕ := 923369274704966

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0045Witness : Array ℤ :=
  #[8, -48, -98, -212, -56, -170, 74, 0, 162, 6, -25, 92, 203, 111, 138,
  -51, 133, 98, -32, 65, -17, 12, -101, 24, 71, -55, -117, -44, -80, -33,
  69, 126, 66, 130, -20, -5, 2, -20, 66, -12, -65, -69, -20, -10, -23, 0,
  -120, -37, 50, -75, -14, 10, 145, -77, 28, -65, -138, -65, 12, -58, -15,
  69, -2, 129, -42, -101, -43, 82, -2, 11, 94, -14, -8, -31, -31, -64, -11,
  -111, 54, 9, -19, 72, 97, 11, 76, 84, 43, -127, 16, 53, -6, -8, 28, -7,
  11, -24, -21, 103, 123, -44, -79, 22, 37, 68, 16, -68, 23, 96, 62, 75, 57,
  9, 2, 53, -113, 0, -67, -19, -59, -57, -6, 16, 40, 14, -37, 17, -38, 94,
  42, -1, -85, 144, -134, -124, 29, -99, -1, -39, 45, 4, -92, -9, 86, -44,
  97, -91, 176, 53, 11, -2, -16, -111, 111, -7, -17, 38, 38, -148, -53, -92,
  66, -35, 77, -12, -28, -3, -74, 22]

theorem fractionalNearFrameSubtreeG2R0045_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0045Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0045Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0045Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0045_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0045LowerBoundTable : List ℤ :=
  [-142, 2, -176, 24, -144, 1, 100, 93, 32, 549, -154, 394, 11, 265, 4,
  -243, 125, 242, -236, 397, 24, 9, -229, 164, 67]

def fractionalNearFrameSubtreeG2R0045LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0045Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0045LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
