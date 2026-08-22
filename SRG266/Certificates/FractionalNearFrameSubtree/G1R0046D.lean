import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0046`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0046Mask : ℕ := 538516704040020

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0046Witness : Array ℤ :=
  #[-204, 3, -71, -57, -182, 91, 11, -56, 69, 18, 230, 175, 84, -11, -12,
  164, -55, -13, 35, -11, 103, 159, -92, 21, -13, -119, 24, -38, -72, 8,
  -60, -182, -119, -111, 313, 125, -105, -165, 128, 92, 334, 303, -37, 133,
  107, 74, 71, -35, -114, -171, 30, 105, 67, -136, -76, -88, 0, 41, 23, 77,
  57, 111, 83, 128, 90, 161, 135, -110, 147, 25, 128, -61, 27, 11, 7, 61,
  11, -33, 14, -54, -55, 64, -102, 22, 85, 20, 14, 56, 69, -6, -9, 125, 195,
  70, -104, -29, 36, 108, 161, 71, 25, 38, 224, 226, 62, -4, 30, -15, -179,
  -29, 47, -67, -65, 43, 56, 136, -83, -110, -8, -58, 24, -194, -100, 47,
  22, 3, 28, -64, -172, 26, 14, 72, 93, -7, 14, -94, 48, 3, 12, 44, -91,
  145, 56, 77, -21, -44, -47, -43, 117, 91, 107, -188, 1, -32, -233, -5,
  -12, -58, 52, -65, -81, -52, -181, -88, -55, -142, 71, -2]

theorem fractionalNearFrameSubtreeG1R0046_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0046Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0046Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0046Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0046_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0046LowerBoundTable : List ℤ :=
  [32, -219, 101, 203, 75, 208, 9, 110, 2, 439, -182, -128, -260, 955, 912,
  313, -80, 12, 161, 99, 172, 343, 535, 175, 906]

def fractionalNearFrameSubtreeG1R0046LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0046Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0046LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
