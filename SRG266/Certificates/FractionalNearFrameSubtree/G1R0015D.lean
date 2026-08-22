import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0015`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0015Mask : ℕ := 267075836102929

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0015Witness : Array ℤ :=
  #[-417, -96, -254, -158, -92, -66, 143, 63, 72, -60, 1, 111, 174, 112, 52,
  82, 158, 135, 92, -121, 264, -152, -67, 73, 300, 13, -118, 96, 51, -312,
  -12, -137, 22, -178, 18, -3, 56, 212, -28, 66, -239, -30, 23, -273, 235,
  175, -62, 0, -51, -106, -58, -148, 243, 202, 250, 264, -40, 165, 147, -82,
  56, 147, 52, 59, 109, -252, -23, -108, 273, -24, -17, 48, 74, 151, -29,
  -129, 147, 70, -60, -95, -4, 51, 96, 84, 113, -126, -3, -122, 19, -115,
  28, 122, -132, -142, -212, -116, -130, -168, 242, 52, 83, -63, 194, 56,
  -115, -66, -73, -80, -199, -26, 112, -52, -199, -160, 65, -73, 122, 84,
  38, 77, 176, 137, 344, -318, -21, 281, 69, -43, 29, 59, 173, 364, -106,
  230, -14, -34, 33, 143, 23, 60, 135, 128, 240, -6, 309, -37, 201, 24,
  -127, -36, 104, 2, -193, 88, 85, 93, -41, -207, 144, -147, -92, 19, 77,
  36, 44, 131, 67, 63]

theorem fractionalNearFrameSubtreeG1R0015_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0015Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0015Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0015Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0015_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0015LowerBoundTable : List ℤ :=
  [13, 568, -152, 2, 15, 489, 127, 2, 95, 222, 878, 141, 245, 412, 836, 648,
  595, 229, 367, -31, 44, 12, 392, 10, 1063]

def fractionalNearFrameSubtreeG1R0015LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0015Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0015LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
