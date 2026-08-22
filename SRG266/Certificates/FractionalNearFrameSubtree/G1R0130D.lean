import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0130`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0130Mask : ℕ := 970618865764784

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0130Witness : Array ℤ :=
  #[-40, 25, -11, 9, 3, 115, 102, 9, -61, 16, 40, 36, -12, 15, -23, 13, -94,
  -29, 47, 42, 18, 0, 64, 10, 27, 101, -25, -108, -20, 0, -179, 216, -7, 88,
  -62, 15, -31, 25, 59, 2, 68, -60, 113, 73, -88, 53, 11, 25, 24, 72, -12,
  15, 24, 73, 68, -67, -168, 9, 21, -61, -155, 149, 40, -14, 96, -53, 91,
  -157, -14, -43, -24, 94, 49, -82, -5, 16, -107, 204, 10, 6, 40, -1, 28,
  -73, 50, 148, -22, 37, -32, 93, -30, -45, -9, -51, 94, 38, 62, 124, 170,
  87, -28, -42, 11, 16, 77, -17, 128, 79, -64, 110, 131, 241, -130, 47,
  -152, 13, 45, -69, -152, -76, -17, 24, 78, 85, 58, -4, 18, 43, 12, 38, -9,
  124, 84, -26, -123, 4, 71, 4, -9, -29, -48, -4, -8, -5, 128, 40, -33, -54,
  66, -55, -69, -4, -78, 31, 187, -23, 31, 79, -14, 73, -42, -15, -6, -75,
  -42, -87, 10, 158]

theorem fractionalNearFrameSubtreeG1R0130_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0130Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0130Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0130Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0130_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0130LowerBoundTable : List ℤ :=
  [87, 56, 28, 112, 171, 255, -80, -22, 297, 242, 553, 149, 171, 296, 10,
  105, 463, 437, -119, -93, 254, 343, 430, 395, 265]

def fractionalNearFrameSubtreeG1R0130LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0130Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0130LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
