import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0080`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0080Mask : ℕ := 971464298439272

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0080Witness : Array ℤ :=
  #[-7, -30, -96, 68, 0, -121, 64, -126, -153, -99, 100, 126, 145, 110, 50,
  49, -33, -15, 94, 24, 124, 83, -80, -49, -53, -73, 66, -75, -60, 156, 42,
  0, -155, -5, 85, -126, 59, -167, 6, -82, 0, 85, -154, -21, -25, 102, -53,
  91, 10, 46, 125, -43, -15, -64, -153, 0, -102, 0, -66, 18, 201, 25, 95,
  38, 73, 138, -36, 53, 135, -67, 57, -3, 60, 1, 106, -31, 53, 19, -127,
  -62, -59, -52, -128, 10, -6, 19, 30, -39, -37, 151, -25, -38, -36, 10,
  -43, -124, 62, -22, 54, 50, -66, 114, -24, -66, -50, -6, 63, 93, -39, 75,
  -77, 39, -103, -50, -32, 158, 102, 81, 48, -200, -128, -198, 23, 85, 10,
  60, -117, 59, 63, 0, -128, -49, 0, 75, 34, 76, 0, -7, -19, 59, 47, 35,
  -87, 98, -39, 98, 35, -138, 39, -82, -31, 33, 17, 42, -41, -70, 94, -13,
  -79, -15, 96, -90, 130, -57, 59, -35, -42, 0]

theorem fractionalNearFrameSubtreeG2R0080_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0080Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0080Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0080Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0080_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0080LowerBoundTable : List ℤ :=
  [-145, 3, -69, -71, -98, 85, 198, 2, -8, 171, 99, 376, 11, 97, 404, -48,
  -292, 10, -124, -57, -74, -39, 23, 478, -226]

def fractionalNearFrameSubtreeG2R0080LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0080Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0080LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
