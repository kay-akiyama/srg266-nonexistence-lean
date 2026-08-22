import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0398`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0398Mask : ℕ := 5740372786647842

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0398Witness : Array ℤ :=
  #[-130, 213, 52, 192, 226, -28, 6, -258, 23, -162, -44, 210, 178, 193,
  162, -14, 121, 206, 8, -37, -61, 64, 125, -35, -44, -31, -10, 121, 78, 2,
  23, 145, 148, 10, -6, -113, -216, 46, -60, -20, 92, -62, 0, -40, 210, 114,
  146, 43, 50, -3, -222, -154, -166, -58, -160, -160, -12, 56, -5, 69, 50,
  -193, 22, -90, -21, -49, 76, 120, 41, 0, -92, 188, -99, -75, 145, 76, -30,
  -165, 118, 114, 206, 209, -118, -106, -118, 12, 43, -15, 52, 88, 46, 10,
  -177, -76, -125, -122, -60, -252, -63, -52, 129, 97, 114, 39, -140, 124,
  121, 46, 169, 110, 117, 80, -83, 60, -43, -6, -52, -163, 85, -34, -36,
  198, 51, 162, 17, -87, 199, 41, -75, 113, -80, 153, 193, 8, 145, -128,
  188, 156, 113, 110, 396, -74, 140, -347, 291, -33, -121, 229, 28, -138,
  119, 13, 155, -60, -161, -117, 139, -180, -161, -97, 144, -73, -31, 62,
  12, 188, -154, 13]

theorem fractionalNearFrameSubtreeG2R0398_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0398Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0398Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0398Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0398_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0398LowerBoundTable : List ℤ :=
  [38, 353, -85, 25, 9, -41, 568, 207, 404, 264, 834, 535, 569, 129, 775,
  -100, 476, -321, -187, 507, 586, 10, -143, 550, 96]

def fractionalNearFrameSubtreeG2R0398LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0398Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0398LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
