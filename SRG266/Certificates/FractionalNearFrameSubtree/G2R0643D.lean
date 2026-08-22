import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0643`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0643Mask : ℕ := 20340650156140038

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0643Witness : Array ℤ :=
  #[-112, -194, 132, -73, 0, -48, -314, -251, 3, -155, -112, 145, 136, -193,
  290, 226, 58, -221, 205, 272, -46, -296, -337, 170, -259, -169, -103, -43,
  0, -93, 107, 251, 34, 138, -43, 37, 58, -64, -61, -172, -1, 62, 56, 336,
  65, -116, -36, 9, -83, 28, 56, 35, 99, 79, 52, 45, 113, 222, 32, 0, -230,
  -202, 163, 3, -27, -268, -99, 168, -85, 367, 79, -29, 143, -86, 15, 52,
  -9, -98, 166, -28, -77, -140, -11, -83, 76, -171, 42, -95, 50, -71, -47,
  78, 28, -246, 58, 95, -66, -119, 213, -6, 78, -87, 55, 0, -107, 126, 105,
  -155, -143, -88, -47, -2, 79, 142, 168, 102, 75, 147, 97, 79, -26, -96,
  165, 2, -161, 0, -134, 138, -16, -66, 47, -196, 86, -44, 129, 247, 133,
  -264, 88, -122, -232, -192, 15, 50, 115, -47, 127, -96, -9, 70, 24, 8,
  -90, -172, -298, 305, 116, 55, 125, 71, 218, 8, 85, -103, -12, 140, 131,
  -77]

theorem fractionalNearFrameSubtreeG2R0643_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0643Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0643Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0643Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0643_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0643LowerBoundTable : List ℤ :=
  [-162, 2, 364, 0, -38, -341, 24, -279, -2, 384, 375, 86, 43, 433, 1069,
  -47, -124, 340, -423, 11, 513, 172, -15, -332, 12]

def fractionalNearFrameSubtreeG2R0643LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0643Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0643LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
