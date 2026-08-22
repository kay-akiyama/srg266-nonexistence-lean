import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0292`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0292Mask : ℕ := 5386184991351186

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0292Witness : Array ℤ :=
  #[-23, -259, -224, -243, -266, -131, 295, 225, 219, 235, 114, -11, 15,
  -55, -186, -69, 107, -139, -246, -39, -195, 74, 28, -92, 10, -90, 173,
  190, 74, 137, 189, -34, 403, 13, -118, -142, -10, -72, 90, -47, -155,
  -100, 0, 128, 189, -128, -182, 89, 49, -23, -45, 24, 134, -68, 80, 165,
  -21, -44, 5, -58, -13, 51, -114, 64, 128, 33, -139, -87, -115, -21, 125,
  207, 56, 3, 187, 269, 31, 185, 49, 72, -104, 89, -30, 16, 70, -91, 167,
  118, 160, 9, 114, -13, 20, 130, -3, 92, 207, 66, 195, 69, -65, -206, -69,
  -207, -151, 136, -96, 102, 72, -50, 8, -95, 2, -23, -152, 140, -17, -58,
  -77, 26, 90, -144, -218, -18, 169, 39, -99, -108, -86, 43, 7, -45, 0, 73,
  51, 133, 111, 27, 30, 142, 6, -6, 91, 44, -1, 15, 76, 12, 83, 224, 75, 55,
  -254, -47, -23, -142, -293, 56, 17, -36, -116, -99, -29, 108, -11, 147,
  -158, -36]

theorem fractionalNearFrameSubtreeG2R0292_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0292Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0292Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0292Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0292_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0292LowerBoundTable : List ℤ :=
  [-42, 2, 313, 33, 194, -180, 25, 31, 182, 10, -33, 469, -215, 1238, 9,
  546, 262, 203, 11, 10, 152, 355, -181, 302, -489]

def fractionalNearFrameSubtreeG2R0292LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0292Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0292LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
