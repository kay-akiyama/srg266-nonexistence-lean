import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0581`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0581Mask : ℕ := 6850671300285032

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0581Witness : Array ℤ :=
  #[-33, 21, 94, 11, 143, -67, -82, -100, -30, -56, 6, 139, 20, 90, 111,
  -122, -110, -103, 93, 156, 200, 62, 71, 150, -68, -8, 5, -44, -20, 95, 82,
  89, -25, 83, 0, 36, -4, 12, -1, -140, -78, 0, -4, 12, -164, -97, 16, 166,
  108, 48, -32, 15, 68, 243, 63, -2, 116, 54, -22, -71, -34, 44, 25, 42,
  -76, 78, 104, -26, 5, -22, -31, -63, 42, 28, 101, -43, -51, -20, 23, 77,
  -128, 17, -18, -44, 16, 26, 1, 110, 18, 126, 21, 96, -109, -12, -37, -6,
  0, -130, -80, -122, -34, 142, 50, 137, 171, -36, 134, 75, 130, -126, 87,
  -100, 38, 103, 109, 71, -3, 22, -200, 57, 17, -29, 80, -13, 278, 58, 99,
  0, -107, 89, -57, 68, 49, 6, -18, 22, -32, 108, 115, -63, -44, 17, -37,
  -47, 55, 42, 3, -65, 32, 0, -100, 83, 117, -133, 20, 52, -8, -193, 104,
  84, 85, 92, 10, 80, 147, 70, -114, 3]

theorem fractionalNearFrameSubtreeG2R0581_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0581Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0581Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0581Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0581_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0581LowerBoundTable : List ℤ :=
  [133, 246, 237, 2, -30, 208, 380, 240, 107, 124, 641, 690, 238, 709, 531,
  215, 351, 112, 93, 122, 95, 195, 10, 452, 61]

def fractionalNearFrameSubtreeG2R0581LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0581Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0581LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
