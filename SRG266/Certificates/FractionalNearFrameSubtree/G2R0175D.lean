import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0175`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0175Mask : ℕ := 1384865772835928

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0175Witness : Array ℤ :=
  #[-18, 6, -42, 54, 53, -62, -22, 21, -11, 59, 149, -5, 197, -2, -17, 17,
  129, 53, -30, -96, -180, 8, 0, 66, -88, 143, 10, -44, 30, 35, 199, 95,
  198, -209, -33, 81, 62, -227, -7, -9, -3, -108, 64, -77, -32, 30, 122,
  -64, -63, 65, 24, -14, -214, 38, 59, 185, 104, 91, -34, 103, -106, -239,
  -19, 61, -154, 2, 104, 45, 86, -36, -32, 19, 47, -54, -50, -54, -59, 40,
  -100, -126, 181, -26, -120, -99, 89, -93, 65, -92, -13, -32, -4, -43, -40,
  -39, -61, -245, -239, -3, 24, -90, 132, -71, -46, -35, 152, 9, 38, -34,
  -225, -71, 45, 111, 126, -105, -91, 164, 62, 237, 137, -60, -5, -60, 127,
  184, -120, -59, 74, 68, -18, 43, 326, 30, -30, 15, 168, -80, -9, 112,
  -172, 171, 103, -128, 197, 41, 2, -76, -205, -30, 35, 51, 37, 94, 67, 19,
  -56, -152, -28, 86, 56, -203, 102, -42, 53, 153, 43, -6, 77, 33]

theorem fractionalNearFrameSubtreeG2R0175_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0175Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0175Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0175Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0175_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0175LowerBoundTable : List ℤ :=
  [-50, 305, 2, -8, 130, -119, -157, 247, 2, 430, 18, 283, 244, 215, 255,
  191, -162, -257, 165, 813, 155, -429, 149, -197, -20]

def fractionalNearFrameSubtreeG2R0175LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0175Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0175LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
