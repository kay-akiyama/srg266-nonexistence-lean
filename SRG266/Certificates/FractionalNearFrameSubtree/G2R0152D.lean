import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0152`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0152Mask : ℕ := 1376362546795666

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0152Witness : Array ℤ :=
  #[70, 13, 49, -61, -139, -42, -74, 108, 7, -78, -30, -15, -24, 5, 30, -11,
  42, 55, 71, -150, -103, 109, -51, 23, 60, 2, 45, 26, 3, 30, 167, 46, 44,
  -43, -53, -44, -128, 26, -31, -50, -45, -101, 38, 92, -83, 53, -54, -96,
  145, 7, 26, -16, 8, -28, 70, 92, -115, 0, 57, -133, -85, -75, 17, 20, 31,
  82, -26, -243, 122, 4, 92, 38, -16, 17, -42, -121, 0, -109, 94, 202, 85,
  40, 118, 42, 28, 91, -43, 159, -41, 55, 133, 180, 17, 152, 86, 117, 19,
  -20, 119, -21, 91, -57, 62, 111, 19, 96, -38, 102, 0, -111, 30, 142, -138,
  -29, -121, -51, -42, -41, 35, -27, -21, -20, 15, 65, 36, -14, 146, 20,
  121, 71, -5, 32, -7, -37, -12, 176, -3, -90, 128, -72, -181, 191, 56, -12,
  13, -29, 13, 143, -27, 89, 53, 4, 125, 91, -19, -44, 0, -20, -10, 31, 54,
  -43, -20, 8, 56, 58, 86, 4]

theorem fractionalNearFrameSubtreeG2R0152_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0152Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0152Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0152Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0152_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0152LowerBoundTable : List ℤ :=
  [59, 234, 319, 130, 109, 145, 83, 1, 41, 267, 94, 128, 184, 783, 400, 576,
  240, 118, 487, 182, 213, 71, 86, 219, -82]

def fractionalNearFrameSubtreeG2R0152LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0152Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0152LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
