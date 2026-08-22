import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0022`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0022Mask : ℕ := 745180735980035

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0022Witness : Array ℤ :=
  #[14, 97, 105, -5, 21, 4, 79, -5, 98, 101, 18, -34, 0, -48, -149, -61,
  -142, -139, 86, -65, 2, -101, -81, -140, 89, -87, 5, -123, -65, 96, 73,
  58, 145, 183, 52, 32, 5, 32, -56, 3, 17, -5, -34, -43, -15, -88, -16, 26,
  41, -22, 1, -48, -22, -6, -16, -8, -44, 55, 80, 26, -9, -3, -23, 26, -22,
  39, -95, 22, -25, 15, 14, -19, 7, -22, -6, -21, -49, 11, 19, 28, -13, 13,
  -15, 2, 26, -35, 122, -9, 37, 30, 4, 45, 40, 40, 24, 75, -77, -28, -9,
  -15, 17, 11, 26, 9, 20, -1, -21, 15, 13, 0, 32, 13, -14, -23, -46, -24,
  -87, -14, 19, -18, 2, -1, 4, -27, -10, 22, -10, -25, 13, -44, 42, 93, -17,
  -2, 3, -10, 54, -89, 42, -17, 13, -18, -25, -34, 3, -12, 7, -8, -33, -19,
  -5, 6, -3, 60, 53, -17, 17, 49, -80, -2, 25, 102, 31, 27, -104, 88, -12,
  71]

theorem fractionalNearFrameSubtreeG2R0022_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0022Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0022Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0022Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0022_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0022LowerBoundTable : List ℤ :=
  [-24, 13, 68, 74, 2, 13, 20, 1, 105, 110, 51, -31, -176, 159, 94, 9, -121,
  70, 28, 73, 11, -114, 131, 139, -279]

def fractionalNearFrameSubtreeG2R0022LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0022Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0022LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
