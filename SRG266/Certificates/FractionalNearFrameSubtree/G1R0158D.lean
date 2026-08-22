import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0158`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0158Mask : ℕ := 1039894347633072

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0158Witness : Array ℤ :=
  #[45, 15, 36, 0, -15, 77, 24, 18, -56, -74, 1, -62, -21, 0, -30, 20, -22,
  -11, -81, 22, 8, 2, -4, -19, -1, 37, -74, 19, -38, -43, 53, -151, 22, 29,
  12, 23, 66, -46, -40, 34, 109, -22, 5, 75, 23, -74, 12, -33, -19, 68, 51,
  37, 7, -59, 39, 26, 76, -23, -35, 10, 26, 52, 21, -23, 24, 1, 46, -47,
  -20, 120, -24, 16, 43, 0, 76, -25, -35, 42, 6, 2, 47, 42, 116, 60, 0, -4,
  -36, -60, -37, 1, -78, 68, -32, -4, 23, -64, 97, -100, -7, -23, -46, -52,
  -8, 66, 9, -16, 28, -6, -43, 35, 6, -103, -114, -77, 41, 81, 142, 36, 61,
  0, -54, 29, 54, -48, -42, -8, 2, -12, -17, -32, 17, 0, 148, 36, -9, -60,
  -19, -20, 28, -23, -3, 30, -6, -4, -30, 10, -8, -1, 103, -90, 6, -9, 53,
  37, 5, 32, -9, 72, 84, 10, 20, -80, 9, -8, 35, -11, 63, 32]

theorem fractionalNearFrameSubtreeG1R0158_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0158Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0158Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0158Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0158_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0158LowerBoundTable : List ℤ :=
  [-19, 135, 183, 1, 12, 118, 2, 1, 90, 151, 10, 13, 45, 209, -116, 9, 130,
  106, -64, 144, 50, -138, 110, 139, -18]

def fractionalNearFrameSubtreeG1R0158LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0158Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0158LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
