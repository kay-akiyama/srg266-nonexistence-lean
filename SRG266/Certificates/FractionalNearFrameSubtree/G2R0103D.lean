import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0103`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0103Mask : ℕ := 1275345057451011

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0103Witness : Array ℤ :=
  #[-8, -32, -40, -71, 57, 0, 52, 87, 52, 87, 55, 85, -86, 0, -64, -43, -6,
  -79, -19, 72, 22, -51, 5, -12, -62, 14, 25, 32, 27, 9, 0, 13, 76, -5, -15,
  43, 1, -71, -20, 17, -19, 22, 21, 74, 25, 22, 45, -30, 27, 0, 13, -10, 49,
  27, -6, 90, -9, -16, 123, 0, -123, 11, -21, 17, -15, 14, 27, 43, 9, -29,
  16, 100, -35, -46, 31, -1, 57, -22, -49, 61, 60, 88, -23, 12, -60, 25,
  -12, 41, 16, 99, 69, 69, 12, 64, 55, -16, -13, -84, -55, 72, 56, 14, -49,
  -26, 36, -38, 37, -4, 1, -89, -69, -101, -53, -52, 8, -3, -17, 113, 28,
  -15, -39, -13, -8, -11, -42, 30, 34, -1, 31, -46, -18, -26, 4, 0, -79, 98,
  48, -20, 0, 22, -63, 63, 0, -121, -20, -107, -31, 86, -110, 61, -101, 35,
  -60, 123, -9, -16, 54, 55, 22, -45, 9, -9, 52, -25, 38, 32, 49, -131]

theorem fractionalNearFrameSubtreeG2R0103_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0103Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0103Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0103Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0103_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0103LowerBoundTable : List ℤ :=
  [3, 1, 2, 90, 2, 31, 108, 130, 10, 226, -65, -47, -196, -127, 158, -32,
  105, 89, 104, 261, 109, 26, 10, 10, 334]

def fractionalNearFrameSubtreeG2R0103LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0103Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0103LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
