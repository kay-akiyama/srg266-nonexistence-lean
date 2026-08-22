import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0047`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0047Mask : ℕ := 4876250696818819

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0047Witness : Array ℤ :=
  #[-10, -20, 6, -91, -46, -31, 56, 60, 112, 41, 45, -12, 0, 0, 10, -36, 62,
  47, 44, 21, -45, 4, -1, -18, 6, -40, 0, 7, 36, -4, 36, -4, 16, -37, -11,
  3, -15, -10, 0, -38, -1, 23, 7, -18, -40, -4, -38, 10, 19, 17, 13, -30,
  -10, 22, 26, -8, 45, 9, -17, -23, 1, 13, -16, 9, -3, -34, -40, 5, 2, 15,
  -23, -43, 19, -26, 28, -27, -12, -39, -22, 6, 32, -8, 10, 33, 21, 22, -26,
  3, 21, -9, -14, -42, 35, 47, 51, 32, 51, 20, 10, -41, 7, 10, 21, 4, 34,
  26, -27, 17, -4, 42, 36, -23, -58, -36, 32, -5, 19, -11, 57, -53, -13,
  -17, 42, -46, -22, -4, 0, -20, 16, 11, -14, 20, 7, -19, 17, -27, -12, 29,
  -31, -47, -29, 4, 22, 9, 7, 13, 43, -30, 6, 10, -20, -5, -4, -59, -2, 19,
  -63, -55, -42, -5, -26, -16, -43, 0, -19, 0, -44, 24]

theorem fractionalNearFrameSubtreeG5R0047_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0047Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0047Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0047Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0047_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0047LowerBoundTable : List ℤ :=
  [-73, -108, -77, 2, -67, 31, 42, -9, 1, 82, -2, 91, -42, 211, -62, 48,
  -34, 9, -84, 109, 9, 19, 92, 9, 111]

def fractionalNearFrameSubtreeG5R0047LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0047Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0047LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
