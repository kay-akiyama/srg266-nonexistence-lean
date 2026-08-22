import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0018`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0018Mask : ℕ := 1039299964281859

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0018Witness : Array ℤ :=
  #[-17, 63, 6, 35, -50, 43, -93, -96, -190, -194, -179, 128, 164, 98, 90,
  138, 15, 62, 50, 48, 26, 24, 21, 95, 12, 0, -20, -116, -123, -38, -124,
  -6, -39, 34, -83, -140, 23, 3, -12, 84, 11, 69, 71, -45, 116, 58, -32,
  -27, 19, -15, -31, 101, -11, 13, -1, -87, -51, -5, -1, 48, 28, -26, -27,
  -25, -2, -1, -5, 58, -26, 93, 82, -116, -28, -67, -12, -85, 91, -26, 79,
  -36, 25, 94, 60, 2, 4, -43, 15, 4, -14, -40, 92, 119, 12, -152, 21, -52,
  5, -14, 29, 68, -17, 67, -23, -41, -67, -81, -49, -57, -16, 65, 29, -25,
  67, 53, 13, -47, -14, 9, -61, -6, -15, -69, 101, 21, -54, -41, -11, 18,
  92, 76, 22, -29, -100, -20, -3, -35, -32, 12, 24, -62, 29, 22, 53, -34,
  -17, 122, 128, 4, 15, 52, 157, 21, -15, 82, -25, 60, -37, -68, -43, -12,
  -18, 11, 52, -37, -92, 115, -131, 18]

theorem fractionalNearFrameSubtreeG5R0018_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0018Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0018Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0018Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0018_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0018LowerBoundTable : List ℤ :=
  [-72, 16, -91, 140, -72, -120, 1, 67, 23, 10, 296, -82, -170, 75, 46, 369,
  398, -39, 40, 336, -214, 129, -74, 8, 110]

def fractionalNearFrameSubtreeG5R0018LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0018Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0018LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
