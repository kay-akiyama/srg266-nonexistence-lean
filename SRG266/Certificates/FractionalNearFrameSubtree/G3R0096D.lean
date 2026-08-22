import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0096`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0096Mask : ℕ := 2517449063731874

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0096Witness : Array ℤ :=
  #[145, 165, -56, 78, 41, 37, 100, 52, 85, -81, -99, 0, -128, -95, -217,
  -102, -62, 99, -7, -65, -82, 2, 53, 9, -121, -51, 96, -34, 171, 235, 12,
  -66, -122, 38, -20, 59, 64, -16, -129, -111, 124, 28, 54, -3, 13, 31, -80,
  -42, -99, 130, 2, 76, -44, -132, -125, -50, 3, 80, 38, 50, -39, 46, 100,
  13, -10, 72, 23, 9, 13, 128, 51, 30, 0, 35, -42, -15, -45, -18, 20, 26,
  37, -27, -122, -17, -2, 7, 143, 8, -37, 20, 93, 11, 52, 67, 44, 222, 36,
  -26, 40, 1, 85, 256, 51, -133, 127, -113, 184, 74, 19, -28, -84, 64, 59,
  64, -24, -93, -143, 76, 40, 125, -149, 45, 50, 137, -65, -170, 81, -1, 75,
  -41, 14, 100, -43, 16, 130, 60, 18, -65, 71, 0, -84, 25, -140, -84, -65,
  -90, 0, 69, 215, 86, 75, 149, -60, -14, 25, 132, -116, -96, -18, 50, -24,
  -62, 38, 17, 120, 82, 62, 110]

theorem fractionalNearFrameSubtreeG3R0096_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0096Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0096Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0096Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0096_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0096LowerBoundTable : List ℤ :=
  [28, 214, 151, 230, 146, 319, -49, 2, 123, 391, -170, -47, 193, -8, 88,
  11, 272, 685, 248, -34, -75, 513, 142, 390, 573]

def fractionalNearFrameSubtreeG3R0096LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0096Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0096LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
