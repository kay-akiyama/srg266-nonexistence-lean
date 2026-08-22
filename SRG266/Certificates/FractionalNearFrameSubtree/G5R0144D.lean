import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0144`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0144Mask : ℕ := 7060430386998305

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0144Witness : Array ℤ :=
  #[94, -29, -185, -39, -153, 20, 203, 34, 47, -35, 103, -75, -73, -49, -68,
  -14, -29, -133, -75, -72, -320, 203, 141, 152, 120, 20, 379, -101, 179,
  -192, -12, -52, -2, -27, -89, 203, -48, -6, -62, 17, -65, 65, 31, -239,
  -35, 52, 50, 66, 25, 4, -81, 50, -237, 68, -3, 14, 159, 26, -295, 58, 1,
  -127, -185, 214, -19, -15, 54, 36, 107, 14, 170, -32, 0, 130, -56, -45,
  -54, 10, 260, 24, -208, -208, -7, -247, 102, -146, -30, -161, 327, 278,
  -137, 170, 167, 116, -41, 95, -208, 117, 157, -43, -94, 50, -46, -90, 149,
  -38, -4, 102, -43, 346, 256, 11, -124, 119, -8, 35, -4, -128, 179, 192,
  -60, -178, 93, -45, 94, 35, 16, 17, -38, -66, 70, 20, 93, 145, -35, 100,
  228, 101, 134, 0, -28, -18, 414, 314, 95, 58, -86, 350, 93, 297, -6, -222,
  -2, 79, -4, 163, -209, -3, -300, 200, 3, 59, 64, 31, -64, 54, 0, 151]

theorem fractionalNearFrameSubtreeG5R0144_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0144Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0144Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0144Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0144_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0144LowerBoundTable : List ℤ :=
  [58, 654, 3, 388, 2, 38, 1, 407, 179, 451, 353, 803, 947, 420, -36, 252,
  845, -179, 162, 115, -195, 345, -433, 754, 433]

def fractionalNearFrameSubtreeG5R0144LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0144Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0144LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
