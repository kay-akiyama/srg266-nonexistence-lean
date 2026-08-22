import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0029`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0029Mask : ℕ := 954016777306314

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0029Witness : Array ℤ :=
  #[89, 35, -67, -28, 51, 94, -26, -89, 21, 0, 13, -119, -128, -99, 37, 67,
  26, 86, 19, -65, 2, 12, 2, -36, -49, -47, 46, 81, 66, -111, -7, -118, -43,
  113, 78, 7, -3, -135, -148, 50, 11, 15, -120, 49, 70, -75, 59, 62, -38,
  -71, 74, 129, -95, -92, -81, 83, 5, -79, 69, 118, 110, 25, 93, -64, -22,
  16, 80, -8, -177, 138, 19, -33, 113, 250, 142, 20, -9, 57, 44, 87, 69, 76,
  71, 19, 2, -60, -17, 137, 65, 172, -55, -23, -19, 70, -66, 87, -40, -75,
  -80, -39, -14, 170, -62, 66, -53, 18, 40, -14, 23, -11, 15, -8, 32, -85,
  -54, -49, -24, 34, 59, 3, -67, -55, -12, -98, -92, 88, 152, 81, -14, -48,
  -120, -144, 97, 164, -63, 42, -46, 100, 23, -120, -16, 68, 20, 66, -67,
  44, -62, -60, 150, -92, 60, -119, 0, -42, 72, -49, 46, -17, 58, -25, -17,
  -156, 59, -31, -68, -98, 95, 249]

theorem fractionalNearFrameSubtreeG3R0029_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0029Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0029Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0029Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0029_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0029LowerBoundTable : List ℤ :=
  [-85, -44, 48, 110, 38, 2, 83, 35, 35, -25, 159, 10, 113, -53, 257, 9,
  -35, 391, 172, 10, 213, 497, 441, 207, 97]

def fractionalNearFrameSubtreeG3R0029LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0029Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0029LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
