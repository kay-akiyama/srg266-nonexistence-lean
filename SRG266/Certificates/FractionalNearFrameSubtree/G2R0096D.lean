import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0096`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0096Mask : ℕ := 1240020082991201

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0096Witness : Array ℤ :=
  #[184, 0, 53, 32, 129, 98, -119, -55, -37, -98, 0, 36, 12, 85, -74, -22,
  -108, 15, 53, 44, 2, 29, -29, -32, 4, -5, -57, -60, 41, 15, 86, -69, -49,
  -6, -88, 8, 23, 148, -18, 119, 103, -74, 0, -92, 29, 55, -59, 78, 8, 42,
  -120, -6, -65, 77, 60, 0, -83, -36, -25, -27, -135, 53, 106, 23, 46, 88,
  -39, 32, 15, 13, 114, -43, -64, -56, 107, 20, -63, 29, -45, 103, -65, 75,
  -30, 25, 149, 6, -54, 81, -26, 139, 102, -46, -98, -86, 17, -1, -106, 66,
  113, 35, -70, -23, -22, -13, 28, -33, 38, -14, -57, -54, -96, -132, -91,
  59, 11, 100, -41, 19, -110, 150, -65, -39, -60, -100, 141, 97, 103, -95,
  -68, -48, 67, -8, -78, -89, -87, 26, 4, 101, 24, 39, 67, 58, -4, -11, 24,
  -35, -49, -83, 30, 47, 14, 9, -38, 31, -11, -61, -44, 37, 0, 55, 6, 49,
  -17, 60, 44, -17, 16, -26]

theorem fractionalNearFrameSubtreeG2R0096_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0096Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0096Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0096Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0096_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0096LowerBoundTable : List ℤ :=
  [-87, -55, -34, -51, 2, 145, 1, 51, 153, 133, 11, 188, -19, -98, -130, 8,
  35, 144, -181, 56, 192, -54, 129, 341, 342]

def fractionalNearFrameSubtreeG2R0096LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0096Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0096LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
