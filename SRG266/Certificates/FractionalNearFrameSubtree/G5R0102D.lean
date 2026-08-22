import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0102`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0102Mask : ℕ := 5542795540078808

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0102Witness : Array ℤ :=
  #[-12, -129, 10, -168, -123, 205, 134, 88, 165, 202, 137, 23, 67, -22,
  128, -13, 21, 89, 167, -55, -38, -4, -4, 2, -197, -78, 33, 85, 16, 208,
  21, -94, -6, 60, 13, 81, -25, 129, -110, 49, 0, -69, 0, -44, 19, -98, 77,
  -50, 61, 24, 100, 172, -252, -14, -6, 48, -23, 181, 181, -137, 34, -175,
  -109, -19, 27, 86, -88, -169, 41, 310, 162, -54, 54, -121, 42, -14, 30,
  -85, 257, 71, 33, 119, 192, 76, 50, 26, 57, 184, 89, 16, 151, 111, 44, 92,
  4, 157, -81, -28, -68, -127, 16, -30, -8, 26, -93, -35, 134, 53, 137, -78,
  148, -58, -3, 52, -147, 134, -41, 128, -104, 109, -39, -76, -168, 62, 40,
  46, -6, -60, -7, 72, 2, 30, 0, 0, -46, 180, 112, 79, -41, -112, -62, 56,
  -13, -20, -103, 124, 126, 137, 62, -38, -237, 7, 100, 197, -195, -16, -4,
  -59, 194, 30, -4, -154, -70, 30, -182, 23, 87, 14]

theorem fractionalNearFrameSubtreeG5R0102_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0102Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0102Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0102Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0102_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0102LowerBoundTable : List ℤ :=
  [120, -5, 147, 290, 343, -3, 148, 253, 290, 10, 10, 520, 136, 510, 350,
  137, 550, 11, 10, 796, 160, 145, -64, 956, 342]

def fractionalNearFrameSubtreeG5R0102LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0102Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0102LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
