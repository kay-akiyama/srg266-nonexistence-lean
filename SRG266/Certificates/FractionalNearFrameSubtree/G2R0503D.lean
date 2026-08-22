import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0503`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0503Mask : ℕ := 5811567915553572

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0503Witness : Array ℤ :=
  #[-187, -35, -70, -5, -69, -40, -41, -33, 94, -7, 11, 4, 61, 192, 93, 46,
  -33, 90, 55, 24, 39, -10, -24, -57, 101, -10, -14, -12, -40, -42, -34,
  -129, -104, 60, 34, 33, 0, 80, 44, 73, 101, 85, 23, 26, 73, 98, -56, 39,
  24, -54, 42, 38, -121, 63, 43, -56, 9, -24, -77, 26, 55, 141, -24, -52,
  -74, 113, 90, 85, 47, 7, 4, -40, 26, -104, 13, -105, -39, 67, 37, 47, 21,
  33, 34, -63, -68, -110, 16, 35, 40, 14, 31, 3, -16, -51, 1, 21, -12, 90,
  18, -48, 26, -55, 54, 44, -15, -82, -11, -36, 30, 48, 39, 18, -16, -37,
  -84, -41, 23, 14, 33, 70, -18, -38, -62, -5, -26, 19, 73, 35, -42, 88, -3,
  -86, -102, -65, -5, -52, -26, 57, 88, 56, -163, 85, 10, 14, -36, 13, -21,
  -41, 32, 0, -74, 74, 53, 8, 31, 46, 19, 48, -58, -5, -23, -27, -55, 2, 3,
  -33, 54, -5]

theorem fractionalNearFrameSubtreeG2R0503_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0503Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0503Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0503Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0503_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0503LowerBoundTable : List ℤ :=
  [-23, 2, 25, 176, 2, 19, 86, 9, 5, -103, -256, 78, 53, -81, 196, -168,
  382, 156, 100, 184, 232, 140, -173, 167, 146]

def fractionalNearFrameSubtreeG2R0503LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0503Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0503LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
