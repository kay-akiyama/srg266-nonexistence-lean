import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0464`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0464Mask : ℕ := 5807438579537042

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0464Witness : Array ℤ :=
  #[50, -4, 52, 114, -51, 113, -52, -16, 43, -58, -32, 91, 44, 75, 65, -47,
  87, 32, 5, 97, 50, 13, 29, 21, -75, -42, -35, 29, -25, -29, 39, 65, 115,
  12, 19, -39, -25, 0, 83, -92, -16, -40, -12, -18, -25, -58, 24, 10, 50,
  -27, 57, 137, 32, -24, 150, 118, 10, -62, 15, 49, -50, 35, 40, 28, 84,
  121, 25, 96, 86, 115, -42, 30, 52, -86, 91, 21, -74, 13, -4, 37, 0, 51, 0,
  105, -32, 47, 39, 37, -6, 4, -81, 15, 19, 1, 81, -32, -96, 36, -83, -127,
  129, -27, 55, -63, 35, -15, 31, -2, -39, -78, 21, -128, 13, 63, -110, 15,
  -54, 46, -46, -29, -36, -44, -29, 49, -20, 85, -14, -30, 52, -4, 21, 50,
  52, 30, 89, 26, 42, -94, -44, -22, -1, 68, 6, 137, 42, 2, 59, 7, 39, 40,
  84, 79, -130, 69, -109, -92, -44, -68, -24, -4, -167, -60, 39, 43, 108, 3,
  33, 56]

theorem fractionalNearFrameSubtreeG2R0464_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0464Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0464Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0464Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0464_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0464LowerBoundTable : List ℤ :=
  [81, 18, 208, 299, 119, 23, 187, 240, 4, 70, 62, 353, -212, -13, 372, 501,
  -111, 56, 9, 300, 354, 8, 203, 353, 10]

def fractionalNearFrameSubtreeG2R0464LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0464Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0464LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
