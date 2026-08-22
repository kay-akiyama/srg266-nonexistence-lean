import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0389`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0389Mask : ℕ := 5739947614651018

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0389Witness : Array ℤ :=
  #[-36, -101, -62, -40, 10, 109, 99, 66, 22, 156, 36, -156, -57, -100, -95,
  -41, -9, 12, 27, -58, 109, 5, 26, -19, -73, -10, -24, -42, 48, 72, -75,
  -113, 76, 89, -100, 97, 8, -11, 17, -194, 17, 90, -144, 30, -65, 263, 50,
  -72, 217, 46, 89, 36, -32, 103, -3, -62, 181, 21, -11, -30, 98, -62, 10,
  30, 62, 29, -44, -57, -110, 97, -77, 47, -19, 27, -147, 60, -89, 26, -18,
  137, 64, 55, 70, -35, 179, 94, 55, 81, 57, 50, 149, -20, 35, 130, -51,
  -31, 34, -45, -20, 28, 58, -3, -57, 40, 71, 36, 50, 126, 70, 28, 79, -218,
  -130, -107, -29, -87, -85, 9, -62, -32, 222, 41, 0, 38, 31, 59, 36, -44,
  3, -17, -19, 29, -38, -1, 63, 67, -79, 24, -21, 118, -89, 8, 6, 64, -8, 0,
  -48, 45, 110, 158, -51, 3, -7, -41, -13, -42, 36, 28, 46, 81, -5, 64, 40,
  64, -1, 112, 77, 80]

theorem fractionalNearFrameSubtreeG2R0389_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0389Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0389Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0389Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0389_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0389LowerBoundTable : List ℤ :=
  [80, 182, 158, 16, 243, 374, 0, 44, 74, 476, 88, 16, 10, 327, 171, 73,
  401, 72, 160, -47, 8, 380, 774, 33, 536]

def fractionalNearFrameSubtreeG2R0389LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0389Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0389LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
