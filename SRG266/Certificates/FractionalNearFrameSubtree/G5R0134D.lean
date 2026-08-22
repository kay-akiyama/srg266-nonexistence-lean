import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0134`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0134Mask : ℕ := 6057673810084934

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0134Witness : Array ℤ :=
  #[110, 115, 71, 40, 75, 125, 14, -7, -34, 0, -27, -150, -45, -3, -55, -88,
  -66, -42, -192, 10, -79, 42, 142, 101, 4, 71, 82, -12, 81, 8, 0, 123, -95,
  2, -147, 59, -75, 86, 88, 66, 3, -54, 110, 81, -129, -60, -67, 33, 1,
  -107, -4, -106, 86, 26, 0, -122, 20, 18, -28, 76, 55, 57, 65, -50, 73,
  -26, -39, 42, 65, 53, 49, 49, 81, 81, -71, -34, -36, 48, -2, 72, 109, 95,
  -56, -13, 156, 123, 188, 42, -2, 27, 10, 24, -20, 42, -76, -58, 19, 93, 8,
  -5, 45, 16, 36, -21, 37, -64, -91, -37, -32, -8, 51, -43, 10, 35, 105,
  -55, -96, -3, -50, -90, -89, 77, -4, 1, -5, -58, -47, -61, 1, 199, -140,
  -64, 11, 106, 6, -56, 36, -18, 69, 29, 51, -79, -40, 8, 28, -78, 53, 19,
  12, 12, 55, -134, -1, -62, -143, -90, 9, -46, 4, 44, -27, 104, 34, -110,
  144, 54, 51, -10]

theorem fractionalNearFrameSubtreeG5R0134_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0134Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0134Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0134Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0134_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0134LowerBoundTable : List ℤ :=
  [-61, -76, -17, 247, 123, 2, 0, 53, 2, 163, -124, -218, -135, 436, 295,
  11, -120, 403, 175, 459, -18, 373, 48, 130, 561]

def fractionalNearFrameSubtreeG5R0134LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0134Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0134LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
