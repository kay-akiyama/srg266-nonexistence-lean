import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0120`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0120Mask : ℕ := 969518362247400

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0120Witness : Array ℤ :=
  #[-26, -40, -3, -167, -70, -28, -71, -19, -12, 22, 146, 185, 44, 50, 50,
  -57, 38, -84, 9, 40, 41, -11, 65, 77, -91, 49, 4, -60, 4, 50, 37, -11,
  -88, 61, -50, 26, -24, -31, 97, 0, -65, 130, -168, 38, 32, 125, 214, -157,
  -32, -69, 129, 87, 130, 247, -66, -91, -1, -48, -32, -48, -10, 31, 128,
  -22, 72, 98, -23, 52, 2, 18, -29, -34, 2, 11, 39, 30, -32, 39, -42, 27,
  -65, 234, 100, 138, 8, 69, -46, 21, 6, 62, 5, -38, 28, 61, 43, -28, -29,
  -9, 43, -29, 61, 45, 48, 69, 112, 62, -32, 71, 50, 80, 27, -38, 71, -15,
  59, 34, 70, 68, -72, 116, 77, -19, -60, 119, 82, 116, -105, 66, 19, 36,
  58, -38, -57, -72, -15, 110, 13, 8, 58, 58, -84, 8, -36, 82, 61, -8, 71,
  -8, -83, 56, 101, -22, 42, -183, 19, 60, -65, -17, 75, 156, 19, 69, -12,
  -3, 20, 43, -46, -5]

theorem fractionalNearFrameSubtreeG1R0120_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0120Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0120Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0120Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0120_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0120LowerBoundTable : List ℤ :=
  [189, 158, 317, 55, 357, 153, 259, 1, 194, 191, 384, 390, 336, 412, 689,
  40, 526, 10, -32, 237, -263, 262, 412, 441, 394]

def fractionalNearFrameSubtreeG1R0120LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0120Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0120LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
