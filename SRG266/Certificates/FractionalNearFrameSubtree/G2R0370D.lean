import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0370`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0370Mask : ℕ := 5716127560281240

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0370Witness : Array ℤ :=
  #[-7, 46, 63, 77, 60, -10, -41, -77, -53, -52, 54, -33, -33, -8, 13, 56,
  -28, 46, 23, -62, 50, -71, 5, -54, 58, -9, 0, -30, 0, -33, -27, 11, -48,
  17, 71, -42, -33, -107, 43, 39, 17, 44, 14, 62, -64, -63, -33, 48, -53,
  24, -96, -17, 26, 77, -17, 62, 12, -24, 78, -91, -12, -30, 46, 24, 64, 94,
  70, -35, 99, 40, -42, -98, 12, -104, -19, 43, 63, -71, 32, 2, 6, -51, -7,
  -77, -50, -30, 32, -37, -7, -32, -27, 33, 23, 18, -41, 8, 12, -46, 33, 22,
  -40, 5, -7, 42, 40, 13, -4, -44, -11, -39, 46, 44, 32, -24, -27, 33, 6,
  -60, -3, 0, -39, -11, -104, 34, -18, -11, -61, -81, -61, 46, 35, 85, -38,
  11, 94, 7, 12, 64, -32, 82, -16, 0, 18, 29, -15, 43, -12, 32, 9, 49, 24,
  35, -34, -86, 84, 42, -22, 19, -58, -5, -39, -39, -48, 2, 4, 8, -12, 7]

theorem fractionalNearFrameSubtreeG2R0370_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0370Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0370Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0370Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0370_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0370LowerBoundTable : List ℤ :=
  [-88, -5, 2, 69, -111, 2, -22, -85, -49, 183, 206, -239, 69, -112, 48, 34,
  74, -1, 86, 30, 44, 143, -22, 11, 149]

def fractionalNearFrameSubtreeG2R0370LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0370Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0370LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
