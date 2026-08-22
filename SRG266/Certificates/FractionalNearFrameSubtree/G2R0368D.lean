import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0368`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0368Mask : ℕ := 5716125683387480

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0368Witness : Array ℤ :=
  #[-14, 58, 81, 18, -43, 57, -63, 14, -8, 22, -36, -68, 41, 50, -13, 0, 15,
  31, 119, 78, -95, 44, -66, -9, -82, 56, 40, 38, 83, 97, 151, 113, -88,
  -85, -23, 15, 98, -68, 31, -134, 86, 0, 25, -11, 27, 0, 7, 12, -71, 42,
  109, -81, 4, 5, 54, 85, 0, -21, 44, 35, 39, 49, -27, 87, -26, -112, 166,
  -9, 12, 65, 63, -1, 13, -57, -3, 76, 37, -15, 95, -28, 47, 11, -23, 80,
  75, 96, 22, -9, -57, -41, 54, -103, -69, -129, -123, 23, -32, 1, 14, 49,
  58, 3, 24, 0, -90, 60, -65, -76, -16, 36, -31, 53, 71, 124, -186, -40, 0,
  -76, 14, 7, 51, 82, 0, 142, 16, 33, -25, -112, 19, -66, 10, -30, 14, 57,
  14, 116, -11, 66, 31, 4, 92, 11, 137, 94, 0, 32, -70, 22, -34, 42, 87,
  -11, 60, 185, 19, -70, -33, -55, -18, 8, 52, 46, 20, -30, -27, -116, 27,
  -20]

theorem fractionalNearFrameSubtreeG2R0368_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0368Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0368Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0368Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0368_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0368LowerBoundTable : List ℤ :=
  [69, 102, 55, 210, 116, -24, 160, 137, 177, 11, 384, 265, 176, -151, 320,
  144, 128, 9, 197, 138, 424, 169, 246, 61, 229]

def fractionalNearFrameSubtreeG2R0368LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0368Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0368LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
