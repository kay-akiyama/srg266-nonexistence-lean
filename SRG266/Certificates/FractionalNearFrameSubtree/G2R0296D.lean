import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0296`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0296Mask : ℕ := 5387179243812116

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0296Witness : Array ℤ :=
  #[-87, -35, -100, 0, -75, 41, 91, 88, 80, 46, 39, 0, -23, 34, 45, -51, -8,
  -92, -21, -31, -31, 44, 71, 53, -38, -31, -12, -38, 98, 34, 45, 0, -54,
  -16, 27, 21, 8, 44, -60, 3, -61, 61, -7, 32, -8, -7, -45, 20, 53, 16, 9,
  70, 4, 58, -9, -2, -35, -19, 33, -26, 50, -2, -58, -40, -42, -36, 37, 19,
  58, -48, -132, 18, -58, -38, -75, -52, -29, -28, 29, 52, -17, -164, 54,
  -66, 77, 57, -64, 117, 63, 24, -56, -46, 134, 1, 56, -111, 116, 110, -24,
  -24, 14, -10, 59, -2, -33, -7, -29, 10, 29, 8, 1, -71, 55, -76, 9, 74, 30,
  47, 12, 44, 80, 64, 39, 123, -69, -33, -45, -46, 0, -71, -44, 41, -5, 43,
  -58, -26, -69, 100, 79, 37, 82, 31, 50, 30, 12, 8, 34, -10, 103, 30, -46,
  38, 43, -27, -21, 96, -39, -60, 164, -50, -18, 49, 0, -38, -96, 68, -15,
  -75]

theorem fractionalNearFrameSubtreeG2R0296_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0296Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0296Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0296Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0296_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0296LowerBoundTable : List ℤ :=
  [-54, 85, 8, 58, 72, -7, 134, -5, 2, 10, 301, 314, 178, 210, 11, -197,
  -138, 35, 84, -56, 305, 596, 103, -187, 31]

def fractionalNearFrameSubtreeG2R0296LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0296Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0296LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
