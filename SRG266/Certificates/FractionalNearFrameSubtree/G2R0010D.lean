import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0010`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0010Mask : ℕ := 268038846206097

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0010Witness : Array ℤ :=
  #[44, 22, -36, -12, -28, -14, -23, -10, 42, -49, 0, -15, 110, -7, -38, 15,
  -167, 0, 1, -16, -62, -18, -61, 84, -30, -83, -138, -18, 115, 118, 39,
  103, 36, -10, -98, -142, -16, 210, 104, -2, -74, -183, -135, 172, 106, 58,
  29, 177, -20, -131, -141, 0, 15, -97, -97, 147, -94, 27, 151, -99, -54,
  23, 13, 129, 18, 37, -16, -93, 156, 38, 71, 6, -2, -53, -3, 43, 5, 78,
  -51, 26, 7, -49, -51, 107, 5, -71, 0, 37, 33, 13, -37, -83, 4, -29, 49,
  -20, -29, 56, 4, -57, 85, 47, 4, 7, -19, 148, -90, -29, -34, -57, -22,
  -31, -65, -172, -99, 138, 186, -1, 0, -19, -1, 25, -40, 81, -59, -30, 13,
  137, 33, -66, 15, 45, 15, -10, -30, 73, -19, -36, 90, 67, 96, 77, -13, 39,
  39, 4, 48, -50, 89, -32, -36, -70, 4, -7, 32, 60, -134, -9, 76, 41, 80,
  39, 39, 5, 1, -37, 82, -104]

theorem fractionalNearFrameSubtreeG2R0010_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0010Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0010Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0010Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0010_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0010LowerBoundTable : List ℤ :=
  [-94, 91, -31, -78, -63, 2, 81, 2, 286, 31, 9, 214, 160, 34, -158, 132, 8,
  99, 76, 343, 503, 10, 32, 191, -68]

def fractionalNearFrameSubtreeG2R0010LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0010Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0010LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
