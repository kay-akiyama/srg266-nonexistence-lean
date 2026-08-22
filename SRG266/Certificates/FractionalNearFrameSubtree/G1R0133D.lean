import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0133`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0133Mask : ℕ := 1022433634847890

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0133Witness : Array ℤ :=
  #[70, 158, 42, -156, 52, -28, -75, -12, -6, -105, -64, 0, -89, 11, 37, 0,
  115, 128, 42, 50, 59, 51, 5, -54, 31, 29, -56, -1, 14, 133, 98, -196,
  -189, -111, -221, 236, 98, 34, 62, 0, 176, 35, 81, 20, -3, -142, 40, -51,
  -172, 128, 84, 110, 67, 57, 66, -28, -108, -67, -159, 2, 0, -108, 43, 223,
  74, -120, -95, -170, 128, 83, -50, 8, 61, 40, -50, -22, 3, -83, -41, 10,
  58, 60, 133, 143, -28, 37, 185, 49, 114, 36, 5, 60, 77, -9, -51, 43, -50,
  -18, 21, 88, 69, 84, 120, 77, 70, 29, 43, 3, -52, 52, -150, -91, -21, 113,
  135, -157, 82, 31, 33, 82, 36, 92, -40, -55, -238, -55, -136, -27, 24,
  124, -58, 174, -25, -29, -86, -51, -60, 64, 34, -3, 32, -163, 27, -14,
  -30, -58, -83, -51, -4, 83, -152, -12, 159, -2, 84, -59, 191, -14, -6,
  212, -61, 5, -110, 44, 32, -70, -94, 353]

theorem fractionalNearFrameSubtreeG1R0133_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0133Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0133Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0133Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0133_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0133LowerBoundTable : List ℤ :=
  [43, 2, 11, 96, 131, 193, 267, 108, 1, 286, 439, -108, -163, 19, -209,
  -95, 10, 498, 173, 10, 28, 555, 344, 308, 627]

def fractionalNearFrameSubtreeG1R0133LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0133Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0133LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
