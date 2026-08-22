import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0112`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0112Mask : ℕ := 5385255726518930

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0112Witness : Array ℤ :=
  #[119, 28, 103, -75, -101, -4, 71, 49, -96, 72, 24, 46, 53, -63, 25, -58,
  12, -136, -20, -85, -180, -84, -14, -50, -86, 15, 214, 236, 78, 11, 124,
  -15, -13, 37, 1, 29, 35, -185, 32, -94, -187, -43, -27, 2, -36, -88, -55,
  93, 56, 11, 34, 45, -71, -78, -110, -44, -36, 53, 103, -94, 155, 28, 128,
  113, 177, 62, 38, 27, 26, 75, -9, -30, -15, -79, 20, 22, -54, 97, -9, 69,
  57, -58, 115, -10, 77, 12, 29, -5, -20, 135, 178, 145, 176, 81, 102, -20,
  53, -41, 109, -75, 95, -8, 31, 0, -113, -68, 57, -109, 155, -3, 19, 50,
  -56, 17, -54, -10, -11, -20, -68, 77, 68, 31, 21, -25, 172, 28, -79, -34,
  103, 92, 34, 62, 190, 74, 42, -35, 60, -5, 148, -75, 128, -16, 48, 12, 57,
  66, 116, 27, -20, 69, 30, 42, -159, -61, -18, -177, 116, -72, 62, 52, -96,
  -95, 31, -88, 48, -5, 168, 0]

theorem fractionalNearFrameSubtreeG3R0112_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0112Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0112Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0112Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0112_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0112LowerBoundTable : List ℤ :=
  [121, 210, 105, 384, 81, 110, 2, 321, 71, 136, 3, 284, 10, 190, 375, 828,
  38, 186, -95, 326, 310, 10, 294, 238, 623]

def fractionalNearFrameSubtreeG3R0112LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0112Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0112LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
