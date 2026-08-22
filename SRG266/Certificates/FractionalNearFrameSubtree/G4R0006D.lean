import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G4R0006`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0006Mask : ℕ := 944046197154051

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0006Witness : Array ℤ :=
  #[100, -52, -26, -108, -34, -8, 21, -26, -41, 15, -1, 12, 28, -37, 61, 48,
  6, -77, -42, -97, -74, -50, 110, 62, -4, 20, 52, 77, -16, -24, 15, -18,
  12, 6, -57, -58, 45, 4, 165, 17, -64, -121, -19, 117, -66, 88, 58, -19,
  59, -42, -38, -21, -66, 62, -94, -43, -24, -21, -97, 9, 87, 18, -35, 86,
  -22, -11, 12, 11, -5, -25, 9, -136, 50, 33, 59, 119, 18, 2, -40, 62, 144,
  74, -76, 5, 142, 56, 4, -16, -37, 120, 16, 22, 53, -25, 80, 47, -94, -38,
  -39, -14, 71, 53, -33, 18, -44, 55, 21, -69, -64, -114, 59, -21, 24, 80,
  -55, -38, 7, -23, -11, -67, 10, -68, 17, 65, 20, -11, -40, 70, 53, -9,
  -25, 64, -129, -4, -56, 44, -31, -83, -46, -81, 13, 43, -11, -47, -96, 1,
  123, -79, -124, 67, -9, -63, 62, -45, 156, 3, 22, -50, 15, 36, 46, 54, 41,
  -30, 23, 14, -156, 66]

theorem fractionalNearFrameSubtreeG4R0006_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0006Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0006Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0006Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0006_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0006LowerBoundTable : List ℤ :=
  [-106, -79, 40, 3, 5, -118, 46, 9, 2, -78, 60, 10, -290, 366, 237, -109,
  229, 201, 72, 17, 10, 10, 253, 73, 10]

def fractionalNearFrameSubtreeG4R0006LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0006Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0006LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
