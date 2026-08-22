import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0002`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0002Mask : ℕ := 521902451761283

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0002Witness : Array ℤ :=
  #[7, -28, 18, -61, -124, -38, 84, 47, -7, -56, -9, 19, 41, -11, -32, 65,
  51, -33, 9, -7, -100, 55, 64, -16, 34, -18, 37, -6, 0, -55, 46, -28, -25,
  50, -28, -13, 7, 0, 7, 0, 5, -37, 25, -6, -25, -30, -50, -19, -47, -75,
  67, -7, 41, 87, 73, -26, -80, 0, 65, -22, -28, -7, 30, 10, 27, 85, 63, 53,
  6, -68, -26, -2, 37, 14, 28, 9, 13, 51, 7, -45, -18, -9, -3, -31, 41, 6,
  23, 109, -3, 19, -6, 33, 29, 39, -13, 46, 62, 111, 108, -29, -6, 0, 46,
  23, -9, -8, -21, 2, 14, -24, -87, -62, 6, -91, -51, 23, 1, 23, 55, 61, 4,
  -5, -39, -97, -78, 68, 43, -11, -26, 9, -14, -37, -11, 24, -43, -20, -23,
  -5, -33, 3, -37, -23, -23, -2, 2, -67, 29, 21, 39, -57, -26, -125, -22,
  60, 8, 47, -53, -14, -19, -89, 4, 85, 6, -34, 57, -10, 43, 11]

theorem fractionalNearFrameSubtreeG4R0002_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0002Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0002Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0002Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0002_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0002LowerBoundTable : List ℤ :=
  [-74, -117, 17, 41, -5, -6, 1, 40, 1, -25, -146, 236, -238, 341, 299, -63,
  127, 78, 165, 49, -241, -45, 129, -86, 151]

def fractionalNearFrameSubtreeG4R0002LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0002Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0002LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
