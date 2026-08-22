import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0009`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0009Mask : ℕ := 4737706040868995

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0009Witness : Array ℤ :=
  #[130, -37, -8, 1, -15, 89, 104, 65, -129, 12, 65, -79, -19, -56, -21, 0,
  -6, -57, -71, -89, -38, 0, -25, 0, 32, 52, 64, 42, -37, 36, 47, 29, 164,
  92, 0, 106, -31, -52, 16, -105, -35, 18, -29, -58, 60, 113, 3, 59, -14,
  27, 40, 22, -116, 59, -27, -130, 2, -27, -64, 4, 5, 14, -4, 133, -15, -72,
  -23, 89, -14, 46, -57, 6, 102, 57, 109, -33, 55, 32, -29, 24, 59, 78, 5,
  -37, -111, 48, 29, 28, 127, 48, 88, -59, -206, 5, -46, -52, 12, 15, 6, 49,
  -18, -108, 39, -136, -33, 4, -96, -90, -87, -66, -7, 124, 30, 63, 71, 11,
  22, -101, -18, 164, -27, -20, 87, -33, -8, -23, -90, 160, 77, -16, -108,
  80, -3, -37, 90, -13, -7, -37, 42, 62, 96, 130, 39, -61, -49, 43, -75,
  -133, 106, -24, -77, 96, -66, -28, 53, 81, -16, 108, 15, -31, 58, 45, 108,
  112, 194, 140, -50, -50]

theorem fractionalNearFrameSubtreeG4R0009_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0009Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0009Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0009Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0009_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0009LowerBoundTable : List ℤ :=
  [3, 143, 127, -5, 1, 2, 196, 3, 2, 209, 561, 241, 110, -301, 136, 143,
  368, 446, 9, -106, 168, 141, 255, 262, 359]

def fractionalNearFrameSubtreeG4R0009LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0009Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0009LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
