import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0329`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0329Mask : ℕ := 5402543147569832

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0329Witness : Array ℤ :=
  #[13, 27, -59, -36, 114, 54, -26, -84, 62, 242, 15, 118, -23, -55, 63, 89,
  40, -54, 0, 146, 41, -48, -31, 12, 86, 41, -6, 120, 42, 123, 67, 86, -23,
  -48, -8, -39, -95, -165, 140, 14, 80, 42, 91, 3, -35, 0, -52, 95, -29,
  -41, -173, -125, -23, 73, 56, -21, -32, 97, 35, 29, 155, -159, -53, -131,
  66, 115, -97, 117, -33, -132, 168, -85, 127, 102, 101, 76, 93, -21, -75,
  86, 61, 80, -25, 7, 91, -73, 60, -91, 35, 61, -63, -162, -94, -29, -12,
  -50, 79, 43, 164, -207, -118, -22, 149, 117, 66, 44, -178, -156, -23, 62,
  62, 135, -37, -67, 18, -94, 35, 15, 113, 178, 171, 12, 59, 73, -170, 7,
  78, 31, 146, 52, 18, -139, 26, 92, -19, -56, -3, -13, -38, -67, -5, -74,
  -37, -5, -42, 59, 30, 51, 58, 120, -15, -268, -259, 125, 80, 18, -15, -76,
  70, 128, 180, 174, 29, 159, 76, 85, -188, 67]

theorem fractionalNearFrameSubtreeG2R0329_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0329Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0329Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0329Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0329_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0329LowerBoundTable : List ℤ :=
  [87, 213, 151, -15, 14, 120, 242, 336, 132, 430, -64, 381, 547, 22, 407,
  400, 35, -45, -171, 42, 329, -72, 195, 389, 775]

def fractionalNearFrameSubtreeG2R0329LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0329Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0329LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
