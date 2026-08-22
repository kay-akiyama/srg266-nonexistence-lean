import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0002`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0002Mask : ℕ := 522871906410565

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0002Witness : Array ℤ :=
  #[26, 6, 24, -160, -13, -41, 88, 89, 14, 40, 27, 108, -69, -110, -53, -74,
  116, -75, -205, -111, -159, 111, 50, -12, -18, -55, -85, 74, 99, 114, 79,
  87, 35, -24, 38, 31, 53, -60, 50, 97, -152, -120, 0, -151, 17, 58, 51,
  -45, -101, -42, 34, -20, 71, 94, -22, 57, 89, -83, -7, -31, -11, -28, 29,
  26, -44, 76, -27, -92, -147, 82, 6, 56, 53, 75, -26, 28, 47, -102, -113,
  -46, 9, -17, 5, 44, 20, 44, 140, 116, 159, -12, -24, -18, -49, 43, 14, 16,
  -64, 13, -24, -33, -42, -4, 13, 76, 36, 59, -41, 20, -51, -49, -39, -63,
  -23, -116, 54, 62, 173, -13, -22, -29, 1, -42, 36, 21, 54, 30, -56, 2,
  -137, -37, 11, 97, -3, -37, -14, -83, -12, 99, 10, 0, -79, 22, 28, -131,
  72, -53, 66, -35, -88, -17, -12, 2, 2, -38, 89, 85, 137, -96, -49, -70,
  -96, -6, -4, -40, 0, 46, 1, -101]

theorem fractionalNearFrameSubtreeG5R0002_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0002Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0002Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0002Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0002_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0002LowerBoundTable : List ℤ :=
  [-106, -120, 2, -98, -116, -10, 90, 76, -21, -281, 9, 166, -156, 245, 148,
  -204, -110, 11, 9, -81, -179, 89, 85, 44, 220]

def fractionalNearFrameSubtreeG5R0002LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0002Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0002LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
