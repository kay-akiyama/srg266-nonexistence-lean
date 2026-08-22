import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0132`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0132Mask : ℕ := 6833383390612626

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0132Witness : Array ℤ :=
  #[-31, -5, 13, 35, 58, 34, -72, 38, -50, -64, -82, 114, 24, 6, 74, 109, 0,
  -14, -48, 95, -27, -10, 135, 148, 156, -68, -17, -41, -195, 154, -141, 21,
  18, 23, 50, 105, 105, 30, -3, 80, -97, 97, 18, -76, -45, -27, 38, -85,
  -42, -30, -22, 59, 89, 86, -58, 85, -13, -106, 47, 93, -80, -18, 63, 127,
  -3, 100, -39, 139, 58, 87, 36, 125, 88, -100, -51, 0, -31, 186, 81, 66,
  -69, -59, -60, 125, -93, -109, -21, -19, 22, -102, -12, 135, 40, 113,
  -201, -35, -81, 0, 87, 29, -7, 8, -19, 31, 34, -24, 96, 65, 31, -54, 67,
  -57, 80, 63, 153, -80, -26, 85, 17, -156, -42, -56, -15, 99, -13, -129,
  31, -33, 0, 258, 66, 40, -84, -64, 41, 13, -70, 91, -22, -12, 156, -10,
  -43, 90, 149, 144, -38, 87, -64, 56, 33, 106, -44, -70, 113, -131, -35,
  -88, -5, 141, 18, -58, -111, -29, 123, -14, 49, -106]

theorem fractionalNearFrameSubtreeG3R0132_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0132Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0132Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0132Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0132_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0132LowerBoundTable : List ℤ :=
  [77, 161, -36, 247, 94, 36, 172, 43, 152, 406, 103, 11, 301, -96, 179,
  275, -226, 477, 473, 298, 781, -141, 327, -36, 597]

def fractionalNearFrameSubtreeG3R0132LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0132Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0132LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
