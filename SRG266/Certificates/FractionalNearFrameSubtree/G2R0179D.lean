import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0179`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0179Mask : ℕ := 1387735914496216

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0179Witness : Array ℤ :=
  #[126, -132, 123, -128, -175, 88, 24, 39, 13, -93, 233, 104, 150, 139,
  126, 14, 179, 28, 25, 114, -1, 75, -66, 57, -33, -102, -88, -58, 187, 50,
  15, -84, -24, 73, -6, -84, -64, -78, -106, 131, -10, -2, -67, -42, -54,
  115, 12, 97, 30, 91, -35, -24, -46, 37, 181, 64, -108, 0, 123, -120, -94,
  -51, -123, 102, 54, 12, -93, -271, 47, 21, 54, 9, 103, -44, 13, -23, 14,
  53, -82, 24, -1, 79, -33, 0, -22, 50, -129, -13, 131, -32, 128, -22, 81,
  -12, 25, 82, 60, 17, 53, 55, 1, 40, 31, -7, 78, 181, -39, -70, -39, 0,
  -30, -64, -30, -5, -76, 131, 4, 43, -29, 36, -154, 30, -37, 38, -51, 8,
  34, 117, -102, 88, -79, 30, 49, 12, 28, 68, 65, 48, 99, 40, 19, 169, 22,
  69, -136, 97, -114, 57, -5, 115, -158, -155, -7, -87, -95, -19, -162, -89,
  0, -35, 101, -82, 66, -76, 42, -8, -22, -24]

theorem fractionalNearFrameSubtreeG2R0179_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0179Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0179Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0179Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0179_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0179LowerBoundTable : List ℤ :=
  [8, 2, 2, -26, -55, 270, 184, 80, 77, 377, 232, -227, -108, 252, 10, -76,
  69, 152, 424, 139, 296, 191, 11, 162, 372]

def fractionalNearFrameSubtreeG2R0179LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0179Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0179LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
