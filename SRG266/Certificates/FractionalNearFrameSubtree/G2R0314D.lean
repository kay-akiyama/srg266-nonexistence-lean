import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0314`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0314Mask : ℕ := 5389104454424084

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0314Witness : Array ℤ :=
  #[107, 132, 202, 127, 148, 7, -154, 38, 7, 59, -71, -129, 84, -59, 31,
  -151, 22, -47, -65, 144, -59, 55, -147, -11, 77, -39, 158, 139, 48, 242,
  -50, -7, 168, -68, 78, 3, -69, -3, 41, -203, 163, -51, 113, 50, -65, 13,
  20, 49, -16, -102, -6, -18, 54, -220, 21, -74, 19, 123, 2, 4, 95, 55, -12,
  -140, -20, -49, 2, -113, -48, -12, 51, 54, -46, -7, 21, -23, 86, -32, 67,
  42, -248, -244, -112, 62, -36, 15, 36, -44, 180, -25, -35, 90, -66, 100,
  21, -38, -19, 71, -94, -96, 23, -48, 65, 86, -8, 97, -108, 134, 115, -165,
  65, -91, -116, -115, 67, 97, 119, 120, 172, 117, 84, 100, 105, 13, 133,
  -77, 2, 44, 42, 37, -53, 16, 50, 71, -20, -74, 182, 11, -57, 110, -86,
  109, -88, -100, 69, 31, 78, 160, -18, 32, 77, 54, 36, 90, -242, -265, 58,
  -173, 48, -221, 237, -26, -266, -39, -74, -22, -163, -136]

theorem fractionalNearFrameSubtreeG2R0314_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0314Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0314Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0314Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0314_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0314LowerBoundTable : List ℤ :=
  [-7, 1, -480, 95, -29, 193, 211, 287, 223, 258, 187, 195, 81, -301, 11,
  107, -40, 140, 24, 9, 98, 187, 11, 316, 29]

def fractionalNearFrameSubtreeG2R0314LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0314Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0314LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
