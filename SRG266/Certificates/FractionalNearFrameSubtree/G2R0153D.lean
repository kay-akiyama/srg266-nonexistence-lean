import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0153`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0153Mask : ℕ := 1378133155890314

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0153Witness : Array ℤ :=
  #[1, 82, -44, 18, 7, 49, 190, 62, 212, 165, 150, -102, -57, -182, -88,
  -165, 5, 8, 39, -1, 23, -15, 25, -23, -117, 62, 167, 138, 159, 114, -31,
  -16, 45, -28, 80, 5, 29, 1, 92, -65, -21, 80, -41, -126, -160, 178, 98,
  89, -42, 102, 95, 47, 43, 105, 34, -20, -27, 162, -182, -22, 79, -14, -58,
  -5, 31, -1, 42, -30, -11, -29, -24, 3, 153, 106, -24, 0, -59, 34, 99, -50,
  -29, -22, -10, -47, 128, -60, 42, 8, 135, -54, 135, -7, 30, -26, 14, 61,
  -28, -21, -1, -68, 4, -115, 26, -55, 92, 17, 102, 5, -23, 96, -106, -25,
  -60, 86, 241, 12, -31, 28, -131, -97, -66, 103, -27, -38, 27, 74, -80,
  -32, -12, 70, -66, 31, 103, -61, 167, -35, -50, -102, 42, -100, -20, 4, 0,
  27, -2, -84, -16, 97, 25, 87, 69, 53, -99, -18, -10, -39, -61, -29, -62,
  11, -40, 28, 18, 60, 96, -99, 27, 7]

theorem fractionalNearFrameSubtreeG2R0153_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0153Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0153Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0153Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0153_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0153LowerBoundTable : List ℤ :=
  [64, 9, -38, -14, 104, 279, 146, 221, 121, 204, 91, 108, -304, 291, -103,
  154, 299, 65, 192, -87, 9, 463, 259, 466, 992]

def fractionalNearFrameSubtreeG2R0153LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0153Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0153LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
