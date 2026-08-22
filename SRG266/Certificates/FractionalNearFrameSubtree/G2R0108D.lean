import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0108`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0108Mask : ℕ := 1284010138835985

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0108Witness : Array ℤ :=
  #[0, 159, 154, 147, -9, -28, -3, 24, 75, -52, 104, -195, 25, 1, -20, -41,
  -18, -121, -96, -26, 47, 55, 17, 25, 11, 43, 76, -14, -22, -47, 35, 150,
  118, 132, 139, -56, 0, -21, 188, -43, 94, -14, -68, -136, 190, -31, 75,
  -70, -131, -7, -153, 128, 224, 63, 7, 236, 52, 128, -166, 39, -7, 33, -3,
  35, -21, 7, -11, -7, -103, 12, 44, 16, 86, -15, -68, -41, -268, -2, 2,
  -106, 102, 148, 175, 72, -151, 82, 230, -4, -110, 43, 15, -17, 31, 13,
  -59, 34, 4, 17, -6, 25, -41, 110, -127, -8, -53, 62, 48, 17, 46, 58, 19,
  -171, 3, 44, -2, 72, 92, 203, -4, -22, -51, -50, 37, 70, 44, 81, 98, 21,
  -23, 3, 133, 33, 24, 8, -38, -42, -75, 92, -25, 11, 9, -22, -63, -104,
  -62, -265, -23, -1, -7, 33, 0, 233, 41, 44, 33, 92, -20, 18, 100, 110,
  -100, -13, 86, -40, 5, 171, -63, -60]

theorem fractionalNearFrameSubtreeG2R0108_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0108Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0108Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0108Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0108_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0108LowerBoundTable : List ℤ :=
  [60, 61, 2, 206, 2, 2, 360, 194, 166, -298, 631, 196, 591, 314, 507, 594,
  376, 617, 102, 8, 10, 191, 15, -102, 597]

def fractionalNearFrameSubtreeG2R0108LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0108Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0108LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
