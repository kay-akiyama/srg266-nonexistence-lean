import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G1R0081`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0081Mask : ℕ := 899211274590753

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0081Witness : Array ℤ :=
  #[-33, 0, 7, 79, -3, 66, 123, 40, 80, 214, 62, 167, -178, -77, -146, -72,
  -115, -64, -113, -105, 1, -4, -44, -39, 83, 25, 142, 160, -47, 47, 37, 73,
  35, 68, 92, 22, 64, -97, -8, -87, 71, 41, 152, 45, -2, -20, 19, 61, 26,
  55, 14, 148, -15, 37, -29, -2, 1, 49, 0, 36, 34, -35, 45, -60, 59, -7,
  -107, -31, 55, 14, -2, -21, 40, 75, -36, 31, -10, 8, -17, -29, 72, 54, 25,
  39, -14, 54, 25, 3, -49, -18, 49, -14, 43, 46, -9, -54, 17, -3, 68, 11,
  -13, 32, 40, -19, -9, 2, 29, -32, 0, -13, 38, 56, -32, -10, 22, 30, 42,
  91, -22, -38, 48, 75, -11, 28, -2, 23, -28, 96, 12, -3, -15, 22, 50, -45,
  84, -29, -6, 6, -50, -4, -47, -87, -92, 93, 59, -3, 17, -33, -14, 11, 0,
  -53, -50, 15, 104, 63, 22, 53, 29, 81, 79, 12, 3, 33, 67, 14, 43, -91]

theorem fractionalNearFrameSubtreeG1R0081_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0081Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0081Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0081Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0081_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0081LowerBoundTable : List ℤ :=
  [149, 91, 239, 138, 224, 214, 194, -68, 180, 251, 187, 191, 136, 322, 122,
  -47, 274, 138, 279, 221, 209, 78, 10, 480, 81]

def fractionalNearFrameSubtreeG1R0081LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0081Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0081LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
