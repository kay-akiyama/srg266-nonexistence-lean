import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0112`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0112Mask : ℕ := 1307847238337027

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0112Witness : Array ℤ :=
  #[37, 12, 18, 0, 71, -11, -68, 14, -75, 44, 126, 126, -200, -68, -55, -66,
  0, 26, 38, 123, 25, 32, 53, -24, -39, 69, 66, 199, 120, -152, -161, -177,
  -134, 19, 13, 47, 4, -28, 24, -111, 57, 82, -125, 53, 23, 88, 167, 9, 10,
  -28, 72, 36, 52, 11, -61, 16, 30, 92, -95, 58, -14, -38, -7, 66, -86, -40,
  -89, -84, -45, 31, 35, -15, 29, 29, -58, 41, -151, 57, 89, 46, 55, 39, 40,
  43, 60, -37, -29, 125, 129, -124, -21, 189, 81, 76, 27, 25, -9, 52, 43,
  12, 104, -3, 66, 74, 92, 89, 130, -103, -54, 77, 29, 0, 8, 137, -91, 161,
  20, -62, 70, 58, 14, -11, 65, 112, 115, 58, -103, -49, 38, 21, -49, -28,
  -14, 102, -26, -53, -41, 28, -61, 43, -6, -35, 7, 21, -88, -57, 60, -55,
  26, 22, 104, 17, -25, 201, 69, 21, 20, -23, 35, 208, -7, 119, -9, 54, 85,
  157, 143, -81]

theorem fractionalNearFrameSubtreeG2R0112_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0112Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0112Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0112Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0112_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0112LowerBoundTable : List ℤ :=
  [207, 366, 447, 68, 175, 350, 153, 21, 38, 542, 203, 276, 82, 335, 259,
  194, 343, 105, 347, 284, 147, 343, 10, 262, 11]

def fractionalNearFrameSubtreeG2R0112LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0112Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0112LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
