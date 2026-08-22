import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0078`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0078Mask : ℕ := 971447253308008

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0078Witness : Array ℤ :=
  #[79, 75, -14, -112, -181, 121, 122, 71, 37, 68, 35, 22, 89, -161, 98,
  127, 95, 55, -26, -5, -152, -18, -96, -164, 37, 132, 84, 93, 62, 19, 23,
  98, -69, -56, -4, -53, 29, -116, -88, 3, -58, 141, 71, 34, 25, 76, 48, 25,
  68, 74, -121, -46, -153, 35, -115, -82, -35, 23, -91, -23, 132, 33, -38,
  172, 157, -163, 26, 27, -20, 128, -90, 2, 21, -57, -115, 94, 55, 1, 168,
  -36, 3, 97, -21, 49, -3, 80, -43, -17, 52, -38, 89, 37, -46, 29, -57, 2,
  4, -50, 104, 131, 130, 72, 85, -18, -37, 150, 7, 21, -41, 103, -104, -132,
  93, -15, -33, -44, 81, -20, -120, 58, -26, -8, 187, 43, 46, 23, 4, -39,
  41, -89, 19, 77, 81, 156, 135, -24, -14, -61, 32, -44, 80, 126, 37, 69,
  82, -28, -54, 12, 19, 3, -140, -75, 33, 64, 206, -31, 27, -118, -77, -142,
  -50, 113, 85, 120, 9, 80, 45, 90]

theorem fractionalNearFrameSubtreeG2R0078_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0078Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0078Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0078Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0078_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0078LowerBoundTable : List ℤ :=
  [96, 199, 145, -27, 138, 262, 130, 44, 276, 441, 139, 9, 82, 278, 475,
  168, 131, 172, 95, 298, 9, 314, 592, 268, 503]

def fractionalNearFrameSubtreeG2R0078LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0078Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0078LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
