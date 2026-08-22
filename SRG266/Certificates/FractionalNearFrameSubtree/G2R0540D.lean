import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0540`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0540Mask : ℕ := 6833354827305362

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0540Witness : Array ℤ :=
  #[39, 104, 46, 139, 56, 166, -102, 15, 1, -132, 20, -61, -77, 11, -25, 0,
  -65, 40, -37, 57, 27, 114, -85, 7, 50, 45, 1, -18, 29, 7, 34, -112, -80,
  2, 8, 175, 55, 35, 30, -4, 73, 137, 42, 33, 143, 27, 75, -124, -63, -100,
  137, 92, 102, -2, 37, -144, 53, 81, 27, 130, -53, 0, -42, -26, 46, 92, 29,
  28, -57, 89, 29, -48, 82, 129, -40, -20, 100, -46, 45, 111, -78, -25, 59,
  -102, -23, 12, -10, -69, 119, -2, 71, 47, 51, -13, 172, 64, -47, 10, -79,
  52, 76, 4, 55, 65, -4, -26, 0, -161, -53, 70, 44, 50, -84, -22, 21, 89,
  -177, 38, -21, 70, 13, -30, -123, -204, -115, 97, -24, -37, 108, 69, 37,
  74, -30, -105, -42, -129, 109, -117, 0, 21, -24, -43, 94, 131, 112, 96,
  -30, 23, -39, 78, -12, 5, 25, 47, -41, -34, -68, -114, 28, -111, -125, 74,
  -52, 5, -46, 0, -84, 7]

theorem fractionalNearFrameSubtreeG2R0540_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0540Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0540Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0540Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0540_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0540LowerBoundTable : List ℤ :=
  [-1, -194, 115, 207, 2, 181, 1, 182, 144, 3, 10, -9, 189, 9, 326, 173,
  486, 11, 205, 322, 18, 152, 129, 284, 306]

def fractionalNearFrameSubtreeG2R0540LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0540Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0540LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
