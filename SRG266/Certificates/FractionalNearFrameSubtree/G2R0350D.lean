import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0350`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0350Mask : ℕ := 5668932107621393

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0350Witness : Array ℤ :=
  #[18, 114, 0, 33, -33, -98, 25, 214, 168, 98, 295, 171, -155, -93, -94,
  -102, -185, -143, 6, -117, 23, -158, -48, -114, -234, -114, -153, 39, 235,
  151, 335, 391, 110, 129, 138, 33, 122, -176, -190, -178, 202, 114, 194,
  152, 90, -56, -165, 200, 13, -88, 114, 31, -47, 103, 157, -40, 145, 114,
  17, -12, 198, -38, -114, 28, 10, -66, -5, -41, 34, -80, -131, -46, -11,
  16, 70, 74, -8, -14, 55, 105, 7, 56, -87, 3, -157, -27, -72, -3, -12, -1,
  77, 46, 218, 116, 224, 43, -3, 107, 85, 101, 94, 59, 23, 96, 46, 38, 102,
  -76, -108, 24, 42, -3, -68, -87, 224, -166, -27, 5, 64, 60, -111, 12, 24,
  25, -102, -64, 57, 121, 205, -132, -286, 29, 11, -29, -38, 78, 2, -67,
  -69, 129, -8, 0, 85, 10, -8, 196, 69, -64, -54, -91, 26, 46, 85, 19, 19,
  -13, -45, 37, -28, -11, -101, 113, -9, 79, 15, 106, 100, -198]

theorem fractionalNearFrameSubtreeG2R0350_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0350Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0350Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0350Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0350_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0350LowerBoundTable : List ℤ :=
  [120, 3, 290, 2, 225, 550, 148, 344, 1, 268, 221, 267, -320, 923, 201,
  754, 186, 289, 233, 10, -426, 381, -45, 288, 844]

def fractionalNearFrameSubtreeG2R0350LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0350Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0350LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
