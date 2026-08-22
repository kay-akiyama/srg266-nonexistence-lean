import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0553`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0553Mask : ℕ := 6840700630667852

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0553Witness : Array ℤ :=
  #[-49, 231, -30, 49, 219, 193, 216, -181, -9, -18, 80, -312, 0, 69, -182,
  35, -110, 140, -5, 28, 93, 205, 71, 131, -31, 216, -138, 103, -85, -64,
  -39, -18, -33, 14, -4, 176, 93, 161, 318, -45, -87, 0, 88, 0, 50, 76, 54,
  190, -49, -120, 2, 60, 55, 3, -78, -99, 43, -9, 82, 40, 92, -68, -24, -8,
  27, 168, -54, 96, -91, 23, 61, -23, 141, 139, 31, -58, -39, -89, -53, -15,
  9, -17, 97, 121, -50, -76, 5, 60, 113, 19, 177, 10, 0, 14, 92, 12, -111,
  33, 105, 90, 15, -59, 44, 40, 10, -165, -127, 34, -127, 174, -9, 60, 2,
  -74, 137, 72, -91, 62, 60, -65, 5, -123, -27, 48, 152, -74, -50, 256, 179,
  147, 87, 71, -186, 5, 48, 159, 28, 177, -30, 221, 92, 19, 102, 56, 5, -18,
  -26, 187, -237, 63, 4, 18, 167, -212, 112, 145, 143, 25, 142, -65, -218,
  30, 27, 95, 205, 77, 14, 158]

theorem fractionalNearFrameSubtreeG2R0553_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0553Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0553Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0553Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0553_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0553LowerBoundTable : List ℤ :=
  [274, 454, 164, 248, 318, 578, 269, -44, 375, 1343, 322, 75, 720, -181,
  147, 399, 506, 10, 612, 10, 361, 933, 555, 1082, 248]

def fractionalNearFrameSubtreeG2R0553LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0553Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0553LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
