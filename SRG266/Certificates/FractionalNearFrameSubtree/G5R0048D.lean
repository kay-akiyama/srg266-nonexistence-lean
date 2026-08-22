import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0048`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0048Mask : ℕ := 4876257134878979

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0048Witness : Array ℤ :=
  #[-31, -14, -51, -42, -22, -63, 97, 29, -27, 49, 72, 5, -46, 59, -51, -18,
  76, 30, -39, -121, 65, -94, -129, -36, 0, -81, -13, 118, 94, 21, 75, 60,
  39, 56, 106, -23, 35, -38, -178, -31, -9, 126, -40, -69, -76, 73, -111,
  49, -33, 44, -30, 5, -43, 46, 72, 40, -51, -28, 12, -18, 9, -6, -10, -107,
  20, -65, -12, 25, 28, -49, 31, -11, -13, -29, -9, 47, 65, -89, 63, 38, 72,
  -17, 81, -114, 157, 38, -59, -84, 39, 7, 65, -63, -46, 56, -22, -1, 17, 9,
  53, 102, 65, 36, -50, -68, -25, -85, 0, -24, 21, 63, 60, -15, -37, 77, 47,
  -12, -49, -51, -59, 23, -12, 111, -60, 40, -35, 100, -128, -26, 0, 8, 29,
  66, 34, 50, 96, 33, -26, -61, 33, -48, 97, 7, 66, 0, -52, 76, -29, 27,
  157, -38, -19, 37, -31, 66, -50, 6, 72, 181, -81, 47, -102, 0, -45, 0, 19,
  -57, 12, 38]

theorem fractionalNearFrameSubtreeG5R0048_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0048Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0048Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0048Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0048_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0048LowerBoundTable : List ℤ :=
  [-30, 126, 71, -5, 1, -17, 53, 1, 13, -17, 366, -217, 7, 90, 317, 295, 4,
  124, -67, 165, -259, 167, 90, 333, 93]

def fractionalNearFrameSubtreeG5R0048LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0048Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0048LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
