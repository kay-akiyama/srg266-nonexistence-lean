import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0045`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0045Mask : ℕ := 4746235570937993

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0045Witness : Array ℤ :=
  #[-261, -317, 370, 114, -194, -387, -120, 0, 515, 273, 342, -233, 0, -500,
  142, -562, 207, -118, -221, -55, -704, -392, -77, -254, -39, 949, 472,
  790, 94, 177, -138, 65, -253, -390, -301, -795, 356, -103, 115, 296, -289,
  9, -88, -258, 501, 449, -33, -95, 268, 88, -458, 468, -11, 180, 681, -289,
  -215, -318, -201, -87, -384, -443, 289, -1236, 165, -180, 500, 488, 769,
  -154, 59, -532, 326, 499, 58, 358, -54, -114, 782, -723, -571, 385, -21,
  349, 571, 453, -209, -144, -180, -671, -498, 590, 422, -108, 156, 420, 59,
  78, 391, -568, 83, 246, 21, 583, 219, 469, 508, 226, -147, -319, -57, 228,
  -645, 16, 321, 542, 1102, 276, -860, 299, -162, -1309, 102, 765, -25, 416,
  -392, -41, 238, 615, 694, 28, 35, 188, -333, -448, -401, -1350, -242, 132,
  285, 955, 268, -651, -131, 129, 47, 116, -151, 1, 385, 379, -108, 93,
  -547, 42, -701, 202, -252, -175, -451, 607, 651, 550, -42, -73, 510, -254]

theorem fractionalNearFrameSubtreeG5R0045_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0045Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0045Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0045Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0045_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0045LowerBoundTable : List ℤ :=
  [-580, 31, 295, 73, 663, 32, 267, 78, -110, 100, 1612, 413, 2124, 1361,
  101, 1316, -895, 1737, -70, 249, 1139, 1731, -56, 521, 481]

def fractionalNearFrameSubtreeG5R0045LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0045Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0045LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
