import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0018`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0018Mask : ℕ := 273604186198289

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0018Witness : Array ℤ :=
  #[-227, -581, 152, 0, -305, 202, 494, -160, 196, -74, 549, 269, 648, 0,
  -286, 11, 76, -815, 929, 6, 202, 6, -318, 78, -146, 379, -850, -129, 288,
  0, 97, 119, -42, 193, 14, 483, -130, 430, -814, -579, 258, -259, 25, -723,
  108, 693, -160, 265, 510, 167, -59, -502, -918, 1405, 121, -281, 82, -581,
  461, 336, 374, -175, 586, 37, 47, 46, 350, 384, -483, -332, 403, 888, 276,
  267, -185, 401, -130, -168, -50, 552, 62, -336, -659, 23, 38, 378, 45,
  166, 108, 1210, -517, 84, 175, 567, -99, 165, -218, 768, 365, -1071, -301,
  -52, 204, 1478, 116, 583, -291, 541, -859, -408, -301, -9, -364, -733,
  -709, -746, -739, -1470, 1358, 809, 675, -145, -275, -180, -118, 243, 123,
  275, 439, 274, -259, -149, 75, 295, -197, 158, -1236, 106, -248, 51, -100,
  -192, 286, 552, -161, 370, 407, -1, -277, 707, -71, -35, 332, -162, 1035,
  -264, -110, 37, -403, -357, -550, -253, -394, 2, -120, -141, -501, 455]

theorem fractionalNearFrameSubtreeG1R0018_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0018Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0018Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0018Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0018_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0018LowerBoundTable : List ℤ :=
  [-670, 33, 32, 33, -233, 34, -466, 105, 1689, -696, -929, -1217, 100, 292,
  1379, 1286, 2923, 1628, -141, 1745, 2098, 1995, 890, 1500, -675]

def fractionalNearFrameSubtreeG1R0018LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0018Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0018LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
