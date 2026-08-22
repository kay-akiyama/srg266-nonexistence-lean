import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0140`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0140Mask : ℕ := 1039411650417428

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0140Witness : Array ℤ :=
  #[203, 92, 289, 174, -81, -125, -60, -45, -108, 54, -168, -17, -14, -206,
  41, -80, 11, -143, -129, -121, 25, 7, 126, -56, 120, 21, 103, -15, 71, -3,
  -102, 13, 67, 140, 18, 16, 31, -110, 25, -53, -13, 65, -12, -56, -35, 25,
  172, 105, 81, 60, -112, 66, -147, -8, -124, -53, 59, 73, -99, 72, -108,
  -106, 0, 44, -6, 90, 61, 6, -27, -12, -46, -102, 30, -69, -162, 0, -104,
  198, 66, 3, 44, -47, 155, 19, 34, 32, -30, 76, 143, 60, -5, 134, -54, 31,
  100, 181, 110, 150, 161, 154, -24, 40, 12, 154, -191, -101, -182, -186,
  16, -53, 65, 183, -34, 162, 154, -25, -60, -52, 32, 65, 31, -87, -11,
  -228, -119, -59, -4, 73, 60, -120, 103, -177, 23, 31, -215, 106, -7, -9,
  28, 236, -35, -129, -169, 108, 13, 194, 82, -20, -117, -34, 35, -12, 31,
  254, 173, 124, 82, 102, 161, 104, -136, 9, -8, 191, -22, 15, -157, 266]

theorem fractionalNearFrameSubtreeG1R0140_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0140Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0140Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0140Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0140_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0140LowerBoundTable : List ℤ :=
  [-2, 169, 169, 58, 272, 26, 50, 83, -34, 641, -189, -201, -14, -168, 237,
  10, 372, 824, -305, 354, 613, 573, 399, 774, 128]

def fractionalNearFrameSubtreeG1R0140LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0140Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0140LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
