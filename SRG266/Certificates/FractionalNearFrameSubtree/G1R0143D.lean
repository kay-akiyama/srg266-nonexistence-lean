import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0143`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0143Mask : ℕ := 1039467485383320

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0143Witness : Array ℤ :=
  #[0, 66, 167, 60, -114, -82, 10, -46, -32, 159, -66, 56, -23, -33, -127,
  197, -49, -106, -179, -83, 0, 30, 214, 192, 3, -74, 159, 184, -176, -193,
  -264, -49, -83, 212, 212, -40, 41, -10, 66, 154, 153, 224, 139, 211, 63,
  -7, -102, -55, -24, -112, 3, 77, 75, 0, 116, 30, 66, -33, -25, 31, -73,
  -231, 40, 134, -243, 45, -86, 78, 54, 25, 98, 85, -8, -1, 60, 5, -95, 201,
  -34, 132, -61, -57, 129, 141, 69, 40, 42, -161, 20, 167, 25, 98, 65, 65,
  140, 46, 177, -28, 34, 19, 146, 6, 121, 183, 178, 33, 54, 184, 67, 56, 96,
  165, 77, -113, -107, -18, -12, 107, 9, 0, 27, -13, 52, -66, -70, 55, 34,
  -12, 104, -45, -83, -106, -98, 71, 200, 20, -24, 22, -88, 196, 54, 217,
  -174, -95, -76, -18, -39, -97, 214, 41, -189, -66, 229, 28, -72, 72, 104,
  -52, 10, -26, -65, 134, -101, 113, -45, 64, -15, -291]

theorem fractionalNearFrameSubtreeG1R0143_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0143Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0143Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0143Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0143_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0143LowerBoundTable : List ℤ :=
  [142, 78, 360, 397, 3, 222, 227, -11, 253, 108, 285, -72, 314, 797, 644,
  9, 541, 633, 657, 321, 1055, 66, -97, 478, 279]

def fractionalNearFrameSubtreeG1R0143LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0143Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0143LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
