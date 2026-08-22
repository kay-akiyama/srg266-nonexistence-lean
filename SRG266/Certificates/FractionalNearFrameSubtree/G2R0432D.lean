import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0432`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0432Mask : ℕ := 5785203527300620

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0432Witness : Array ℤ :=
  #[25, -83, -161, 0, 1, -26, 97, 92, 3, 33, 170, -86, 78, 63, -6, 113, 51,
  -94, 40, 102, 13, 16, 84, -53, 99, -21, 89, 210, -22, -20, 118, 78, -5,
  -10, -114, -194, 109, 150, 165, -106, -53, -105, -9, 18, 77, -82, -91, 75,
  52, -3, 42, 34, -34, 164, 37, 55, -59, -198, 224, -113, -38, 124, 410,
  -136, 172, -79, -17, 247, -105, 166, 12, -104, 3, 154, 45, -59, 37, -107,
  51, 19, 2, 65, -32, 192, 191, -42, 37, 50, -49, 45, -28, -84, -73, 130,
  72, 164, 177, -90, -22, 67, -13, -94, -59, 97, 86, 118, 162, 117, -20,
  -39, -106, -242, -121, 176, -45, 37, 48, -29, 88, 13, 117, -173, -28, -4,
  58, 155, -18, -11, -195, 12, -39, -82, 54, 73, 182, 79, 84, 21, 99, 171,
  -63, -16, -85, 96, 8, -26, 8, 55, -83, 36, 100, 86, 0, -93, -28, -86,
  -103, 56, 19, -123, -270, 95, 40, 171, -42, 19, 1, -8]

theorem fractionalNearFrameSubtreeG2R0432_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0432Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0432Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0432Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0432_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0432LowerBoundTable : List ℤ :=
  [99, 2, 343, 353, 258, 248, 184, 1, 253, 147, 433, 53, -105, 566, 164,
  273, 488, 641, 589, 365, 120, -97, 639, 10, -26]

def fractionalNearFrameSubtreeG2R0432LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0432Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0432LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
