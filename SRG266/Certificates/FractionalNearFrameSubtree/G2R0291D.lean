import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0291`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0291Mask : ℕ := 5385256165938706

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0291Witness : Array ℤ :=
  #[-29, 20, 40, 119, 7, 47, 76, 52, 121, -9, -5, -71, -94, -52, 29, -69,
  22, 14, -1, 6, 14, 35, 21, -37, 84, -38, 5, 24, -78, 17, 10, -9, -41, 46,
  0, -105, 3, 51, 47, -34, -54, -31, 82, 26, -25, 16, 46, -27, 14, 73, 43,
  49, -30, -77, -145, 152, 63, -91, -15, -114, 37, 16, -41, 6, 122, -39,
  -16, 44, 56, 47, 19, -26, 45, 31, 135, -108, 18, -176, 6, -65, -24, 26, 0,
  -28, -29, 77, 139, 51, -149, 45, -53, 14, 39, 4, -30, -64, 21, -55, 68,
  36, -211, 94, 27, -43, 67, -63, -40, 22, 49, -27, 27, -65, 96, -50, 46,
  181, -62, -3, -38, -15, -42, 35, -56, 43, -27, 14, 102, 158, -51, 45, 7,
  -19, 21, 22, -46, -57, -21, -11, 1, 114, -124, 138, 65, 63, -15, -33, -49,
  63, 43, -167, 43, 7, 36, 57, -22, -51, 81, 85, -70, 0, -62, 11, 128, -141,
  12, 40, 120, 71]

theorem fractionalNearFrameSubtreeG2R0291_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0291Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0291Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0291Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0291_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0291LowerBoundTable : List ℤ :=
  [-32, 64, 104, 136, 51, -6, 2, 76, 26, 46, 170, 345, 10, 94, 83, -149,
  111, 186, 135, 469, 256, 162, -115, 14, -30]

def fractionalNearFrameSubtreeG2R0291LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0291Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0291LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
