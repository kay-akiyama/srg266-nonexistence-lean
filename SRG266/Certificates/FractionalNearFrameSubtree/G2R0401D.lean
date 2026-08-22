import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0401`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0401Mask : ℕ := 5741390692162216

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0401Witness : Array ℤ :=
  #[8, -16, 112, -6, -160, -18, 0, 4, 36, -8, 80, 231, 68, -5, 57, 88, 58,
  150, 55, 34, -13, 63, 36, -33, -5, -155, -73, -50, -56, -56, -65, -58,
  -13, 88, 58, -68, -112, 78, 27, 144, -64, -29, -73, 28, 63, -12, 4, 15,
  -18, 55, 102, 24, 9, -42, 34, -6, 32, -39, 15, -102, -64, -20, -14, 169,
  45, -13, -18, 91, -59, 169, 102, 114, -76, -5, -64, 25, -34, -52, -30,
  -62, 22, 36, 107, -22, 28, -58, 52, 52, 133, 31, 42, -110, -39, 146, 86,
  3, 109, -43, 64, -4, 80, 104, 81, 16, 1, -14, -63, -21, -36, 4, 62, -16,
  172, 57, 23, 59, 0, 81, 13, 144, 136, 7, -79, -61, -15, 72, -91, -73, 141,
  -35, -6, 1, 18, -126, -19, -17, 104, -6, -43, -57, -41, -136, 112, -20,
  31, -26, 38, -89, 75, 59, 76, 107, 84, -30, 111, -141, 14, 5, -54, -90,
  51, -120, -26, -192, 30, -1, -6, -79]

theorem fractionalNearFrameSubtreeG2R0401_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0401Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0401Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0401Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0401_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0401LowerBoundTable : List ℤ :=
  [54, -60, -48, 218, 112, 220, 3, 44, 106, 408, 341, -52, -17, 236, 283,
  -251, -231, -66, 635, 602, 279, 310, 305, 357, 179]

def fractionalNearFrameSubtreeG2R0401LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0401Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0401LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
