import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0085`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0085Mask : ℕ := 5471567696602386

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0085Witness : Array ℤ :=
  #[19, -74, 46, -22, -34, 11, 12, -33, 69, -43, 38, -14, -102, 38, 105, 12,
  -8, -3, 99, 9, -3, -30, 13, -56, 5, -41, 3, -21, 22, 38, 34, -19, -52, 91,
  54, -33, 66, 156, -24, 15, -12, -64, 51, 10, 11, -4, 47, 72, 8, 7, 22, 38,
  141, 15, 86, 58, -12, 24, -85, -88, -86, 52, -13, 28, 117, -16, -82, 1,
  -28, 49, -4, -40, -166, 42, -62, -45, -21, 61, 83, 82, 7, -70, 37, -39,
  -11, 3, -27, -42, 61, 0, 118, -37, 39, -69, 59, 16, 128, 41, 33, -45, -67,
  -14, -52, 17, 84, -94, -14, 86, 39, 56, -29, 61, 76, 49, -22, -61, -102,
  -15, 48, 10, 107, 21, 144, 0, -40, -14, -53, 53, -92, -138, 77, 64, -35,
  -29, -16, 56, -53, -89, 53, -7, -58, 77, 60, -35, 54, 26, -32, 17, -45,
  -19, 0, -29, -74, -63, 27, 119, -110, -21, 24, -54, -32, -7, -57, 84, -8,
  4, 39, -74]

theorem fractionalNearFrameSubtreeG5R0085_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0085Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0085Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0085Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0085_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0085LowerBoundTable : List ℤ :=
  [-13, -24, 153, 1, 1, 86, 76, -5, 86, 198, -99, -100, -53, 72, 10, 208,
  347, -62, 54, 295, 70, 9, -119, 341, 65]

def fractionalNearFrameSubtreeG5R0085LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0085Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0085LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
