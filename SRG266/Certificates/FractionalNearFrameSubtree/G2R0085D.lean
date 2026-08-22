import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0085`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0085Mask : ℕ := 1041831968871024

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0085Witness : Array ℤ :=
  #[7, 75, 29, 33, -36, -90, -18, -70, 61, 60, -72, -33, 0, 76, -121, -103,
  -15, -13, 6, -40, -7, 14, 147, 22, -72, 66, -102, 35, -58, 52, -4, -132,
  70, 36, 40, 18, 99, -33, 65, 53, -83, 74, 45, 7, -1, -150, -25, 47, 46, 9,
  17, 41, -100, 76, 121, 95, 70, 30, 18, -53, -19, -46, 16, -157, -33, -57,
  23, 25, 1, -9, -50, 8, -18, 0, 72, -127, -71, -5, -13, -120, -14, 6, 73,
  -34, -75, -1, 0, -75, -107, 71, -71, -79, 56, 92, -73, 78, 53, 29, -129,
  45, -51, 37, -43, 56, 34, -76, 98, 80, 78, 17, 22, -39, 66, -23, 16, 26,
  -37, 110, 124, 65, -37, -24, -70, 16, 153, 51, -57, -37, 59, -34, 33, -87,
  7, 72, 6, -16, 51, -101, -27, -112, 94, -64, -70, 32, 22, 20, -108, 58,
  36, 87, 58, 4, 71, 69, 40, -12, -76, -70, 57, 75, 118, -49, 89, -153, 124,
  8, 41, -57]

theorem fractionalNearFrameSubtreeG2R0085_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0085Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0085Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0085Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0085_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0085LowerBoundTable : List ℤ :=
  [-50, 101, -58, 55, -24, -165, 1, 2, 139, 29, 146, 312, 306, 23, 215,
  -389, 315, 148, 237, 76, -155, -176, 296, 154, 11]

def fractionalNearFrameSubtreeG2R0085LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0085Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0085LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
