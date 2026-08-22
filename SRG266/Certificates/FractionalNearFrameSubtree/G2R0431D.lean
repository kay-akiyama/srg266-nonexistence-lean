import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0431`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0431Mask : ℕ := 5785185574130252

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0431Witness : Array ℤ :=
  #[-23, 15, -1, -22, -96, 76, -28, 50, 92, -12, 94, 114, 40, 32, -54, -23,
  32, 35, -6, -5, -34, 66, -24, 80, -63, 123, 24, 46, -25, -26, 124, -96,
  -38, -58, 73, -12, 84, 108, 129, -1, -78, 63, 143, -87, 10, -4, 11, 55,
  66, -163, 75, 46, 96, -25, 146, 51, 91, 59, 27, 21, 40, 149, -29, -80,
  -23, -3, 49, 91, 61, -2, 9, 11, -95, 86, 77, 41, 16, -27, -21, 73, -51,
  50, -80, 110, -53, 80, 93, -7, -47, -44, 126, -19, -78, 23, -39, 47, 139,
  -82, -9, 18, 8, -10, 38, 50, 148, 42, 128, 81, -88, -96, 104, 126, 121,
  -13, 21, -90, -18, 77, -95, 59, 20, -12, 8, 171, -12, 109, -60, -34, 7,
  -62, -36, 9, -78, -67, -127, 45, -87, 31, 57, 54, 47, 12, 14, 52, -62,
  174, 58, -7, -48, -34, 47, -83, 0, -66, 27, 39, 112, 71, -96, 15, 60, -31,
  12, 47, 91, 43, 16, 140]

theorem fractionalNearFrameSubtreeG2R0431_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0431Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0431Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0431Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0431_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0431LowerBoundTable : List ℤ :=
  [190, 117, 407, 173, 146, 110, 241, 51, 477, 665, 73, 71, 163, 374, 388,
  -10, 466, 265, 171, 454, 274, -81, 326, 382, 1]

def fractionalNearFrameSubtreeG2R0431LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0431Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0431LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
