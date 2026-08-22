import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0132`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0132Mask : ℕ := 5893782040462610

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0132Witness : Array ℤ :=
  #[10, -3, 9, 25, -16, -50, 92, -39, 0, 11, 8, 0, -15, 50, 1, 72, 2, 81,
  16, 23, 83, 0, 70, 48, -66, 0, -38, -51, -35, -35, -117, 16, -24, 76, -81,
  11, 66, 44, -24, -2, 40, 17, 37, 72, 56, -98, -157, -24, 22, 4, -8, -11,
  35, -22, -96, -84, -44, 40, 48, 109, 43, 47, -99, 0, 84, 84, 48, 66, 98,
  44, 38, 48, 49, 39, -69, 0, -24, 27, -16, 53, 71, 14, 113, -66, 33, -1,
  -29, -47, 67, -30, 66, 2, 52, -5, 13, 5, -67, 77, 15, -50, 96, 84, -44,
  -14, 62, 20, 20, 45, -9, -106, 23, 41, 24, 154, 24, 83, -4, -121, -248,
  99, 23, 63, 50, -98, -37, 67, 128, -89, 55, 48, 13, 7, 4, -86, 16, 48, 56,
  27, 50, 4, 38, 30, -13, 0, -8, 32, 17, -4, -29, -21, 72, 0, 1, -9, -34,
  -87, 68, 80, -17, 27, 16, 23, 30, 106, 57, 116, 8, 20]

theorem fractionalNearFrameSubtreeG5R0132_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0132Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0132Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0132Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0132_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0132LowerBoundTable : List ℤ :=
  [72, 176, 221, 136, 0, 177, 83, 149, 158, 302, 219, 93, 632, 191, 293, 9,
  26, 53, 267, 122, 211, 44, 30, 145, 191]

def fractionalNearFrameSubtreeG5R0132LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0132Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0132LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
