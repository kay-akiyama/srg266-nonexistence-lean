import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0111`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0111Mask : ℕ := 1305925223687171

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0111Witness : Array ℤ :=
  #[-46, 9, 89, 28, 0, 118, 72, 77, 118, 139, 147, 167, -181, -238, -229,
  -173, -102, -133, -84, -60, 0, -33, 62, -17, 1, -30, -18, 18, 3, 14, 0,
  34, 70, 24, -51, -61, -20, -4, 26, -15, -29, -22, 94, 67, 49, 126, -62,
  -19, -18, 53, 0, 19, -27, -4, -5, 83, 1, -2, 66, 22, -36, 63, -31, 106,
  -92, 72, -13, 83, 42, 13, -9, 17, 25, -67, -67, 58, 55, -42, -20, 83, -56,
  45, -64, 118, 0, -37, 64, 40, 22, 111, 0, -16, 40, -9, -61, 39, 78, 26,
  -23, 155, 110, 54, 2, 110, 86, 18, -7, -95, -94, -57, -53, 15, 14, -32,
  -107, -117, -19, 0, -20, 25, -32, -15, -88, -77, 50, -24, -23, 16, -8,
  -100, 17, -82, 8, -45, -19, 53, 0, -75, 54, 90, -56, -1, -17, 74, -9, -22,
  -91, 21, -126, 123, 16, -80, -91, 100, 10, 13, 4, 1, 24, 39, -21, 39, 5,
  125, 7, 28, 38, -97]

theorem fractionalNearFrameSubtreeG2R0111_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0111Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0111Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0111Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0111_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0111LowerBoundTable : List ℤ :=
  [-35, 3, 71, 116, 100, 109, -35, -79, -108, -7, -257, 257, -328, -121,
  208, 31, 127, 140, 455, 63, 10, 170, 116, -201, 380]

def fractionalNearFrameSubtreeG2R0111LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0111Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0111LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
