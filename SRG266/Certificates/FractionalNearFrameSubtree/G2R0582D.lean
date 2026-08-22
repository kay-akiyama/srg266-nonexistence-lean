import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0582`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0582Mask : ℕ := 6850681030773352

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0582Witness : Array ℤ :=
  #[-39, 54, -63, -22, -51, 24, -109, -178, -67, -64, 77, 69, 78, 89, -55,
  63, -119, 37, 13, 155, 40, -88, -147, 94, -60, 37, 187, -11, 33, 1, 13,
  79, 0, 8, 84, 106, 34, -10, 61, -147, 27, 36, 11, -13, 107, 40, 41, 30,
  18, -19, 3, -172, -113, -28, 35, 72, -25, 67, 42, -34, 70, -63, -22, 115,
  82, 12, 74, 133, -59, 5, 1, 21, 7, -16, 18, -105, 27, -45, 2, 42, -24,
  -108, 11, 138, 44, 117, -1, -20, -22, -30, 52, -10, -13, -20, -51, 63,
  -181, -110, -82, 20, -83, -28, -165, -60, 62, -27, -3, -1, -13, 103, 41,
  11, 106, -179, -172, -168, -39, 83, -192, 61, 175, -20, -169, 92, -76,
  -62, 119, -7, 39, 7, -127, 1, 177, 117, 18, 56, 12, -38, 14, 178, -37,
  -44, -23, -48, -88, -61, 36, 39, -44, 137, 30, 28, 99, 0, 19, -7, -37,
  -232, -48, 56, 2, 154, -89, 83, 281, -40, 29, -4]

theorem fractionalNearFrameSubtreeG2R0582_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0582Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0582Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0582Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0582_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0582LowerBoundTable : List ℤ :=
  [-23, 2, 234, 2, -192, 2, 211, 20, -65, 333, 431, -16, -263, -246, -13,
  261, 87, 179, -565, 58, 73, 294, 102, 172, 63]

def fractionalNearFrameSubtreeG2R0582LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0582Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0582LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
