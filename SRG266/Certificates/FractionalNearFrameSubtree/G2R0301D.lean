import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0301`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0301Mask : ℕ := 5387216655859928

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0301Witness : Array ℤ :=
  #[24, 7, 79, 15, -10, 26, 52, 128, -61, 20, 5, 56, 32, -141, -45, -2, 76,
  -60, 28, 22, 136, -3, -7, -58, -79, -1, -16, -61, 69, 109, 112, 25, 2,
  120, -254, -86, -80, 7, 187, 74, 0, -106, 51, 112, 83, -125, 51, -56, 0,
  121, -21, -35, 13, 353, 14, 103, -84, -105, -32, 57, 66, -56, 43, -66,
  -143, -67, 107, 58, -88, 69, -4, 145, 86, 144, 39, -14, 4, 84, -160, -142,
  -7, -14, 119, 59, -20, 203, -18, -1, 33, 17, -12, -96, -238, -21, 33, 57,
  172, -38, 27, -66, 28, -141, -133, 137, 15, -5, -4, -4, -16, 60, 67, -38,
  0, 40, -25, 69, 124, -23, -122, -4, -179, -149, -55, 93, -105, 209, -11,
  17, 80, 17, -34, -161, -217, 29, -11, -32, 61, 57, 32, 184, -79, -128,
  148, 76, 160, 34, 258, 7, -118, 171, 95, -8, -33, -34, 145, 31, 39, -69,
  46, -74, 74, 82, 86, 10, -32, -122, -64, 87]

theorem fractionalNearFrameSubtreeG2R0301_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0301Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0301Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0301Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0301_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0301LowerBoundTable : List ℤ :=
  [21, 176, 72, 1, 256, 2, 32, 196, 160, 190, 9, 10, 336, 108, 417, 235,
  741, -104, -270, 192, 384, 9, 135, 84, 317]

def fractionalNearFrameSubtreeG2R0301LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0301Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0301LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
