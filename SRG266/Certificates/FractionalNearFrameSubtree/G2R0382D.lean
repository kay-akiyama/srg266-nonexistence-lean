import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0382`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0382Mask : ℕ := 5738192956007698

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0382Witness : Array ℤ :=
  #[-24, -32, -27, -12, -41, 26, -64, -30, -31, -7, -43, 38, 110, 36, 27,
  59, -35, -33, -14, -33, 34, 9, 22, 45, 38, 41, 8, -21, -39, -16, -46, -43,
  6, 28, 16, 16, 3, -3, 5, -21, 11, -10, 0, 28, -39, 17, -36, 17, 2, 2, 1,
  19, 10, 26, -2, -2, 0, -30, -23, -14, 0, 67, 57, 5, -24, 77, 48, -42, -64,
  27, 13, 19, 12, -22, -6, 26, 10, 5, 24, 0, 10, -5, 25, -6, 35, 15, 9, 19,
  -4, 7, 29, 9, 14, 9, 13, 25, -17, 50, -3, -28, 57, -23, -15, -12, -34, -7,
  37, -35, -20, -2, -36, 1, 14, 25, 25, -16, -5, 72, 0, -97, -20, -10, -88,
  13, 13, 83, 28, -5, -39, 20, -6, -1, 48, -3, 30, 38, -3, 3, 11, -49, 14,
  -31, 0, 12, 56, -36, -15, 28, -20, -15, 19, 27, 3, 50, 33, 0, 12, -37, -6,
  -27, -36, -38, -17, 1, 27, -1, 15, 32]

theorem fractionalNearFrameSubtreeG2R0382_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0382Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0382Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0382Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0382_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0382LowerBoundTable : List ℤ :=
  [-3, 3, 3, 46, 69, 20, 28, 60, 2, 50, 65, 280, -49, 43, 67, 35, -35, 55,
  11, 10, 101, 10, 5, 115, 8]

def fractionalNearFrameSubtreeG2R0382LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0382Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0382LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
