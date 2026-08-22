import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0070`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0070Mask : ℕ := 2337418075935235

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0070Witness : Array ℤ :=
  #[118, 117, 82, 181, 39, 76, -38, -150, -202, -186, -137, -168, 108, 0,
  161, 6, 53, -85, -120, -49, -51, -92, -161, -139, 51, -55, 25, -86, -115,
  333, 132, 84, 139, 120, -24, -15, -19, -7, -123, 35, 72, 161, -157, 83,
  -55, -51, 189, 94, -65, -2, -85, 23, -69, 37, 14, -183, 80, 125, -32, -62,
  108, 36, -5, -109, -39, -3, 118, -45, 22, -70, 17, 1, -55, -58, -8, 80,
  -40, 92, -82, -21, -48, 47, 115, 87, -54, 105, -65, 4, 61, -130, -55, -4,
  27, 57, 44, -29, 132, 66, 91, 39, -65, 55, 28, 24, 150, 77, 41, 170, 144,
  108, 101, -3, 32, 86, -66, 80, -5, 120, 5, 15, -85, 49, 173, -13, -16,
  -93, 153, 109, -113, 129, 67, 14, 82, -42, 10, 32, 206, -81, 95, -42, 31,
  -92, 23, 64, 55, 0, -42, 35, 107, 67, 105, 125, 125, 14, -137, -2, -88,
  -66, -114, 33, 75, -216, -62, -15, -60, 42, 14, -103]

theorem fractionalNearFrameSubtreeG3R0070_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0070Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0070Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0070Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0070_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0070LowerBoundTable : List ℤ :=
  [39, 152, 1, -9, 7, 158, 291, 247, -102, 379, 613, 319, 226, 257, 69, -11,
  -68, 43, 10, 164, 402, 11, 454, 415, 680]

def fractionalNearFrameSubtreeG3R0070LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0070Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0070LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
