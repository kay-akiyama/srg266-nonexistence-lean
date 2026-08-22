import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0282`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0282Mask : ℕ := 5372953977017000

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0282Witness : Array ℤ :=
  #[-60, 31, 14, -4, 60, 2, -40, -85, 68, -54, 55, 16, 146, 9, -8, 66, 47,
  1, 16, 67, 29, -99, 66, 17, 24, -109, -13, 57, 47, 29, -36, 60, -9, 20,
  37, 4, -13, -6, 74, 38, -10, 71, 23, 94, -32, -21, -25, 15, 93, -20, -110,
  -68, 105, 69, -30, 168, 10, -90, 26, -17, -32, -42, -18, 66, 46, -58, 168,
  -34, -6, -11, 18, -87, -38, -29, 33, 51, -74, -14, -38, 54, -48, 114, 24,
  36, -41, 18, -15, -20, -93, 28, 73, 18, 45, -88, -32, -22, -52, -11, 5,
  78, -13, 72, 48, 14, 56, 125, 19, -159, -149, -162, 78, 62, -28, 10, 145,
  9, 20, -17, -61, -157, 133, 147, -49, -41, 103, 87, 75, 101, -46, -27, -9,
  -180, 36, 23, -33, -3, -3, -71, 79, 24, 29, 40, -12, 127, 96, -59, 62,
  -11, 23, 116, 111, 23, 24, 55, 41, -76, -46, -3, -108, 25, -12, 18, 59,
  147, 49, -39, -184, 88]

theorem fractionalNearFrameSubtreeG2R0282_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0282Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0282Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0282Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0282_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0282LowerBoundTable : List ℤ :=
  [56, 187, 2, 250, 1, 103, 3, 157, 116, 206, -65, 238, 156, 11, 145, 224,
  302, -142, 450, 314, 353, 10, -1, 188, 82]

def fractionalNearFrameSubtreeG2R0282LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0282Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0282LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
