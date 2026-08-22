import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0005`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0005Mask : ℕ := 254736392475141

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0005Witness : Array ℤ :=
  #[-14, -72, -27, -123, -13, -51, 61, -42, -11, 129, 0, -37, 56, -36, 90,
  72, 0, -19, -63, -64, -64, 11, 0, 104, 34, 7, 38, -6, -13, 20, 58, 48, 75,
  6, 102, 20, -190, -4, -46, 78, 57, 44, 92, -42, -45, -121, 32, 11, -13,
  -90, -67, -73, 121, 26, -8, -48, 110, -28, -43, -31, -35, 52, -55, 6, 124,
  -40, -52, 103, 121, -51, 92, -2, 53, 54, -61, -91, 59, -70, -98, 134, 43,
  116, 31, 59, -38, -59, 57, 40, -17, -4, 3, 15, 116, -46, -3, -13, 89, -65,
  -45, -6, -2, 40, 84, -65, -9, -33, -21, 85, -26, 74, 47, 64, -119, 89, 75,
  76, -128, 129, 119, 13, -14, -5, -9, -31, -24, -14, 63, -25, -20, 55, 7,
  63, 74, -51, -47, -75, -31, 28, -108, -11, -3, 31, -103, -123, -137, 53,
  -24, 34, 79, -30, -30, 40, 46, -15, 58, 59, 8, 117, 14, 11, 91, 127, 37,
  -75, -30, 64, 46, -108]

theorem fractionalNearFrameSubtreeG2R0005_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0005Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0005Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0005Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0005_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0005LowerBoundTable : List ℤ :=
  [-23, 16, 20, 127, 56, 11, -14, 156, 203, -126, 397, 520, 148, 10, 9, 202,
  163, 199, 10, 213, 8, 7, 172, 9, -171]

def fractionalNearFrameSubtreeG2R0005LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0005Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0005LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
