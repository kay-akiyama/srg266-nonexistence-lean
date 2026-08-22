import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0595`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0595Mask : ℕ := 6867157599062632

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0595Witness : Array ℤ :=
  #[-17, -43, 76, -13, -60, -23, -105, 20, -4, -130, 59, 57, 43, 81, 133,
  40, 111, 47, 34, 39, -66, 12, 53, -67, -63, -112, -128, -82, 15, -8, 33,
  38, 0, -2, -36, -2, -81, -24, -3, 22, -16, -53, 25, -3, 45, -84, -13, 41,
  -27, -11, -86, -52, 82, -9, 59, 92, -29, 0, 10, -49, -22, -68, -22, -19,
  21, -67, -22, 34, -83, 34, -50, -1, -12, 6, 26, 7, -104, -75, 145, 20, 44,
  5, 26, 29, 39, 36, 46, 21, 49, -66, 33, 30, 41, 61, -21, -18, -5, 26, 62,
  -11, -32, 14, -47, -14, -61, 4, 16, -44, 87, 9, -7, -1, 26, 8, 13, -52,
  -104, -90, -104, 13, 3, -67, 0, 148, 5, -85, -21, -50, 40, 10, -33, -13,
  51, -59, -8, -87, -38, -138, 57, 44, -28, -114, 41, 14, 32, 28, 106, 63,
  15, -3, -8, -25, 27, -17, 30, 13, 42, -46, 22, 14, 0, 39, 60, 20, 31, -4,
  -32, -19]

theorem fractionalNearFrameSubtreeG2R0595_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0595Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0595Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0595Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0595_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0595LowerBoundTable : List ℤ :=
  [-119, -19, 3, 3, -149, -53, 2, 2, -112, 10, 304, 60, -21, 59, -44, -5,
  11, -54, 11, 233, 25, -189, -133, 9, 190]

def fractionalNearFrameSubtreeG2R0595LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0595Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0595LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
