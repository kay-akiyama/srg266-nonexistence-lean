import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0190`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0190Mask : ℕ := 6866916357327512

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0190Witness : Array ℤ :=
  #[-3, 26, 5, 26, -5, -4, 22, 24, -53, 3, -27, -49, -32, -4, 17, -23, 8,
  -38, -1, -8, 3, -6, -23, -45, 32, 29, 20, -21, -28, 21, 40, -26, -10, 43,
  44, -51, -16, -39, 62, 0, -33, 0, -23, 4, 41, 78, -21, -47, 46, 44, 22,
  -28, -50, -23, 43, 42, 42, 32, 14, 13, -23, -24, 13, -46, 48, -16, -41,
  -34, 2, 35, 23, 2, -17, -2, -22, 15, -27, -13, 51, 37, 41, 16, -16, -16,
  12, 14, -2, -11, -39, -4, -28, 8, 6, -34, 33, 23, 5, -67, -4, -46, -35,
  59, -3, -65, 28, 32, 48, -10, -68, 5, 64, 0, 13, -9, 32, 42, -9, 0, 3, 7,
  50, 13, -5, 15, 13, -18, -45, -1, -23, -32, -52, -3, 9, 4, -1, 22, -94,
  46, 12, 23, 64, -16, 42, 0, 11, 35, 16, 17, 12, 47, 11, 30, -8, -5, 16,
  43, 40, 18, 7, 3, 8, 37, 4, 10, -21, 27, -61, -25]

theorem fractionalNearFrameSubtreeG3R0190_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0190Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0190Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0190Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0190_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0190LowerBoundTable : List ℤ :=
  [-20, 60, 43, -14, 2, 45, 62, 2, -3, 49, 148, 103, 121, 41, -31, 26, -26,
  -28, 46, 145, -121, 171, 61, 102, 52]

def fractionalNearFrameSubtreeG3R0190LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0190Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0190LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
