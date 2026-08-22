import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0198`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0198Mask : ℕ := 2339514556846161

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0198Witness : Array ℤ :=
  #[-23, -30, 45, 94, 0, 88, 0, -35, 48, 72, -43, -68, -20, 9, -62, 27, 20,
  -134, 63, 129, 41, 19, -22, 28, 22, 28, 13, -103, 43, -22, -23, 74, 34,
  126, 136, 81, 208, -101, 0, -100, 44, -147, -21, -65, -116, 0, -109, 41,
  -2, 51, 48, 11, -11, -8, 7, -46, 5, -8, -29, 4, 65, 25, 13, -6, 11, 20,
  28, 35, 3, 11, -18, -29, -1, 39, 22, 52, -22, 27, 17, -1, 7, 12, 46, -22,
  -26, -34, 22, -40, 51, -23, -15, -1, 25, -31, -8, 31, 57, -110, 34, -51,
  -20, -9, 15, -11, 9, -22, 45, 94, 79, 107, -1, -44, 45, 20, -93, 76, -43,
  -72, 37, 37, 68, -2, 64, 5, -9, -12, -30, 117, 22, 16, 38, 70, 33, -14,
  49, -23, -33, -41, 67, 1, 2, 28, 27, -18, -29, 45, 92, 66, 35, 38, 23, 90,
  143, -20, -40, -47, -1, 14, -59, -14, -17, -13, -62, 47, 5, 55, 59, -94]

theorem fractionalNearFrameSubtreeG2R0198_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0198Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0198Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0198Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0198_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0198LowerBoundTable : List ℤ :=
  [62, 224, 2, 175, -33, 1, 307, 133, 1, 160, 366, 322, 125, 10, 63, 100,
  132, -62, 292, 81, 243, 255, -128, 226, -36]

def fractionalNearFrameSubtreeG2R0198LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0198Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0198LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
