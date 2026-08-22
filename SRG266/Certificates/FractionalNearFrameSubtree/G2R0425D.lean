import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0425`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0425Mask : ℕ := 5778801969238612

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0425Witness : Array ℤ :=
  #[9, 78, 42, -90, -177, 8, -113, -13, -99, -16, -29, -20, 185, -43, 277,
  144, -79, 159, -23, -32, -59, 61, -72, 149, 67, 31, 57, -17, 0, 150, 87,
  201, -21, -68, -116, -54, -85, -45, -5, 28, 31, -69, 0, 70, -39, 76, 182,
  81, -199, -156, 47, 50, -127, -24, -92, 83, 193, 54, -13, -52, 76, 42, 46,
  -28, 56, 29, 23, 28, -138, 69, -22, 83, 175, 68, -139, 205, 16, -153,
  -137, -169, -158, -23, -54, 69, 226, -62, 49, 23, -5, 69, -47, 77, -42,
  -199, 186, 103, 110, -23, 5, -13, 138, 76, -12, 180, 20, 83, 123, 132,
  180, 171, -173, -18, 27, -37, 2, 42, 22, 73, 42, -81, 39, 102, 43, 43, 82,
  37, 0, -48, -36, 7, 13, -36, 83, -75, 58, 66, -108, -4, 13, 3, -5, -99,
  20, 101, -86, -67, 4, 74, -27, -48, -16, -114, -28, -36, -33, -53, 62, 60,
  29, 88, 18, -38, 30, 52, 99, -26, -46, -162]

theorem fractionalNearFrameSubtreeG2R0425_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0425Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0425Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0425Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0425_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0425LowerBoundTable : List ℤ :=
  [60, 37, 262, 108, 127, 2, -23, 3, 310, 87, 10, 344, -26, 834, 626, 322,
  246, 9, 351, -244, 764, 9, 432, -157, -55]

def fractionalNearFrameSubtreeG2R0425LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0425Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0425LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
