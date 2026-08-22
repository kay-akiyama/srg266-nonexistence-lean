import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0328`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0328Mask : ℕ := 5402539391685224

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0328Witness : Array ℤ :=
  #[33, -58, -101, 107, 4, -51, -12, -9, -11, -32, -3, 54, -35, -3, 143,
  -56, 68, 10, -19, -72, -62, -69, 58, -28, 65, 11, -37, 9, 22, 41, 118, 17,
  81, 63, -77, -35, -25, 34, 15, 35, -122, 41, 81, 14, -3, -56, 115, 95, 71,
  -59, -1, -78, 161, 179, 30, 83, 88, -18, -86, -108, 19, 14, -33, 19, -90,
  -42, 24, 49, -7, 30, -143, -5, 3, -22, -36, 65, -28, 65, 48, 28, 52, 103,
  96, 21, 92, -17, -101, -5, -82, -45, -46, -97, -25, -94, 22, -37, -8, -46,
  -5, -9, 86, 53, 31, -45, -6, -50, 84, 56, -5, 28, 101, 81, 69, -18, 157,
  120, -8, 102, 42, 5, 42, -15, 63, 60, -9, 52, -5, -66, 140, 5, 27, 14,
  -70, 1, 48, 15, 87, 7, -5, 117, 4, 49, 50, 54, -41, -33, -48, 11, -53,
  -103, -25, -59, -26, 57, 22, -8, 78, 45, 9, -30, 0, -52, 19, 60, 66, 56,
  -32, 1]

theorem fractionalNearFrameSubtreeG2R0328_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0328Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0328Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0328Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0328_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0328LowerBoundTable : List ℤ :=
  [43, 215, 174, 2, 67, 115, 182, 2, 213, 253, 314, 109, 348, 22, 244, -59,
  526, -38, 154, 154, 85, -172, 184, 191, 287]

def fractionalNearFrameSubtreeG2R0328LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0328Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0328LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
