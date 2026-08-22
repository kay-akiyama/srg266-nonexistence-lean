import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0043`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0043Mask : ℕ := 2519149015187537

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0043Witness : Array ℤ :=
  #[-79, -22, -15, -37, -15, 33, -51, -81, -115, 63, -90, 94, 0, 2, 8, 97,
  77, 12, 64, 7, 78, 38, -13, 43, -35, 44, -154, -130, -86, -13, 18, 7, 56,
  -101, -84, -58, 48, 113, 11, -2, -74, 0, 98, 72, -98, -120, -71, -226,
  113, 0, 81, 120, 151, 147, 51, 26, -32, 83, 89, 64, -20, -31, -65, -19,
  57, -15, 35, 51, -3, -28, -64, -41, -50, 7, -78, 143, -44, -37, 23, 90,
  48, 134, 18, -26, 32, 45, -8, 62, 112, 14, 96, -19, 40, -74, 40, -61, 0,
  1, 82, 4, -52, -29, -37, 9, 52, 3, 98, -4, -91, -117, -62, 41, 2, -2, -44,
  28, -24, 144, 47, -3, 14, -1, 92, -6, -39, -29, 10, -56, -41, 40, 0, -54,
  -63, 73, 81, -80, 32, 57, 38, -35, 49, 124, -110, -91, -180, -19, -88,
  -66, -113, 90, -22, -19, 17, -56, 76, -23, 84, -22, -62, 76, -7, -12, 13,
  43, 41, 11, -7, -55]

theorem fractionalNearFrameSubtreeG5R0043_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0043Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0043Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0043Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0043_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0043LowerBoundTable : List ℤ :=
  [-48, 2, 2, 228, -81, 2, 42, 14, -86, 76, 74, 99, -424, 10, 51, 339, -51,
  134, 311, 346, 9, -153, 2, 191, -54]

def fractionalNearFrameSubtreeG5R0043LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0043Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0043LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
