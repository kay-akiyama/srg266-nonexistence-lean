import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G3R0108`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0108Mask : ℕ := 5385117356462730

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0108Witness : Array ℤ :=
  #[118, -102, 179, 1, 20, -43, 34, -5, 61, 84, 6, 20, 88, -73, 119, 96, 77,
  37, 222, 10, -2, 167, -49, 70, 106, -24, -69, 12, -9, -12, 138, 127, -52,
  -6, -151, 32, -87, 2, 71, -29, -63, -65, 35, -123, 31, -25, 11, -82, 82,
  40, 201, 113, 10, 86, 171, 65, 2, -19, -34, 63, 4, -13, 3, 24, 86, -67,
  135, -147, 29, -6, -101, -95, -28, -174, -105, -116, 30, 51, 35, -99, -1,
  134, 47, 44, -32, 35, -77, 93, -29, 6, -36, -6, 19, -4, -37, -54, -123,
  -166, 124, 48, -31, 120, 54, 33, 107, 100, 118, 82, 71, -3, 80, 73, -45,
  41, -26, 117, 77, -12, -21, -42, 152, -15, 71, 66, -90, -1, 22, 58, 253,
  32, -70, -10, -96, -101, -10, 119, 66, -27, 24, -159, 13, 35, -108, 52,
  25, -11, 15, -4, 6, 28, 53, 55, -3, -21, -28, 3, 124, -162, 104, -42, 17,
  -130, -105, 22, -20, 69, 0, -157]

theorem fractionalNearFrameSubtreeG3R0108_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0108Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0108Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0108Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0108_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0108LowerBoundTable : List ℤ :=
  [91, 60, -23, 221, -22, 114, 120, 158, 373, 73, 289, 182, 260, 11, 313,
  255, 116, 158, 200, 213, 637, 338, -214, 277, 207]

def fractionalNearFrameSubtreeG3R0108LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0108Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0108LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
