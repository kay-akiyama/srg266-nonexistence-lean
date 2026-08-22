import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0067`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0067Mask : ℕ := 828787580453208

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0067Witness : Array ℤ :=
  #[-22, -11, -52, 67, -33, 73, 35, 49, 31, 57, -45, -6, -18, 0, -12, 15,
  -13, -34, 38, 21, 30, -15, -24, -29, 5, 26, 67, 40, -11, -40, 12, -12,
  -91, 42, -25, 21, -46, -36, 41, -22, 78, 0, 7, -34, 77, 25, 4, 89, -93,
  -32, 28, 22, 55, -31, -10, -18, -63, -31, 23, 60, 56, 74, 24, -25, 6, -71,
  12, 44, -16, 65, 20, 70, 20, -92, 35, 92, -14, 37, 56, 22, -10, 42, 33,
  -5, 35, 36, -36, 8, 3, -15, 2, 62, 28, -16, -44, 10, 6, 14, -16, -2, 99,
  20, 31, 30, 24, -16, 98, 6, -51, -20, -2, -7, 50, -3, 13, 32, -39, -33,
  55, 72, 7, -24, -20, 102, 26, -27, -47, 28, -40, 52, -16, 4, 12, -12, 64,
  -69, 81, -19, 6, 61, -5, 47, 19, 41, 32, -72, -77, 1, -40, 35, 52, -10,
  72, 38, -44, 30, -17, 31, 8, 31, -35, 52, -64, 46, 42, 56, 59, 29]

theorem fractionalNearFrameSubtreeG1R0067_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0067Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0067Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0067Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0067_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0067LowerBoundTable : List ℤ :=
  [85, 151, 138, 80, 201, 100, 51, 68, 41, 10, 43, 170, 185, 349, 183, 44,
  7, 322, 120, 139, 39, 81, 429, 199, 147]

def fractionalNearFrameSubtreeG1R0067LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0067Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0067LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
