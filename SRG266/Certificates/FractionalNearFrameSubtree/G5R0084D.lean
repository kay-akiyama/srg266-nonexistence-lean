import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0084`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0084Mask : ℕ := 5471537393680786

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0084Witness : Array ℤ :=
  #[47, 81, 47, 69, 132, 17, 102, 64, 18, 90, 69, -93, 11, -45, -147, -36,
  -14, -107, -2, -40, 9, -5, -93, -34, 108, -90, 55, 51, 66, 181, 0, 21,
  -104, 54, 63, 17, -47, -9, -26, 160, 139, 7, -68, -70, -14, -77, 87, 31,
  111, 96, 15, -103, 196, -79, -162, -147, -19, 4, 40, 51, 84, -167, 96,
  -135, 135, 131, -67, -57, 155, -104, 92, -79, 83, 15, 23, 3, -40, 13, 40,
  16, 87, 73, -112, -89, 108, 116, -80, 123, 16, -149, -73, -51, -90, -13,
  -65, 59, 69, 132, -166, 103, -36, 24, 80, -12, 29, 7, 197, -7, 118, 25,
  20, -70, 24, -107, -97, 102, 27, -170, 20, 76, -54, -48, -42, -73, 12,
  -35, -33, 129, -71, 70, -67, 102, 118, 50, -149, 37, 132, 109, 99, -13,
  222, 92, -133, -233, 39, 78, -101, 38, 78, -20, -86, -10, 152, -24, 34, 4,
  91, 135, 31, -127, -23, -68, -106, -8, -38, -11, 66, 31]

theorem fractionalNearFrameSubtreeG5R0084_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0084Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0084Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0084Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0084_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0084LowerBoundTable : List ℤ :=
  [2, 80, 1, 258, -44, 167, 130, 234, 21, -232, 262, 198, 128, 164, -54,
  -70, -434, 111, 478, 265, 162, 313, 228, 641, 120]

def fractionalNearFrameSubtreeG5R0084LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0084Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0084LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
