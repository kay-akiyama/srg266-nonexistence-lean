import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0031`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0031Mask : ℕ := 5387247644789009

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0031Witness : Array ℤ :=
  #[33, 36, -18, 122, 33, 405, -234, -372, -316, -349, -282, 383, 443, -251,
  54, 206, 50, 351, -29, 75, 317, 84, 63, 218, 373, 0, -699, -219, -71, 271,
  -77, 138, -150, 44, -235, -202, 258, 81, -12, 255, 182, 373, -206, 56,
  239, -43, 224, -23, -153, 148, -161, 217, 31, 85, 183, -41, 81, 36, -125,
  70, 307, -90, 201, -159, 58, 533, 451, 218, -352, 257, -276, -141, 92,
  -187, 97, 273, 90, -394, 252, 99, 245, -190, 262, 100, -101, 93, 667, 352,
  84, -162, 646, -487, -242, 35, 456, -135, -349, 92, 292, 0, -179, -72,
  -383, 104, -175, 102, -424, -205, -164, 144, -61, 40, -170, -194, 52,
  -395, -42, -13, -88, 56, -214, -644, 14, 786, 151, 497, 225, -245, 26, 44,
  -599, -8, 263, 419, 36, 0, -91, -266, 967, -95, -34, 435, 0, 116, 504, 30,
  4, -401, -31, -48, 482, 532, 297, -106, -399, -154, -143, -351, -151, -78,
  619, 401, -558, -60, -351, 33, -90, 98]

theorem fractionalNearFrameSubtreeG4R0031_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0031Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0031Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0031Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0031_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0031LowerBoundTable : List ℤ :=
  [151, 147, 2, 1604, 263, 35, 94, 2, 337, 9, 598, -332, -23, 21, 186, 9,
  283, 1096, 981, 2720, 65, -71, 12, 445, 516]

def fractionalNearFrameSubtreeG4R0031LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0031Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0031LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
