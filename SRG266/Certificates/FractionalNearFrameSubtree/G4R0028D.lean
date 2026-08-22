import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0028`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0028Mask : ℕ := 5368610111261187

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0028Witness : Array ℤ :=
  #[-47, 122, 79, -13, 33, 193, 68, 207, 271, 178, 209, -277, -172, -261,
  -143, -182, -2, 15, 133, -82, -59, 180, -309, -31, 14, -134, 47, -120, 11,
  75, 132, 103, -56, 132, 116, 54, 195, 47, 114, 49, 11, -55, 132, 34, 13,
  77, -59, 64, 22, 111, 28, 76, 23, -121, 87, 40, -232, 113, 24, 89, 126,
  55, 33, -64, -81, -212, -111, 15, -75, 29, 114, -52, 30, -38, 131, -9,
  -149, -31, -76, 20, 201, -3, 261, 53, 119, 167, -165, -138, -119, 115, 28,
  4, -22, -107, 80, 206, 213, 122, 121, 175, 32, 167, -114, -109, 202, -64,
  -256, -159, -296, 96, -226, 217, 101, 283, -3, 134, -13, 41, 56, 38, -123,
  -27, 136, -128, -172, 29, 219, 132, -134, -131, -57, -135, -185, -60, 140,
  -12, -54, 129, -137, 0, -74, -155, -2, 26, -130, -188, 103, 207, 106, 172,
  50, -151, 134, -120, 249, 260, -56, 161, 57, 46, 128, -224, 284, 256, 173,
  153, -43, 124]

theorem fractionalNearFrameSubtreeG4R0028_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0028Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0028Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0028Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0028_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0028LowerBoundTable : List ℤ :=
  [86, 328, 410, 199, 240, 259, 179, -112, 206, 222, 72, 109, 450, 732, 362,
  -189, 666, 154, 431, 10, -114, 1028, 1033, 11, 165]

def fractionalNearFrameSubtreeG4R0028LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0028Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0028LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
