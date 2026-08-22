import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0038`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0038Mask : ℕ := 5447569836182616

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0038Witness : Array ℤ :=
  #[131, 82, -52, 65, 50, -77, 258, 66, -88, -101, 26, -214, 71, -37, -67,
  53, 14, 61, -130, -88, 191, -115, 292, -19, -67, -42, -217, 248, -130,
  220, -58, -57, 194, 5, -396, -232, 55, 292, -49, 51, -304, 74, 164, 323,
  -66, -12, 83, 81, -252, -71, -93, -71, 6, 165, 184, -73, 65, -145, -90,
  103, -181, -9, 205, -54, 462, 31, 29, -166, 55, 161, 75, 354, -116, 116,
  -46, 33, 331, 5, -123, 18, -53, 25, -53, 29, -89, 0, -82, 30, 0, -29,
  -257, -143, -30, 0, 30, 5, -144, 248, 141, -141, 279, 79, -16, -82, 214,
  -230, 10, 1, 212, -4, 100, 66, 227, 413, 298, 351, -197, -122, -477, 25,
  3, -196, 148, 75, -92, 82, -63, -127, 201, 224, 47, -41, 37, -236, 143,
  67, -44, 238, 54, 28, 223, 63, 234, 80, 84, -52, 107, -305, 47, 112, 65,
  -190, 46, -13, 175, 46, 218, -119, 287, 256, -327, -197, 229, 168, 222,
  102, 64, -151]

theorem fractionalNearFrameSubtreeG4R0038_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0038Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0038Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0038Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0038_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0038LowerBoundTable : List ℤ :=
  [182, 408, 474, -30, 264, 531, 176, 2, 179, 897, 437, 602, 675, 9, 592,
  258, 704, 393, -167, 273, 471, 441, 162, 187, 11]

def fractionalNearFrameSubtreeG4R0038LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0038Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0038LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
