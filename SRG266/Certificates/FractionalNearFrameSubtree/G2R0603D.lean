import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0603`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0603Mask : ℕ := 6881376079680112

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0603Witness : Array ℤ :=
  #[-70, 107, 58, -17, 131, -98, 93, 152, -44, 47, 67, -2, -22, 32, 6, -44,
  191, 45, -77, 72, 62, 189, 2, 44, -57, -19, -215, 0, -104, -134, 31, 65,
  186, 308, -222, -206, -19, 172, 118, 226, -49, -368, 87, 62, -53, 47, 102,
  149, 86, 371, -164, -350, -85, 85, 289, -68, 153, -212, 27, 316, 89, -214,
  -97, -192, -125, 52, 19, 33, 119, -44, 66, 45, -42, 39, -29, 99, 203, 21,
  92, 122, -9, 124, 118, 266, 127, 179, 15, -107, -59, -218, 65, 48, -127,
  -114, -33, -81, -93, -94, 109, 33, -258, 78, -71, -141, -325, -98, -10, 0,
  23, 114, 13, 121, -123, -218, 83, 88, -109, 230, 136, -199, 93, 111, -259,
  86, -41, -245, 129, 62, -136, -44, 111, 123, 143, 85, -143, 3, -49, -189,
  220, -129, 243, 136, -161, 0, -202, 53, 89, -219, 123, 49, 96, -165, 51,
  48, 110, -115, -90, -10, 31, -22, 57, 114, -207, 169, 27, 35, -40, 39]

theorem fractionalNearFrameSubtreeG2R0603_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0603Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0603Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0603Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0603_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0603LowerBoundTable : List ℤ :=
  [-86, 25, -118, 203, 250, 57, 2, 193, 105, -7, -37, 64, 128, -161, -121,
  -120, 608, -555, 263, 762, 799, -139, 953, -237, 290]

def fractionalNearFrameSubtreeG2R0603LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0603Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0603LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
