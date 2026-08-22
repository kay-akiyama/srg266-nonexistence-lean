import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0638`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0638Mask : ℕ := 11345391171244644

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0638Witness : Array ℤ :=
  #[64, 243, 251, 218, 293, -109, -140, -7, -117, -112, -49, -144, -110,
  -84, -38, 0, -201, -2, -65, -99, -147, 39, 100, -27, 201, 120, -34, 66,
  167, 114, -108, 35, -102, 50, -85, -128, 83, 241, 133, -47, -110, 40, 111,
  176, 178, 74, 45, 102, 52, -53, -175, -117, -31, 64, -22, -117, 41, 75,
  -97, 54, 34, 158, -47, -87, 8, -68, 14, 32, -101, 120, 117, 92, 37, 31,
  33, -15, -44, 4, 45, 108, 65, 122, 44, -19, 0, 0, -5, 106, -17, 130, -66,
  -69, -36, 30, 73, 32, 68, -68, -154, 53, -51, -56, -6, 80, -70, -2, 171,
  168, -31, 103, 17, -36, 3, -19, 76, -34, 151, -42, -79, -64, 58, 218, -15,
  121, -72, -39, 6, -105, 86, 86, 70, 46, 73, 38, 82, -49, 62, 37, 101, 38,
  92, 74, -172, 9, -223, 10, -17, 27, 3, -13, 35, 53, 87, 72, 139, 33, 28,
  93, 88, 53, 0, 59, 130, -49, -4, -65, -74, 16]

theorem fractionalNearFrameSubtreeG2R0638_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0638Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0638Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0638Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0638_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0638LowerBoundTable : List ℤ :=
  [174, 273, 343, 209, 166, 345, 94, 1, 233, 310, 380, 318, 250, -6, 482,
  -230, 398, 403, 438, 337, 457, 263, 56, 292, -96]

def fractionalNearFrameSubtreeG2R0638LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0638Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0638LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
