import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G1R0149`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG1R0149Mask : ℕ := 1039746911865448

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG1R0149Witness : Array ℤ :=
  #[-17, 120, -14, -23, -91, 87, 18, 96, 5, -27, -157, -38, -24, -129, 89,
  45, 39, -117, -125, -31, -30, 102, -30, -84, 131, 17, 23, 47, -30, 112,
  -59, 88, -64, -42, -122, 110, -8, -58, -1, 22, 104, 64, 13, 78, 37, 64,
  22, 45, 27, -64, 8, -86, -77, -175, -73, 55, -90, -88, 152, -87, -12, 44,
  87, -120, 103, -210, 96, 96, -140, -80, 8, 86, 35, -59, -63, -92, 34,
  -102, -5, -36, 151, -146, 36, 17, -25, 51, -15, 92, 39, -17, -44, 105, 48,
  -43, -69, 114, 58, 54, 57, -82, 139, -34, -40, 71, 29, 37, -118, 127, 134,
  -103, 15, 34, 29, -110, -95, 91, 32, 16, -65, 178, -72, -40, -73, 32, 183,
  -53, -94, 77, -46, -45, -168, 69, -4, 9, 61, 178, -81, -13, -11, -112, 20,
  11, 80, 29, -23, -67, -120, 25, -90, 37, -7, -81, 106, 89, 70, -32, -21,
  101, -15, -51, -131, 39, 55, 3, -29, -29, -118, 165]

theorem fractionalNearFrameSubtreeG1R0149_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG1R0149Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG1R0149Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG1R0149Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG1R0149_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG1R0149LowerBoundTable : List ℤ :=
  [-87, 10, -8, -87, 3, 1, 108, 1, -67, -41, -288, -177, 170, 321, 89, 246,
  -148, -106, 114, 31, -137, -137, -199, 472, 354]

def fractionalNearFrameSubtreeG1R0149LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG1R0149Mask) : ℤ :=
  fractionalNearFrameSubtreeG1R0149LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
