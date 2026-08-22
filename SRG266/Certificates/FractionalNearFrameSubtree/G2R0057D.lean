import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0057`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0057Mask : ℕ := 939862479192482

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0057Witness : Array ℤ :=
  #[-65, 36, 50, 51, 93, 144, 57, -99, 22, 131, 78, -38, -37, -130, -28, 0,
  -97, 15, -9, -96, -51, 62, -66, 95, 8, 31, 32, -45, 64, -12, -64, -102,
  -60, -78, 93, 162, 139, 120, 42, -82, 116, 63, -31, -28, 0, -20, -33, 82,
  46, 20, 49, 80, -54, -48, 128, -19, -60, -104, -55, 0, 69, 165, -34, 37,
  -45, 59, 69, 157, 81, 8, 22, 65, 25, 117, 44, 40, -146, 104, 1, 91, 72,
  -41, -100, -52, 51, -6, 113, 19, 70, -84, 63, -109, 36, 29, 28, -12, -84,
  -29, -7, -97, -70, -92, -109, 0, 21, -26, 18, 96, 19, 46, 62, -12, -100,
  22, 36, -14, 12, -71, 5, -66, -96, 0, 6, 40, -118, -77, 155, 16, -26, 56,
  82, 60, -7, -92, 12, -35, -14, -74, -105, -30, -70, 67, 84, -43, -116,
  -11, -97, -41, -149, -133, -128, 80, 31, 0, 0, 61, -11, 89, 96, -51, -45,
  30, 68, 73, 170, 29, -15, 74]

theorem fractionalNearFrameSubtreeG2R0057_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0057Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0057Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0057Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0057_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0057LowerBoundTable : List ℤ :=
  [-86, -72, 112, 5, -89, 104, -68, 230, 53, -56, -247, 357, -109, 10, 110,
  372, 389, 183, 477, 148, 34, -273, 400, -19, 444]

def fractionalNearFrameSubtreeG2R0057LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0057Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0057LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
