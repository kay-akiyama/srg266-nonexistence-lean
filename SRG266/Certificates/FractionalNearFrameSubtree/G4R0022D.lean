import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G4R0022`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0022Mask : ℕ := 4887108405020961

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0022Witness : Array ℤ :=
  #[140, 204, 62, -12, 58, -25, -150, -310, -169, -233, -455, 585, 94, -7,
  -13, -40, -140, -143, -190, -88, 32, 260, 240, 213, 11, -45, -43, -282,
  -217, -68, -9, 23, -96, -87, -197, -197, 349, 295, 14, -27, -104, 256,
  167, 44, -140, 164, -79, 273, 311, -67, -135, -92, -4, -122, -117, -184,
  -6, 413, 161, 390, 143, -428, -22, -312, -84, 112, 23, -221, 388, 148,
  -92, -77, 159, 153, -137, -12, 35, 182, -154, 102, 70, 208, -73, -8, 231,
  445, -68, 144, -87, -225, -193, 65, 226, -89, -54, 85, -93, -61, 69, -206,
  96, -160, 10, 22, -41, -186, 122, -25, 353, -224, -200, 75, -125, 369,
  -33, -80, -180, 155, 200, 56, -293, -86, -48, 217, 174, 360, -20, -336,
  -120, 180, -140, 38, 374, -62, 0, 136, 152, -20, -131, 51, 326, 0, 149, 8,
  -145, 152, 347, 192, -192, 585, 195, -239, 249, 390, 185, -484, -19, -332,
  -81, -177, 11, 260, 155, 116, 85, -51, 147, 70]

theorem fractionalNearFrameSubtreeG4R0022_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0022Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0022Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0022Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0022_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0022LowerBoundTable : List ℤ :=
  [-156, 518, -409, 3, 3, 600, 162, 304, 2, 1596, 800, 607, -330, -127, 356,
  -163, -214, 213, 302, 1472, 64, 360, 587, 1263, 216]

def fractionalNearFrameSubtreeG4R0022LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0022Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0022LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
