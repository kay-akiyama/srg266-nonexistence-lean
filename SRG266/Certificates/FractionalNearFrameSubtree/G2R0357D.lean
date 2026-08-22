import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0357`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0357Mask : ℕ := 5707403573793542

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0357Witness : Array ℤ :=
  #[-250, 211, 133, 214, -31, 188, 0, -6, -106, -122, 39, 123, 201, 2, -136,
  -38, -375, -8, -207, -196, -76, 26, 92, 267, 152, -34, 204, 203, 33, 203,
  -43, 53, -224, -234, -162, 46, 0, 160, -147, 72, 126, 122, 13, 266, 210,
  98, 227, 37, 6, 48, 132, 28, -128, -149, -58, 63, -87, -192, 53, 127, 71,
  -200, -121, -88, -176, -91, 99, 323, 138, -101, -112, 108, -88, -35, 87,
  221, 212, -34, -47, 69, 93, -69, 157, 184, 197, -194, -124, 106, -201,
  -92, 26, 9, -82, 49, -35, 116, -15, 205, -38, 55, 142, 92, -21, 8, 26,
  -40, -78, -56, 17, 78, 73, 201, -212, -46, 40, 97, 33, 0, -65, -73, 85,
  119, -15, -217, -127, 58, -36, 62, 14, -179, 172, -146, -222, 114, 74,
  -85, 36, -8, 179, -54, 113, 88, 0, 205, -18, -65, 105, 174, 68, -103, 7,
  -49, -57, -34, 16, 35, 189, -211, 65, 54, 68, -16, -111, -2, 26, 30, 94,
  -98]

theorem fractionalNearFrameSubtreeG2R0357_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0357Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0357Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0357Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0357_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0357LowerBoundTable : List ℤ :=
  [13, 40, 90, 34, -60, 164, 643, 2, 171, 57, 295, 458, 280, 11, 848, 423,
  840, -25, -43, -7, -122, 382, -125, 746, -7]

def fractionalNearFrameSubtreeG2R0357LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0357Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0357LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
