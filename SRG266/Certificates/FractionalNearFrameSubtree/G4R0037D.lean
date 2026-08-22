import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G4R0037`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG4R0037Mask : ℕ := 5441246314957218

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG4R0037Witness : Array ℤ :=
  #[-73, -41, 13, -66, -108, -138, 92, 185, 22, 73, 144, -108, 0, -68, 117,
  0, -105, 8, 0, 62, 39, 11, -38, 43, -23, -112, 130, -10, 48, -4, 12, -192,
  -248, 173, 58, 1, 0, -30, 201, 77, 115, -48, 10, 27, -11, 114, -67, 7,
  -32, 71, 104, -22, -115, 170, -43, 66, 112, -31, -132, 14, -33, 57, 12,
  -59, -5, -29, 177, 7, 94, -136, 94, -205, -164, -58, -51, -58, 209, -3,
  -127, 102, 3, 10, -105, 0, 195, -5, 51, 78, 25, 52, -33, 196, 35, 43, 230,
  -11, 14, 163, 37, -98, -100, 8, 64, 366, 173, -89, -105, 116, 136, 134,
  -40, 37, -162, 103, -9, 100, 102, 24, 0, 96, -192, -85, 165, 8, 72, -60,
  50, -25, -111, 5, -40, -61, 136, 56, -67, -120, 32, 70, -3, -3, -193, -53,
  19, -138, -5, 168, 11, -30, 14, -10, -116, 13, 40, 113, 201, -71, 0, -29,
  57, 57, 46, 48, 54, -70, -193, -25, 187, 5]

theorem fractionalNearFrameSubtreeG4R0037_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG4R0037Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG4R0037Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG4R0037Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG4R0037_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG4R0037LowerBoundTable : List ℤ :=
  [58, 50, 270, 294, -61, 132, -95, 183, 60, 10, 167, 438, -332, 1085, 10,
  275, 421, 427, 182, 467, 9, 8, 112, 99, 292]

def fractionalNearFrameSubtreeG4R0037LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG4R0037Mask) : ℤ :=
  fractionalNearFrameSubtreeG4R0037LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
