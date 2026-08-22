import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0261`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0261Mask : ℕ := 5368609985176202

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0261Witness : Array ℤ :=
  #[-2, -111, 67, -136, -39, -48, -202, -152, -15, -186, -167, 63, 133, 356,
  249, 336, 70, 129, 60, -62, 25, -3, 140, 57, 148, -58, -6, -144, -41, -34,
  -55, 117, 94, 109, -68, 102, -65, 88, -25, 7, -116, 16, 106, -77, -38,
  -71, 239, 33, -35, -40, -198, -12, -71, 121, 128, -29, -125, 0, -116,
  -147, 377, 43, -303, -217, -179, 198, 46, 346, 133, 82, 2, 1, 17, 75,
  -168, 44, 41, -71, -19, 170, 112, 205, 39, -42, 237, -50, 180, 34, 16,
  -106, -70, 114, 138, -4, -109, 116, 115, -96, 3, -82, 261, -18, 87, 10,
  -24, -195, 43, -40, 62, 77, 153, 70, 100, 159, -124, -72, 176, 73, -78,
  184, 159, -93, -43, 39, -104, 42, 30, 213, 192, 72, 150, 85, 4, 118, 136,
  117, -27, 187, -75, 148, -125, 124, 67, -147, -42, -7, 210, 114, 96, 49,
  -61, 6, 241, -24, 32, -126, 22, -27, -4, 93, -28, 60, -65, 1, 0, -56, 161,
  29]

theorem fractionalNearFrameSubtreeG2R0261_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0261Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0261Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0261Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0261_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0261LowerBoundTable : List ℤ :=
  [302, 484, 206, 567, 369, 1, 62, 481, 275, 572, 261, 1265, 122, 392, -14,
  149, 84, 413, -32, 294, 810, 159, 515, -237, 759]

def fractionalNearFrameSubtreeG2R0261LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0261Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0261LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
