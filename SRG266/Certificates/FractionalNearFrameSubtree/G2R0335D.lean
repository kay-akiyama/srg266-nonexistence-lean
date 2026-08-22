import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0335`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0335Mask : ℕ := 5638212631833609

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0335Witness : Array ℤ :=
  #[-229, -235, -103, -153, -203, -325, -39, 106, 93, 130, 105, 136, 127,
  -30, 99, 89, 70, 56, 150, -85, -53, -22, -153, -66, -47, -59, -26, 113,
  35, 29, 280, -27, -10, -26, 17, -21, -196, 17, 101, -52, -23, -154, -40,
  -213, 207, -68, -146, 5, 42, 72, -14, 20, -10, 109, 93, 5, 74, 134, -78,
  -81, 96, 51, 81, 85, -172, 0, -55, 30, -89, 182, 40, -136, -27, 48, 120,
  30, -35, 99, 0, 31, -9, -22, -60, 153, 46, -80, -29, 0, 121, 0, 106, 1,
  91, -76, 53, -100, 31, -135, 74, -77, 91, 59, 61, -45, 130, -22, 153, -24,
  107, 38, 53, 46, -48, -16, -132, 0, -91, 27, -5, 144, -108, 26, 119, 140,
  80, 55, 127, -68, 39, 31, -20, 52, -64, 56, 30, 62, -42, 72, 29, -29, 0,
  -15, 108, 19, 41, 33, -81, 26, -78, 145, -34, -57, -27, -38, -122, 26, 42,
  -77, 10, 91, -5, -11, -12, -82, -109, -103, 5, -116]

theorem fractionalNearFrameSubtreeG2R0335_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0335Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0335Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0335Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0335_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0335LowerBoundTable : List ℤ :=
  [-126, -107, 2, 53, -67, 26, -162, 163, 2, 11, 357, 11, 422, 178, 37, 191,
  -60, 137, 501, 111, 11, -4, 117, 8, 898]

def fractionalNearFrameSubtreeG2R0335LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0335Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0335LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
