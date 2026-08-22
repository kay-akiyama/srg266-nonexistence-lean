import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G5R0035`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0035Mask : ℕ := 1399762896789577

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0035Witness : Array ℤ :=
  #[4, 9, 12, 61, 14, -6, 44, 89, 25, 47, 34, -51, -53, -124, -67, -69, -28,
  -29, -32, 47, -45, 0, -57, 25, 40, 38, 22, 18, 30, 20, 36, 0, -27, 55,
  102, 5, 26, 52, -12, -3, -8, -98, 4, 53, -84, 2, -44, -30, 101, -18, 5,
  13, -12, -4, 31, -58, 85, -53, -35, -6, 70, 83, -29, 17, 13, -26, -10,
  -52, -5, -7, 7, -89, 13, 8, -21, 15, -8, 35, 68, -122, -31, -12, 27, 14,
  -74, -64, -6, 47, 0, -3, -14, 0, 52, -45, 18, 32, -19, -15, -40, -54, -36,
  27, 15, 26, 38, -15, -39, 42, -9, -35, -25, -31, 2, -8, 21, -36, -15, -80,
  28, -28, -10, 53, -54, -4, -7, -8, 5, 10, -66, 95, -70, 37, -11, -53, -47,
  15, 53, 25, -46, 58, 39, -5, 83, 5, -83, 35, -41, -7, 51, 36, 56, 14, -42,
  -41, -29, -15, -16, 16, 21, -15, -66, 62, 31, 44, 1, 30, 0, 36]

theorem fractionalNearFrameSubtreeG5R0035_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0035Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0035Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0035Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0035_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0035LowerBoundTable : List ℤ :=
  [-73, -10, 3, -51, -35, -21, 11, 48, -56, 60, -198, 37, 139, 105, 22, -47,
  -205, 10, 128, 108, -64, 198, 64, 48, 27]

def fractionalNearFrameSubtreeG5R0035LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0035Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0035LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
