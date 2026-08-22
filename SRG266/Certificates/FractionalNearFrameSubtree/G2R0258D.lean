import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0258`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0258Mask : ℕ := 5356600142896660

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0258Witness : Array ℤ :=
  #[81, 43, 159, 158, 28, -60, -101, 81, -94, -9, -64, 86, -68, -101, -11,
  9, -96, -14, 202, 27, 74, -18, -66, 68, 77, -111, 21, -5, 156, 17, 80,
  137, 42, 89, 38, -58, -160, -75, 88, 65, 107, 14, 8, -298, 45, -59, 42,
  125, 46, 127, 83, 80, -31, 71, 72, -168, -125, -77, 95, -19, 272, 111,
  -51, 207, 189, 22, 197, 312, 145, -16, -16, 56, -53, -27, -18, -151, -53,
  -74, -28, 168, 191, 1, 110, -108, -105, -23, 48, 123, 43, 38, 0, -3, -66,
  -79, 0, 8, -30, 18, -109, 37, 110, 111, 80, 22, 160, 79, 16, 54, -25, 41,
  147, 56, 101, -131, -15, 37, -157, -87, -142, 58, -147, 136, -77, -74, 35,
  -89, -118, -107, 52, -130, 52, 35, 34, -72, 86, -42, -89, 149, 47, 145,
  -101, 130, -63, -6, 77, -67, -74, 64, 86, 59, 12, 149, -5, -30, -31, 149,
  72, 4, -100, 29, 50, -89, -77, 139, -15, -16, 7, 44]

theorem fractionalNearFrameSubtreeG2R0258_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0258Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0258Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0258Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0258_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0258LowerBoundTable : List ℤ :=
  [152, -49, 289, 392, 1, 172, 233, 105, 268, 10, 614, -67, 255, 40, 661,
  -407, 641, -16, 625, 136, 965, -66, -33, 314, 480]

def fractionalNearFrameSubtreeG2R0258LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0258Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0258LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
