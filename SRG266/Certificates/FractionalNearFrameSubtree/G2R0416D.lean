import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0416`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0416Mask : ℕ := 5748628675846552

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0416Witness : Array ℤ :=
  #[-26, -57, 53, 33, 26, -8, -13, 26, 42, -2, 39, -8, -63, 30, 21, 53, 12,
  1, 17, -9, 21, 40, -44, 39, -100, -5, -14, -25, -47, 28, -68, 27, 18, 29,
  51, 6, -98, -35, 22, 71, 22, 115, 29, -37, 23, 70, -63, -65, -34, 99, 20,
  75, -72, -84, -68, -77, -13, 35, 19, -83, 8, 21, 22, 79, 51, 16, 39, 40,
  9, 88, 3, 5, -123, 23, 25, -53, -29, 56, -7, 61, -19, 25, -59, -16, 18,
  -18, 22, -5, 62, 40, 30, 33, 7, 32, -10, 3, 54, 51, 5, 6, -7, 91, 19, 91,
  94, -35, 19, -59, -69, -47, 24, -68, -15, 3, 26, -5, -51, -65, -5, 14,
  -36, 43, 8, 62, 16, -29, 10, -4, 72, 56, 4, 15, 20, -35, 29, 30, -9, -36,
  -2, -34, 11, -34, -28, -12, -52, 53, -69, 23, 49, 44, -2, -60, -59, 8, 41,
  50, 39, 82, -38, 0, -29, 6, 30, 22, 45, 109, -3, 12]

theorem fractionalNearFrameSubtreeG2R0416_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0416Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0416Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0416Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0416_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0416LowerBoundTable : List ℤ :=
  [-5, 41, 151, 97, 114, 117, -64, 1, 3, 210, 48, -107, -127, 157, -45, 9,
  89, 290, 325, 346, 136, 3, 11, 143, 253]

def fractionalNearFrameSubtreeG2R0416LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0416Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0416LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
