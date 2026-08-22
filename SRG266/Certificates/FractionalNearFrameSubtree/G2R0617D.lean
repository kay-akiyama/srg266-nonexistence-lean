import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0617`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0617Mask : ℕ := 9609579902522385

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0617Witness : Array ℤ :=
  #[122, 129, 142, 72, -35, 67, 0, 36, -37, -12, -11, -166, 78, -80, -84,
  64, -71, -207, -191, 29, 117, -13, -98, 9, 24, 65, 91, 84, -4, -36, -78,
  125, -52, 4, 39, -45, -210, -1, -60, -1, 78, -31, 13, 44, 182, 13, -150,
  53, 65, -34, 20, -15, 48, -42, 3, 59, -14, 65, 7, 111, 37, -142, -61, 15,
  39, -31, 2, -143, 78, 9, -15, 37, 70, -19, 7, 28, 29, -21, 20, -38, 82,
  -5, -121, 23, -188, 162, 75, 124, 22, 33, 69, 76, 102, 75, 59, -68, -19,
  9, -57, 30, 86, -6, 62, -10, 117, 96, 104, 110, -54, 99, -62, -74, -23,
  -158, 116, 46, 78, -67, -19, 65, 3, -46, -33, -113, 0, 38, 2, 95, 35,
  -113, -12, 43, -34, 18, 10, 0, -82, 137, -42, -91, 58, -41, -139, 22, -79,
  -48, -92, 100, 48, 29, 34, 50, 47, 44, -67, -128, -42, -54, -15, 44, -56,
  28, 13, -46, 1, 36, 111, 0]

theorem fractionalNearFrameSubtreeG2R0617_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0617Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0617Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0617Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0617_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0617LowerBoundTable : List ℤ :=
  [-2, 1, 72, 65, -94, -171, 2, 190, 215, 62, -59, -66, 10, 473, 202, 11,
  151, 172, 324, 317, 97, 25, 338, -33, -115]

def fractionalNearFrameSubtreeG2R0617LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0617Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0617LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
