import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0363`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0363Mask : ℕ := 5714010151560458

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0363Witness : Array ℤ :=
  #[-165, 71, 51, -79, -160, 22, 319, 561, 483, 565, 530, -336, -212, -276,
  -368, -489, 2, 212, -172, -271, -233, -195, -61, -62, -94, -45, 166, 360,
  291, 230, 307, 29, -54, -53, -24, -167, 4, -64, -64, -212, -114, 96, 179,
  190, 178, 482, 121, 91, -52, 91, -30, -225, -83, -158, -25, 231, -37, 363,
  285, -291, 114, 111, -319, -192, 275, 253, -388, -117, -105, -503, 59,
  -97, -94, -119, -39, -52, 10, -79, 164, 60, 128, 140, 55, 185, -77, 172,
  -76, -20, 137, 98, 14, 88, 9, 17, 32, 85, 181, 150, 72, 127, -86, 336, 84,
  97, 199, -43, 52, 30, -148, 29, -49, -84, 32, 88, 18, 100, -48, 40, 64,
  -136, -33, 83, -96, -24, 125, 151, -25, 211, -304, -104, 91, 88, 167, -96,
  8, 87, 33, 110, -129, 37, -34, 3, -47, -212, 125, -1, 129, 128, -85, -20,
  -38, -59, -58, 45, 22, 23, -176, -63, -41, -22, -15, 283, -109, 70, 60,
  -40, 18, 14]

theorem fractionalNearFrameSubtreeG2R0363_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0363Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0363Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0363Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0363_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0363LowerBoundTable : List ℤ :=
  [124, 2, 394, 233, 68, 333, 571, -121, -70, 13, 331, 277, -426, 1033, 686,
  226, 273, 104, 86, 365, -152, 394, 10, 1241, 10]

def fractionalNearFrameSubtreeG2R0363LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0363Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0363LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
