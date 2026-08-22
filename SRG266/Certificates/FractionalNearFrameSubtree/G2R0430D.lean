import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0430`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0430Mask : ℕ := 5784377821992210

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0430Witness : Array ℤ :=
  #[-95, 341, 143, 31, 74, -74, 33, 143, 7, -23, -64, -3, 29, 135, 61, 0,
  -147, 45, 121, -44, -8, 40, 84, -50, -72, -169, 60, 338, 280, 72, -191,
  -51, -208, -31, -95, 231, 175, 195, -36, -36, 25, -14, 131, 245, 190, 188,
  112, 32, 57, -151, -38, -138, -71, 193, -84, -257, 29, 2, -24, 18, 35,
  -102, 128, -19, -84, -155, -10, -114, -9, -46, -74, 36, -8, 83, 41, -146,
  86, 29, -8, -60, -69, 133, 14, -42, 274, 92, -10, -62, -38, 25, 171, 63,
  -118, -6, 240, 45, -34, 103, 4, -17, 137, 296, 107, -37, -17, 104, 157,
  -19, 149, 97, 46, -242, -98, 142, 79, 175, 78, 84, -153, -52, -26, 97,
  -125, 125, 69, -97, 102, -203, -28, -222, 146, 206, -17, 22, 6, -38, -19,
  -50, 3, -254, 138, 193, 125, -52, -106, -67, 177, 170, 174, 198, 38, -65,
  -357, 125, 105, 80, -78, -177, -329, 22, -85, -204, 51, 64, 285, -159,
  -39, -140]

theorem fractionalNearFrameSubtreeG2R0430_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0430Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0430Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0430Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0430_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0430LowerBoundTable : List ℤ :=
  [56, 2, -94, -42, 244, 86, 465, 519, 105, -48, 491, 391, -462, 607, 286,
  500, 80, -57, 307, 516, 125, 280, 11, 711, 1066]

def fractionalNearFrameSubtreeG2R0430LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0430Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0430LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
