import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Certificate data for `G2R0316`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0316Mask : ℕ := 5389413972019816

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0316Witness : Array ℤ :=
  #[69, 11, 117, -60, -26, 12, -88, -104, -69, -188, 190, 6, 97, 32, 38,
  -25, 35, 30, 0, 0, -33, 60, -23, -13, -129, -165, -5, -114, 146, -17, 68,
  -66, 160, 124, -133, -104, -192, 196, 164, 0, -172, -138, 141, 78, 59,
  -98, 38, 27, -35, -55, -79, -41, 66, 118, 44, 12, -135, -28, 14, -23, -96,
  28, 118, 76, -78, 40, -89, -36, -171, 83, -23, 31, 138, -41, 40, 79, 101,
  -43, -14, -56, 99, 4, -32, 118, 1, 23, 43, 7, -129, -76, -66, 25, -112,
  31, 43, 37, 0, 98, 94, 44, -104, 42, -25, -80, 3, 92, 52, -25, -46, 96,
  46, -68, 17, -84, -103, -150, -133, 37, 65, -88, 63, 92, -19, -100, 5, 4,
  -112, 80, -143, -20, 84, -7, 39, -6, -100, -67, -148, 169, 21, -187, 125,
  69, 22, 132, 68, 98, -29, -52, -62, 124, 19, 61, 97, 101, -106, -152, 20,
  -2, 26, -152, 163, 123, 8, 100, -96, 56, -78, 56]

theorem fractionalNearFrameSubtreeG2R0316_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0316Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0316Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0316Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0316_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0316LowerBoundTable : List ℤ :=
  [-126, 3, 2, 2, -228, -51, -151, 3, 136, 12, 417, 51, 444, 11, 390, 121,
  454, 40, 11, 44, -149, -110, -219, -111, 237]

def fractionalNearFrameSubtreeG2R0316LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0316Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0316LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
