import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0455`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0455Mask : ℕ := 5794879015013528

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0455Witness : Array ℤ :=
  #[56, 54, 6, 22, -67, -153, -87, -47, -18, -141, -141, 104, -1, 130, 20,
  121, -82, 110, -40, 37, 35, 70, -140, -20, 32, -85, -89, -143, 50, 92, 10,
  40, -51, 43, 48, -14, -87, 18, -22, -50, -94, -4, 62, 115, 2, 67, -76, 55,
  -19, 33, -36, -39, 0, -92, -30, -34, 42, 104, 152, 173, -29, 32, 76, 145,
  6, 69, 65, -43, -22, -26, 47, 77, 13, 57, -104, -29, 24, -71, 25, 81, -38,
  9, 145, -20, 117, 1, -102, 27, -6, -133, 11, 43, 84, 76, -26, -42, 91, 64,
  -3, -34, 87, -60, 37, 28, 65, -62, 40, 17, 150, 45, 73, -11, -63, 131,
  107, -22, 48, -150, -53, 36, 85, 32, -37, 78, 90, 81, -24, 12, -124, 53,
  91, -15, -148, 11, -58, 73, 14, -39, 98, 45, 37, 42, -231, 60, -42, -34,
  128, 33, 29, -138, 58, -54, 36, 84, 11, 223, 116, -18, 91, 93, 124, 126,
  12, 66, -58, 142, 87, 128]

theorem fractionalNearFrameSubtreeG2R0455_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0455Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0455Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0455Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0455_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0455LowerBoundTable : List ℤ :=
  [98, 349, 458, 133, 2, 66, 257, 53, -2, 536, 328, 66, 328, 330, 9, 522,
  207, 76, 96, 379, -184, 102, 116, 646, 127]

def fractionalNearFrameSubtreeG2R0455LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0455Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0455LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
