import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0026`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0026Mask : ℕ := 1109980908191970

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0026Witness : Array ℤ :=
  #[71, 24, 104, 58, -11, -4, -78, -21, 20, -23, -20, 53, -55, 14, 0, 24,
  83, -237, -15, -50, -110, 51, 99, 48, 116, -113, 78, 24, 39, 128, -36, 80,
  -141, 12, 31, -45, 63, -42, -12, 14, 67, -110, -32, 97, -184, -170, -170,
  -221, 141, -74, -62, 166, 218, 107, -100, -60, 126, 153, 154, -17, 5, 18,
  57, -44, -4, -4, 19, 40, 5, 4, -52, -22, -21, -82, 3, -7, 16, -21, -11, 7,
  181, 86, 26, -4, 0, 70, 55, 2, -39, 91, 75, -9, 59, 29, 33, -6, -34, -10,
  -119, 57, 93, 67, 32, 52, 64, 60, 78, 35, -49, 3, 69, -108, -47, -44, -44,
  63, 10, 79, -56, 88, 27, -49, -2, 30, -40, 2, 21, -6, -34, -15, 43, -74,
  -42, 43, 23, 108, 9, -15, 17, -216, 131, 37, 95, 14, -84, 96, 10, 104, 83,
  44, 15, -121, 91, -74, -108, -116, 8, -34, -38, -31, -1, 19, 38, -24, -24,
  -11, -15, -4]

theorem fractionalNearFrameSubtreeG5R0026_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0026Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0026Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0026Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0026_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0026LowerBoundTable : List ℤ :=
  [10, 42, 2, 182, 2, 68, 135, 142, 2, 125, -61, 202, -18, 244, -91, 168,
  -344, 317, -97, 383, 107, 48, 316, 33, 351]

def fractionalNearFrameSubtreeG5R0026LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0026Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0026LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
