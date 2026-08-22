import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G5R0145`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG5R0145Mask : ℕ := 7971842940669202

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG5R0145Witness : Array ℤ :=
  #[-5, -62, 34, -6, -60, 90, -10, 70, 29, 59, -99, 85, 116, 28, -20, 211,
  60, 12, 7, -20, 40, 14, 23, 97, -23, 8, 20, 27, -67, -70, 39, 67, 152, 31,
  92, 96, -43, -114, 92, -52, -94, -21, -2, 57, -11, 2, 57, 235, 81, -68,
  -167, 99, -9, -71, 43, 38, -38, 7, 85, -70, 7, -77, -13, 6, 67, 52, -33,
  39, -123, -16, -5, -66, 7, -212, -35, -75, 255, -64, -55, -133, -1, 162,
  -59, -222, 176, 178, -68, 163, 47, -206, 22, 105, 74, 153, -301, 13, 89,
  90, 112, 60, 56, -111, 14, -164, -69, -25, 42, -16, -49, -55, 273, 203,
  132, -91, -100, -93, 17, -184, 13, -181, -1, -104, -146, 84, -13, -146,
  161, -108, 166, 128, 61, -125, 36, -195, -252, -155, -254, -60, 1, -256,
  -365, 0, -177, 80, 12, -159, 197, 51, 10, 76, -36, -89, 131, 260, 23, -55,
  80, 73, -50, 67, -151, 25, 19, -8, 54, 134, -6, -117]

theorem fractionalNearFrameSubtreeG5R0145_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG5R0145Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG5R0145Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG5R0145Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG5R0145_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG5R0145LowerBoundTable : List ℤ :=
  [-148, -359, -110, 61, 1, 163, 2, 2, -54, 369, -52, -653, -562, -308, 343,
  -46, -258, 170, -198, -37, 411, 927, 404, 19, 197]

def fractionalNearFrameSubtreeG5R0145LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG5R0145Mask) : ℤ :=
  fractionalNearFrameSubtreeG5R0145LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
