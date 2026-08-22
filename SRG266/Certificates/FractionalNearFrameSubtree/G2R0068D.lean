import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0068`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0068Mask : ℕ := 957042742117522

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0068Witness : Array ℤ :=
  #[79, 110, 93, 12, 156, 35, -51, 4, -77, 32, -156, 0, -2, 57, 20, -192,
  -76, -30, -20, -118, -88, 54, 42, 82, 20, 53, 115, 15, -32, 83, -32, 149,
  -69, -6, 14, 102, 114, 54, -108, -22, 62, 86, 29, -32, 162, 45, 63, 28,
  48, 73, 108, -100, -73, -212, 2, 138, 184, -50, 64, 145, -135, 11, -24,
  -13, 25, -174, -6, -4, 46, -40, -31, -26, 129, 168, -17, -52, 61, 192,
  -28, -91, -85, 209, 121, -137, -186, -165, -102, -35, 51, -11, -64, -71,
  145, 5, 66, 16, 81, -28, 6, 17, 11, -68, 152, -22, 47, -24, -64, 77, 0,
  144, 0, 84, -140, -21, 6, -19, -1, 27, -5, 115, -8, 52, 2, 54, -130, -60,
  115, 119, -20, -187, -123, -36, 102, 109, 155, 41, -10, -9, 165, 12, -37,
  217, 37, -54, 86, -13, 8, -92, -8, 54, -35, 169, 15, 57, 72, -33, 125,
  -170, -93, -62, 132, 43, 100, 14, -62, -137, 14, -173]

theorem fractionalNearFrameSubtreeG2R0068_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0068Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0068Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0068Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0068_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0068LowerBoundTable : List ℤ :=
  [-28, 119, 2, 197, 16, 159, 233, 214, 113, 10, 717, -14, 118, -169, 365,
  -226, 387, 157, -29, 452, 9, 415, 8, 230, 185]

def fractionalNearFrameSubtreeG2R0068LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0068Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0068LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
