import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G3R0155`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG3R0155Mask : ℕ := 6850425814043800

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG3R0155Witness : Array ℤ :=
  #[-3, -131, -77, -29, -11, 80, 73, 112, 203, 276, 97, 28, 0, 15, 151, 156,
  18, 116, 22, -5, -20, -31, 30, 69, -41, -68, 0, 20, 55, 93, 68, 64, 30,
  -73, -186, 144, 51, -25, -121, -134, 55, 7, 51, -72, -122, 102, 186, 196,
  -73, -165, -13, 153, -42, 16, -109, -20, 69, -115, 46, 101, 152, -114, 11,
  11, 46, 39, -21, 56, 18, 0, 43, -69, 57, 41, -21, 47, 37, -48, -7, -50,
  157, 140, 52, 38, 120, 165, 109, 128, 88, 6, -49, -72, 167, -106, 49, 115,
  120, 117, -40, -107, 32, 36, 192, -18, -33, 27, 129, -47, 6, 46, 39, -16,
  22, -75, -74, 81, -192, -50, 100, 166, 5, 51, -6, 59, 66, 9, -100, -11,
  29, 29, 138, 106, 116, -24, -113, 39, 7, 44, -34, 44, -23, 42, 124, 10,
  54, -178, -96, 19, -10, 133, 0, -59, 100, -61, -119, 113, 124, 0, 140,
  -132, 165, 82, -6, 8, 150, -20, -20, 9]

theorem fractionalNearFrameSubtreeG3R0155_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG3R0155Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG3R0155Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG3R0155Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG3R0155_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG3R0155LowerBoundTable : List ℤ :=
  [230, 242, 256, 297, 213, 360, 160, 234, 327, 513, -150, 177, 479, 303,
  232, 297, 200, 690, 782, 263, 10, 676, 77, 404, 507]

def fractionalNearFrameSubtreeG3R0155LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG3R0155Mask) : ℤ :=
  fractionalNearFrameSubtreeG3R0155LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
