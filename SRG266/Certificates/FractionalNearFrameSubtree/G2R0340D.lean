import SRG266.QuasiSymmetric.FractionalNearFrameSubtreeAudit
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/

/-!
# Certificate data for `G2R0340`
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The rooted near normal form. -/
def fractionalNearFrameSubtreeG2R0340Mask : ℕ := 5645702115079177

/-- Integer weights on the 168 intersecting row pairs. -/
def fractionalNearFrameSubtreeG2R0340Witness : Array ℤ :=
  #[-142, -609, -285, -624, -572, -947, -255, -115, -3, 105, 237, 172, 620,
  869, 408, 509, 487, 479, 196, -64, -57, 61, -300, 7, 389, 325, 398, 299,
  -181, -435, 67, -161, 288, -23, 52, -444, 60, 179, -13, -332, 18, 286,
  -287, -105, 439, -109, 182, -315, 395, 3, 549, -147, -149, 157, 364, -234,
  94, 263, 59, 265, 254, 28, -152, 312, -135, 112, 203, 0, -242, -33, -234,
  333, 9, 115, -9, -133, 34, 112, 236, 512, 235, 132, 180, 96, 47, 216, -15,
  12, 144, 118, -153, 132, -54, 122, -28, 203, -73, 415, 1, 67, -87, 489,
  269, 271, 1, 389, 17, -462, -417, -258, 111, -1, -117, -302, 3, 264, 234,
  -85, 127, -31, 16, -49, -241, 82, 180, 466, 14, -210, 168, 89, -194, -397,
  42, -9, 24, 210, -187, 233, 96, -29, 64, -96, -5, 308, 148, -124, -397,
  -19, 102, -122, -11, -16, 68, -87, -49, 147, -414, -148, -179, 178, 25,
  -130, -51, 185, -24, -30, 395, 483]

theorem fractionalNearFrameSubtreeG2R0340_endpointCount :
    (compactEndpointMasks fractionalNearFrameSubtreeG2R0340Mask).length = 25 := by
  decide +kernel

/-- Typed endpoint index. -/
def fractionalNearFrameSubtreeG2R0340Endpoint (k : Fin 25) :
    CompactEndpointIndex fractionalNearFrameSubtreeG2R0340Mask :=
  ⟨k.val, by rw [fractionalNearFrameSubtreeG2R0340_endpointCount]; exact k.isLt⟩

/-- Per-endpoint lower bounds on the indexed pair objective. -/
def fractionalNearFrameSubtreeG2R0340LowerBoundTable : List ℤ :=
  [179, 2, 696, 852, -33, 236, 2, 1068, 575, 52, -171, -62, -142, 303, 1354,
  871, 837, 197, -15, 1556, 1370, 406, 201, -494, 2459]

def fractionalNearFrameSubtreeG2R0340LowerBound (endpoint : CompactEndpointIndex fractionalNearFrameSubtreeG2R0340Mask) : ℤ :=
  fractionalNearFrameSubtreeG2R0340LowerBoundTable.getD endpoint.val 0

end SRG266.Certificates
