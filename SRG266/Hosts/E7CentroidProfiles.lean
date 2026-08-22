/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.E7CentroidData
import SRG266.Certificates.E7CentroidTransportData

/-!
# Lightweight E7 centroid profile list

This module combines the rejected centroid profiles with the surviving
Weyl-transported profiles.  It deliberately imports only source data, not the
kernel Farkas audit, so the large native scalar-DP computation can consume the
956 profile pairs without inheriting audit proof data.
-/

namespace SRG266

/-- Pairs of centroid arrays covered by either a Farkas separator or a
checked survivor Weyl witness. -/
def e7ListedCentroidProfiles :
    List ((Fin 8 → ℤ) × (Fin 8 → ℤ)) :=
  List.map (fun c => (c.y₁, c.y₂))
      e7GeneratedCentroidCertificates ++
    List.map (fun c => (c.y₁, c.y₂))
      e7GeneratedSurvivorOrbitCertificates

end SRG266
