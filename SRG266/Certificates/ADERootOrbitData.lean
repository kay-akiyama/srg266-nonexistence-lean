/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.ADERootOrbitDataA
import SRG266.Certificates.ADERootOrbitDataD
import SRG266.Certificates.ADERootOrbitDataE

/-!
# Certified ADE root orbits through rank fifteen

The generated family files contain explicit reflection and negation tables.
This module combines them into a certificate for every regular irreducible
ADE type of rank at most fifteen.  The finite case split below is checked by
the elaborator; the mathematical contents of every selected certificate are
checked by the Lean kernel in the generated modules.
-/

namespace SRG266
namespace Lattice

open ADERootOrbitData

/-- Select a checked finite root-orbit certificate for every regular ADE type
of rank at most fifteen. -/
noncomputable def adeRootOrbitCertificateOfRegularOfRankLE
    (t : ADEType) (hregular : t.IsRegular) (hrank : t.rank ≤ 15) :
    ADERootOrbitCertificate t := by
  cases t with
  | A n =>
      simp only [ADEType.IsRegular, ADEType.rank] at hregular hrank
      interval_cases n <;> simp_all <;>
        first
        | exact certA1 | exact certA2 | exact certA3 | exact certA4
        | exact certA5 | exact certA6 | exact certA7 | exact certA8
        | exact certA9 | exact certA10 | exact certA11 | exact certA12
        | exact certA13 | exact certA14 | exact certA15
  | D n =>
      simp only [ADEType.IsRegular, ADEType.rank] at hregular hrank
      interval_cases n <;> simp_all <;>
        first
        | exact certD4 | exact certD5 | exact certD6 | exact certD7
        | exact certD8 | exact certD9 | exact certD10 | exact certD11
        | exact certD12 | exact certD13 | exact certD14 | exact certD15
  | E6 => exact certE6
  | E7 => exact certE7
  | E8 => exact certE8

end Lattice
end SRG266
