/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Lattice.ADERootMoment

/-!
# Assembly of bounded ADE root-orbit certificates

The generated data supplies one certificate for each regular irreducible ADE
type through rank fifteen.  This module contains the lightweight dependent
assembly that selects one certificate for every occurrence in a component
list.  It is separated from the generated selector so the mathematical
reduction can be rebuilt without scheduling all certificate shards.
-/

namespace SRG266
namespace Lattice

/-- A source of checked root-orbit certificates for regular irreducible ADE
types of rank at most fifteen. -/
abbrev ADEOrbitCertificateSelectorLE15 : Type :=
  ∀ (t : ADEType), t.IsRegular → t.rank ≤ 15 → ADERootOrbitCertificate t

/-- Assemble component certificates recursively, retaining repeated
components as distinct occurrences. -/
noncomputable def adeOrbitFamilyOfSelectorLE15
    (select : ADEOrbitCertificateSelectorLE15) :
    ∀ (ts : List ADEType),
      (∀ t ∈ ts, t.IsRegular) → ADEType.rankSum ts ≤ 15 →
        ADEOrbitFamily ts
  | [], _, _ => PUnit.unit
  | t :: ts, hregular, hrank =>
      (select t (hregular t (by simp)) (by
          simp only [ADEType.rankSum_cons] at hrank
          omega),
        adeOrbitFamilyOfSelectorLE15 select ts
          (fun u hu => hregular u (by simp [hu])) (by
            simp only [ADEType.rankSum_cons] at hrank
            omega))

end Lattice
end SRG266
