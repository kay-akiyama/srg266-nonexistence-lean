/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.E7FourEightSpecialAllowedAtBridge

namespace SRG266
namespace E7FourEightSpecialCrossData

theorem allowedCount_characteristic (s : Finset FirstWeight) :
    allowedCount (characteristic s) = (crossAllowed s).card := by
  classical
  rw [allowedCount]
  have hsum :
      (∑ j : Fin 16,
        if allowedAt (characteristic s) j then 1 else 0) =
        (Finset.univ.filter fun j : Fin 16 =>
          allowedAt (characteristic s) j).card := by
    simp
  rw [hsum]
  apply Finset.card_bij (fun j _ => firstWeight j)
  · intro j hj
    exact (allowedAt_characteristic_iff s j).mp
      (Finset.mem_filter.mp hj).2
  · intro i _ j _ hij
    exact firstWeight_bijective.1 hij
  · intro w hw
    obtain ⟨j, rfl⟩ := firstWeight_bijective.2 w
    refine ⟨j, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (allowedAt_characteristic_iff s j).mpr hw

end E7FourEightSpecialCrossData
end SRG266
