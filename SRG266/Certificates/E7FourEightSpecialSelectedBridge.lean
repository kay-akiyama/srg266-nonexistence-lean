/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.E7FourEightSpecialWeightBijective

namespace SRG266
namespace E7FourEightSpecialCrossData

theorem selectedCount_characteristic (s : Finset FirstWeight) :
    selectedCount (characteristic s) = s.card := by
  classical
  rw [selectedCount]
  have hsum :
      (∑ i : Fin 16, if characteristic s i = true then 1 else 0) =
        (Finset.univ.filter fun i : Fin 16 =>
          characteristic s i = true).card := by
    simp
  rw [hsum]
  apply Finset.card_bij (fun i _ => firstWeight i)
  · intro i hi
    simpa [characteristic] using (Finset.mem_filter.mp hi).2
  · intro i _ j _ hij
    exact firstWeight_bijective.1 hij
  · intro w hw
    obtain ⟨i, rfl⟩ := firstWeight_bijective.2 w
    refine ⟨i, ?_, rfl⟩
    simp [characteristic, hw]

end E7FourEightSpecialCrossData
end SRG266
