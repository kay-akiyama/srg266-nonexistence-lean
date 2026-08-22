/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Hosts.E7E7PlusZDefinitions

/-! # Symmetry check for the rank-15 E7 host -/

namespace SRG266
namespace Lattice

open scoped BigOperators Matrix

theorem e7e7PlusZGram_entries_symm :
    ∀ i j, e7e7PlusZGram i j = e7e7PlusZGram j i := by
  decide +kernel

theorem e7e7PlusZGram_isSymm : e7e7PlusZGram.IsSymm :=
  isSymm_of_entries e7e7PlusZGram e7e7PlusZGram_entries_symm

end Lattice
end SRG266

