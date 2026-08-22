/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Hosts.E7E7PlusDefinitions

namespace SRG266
namespace Lattice

theorem e7e7PlusGram_entries_symm :
    ∀ i j, e7e7PlusGram i j = e7e7PlusGram j i := by
  decide +kernel

theorem e7e7PlusGram_isSymm : e7e7PlusGram.IsSymm :=
  isSymm_of_entries e7e7PlusGram e7e7PlusGram_entries_symm

end Lattice
end SRG266
