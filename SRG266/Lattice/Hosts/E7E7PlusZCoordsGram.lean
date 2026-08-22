/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.Hosts.E7E7PlusZCoordsGramA
import SRG266.Lattice.Hosts.E7E7PlusZCoordsGramB
import SRG266.Lattice.Hosts.E7E7PlusZCoordsGramC
import SRG266.Lattice.Hosts.E7E7PlusZCoordsGramD

namespace SRG266
namespace Lattice

theorem e7e7PlusZCoords_gram :
    ∀ i j, (e7e7PlusZCoords * e7e7PlusZCoords.transpose) i j =
      4 ^ 2 * e7e7PlusZGram i j := by
  intro i j
  fin_cases i
  · exact e7e7PlusZCoords_gram_row_0 j
  · exact e7e7PlusZCoords_gram_row_1 j
  · exact e7e7PlusZCoords_gram_row_2 j
  · exact e7e7PlusZCoords_gram_row_3 j
  · exact e7e7PlusZCoords_gram_row_4 j
  · exact e7e7PlusZCoords_gram_row_5 j
  · exact e7e7PlusZCoords_gram_row_6 j
  · exact e7e7PlusZCoords_gram_row_7 j
  · exact e7e7PlusZCoords_gram_row_8 j
  · exact e7e7PlusZCoords_gram_row_9 j
  · exact e7e7PlusZCoords_gram_row_10 j
  · exact e7e7PlusZCoords_gram_row_11 j
  · exact e7e7PlusZCoords_gram_row_12 j
  · exact e7e7PlusZCoords_gram_row_13 j
  · exact e7e7PlusZCoords_gram_row_14 j

end Lattice
end SRG266

