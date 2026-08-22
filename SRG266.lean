/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.FractionalNearFrameMain

/-!
# There is no strongly regular graph with parameters `(266, 45, 0, 9)`

`SRG266.srg266_nonexistence` is the headline result: no finite simple graph
satisfies `SRG266.IsHypothetical`, the predicate spelling out the parameter
set `(266, 45, 0, 9)`.  The proof is checked by the Lean kernel alone --
`#print axioms SRG266.srg266_nonexistence` lists `propext`,
`Classical.choice` and `Quot.sound` and nothing else.
-/
