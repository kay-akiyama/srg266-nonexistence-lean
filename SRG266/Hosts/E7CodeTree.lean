/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.E7ComponentCode

/-!
# A literal search tree over packed component codes

The coverage sweep tests each of the 120,036 enumerated profiles against the
5,253 listed component codes.  A linear scan would dominate the sweep, so the
codes are stored in a balanced binary search tree of natural numbers and
looked up with about thirteen GMP-accelerated comparisons.

No ordering invariant is assumed.  `E7CodeTree.mem_toList_of_contains` only
uses that a successful lookup returns along a path of the tree, so the tree is
allowed to be an arbitrary literal; a badly shaped tree can only make lookups
fail, never succeed wrongly.
-/

namespace SRG266

/-- A literal binary search tree of packed component codes. -/
inductive E7CodeTree where
  /-- The empty tree. -/
  | leaf : E7CodeTree
  /-- A node carrying one code, with smaller codes to the left. -/
  | node : E7CodeTree → ℕ → E7CodeTree → E7CodeTree

namespace E7CodeTree

/-- Search a code in the tree. -/
def contains : E7CodeTree → ℕ → Bool
  | leaf, _ => false
  | node left value right, code =>
      if code = value then true
      else if code < value then left.contains code
      else right.contains code

/-- The codes stored in the tree, in symmetric order. -/
def toList : E7CodeTree → List ℕ
  | leaf => []
  | node left value right => left.toList ++ value :: right.toList

theorem mem_toList_of_contains :
    ∀ (tree : E7CodeTree) (code : ℕ), tree.contains code = true → code ∈ tree.toList
  | leaf, code, hcode => by simp [contains] at hcode
  | node left value right, code, hcode => by
      simp only [contains] at hcode
      split at hcode
      · rename_i heq
        subst heq
        simp [toList]
      · split at hcode
        · exact List.mem_append_left _ (mem_toList_of_contains left code hcode)
        · exact List.mem_append_right _
            (List.mem_cons_of_mem _ (mem_toList_of_contains right code hcode))

end E7CodeTree

end SRG266
