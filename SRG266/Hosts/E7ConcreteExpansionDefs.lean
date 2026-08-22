/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.E7ConcreteFilterData
import SRG266.Hosts.E7ConcreteEnumeration

/-!
# Vocabulary for the concrete E7 profile expansion

The filtering sweep of `SRG266/Certificates/E7ConcreteFilterAssembly.lean`
produces the 335 enumerated component profiles whose component key is one of
the 37 keys carried by the 43 listed histogram key pairs.  This module names
the derived objects that the kernel checks operate on:

* `e7ConcreteFibre` — the fibre of one packed component code, as a filter of
  the surviving profiles;
* `e7ConcreteFibreOf` — the same fibre, read off the listed table;
* `e7ConcreteExpansion` — the expansion of the 43 listed key pairs;
* `e7PairEncode` — a packed encoding of a canonical profile pair, used *only*
  as a sort key, so no property of it is ever needed.
-/

namespace SRG266

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The surviving profiles whose packed component code is `code`. -/
def e7ConcreteFibre (code : ℕ) : List (Array ℤ) :=
  e7ConcreteRelevantProfiles.filter fun profile =>
    decide (e7FastComponentCode profile = code)

/-- The fibre of `code` read off the listed table. -/
def e7ConcreteFibreOf (code : ℕ) : List (Array ℤ) :=
  match e7ConcreteFibreTable.find? fun entry => decide (entry.1 = code) with
  | some entry => entry.2
  | none => []

/-- The expansion of the 43 listed key pairs, from the listed fibres. -/
def e7ConcreteExpansion : List E7ComponentArrayPair :=
  e7ConcreteCodePairs.flatMap fun codes =>
    (e7ConcreteFibreOf codes.1).flatMap fun left =>
      (e7ConcreteFibreOf codes.2).map fun right =>
        e7CanonicalComponentArrayPair left right

/-- A coordinate of an enumerated component profile, shifted to be positive. -/
def e7CoordCode (z : ℤ) : ℕ := (z + 64).toNat

/-- The eight coordinates of a profile, packed into one natural number. -/
def e7ArrayEncode (profile : Array ℤ) : ℕ :=
  profile.foldl (fun code z => code * 128 + e7CoordCode z) 0

/-- A canonical profile pair, packed into one natural number.  This is used
only as a sort key: the kernel compares the *pairs* themselves, so no
injectivity is ever assumed. -/
def e7PairEncode (pair : E7ComponentArrayPair) : ℕ :=
  e7ArrayEncode pair.1 * 128 ^ 8 + e7ArrayEncode pair.2

/-- One shifted coordinate, read back from a packed encoding. -/
def e7CoordDecode (digit : ℕ) : ℤ := (digit : ℤ) - 64

/-- The eight coordinates of a profile, read back from a packed encoding. -/
def e7ArrayDecode (code : ℕ) : Array ℤ :=
  ((List.range 8).reverse.map fun k => e7CoordDecode (code / 128 ^ k % 128)).toArray

/-- A canonical profile pair, read back from a packed encoding.  Only the
round trip `e7PairDecode (e7PairEncode x) = x`, checked element by element, is
ever used, so the decoder needs no correctness proof of its own. -/
def e7PairDecode (code : ℕ) : E7ComponentArrayPair :=
  (e7ArrayDecode (code / 128 ^ 8), e7ArrayDecode (code % 128 ^ 8))

/-- The packed encodings of the listed canonical profile pairs. -/
def e7ConcreteListedCodes : List ℕ :=
  e7ListedCanonicalArrayPairs.map e7PairEncode

/-- Linear distinctness test for a list of packed encodings. -/
def e7NatDistinct : List ℕ → Bool
  | [] => true
  | code :: codes => !codes.contains code && e7NatDistinct codes

/-- A list passing `e7NatDistinct` has no repetitions. -/
theorem e7NatDistinct_nodup :
    ∀ codes : List ℕ, e7NatDistinct codes = true → codes.Nodup := by
  intro codes
  induction codes with
  | nil => intro _; exact List.nodup_nil
  | cons code codes ih =>
      intro hcodes
      simp only [e7NatDistinct, Bool.and_eq_true, Bool.not_eq_true'] at hcodes
      refine List.nodup_cons.mpr ⟨?_, ih hcodes.2⟩
      intro hmem
      have hcontains : codes.contains code = true := by simpa using hmem
      rw [hcontains] at hcodes
      exact Bool.noConfusion hcodes.1

/-- A packed encoding found among the encodings of `l` comes from an element
of `l`, provided both sides survive the decoding round trip. -/
theorem e7Pair_mem_of_code_mem (l : List E7ComponentArrayPair)
    (hround : ∀ y ∈ l, e7PairDecode (e7PairEncode y) = y)
    (x : E7ComponentArrayPair) (hx : e7PairDecode (e7PairEncode x) = x)
    (hmem : e7PairEncode x ∈ l.map e7PairEncode) : x ∈ l := by
  rw [List.mem_map] at hmem
  obtain ⟨y, hy, hcode⟩ := hmem
  have hyx : y = x := by rw [← hround y hy, hcode, hx]
  exact hyx ▸ hy

end SRG266
