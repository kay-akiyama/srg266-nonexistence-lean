/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.NormNum

/-!
# A reduced-search framework over bitmasks

This file supplies two pieces of search-completeness machinery:

* `SRG266.Search.maskDFS` — an increasing-index depth-first enumeration of the
  submasks of `Fin n` under a pruning predicate, together with
  `SRG266.Search.maskDFS_complete`: a mask that passes every pruning test along
  its own path and is accepted *is* in the returned list.  Combined with one
  `decide +kernel` equation `maskDFS step accept n = listed`, this turns a
  pruned kernel search into the statement "every solution is listed".
* `SRG266.Search.cliqueDFS` — a bitmask clique search with
  `SRG266.Search.cliqueDFS_sound`: a `false` answer refutes the existence of a
  clique of the requested size.

Both are stated for arbitrary user-supplied predicates, so nothing here is
specific to the graph `srg(266,45,0,9)`.

## Representation

Kernel-hot lookup tables are stored as packed natural numbers rather than
arrays.  `atMost` compares a population count without computing it, and
`rowDFS` prunes both branches using precomputed per-position data.

## Main results

* `SRG266.Search.popcount_correct`
* `SRG266.Search.maskDFS_complete`, `SRG266.Search.maskDFS_complete_of_hereditary`
* `SRG266.Search.maskDFS_accept`
* `SRG266.Search.cliqueDFS_sound`
* `SRG266.Search.atMost_eq_true_iff`, `SRG266.Search.zeroOrThree_of_card`
* `SRG266.Search.rowDFS_mem`
-/

namespace SRG266.Search

/-! ## Bit cardinality

`bitCard n k` is the mathematical specification: the number of set bits of `n`
strictly below position `k`.  It is a `Finset.card`, so it is the shape a
consumer wants when bounding the size of a set of vertices by a mask.
-/

/-- The number of set bits of `n` at positions `< k`. -/
def bitCard (n k : ℕ) : ℕ :=
  ((Finset.range k).filter fun i => n.testBit i = true).card

@[simp] theorem bitCard_zero (n : ℕ) : bitCard n 0 = 0 := by
  simp [bitCard]

@[simp] theorem zero_bitCard (k : ℕ) : bitCard 0 k = 0 := by
  simp [bitCard]

theorem bitCard_succ (n k : ℕ) :
    bitCard n (k + 1) = (if n.testBit 0 = true then 1 else 0) + bitCard (n / 2) k := by
  classical
  simp only [bitCard, Finset.card_filter]
  rw [Finset.sum_range_succ']
  simp only [Nat.testBit_succ]
  exact Nat.add_comm _ _

/-- Splitting the window `[0, k + m)` at `k`: the low bits are the bits of
`n % 2 ^ k` and the high bits are the bits of `n / 2 ^ k`. -/
theorem bitCard_add (n k m : ℕ) :
    bitCard n (k + m) = bitCard (n % 2 ^ k) k + bitCard (n / 2 ^ k) m := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
      have hsplit : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by
        rw [pow_succ]; exact Nat.mul_comm _ _
      have hmod : n % 2 ^ (k + 1) % 2 = n % 2 := by
        rw [hsplit]
        exact Nat.mod_mod_of_dvd n ⟨2 ^ k, rfl⟩
      have hdiv : n % 2 ^ (k + 1) / 2 = n / 2 % 2 ^ k := by
        rw [hsplit]; exact Nat.mod_mul_right_div_self n 2 (2 ^ k)
      have hdd : n / 2 / 2 ^ k = n / 2 ^ (k + 1) := by
        rw [Nat.div_div_eq_div_mul, ← hsplit]
      have hbit : (n % 2 ^ (k + 1)).testBit 0 = n.testBit 0 := by
        simp [Nat.testBit_zero, hmod]
      have hstep : k + 1 + m = (k + m) + 1 := by omega
      rw [hstep, bitCard_succ, ih (n / 2), bitCard_succ (n % 2 ^ (k + 1)) k, hbit, hdiv, hdd]
      omega

theorem bitCard_eq_of_lt {n k : ℕ} (h : n < 2 ^ k) {K : ℕ} (hk : k ≤ K) :
    bitCard n K = bitCard n k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [bitCard_add, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h, zero_bitCard, Nat.add_zero]

theorem bitCard_eq_bitCard {n k k' : ℕ} (h : n < 2 ^ k) (h' : n < 2 ^ k') :
    bitCard n k = bitCard n k' := by
  rw [← bitCard_eq_of_lt h (le_max_left k k'), ← bitCard_eq_of_lt h' (le_max_right k k')]

/-! ## The 256-entry byte table -/

/-- The popcount byte table: 256 entries of four bits each, entry `b` occupying
bits `4b` to `4b + 3`.  Stored as a single natural number rather than an
`Array UInt8` for the reason recorded in the module header — kernel array
indexing is a list traversal and costs about seventy times more. -/
def popcountTable : ℕ :=
  0x8776766576656554766565546554544376656554655454436554544354434332766565546554544365545443544343326554544354434332544343324332322176656554655454436554544354434332655454435443433254434332433232216554544354434332544343324332322154434332433232214332322132212110

/-- The table entry for a byte. -/
def popcountByte (b : ℕ) : ℕ := (popcountTable >>> (4 * b)) &&& 15

theorem popcountByte_eq : ∀ b < 256, popcountByte b = bitCard b 8 := by
  decide +kernel

/-! ## Popcount -/

/-- Byte-at-a-time popcount with a fuel argument.  The fuel is only an upper
bound on the number of bytes: the recursion stops as soon as the argument is
zero, so a wildly generous fuel costs nothing. -/
def popcountAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | f + 1, n => popcountByte (n % 256) + popcountAux f (n / 256)

/-- The number of set bits of `n`. -/
def popcount (n : ℕ) : ℕ := popcountAux n n

theorem popcountAux_eq : ∀ (f n : ℕ), n < 256 ^ f → popcountAux f n = bitCard n (8 * f)
  | 0, n, h => by
      have : n = 0 := by simpa using h
      subst this; simp [popcountAux]
  | f + 1, 0, _ => by simp [popcountAux]
  | f + 1, n + 1, h => by
      have hpow : (256 : ℕ) ^ (f + 1) = 256 * 256 ^ f := by
        rw [pow_succ]; exact Nat.mul_comm _ _
      have hdiv : (n + 1) / 256 < 256 ^ f := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        omega
      have hlow : (n + 1) % 256 < 256 := Nat.mod_lt _ (by omega)
      have hmul : 8 * (f + 1) = 8 + 8 * f := by omega
      have h256 : (2 : ℕ) ^ 8 = 256 := by norm_num
      rw [popcountAux, popcountByte_eq _ hlow, popcountAux_eq f _ hdiv, hmul,
        bitCard_add (n + 1) 8 (8 * f), h256]
      omega

theorem popcount_correct (n k : ℕ) (h : n < 2 ^ k) : popcount n = bitCard n k := by
  have hn : n < 256 ^ n :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left (by omega) n)
  have h8 : n < 2 ^ (8 * n) := by
    refine lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by omega) ?_)
    omega
  rw [popcount, popcountAux_eq n n hn]
  exact bitCard_eq_bitCard h8 h

/-- A set of positions at which `n` has a set bit is no larger than the
popcount of `n`.  This is what makes the `cliqueDFS` candidate-count pruning
sound. -/
theorem card_le_popcount {S : Finset ℕ} {n : ℕ} (h : ∀ x ∈ S, n.testBit x = true) :
    S.card ≤ popcount n := by
  classical
  have hsub : S ⊆ (Finset.range n).filter fun i => n.testBit i = true := by
    intro x hx
    have hbit := h x hx
    have hle : 2 ^ x ≤ n := by
      by_contra hcon
      exact absurd hbit (by simp [Nat.testBit_lt_two_pow (Nat.lt_of_not_le hcon)])
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (lt_of_lt_of_le Nat.lt_two_pow_self hle), hbit⟩
  calc S.card ≤ ((Finset.range n).filter fun i => n.testBit i = true).card :=
        Finset.card_le_card hsub
    _ = bitCard n n := rfl
    _ = popcount n := (popcount_correct n n Nat.lt_two_pow_self).symm

/-! ## The submask order

Pruning predicates have to be *hereditary*: true of every submask of a mask on
which they are true.  Every bitwise operation below is monotone for the submask
order, so a predicate assembled from them is hereditary for free.
-/

/-- `Submask m m'` says every position set in `m` is set in `m'`. -/
def Submask (m m' : ℕ) : Prop := ∀ i, m.testBit i = true → m'.testBit i = true

@[refl] theorem Submask.refl (m : ℕ) : Submask m m := fun _ h => h

theorem Submask.trans {a b c : ℕ} (h₁ : Submask a b) (h₂ : Submask b c) : Submask a c :=
  fun i h => h₂ i (h₁ i h)

theorem Submask.and {a b a' b' : ℕ} (ha : Submask a a') (hb : Submask b b') :
    Submask (a &&& b) (a' &&& b') := by
  intro i hi
  simp only [Nat.testBit_and, Bool.and_eq_true] at hi ⊢
  exact ⟨ha i hi.1, hb i hi.2⟩

theorem Submask.or {a b a' b' : ℕ} (ha : Submask a a') (hb : Submask b b') :
    Submask (a ||| b) (a' ||| b') := by
  intro i hi
  simp only [Nat.testBit_or, Bool.or_eq_true] at hi ⊢
  exact hi.imp (ha i) (hb i)

theorem Submask.shiftLeft {a a' : ℕ} (h : Submask a a') (k : ℕ) :
    Submask (a <<< k) (a' <<< k) := by
  intro i hi
  simp only [Nat.testBit_shiftLeft, Bool.and_eq_true] at hi ⊢
  exact ⟨hi.1, h _ hi.2⟩

theorem Submask.shiftRight {a a' : ℕ} (h : Submask a a') (k : ℕ) :
    Submask (a >>> k) (a' >>> k) := by
  intro i hi
  simp only [Nat.testBit_shiftRight] at hi ⊢
  exact h _ hi

theorem Submask.eq_zero {a : ℕ} (h : Submask a 0) : a = 0 := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rcases Bool.eq_false_or_eq_true (a.testBit i) with hi | hi
  · simpa using h i hi
  · simp [hi]

/-- Deleting bits cannot raise the popcount. -/
theorem popcount_mono {m m' : ℕ} (h : Submask m m') : popcount m ≤ popcount m' := by
  classical
  have hcard : ((Finset.range m).filter fun i => m.testBit i = true).card = popcount m :=
    (popcount_correct m m Nat.lt_two_pow_self).symm
  rw [← hcard]
  exact card_le_popcount fun x hx => h x (Finset.mem_filter.1 hx).2

/-! ## The increasing-index subset search

`maskDFS step accept n` walks the binary tree of subsets of `{0, …, n-1}`,
deciding the positions in increasing order.  The mask built so far is passed to
the pruning predicate: at a node whose decided positions are `{0, …, i-1}` and
whose accumulated mask is `m`, the branch that *sets* position `i` is explored
only when `step m i = true`.  Leaves are collected when `accept` holds.

The two facts a consumer needs are `maskDFS_complete` (nothing that survives the
pruning is missed) and `maskDFS_accept` (nothing else is listed).
-/

/-- One node of the increasing-index subset search.  `d` is the number of
positions still to decide, `i` the position being decided, `m` the mask of the
positions already chosen and `acc` the accumulator. -/
def maskDFSAux (step : ℕ → ℕ → Bool) (accept : ℕ → Bool) :
    ℕ → ℕ → ℕ → List ℕ → List ℕ
  | 0, _, m, acc => if accept m then m :: acc else acc
  | d + 1, i, m, acc =>
      if step m i then
        maskDFSAux step accept d (i + 1) (m ||| 2 ^ i)
          (maskDFSAux step accept d (i + 1) m acc)
      else maskDFSAux step accept d (i + 1) m acc

/-- The accepted submasks of `{0, …, n-1}` that survive the pruning predicate
`step`, in reverse visiting order (the accumulator is consed at the leaves, and
the branch that sets a position is explored after the branch that clears it). -/
def maskDFS (step : ℕ → ℕ → Bool) (accept : ℕ → Bool) (n : ℕ) : List ℕ :=
  maskDFSAux step accept n 0 0 []

variable {step : ℕ → ℕ → Bool} {accept : ℕ → Bool}

theorem maskDFSAux_subset (step : ℕ → ℕ → Bool) (accept : ℕ → Bool) :
    ∀ (d i m : ℕ) (acc : List ℕ) {x : ℕ}, x ∈ acc → x ∈ maskDFSAux step accept d i m acc
  | 0, _, m, acc, x, hx => by
      by_cases h : accept m = true
      · simp [maskDFSAux, h, hx]
      · simpa [maskDFSAux, h] using hx
  | d + 1, i, m, acc, x, hx => by
      by_cases h : step m i = true
      · simp only [maskDFSAux, h, if_true]
        exact maskDFSAux_subset step accept d (i + 1) _ _
          (maskDFSAux_subset step accept d (i + 1) m acc hx)
      · simp only [maskDFSAux, h, if_false, Bool.false_eq_true]
        exact maskDFSAux_subset step accept d (i + 1) m acc hx

/-- Low-bit decomposition: setting position `i` of the window `[0, i)` of `t`
gives the window `[0, i+1)` of `t`. -/
private theorem lowBits_succ (t i : ℕ) :
    t % 2 ^ (i + 1) = if t.testBit i = true then t % 2 ^ i ||| 2 ^ i else t % 2 ^ i := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  have hL : (t % 2 ^ (i + 1)).testBit j = (decide (j < i + 1) && t.testBit j) :=
    Nat.testBit_mod_two_pow t (i + 1) j
  rcases Bool.eq_false_or_eq_true (t.testBit i) with h | h
  · rw [if_pos h, hL, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
    rcases lt_trichotomy j i with hj | hj | hj
    · simp [hj, Nat.lt_succ_of_lt hj, Nat.ne_of_gt hj]
    · subst hj; simp [h]
    · simp [Nat.not_lt.2 (Nat.le_of_lt hj), Nat.not_lt.2 hj, Nat.ne_of_lt hj]
  · rw [if_neg (by simp [h]), hL, Nat.testBit_mod_two_pow]
    rcases lt_trichotomy j i with hj | hj | hj
    · simp [hj, Nat.lt_succ_of_lt hj]
    · subst hj; simp [h]
    · simp [Nat.not_lt.2 (Nat.le_of_lt hj), Nat.not_lt.2 hj]

/-- **Completeness of the pruned search, node form.**  A target `t` whose own
path is never pruned is produced by the node at `(d, i, t % 2 ^ i)`. -/
theorem maskDFSAux_mem (step : ℕ → ℕ → Bool) (accept : ℕ → Bool) {t : ℕ}
    (hacc : accept t = true) :
    ∀ (d i : ℕ) (acc : List ℕ), t < 2 ^ (i + d) →
      (∀ j, i ≤ j → j < i + d → t.testBit j = true → step (t % 2 ^ j) j = true) →
      t ∈ maskDFSAux step accept d i (t % 2 ^ i) acc
  | 0, i, acc, hlt, _ => by
      rw [Nat.add_zero] at hlt
      rw [Nat.mod_eq_of_lt hlt]
      simp [maskDFSAux, hacc]
  | d + 1, i, acc, hlt, hstep => by
      have hlt' : t < 2 ^ (i + 1 + d) := by
        rw [show i + 1 + d = i + (d + 1) by omega]; exact hlt
      have hstep' : ∀ j, i + 1 ≤ j → j < i + 1 + d → t.testBit j = true →
          step (t % 2 ^ j) j = true := by
        intro j hj hj' hbit
        exact hstep j (by omega) (by omega) hbit
      by_cases hbit : t.testBit i = true
      · have hs : step (t % 2 ^ i) i = true := hstep i le_rfl (by omega) hbit
        simp only [maskDFSAux, hs, if_true]
        have := maskDFSAux_mem step accept hacc d (i + 1)
          (maskDFSAux step accept d (i + 1) (t % 2 ^ i) acc) hlt' hstep'
        rwa [lowBits_succ, if_pos hbit] at this
      · have := maskDFSAux_mem step accept hacc d (i + 1) acc hlt' hstep'
        rw [lowBits_succ, if_neg hbit] at this
        by_cases hs : step (t % 2 ^ i) i = true
        · simp only [maskDFSAux, hs, if_true]
          exact maskDFSAux_subset step accept d (i + 1) _ _ this
        · simpa only [maskDFSAux, hs, if_false, Bool.false_eq_true] using this

/-- **Completeness of the pruned search.**  If `m` fits in `n` bits, is
accepted, and every position it sets passes the pruning test against the mask of
its own lower positions, then `m` appears in `maskDFS step accept n`. -/
theorem maskDFS_complete {n m : ℕ} (hlt : m < 2 ^ n) (hacc : accept m = true)
    (hstep : ∀ j, j < n → m.testBit j = true → step (m % 2 ^ j) j = true) :
    m ∈ maskDFS step accept n := by
  have h := maskDFSAux_mem step accept hacc n 0 [] (by simpa using hlt)
    (by simpa using fun j hj hbit => hstep j hj hbit)
  simpa [maskDFS, Nat.mod_one] using h

/-- A pruning predicate is hereditary when it survives deleting bits. -/
def Hereditary (P : ℕ → Bool) : Prop :=
  ∀ m m' : ℕ, Submask m m' → P m' = true → P m = true

/-- **Completeness for a hereditary pruning predicate.**  This is the form a
consumer uses: the pruning is a property `P` of masks that is inherited by
submasks, and then only `P m` itself has to be checked, not the whole path. -/
theorem maskDFS_complete_of_hereditary {P : ℕ → Bool} (hP : Hereditary P) {n m : ℕ}
    (hlt : m < 2 ^ n) (hPm : P m = true) (hacc : accept m = true) :
    m ∈ maskDFS (fun m' i => P (m' ||| 2 ^ i)) accept n := by
  refine maskDFS_complete hlt hacc fun j _ hbit => ?_
  refine hP _ m (fun i hi => ?_) hPm
  simp only [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_two_pow, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq] at hi
  rcases hi with ⟨-, h⟩ | h
  · exact h
  · exact h ▸ hbit

/-- Only accepted masks are listed. -/
theorem maskDFS_accept {n x : ℕ} (hx : x ∈ maskDFS step accept n) : accept x = true := by
  have key : ∀ (d i m : ℕ) (acc : List ℕ),
      x ∈ maskDFSAux step accept d i m acc → x ∈ acc ∨ accept x = true := by
    intro d
    induction d with
    | zero =>
        intro i m acc hmem
        by_cases h : accept m = true
        · simp only [maskDFSAux, h, if_true, List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact Or.inr h
          · exact Or.inl hmem
        · simp only [maskDFSAux, h, if_false, Bool.false_eq_true] at hmem
          exact Or.inl hmem
    | succ d ih =>
        intro i m acc hmem
        by_cases h : step m i = true
        · simp only [maskDFSAux, h, if_true] at hmem
          rcases ih (i + 1) _ _ hmem with hmem' | hacc
          · exact ih (i + 1) m acc hmem'
          · exact Or.inr hacc
        · simp only [maskDFSAux, h, if_false, Bool.false_eq_true] at hmem
          exact ih (i + 1) m acc hmem
  rcases key n 0 0 [] hx with hmem | hacc
  · simp at hmem
  · exact hacc

/-! ## The clique search

`cliqueDFS adj n target` decides whether the graph on `{0, …, n-1}` whose
neighbourhood masks are `adj 0, …, adj (n-1)` contains a clique of size
`target`.  Only the `false` answer is certified: `cliqueDFS_sound` turns it into
the nonexistence statement, which is the direction every refutation chunk needs.

The adjacency is a *function* rather than an `Array ℕ` — see the module header
for the measurement that forced this.  A caller with `n` vertices typically
supplies `fun v => (packed >>> (n * v)) &&& (2 ^ n - 1)` for a single packed
natural number `packed`.
-/

/-- One node of the clique search: is there a clique of size `d` among the
candidate vertices `≥ v` recorded in the bitmask `cand`?  `fuel` bounds the
number of vertices still to scan.  The first test is the counting cut: a
candidate set with fewer than `d` bits cannot contain `d` vertices. -/
def cliqueDFSAux (adj : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, d, _, _ => decide (d = 0)
  | _ + 1, 0, _, _ => true
  | fuel + 1, d + 1, v, cand =>
      if popcount cand < d + 1 then false
      else if cand.testBit v then
        cliqueDFSAux adj fuel d (v + 1) (cand &&& adj v) ||
          cliqueDFSAux adj fuel (d + 1) (v + 1) cand
      else cliqueDFSAux adj fuel (d + 1) (v + 1) cand

/-- Search the graph on `{0, …, n-1}` with neighbourhood masks `adj` for a
clique of size `target`. -/
def cliqueDFS (adj : ℕ → ℕ) (n target : ℕ) : Bool :=
  cliqueDFSAux adj n target 0 (2 ^ n - 1)

theorem cliqueDFSAux_sound (adj : ℕ → ℕ) :
    ∀ (fuel d v cand : ℕ) (S : Finset ℕ),
      cliqueDFSAux adj fuel d v cand = false → S.card = d →
      (∀ x ∈ S, v ≤ x ∧ x < v + fuel) →
      (∀ x ∈ S, cand.testBit x = true) →
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → (adj a).testBit b = true) → False := by
  intro fuel
  induction fuel with
  | zero =>
      intro d v cand S hfalse hcard hrange _ _
      rw [cliqueDFSAux] at hfalse
      have hd : d ≠ 0 := by simpa using hfalse
      obtain ⟨x, hx⟩ := Finset.card_pos.1 (by omega : 0 < S.card)
      have := hrange x hx
      omega
  | succ fuel ih =>
      intro d v cand S hfalse hcard hrange hcand hclique
      cases d with
      | zero => rw [cliqueDFSAux] at hfalse; exact Bool.noConfusion hfalse
      | succ d =>
        rw [cliqueDFSAux] at hfalse
        by_cases hpc : popcount cand < d + 1
        · have hle : S.card ≤ popcount cand := card_le_popcount hcand
          omega
        rw [if_neg hpc] at hfalse
        by_cases hbit : cand.testBit v = true
        · rw [if_pos hbit, Bool.or_eq_false_iff] at hfalse
          by_cases hv : v ∈ S
          · refine ih d (v + 1) (cand &&& adj v) (S.erase v) hfalse.1 ?_ ?_ ?_ ?_
            · rw [Finset.card_erase_of_mem hv, hcard]
              omega
            · intro x hx
              have hne : x ≠ v := Finset.ne_of_mem_erase hx
              have := hrange x (Finset.mem_of_mem_erase hx)
              omega
            · intro x hx
              have hxS := Finset.mem_of_mem_erase hx
              have hne : x ≠ v := Finset.ne_of_mem_erase hx
              simp [Nat.testBit_and, hcand x hxS, hclique v hv x hxS (Ne.symm hne)]
            · intro a ha b hb hab
              exact hclique a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab
          · refine ih (d + 1) (v + 1) cand S hfalse.2 hcard ?_ hcand hclique
            intro x hx
            have hne : x ≠ v := fun hxv => hv (hxv ▸ hx)
            have := hrange x hx
            omega
        · rw [if_neg hbit] at hfalse
          refine ih (d + 1) (v + 1) cand S hfalse hcard ?_ hcand hclique
          intro x hx
          have hne : x ≠ v := fun hxv => hbit (hxv ▸ hcand x hx)
          have := hrange x hx
          omega

/-- **Soundness of the clique search.**  A `false` answer refutes every clique
of the requested size in the graph on `{0, …, n-1}` given by the neighbourhood
masks `adj`. -/
theorem cliqueDFS_sound {adj : ℕ → ℕ} {n target : ℕ} (h : cliqueDFS adj n target = false)
    {S : Finset ℕ} (hcard : S.card = target) (hmem : ∀ x ∈ S, x < n)
    (hclique : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (adj a).testBit b = true) : False := by
  refine cliqueDFSAux_sound adj n target 0 (2 ^ n - 1) S h hcard (fun x hx => ?_)
    (fun x hx => ?_) hclique
  · exact ⟨Nat.zero_le _, by simpa using hmem x hx⟩
  · simp [Nat.testBit_two_pow_sub_one, hmem x hx]

/-! ## Comparing a population count without computing one

`dropLowest y = y &&& (y - 1)` deletes the lowest set bit of `y`.  Iterating it
`k` times and testing the result against zero decides `popcount y ≤ k` using
`atMost` and `zeroOrThree` without computing a full population count.
-/

/-- Delete the lowest set bit. -/
def dropLowest (y : ℕ) : ℕ := y &&& (y - 1)

@[simp] theorem dropLowest_zero : dropLowest 0 = 0 := rfl

@[simp] theorem popcount_zero : popcount 0 = 0 := rfl

/-- Doubling shifts every bit up, so it does not change the population count. -/
theorem popcount_two_mul (q : ℕ) : popcount (2 * q) = popcount q := by
  have hq : q < 2 ^ q := Nat.lt_two_pow_self
  have h2 : 2 * q < 2 ^ (q + 1) := by
    have hpow : (2 : ℕ) * 2 ^ q = 2 ^ (q + 1) := by rw [pow_succ, Nat.mul_comm]
    omega
  have hbit : (2 * q).testBit 0 = false := by
    simp [Nat.testBit_zero, Nat.mul_mod_right]
  rw [popcount_correct _ (q + 1) h2, popcount_correct q q hq, bitCard_succ, hbit,
    Nat.mul_div_cancel_left q (by norm_num)]
  simp

/-- Doubling and adding one adds exactly one bit. -/
theorem popcount_two_mul_add_one (q : ℕ) : popcount (2 * q + 1) = popcount q + 1 := by
  have hq : q < 2 ^ q := Nat.lt_two_pow_self
  have h2 : 2 * q + 1 < 2 ^ (q + 1) := by
    have hpow : (2 : ℕ) * 2 ^ q = 2 ^ (q + 1) := by rw [pow_succ, Nat.mul_comm]
    omega
  have hbit : (2 * q + 1).testBit 0 = true := by
    simp [Nat.testBit_zero]
  rw [popcount_correct _ (q + 1) h2, popcount_correct q q hq, bitCard_succ, hbit,
    show (2 * q + 1) / 2 = q from by omega, if_pos rfl]
  omega

/-- Deleting the lowest set bit of an odd number leaves the number below it. -/
private theorem dropLowest_odd (q : ℕ) : dropLowest (2 * q + 1) = 2 * q := by
  rw [dropLowest, show 2 * q + 1 - 1 = 2 * q from by omega]
  refine Nat.eq_of_testBit_eq fun i => ?_
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ i =>
      rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ,
        show (2 * q + 1) / 2 = q from by omega, Nat.mul_div_cancel_left q (by norm_num)]
      simp

/-- Deleting the lowest set bit commutes with doubling. -/
private theorem dropLowest_even {q : ℕ} (hq : q ≠ 0) :
    dropLowest (2 * q) = 2 * dropLowest q := by
  rw [dropLowest, dropLowest, show 2 * q - 1 = 2 * (q - 1) + 1 from by omega]
  refine Nat.eq_of_testBit_eq fun i => ?_
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ i =>
      rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
        Nat.mul_div_cancel_left q (by norm_num),
        show (2 * (q - 1) + 1) / 2 = q - 1 from by omega,
        Nat.mul_div_cancel_left (q &&& (q - 1)) (by norm_num), Nat.testBit_and]

/-- **The defining property of `dropLowest`.**  It removes exactly one bit,
except at zero where there is none to remove. -/
theorem popcount_dropLowest (y : ℕ) : popcount (dropLowest y) = popcount y - 1 := by
  induction y using Nat.strong_induction_on with
  | _ y ih =>
      rcases Nat.eq_zero_or_pos y with rfl | hpos
      · simp [popcount, popcountAux]
      rcases Nat.even_or_odd y with ⟨q, hq⟩ | ⟨q, hq⟩
      · have hq0 : q ≠ 0 := by omega
        have hlt : q < y := by omega
        have hy : y = 2 * q := by omega
        subst hy
        rw [dropLowest_even hq0, popcount_two_mul, popcount_two_mul, ih q hlt]
      · subst hq
        rw [dropLowest_odd, popcount_two_mul, popcount_two_mul_add_one]
        omega

/-- A number with no bits is zero. -/
theorem eq_zero_of_popcount_eq_zero {y : ℕ} (h : popcount y = 0) : y = 0 := by
  classical
  have hcard : ((Finset.range y).filter fun i => y.testBit i = true).card = 0 := by
    rw [show ((Finset.range y).filter fun i => y.testBit i = true).card = bitCard y y from rfl,
      ← popcount_correct y y Nat.lt_two_pow_self, h]
  have hempty := Finset.card_eq_zero.1 hcard
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < y
  · have hmem : i ∉ (Finset.range y).filter fun j => y.testBit j = true := by
      rw [hempty]; simp
    simp only [Finset.mem_filter, Finset.mem_range, not_and] at hmem
    simpa using hmem hi
  · have hlt : y < 2 ^ i :=
      lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
    simp [Nat.testBit_lt_two_pow hlt]

/-- Delete the `k` lowest set bits. -/
def dropIter : ℕ → ℕ → ℕ
  | 0, y => y
  | k + 1, y => dropIter k (dropLowest y)

theorem popcount_dropIter (k y : ℕ) : popcount (dropIter k y) = popcount y - k := by
  induction k generalizing y with
  | zero => simp [dropIter]
  | succ k ih => rw [dropIter, ih, popcount_dropLowest]; omega

/-- `atMost k y` decides `popcount y ≤ k` in `2k` machine operations. -/
def atMost (k y : ℕ) : Bool := dropIter k y == 0

theorem atMost_eq_true_iff {k y : ℕ} : atMost k y = true ↔ popcount y ≤ k := by
  rw [atMost, beq_iff_eq]
  constructor
  · intro h
    have hp := popcount_dropIter k y
    rw [h, popcount_zero] at hp
    omega
  · intro h
    exact eq_zero_of_popcount_eq_zero (by rw [popcount_dropIter]; omega)

/-- `zeroOrThree y` decides `popcount y = 0 ∨ popcount y = 3`. -/
def zeroOrThree (y : ℕ) : Bool := atMost 3 y && ((y == 0) || !atMost 2 y)

/-- The soundness direction the certificates use: a set of edges meeting a
member of a cherry cover in `0` or `3` edges passes the test. -/
theorem zeroOrThree_of_card {y : ℕ} (h : popcount y = 0 ∨ popcount y = 3) :
    zeroOrThree y = true := by
  rw [zeroOrThree, Bool.and_eq_true]
  refine ⟨atMost_eq_true_iff.2 (by omega), ?_⟩
  rcases h with h | h
  · simp [eq_zero_of_popcount_eq_zero h]
  · have h3 : ¬ popcount y ≤ 2 := by omega
    have hfalse : atMost 2 y = false := by
      rcases Bool.eq_false_or_eq_true (atMost 2 y) with h2 | h2
      · exact absurd (atMost_eq_true_iff.1 h2) h3
      · exact h2
    simp [hfalse]

/-! ## The doubly pruned search

`rowDFS guard accept rows i m` walks the same binary tree as `maskDFS`, but
*both* branches are tested, and the pruning predicate reads its per-position
data from the head of `rows`, which the recursion consumes.  A consumer
therefore pays neither for exploring an already-dead mask to the end of the
window nor for indexing a table.

Completeness is `rowDFS_mem`: a target whose every prefix passes its own row's
test, and which is accepted, is listed.  `RowGuardChain` is the "every prefix
passes" hypothesis, phrased so that it unfolds one row at a time.
-/

/-- One node of the doubly pruned search: `rows` are the per-position data of
the positions still to decide, `i` is the position being decided and `m` the
mask of the positions already chosen. -/
def rowDFS {α : Type*} (guard : α → ℕ → Bool) (accept : ℕ → Bool) :
    List α → ℕ → ℕ → List ℕ
  | [], _, m => if accept m then [m] else []
  | row :: rows, i, m =>
      (if guard row (m ||| 2 ^ i) then rowDFS guard accept rows (i + 1) (m ||| 2 ^ i) else []) ++
        (if guard row m then rowDFS guard accept rows (i + 1) m else [])

/-- Unfolding `rowDFS` one position at a time. -/
theorem rowDFS_cons {α : Type*} (guard : α → ℕ → Bool) (accept : ℕ → Bool)
    (row : α) (rows : List α) (i m : ℕ) :
    rowDFS guard accept (row :: rows) i m =
      (if guard row (m ||| 2 ^ i) then rowDFS guard accept rows (i + 1) (m ||| 2 ^ i)
        else []) ++
        (if guard row m then rowDFS guard accept rows (i + 1) m else []) := rfl

/-- The hypothesis of `rowDFS_mem`: every prefix of `t` passes the test of the
row that decides its last position. -/
def RowGuardChain {α : Type*} (guard : α → ℕ → Bool) : List α → ℕ → ℕ → Prop
  | [], _, _ => True
  | row :: rows, i, t => guard row (t % 2 ^ (i + 1)) = true ∧ RowGuardChain guard rows (i + 1) t

/-- **Completeness of the doubly pruned search.** -/
theorem rowDFS_mem {α : Type*} (guard : α → ℕ → Bool) (accept : ℕ → Bool) {t : ℕ}
    (hacc : accept t = true) :
    ∀ (rows : List α) (i : ℕ), t < 2 ^ (i + rows.length) →
      RowGuardChain guard rows i t → t ∈ rowDFS guard accept rows i (t % 2 ^ i)
  | [], i, hlt, _ => by
      rw [List.length_nil, Nat.add_zero] at hlt
      rw [Nat.mod_eq_of_lt hlt]
      simp [rowDFS, hacc]
  | row :: rows, i, hlt, hchain => by
      obtain ⟨hrow, hrest⟩ := hchain
      have hlt' : t < 2 ^ (i + 1 + rows.length) := by
        rw [show i + 1 + rows.length = i + (row :: rows).length from by
          rw [List.length_cons]; omega]
        exact hlt
      have hstep := rowDFS_mem guard accept hacc rows (i + 1) hlt' hrest
      rw [rowDFS_cons]
      by_cases hbit : t.testBit i = true
      · rw [lowBits_succ, if_pos hbit] at hrow hstep
        rw [if_pos hrow]
        exact List.mem_append_left _ hstep
      · rw [lowBits_succ, if_neg hbit] at hrow hstep
        rw [if_pos hrow]
        exact List.mem_append_right _ hstep

end SRG266.Search
