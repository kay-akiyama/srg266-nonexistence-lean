/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Search.CNFSemantics
import SRG266.Search.SubsetDFS
import SRG266.Search.SequentialCountCNF

/-!
# CNF encodings of exact local bit counts

The finite rooted certificates use small Boolean constraint systems.  An
exact-count constraint is encoded extensionally: for every local assignment
of the wrong weight, one clause forbids precisely that assignment.  This is
not the smallest SAT encoding, but it has a particularly transparent Lean
semantics and the local scopes have only six or seven vars.

The SAT solver is not trusted.  This module proves directly that a natural
number whose selected bits have the requested count satisfies every generated
clause.  A later LRAT proof can therefore refute only the remaining finite
search statement.
-/

namespace SRG266.Search

/-- The literal which is false exactly when var `var` has value
`bit`. -/
def literalForbidding (var : ℕ) : Bool → Sat.Literal
  | false => .pos var
  | true => .neg var

/-- A clause false at exactly one assignment of the listed vars.  The
low bit of `pattern` belongs to the head var. -/
def forbiddenLocalClause : List ℕ → ℕ → Sat.Clause
  | [], _ => []
  | var :: vars, pattern =>
      literalForbidding var (pattern.testBit 0) ::
        forbiddenLocalClause vars (pattern / 2)

/-- Project the selected bits of `assignment` to consecutive low positions.
The low bit belongs to the head var. -/
def localAssignmentMask : List ℕ → ℕ → ℕ
  | [], _ => 0
  | var :: vars, assignment =>
      Nat.bit (assignment.testBit var)
        (localAssignmentMask vars assignment)

private theorem testBit_bit_zero (b : Bool) (n : ℕ) :
    (Nat.bit b n).testBit 0 = b := by
  cases b <;> simp [Nat.bit, Nat.testBit_zero]

private theorem testBit_bit_succ (b : Bool) (n i : ℕ) :
    (Nat.bit b n).testBit (i + 1) = n.testBit i := by
  rw [Nat.testBit_succ]
  cases b
  · simp [Nat.bit]
  · have hdiv : (2 * n + 1) / 2 = n := by omega
    simp [Nat.bit, hdiv]

theorem testBit_localAssignmentMask_of_lt
    (assignment : ℕ) (vars : List ℕ) {i : ℕ}
    (hi : i < vars.length) :
    (localAssignmentMask vars assignment).testBit i =
      assignment.testBit vars[i] := by
  induction vars generalizing i with
  | nil => simp at hi
  | cons var vars ih =>
      cases i with
      | zero => simp [localAssignmentMask]
      | succ i =>
          simpa [localAssignmentMask, testBit_bit_succ] using
            ih (by simpa using hi)

theorem testBit_localAssignmentMask_of_length_le
    (assignment : ℕ) (vars : List ℕ) {i : ℕ}
    (hi : vars.length ≤ i) :
    (localAssignmentMask vars assignment).testBit i = false := by
  induction vars generalizing i with
  | nil => simp [localAssignmentMask]
  | cons var vars ih =>
      cases i with
      | zero => simp at hi
      | succ i =>
          rw [localAssignmentMask, show i + 1 = Nat.succ i by omega,
            testBit_bit_succ]
          exact ih (by simpa using hi)

theorem localAssignmentMask_lt (vars : List ℕ) (assignment : ℕ) :
    localAssignmentMask vars assignment < 2 ^ vars.length := by
  induction vars with
  | nil => simp [localAssignmentMask]
  | cons var vars ih =>
      rw [localAssignmentMask, List.length_cons, pow_succ]
      cases assignment.testBit var <;> simp [Nat.bit] <;> omega

/-- The projected mask counts the true selected variables, including their
list multiplicity. -/
theorem popcount_localAssignmentMask (vars : List ℕ) (assignment : ℕ) :
    popcount (localAssignmentMask vars assignment) =
      (vars.filter fun var => assignment.testBit var).length := by
  rw [popcount_correct _ vars.length (localAssignmentMask_lt vars assignment)]
  induction vars with
  | nil => simp [localAssignmentMask]
  | cons var vars ih =>
      rw [List.length_cons, localAssignmentMask, bitCard_succ]
      have hdiv : Nat.bit (assignment.testBit var)
          (localAssignmentMask vars assignment) / 2 =
          localAssignmentMask vars assignment := by
        cases assignment.testBit var
        · simp [Nat.bit]
        · simp [Nat.bit]
          omega
      rw [testBit_bit_zero, hdiv, ih]
      cases hbit : assignment.testBit var
      · simp [hbit]
      · simp [hbit]
        omega

/-- All clauses excluding local assignments whose population is not `need`. -/
def exactCountFmla (vars : List ℕ) (need : ℕ) : Sat.Fmla :=
  ((List.range (2 ^ vars.length)).filter fun pattern =>
    popcount pattern != need).map (forbiddenLocalClause vars)

/-- Clauses excluding each complete assignment in `masks`. -/
def forbiddenMasksFmla (width : ℕ) (masks : List ℕ) : Sat.Fmla :=
  masks.map (forbiddenLocalClause (List.range width))

/-- A blocking clause only mentions variables from its supplied scope. -/
theorem forbiddenLocalClause_below {bound pattern : ℕ} :
    ∀ {vars : List ℕ}, (∀ var ∈ vars, var < bound) →
      ∀ (literal : Sat.Literal),
        literal ∈ (show List Sat.Literal from
          forbiddenLocalClause vars pattern) →
          literalVar literal < bound := by
  intro vars hvars
  induction vars generalizing pattern with
  | nil =>
      intro literal hliteral
      simp [forbiddenLocalClause] at hliteral
  | cons var vars ih =>
      intro literal hliteral
      rw [forbiddenLocalClause, List.mem_cons] at hliteral
      rcases hliteral with rfl | hliteral
      · cases hbit : pattern.testBit 0 <;>
          simpa [literalForbidding, literalVar, hbit] using
            hvars var (by simp)
      · exact ih (fun item hitem => hvars item (by simp [hitem]))
          literal hliteral

/-- Complete-assignment blocking clauses of width `width` stay below that
primary-variable boundary. -/
theorem forbiddenMasksFmla_below (width : ℕ) (masks : List ℕ) :
    FmlaBelow width (forbiddenMasksFmla width masks) := by
  intro clause hclause literal hliteral
  rw [forbiddenMasksFmla, List.mem_map] at hclause
  obtain ⟨mask, _, rfl⟩ := hclause
  exact forbiddenLocalClause_below
    (fun var hvar => List.mem_range.mp hvar) literal hliteral

/-- Conjunction of several local exact-count constraints. -/
def exactCountsFmla (constraints : List (List ℕ × ℕ)) : Sat.Fmla :=
  constraints.flatMap fun constraint => exactCountFmla constraint.1 constraint.2

/-- An exact-count system together with clauses blocking complete models. -/
def exactCountCoverFmla (width : ℕ) (constraints : List (List ℕ × ℕ))
    (masks : List ℕ) : Sat.Fmla :=
  exactCountsFmla constraints ++ forbiddenMasksFmla width masks

/-- Unit clauses fixing the low `prefixWidth` bits to `prefixMask`. -/
def fixedLowBitsFmla (prefixWidth prefixMask : ℕ) : Sat.Fmla :=
  (List.range prefixWidth).map fun i =>
    [if prefixMask.testBit i then Sat.Literal.pos i else Sat.Literal.neg i]

/-- A chunked exact-count counterexample formula. -/
def exactCountCoverChunkFmla (width prefixWidth prefixMask : ℕ)
    (constraints : List (List ℕ × ℕ)) (masks : List ℕ) : Sat.Fmla :=
  exactCountsFmla constraints ++ fixedLowBitsFmla prefixWidth prefixMask ++
    forbiddenMasksFmla width masks

private theorem bit_div_two (n : ℕ) :
    Nat.bit (n.testBit 0) (n / 2) = n := by
  rw [Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · simp [Nat.bit, h]
    omega
  · simp [Nat.bit, h]
    omega

/-- If the forbidden clause is false, the selected assignment is exactly its
forbidden pattern. -/
theorem localAssignmentMask_eq_of_eval_forbidden_false
    (assignment : ℕ) : ∀ (vars : List ℕ) (pattern : ℕ),
    pattern < 2 ^ vars.length →
    evalClause (fun i => assignment.testBit i)
      (forbiddenLocalClause vars pattern) = false →
    localAssignmentMask vars assignment = pattern := by
  intro vars
  induction vars with
  | nil =>
      intro pattern hlt _
      have : pattern = 0 := by simpa using hlt
      simp [localAssignmentMask, this]
  | cons var vars ih =>
      intro pattern hlt hfalse
      have htailLt : pattern / 2 < 2 ^ vars.length := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        simpa [pow_succ, Nat.mul_comm] using hlt
      have hparts :
          evalLiteral (fun i => assignment.testBit i)
              (literalForbidding var (pattern.testBit 0)) = false ∧
            evalClause (fun i => assignment.testBit i)
              (forbiddenLocalClause vars (pattern / 2)) = false := by
        simpa [forbiddenLocalClause, evalClause] using hfalse
      have hhead : assignment.testBit var = pattern.testBit 0 := by
        cases hpattern : pattern.testBit 0
        · simpa [literalForbidding, evalLiteral, hpattern] using hparts.1
        · simpa [literalForbidding, evalLiteral, hpattern] using hparts.1
      rw [localAssignmentMask, hhead, ih (pattern / 2) htailLt hparts.2,
        bit_div_two]

/-- A correct local exact count satisfies every clause of its extensional CNF
encoding. -/
theorem eval_exactCountFmla_eq_true {vars : List ℕ} {need assignment : ℕ}
    (hcount : popcount (localAssignmentMask vars assignment) = need) :
    evalFmla (fun i => assignment.testBit i)
      (exactCountFmla vars need) = true := by
  rw [evalFmla, List.all_eq_true]
  intro clause hclause
  rw [exactCountFmla, List.mem_map] at hclause
  obtain ⟨pattern, hpattern, rfl⟩ := hclause
  have hlt : pattern < 2 ^ vars.length :=
    List.mem_range.mp (List.mem_of_mem_filter hpattern)
  have hwrong : popcount pattern ≠ need := by
    have := (List.mem_filter.mp hpattern).2
    simpa using this
  by_contra hfalse
  have heq := localAssignmentMask_eq_of_eval_forbidden_false
    assignment vars pattern hlt (Bool.eq_false_of_not_eq_true hfalse)
  exact hwrong (heq ▸ hcount)

theorem eval_exactCountsFmla_eq_true {constraints : List (List ℕ × ℕ)}
    {assignment : ℕ}
    (hcounts : ∀ constraint ∈ constraints,
      popcount (localAssignmentMask constraint.1 assignment) = constraint.2) :
    evalFmla (fun i => assignment.testBit i)
      (exactCountsFmla constraints) = true := by
  rw [evalFmla, List.all_eq_true]
  intro clause hclause
  rw [exactCountsFmla, List.mem_flatMap] at hclause
  obtain ⟨constraint, hconstraint, hclause⟩ := hclause
  have heval := eval_exactCountFmla_eq_true
    (hcounts constraint hconstraint)
  rw [evalFmla, List.all_eq_true] at heval
  exact heval clause hclause

theorem eval_fixedLowBitsFmla_eq_true {assignment prefixWidth prefixMask : ℕ}
    (hbits : ∀ i < prefixWidth,
      assignment.testBit i = prefixMask.testBit i) :
    evalFmla (fun i => assignment.testBit i)
      (fixedLowBitsFmla prefixWidth prefixMask) = true := by
  rw [evalFmla, List.all_eq_true]
  intro clause hclause
  rw [fixedLowBitsFmla, List.mem_map] at hclause
  obtain ⟨i, hi, rfl⟩ := hclause
  have hbit := hbits i (List.mem_range.mp hi)
  cases hp : prefixMask.testBit i <;>
    simp [evalClause, evalLiteral, hp, hbit]

/-- If a bounded complete assignment is not one of the forbidden masks, it
satisfies all their blocking clauses. -/
theorem eval_forbiddenMasksFmla_eq_true {width assignment : ℕ} {masks : List ℕ}
    (hassignment : assignment < 2 ^ width)
    (hmasks : ∀ mask ∈ masks, mask < 2 ^ width)
    (hnot : assignment ∉ masks) :
    evalFmla (fun i => assignment.testBit i)
      (forbiddenMasksFmla width masks) = true := by
  rw [evalFmla, List.all_eq_true]
  intro clause hclause
  rw [forbiddenMasksFmla, List.mem_map] at hclause
  obtain ⟨mask, hmask, rfl⟩ := hclause
  by_contra hfalse
  have heq := localAssignmentMask_eq_of_eval_forbidden_false assignment
    (List.range width) mask (by simpa using hmasks mask hmask)
    (Bool.eq_false_of_not_eq_true hfalse)
  have hlocal : localAssignmentMask (List.range width) assignment = assignment := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < width
    · rw [testBit_localAssignmentMask_of_lt assignment (List.range width)
          (by simpa using hi), List.getElem_range]
    · rw [testBit_localAssignmentMask_of_length_le assignment (List.range width)
          (by simpa using Nat.le_of_not_gt hi)]
      have hpow : 2 ^ width ≤ 2 ^ i :=
        Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hi)
      exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hassignment hpow)).symm
  exact hnot (hlocal ▸ heq ▸ hmask)

theorem eval_exactCountCoverFmla_eq_true
    {width assignment : ℕ} {constraints : List (List ℕ × ℕ)}
    {masks : List ℕ}
    (hcounts : ∀ constraint ∈ constraints,
      popcount (localAssignmentMask constraint.1 assignment) = constraint.2)
    (hassignment : assignment < 2 ^ width)
    (hmasks : ∀ mask ∈ masks, mask < 2 ^ width)
    (hnot : assignment ∉ masks) :
    evalFmla (fun i => assignment.testBit i)
      (exactCountCoverFmla width constraints masks) = true := by
  rw [evalFmla, exactCountCoverFmla, List.all_append, Bool.and_eq_true]
  exact ⟨eval_exactCountsFmla_eq_true hcounts,
    eval_forbiddenMasksFmla_eq_true hassignment hmasks hnot⟩

theorem eval_exactCountCoverChunkFmla_eq_true
    {width prefixWidth prefixMask assignment : ℕ}
    {constraints : List (List ℕ × ℕ)} {masks : List ℕ}
    (hcounts : ∀ constraint ∈ constraints,
      popcount (localAssignmentMask constraint.1 assignment) = constraint.2)
    (hbits : ∀ i < prefixWidth,
      assignment.testBit i = prefixMask.testBit i)
    (hassignment : assignment < 2 ^ width)
    (hmasks : ∀ mask ∈ masks, mask < 2 ^ width)
    (hnot : assignment ∉ masks) :
    evalFmla (fun i => assignment.testBit i)
      (exactCountCoverChunkFmla width prefixWidth prefixMask constraints masks) = true := by
  rw [evalFmla, exactCountCoverChunkFmla, List.all_append,
    List.all_append, Bool.and_eq_true]
  constructor
  · rw [Bool.and_eq_true]
    exact ⟨eval_exactCountsFmla_eq_true hcounts,
      eval_fixedLowBitsFmla_eq_true hbits⟩
  · exact eval_forbiddenMasksFmla_eq_true hassignment hmasks hnot

end SRG266.Search
