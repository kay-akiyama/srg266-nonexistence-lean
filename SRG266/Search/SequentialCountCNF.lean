/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Search.CNFSemantics

/-!
# Sequential exact-count CNF

Large Cherry certificates need exact-cardinality constraints whose scopes are
too wide for the extensional encoder in `ExactCountCNF`.  This file gives a
polynomial threshold-counter encoding and proves its Boolean semantics.

The counter variable at `(row, threshold)` means that at least `threshold` of
the first `row` input variables are true.  Every auxiliary value is defined by
Lean; an external SAT solver only supplies an LRAT refutation of the resulting
clause list.
-/

namespace SRG266.Search

/-- CNF for `output = same || (bit && less)`. -/
def thresholdStepFmla (output same bit less : ℕ) : Sat.Fmla :=
  [[.neg same, .pos output],
   [.neg bit, .neg less, .pos output],
   [.neg output, .pos same, .pos bit],
   [.neg output, .pos same, .pos less]]

theorem eval_thresholdStepFmla_eq_true (assignment : ℕ → Bool)
    {output same bit less : ℕ}
    (houtput : assignment output =
      (assignment same || (assignment bit && assignment less))) :
    evalFmla assignment (thresholdStepFmla output same bit less) = true := by
  cases hs : assignment same <;> cases hb : assignment bit <;>
    cases hl : assignment less <;>
      simp [thresholdStepFmla, evalFmla, evalClause, evalLiteral,
        houtput, hs, hb, hl]

/-- CNF for `output = left && right`. -/
def andGateFmla (output left right : ℕ) : Sat.Fmla :=
  [[.neg output, .pos left],
   [.neg output, .pos right],
   [.pos output, .neg left, .neg right]]

theorem eval_andGateFmla_eq_true (assignment : ℕ → Bool)
    {output left right : ℕ}
    (houtput : assignment output = (assignment left && assignment right)) :
    evalFmla assignment (andGateFmla output left right) = true := by
  cases hl : assignment left <;> cases hr : assignment right <;>
    simp [andGateFmla, evalFmla, evalClause, evalLiteral,
      houtput, hl, hr]

/-- Consecutive auxiliary-variable index for one threshold state. -/
def thresholdVar (start cap row threshold : ℕ) : ℕ :=
  start + row * (cap + 1) + threshold

/-- Number of true inputs in a prefix. -/
def truePrefixCount (assignment : ℕ → Bool) (vars : List ℕ)
    (row : ℕ) : ℕ :=
  (vars.take row).countP assignment

/-- Canonical valuation of one threshold-counter block.  Variables below
`start` retain their original values. -/
def thresholdValuation (start cap : ℕ) (vars : List ℕ)
    (assignment : ℕ → Bool) (i : ℕ) : Bool :=
  if i < start then assignment i
  else
    let offset := i - start
    let row := offset / (cap + 1)
    let threshold := offset % (cap + 1)
    if row ≤ vars.length then
      decide (threshold ≤ truePrefixCount assignment vars row)
    else assignment i

theorem thresholdValuation_of_lt (start cap : ℕ) (vars : List ℕ)
    (assignment : ℕ → Bool) {i : ℕ} (hi : i < start) :
    thresholdValuation start cap vars assignment i = assignment i := by
  simp [thresholdValuation, hi]

theorem thresholdValuation_thresholdVar (start cap : ℕ)
    (vars : List ℕ) (assignment : ℕ → Bool)
    {row threshold : ℕ} (hrow : row ≤ vars.length)
    (hthreshold : threshold ≤ cap) :
    thresholdValuation start cap vars assignment
        (thresholdVar start cap row threshold) =
      decide (threshold ≤ truePrefixCount assignment vars row) := by
  have hpositive : 0 < cap + 1 := by omega
  have hthreshold' : threshold < cap + 1 := by omega
  have hstart : ¬ thresholdVar start cap row threshold < start := by
    rw [thresholdVar]
    omega
  simp only [thresholdValuation, if_neg hstart]
  have hoffset : thresholdVar start cap row threshold - start =
      row * (cap + 1) + threshold := by
    rw [thresholdVar, Nat.add_assoc, Nat.add_sub_cancel_left]
  rw [hoffset]
  have hmod : (row * (cap + 1) + threshold) % (cap + 1) = threshold := by
    rw [Nat.mul_comm row, Nat.mul_add_mod,
      Nat.mod_eq_of_lt hthreshold']
  have hdiv : (row * (cap + 1) + threshold) / (cap + 1) = row := by
    rw [Nat.mul_comm row, Nat.mul_add_div hpositive,
      Nat.div_eq_of_lt hthreshold', add_zero]
  rw [hmod, hdiv]
  simp [hrow]

/-- Initial and transition clauses for the threshold counter.  The final
exact-count units are added by `sequentialExactCountFmla`. -/
def thresholdCounterFmla (start cap : ℕ) (vars : List ℕ) : Sat.Fmla :=
  (((List.range (vars.length + 1)).map fun row =>
      ([Sat.Literal.pos (thresholdVar start cap row 0)] : Sat.Clause)) :
        Sat.Fmla) ++
    (((List.range cap).map fun threshold =>
      ([Sat.Literal.neg (thresholdVar start cap 0 (threshold + 1))] :
        Sat.Clause)) : Sat.Fmla) ++
    (vars.zipIdx.flatMap fun bitAndRow =>
      (List.range cap).flatMap fun threshold =>
        thresholdStepFmla
          (thresholdVar start cap (bitAndRow.2 + 1) (threshold + 1))
          (thresholdVar start cap bitAndRow.2 (threshold + 1))
          bitAndRow.1
          (thresholdVar start cap bitAndRow.2 threshold))

/-- Polynomial CNF saying that exactly `need` input variables are true.
Its auxiliary block occupies `(vars.length + 1) * (need + 2)` variables. -/
def sequentialExactCountFmla (start : ℕ) (vars : List ℕ)
    (need : ℕ) : Sat.Fmla :=
  let cap := need + 1
  thresholdCounterFmla start cap vars ++
    ([[Sat.Literal.pos (thresholdVar start cap vars.length need)],
      [Sat.Literal.neg (thresholdVar start cap vars.length (need + 1))]] :
        Sat.Fmla)

private theorem truePrefixCount_zero (assignment : ℕ → Bool)
    (vars : List ℕ) :
    truePrefixCount assignment vars 0 = 0 := by
  simp [truePrefixCount]

private theorem truePrefixCount_succ (assignment : ℕ → Bool)
    (vars : List ℕ) {row : ℕ} (hrow : row < vars.length) :
    truePrefixCount assignment vars (row + 1) =
      truePrefixCount assignment vars row +
        if assignment vars[row] then 1 else 0 := by
  rw [truePrefixCount, truePrefixCount, List.take_add_one,
    List.getElem?_eq_getElem hrow, List.countP_append]
  simp

private theorem threshold_step (count : ℕ) (bit : Bool)
    (threshold : ℕ) :
    decide (threshold + 1 ≤ count + if bit then 1 else 0) =
      (decide (threshold + 1 ≤ count) ||
        (bit && decide (threshold ≤ count))) := by
  cases bit <;> simp <;> omega

/-- The canonical threshold valuation satisfies every counter transition,
provided all input variables lie below the fresh-variable boundary. -/
theorem eval_thresholdCounterFmla_eq_true
    (start cap : ℕ) (vars : List ℕ) (assignment : ℕ → Bool)
    (hfresh : ∀ var ∈ vars, var < start) :
    evalFmla (thresholdValuation start cap vars assignment)
      (thresholdCounterFmla start cap vars) = true := by
  rw [thresholdCounterFmla, evalFmla, List.all_append,
    List.all_append, Bool.and_eq_true]
  constructor
  · rw [Bool.and_eq_true]
    constructor
    · rw [List.all_eq_true]
      intro clause hclause
      rw [List.mem_map] at hclause
      obtain ⟨row, hrow, rfl⟩ := hclause
      have hrow' : row ≤ vars.length := by
        have := List.mem_range.mp hrow
        omega
      rw [evalClause]
      simp [evalLiteral,
        thresholdValuation_thresholdVar start cap vars assignment hrow'
          (Nat.zero_le cap), truePrefixCount]
    · rw [List.all_eq_true]
      intro clause hclause
      rw [List.mem_map] at hclause
      obtain ⟨threshold, hthreshold, rfl⟩ := hclause
      have hthreshold' : threshold + 1 ≤ cap := by
        have := List.mem_range.mp hthreshold
        omega
      rw [evalClause]
      simp [evalLiteral,
        thresholdValuation_thresholdVar start cap vars assignment
          (Nat.zero_le _) hthreshold', truePrefixCount_zero]
  · rw [List.all_eq_true]
    intro clause hclause
    rw [List.mem_flatMap] at hclause
    obtain ⟨bitAndRow, hbitAndRow, hclause⟩ := hclause
    rcases bitAndRow with ⟨bit, row⟩
    have hindexed := List.mem_zipIdx hbitAndRow
    simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and] at hindexed
    rcases hindexed with ⟨hrowLt, hbit⟩
    rw [hbit] at hclause
    rw [List.mem_flatMap] at hclause
    obtain ⟨threshold, hthreshold, hclause⟩ := hclause
    have hthresholdLt : threshold < cap := List.mem_range.mp hthreshold
    have hbitFresh : vars[row] < start :=
      hfresh vars[row] (List.getElem_mem hrowLt)
    have hstep :
        thresholdValuation start cap vars assignment
            (thresholdVar start cap (row + 1) (threshold + 1)) =
          (thresholdValuation start cap vars assignment
              (thresholdVar start cap row (threshold + 1)) ||
            (thresholdValuation start cap vars assignment vars[row] &&
              thresholdValuation start cap vars assignment
                (thresholdVar start cap row threshold))) := by
      rw [thresholdValuation_thresholdVar start cap vars assignment
          (by omega) (by omega),
        thresholdValuation_thresholdVar start cap vars assignment
          (by omega) (by omega),
        thresholdValuation_of_lt start cap vars assignment hbitFresh,
        thresholdValuation_thresholdVar start cap vars assignment
          (by omega) (by omega),
        truePrefixCount_succ assignment vars hrowLt,
        threshold_step]
    have heval := eval_thresholdStepFmla_eq_true
      (thresholdValuation start cap vars assignment) hstep
    rw [evalFmla, List.all_eq_true] at heval
    exact heval clause hclause

/-- A primary assignment of exact weight extends canonically to a model of the
sequential exact-count CNF. -/
theorem eval_sequentialExactCountFmla_eq_true
    (start : ℕ) (vars : List ℕ) (need : ℕ)
    (assignment : ℕ → Bool)
    (hfresh : ∀ var ∈ vars, var < start)
    (hcount : vars.countP assignment = need) :
    evalFmla (thresholdValuation start (need + 1) vars assignment)
      (sequentialExactCountFmla start vars need) = true := by
  rw [sequentialExactCountFmla, evalFmla, List.all_append,
    Bool.and_eq_true]
  constructor
  · exact eval_thresholdCounterFmla_eq_true start (need + 1) vars
      assignment hfresh
  · rw [List.all_eq_true]
    intro clause hclause
    rcases List.mem_cons.mp hclause with rfl | hclause
    · rw [evalClause]
      simp only [evalLiteral, List.any_cons, List.any_nil, Bool.or_false]
      rw [thresholdValuation_thresholdVar start (need + 1) vars assignment
        (row := vars.length) (threshold := need)
        (Nat.le_refl _) (Nat.le_succ need)]
      simp [truePrefixCount, hcount]
    · have heq := List.mem_singleton.mp hclause
      subst clause
      rw [evalClause]
      simp only [evalLiteral, List.any_cons, List.any_nil, Bool.or_false]
      rw [thresholdValuation_thresholdVar start (need + 1) vars assignment
        (row := vars.length) (threshold := need + 1)
        (Nat.le_refl _) (Nat.le_refl _)]
      simp [truePrefixCount, hcount]

/-! ## Serial composition -/

/-- The variable named by a literal. -/
def literalVar : Sat.Literal → ℕ
  | .pos i => i
  | .neg i => i

/-- Every variable occurring in a formula lies below a boundary. -/
def FmlaBelow (bound : ℕ) (fmla : Sat.Fmla) : Prop :=
  ∀ (clause : Sat.Clause),
    clause ∈ (show List Sat.Clause from fmla) →
      ∀ (literal : Sat.Literal),
        literal ∈ (show List Sat.Literal from clause) →
          literalVar literal < bound

private theorem evalLiteral_eq_of_below
    {left right : ℕ → Bool} {bound : ℕ}
    (heq : ∀ i < bound, left i = right i)
    (literal : Sat.Literal) (hliteral : literalVar literal < bound) :
    evalLiteral left literal = evalLiteral right literal := by
  cases literal with
  | pos i => simpa [literalVar, evalLiteral] using heq i hliteral
  | neg i => simp [evalLiteral, heq i hliteral]

private theorem evalClause_eq_of_below
    {left right : ℕ → Bool} {bound : ℕ}
    (heq : ∀ i < bound, left i = right i) :
    ∀ clause : List Sat.Literal,
      (∀ (literal : Sat.Literal), literal ∈ clause →
        literalVar literal < bound) →
        evalClause left clause = evalClause right clause := by
  intro clause
  induction clause with
  | nil => intro; rfl
  | cons literal clause ih =>
      intro hbelow
      have hiheq := ih (fun item hitem => hbelow item (by simp [hitem]))
      rw [evalClause, evalClause, List.any_cons, List.any_cons,
        evalLiteral_eq_of_below heq literal (hbelow literal (by simp))]
      exact congrArg (fun tail => evalLiteral right literal || tail) hiheq

theorem evalFmla_eq_of_below
    {left right : ℕ → Bool} {bound : ℕ} {fmla : Sat.Fmla}
    (hbelow : FmlaBelow bound fmla)
    (heq : ∀ i < bound, left i = right i) :
    evalFmla left fmla = evalFmla right fmla := by
  induction fmla with
  | nil => rfl
  | cons clause fmla ih =>
      have hiheq := ih (fun tail htail literal hliteral =>
        hbelow tail (by simp [htail]) literal hliteral)
      rw [evalFmla, evalFmla, List.all_cons, List.all_cons,
        evalClause_eq_of_below heq clause
          (fun literal hliteral => hbelow clause (by simp) literal hliteral)]
      exact congrArg (fun tail => evalClause right clause && tail) hiheq

private theorem thresholdVar_lt_end
    {start cap row threshold rows : ℕ}
    (hrow : row < rows) (hthreshold : threshold ≤ cap) :
    thresholdVar start cap row threshold < start + rows * (cap + 1) := by
  have hpositive : 0 < cap + 1 := by omega
  have hthreshold' : threshold < cap + 1 := by omega
  have hfirst : row * (cap + 1) + threshold <
      (row + 1) * (cap + 1) := by
    rw [Nat.add_mul]
    omega
  have hsecond : (row + 1) * (cap + 1) ≤ rows * (cap + 1) :=
    Nat.mul_le_mul_right (cap + 1) hrow
  rw [thresholdVar]
  omega

theorem thresholdStepFmla_below {bound output same bit less : ℕ}
    (houtput : output < bound) (hsame : same < bound)
    (hbit : bit < bound) (hless : less < bound) :
    FmlaBelow bound (thresholdStepFmla output same bit less) := by
  intro clause hclause literal hliteral
  rw [thresholdStepFmla] at hclause
  rcases List.mem_cons.mp hclause with rfl | hclause
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hliteral
    rcases hliteral with rfl | rfl <;> assumption
  · rcases List.mem_cons.mp hclause with rfl | hclause
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hliteral
      rcases hliteral with rfl | rfl | rfl <;> assumption
    · rcases List.mem_cons.mp hclause with rfl | hclause
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hliteral
        rcases hliteral with rfl | rfl | rfl <;> assumption
      · have heq := List.mem_singleton.mp hclause
        subst clause
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hliteral
        rcases hliteral with rfl | rfl | rfl <;> assumption

theorem andGateFmla_below {bound output left right : ℕ}
    (houtput : output < bound) (hleft : left < bound)
    (hright : right < bound) :
    FmlaBelow bound (andGateFmla output left right) := by
  intro clause hclause literal hliteral
  rw [andGateFmla] at hclause
  rcases List.mem_cons.mp hclause with rfl | hclause
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hliteral
    rcases hliteral with rfl | rfl <;> assumption
  · rcases List.mem_cons.mp hclause with rfl | hclause
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hliteral
      rcases hliteral with rfl | rfl <;> assumption
    · have heq := List.mem_singleton.mp hclause
      subst clause
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hliteral
      rcases hliteral with rfl | rfl | rfl <;> assumption

theorem sequentialExactCountFmla_below
    (start : ℕ) (vars : List ℕ) (need : ℕ)
    (hfresh : ∀ var ∈ vars, var < start) :
    FmlaBelow (start + (vars.length + 1) * (need + 2))
      (sequentialExactCountFmla start vars need) := by
  let cap := need + 1
  let bound := start + (vars.length + 1) * (cap + 1)
  have hstate : ∀ {row threshold : ℕ}, row ≤ vars.length →
      threshold ≤ cap → thresholdVar start cap row threshold < bound := by
    intro row threshold hrow hthreshold
    apply thresholdVar_lt_end (rows := vars.length + 1)
    · omega
    · exact hthreshold
  change FmlaBelow bound (sequentialExactCountFmla start vars need)
  intro clause hclause literal hliteral
  rw [sequentialExactCountFmla, List.mem_append] at hclause
  rcases hclause with hcounter | hfinal
  · rw [thresholdCounterFmla, List.mem_append,
      List.mem_append] at hcounter
    rcases hcounter with (hzero | hinitial) | hstep
    · rw [List.mem_map] at hzero
      obtain ⟨row, hrow, rfl⟩ := hzero
      have hrow' : row ≤ vars.length := by
        have := List.mem_range.mp hrow
        omega
      have heq := List.mem_singleton.mp hliteral
      subst literal
      exact hstate hrow' (Nat.zero_le cap)
    · rw [List.mem_map] at hinitial
      obtain ⟨threshold, hthreshold, rfl⟩ := hinitial
      have hthreshold' : threshold + 1 ≤ cap := by
        have := List.mem_range.mp hthreshold
        omega
      have heq := List.mem_singleton.mp hliteral
      subst literal
      exact hstate (row := 0) (Nat.zero_le _) hthreshold'
    · rw [List.mem_flatMap] at hstep
      obtain ⟨bitAndRow, hbitAndRow, hstep⟩ := hstep
      rcases bitAndRow with ⟨bit, row⟩
      have hindexed := List.mem_zipIdx hbitAndRow
      simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and] at hindexed
      rcases hindexed with ⟨hrow, hbit⟩
      rw [hbit] at hstep
      rw [List.mem_flatMap] at hstep
      obtain ⟨threshold, hthreshold, hstep⟩ := hstep
      have hthreshold' : threshold < cap := List.mem_range.mp hthreshold
      have hboundPos : 0 < (vars.length + 1) * (cap + 1) :=
        Nat.mul_pos (by omega) (by omega)
      exact thresholdStepFmla_below
        (hstate (row := row + 1) (threshold := threshold + 1)
          (by omega) (by omega))
        (hstate (row := row) (threshold := threshold + 1)
          (by omega) (by omega))
        (Nat.lt_trans (hfresh vars[row] (List.getElem_mem hrow))
          (Nat.lt_add_of_pos_right hboundPos))
        (hstate (row := row) (threshold := threshold)
          (by omega) (by omega)) clause hstep literal hliteral
  · rcases List.mem_cons.mp hfinal with rfl | hfinal
    · have heq := List.mem_singleton.mp hliteral
      subst literal
      exact hstate (row := vars.length) (threshold := need)
        (Nat.le_refl _) (by dsimp [cap]; omega)
    · have hclause := List.mem_singleton.mp hfinal
      subst clause
      have heq := List.mem_singleton.mp hliteral
      subst literal
      exact hstate (row := vars.length) (threshold := need + 1)
        (Nat.le_refl _) (by exact Nat.le_refl _)

/-- One exact-count constraint for serial CNF construction. -/
structure SequentialCountConstraint where
  vars : List ℕ
  need : ℕ
deriving DecidableEq, Repr

namespace SequentialCountConstraint

/-- Number of auxiliary variables reserved by this constraint. -/
def auxiliarySize (constraint : SequentialCountConstraint) : ℕ :=
  (constraint.vars.length + 1) * (constraint.need + 2)

end SequentialCountConstraint

/-- Concatenate disjoint threshold-counter blocks. -/
def sequentialExactCountsFmla : ℕ →
    List SequentialCountConstraint → Sat.Fmla
  | _, [] => []
  | start, constraint :: constraints =>
      sequentialExactCountFmla start constraint.vars constraint.need ++
        sequentialExactCountsFmla
          (start + constraint.auxiliarySize) constraints

/-- Canonical valuation for a serial family of threshold counters. -/
def sequentialExactCountsValuation : ℕ →
    List SequentialCountConstraint → (ℕ → Bool) → ℕ → Bool
  | _, [], assignment => assignment
  | start, constraint :: constraints, assignment =>
      sequentialExactCountsValuation
        (start + constraint.auxiliarySize) constraints
        (thresholdValuation start (constraint.need + 1)
          constraint.vars assignment)

theorem sequentialExactCountsValuation_of_lt
    (start : ℕ) (constraints : List SequentialCountConstraint)
    (assignment : ℕ → Bool) {i : ℕ} (hi : i < start) :
    sequentialExactCountsValuation start constraints assignment i =
      assignment i := by
  induction constraints generalizing start assignment with
  | nil => rfl
  | cons constraint constraints ih =>
      rw [sequentialExactCountsValuation,
        ih (start + constraint.auxiliarySize)
          (thresholdValuation start (constraint.need + 1)
            constraint.vars assignment) (by omega),
        thresholdValuation_of_lt start (constraint.need + 1)
          constraint.vars assignment hi]

private theorem countP_eq_of_eq_on_mem {left right : ℕ → Bool}
    (vars : List ℕ) (heq : ∀ var ∈ vars, left var = right var) :
    vars.countP left = vars.countP right := by
  induction vars with
  | nil => rfl
  | cons var vars ih =>
      rw [List.countP_cons, List.countP_cons, heq var (by simp),
        ih (fun item hitem => heq item (by simp [hitem]))]

/-- Every exact primary count has a canonical model of all serial counter
clauses. -/
theorem eval_sequentialExactCountsFmla_eq_true
    (start : ℕ) (constraints : List SequentialCountConstraint)
    (assignment : ℕ → Bool)
    (hfresh : ∀ constraint ∈ constraints,
      ∀ var ∈ constraint.vars, var < start)
    (hcounts : ∀ constraint ∈ constraints,
      constraint.vars.countP assignment = constraint.need) :
    evalFmla (sequentialExactCountsValuation start constraints assignment)
      (sequentialExactCountsFmla start constraints) = true := by
  induction constraints generalizing start assignment with
  | nil => rfl
  | cons constraint constraints ih =>
      let next := start + constraint.auxiliarySize
      let headAssignment := thresholdValuation start (constraint.need + 1)
        constraint.vars assignment
      let finalAssignment := sequentialExactCountsValuation next constraints
        headAssignment
      have hheadFresh : ∀ var ∈ constraint.vars, var < start :=
        fun var hvar => hfresh constraint (by simp) var hvar
      have hheadCount : constraint.vars.countP assignment = constraint.need :=
        hcounts constraint (by simp)
      have hheadEval : evalFmla headAssignment
          (sequentialExactCountFmla start constraint.vars constraint.need) =
          true :=
        eval_sequentialExactCountFmla_eq_true start constraint.vars
          constraint.need assignment hheadFresh hheadCount
      have hheadBelow : FmlaBelow next
          (sequentialExactCountFmla start constraint.vars constraint.need) := by
        simpa [next, SequentialCountConstraint.auxiliarySize] using
          sequentialExactCountFmla_below start constraint.vars
            constraint.need hheadFresh
      have hfinalHead : evalFmla finalAssignment
          (sequentialExactCountFmla start constraint.vars constraint.need) =
          true := by
        rw [evalFmla_eq_of_below hheadBelow
          (fun i hi => sequentialExactCountsValuation_of_lt
            next constraints headAssignment hi)]
        exact hheadEval
      have htailFresh : ∀ tail ∈ constraints,
          ∀ var ∈ tail.vars, var < next := by
        intro tail htail var hvar
        have hlt := hfresh tail (by simp [htail]) var hvar
        omega
      have htailCounts : ∀ tail ∈ constraints,
          tail.vars.countP headAssignment = tail.need := by
        intro tail htail
        rw [countP_eq_of_eq_on_mem tail.vars (fun var hvar =>
          thresholdValuation_of_lt start (constraint.need + 1)
            constraint.vars assignment
            (hfresh tail (by simp [htail]) var hvar))]
        exact hcounts tail (by simp [htail])
      have htailEval : evalFmla finalAssignment
          (sequentialExactCountsFmla next constraints) = true :=
        ih next headAssignment htailFresh htailCounts
      rw [sequentialExactCountsFmla, evalFmla, List.all_append,
        Bool.and_eq_true]
      exact ⟨hfinalHead, htailEval⟩

/-- A bounded CNF prefix and a serial exact-count family may be checked
independently and then concatenated. -/
theorem eval_prefix_append_sequentialExactCountsFmla_eq_true
    (start : ℕ) (prefixFmla : Sat.Fmla)
    (constraints : List SequentialCountConstraint)
    (assignment : ℕ → Bool)
    (hprefixBelow : FmlaBelow start prefixFmla)
    (hprefix : evalFmla assignment prefixFmla = true)
    (hfresh : ∀ constraint ∈ constraints,
      ∀ var ∈ constraint.vars, var < start)
    (hcounts : ∀ constraint ∈ constraints,
      constraint.vars.countP assignment = constraint.need) :
    evalFmla (sequentialExactCountsValuation start constraints assignment)
      (prefixFmla ++ sequentialExactCountsFmla start constraints) = true := by
  rw [evalFmla, List.all_append, Bool.and_eq_true]
  constructor
  · change evalFmla
        (sequentialExactCountsValuation start constraints assignment)
        prefixFmla = true
    rw [evalFmla_eq_of_below hprefixBelow
      (fun i hi => sequentialExactCountsValuation_of_lt
        start constraints assignment hi)]
    exact hprefix
  · exact eval_sequentialExactCountsFmla_eq_true start constraints
      assignment hfresh hcounts

end SRG266.Search
