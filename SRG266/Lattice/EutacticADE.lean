/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.RootLattice

/-!
# The finite ADE arithmetic behind the theta-eutaxy bypass

For a norm-one-free unimodular lattice of rank `n < 16`, the degree-two
weighted theta identity predicts that its roots are strongly eutactic with
constant `4 * (23 - n)`.  On an irreducible simply-laced root component the
same operator has constant twice the Coxeter number.  Consequently every ADE
component must have Coxeter number

`h = 2 * (23 - n)`.

This file proves the complete finite arithmetic consequence for the only
ranks relevant to `srg(266,45,0,9)`.  No lattice classification is used:

* rank 12, `h = 22`: `D12`;
* rank 13, `h = 20`: impossible;
* rank 14, `h = 18`: `E7 + E7`;
* rank 15, `h = 16`: `A15`.

Thus strong eutaxy and the standard ADE decomposition force the root-lattice
type without enumerating the 1,442 ADE multisets of rank 12--15.
-/

namespace SRG266
namespace Lattice

namespace ADEType

/-- The Coxeter number of an irreducible simply-laced root system. -/
def coxeterNumber : ADEType → ℕ
  | .A n => n + 1
  | .D n => 2 * n - 2
  | .E6 => 12
  | .E7 => 18
  | .E8 => 30

@[simp] theorem coxeterNumber_A (n : ℕ) : coxeterNumber (.A n) = n + 1 := rfl
@[simp] theorem coxeterNumber_D (n : ℕ) : coxeterNumber (.D n) = 2 * n - 2 := rfl
@[simp] theorem coxeterNumber_E6 : coxeterNumber .E6 = 12 := rfl
@[simp] theorem coxeterNumber_E7 : coxeterNumber .E7 = 18 := rfl
@[simp] theorem coxeterNumber_E8 : coxeterNumber .E8 = 30 := rfl

/-- At rank at most twelve, Coxeter number `22` forces `D12`. -/
theorem eq_D12_of_rank_le_twelve_of_coxeter_eq_twentyTwo
    (t : ADEType) (hrank : t.rank ≤ 12) (hcox : t.coxeterNumber = 22) :
    t = .D 12 := by
  cases t with
  | A n => simp only [rank, coxeterNumber] at hrank hcox; omega
  | D n => simp only [rank, coxeterNumber] at hrank hcox; congr 1; omega
  | E6 => simp at hcox
  | E7 => simp at hcox
  | E8 => simp at hcox

/-- At rank at most thirteen, Coxeter number `20` forces `D11`. -/
theorem eq_D11_of_rank_le_thirteen_of_coxeter_eq_twenty
    (t : ADEType) (hrank : t.rank ≤ 13) (hcox : t.coxeterNumber = 20) :
    t = .D 11 := by
  cases t with
  | A n => simp only [rank, coxeterNumber] at hrank hcox; omega
  | D n => simp only [rank, coxeterNumber] at hrank hcox; congr 1; omega
  | E6 => simp at hcox
  | E7 => simp at hcox
  | E8 => simp at hcox

/-- At rank at most fourteen, Coxeter number `18` leaves `D10` and `E7`. -/
theorem eq_D10_or_E7_of_rank_le_fourteen_of_coxeter_eq_eighteen
    (t : ADEType) (hrank : t.rank ≤ 14) (hcox : t.coxeterNumber = 18) :
    t = .D 10 ∨ t = .E7 := by
  cases t with
  | A n => simp only [rank, coxeterNumber] at hrank hcox; omega
  | D n => left; simp only [rank, coxeterNumber] at hrank hcox; congr 1; omega
  | E6 => simp at hcox
  | E7 => exact Or.inr rfl
  | E8 => simp at hcox

/-- At rank at most fifteen, Coxeter number `16` leaves `A15` and `D9`. -/
theorem eq_A15_or_D9_of_rank_le_fifteen_of_coxeter_eq_sixteen
    (t : ADEType) (hrank : t.rank ≤ 15) (hcox : t.coxeterNumber = 16) :
    t = .A 15 ∨ t = .D 9 := by
  cases t with
  | A n => left; simp only [rank, coxeterNumber] at hrank hcox; congr 1; omega
  | D n => right; simp only [rank, coxeterNumber] at hrank hcox; congr 1; omega
  | E6 => simp at hcox
  | E7 => simp at hcox
  | E8 => simp at hcox

end ADEType

private theorem head_rank_le_rankSum {t : ADEType} {ts : List ADEType} {n : ℕ}
    (h : ADEType.rankSum (t :: ts) = n) : t.rank ≤ n := by
  simp only [ADEType.rankSum_cons] at h
  omega

/-- Rank twelve and the common Coxeter number `22` force the single component
`D12`. -/
theorem ade_perm_D12_of_rankSum_twelve_of_coxeter_twentyTwo
    {ts : List ADEType} (hrank : ADEType.rankSum ts = 12)
    (hcox : ∀ t ∈ ts, t.coxeterNumber = 22) :
    ts.Perm [.D 12] := by
  cases ts with
  | nil => simp at hrank
  | cons t ts =>
      have ht := ADEType.eq_D12_of_rank_le_twelve_of_coxeter_eq_twentyTwo t
        (head_rank_le_rankSum hrank) (hcox t (by simp))
      subst t
      have htail : ADEType.rankSum ts = 0 := by
        simp only [ADEType.rankSum_cons, ADEType.rank] at hrank
        omega
      have hnil : ts = [] := by
        by_contra hne
        obtain ⟨s, ss, rfl⟩ := List.exists_cons_of_ne_nil hne
        have hscox : s.coxeterNumber = 22 := hcox s (by simp)
        have hsle : s.rank ≤ 12 := by
          simp only [ADEType.rankSum_cons] at htail
          omega
        have hs := ADEType.eq_D12_of_rank_le_twelve_of_coxeter_eq_twentyTwo s hsle hscox
        subst s
        simp only [ADEType.rankSum_cons, ADEType.rank] at htail
        omega
      subst ts
      simp

/-- There is no ADE root system of rank thirteen all of whose components have
Coxeter number `20`. -/
theorem no_ade_rankSum_thirteen_of_coxeter_twenty
    {ts : List ADEType} (hrank : ADEType.rankSum ts = 13)
    (hcox : ∀ t ∈ ts, t.coxeterNumber = 20) : False := by
  cases ts with
  | nil => simp at hrank
  | cons t ts =>
      have ht := ADEType.eq_D11_of_rank_le_thirteen_of_coxeter_eq_twenty t
        (head_rank_le_rankSum hrank) (hcox t (by simp))
      subst t
      have htail : ADEType.rankSum ts = 2 := by
        simp only [ADEType.rankSum_cons, ADEType.rank] at hrank
        omega
      cases ts with
      | nil => simp at htail
      | cons s ss =>
          have hscox : s.coxeterNumber = 20 := hcox s (by simp)
          have hsle : s.rank ≤ 13 := by
            simp only [ADEType.rankSum_cons] at htail
            omega
          have hs := ADEType.eq_D11_of_rank_le_thirteen_of_coxeter_eq_twenty s hsle hscox
          subst s
          simp only [ADEType.rankSum_cons, ADEType.rank] at htail
          omega

/-- Rank fourteen and the common Coxeter number `18` force `E7 + E7`. -/
theorem ade_perm_E7_E7_of_rankSum_fourteen_of_coxeter_eighteen
    {ts : List ADEType} (hrank : ADEType.rankSum ts = 14)
    (hcox : ∀ t ∈ ts, t.coxeterNumber = 18) :
    ts.Perm [.E7, .E7] := by
  cases ts with
  | nil => simp at hrank
  | cons t ts =>
      have ht := ADEType.eq_D10_or_E7_of_rank_le_fourteen_of_coxeter_eq_eighteen t
        (head_rank_le_rankSum hrank) (hcox t (by simp))
      rcases ht with rfl | rfl
      · have htail : ADEType.rankSum ts = 4 := by
          simp only [ADEType.rankSum_cons, ADEType.rank] at hrank
          omega
        cases ts with
        | nil => simp at htail
        | cons s ss =>
            have hscox : s.coxeterNumber = 18 := hcox s (by simp)
            have hsle : s.rank ≤ 14 := by
              simp only [ADEType.rankSum_cons] at htail
              omega
            rcases ADEType.eq_D10_or_E7_of_rank_le_fourteen_of_coxeter_eq_eighteen
                s hsle hscox with rfl | rfl <;>
              simp only [ADEType.rankSum_cons, ADEType.rank] at htail <;> omega
      · have htail : ADEType.rankSum ts = 7 := by
          simp only [ADEType.rankSum_cons, ADEType.rank] at hrank
          omega
        cases ts with
        | nil => simp at htail
        | cons s ss =>
            have hscox : s.coxeterNumber = 18 := hcox s (by simp)
            have hsle : s.rank ≤ 14 := by
              simp only [ADEType.rankSum_cons] at htail
              omega
            rcases ADEType.eq_D10_or_E7_of_rank_le_fourteen_of_coxeter_eq_eighteen
                s hsle hscox with rfl | rfl
            · simp only [ADEType.rankSum_cons, ADEType.rank] at htail
              omega
            · have hzero : ADEType.rankSum ss = 0 := by
                simp only [ADEType.rankSum_cons, ADEType.rank] at htail
                omega
              have hnil : ss = [] := by
                by_contra hne
                obtain ⟨r, rs, rfl⟩ := List.exists_cons_of_ne_nil hne
                have hrcox : r.coxeterNumber = 18 := hcox r (by simp)
                have hrle : r.rank ≤ 14 := by
                  simp only [ADEType.rankSum_cons] at hzero
                  omega
                rcases ADEType.eq_D10_or_E7_of_rank_le_fourteen_of_coxeter_eq_eighteen
                    r hrle hrcox with rfl | rfl <;>
                  simp only [ADEType.rankSum_cons, ADEType.rank] at hzero <;> omega
              subst ss
              simp

/-- Rank fifteen and the common Coxeter number `16` force the single component
`A15`. -/
theorem ade_perm_A15_of_rankSum_fifteen_of_coxeter_sixteen
    {ts : List ADEType} (hrank : ADEType.rankSum ts = 15)
    (hcox : ∀ t ∈ ts, t.coxeterNumber = 16) :
    ts.Perm [.A 15] := by
  cases ts with
  | nil => simp at hrank
  | cons t ts =>
      have ht := ADEType.eq_A15_or_D9_of_rank_le_fifteen_of_coxeter_eq_sixteen t
        (head_rank_le_rankSum hrank) (hcox t (by simp))
      rcases ht with rfl | rfl
      · have hzero : ADEType.rankSum ts = 0 := by
          simp only [ADEType.rankSum_cons, ADEType.rank] at hrank
          omega
        have hnil : ts = [] := by
          by_contra hne
          obtain ⟨s, ss, rfl⟩ := List.exists_cons_of_ne_nil hne
          have hscox : s.coxeterNumber = 16 := hcox s (by simp)
          have hsle : s.rank ≤ 15 := by
            simp only [ADEType.rankSum_cons] at hzero
            omega
          rcases ADEType.eq_A15_or_D9_of_rank_le_fifteen_of_coxeter_eq_sixteen
              s hsle hscox with rfl | rfl <;>
            simp only [ADEType.rankSum_cons, ADEType.rank] at hzero <;> omega
        subst ts
        simp
      · have htail : ADEType.rankSum ts = 6 := by
          simp only [ADEType.rankSum_cons, ADEType.rank] at hrank
          omega
        cases ts with
        | nil => simp at htail
        | cons s ss =>
            have hscox : s.coxeterNumber = 16 := hcox s (by simp)
            have hsle : s.rank ≤ 15 := by
              simp only [ADEType.rankSum_cons] at htail
              omega
            rcases ADEType.eq_A15_or_D9_of_rank_le_fifteen_of_coxeter_eq_sixteen
                s hsle hscox with rfl | rfl <;>
              simp only [ADEType.rankSum_cons, ADEType.rank] at htail <;> omega

/-- The four-rank form consumed by the lattice bypass. -/
theorem ade_eutactic_rank_cases
    {n : ℕ} (hnlo : 12 ≤ n) (hnhi : n ≤ 15) {ts : List ADEType}
    (hrank : ADEType.rankSum ts = n)
    (hcox : ∀ t ∈ ts, t.coxeterNumber = 2 * (23 - n)) :
    (n = 12 ∧ ts.Perm [.D 12]) ∨
      (n = 14 ∧ ts.Perm [.E7, .E7]) ∨
      (n = 15 ∧ ts.Perm [.A 15]) := by
  interval_cases n
  · left
    refine ⟨rfl, ade_perm_D12_of_rankSum_twelve_of_coxeter_twentyTwo hrank ?_⟩
    simpa using hcox
  · exact (no_ade_rankSum_thirteen_of_coxeter_twenty hrank (by simpa using hcox)).elim
  · right; left
    refine ⟨rfl, ade_perm_E7_E7_of_rankSum_fourteen_of_coxeter_eighteen hrank ?_⟩
    simpa using hcox
  · right; right
    refine ⟨rfl, ade_perm_A15_of_rankSum_fifteen_of_coxeter_sixteen hrank ?_⟩
    simpa using hcox

end Lattice
end SRG266
