/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.E7ScalarPairData
import SRG266.Hosts.E7CodeKeyArithmetic

/-!
# The eligible-pair filter on packed codes

Once every enumerated component key is known to be listed, the pair filters
become a finite statement about the 5,253 listed codes.  Bucketing them by
squared norm turns the search for norm-complementary eligible pairs into 151
independent scans, and each scan is one kernel evaluation of
`e7CandidatePairCheckAt`.
-/

namespace SRG266

set_option maxRecDepth 100000

/-- The listed codes of squared norm `2 * halfNorm`. -/
def e7CodesAtHalfNorm (halfNorm : ℕ) : List ℕ :=
  e7CodeNormBuckets.getD halfNorm []

/-- Every listed code sits in the bucket of its own squared norm. -/
def e7CodeBucketOk : Bool :=
  e7ListedKeyCodes.all fun code =>
    decide (code ∈ e7CodesAtHalfNorm (code % e7NormBase / 2))

/-- Every eligible norm-complementary pair of listed codes at this squared
norm is one of the listed candidate pairs. -/
def e7CandidatePairCheckAt (halfNorm : ℕ) : Bool :=
  (e7CodesAtHalfNorm halfNorm).all fun leftCode =>
    (e7CodesAtHalfNorm (150 - halfNorm)).all fun rightCode =>
      decide (e7CodeEligibleCount leftCode rightCode < 74) ||
        decide ((leftCode, rightCode) ∈ e7CandidateCodePairs)

theorem e7CandidateCodePair_of
    (hbucket : e7CodeBucketOk = true)
    (hcheck : ∀ halfNorm, 19 ≤ halfNorm → halfNorm ≤ 131 →
      e7CandidatePairCheckAt halfNorm = true)
    (leftCode rightCode halfNorm : ℕ)
    (hleft : leftCode ∈ e7ListedKeyCodes)
    (hright : rightCode ∈ e7ListedKeyCodes)
    (hleftNorm : leftCode % e7NormBase = 2 * halfNorm)
    (hrightNorm : rightCode % e7NormBase = 300 - 2 * halfNorm)
    (hhalf : halfNorm < 151)
    (hlow : 38 ≤ leftCode % e7NormBase)
    (hhigh : leftCode % e7NormBase ≤ 262)
    (hcount : 74 ≤ e7CodeEligibleCount leftCode rightCode) :
    (leftCode, rightCode) ∈ e7CandidateCodePairs := by
  have hbucketLeft :
      leftCode ∈ e7CodesAtHalfNorm halfNorm := by
    have := (List.all_eq_true.mp hbucket) leftCode hleft
    rw [decide_eq_true_eq] at this
    rwa [hleftNorm, Nat.mul_div_cancel_left _ (by norm_num)] at this
  have hbucketRight :
      rightCode ∈ e7CodesAtHalfNorm (150 - halfNorm) := by
    have := (List.all_eq_true.mp hbucket) rightCode hright
    rw [decide_eq_true_eq] at this
    have hdiv : rightCode % e7NormBase / 2 = 150 - halfNorm := by
      rw [hrightNorm]; omega
    rwa [hdiv] at this
  have hstep :=
    (List.all_eq_true.mp (hcheck halfNorm (by omega) (by omega)))
      leftCode hbucketLeft
  have hstep' := (List.all_eq_true.mp hstep) rightCode hbucketRight
  rcases Bool.or_eq_true_iff.mp hstep' with h | h
  · rw [decide_eq_true_eq] at h
    omega
  · rwa [decide_eq_true_eq] at h

end SRG266
