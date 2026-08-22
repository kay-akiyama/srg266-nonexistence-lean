/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.E7ComponentKeyCoverage
import SRG266.Certificates.E7ScalarPairAudit
import SRG266.Hosts.E7ScalarTraceSubset

/-!
# `E7ScalarDPAuditInput` as a kernel-checked instance

Feeding the two audited chunk sweeps into `e7Trace_subset_of_checks`
discharges the scalar-DP and trace audit interface.  Every step is a kernel
evaluation or an ordinary proof; nothing here is an axiom.

This module is outside the default build because its two imports are: the
coverage sweep and the pair scan are gigabyte-scale kernel evaluations that
must be run one at a time.  See
`scripts/build_e7_component_key_chunks.py` and
`scripts/build_e7_scalar_pair_chunks.py`.
-/

namespace SRG266

theorem e7Trace_subset
    (pair : E7ComponentKey × E7ComponentKey)
    (hpair : pair ∈ e7TraceFeasibleHistogramPairs) :
    pair ∈ e7ListedCentroidHistogramPairsUpToSwap :=
  e7Trace_subset_of_checks
    e7ComponentKey_mem_listed_of_mem_enumeration
    e7CodeBucketOk_checked
    e7CandidatePairCheckAt_checked
    e7RefutedCodePairs_checked
    e7TraceCodePairs_checked
    e7ListedCentroidCodeOk_checked
    pair hpair

instance instE7ScalarDPAuditInput : E7ScalarDPAuditInput where
  trace_subset := e7Trace_subset

end SRG266
