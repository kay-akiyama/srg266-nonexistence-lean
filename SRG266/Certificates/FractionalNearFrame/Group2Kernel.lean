import SRG266.Certificates.FractionalNearFrame.Group2KernelRule
import SRG266.Certificates.FractionalNearFrame.Group2Representative0000Proof
import SRG266.Certificates.FractionalNearFrame.Group2Chunk0000TailKernel
import SRG266.Certificates.FractionalNearFrame.Group2Chunk0279Kernel
import SRG266.Certificates.FractionalNearFrame.Group2Chunk0558Kernel
import SRG266.Certificates.FractionalNearFrame.Group2Chunk0837Kernel
import SRG266.Certificates.FractionalNearFrame.Group2Chunk1116Kernel
import SRG266.QuasiSymmetric.FractionalNearFrameKernelSplit

/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Group 2 without a native Farkas audit

Each of the five tail chunks has a kernel Farkas rule of its own, and
representative zero keeps its bounded kernel proof, so the group dispatcher
does not reduce stored witnesses natively.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- Every group-2 normal form is impossible, with no native audit anywhere in
the proof term. -/
theorem noCompactFractionalNearFrame_of_mem_group2_kernel
    {nearMask : ℕ} (hmem : nearMask ∈ rootNearRepresentativeGroup2) :
    NoCompactFractionalNearFrame nearMask := by
  rw [← fractionalNearFrameCertificatesGroup2_masks] at hmem
  obtain ⟨entry, hentry, hmask⟩ := List.mem_map.mp hmem
  subst nearMask
  rw [fractionalNearFrameCertificatesGroup2,
    fractionalNearFrameCertificatesGroup2Tail] at hentry
  rcases List.mem_cons.mp hentry with hfirst | htail
  · subst entry
    exact fractionalNearFrameGroup2Representative0000_noFrame
  · rcases List.mem_append.mp htail with htail | h1116
    · rcases List.mem_append.mp htail with htail | h0837
      · rcases List.mem_append.mp htail with htail | h0558
        · rcases List.mem_append.mp htail with h0000 | h0279
          · exact noCompactFractionalNearFrame_of_mem_kernel_split
              fractionalNearFrameCertificatesGroup2Chunk0000Tail
              fractionalNearFrameCertificatesGroup2Chunk0000Tail_emptyRule
              group2Chunk0000TailFarkasRule h0000
          · exact noCompactFractionalNearFrame_of_mem_kernel_split
              fractionalNearFrameCertificatesGroup2Chunk0279
              fractionalNearFrameCertificatesGroup2Chunk0279_emptyRule
              group2Chunk0279FarkasRule h0279
        · exact noCompactFractionalNearFrame_of_mem_kernel_split
            fractionalNearFrameCertificatesGroup2Chunk0558
            fractionalNearFrameCertificatesGroup2Chunk0558_emptyRule
            group2Chunk0558FarkasRule h0558
      · exact noCompactFractionalNearFrame_of_mem_kernel_split
          fractionalNearFrameCertificatesGroup2Chunk0837
          fractionalNearFrameCertificatesGroup2Chunk0837_emptyRule
          group2Chunk0837FarkasRule h0837
    · exact noCompactFractionalNearFrame_of_mem_kernel_split
        fractionalNearFrameCertificatesGroup2Chunk1116
        fractionalNearFrameCertificatesGroup2Chunk1116_emptyRule
        group2Chunk1116FarkasRule h1116

end SRG266.Certificates
