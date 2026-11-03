import VOA.DeligneAudit.D4LeviKSPairSymmetricMap

/-! Surjectivity and the kernel of symmetric PAIR restriction. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

private theorem pairTargetPower_has_preimage (a b c : ℕ) (j : Fin 3) (r : ℕ) :
    ∃ P : pairSourceSymmetric a b c,
      pairSymmetricRestriction a b c P =
        ⟨pairTargetPower a b c j r, pairTargetPower_mem a b c j r⟩ := by
  fin_cases j
  · have hX : pairSourceXPsum a b c r ∈ pairSourceSymmetric a b c := by
      simpa [pairSourcePower] using pairSourcePower_mem a b c 0 r
    have hY : sourceYPsum a b c r ∈ pairSourceSymmetric a b c := by
      simpa [pairSourcePower] using pairSourcePower_mem a b c 1 r
    refine ⟨⟨pairSourceXPsum a b c r - sourceYPsum a b c r,
      (pairSourceSymmetric a b c).sub_mem hX hY⟩, ?_⟩
    apply Subtype.ext
    simp [pairSymmetricRestriction_apply, pairRestriction_XPsum,
      pairRestriction_sourceYPsum, pairTargetPower]
  · have hY : sourceYPsum a b c r ∈ pairSourceSymmetric a b c := by
      simpa [pairSourcePower] using pairSourcePower_mem a b c 1 r
    refine ⟨⟨sourceYPsum a b c r, hY⟩, ?_⟩
    apply Subtype.ext
    simp [pairSymmetricRestriction_apply, pairRestriction_sourceYPsum,
      pairTargetPower]
  · have hZ : pairSourceZPsum a b c r ∈ pairSourceSymmetric a b c := by
      simpa [pairSourcePower] using pairSourcePower_mem a b c 2 r
    refine ⟨⟨pairSourceZPsum a b c r, hZ⟩, ?_⟩
    apply Subtype.ext
    simp [pairSymmetricRestriction_apply, pairRestriction_ZPsum,
      pairTargetPower]

/-- Every separately symmetric target polynomial has a separately
    symmetric source representative. -/
theorem pairSymmetricRestriction_surjective (a b c : ℕ) :
    Function.Surjective (pairSymmetricRestriction a b c) := by
  rintro ⟨P, hP⟩
  induction hP using Algebra.adjoin_induction with
  | mem P hP =>
      rcases hP with ⟨⟨j, r⟩, rfl⟩
      exact pairTargetPower_has_preimage a b c j r
  | algebraMap z =>
      refine ⟨algebraMap ℂ (pairSourceSymmetric a b c) z, ?_⟩
      apply Subtype.ext
      simp
  | add P Q _ _ hP hQ =>
      obtain ⟨u, hu⟩ := hP
      obtain ⟨v, hv⟩ := hQ
      refine ⟨u + v, ?_⟩
      rw [map_add, hu, hv]
      apply Subtype.ext
      rfl
  | mul P Q _ _ hP hQ =>
      obtain ⟨u, hu⟩ := hP
      obtain ⟨v, hv⟩ := hQ
      refine ⟨u * v, ?_⟩
      rw [map_mul, hu, hv]
      apply Subtype.ext
      rfl

/-- The symmetric kernel is exactly the intersection with the ideal of
    paired-variable differences in the labelled polynomial ring. -/
theorem pairSymmetricRestriction_kernel_iff (a b c : ℕ)
    (P : pairSourceSymmetric a b c) :
    P ∈ RingHom.ker (pairSymmetricRestriction a b c).toRingHom ↔
      (P : MvPolynomial (PairSource a b c) ℂ) ∈
        pairVariableIdeal a b c := by
  rw [← pairRestriction_kernel]
  simp only [RingHom.mem_ker]
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    simpa [pairSymmetricRestriction_apply] using hv
  · intro h
    apply Subtype.ext
    simpa [pairSymmetricRestriction_apply] using h

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairSymmetricRestriction_surjective
#print axioms VOA.DeligneAudit.D4Levi.pairSymmetricRestriction_kernel_iff
