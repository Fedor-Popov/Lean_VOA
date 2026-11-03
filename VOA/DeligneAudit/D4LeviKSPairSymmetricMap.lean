import VOA.DeligneAudit.D4LeviKSPairKernelAlgebra
import VOA.DeligneAudit.D4LeviKSPowerSums

/-! The PAIR substitution on three separately symmetric alphabets. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

noncomputable def pairSourceXPsum (a b c r : ℕ) :
    MvPolynomial (PairSource a b c) ℂ :=
  ∑ x : Fin b ⊕ Fin a, X (Sum.inl x) ^ r

noncomputable def pairSourceZPsum (a b c r : ℕ) :
    MvPolynomial (PairSource a b c) ℂ :=
  ∑ z : Fin c, X (Sum.inr (Sum.inr z)) ^ r

noncomputable def pairTargetXPsum (a b c r : ℕ) :
    MvPolynomial (PairTarget a b c) ℂ :=
  ∑ x : Fin a, X (Sum.inl x) ^ r

noncomputable def pairTargetZPsum (a b c r : ℕ) :
    MvPolynomial (PairTarget a b c) ℂ :=
  ∑ z : Fin c, X (Sum.inr (Sum.inr z)) ^ r

theorem pairRestriction_XPsum (a b c r : ℕ) :
    pairRestriction a b c (pairSourceXPsum a b c r) =
      targetYPsum a b c r + pairTargetXPsum a b c r := by
  simp [pairSourceXPsum, targetYPsum, pairTargetXPsum,
    Fintype.sum_sum_type, pairRestriction_paired_X,
    pairRestriction_unpaired_X]

theorem pairRestriction_ZPsum (a b c r : ℕ) :
    pairRestriction a b c (pairSourceZPsum a b c r) =
      pairTargetZPsum a b c r := by
  simp [pairSourceZPsum, pairTargetZPsum, pairRestriction_Z]

/-- Three power-sum families, one for each source alphabet. -/
noncomputable def pairSourcePower (a b c : ℕ) (j : Fin 3) (r : ℕ) :
    MvPolynomial (PairSource a b c) ℂ :=
  if j = 0 then pairSourceXPsum a b c r
  else if j = 1 then sourceYPsum a b c r
  else pairSourceZPsum a b c r

/-- Three power-sum families after PAIR restriction. -/
noncomputable def pairTargetPower (a b c : ℕ) (j : Fin 3) (r : ℕ) :
    MvPolynomial (PairTarget a b c) ℂ :=
  if j = 0 then pairTargetXPsum a b c r
  else if j = 1 then targetYPsum a b c r
  else pairTargetZPsum a b c r

/-- The power-sum presentation of separately symmetric source modes. -/
noncomputable def pairSourceSymmetric (a b c : ℕ) :
    Subalgebra ℂ (MvPolynomial (PairSource a b c) ℂ) :=
  Algebra.adjoin ℂ (Set.range fun p : Fin 3 × ℕ =>
    pairSourcePower a b c p.1 p.2)

noncomputable def pairTargetSymmetric (a b c : ℕ) :
    Subalgebra ℂ (MvPolynomial (PairTarget a b c) ℂ) :=
  Algebra.adjoin ℂ (Set.range fun p : Fin 3 × ℕ =>
    pairTargetPower a b c p.1 p.2)

theorem pairSourcePower_mem (a b c : ℕ) (j : Fin 3) (r : ℕ) :
    pairSourcePower a b c j r ∈ pairSourceSymmetric a b c :=
  Algebra.subset_adjoin ⟨(j, r), rfl⟩

theorem pairTargetPower_mem (a b c : ℕ) (j : Fin 3) (r : ℕ) :
    pairTargetPower a b c j r ∈ pairTargetSymmetric a b c :=
  Algebra.subset_adjoin ⟨(j, r), rfl⟩

theorem pairRestriction_sourcePower_mem (a b c : ℕ)
    (j : Fin 3) (r : ℕ) :
    pairRestriction a b c (pairSourcePower a b c j r) ∈
      pairTargetSymmetric a b c := by
  fin_cases j
  · change pairRestriction a b c (pairSourceXPsum a b c r) ∈ _
    rw [pairRestriction_XPsum]
    exact (pairTargetSymmetric a b c).add_mem
      (by simpa [pairTargetPower] using pairTargetPower_mem a b c 1 r)
      (by simpa [pairTargetPower] using pairTargetPower_mem a b c 0 r)
  · change pairRestriction a b c (sourceYPsum a b c r) ∈ _
    rw [pairRestriction_sourceYPsum]
    simpa [pairTargetPower] using pairTargetPower_mem a b c 1 r
  · change pairRestriction a b c (pairSourceZPsum a b c r) ∈ _
    rw [pairRestriction_ZPsum]
    simpa [pairTargetPower] using pairTargetPower_mem a b c 2 r

theorem pairRestriction_symmetric (a b c : ℕ) :
    pairSourceSymmetric a b c ≤
      (pairTargetSymmetric a b c).comap (pairRestriction a b c) := by
  apply Algebra.adjoin_le
  rintro P ⟨⟨j, r⟩, rfl⟩
  exact pairRestriction_sourcePower_mem a b c j r

/-- The PAIR restriction as an algebra map on separately symmetric modes. -/
noncomputable def pairSymmetricRestriction (a b c : ℕ) :
    pairSourceSymmetric a b c →ₐ[ℂ] pairTargetSymmetric a b c :=
  ((pairRestriction a b c).comp
    (Subalgebra.val (pairSourceSymmetric a b c))).codRestrict
      (pairTargetSymmetric a b c)
      (fun P => pairRestriction_symmetric a b c P.property)

theorem pairSymmetricRestriction_apply (a b c : ℕ)
    (P : pairSourceSymmetric a b c) :
    (pairSymmetricRestriction a b c P :
      MvPolynomial (PairTarget a b c) ℂ) = pairRestriction a b c P := rfl

/-- Multiplication by any Y/Z spectator polynomial commutes with PAIR
    substitution. This is the explicit module-linearity identity. -/
theorem pairRestriction_spectator_linear (a b c : ℕ)
    (S P : MvPolynomial (PairSource a b c) ℂ) :
    pairRestriction a b c (S * P) =
      pairRestriction a b c S * pairRestriction a b c P := map_mul _ _ _

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_XPsum
#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_ZPsum
#print axioms VOA.DeligneAudit.D4Levi.pairSourcePower_mem
#print axioms VOA.DeligneAudit.D4Levi.pairTargetPower_mem
#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_sourcePower_mem
#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_symmetric
#print axioms VOA.DeligneAudit.D4Levi.pairSymmetricRestriction_apply
#print axioms VOA.DeligneAudit.D4Levi.pairRestriction_spectator_linear
