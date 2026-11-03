import VOA.DeligneAudit.D4LeviKSBlockMaximal
import VOA.DeligneAudit.D4LeviKSFlagDegenerate

/-! The Z step of the partial-flag box reduction, with arbitrary target spectators. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

noncomputable def ksFlagZMultiplication (a b c : ℕ)
    (U : pairTargetSymmetric a b c) :
    MvPolynomial (Fin c) ℂ →ₗ[ℂ] MvPolynomial (PairTarget a b c) ℂ :=
  (LinearMap.mulLeft ℂ (U : MvPolynomial (PairTarget a b c) ℂ)).comp
    (rename (fun z : Fin c =>
      (Sum.inr (Sum.inr z) : PairTarget a b c))).toLinearMap

theorem ksHsymm_empty_of_pos (s : ℕ) (hs : 0 < s) :
    hsymm (Fin 0) ℂ s = 0 := by
  rw [← ksHSeries_coeff_hsymm]
  simp [ksHSeries, Nat.ne_of_gt hs]

/-- Maximal one-alphabet Z relations, multiplied by any target polynomial,
    are genuine members of the existing flag relation span. -/
theorem ksBlockMaximal_z_mul_le_flag (m a b c d e : ℕ) (hde : d ≤ e)
    (U : pairTargetSymmetric a b c) :
    (ksBlockMaximalSpan m c d).map (ksFlagZMultiplication a b c U) ≤
      (ksFlagMaximalRelationSpan m a b c e).map
        (Subalgebra.val (pairTargetSymmetric a b c)).toLinearMap := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro T ⟨s, hs, hsd, W, hW, rfl⟩
  change ksFlagZMultiplication a b c U (W * hsymm (Fin c) ℂ s) ∈
    (ksFlagMaximalRelationSpan m a b c e).map
      (Subalgebra.val (pairTargetSymmetric a b c)).toLinearMap
  by_cases hc : 1 ≤ c
  · let ZW : pairTargetSymmetric a b c :=
      ⟨rename (fun z : Fin c =>
        (Sum.inr (Sum.inr z) : PairTarget a b c)) W,
        pairTarget_symmetric_Z_mem a b c W hW⟩
    refine ⟨(U * ZW) * rzFullHSymm a b c s, ?_, ?_⟩
    · exact Submodule.subset_span (Or.inl
        ⟨s, e - s, U * ZW, hc, hs, by omega, rfl⟩)
    · change (U : MvPolynomial (PairTarget a b c) ℂ) *
          rename _ W * rename _ (hsymm (Fin c) ℂ s) =
        (U : MvPolynomial (PairTarget a b c) ℂ) *
          rename _ (W * hsymm (Fin c) ℂ s)
      rw [map_mul, mul_assoc]
  · have hc0 : c = 0 := by omega
    subst c
    rw [ksHsymm_empty_of_pos s (by omega), mul_zero, map_zero]
    exact Submodule.zero_mem _

/-- A homogeneous Z factor can be reduced to its exact-degree box, modulo
    the flag relations. The multiplier may contain arbitrary X, Y, and Z factors. -/
theorem ksFlag_z_box_step (m a b c d e : ℕ)
    (hc : c ≤ m) (hde : d ≤ e) (U : pairTargetSymmetric a b c)
    (P : MvPolynomial (Fin c) ℂ)
    (hP : P ∈ symmetricSubalgebra (Fin c) ℂ) (hd : P.IsHomogeneous d) :
    ksFlagZMultiplication a b c U P ∈
      Submodule.span ℂ
        (ksFlagZMultiplication a b c U '' (ksBlockBoxPolys m c d : Set _)) ⊔
      (ksFlagMaximalRelationSpan m a b c e).map
        (Subalgebra.val (pairTargetSymmetric a b c)).toLinearMap := by
  obtain ⟨B, hB, C, hC, rfl⟩ := Submodule.mem_sup.mp
    (ksBlockSymmetric_span_maximal m c d hc P hP hd)
  rw [map_add]
  apply Submodule.add_mem_sup
  · have hb : ksFlagZMultiplication a b c U B ∈
        (Submodule.span ℂ (ksBlockBoxPolys m c d : Set _)).map
          (ksFlagZMultiplication a b c U) := ⟨B, hB, rfl⟩
    simpa only [Submodule.map_span] using hb
  · exact ksBlockMaximal_z_mul_le_flag m a b c d e hde U ⟨C, hC, rfl⟩

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksHsymm_empty_of_pos
#print axioms VOA.DeligneAudit.D4Levi.ksBlockMaximal_z_mul_le_flag
#print axioms VOA.DeligneAudit.D4Levi.ksFlag_z_box_step
