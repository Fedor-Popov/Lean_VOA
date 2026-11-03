import VOA.DeligneAudit.D4LeviKSFlagTargetRank
import VOA.DeligneAudit.D4LeviKSWordPresentation

/-! Homogeneous symmetric source representatives of labelled XYZ evaluations. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

def ksPairBlockPerm (a b c : ℕ) (ex : Equiv.Perm (Fin b ⊕ Fin a))
    (ey : Equiv.Perm (Fin b)) (ez : Equiv.Perm (Fin c)) :
    Equiv.Perm (PairSource a b c) :=
  Equiv.sumCongr ex (Equiv.sumCongr ey ez)

noncomputable def ksPairBlockOrbit (a b c : ℕ) (f : PairSource a b c → ℕ) :
    MvPolynomial (PairSource a b c) ℂ :=
  rename Sum.inl (rzOrbitSum _ (∏ x, X x ^ f (Sum.inl x))) *
    rename (fun y => Sum.inr (Sum.inl y))
      (rzOrbitSum _ (∏ y, X y ^ f (Sum.inr (Sum.inl y)))) *
    rename (fun z => Sum.inr (Sum.inr z))
      (rzOrbitSum _ (∏ z, X z ^ f (Sum.inr (Sum.inr z))))

theorem ksPairBlockOrbit_symmetric (a b c : ℕ) (f : PairSource a b c → ℕ) :
    ksPairBlockOrbit a b c f ∈ pairSourceSymmetric a b c :=
  pairSource_separate_symmetric_mem a b c _ _ _
    (rzOrbitSum_symmetric _ _) (rzOrbitSum_symmetric _ _) (rzOrbitSum_symmetric _ _)

set_option maxHeartbeats 800000 in
-- Distributing three permutation sums elaborates large dependent variable types.
theorem ksPairBlockOrbit_sum (a b c : ℕ) (f : PairSource a b c → ℕ) :
    ksPairBlockOrbit a b c f =
      ∑ ez : Equiv.Perm (Fin c), ∑ ey : Equiv.Perm (Fin b),
        ∑ ex : Equiv.Perm (Fin b ⊕ Fin a),
          rename (ksPairBlockPerm a b c ex ey ez) (∏ i, X i ^ f i) := by
  classical
  simp only [ksPairBlockOrbit, rzOrbitSum, map_sum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr
  · ext ez; simp
  · intro ez hez
    apply Finset.sum_congr
    · ext ey; simp
    · intro ey hey
      apply Finset.sum_congr
      · ext ex; simp
      · intro ex hex
        simp only [map_mul, map_prod, map_pow, rename_X, Fintype.prod_sum_type,
          ksPairBlockPerm, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr]
        ring

theorem ksPairBlockOrbit_homogeneous (a b c : ℕ) (f : PairSource a b c → ℕ) :
    (ksPairBlockOrbit a b c f).IsHomogeneous (∑ i, f i) := by
  classical
  rw [ksPairBlockOrbit_sum]
  apply IsHomogeneous.sum
  intro ez hez
  apply IsHomogeneous.sum
  intro ey hey
  apply IsHomogeneous.sum
  intro ex hex
  apply IsHomogeneous.rename_isHomogeneous
  exact IsHomogeneous.prod _ _ _ fun i _ => isHomogeneous_X_pow i (f i)

theorem ksPairBlockPerm_shape (a b c : ℕ) (ex : Equiv.Perm (Fin b ⊕ Fin a))
    (ey : Equiv.Perm (Fin b)) (ez : Equiv.Perm (Fin c)) :
    pairSourceShape a b c ∘ ksPairBlockPerm a b c ex ey ez =
      pairSourceShape a b c := by
  funext i
  rcases i with x | (y | z) <;> rfl

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem ksPairBlockOrbit_evaluation (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c : ℕ) (f : PairSource a b c → ℕ) :
    xyzEvaluation ρ w (pairSourceShape a b c) (ksPairBlockOrbit a b c f) =
      ((Nat.card (Equiv.Perm (Fin c)) * Nat.card (Equiv.Perm (Fin b)) *
        Nat.card (Equiv.Perm (Fin b ⊕ Fin a)) : ℕ) : ℂ) •
      xyzEvaluation ρ w (pairSourceShape a b c) (∏ i, X i ^ f i) := by
  classical
  rw [ksPairBlockOrbit_sum]
  simp only [map_sum, xyzEvaluation_rename_equiv, ksPairBlockPerm_shape]
  simp [Nat.card_eq_fintype_card, mul_smul, Nat.cast_smul_eq_nsmul]

/-- Every labelled mode monomial has a homogeneous separately symmetric
    representative with exactly the same module evaluation. -/
theorem ksPair_monomial_symmetric_lift (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c : ℕ) (f : PairSource a b c → ℕ) :
    ∃ P : pairSourceSymmetric a b c,
      (P : MvPolynomial (PairSource a b c) ℂ).IsHomogeneous (∑ i, f i) ∧
      xyzEvaluation ρ w (pairSourceShape a b c) P =
        xyzEvaluation ρ w (pairSourceShape a b c) (∏ i, X i ^ f i) := by
  let t : ℂ := (Nat.card (Equiv.Perm (Fin c)) * Nat.card (Equiv.Perm (Fin b)) *
    Nat.card (Equiv.Perm (Fin b ⊕ Fin a)) : ℕ)
  have ht : t ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero
      (Nat.mul_ne_zero (Nat.ne_of_gt Nat.card_pos) (Nat.ne_of_gt Nat.card_pos))
      (Nat.ne_of_gt Nat.card_pos))
  refine ⟨⟨t⁻¹ • ksPairBlockOrbit a b c f,
    (pairSourceSymmetric a b c).toSubmodule.smul_mem _
      (ksPairBlockOrbit_symmetric a b c f)⟩, ?_, ?_⟩
  · exact (homogeneousSubmodule _ ℂ _).smul_mem _ (ksPairBlockOrbit_homogeneous a b c f)
  · change xyzEvaluation ρ w (pairSourceShape a b c) (t⁻¹ • _) = _
    rw [map_smul, ksPairBlockOrbit_evaluation]
    change t⁻¹ • t • _ = _
    rw [smul_smul, inv_mul_cancel₀ ht, one_smul]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksPairBlockOrbit_symmetric
#print axioms VOA.DeligneAudit.D4Levi.ksPairBlockOrbit_sum
#print axioms VOA.DeligneAudit.D4Levi.ksPairBlockOrbit_homogeneous
#print axioms VOA.DeligneAudit.D4Levi.ksPairBlockPerm_shape
#print axioms VOA.DeligneAudit.D4Levi.ksPairBlockOrbit_evaluation
#print axioms VOA.DeligneAudit.D4Levi.ksPair_monomial_symmetric_lift
