import VOA.DeligneAudit.D4LevelReductionZeroModeConversion

/-! Symmetric mode generation for arbitrary three-colour radical counts. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi

/-- The positional shape with independent adjoint, middle, and central counts. -/
def threeColourModeShape (a j c : ℕ) : PairTarget a j c → Fin 6 :=
  Sum.elim (fun _ => 1) (Sum.elim (fun _ => 4) (fun _ => 5))

theorem threeColourModeShape_colours (a j c : ℕ) (i : PairTarget a j c) :
    threeColourModeShape a j c i = 1 ∨ threeColourModeShape a j c i = 4 ∨
      threeColourModeShape a j c i = 5 := by
  rcases i with x | (y | z) <;> simp [threeColourModeShape]

/-- The three separately symmetric alphabets act by the selective Cartan currents. -/
theorem threeColour_symmetric_le_powerSum (a j c : ℕ) :
    pairTargetSymmetric a j c ≤ xyzPowerSumAlgebra (threeColourModeShape a j c) := by
  classical
  apply Algebra.adjoin_le
  rintro P ⟨⟨i, r⟩, rfl⟩
  cases r with
  | zero =>
      fin_cases i <;>
        simp [pairTargetPower, pairTargetXPsum, targetYPsum, pairTargetZPsum]
  | succ r =>
      fin_cases i
      · convert (Algebra.subset_adjoin ⟨1, r + 1, by simp, by omega, rfl⟩ :
          colourPsum (threeColourModeShape a j c) 1 (r + 1) ∈
            xyzPowerSumAlgebra (threeColourModeShape a j c)) using 1
        simp [colourPsum, Finset.sum_map_toList, Fintype.sum_sum_type,
          threeColourModeShape, pairTargetPower, pairTargetXPsum]
      · convert (Algebra.subset_adjoin ⟨4, r + 1, by simp, by omega, rfl⟩ :
          colourPsum (threeColourModeShape a j c) 4 (r + 1) ∈
            xyzPowerSumAlgebra (threeColourModeShape a j c)) using 1
        simp [colourPsum, Finset.sum_map_toList, Fintype.sum_sum_type,
          threeColourModeShape, pairTargetPower, targetYPsum]
      · convert (Algebra.subset_adjoin ⟨5, r + 1, by simp, by omega, rfl⟩ :
          colourPsum (threeColourModeShape a j c) 5 (r + 1) ∈
            xyzPowerSumAlgebra (threeColourModeShape a j c)) using 1
        simp [colourPsum, Finset.sum_map_toList, Fintype.sum_sum_type,
          threeColourModeShape, pairTargetPower, pairTargetZPsum]

def threeColourBlockPermutation (a b c : ℕ) (ex : Equiv.Perm (Fin a))
    (ey : Equiv.Perm (Fin b)) (ez : Equiv.Perm (Fin c)) :
    Equiv.Perm (PairTarget a b c) :=
  Equiv.sumCongr ex (Equiv.sumCongr ey ez)

noncomputable def threeColourBlockOrbitSum (a b c : ℕ) (f : PairTarget a b c → ℕ) :
    MvPolynomial (PairTarget a b c) ℂ :=
  rename Sum.inl (rzOrbitSum _ (∏ x, X x ^ f (Sum.inl x))) *
    rename (fun y => Sum.inr (Sum.inl y))
      (rzOrbitSum _ (∏ y, X y ^ f (Sum.inr (Sum.inl y)))) *
    rename (fun z => Sum.inr (Sum.inr z))
      (rzOrbitSum _ (∏ z, X z ^ f (Sum.inr (Sum.inr z))))

theorem threeColourBlockOrbitSum_symmetric (a b c : ℕ) (f : PairTarget a b c → ℕ) :
    threeColourBlockOrbitSum a b c f ∈ pairTargetSymmetric a b c :=
  pairTarget_separate_symmetric_mem a b c _ _ _
    (rzOrbitSum_symmetric _ _) (rzOrbitSum_symmetric _ _) (rzOrbitSum_symmetric _ _)

set_option maxHeartbeats 800000 in
-- Distributing three permutation sums elaborates large dependent variable types.
theorem threeColourBlockOrbitSum_sum (a b c : ℕ) (f : PairTarget a b c → ℕ) :
    threeColourBlockOrbitSum a b c f =
      ∑ ez : Equiv.Perm (Fin c), ∑ ey : Equiv.Perm (Fin b),
        ∑ ex : Equiv.Perm (Fin a),
          rename (threeColourBlockPermutation a b c ex ey ez) (∏ i, X i ^ f i) := by
  classical
  simp only [threeColourBlockOrbitSum, rzOrbitSum, map_sum, Finset.sum_mul, Finset.mul_sum]
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
          threeColourBlockPermutation, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr]
        ring

theorem threeColourBlockOrbitSum_homogeneous (a b c : ℕ) (f : PairTarget a b c → ℕ) :
    (threeColourBlockOrbitSum a b c f).IsHomogeneous (∑ i, f i) := by
  classical
  rw [threeColourBlockOrbitSum_sum]
  apply IsHomogeneous.sum
  intro ez hez
  apply IsHomogeneous.sum
  intro ey hey
  apply IsHomogeneous.sum
  intro ex hex
  apply IsHomogeneous.rename_isHomogeneous
  exact IsHomogeneous.prod _ _ _ fun i _ => isHomogeneous_X_pow i (f i)

theorem threeColourBlockPermutation_shape (a b c : ℕ) (ex : Equiv.Perm (Fin a))
    (ey : Equiv.Perm (Fin b)) (ez : Equiv.Perm (Fin c)) :
    threeColourModeShape a b c ∘ threeColourBlockPermutation a b c ex ey ez =
      threeColourModeShape a b c := by
  funext i
  rcases i with x | (y | z) <;> rfl

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem threeColourBlockOrbitSum_evaluation (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c : ℕ) (f : PairTarget a b c → ℕ) :
    xyzEvaluation ρ w (threeColourModeShape a b c) (threeColourBlockOrbitSum a b c f) =
      ((Nat.card (Equiv.Perm (Fin c)) * Nat.card (Equiv.Perm (Fin b)) *
        Nat.card (Equiv.Perm (Fin a)) : ℕ) : ℂ) •
      xyzEvaluation ρ w (threeColourModeShape a b c) (∏ i, X i ^ f i) := by
  classical
  rw [threeColourBlockOrbitSum_sum]
  simp only [map_sum, xyzEvaluation_rename_equiv, threeColourBlockPermutation_shape]
  simp [Nat.card_eq_fintype_card, mul_smul, Nat.cast_smul_eq_nsmul]

/-- Every labelled mode monomial has a homogeneous separately symmetric
    representative with exactly the same module evaluation. -/
theorem threeColour_monomial_symmetric_lift (ρ : CurrentModule D4sector.f V) (w : V)
    (a b c : ℕ) (f : PairTarget a b c → ℕ) :
    ∃ P : pairTargetSymmetric a b c,
      (P : MvPolynomial (PairTarget a b c) ℂ).IsHomogeneous (∑ i, f i) ∧
      xyzEvaluation ρ w (threeColourModeShape a b c) P =
        xyzEvaluation ρ w (threeColourModeShape a b c) (∏ i, X i ^ f i) := by
  let t : ℂ := (Nat.card (Equiv.Perm (Fin c)) * Nat.card (Equiv.Perm (Fin b)) *
    Nat.card (Equiv.Perm (Fin a)) : ℕ)
  have ht : t ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero
      (Nat.mul_ne_zero (Nat.ne_of_gt Nat.card_pos) (Nat.ne_of_gt Nat.card_pos))
      (Nat.ne_of_gt Nat.card_pos))
  refine ⟨⟨t⁻¹ • threeColourBlockOrbitSum a b c f,
    (pairTargetSymmetric a b c).toSubmodule.smul_mem _
      (threeColourBlockOrbitSum_symmetric a b c f)⟩, ?_, ?_⟩
  · exact (homogeneousSubmodule _ ℂ _).smul_mem _ (threeColourBlockOrbitSum_homogeneous a b c f)
  · change xyzEvaluation ρ w (threeColourModeShape a b c) (t⁻¹ • _) = _
    rw [map_smul, threeColourBlockOrbitSum_evaluation]
    change t⁻¹ • t • _ = _
    rw [smul_smul, inv_mul_cancel₀ ht, one_smul]


variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- Selective Cartan combinations preserve every reductive Levi invariant subspace. -/
theorem leviInvariant_selectiveCartan (N : Submodule ℂ V)
    (hN : ∀ e r, IsLevi e → N ≤ N.comap (ρ.op e r)) (j : Fin 3) (r : ℕ)
    {v : V} (hv : v ∈ N) : selectiveCartan ρ j r v ∈ N := by
  have hb (u v' t : ℂ) : cartanBlend ρ u v' t r v ∈ N := by
    exact N.add_mem (N.add_mem
      (N.smul_mem u (hN _ r (leviColour_isLevi (A3Sector.simpleH 0)) hv))
      (N.smul_mem v' (hN _ r (leviColour_isLevi (A3Sector.simpleH 1)) hv)))
      (N.smul_mem t (hN 0 r ⟨0, rfl⟩ hv))
  fin_cases j <;> exact hb _ _ _

/-- Symmetric mode multiplication preserves every evaluated Levi invariant subspace. -/
theorem leviInvariant_modePolynomial {σ : Type*} [Fintype σ] (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (N : Submodule ℂ V)
    (hN : ∀ e r, IsLevi e → N ≤ N.comap (ρ.op e r))
    (shape : σ → Fin 6) (hshape : ∀ t, shape t = 1 ∨ shape t = 4 ∨ shape t = 5)
    (P : MvPolynomial σ ℂ) (hP : P ∈ xyzPowerSumAlgebra shape)
    (W : MvPolynomial σ ℂ) (hW : xyzEvaluation ρ w shape W ∈ N) :
    xyzEvaluation ρ w shape (P * W) ∈ N := by
  let T := N.comap (xyzEvaluation ρ w shape)
  have hsub : xyzPowerSumAlgebra shape ≤
      preservingShiftAlgebra (MvPolynomial σ ℂ) (symmetricShiftAction σ) T := by
    apply Algebra.adjoin_le
    rintro Q ⟨j, r, hj, hr, rfl⟩ U hU
    have hh := leviInvariant_selectiveCartan ρ N hN
      (if j = 1 then 0 else if j = 4 then 1 else 2) r hU
    rw [xyzEvaluation_psum_intertwine ρ w m h shape hshape j hj r hr U] at hh
    have hn : (if j = 5 then (1 : ℂ) else 2) ≠ 0 := by split_ifs <;> norm_num
    change xyzEvaluation ρ w shape
      (symmetricShiftAction σ (colourPsum shape j r) U) ∈ N
    exact (Submodule.smul_mem_iff N hn).mp hh
  exact hsub hP W hW

/-- Evaluation at zero modes gives the corresponding three-colour zero word. -/
theorem threeColour_evaluation_one (a j c : ℕ) :
    xyzEvaluation ρ w (threeColourModeShape a j c) 1 =
      threeColourZeroVector ρ w a j c := by
  classical
  have he : (1 : MvPolynomial (PairTarget a j c) ℂ) =
      modeMonomial (PairTarget a j c) 0 := by simp [modeMonomial]
  rw [he, xyzEvaluation, modeWordEvaluation_monomial]
  change radicalWord ρ w (shapedModes (threeColourModeShape a j c) Finset.univ.toList 0) = _
  apply radicalWord_perm
  apply List.perm_iff_count.mpr
  rintro ⟨k, s⟩
  simp only [List.count, List.countP_map, shapedModes, List.map_map,
    Function.comp_def, threeColourZeroWord, List.countP_append, List.countP_replicate,
    Finsupp.coe_zero, Pi.zero_apply, Prod.mk.injEq]
  rw [ksCountP_sum, Finset.sum_map_toList]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  fin_cases k <;> simp [threeColourModeShape] <;> split_ifs <;> simp_all

/-- Every mode assignment on three colours is generated by its zero-mode vector. -/
theorem threeColour_evaluation_mem (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (a j c : ℕ)
    (P : MvPolynomial (PairTarget a j c) ℂ) :
    xyzEvaluation ρ w (threeColourModeShape a j c) P ∈
      keyVectorOrbit ρ (bottomVector ρ w a (j + c)) := by
  let N := keyVectorOrbit ρ (bottomVector ρ w a (j + c))
  have hone : xyzEvaluation ρ w (threeColourModeShape a j c) 1 ∈ N := by
    rw [threeColour_evaluation_one]
    exact threeColourZero_mem_bottomOrbit ρ w m h a j c
  induction P using MvPolynomial.induction_on' with
  | monomial d z =>
      obtain ⟨Q, _, hQ⟩ := threeColour_monomial_symmetric_lift ρ w a j c d
      have hh := leviInvariant_modePolynomial ρ w m h N
        (fun e r he v hv => keyVectorOrbit_inv ρ _ e r he hv)
        (threeColourModeShape a j c) (threeColourModeShape_colours a j c) Q
        (threeColour_symmetric_le_powerSum a j c Q.property) 1 hone
      rw [mul_one, hQ] at hh
      rw [MvPolynomial.prod_X_pow] at hh
      have hd : (Finsupp.indicator Finset.univ fun i _ => d i) = d := by
        ext i
        simp
      rw [hd] at hh
      have hm : (monomial d z : MvPolynomial (PairTarget a j c) ℂ) = z • monomial d 1 := by
        simp [smul_monomial]
      rw [hm, map_smul]
      exact N.smul_mem z hh
  | add P Q hP hQ => rw [map_add]; exact N.add_mem hP hQ

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.threeColourModeShape_colours
#print axioms VOA.DeligneAudit.D4LevelReduction.threeColour_symmetric_le_powerSum
#print axioms VOA.DeligneAudit.D4LevelReduction.threeColourBlockOrbitSum_symmetric
#print axioms VOA.DeligneAudit.D4LevelReduction.threeColourBlockOrbitSum_sum
#print axioms VOA.DeligneAudit.D4LevelReduction.threeColourBlockOrbitSum_homogeneous
#print axioms VOA.DeligneAudit.D4LevelReduction.threeColourBlockPermutation_shape
#print axioms VOA.DeligneAudit.D4LevelReduction.threeColourBlockOrbitSum_evaluation
#print axioms VOA.DeligneAudit.D4LevelReduction.threeColour_monomial_symmetric_lift
#print axioms VOA.DeligneAudit.D4LevelReduction.leviInvariant_selectiveCartan
#print axioms VOA.DeligneAudit.D4LevelReduction.leviInvariant_modePolynomial
#print axioms VOA.DeligneAudit.D4LevelReduction.threeColour_evaluation_one
#print axioms VOA.DeligneAudit.D4LevelReduction.threeColour_evaluation_mem
