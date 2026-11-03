import VOA.Huang.GenusTwoPointCoordinates

/-!
# Sewing with a vacuum insertion

The uniform coefficient bounds are discharged in the unit-insertion sector,
with an arbitrary remaining intertwiner and irreducible insertion module.
The product has diagonal level support; the iterate has one intermediate level.
These are specializations, not convergence of two general insertions.
-/
namespace VOA.Huang.GenusTwoPoint
open VOA
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

noncomputable def vacuumLW (W : VertexOperatorAlgebra V) (hv : W.vacuum ≠ 0) : LWModule W :=
  ⟨V, adjointModule W, 0, (hasConformalWeight_adjoint W hv).2,
    (hasConformalWeight_adjoint W hv).1⟩

theorem moduleIntertwiner_vacuum_mode {M : Type u} [AddCommGroup M] [Module ℂ M]
    (A : OrdVModule W M) :
    (moduleIntertwiner A).val (-1) W.vacuum = LinearMap.id := by
  ext x
  change moduleModes A (-1) W.vacuum x = x
  rw [show (-1 : ℂ) = ((-1 : ℤ) : ℂ) by norm_num]
  rw [moduleModes_apply_intCast, ← WeakModule.act_def, WeakModule.act_vacuum, if_pos rfl]

variable {P N : LWModule W}

theorem productLevelCoeff_vacuum (hv : W.vacuum ≠ 0)
    (Y : IntertwiningOperator P.isMod N.isMod N.isMod)
    {α : ℂ} {w : P.carrier} (hw : w ∈ P.isMod.weight α) (n k : ℕ) :
    productLevelCoeff (P₁ := vacuumLW W hv) (moduleIntertwiner N.isMod) Y
      W.vacuum w 0 α n k =
      if k = n then GenusOne.trace Y w (N.h + n - W.centralCharge / 24) else 0 := by
  unfold productLevelCoeff productModeTrace
  by_cases hk : k = n
  · subst k
    rw [if_pos rfl,
      show (0 + α - 2) - (α + N.h + (n : ℂ) - 1 - N.h) + n = -1 by ring,
      show (α + N.h + (n : ℂ) - 1 - N.h) - n = α - 1 by ring]
    erw [moduleIntertwiner_vacuum_mode N.isMod]
    change _ = gradedTraceOp N.isMod (GenusOne.zeroMode P.isMod Y.val w) _
    rw [GenusOne.zeroMode_of_mem P.isMod Y.val hw]
    simp only [LinearMap.id_comp]
  · rw [if_neg hk]
    have hn : (0 + α - 2) - (α + N.h + (n : ℂ) - 1 - N.h) + k ≠ -1 := by
      intro he
      have : (k : ℂ) = (n : ℂ) := by linear_combination he
      exact hk (Nat.cast_injective this)
    erw [FusionUnit.vac_mode_eq_zero (moduleIntertwiner N.isMod).property hn,
      LinearMap.zero_comp]
    simp [gradedTraceOp, weightBlock]

/-- General one-point convergence supplies the joint growth bound in this sector. -/
theorem productModeGrowth_vacuum (hv : W.vacuum ≠ 0)
    (hC2 : C2Cofinite W) (iP : P.IsIrreducibleLW)
    (Y : IntertwiningOperator P.isMod N.isMod N.isMod)
    {α : ℂ} {w : P.carrier} (hw : w ∈ P.isMod.weight α) :
    ProductModeGrowth (P₁ := vacuumLW W hv) (moduleIntertwiner N.isMod) Y W.vacuum w 0 α := by
  intro a ha
  obtain ⟨C, hC⟩ := (GenusOne.traceSubexponential_of_irreducible hC2 iP Y
    ⟨N.realized, N.isLow⟩ w) a ha
  have hC0 : 0 ≤ C := by simpa using le_trans (norm_nonneg _) (hC 0)
  refine ⟨C, hC0, fun n k => ?_⟩
  rw [productLevelCoeff_vacuum hv Y hw]
  split_ifs with hk
  · rw [show N.h + (n : ℂ) - W.centralCharge / 24 = N.h - W.centralCharge / 24 + n by ring]
    exact le_trans (hC n) (le_mul_of_one_le_right
      (mul_nonneg hC0 (pow_nonneg (by linarith) _)) (one_le_pow₀ ha.le))
  · simpa only [norm_zero] using
      mul_nonneg (mul_nonneg hC0 (pow_nonneg (by linarith) _)) (pow_nonneg (by linarith) _)

/-- Both product obligations, without any unproved growth hypothesis, when the
first insertion is the vacuum and the other is arbitrary homogeneous. -/
theorem productSummable_vacuum (hv : W.vacuum ≠ 0)
    (hC2 : C2Cofinite W) (iP : P.IsIrreducibleLW)
    (Y : IntertwiningOperator P.isMod N.isMod N.isMod)
    {α : ℂ} {w : P.carrier} (hw : w ∈ P.isMod.weight α)
    {z₁ z₂ : ℂ} (hz₁ : ‖z₁‖ < 1) (hz : ‖z₂‖ < ‖z₁‖)
    (τ : UpperHalfPlane) (hq : ‖qParam τ‖ < ‖z₂‖) :
    ProductSewingSummable (P₁ := vacuumLW W hv)
        (moduleIntertwiner N.isMod) Y W.vacuum w 0 α z₁ z₂ τ ∧
      ProductQSummable (P₁ := vacuumLW W hv)
        (moduleIntertwiner N.isMod) Y W.vacuum w 0 α z₁ z₂ τ :=
  productSummable_in_sewingRegion_of_modeGrowth _ _ _ _ _ _
    (productModeGrowth_vacuum hv hC2 iP Y hw) hz₁ hz τ hq

theorem iterateLevelCoeff_vacuum (hv : W.vacuum ≠ 0)
    (Y : IntertwiningOperator P.isMod N.isMod N.isMod)
    {ℓ : ℕ} {w : P.carrier} (hw : w ∈ P.isMod.weight (P.h + ℓ)) (n k : ℕ) :
    iterateLevelCoeff (P₁ := vacuumLW W hv) Y (moduleIntertwiner P.isMod)
      W.vacuum w 0 (P.h + ℓ) n k =
      if k = ℓ then GenusOne.trace Y w (N.h + n - W.centralCharge / 24) else 0 := by
  unfold iterateLevelCoeff iterateModeTrace
  by_cases hk : k = ℓ
  · subst k
    rw [if_pos rfl,
      show (0 + (P.h + (ℓ : ℂ)) - 1 - P.h) - ℓ = -1 by ring,
      show (0 + (P.h + (ℓ : ℂ)) - 2) - (0 + (P.h + ℓ) - 1 - P.h) + ℓ =
        (P.h + ℓ) - 1 by ring]
    erw [moduleIntertwiner_vacuum_mode P.isMod]
    change _ = gradedTraceOp N.isMod (GenusOne.zeroMode P.isMod Y.val w) _
    rw [GenusOne.zeroMode_of_mem P.isMod Y.val hw]
    rfl
  · rw [if_neg hk]
    have hn : (0 + (P.h + (ℓ : ℂ)) - 1 - P.h) - k ≠ -1 := by
      intro he
      have : (k : ℂ) = (ℓ : ℂ) := by linear_combination -he
      exact hk (Nat.cast_injective this)
    erw [FusionUnit.vac_mode_eq_zero (moduleIntertwiner P.isMod).property hn,
      LinearMap.zero_apply, map_zero]
    simp [gradedTraceOp, weightBlock]

theorem iterateModeBound_vacuum (hv : W.vacuum ≠ 0)
    (hC2 : C2Cofinite W) (iP : P.IsIrreducibleLW)
    (Y : IntertwiningOperator P.isMod N.isMod N.isMod)
    {ℓ : ℕ} {w : P.carrier} (hw : w ∈ P.isMod.weight (P.h + ℓ))
    {a : ℝ} (ha : 1 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ TwoLevelBound
      (iterateLevelCoeff (P₁ := vacuumLW W hv) Y (moduleIntertwiner P.isMod)
        W.vacuum w 0 (P.h + ℓ)) C a 1 := by
  obtain ⟨C, hC⟩ := (GenusOne.traceSubexponential_of_irreducible hC2 iP Y
    ⟨N.realized, N.isLow⟩ w) a ha
  have hC0 : 0 ≤ C := by simpa using le_trans (norm_nonneg _) (hC 0)
  refine ⟨C, hC0, fun n k => ?_⟩
  rw [iterateLevelCoeff_vacuum hv Y hw]
  simp only [one_pow, mul_one]
  split_ifs
  · rw [show N.h + (n : ℂ) - W.centralCharge / 24 = N.h - W.centralCharge / 24 + n by ring]
    exact hC n
  · simpa only [norm_zero] using mul_nonneg hC0 (pow_nonneg (by linarith) _)

/-- The iterate obligation is discharged in the same unit sector. The explicit
region here is a sufficient one; finite intermediate support permits more. -/
theorem iterateSewingSummable_vacuum (hv : W.vacuum ≠ 0)
    (hC2 : C2Cofinite W) (iP : P.IsIrreducibleLW)
    (Y : IntertwiningOperator P.isMod N.isMod N.isMod)
    {ℓ : ℕ} {w : P.carrier} (hw : w ∈ P.isMod.weight (P.h + ℓ))
    {z₀ z₂ : ℂ} (hz₀ : z₀ ≠ 0) (hz₂ : z₂ ≠ 0) (hz : ‖z₀‖ < ‖z₂‖)
    (τ : UpperHalfPlane) :
    IterateSewingSummable (P₁ := vacuumLW W hv) Y (moduleIntertwiner P.isMod)
      W.vacuum w 0 (P.h + ℓ) z₀ z₂ τ := by
  obtain ⟨a, ha, hqa⟩ := exists_geometric_margin (norm_nonneg _) (norm_qParam_lt_one τ)
  obtain ⟨C, hC, hbound⟩ := iterateModeBound_vacuum hv hC2 iP Y hw ha
  apply iterateSewingSummable_of_modeBound _ _ _ _ _ _ hC (by linarith) zero_le_one
    hbound hz₀ hz₂ τ hqa
  simpa only [one_mul, norm_div, div_lt_one (norm_pos_iff.mpr hz₂)] using hz

end VOA.Huang.GenusTwoPoint
