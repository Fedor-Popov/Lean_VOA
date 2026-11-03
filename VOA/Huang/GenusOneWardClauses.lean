import VOA.Huang.GenusOneWardCollection

/-!
# The left and right clauses of `RawCuspCoordinateCollection`

Each square-coordinate insertion of the actual raw cusp trace is a mode factor
times the evaluation of `Phi`; collecting the factors gives `2πi · pref` times
the evaluation of the formal minus-two Ward expression, which vanishes.
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open VOA Module
open VOA.Huang.GenusTwoPoint.Separate
open VOA.Huang.GenusTwoPoint (moduleWeightExp moduleWeightExp_of_weight moduleWeightExp_add
  moduleWeightExp_zero logTwoPiI)
open VOA.Huang.GenusTwoPoint.QEquation (TailBound exists_tailBound ellipticCoeff Kernels)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

section Clauses
variable (hV : StronglyRational W)
  (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
  (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
  (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)

theorem weightExp_neg_cancel {M : Type u} [AddCommGroup M] [Module ℂ M] (A : OrdVModule W M)
    (t : ℂ) (v : M) : moduleWeightExp A t (moduleWeightExp A (-t) v) = v := by
  rw [← moduleWeightExp_add, add_neg_cancel, moduleWeightExp_zero]

theorem S_plain {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (rho : ℂ)
    (x : P₁.carrier) (y : P₂.carrier) :
    productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x y =
      wardPref N Q z₁ z₂ • evF (z₂ / z₁) (rho * (z₂ / z₁)⁻¹) (Phi Y₁ Y₂
        (moduleWeightExp P₁.isMod (-Complex.log z₁) x)
        (moduleWeightExp P₂.isMod (-Complex.log z₂) y)) := by
  rw [← productCuspSeries_weightExp, weightExp_neg_cancel, weightExp_neg_cancel]

theorem S_sq_left {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (rho : ℂ)
    (a : V) (x : P₁.carrier) (y : P₂.carrier) (m : ℤ) :
    productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho
        (spatialSquareMode P₁ (Complex.log z₁) a m x) y =
      (huangModeScale m * wardPref N Q z₁ z₂) • evF (z₂ / z₁) (rho * (z₂ / z₁)⁻¹) (Phi Y₁ Y₂
        (GenusOne.SquareModule.sqMode P₁.isMod m (huangStateU W a)
          (moduleWeightExp P₁.isMod (-Complex.log z₁) x))
        (moduleWeightExp P₂.isMod (-Complex.log z₂) y)) := by
  rw [spatialSquareMode, map_smul, LinearMap.smul_apply]
  conv_lhs => rw [← weightExp_neg_cancel P₂.isMod (Complex.log z₂) y]
  rw [productCuspSeries_weightExp, smul_smul]

theorem S_sq_right {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (rho : ℂ)
    (a : V) (x : P₁.carrier) (y : P₂.carrier) (m : ℤ) :
    productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x
        (spatialSquareMode P₂ (Complex.log z₂) a m y) =
      (huangModeScale m * wardPref N Q z₁ z₂) • evF (z₂ / z₁) (rho * (z₂ / z₁)⁻¹) (Phi Y₁ Y₂
        (moduleWeightExp P₁.isMod (-Complex.log z₁) x)
        (GenusOne.SquareModule.sqMode P₂.isMod m (huangStateU W a)
          (moduleWeightExp P₂.isMod (-Complex.log z₂) y))) := by
  rw [spatialSquareMode, map_smul]
  conv_lhs => rw [← weightExp_neg_cancel P₁.isMod (Complex.log z₁) x]
  rw [productCuspSeries_weightExp, smul_smul]

/-- A generic rearrangement: kernel times scaled evaluation. -/
theorem kernel_term_eq (G R Z : PowerSeries ℂ) (c h p E : ℂ) (hG : h • G = E • R) :
    (PowerSeries.C c * G) * ((h * p) • Z) = (E * p) • (c • (R * Z)) := by
  simp only [Algebra.smul_def, map_mul] at hG ⊢
  have hC : ∀ a : ℂ, algebraMap ℂ (PowerSeries ℂ) a = PowerSeries.C a := fun _ => rfl
  simp only [hC] at hG ⊢
  linear_combination (PowerSeries.C c * PowerSeries.C p * Z) * hG

/-- **First clause of `RawCuspCoordinateCollection`**: the collected
minus-two Ward identity in the first slot, on the actual raw cusp trace. -/
theorem leftClause {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) {rho : ℂ}
    (hr : ‖rho‖ ≤ ‖z₂ / z₁‖) :
    ∀ (a : V) (x : P₁.carrier) (y : P₂.carrier), ∃ K,
      TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule a
        ((huangU P₁ (Complex.log z₁)).symm x) ((huangU P₂ (Complex.log z₂)).symm y) K ∧
      productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho
          (spatialSquareMode P₁ (Complex.log z₁) a (-2) x) y +
        (∑ k ∈ Finset.range K, (((2 * k + 3 : ℕ) : SubexpPS) * (cuspWardKernels hz₂ hz hr).G k) •
          productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho
            (spatialSquareMode P₁ (Complex.log z₁) a (2 * (k + 1)) x) y) +
        (∑ m ∈ Finset.range K, ((-1 : SubexpPS) ^ m * (m + 1) * (cuspWardKernels hz₂ hz hr).Pleft m) •
          productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x
            (spatialSquareMode P₂ (Complex.log z₂) a m y)) = 0 := by
  intro a x y
  have hz₁ : z₁ ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hz)
  have ht0 : z₂ / z₁ ≠ 0 := div_ne_zero hz₂ hz₁
  have ht : ‖z₂ / z₁‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hz₁)]; exact hz
  set b := huangStateU W a with hb
  set x' := moduleWeightExp P₁.isMod (-Complex.log z₁) x with hx'
  set y' := moduleWeightExp P₂.isMod (-Complex.log z₂) y with hy'
  obtain ⟨K₀, hK₀⟩ := leftLHS_evZero Y₁ Y₂ b x' y'
  obtain ⟨K₁, hK₁⟩ := exists_tailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule a
    ((huangU P₁ (Complex.log z₁)).symm x) ((huangU P₂ (Complex.log z₂)).symm y)
  refine ⟨max K₀ K₁, fun j hj => hK₁ j (by omega), ?_⟩
  set K := max K₀ K₁ with hKdef
  have hΦ := conv_Phi Y₁ Y₂ hV i₁ i₂ iN hz₂ hz
  have hev := congrArg (evF (z₂ / z₁) (rho * (z₂ / z₁)⁻¹)) (hK₀ K (le_max_left _ _))
  rw [evF_leftLHS Y₁ Y₂ ht hΦ, evF_zero] at hev
  set E := 2 * (Real.pi : ℂ) * Complex.I with hE
  set p := wardPref N Q z₁ z₂ with hp
  have e0 : productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho
      (spatialSquareMode P₁ (Complex.log z₁) a (-2) x) y =
      (E * p) • evF (z₂ / z₁) (rho * (z₂ / z₁)⁻¹)
        (Phi Y₁ Y₂ (GenusOne.SquareModule.sqMode P₁.isMod (-2) b x') y') := by
    rw [S_sq_left, huangModeScale_neg_two]
  have e1 : ∀ k ∈ Finset.range K,
      (((2 * k + 3 : ℕ) : SubexpPS) * (cuspWardKernels hz₂ hz hr).G k) •
        productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho
          (spatialSquareMode P₁ (Complex.log z₁) a (2 * (k + 1)) x) y =
      (E * p) • (((2 * k + 3 : ℕ) : ℂ) • (evF (z₂ / z₁) (rho * (z₂ / z₁)⁻¹) (eis (k + 2)) *
        evF (z₂ / z₁) (rho * (z₂ / z₁)⁻¹) (Phi Y₁ Y₂
          (GenusOne.SquareModule.sqMode P₁.isMod ((2 * k + 2 : ℕ) : ℤ) b x') y'))) := by
    intro k _
    rw [Subalgebra.smul_def, smul_eq_mul,
      show (2 * ((k : ℤ) + 1)) = ((2 * k + 2 : ℕ) : ℤ) by push_cast; ring, S_sq_left]
    have hco : ((((2 * k + 3 : ℕ) : SubexpPS) * (cuspWardKernels hz₂ hz hr).G k : SubexpPS) :
        PowerSeries ℂ) = PowerSeries.C ((2 * k + 3 : ℕ) : ℂ) * eisensteinCuspSeries (k + 2) rho := by
      rw [Subalgebra.coe_mul, map_natCast]
      rfl
    rw [hco]
    exact kernel_term_eq _ _ _ _ _ _ _ (eisCusp_scale ht0 rho k)
  have e2 : ∀ m ∈ Finset.range K,
      ((-1 : SubexpPS) ^ m * (m + 1) * (cuspWardKernels hz₂ hz hr).Pleft m) •
        productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x
          (spatialSquareMode P₂ (Complex.log z₂) a m y) =
      (E * p) • (evF (z₂ / z₁) (rho * (z₂ / z₁)⁻¹) (((m + 1 : ℕ) : ℂ) • piK (m + 1) -
          if m = 0 then eis 1 else 0) *
        evF (z₂ / z₁) (rho * (z₂ / z₁)⁻¹)
          (Phi Y₁ Y₂ x' (GenusOne.SquareModule.sqMode P₂.isMod (m : ℤ) b y'))) := by
    intro m _
    rw [Subalgebra.smul_def, smul_eq_mul, S_sq_right]
    have hco : (((-1 : SubexpPS) ^ m * (m + 1) * (cuspWardKernels hz₂ hz hr).Pleft m : SubexpPS) :
        PowerSeries ℂ) = PowerSeries.C 1 *
          ((-1 : PowerSeries ℂ) ^ m * ((m : PowerSeries ℂ) + 1) *
            wpCuspSeries (m + 1) (z₂ / z₁) 0 rho) := by
      rw [map_one, one_mul]
      push_cast
      rfl
    rw [hco]
    rw [kernel_term_eq _ _ _ 1 _ _ _ (wpCusp_scale ht0 ht rho m), one_smul]
  rw [e0, Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.smul_sum, ← Finset.smul_sum,
    ← smul_add, ← smul_add, hev, smul_zero]

/-- The reverse-orientation Weierstrass kernel with its mode factor. -/
theorem wpCusp_scale_right {t₀ : ℂ} (ht0 : t₀ ≠ 0) (ht : ‖t₀‖ < 1) (rho : ℂ) (m : ℕ) :
    huangModeScale (m : ℤ) •
        ((-1 : PowerSeries ℂ) ^ m * ((m : PowerSeries ℂ) + 1) *
          ((-1 : PowerSeries ℂ) ^ (m + 2) * wpCuspSeries (m + 1) t₀ 0 rho)) =
      (2 * (Real.pi : ℂ) * Complex.I) • evF t₀ (rho * t₀⁻¹)
        (((m + 1 : ℕ) : ℂ) • (((-1 : ℂ) ^ (m + 1 + 1)) • piK (m + 1)) -
          if m = 0 then eis 1 else 0) := by
  have h := wpCusp_scale ht0 ht rho m
  have hneg : ((-1 : PowerSeries ℂ) ^ (m + 2)) = PowerSeries.C ((-1 : ℂ) ^ (m + 2)) := by simp
  have hre : (-1 : PowerSeries ℂ) ^ m * ((m : PowerSeries ℂ) + 1) *
      ((-1 : PowerSeries ℂ) ^ (m + 2) * wpCuspSeries (m + 1) t₀ 0 rho) =
      ((-1 : ℂ) ^ (m + 2)) • ((-1 : PowerSeries ℂ) ^ m * ((m : PowerSeries ℂ) + 1) *
        wpCuspSeries (m + 1) t₀ 0 rho) := by
    rw [hneg, PowerSeries.smul_eq_C_mul]; ring
  rw [hre, smul_comm, h, smul_comm]
  congr 1
  have hc : Conv t₀ (((m + 1 : ℕ) : ℂ) • piK (m + 1)) := (conv_piK ht _).smul _
  have hc' : Conv t₀ (((m + 1 : ℕ) : ℂ) • (((-1 : ℂ) ^ (m + 1 + 1)) • piK (m + 1))) :=
    ((conv_piK ht _).smul _).smul _
  rw [evF_sub hc (conv_kernel_ite t₀ m), evF_sub hc' (conv_kernel_ite t₀ m), evF_smul, evF_smul,
    evF_smul, smul_sub, smul_comm ((-1 : ℂ) ^ (m + 2))]
  by_cases h0 : m = 0
  · subst h0; simp
  · simp [h0, evF_zero]

/-- **Second clause of `RawCuspCoordinateCollection`**: the collected
minus-two Ward identity in the second slot, on the actual raw cusp trace. -/
theorem rightClause {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) {rho : ℂ}
    (hr : ‖rho‖ ≤ ‖z₂ / z₁‖) :
    ∀ (a : V) (x : P₁.carrier) (y : P₂.carrier), ∃ K,
      TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule a
        ((huangU P₁ (Complex.log z₁)).symm x) ((huangU P₂ (Complex.log z₂)).symm y) K ∧
      productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x
          (spatialSquareMode P₂ (Complex.log z₂) a (-2) y) +
        (∑ k ∈ Finset.range K, (((2 * k + 3 : ℕ) : SubexpPS) * (cuspWardKernels hz₂ hz hr).G k) •
          productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x
            (spatialSquareMode P₂ (Complex.log z₂) a (2 * (k + 1)) y)) +
        (∑ m ∈ Finset.range K, ((-1 : SubexpPS) ^ m * (m + 1) * (cuspWardKernels hz₂ hz hr).Pright m) •
          productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho
            (spatialSquareMode P₁ (Complex.log z₁) a m x) y) = 0 := by
  intro a x y
  have hz₁ : z₁ ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hz)
  have ht0 : z₂ / z₁ ≠ 0 := div_ne_zero hz₂ hz₁
  have ht : ‖z₂ / z₁‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hz₁)]; exact hz
  set b := huangStateU W a with hb
  set x' := moduleWeightExp P₁.isMod (-Complex.log z₁) x with hx'
  set y' := moduleWeightExp P₂.isMod (-Complex.log z₂) y with hy'
  obtain ⟨K₀, hK₀⟩ := rightLHS_evZero Y₁ Y₂ b x' y'
  obtain ⟨K₁, hK₁⟩ := exists_tailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule a
    ((huangU P₁ (Complex.log z₁)).symm x) ((huangU P₂ (Complex.log z₂)).symm y)
  refine ⟨max K₀ K₁, fun j hj => hK₁ j (by omega), ?_⟩
  set K := max K₀ K₁ with hKdef
  have hΦ := conv_Phi Y₁ Y₂ hV i₁ i₂ iN hz₂ hz
  have hev := congrArg (evF (z₂ / z₁) (rho * (z₂ / z₁)⁻¹)) (hK₀ K (le_max_left _ _))
  rw [evF_rightLHS Y₁ Y₂ ht hΦ, evF_zero] at hev
  set E := 2 * (Real.pi : ℂ) * Complex.I with hE
  set p := wardPref N Q z₁ z₂ with hp
  have e0 : productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x
      (spatialSquareMode P₂ (Complex.log z₂) a (-2) y) =
      (E * p) • evF (z₂ / z₁) (rho * (z₂ / z₁)⁻¹)
        (Phi Y₁ Y₂ x' (GenusOne.SquareModule.sqMode P₂.isMod (-2) b y')) := by
    rw [S_sq_right, huangModeScale_neg_two]
  have e1 : ∀ k ∈ Finset.range K,
      (((2 * k + 3 : ℕ) : SubexpPS) * (cuspWardKernels hz₂ hz hr).G k) •
        productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x
          (spatialSquareMode P₂ (Complex.log z₂) a (2 * (k + 1)) y) =
      (E * p) • (((2 * k + 3 : ℕ) : ℂ) • (evF (z₂ / z₁) (rho * (z₂ / z₁)⁻¹) (eis (k + 2)) *
        evF (z₂ / z₁) (rho * (z₂ / z₁)⁻¹) (Phi Y₁ Y₂ x'
          (GenusOne.SquareModule.sqMode P₂.isMod ((2 * k + 2 : ℕ) : ℤ) b y')))) := by
    intro k _
    rw [Subalgebra.smul_def, smul_eq_mul,
      show (2 * ((k : ℤ) + 1)) = ((2 * k + 2 : ℕ) : ℤ) by push_cast; ring, S_sq_right]
    have hco : ((((2 * k + 3 : ℕ) : SubexpPS) * (cuspWardKernels hz₂ hz hr).G k : SubexpPS) :
        PowerSeries ℂ) = PowerSeries.C ((2 * k + 3 : ℕ) : ℂ) * eisensteinCuspSeries (k + 2) rho := by
      rw [Subalgebra.coe_mul, map_natCast]
      rfl
    rw [hco]
    exact kernel_term_eq _ _ _ _ _ _ _ (eisCusp_scale ht0 rho k)
  have e2 : ∀ m ∈ Finset.range K,
      ((-1 : SubexpPS) ^ m * (m + 1) * (cuspWardKernels hz₂ hz hr).Pright m) •
        productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho
          (spatialSquareMode P₁ (Complex.log z₁) a m x) y =
      (E * p) • (evF (z₂ / z₁) (rho * (z₂ / z₁)⁻¹)
          (((m + 1 : ℕ) : ℂ) • (((-1 : ℂ) ^ (m + 1 + 1)) • piK (m + 1)) -
            if m = 0 then eis 1 else 0) *
        evF (z₂ / z₁) (rho * (z₂ / z₁)⁻¹)
          (Phi Y₁ Y₂ (GenusOne.SquareModule.sqMode P₁.isMod (m : ℤ) b x') y')) := by
    intro m _
    rw [Subalgebra.smul_def, smul_eq_mul, S_sq_left]
    have hco : (((-1 : SubexpPS) ^ m * (m + 1) * (cuspWardKernels hz₂ hz hr).Pright m :
        SubexpPS) : PowerSeries ℂ) = PowerSeries.C 1 *
          ((-1 : PowerSeries ℂ) ^ m * ((m : PowerSeries ℂ) + 1) *
            ((-1 : PowerSeries ℂ) ^ (m + 2) * wpCuspSeries (m + 1) (z₂ / z₁) 0 rho)) := by
      rw [map_one, one_mul]
      push_cast
      rfl
    rw [hco, kernel_term_eq _ _ _ 1 _ _ _ (wpCusp_scale_right ht0 ht rho m), one_smul]
  rw [e0, Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.smul_sum, ← Finset.smul_sum,
    ← smul_add, ← smul_add, hev, smul_zero]

end Clauses

end VOA.Huang.GenusOneWard
