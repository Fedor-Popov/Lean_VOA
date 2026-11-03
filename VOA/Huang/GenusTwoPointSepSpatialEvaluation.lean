import VOA.Huang.GenusTwoPointSepCoefficientTransport

/-!
# Spatial evaluation with q left formal

The domain is the actual subalgebra of power series absolutely convergent at
the specified spatial parameter. Its q-power-series ring needs no convergence
in q. Thus multiplication can be evaluated degree by degree without using
the genus-one convergence theorem that the Ward calculation is to establish.
Localization at the spatial variable allows Laurent shifts. Nonintegral
prefactors remain external, with their logarithmic branches specified.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open scoped BigOperators

/-- Absolute convergence at one specified spatial point, including boundary points. -/
def SpatialSummable (t : ℂ) (F : PowerSeries ℂ) : Prop :=
  Summable (fun k : ℕ => ‖PowerSeries.coeff k F * t ^ k‖)

theorem spatialTerm_mul (t : ℂ) (F G : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n (F * G) * t ^ n =
      ∑ p ∈ Finset.antidiagonal n,
        (PowerSeries.coeff p.1 F * t ^ p.1) *
          (PowerSeries.coeff p.2 G * t ^ p.2) := by
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.mem_antidiagonal.mp hp, pow_add]
  ring

theorem SpatialSummable.mul {t : ℂ} {F G : PowerSeries ℂ}
    (hF : SpatialSummable t F) (hG : SpatialSummable t G) :
    SpatialSummable t (F * G) := by
  simpa only [SpatialSummable, spatialTerm_mul] using
    summable_norm_sum_mul_antidiagonal_of_summable_norm hF hG

theorem SpatialSummable.add {t : ℂ} {F G : PowerSeries ℂ}
    (hF : SpatialSummable t F) (hG : SpatialSummable t G) :
    SpatialSummable t (F + G) := by
  exact (Summable.add hF hG).of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => by
    simpa only [map_add, add_mul] using
      norm_add_le (PowerSeries.coeff n F * t ^ n) (PowerSeries.coeff n G * t ^ n))

theorem spatialSummable_C (t c : ℂ) : SpatialSummable t (PowerSeries.C c) := by
  classical
  unfold SpatialSummable
  simp only [PowerSeries.coeff_C]
  have h : (fun n : ℕ => ‖(if n = 0 then c else 0) * t ^ n‖) =
      fun n => if n = 0 then ‖c‖ else 0 := by
    funext n
    split_ifs with hn <;> simp [hn]
  rw [h]
  exact (hasSum_ite_eq 0 ‖c‖).summable

/-- The convergent subring, with convergence checked independently for each element. -/
def spatialConvergent (t : ℂ) : Subalgebra ℂ (PowerSeries ℂ) where
  carrier := {F | SpatialSummable t F}
  mul_mem' := SpatialSummable.mul
  add_mem' := SpatialSummable.add
  zero_mem' := by simpa using spatialSummable_C t 0
  one_mem' := by simpa using spatialSummable_C t 1
  algebraMap_mem' := spatialSummable_C t

/-- Evaluation is an algebra homomorphism on precisely this convergent subalgebra. -/
def spatialEval (t : ℂ) : spatialConvergent t →ₐ[ℂ] ℂ where
  toFun F := ∑' k : ℕ, PowerSeries.coeff k F.val * t ^ k
  map_one' := by simp
  map_zero' := by simp
  map_add' F G := by
    simpa only [Subalgebra.coe_add, map_add, add_mul] using
      F.property.of_norm.tsum_add G.property.of_norm
  map_mul' F G := by
    simp only [Subalgebra.coe_mul, spatialTerm_mul]
    exact (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      F.property G.property).symm
  commutes' c := by
    classical
    simp [Algebra.algebraMap_eq_smul_one]

theorem hasSum_spatialEval (t : ℂ) (F : spatialConvergent t) :
    HasSum (fun k : ℕ => PowerSeries.coeff k F.val * t ^ k) (spatialEval t F) :=
  F.property.of_norm.hasSum

/-- Spatial specialization of a formal q-series. No outer summability premise. -/
def spatialQEval (t : ℂ) :
    PowerSeries (spatialConvergent t) →+* PowerSeries ℂ :=
  PowerSeries.map (spatialEval t).toRingHom

@[simp] theorem coeff_spatialQEval (t : ℂ)
    (F : PowerSeries (spatialConvergent t)) (n : ℕ) :
    PowerSeries.coeff n (spatialQEval t F) =
      ∑' k : ℕ, PowerSeries.coeff k (PowerSeries.coeff n F).val * t ^ k := by
  simp [spatialQEval, spatialEval]

/-- A finite formal relation evaluates without an interchange of two infinite sums. -/
theorem spatialQEval_relation (t : ℂ) {ι : Type*} (s : Finset ι)
    (A F : ι → PowerSeries (spatialConvergent t))
    (h : ∑ i ∈ s, A i * F i = 0) :
    ∑ i ∈ s, spatialQEval t (A i) * spatialQEval t (F i) = 0 := by
  simpa using congrArg (spatialQEval t) h

/-- The spatial variable belongs to the convergent subalgebra at every point. -/
def spatialX (t : ℂ) : spatialConvergent t :=
  ⟨PowerSeries.X, by
    classical
    change SpatialSummable t PowerSeries.X
    unfold SpatialSummable
    simp only [PowerSeries.coeff_X]
    have h : (fun n : ℕ => ‖(if n = 1 then (1 : ℂ) else 0) * t ^ n‖) =
        fun n => if n = 1 then ‖t‖ else 0 := by
      funext n
      split_ifs with hn <;> simp [hn]
    rw [h]
    exact (hasSum_ite_eq 1 ‖t‖).summable⟩

@[simp] theorem spatialEval_X (t : ℂ) : spatialEval t (spatialX t) = t := by
  classical
  simp [spatialEval, spatialX, PowerSeries.coeff_X]

/-- Convergent Laurent expressions: a convergent power series divided by a
finite power of t. The pole order is allowed to vary with the q-degree. -/
abbrev SpatialLaurent (t : ℂ) := Localization.Away (spatialX t)

/-- The same evaluation homomorphism extends to Laurent expressions at t≠0. -/
def spatialLaurentEval {t : ℂ} (ht : t ≠ 0) : SpatialLaurent t →+* ℂ :=
  IsLocalization.Away.lift (spatialX t)
    (show IsUnit ((spatialEval t).toRingHom (spatialX t)) by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, spatialEval_X]
      exact isUnit_iff_ne_zero.mpr ht)

@[simp] theorem spatialLaurentEval_of {t : ℂ} (ht : t ≠ 0)
    (F : spatialConvergent t) :
    spatialLaurentEval ht (algebraMap (spatialConvergent t) (SpatialLaurent t) F) =
      spatialEval t F :=
  IsLocalization.Away.lift_eq (spatialX t) _ F

/-- Laurent spatial specialization with the q-variable entirely formal. -/
def spatialLaurentQEval {t : ℂ} (ht : t ≠ 0) :
    PowerSeries (SpatialLaurent t) →+* PowerSeries ℂ :=
  PowerSeries.map (spatialLaurentEval ht)

/-- Negative spatial shifts evaluate to genuine inverse powers. -/
theorem spatialLaurentEval_invX {t : ℂ} (ht : t ≠ 0) :
    spatialLaurentEval ht (IsLocalization.Away.invSelf (S := SpatialLaurent t) (spatialX t)) =
      t⁻¹ := by
  have h := congrArg (spatialLaurentEval ht)
    (IsLocalization.Away.mul_invSelf (S := SpatialLaurent t) (spatialX t))
  simp only [map_mul, spatialLaurentEval_of, spatialEval_X, map_one] at h
  calc
    _ = t⁻¹ * (t * spatialLaurentEval ht
        (IsLocalization.Away.invSelf (S := SpatialLaurent t) (spatialX t))) := by
      rw [← mul_assoc, inv_mul_cancel₀ ht, one_mul]
    _ = t⁻¹ := by rw [h, mul_one]

theorem spatialLaurentQEval_relation {t : ℂ} (ht : t ≠ 0)
    {ι : Type*} (s : Finset ι) (A F : ι → PowerSeries (SpatialLaurent t))
    (h : ∑ i ∈ s, A i * F i = 0) :
    ∑ i ∈ s, spatialLaurentQEval ht (A i) * spatialLaurentQEval ht (F i) = 0 := by
  simpa using congrArg (spatialLaurentQEval ht) h

end VOA.Huang.GenusTwoPoint.Separate
