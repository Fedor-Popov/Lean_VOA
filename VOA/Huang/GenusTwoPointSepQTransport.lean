import VOA.Huang.GenusTwoPointModifiedTrace
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Formal q-transport of an inserted vertex mode

Cyclicity is applied on the finite-dimensional weight spaces, including the
bottom boundary. This gives the actual formal factors `1 / (1 - q^d)` in both
orientations of the two-intertwiner Ward identity. No convergence of the
product trace, geometric coordinate conjugation, or elliptic collection is
assumed or concluded.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA Module
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- The normalized q-series of actual finite-dimensional weight-space traces. -/
def operatorTraceSeries (N : LWModule W) (T : Module.End ℂ N.carrier) : PowerSeries ℂ :=
  PowerSeries.mk fun n => gradedTraceOp N.isMod T (N.h - W.centralCharge / 24 + n)

@[simp] theorem coeff_operatorTraceSeries (N : LWModule W)
    (T : Module.End ℂ N.carrier) (n : ℕ) :
    PowerSeries.coeff n (operatorTraceSeries N T) =
      gradedTraceOp N.isMod T (N.h - W.centralCharge / 24 + n) := by
  simp [operatorTraceSeries]

theorem operatorTraceSeries_sub (N : LWModule W) (S T : Module.End ℂ N.carrier) :
    operatorTraceSeries N (S - T) = operatorTraceSeries N S - operatorTraceSeries N T := by
  ext n
  simp [gradedTraceOp_sub]

/-- Transport around the q-trace. The factor q^d includes the vanishing of
the first d coefficients, which cannot be obtained by cyclicity at one weight. -/
theorem operatorTraceSeries_cyclic (N : LWModule W) (A B : Module.End ℂ N.carrier)
    (d : ℕ) (hA : WeightShift N.isMod A (-(d : ℂ)))
    (hB : WeightShift N.isMod B (d : ℂ)) :
    operatorTraceSeries N (B * A) =
      PowerSeries.X ^ d * operatorTraceSeries N (A * B) := by
  ext n
  rw [coeff_operatorTraceSeries, PowerSeries.coeff_X_pow_mul']
  split_ifs with hd
  · rw [coeff_operatorTraceSeries]
    have hc := gradedTraceOp_comm_shift N.isMod A B (d : ℂ) hA hB
      (N.h - W.centralCharge / 24 + (n - d : ℕ))
    rw [Nat.cast_sub hd] at hc ⊢
    convert hc.symm using 1
    congr 1
    ring
  · apply gradedTraceOp_mul_eq_zero_of_kills
    intro x hx
    have hx' : x ∈ N.isMod.weight (N.h + n) := by
      convert hx using 1
      congr 1
      ring
    have hl := hA _ x hx'
    have he : N.h + (n : ℂ) + -(d : ℂ) = N.h + ((n : ℤ) - d : ℤ) := by
      push_cast
      ring
    rw [he, LWBottomRecovery.weight_neg_eq_bot N (by omega), Submodule.mem_bot] at hl
    exact hl

/-- The geometric denominator as a formal power series. Positive d is
essential: the zero-shift case is a Ward vanishing identity instead. -/
def geometricDenominator (d : ℕ) : PowerSeries ℂ := (1 - PowerSeries.X ^ d)⁻¹

theorem geometricDenominator_mul {d : ℕ} (hd : 0 < d) :
    geometricDenominator d * (1 - PowerSeries.X ^ d) = 1 := by
  apply PowerSeries.inv_mul_cancel
  simp [hd.ne']

/-- The denominator is the geometric series: a coefficient is one exactly
at multiples of d. Thus the inversion really supplies the Lambert factors. -/
theorem coeff_geometricDenominator {d : ℕ} (hd : 0 < d) (n : ℕ) :
    PowerSeries.coeff n (geometricDenominator d) = if d ∣ n then 1 else 0 := by
  let G : PowerSeries ℂ := PowerSeries.mk fun n => if d ∣ n then 1 else 0
  have hG : (1 - PowerSeries.X ^ d) * G = 1 := by
    ext m
    rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul']
    simp only [G, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    by_cases hdm : d ≤ m
    · have hm0 : m ≠ 0 := by omega
      have he : d ∣ m - d ↔ d ∣ m := Nat.dvd_sub_iff_left hdm (dvd_refl d)
      simp [hdm, he, hm0]
    · have he : d ∣ m ↔ m = 0 := by
        constructor
        · intro h
          exact Nat.eq_zero_of_dvd_of_lt h (by omega)
        · rintro rfl
          exact dvd_zero d
      simp [hdm, he]
  have he : geometricDenominator d = G := by
    calc
      geometricDenominator d = geometricDenominator d * ((1 - PowerSeries.X ^ d) * G) := by
        rw [hG, mul_one]
      _ = G := by rw [← mul_assoc, geometricDenominator_mul hd, one_mul]
  simp [he, G]

/-- The same formal denominator evaluates to the convergent geometric kernel
on the unit disc. This asserts convergence of the kernel, not of a trace. -/
theorem hasSum_geometricDenominator {d : ℕ} (hd : 0 < d) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n (geometricDenominator d) * q ^ n)
      (1 - q ^ d)⁻¹ := by
  let f : ℕ → ℂ := fun n => PowerSeries.coeff n (geometricDenominator d) * q ^ n
  have hi : Function.Injective (fun j : ℕ => d * j) := by
    intro j k h
    exact Nat.eq_of_mul_eq_mul_left hd h
  have hz : ∀ n, n ∉ Set.range (fun j : ℕ => d * j) → f n = 0 := by
    intro n hn
    have hnd : ¬d ∣ n := by
      rintro ⟨j, hj⟩
      exact hn ⟨j, hj.symm⟩
    simp [f, coeff_geometricDenominator hd, hnd]
  apply (hi.hasSum_iff hz).mp
  have hqd : ‖q ^ d‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq hd.ne'
  simpa [f, Function.comp_def, coeff_geometricDenominator hd, pow_mul] using
    (hasSum_geometric_of_norm_lt_one hqd)

section WeightConjugation
variable {E M K : Type u} [AddCommGroup E] [Module ℂ E]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup K] [Module ℂ K]
  {A : OrdVModule W E} {N : OrdVModule W M} {Q : OrdVModule W K}

/-- The coefficient form of q^{L(0)} conjugation for an intertwiner. The
logarithm t is specified; the insertion need not be homogeneous. -/
theorem intertwiner_weightExp_conjugation (Y : IntertwiningOperator A Q N)
    (t n : ℂ) (w : E) (x : K) :
    moduleWeightExp N t (Y.val n w (moduleWeightExp Q (-t) x)) =
      Complex.exp (-t * (n + 1)) • Y.val n (moduleWeightExp A t w) x := by
  refine FusionTop.induction_weight A w (by simp) ?_ ?_
  · intro w v hw hv
    simp only [map_add, LinearMap.add_apply, hw, hv, smul_add]
  · intro α w hw
    refine FusionTop.induction_weight Q x (by simp) ?_ ?_
    · intro x y hx hy
      simp only [map_add, hx, hy, smul_add]
    · intro β x hx
      rw [moduleWeightExp_of_weight Q _ hx, map_smul, map_smul,
        moduleWeightExp_of_weight N _ (FusionTop.mem_weight Y.property hw hx n),
        moduleWeightExp_of_weight A _ hw, map_smul, LinearMap.smul_apply,
        smul_smul, smul_smul, ← Complex.exp_add, ← Complex.exp_add]
      congr 2
      ring

/-- The vertex-mode specialization used to move the inserted mode through
q^{L(0)}. The eigenvalue is the full weight shift k-i-1. -/
theorem vertexMode_weightExp_conjugation (N : OrdVModule W M)
    {a : V} {k : ℤ} (ha : a ∈ W.grading k) (i : ℤ) (t : ℂ) (x : M) :
    moduleWeightExp N t (mode (N.YM a) i (moduleWeightExp N (-t) x)) =
      Complex.exp (t * ((k : ℂ) - i - 1)) • mode (N.YM a) i x := by
  refine FusionTop.induction_weight N x (by simp) ?_ ?_
  · intro x y hx hy
    simp only [map_add, hx, hy, smul_add]
  · intro β x hx
    rw [moduleWeightExp_of_weight N _ hx, map_smul, map_smul,
      moduleWeightExp_of_weight N _ (mode_mem_weight N ha hx i),
      smul_smul, ← Complex.exp_add]
    congr 2
    ring

end WeightConjugation

/-- Formal geometric inversion of the commutator, with both orientations. -/
theorem operatorTraceSeries_geometric (N : LWModule W) (A B : Module.End ℂ N.carrier)
    {d : ℕ} (hd : 0 < d) (hA : WeightShift N.isMod A (-(d : ℂ)))
    (hB : WeightShift N.isMod B (d : ℂ)) :
    operatorTraceSeries N (A * B) =
        geometricDenominator d * operatorTraceSeries N (A * B - B * A) ∧
    operatorTraceSeries N (B * A) =
        PowerSeries.X ^ d * geometricDenominator d *
          operatorTraceSeries N (A * B - B * A) := by
  have hc := operatorTraceSeries_cyclic N A B d hA hB
  have he : operatorTraceSeries N (A * B - B * A) =
      (1 - PowerSeries.X ^ d) * operatorTraceSeries N (A * B) := by
    rw [operatorTraceSeries_sub, hc]
    ring
  have hi : geometricDenominator d * operatorTraceSeries N (A * B - B * A) =
      operatorTraceSeries N (A * B) := by
    rw [he, ← mul_assoc, geometricDenominator_mul hd, one_mul]
  exact ⟨hi.symm, by rw [mul_assoc, hi, hc]⟩

section Intertwiners
variable {P₁ P₂ N Q : LWModule W}

/-- The actual uncollected two-insertion commutator, normalized in q. -/
def wardTraceSeries (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (a : V) (w₁ : P₁.carrier) (w₂ : P₂.carrier)
    (i : ℤ) (n₁ n₂ : ℂ) (J : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => wardTrace Y₁ Y₂ a w₁ w₂ i n₁ n₂ J
    (N.h - W.centralCharge / 24 + n)

theorem wardTraceSeries_eq (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (a : V) (w₁ : P₁.carrier) (w₂ : P₂.carrier)
    (i : ℤ) (n₁ n₂ : ℂ) (J : ℕ)
    (hJ : QEquation.TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule a w₁ w₂ J) :
    wardTraceSeries Y₁ Y₂ a w₁ w₂ i n₁ n₂ J = operatorTraceSeries N
      (mode (N.isMod.YM a) i * ((Y₁.val n₁ w₁).comp (Y₂.val n₂ w₂)) -
        ((Y₁.val n₁ w₁).comp (Y₂.val n₂ w₂)) * mode (N.isMod.YM a) i) := by
  ext n
  simpa [wardTraceSeries] using
    (trace_product_commutator Y₁ Y₂ a w₁ w₂ i n₁ n₂ J hJ
      (N.h - W.centralCharge / 24 + n)).symm

/-- Raising the traced weight gives the negative q^d/(1-q^d) factor.
This is an identity of actual raw two-intertwiner trace series. -/
theorem trace_product_q_transport_pos
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {k i : ℤ} {α₁ α₂ : ℂ} {a : V} {w₁ : P₁.carrier} {w₂ : P₂.carrier}
    (ha : a ∈ W.grading k) (h₁ : w₁ ∈ P₁.isMod.weight α₁)
    (h₂ : w₂ ∈ P₂.isMod.weight α₂) {d : ℕ} (hd : 0 < d)
    (hdi : k - i - 1 = (d : ℤ)) (n₁ n₂ : ℂ)
    (hn : n₁ + n₂ = α₁ + α₂ + k - i - 3) (J : ℕ)
    (hJ : QEquation.TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule a w₁ w₂ J) :
    operatorTraceSeries N
      (mode (N.isMod.YM a) i * ((Y₁.val n₁ w₁).comp (Y₂.val n₂ w₂))) =
      -(PowerSeries.X ^ d * geometricDenominator d *
        wardTraceSeries Y₁ Y₂ a w₁ w₂ i n₁ n₂ J) := by
  have hdC : (k : ℂ) - i - 1 = d := by exact_mod_cast hdi
  have hA := weightShift_product Y₁ Y₂ h₁ h₂ n₁ n₂
  rw [show α₁ + α₂ - n₁ - n₂ - 2 = -(d : ℂ) by linear_combination -hn - hdC] at hA
  have hB := VOA.weightShift_mode N.isMod ha i
  rw [hdC] at hB
  have he := (operatorTraceSeries_geometric N _ _ hd hA hB).2
  rw [wardTraceSeries_eq Y₁ Y₂ a w₁ w₂ i n₁ n₂ J hJ]
  rw [operatorTraceSeries_sub] at he ⊢
  linear_combination he

/-- Lowering the traced weight gives the positive 1/(1-q^d) factor. -/
theorem trace_product_q_transport_neg
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {k i : ℤ} {α₁ α₂ : ℂ} {a : V} {w₁ : P₁.carrier} {w₂ : P₂.carrier}
    (ha : a ∈ W.grading k) (h₁ : w₁ ∈ P₁.isMod.weight α₁)
    (h₂ : w₂ ∈ P₂.isMod.weight α₂) {d : ℕ} (hd : 0 < d)
    (hdi : i - k + 1 = (d : ℤ)) (n₁ n₂ : ℂ)
    (hn : n₁ + n₂ = α₁ + α₂ + k - i - 3) (J : ℕ)
    (hJ : QEquation.TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule a w₁ w₂ J) :
    operatorTraceSeries N
      (mode (N.isMod.YM a) i * ((Y₁.val n₁ w₁).comp (Y₂.val n₂ w₂))) =
      geometricDenominator d * wardTraceSeries Y₁ Y₂ a w₁ w₂ i n₁ n₂ J := by
  have hdC : (i : ℂ) - k + 1 = d := by exact_mod_cast hdi
  have hB := weightShift_product Y₁ Y₂ h₁ h₂ n₁ n₂
  rw [show α₁ + α₂ - n₁ - n₂ - 2 = (d : ℂ) by linear_combination -hn + hdC] at hB
  have hA := VOA.weightShift_mode N.isMod ha i
  rw [show (k : ℂ) - i - 1 = -(d : ℂ) by linear_combination -hdC] at hA
  rw [wardTraceSeries_eq Y₁ Y₂ a w₁ w₂ i n₁ n₂ J hJ]
  exact (operatorTraceSeries_geometric N _ _ hd hA hB).1

end Intertwiners
end VOA.Huang.GenusTwoPoint.Separate
