import VOA.Huang.GenusOneG1bIterateSystem

/-!
# Uniform growth of the genus-one iterate channel

`iterateModeGrowth_holds`: for strongly rational `W`, irreducible `P₁, P₂, N, Q` and
homogeneous insertions, the iterate coefficients
`T(n,k) = Tr_{N_{h+n}} Y₃(Y₄(w₁)_{k} w₂)` (traced level `n`, intermediate level `k`) satisfy
`IterateModeGrowth`: for every `a > 1` there are `C, b` with `|T(n,k)| ≤ C aⁿ bᵏ`.
Consequently (`exists_iterateSewingRadius_holds`) the genus-one iterate double series
converges absolutely on a positive collision disc at every `τ` (`IterateSewingSummable`).

Route (the iterate-transport argument, steps 1–4, all machine-checked):
1. converse associativity: the iterate is `Σ_j` of product channels on the real segment
   (`coefficientAssociativityConverse_of_stronglyRational_pbw`);
2. ONE Euler system `Θ S = C S` for the vector of product channels with kernels in the
   subalgebra `RatSub` of `t`-rational kernels (`exists_homog_euler`, `exists_uniform_rat`);
3. evaluation at `t = 1/(1+s)` on `0 < s < 1`, recombination of the channels, and the
   identity theorem give a FORMAL Laurent Euler system for the iterate rows
   (`transport_system`);
4. the Laurent majorant (`euler_laurent_bound`) with kernel bounds `kerOf_normLe`.
-/
noncomputable section
namespace VOA.Huang.GenusOneG1b
open VOA VOA.Huang
open scoped BigOperators
open VOA.Huang.GenusOneWard (Phi c2 R2 RatSub RatRows pc omt thetaR2 mem_RatSub)
open VOA.Huang.GenusTwoPoint (IterateModeGrowth IterateSewingSummable iterateLevelCoeff
  iterateModeTrace TwoLevelBound CoefficientAssociativityConverse
  coefficientAssociativityConverse_of_stronglyRational_pbw)
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- The formal Laurent Euler system satisfied by the iterate rows of a finite homogeneous
family containing a prescribed pair. -/
theorem iterate_formal_system (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (iQ : Q.IsIrreducibleLW)
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (x : P₁.carrier) (y : P₂.carrier) (a₀ b₀ : ℕ)
    (hx : x ∈ P₁.isMod.weight (P₁.h + a₀)) (hy : y ∈ P₂.isMod.weight (P₂.h + b₀)) :
    ∃ (κ : Type u) (_ : Fintype κ) (xs : κ → P₁.carrier) (ys : κ → P₂.carrier)
      (a b : κ → ℕ) (f₀ : κ) (Cc : κ → κ → R2) (E c d : ℕ)
      (Pol : κ → κ → ℕ → Polynomial ℂ),
      (∀ f, xs f ∈ P₁.isMod.weight (P₁.h + a f)) ∧
      (∀ f, ys f ∈ P₂.isMod.weight (P₂.h + b f)) ∧
      xs f₀ = x ∧ ys f₀ = y ∧ a f₀ = a₀ ∧ b f₀ = b₀ ∧
      (∀ f g, Cc f g ∈ RatSub) ∧
      (∀ f g p, (Pol f g p).natDegree ≤ c * p + d) ∧
      (∀ f g p, omt ^ E * PowerSeries.coeff p (Cc f g) = pc (Pol f g p)) ∧
      ∀ f (n : ℕ), (N.h - W.centralCharge / 24 + n) •
        (PowerSeries.X ^ (E + dTot a b) *
          iterRow Y₃ Y₄ (xs f) (ys f) (P₁.h + a f) (P₂.h + b f) n) =
        ∑ g, ∑ p ∈ Finset.range (n + 1), PowerSeries.X ^ (shiftOf a b f g) *
          (kerOf Pol E c d a f g p *
            iterRow Y₃ Y₄ (xs g) (ys g) (P₁.h + a g) (P₂.h + b g) (n - p)) := by
  classical
  obtain ⟨r, R, iR, Y₁, Y₂, heq⟩ :=
    coefficientAssociativityConverse_of_stronglyRational_pbw hV P₁ P₂ N Q i₁ i₂ iN iQ Y₃ Y₄
  obtain ⟨κ, hκ, xs, ys, a, b, f₀, Cc, hxs, hys, hx0, hy0, ha0, hb0, hCr, heul⟩ :=
    exists_homog_euler (phiVec Y₁ Y₂) (wardBilinearV_phiVec Y₁ Y₂) hV i₁ i₂ x y a₀ b₀ hx hy
  obtain ⟨E, c, d, hrat⟩ := exists_uniform_rat hCr
  choose Pol hdeg hnum using fun (f g : κ) (p : ℕ) => hrat f g p
  refine ⟨κ, hκ, xs, ys, a, b, f₀, Cc, E, c, d, Pol, hxs, hys, hx0, hy0, ha0, hb0, hCr, hdeg,
    hnum, ?_⟩
  set lam := N.h - W.centralCharge / 24
  -- the row systems of the product channels
  have H1 : ∀ j f (n : ℕ), (lam + n) • (omt ^ E *
      PowerSeries.coeff n (Phi (Y₁ j) (Y₂ j) (xs f) (ys f))) =
      ∑ g, ∑ p ∈ Finset.range (n + 1), pc (Pol f g p) *
        PowerSeries.coeff (n - p) (Phi (Y₁ j) (Y₂ j) (xs g) (ys g)) := by
    intro j f n
    exact rows_euler (F := fun f => Phi (Y₁ j) (Y₂ j) (xs f) (ys f))
      (fun f => by simpa only [phiVec_apply] using heul f j) hnum f n
  have hph : ∀ j f n (s : ℝ), 0 < s → s < 1 →
      SumAt (PowerSeries.coeff n (Phi (Y₁ j) (Y₂ j) (xs f) (ys f))) (((1 + s : ℝ) : ℂ)⁻¹) := by
    intro j f n s hs0 _
    have h1 : (0 : ℝ) < 1 + s := by linarith
    refine phiRow_sumAt (Y₁ j) (Y₂ j) hV i₁ i₂ iN _ _ n ?_ ?_
    · exact inv_ne_zero (by exact_mod_cast h1.ne')
    · rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg h1.le]
      exact inv_lt_one_of_one_lt₀ (by linarith)
  have hΓ : ∀ f n, WB (3 / 4) (iterRow Y₃ Y₄ (xs f) (ys f) (P₁.h + a f) (P₂.h + b f) n) :=
    fun f n => iterRow_bound hV i₁ i₂ iN Y₃ Y₄ (hxs f) (hys f) n (by norm_num) (by norm_num)
  have hC : ∀ f (n : ℕ) (s : ℝ), 0 < s → s < 1 →
      (s : ℂ) ^ (Q.h - P₁.h - P₂.h - a f - b f) *
        evS (iterRow Y₃ Y₄ (xs f) (ys f) (P₁.h + a f) (P₂.h + b f) n) s =
      ∑ j, ((1 + s : ℝ) : ℂ) ^ (-P₁.h + N.h - (R j).h - a f + n) *
        evS (PowerSeries.coeff n (Phi (Y₁ j) (Y₂ j) (xs f) (ys f))) (((1 + s : ℝ) : ℂ)⁻¹) := by
    intro f n s hs0 hs1
    have hs : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    have hz : ((1 + s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1 + s : ℝ) ≠ 0)
    have h := heq (P₁.h + a f) (P₂.h + b f) (xs f) (ys f) (hxs f) (hys f) (N.h + n) (1 + s) 1
      (by linarith) (by linarith)
    have h01 : ((1 + s : ℝ) : ℂ) - ((1 : ℝ) : ℂ) = (s : ℂ) := by push_cast; ring
    rw [h01, Complex.ofReal_one, iterateCoeff_eq_evS Y₃ Y₄ _ _ _ _ n hs] at h
    simp only [productCoeff_eq_evS (Y₁ _) (Y₂ _) (hxs f) (hys f) n hz] at h
    rw [show Q.h - P₁.h - P₂.h - (a f : ℂ) - b f = Q.h - (P₁.h + a f) - (P₂.h + b f) by ring, h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show -P₁.h + N.h - (R j).h - (a f : ℂ) + n = -(P₁.h + a f) + N.h - (R j).h + n by ring]
  have hsys := transport_system hdeg (ph := fun j f n => PowerSeries.coeff n
      (Phi (Y₁ j) (Y₂ j) (xs f) (ys f))) H1 a b (fun j => -P₁.h + N.h - (R j).h)
    (Q.h - P₁.h - P₂.h)
    (fun f n => iterRow Y₃ Y₄ (xs f) (ys f) (P₁.h + a f) (P₂.h + b f) n) hph hΓ
    (fun f n s hs0 hs1 => by
      have := hC f n s hs0 hs1
      simp only [sub_sub] at this ⊢
      convert this using 3 <;> ring_nf)
  exact hsys

/-- Exponential room: some `μ > 1` with `μ^m < a`. -/
theorem exists_root_lt {a : ℝ} (ha : 1 < a) (m : ℕ) (hm : 0 < m) :
    ∃ μ : ℝ, 1 < μ ∧ μ ^ m < a := by
  have ha0 : 0 ≤ a := by linarith
  refine ⟨a ^ ((1 : ℝ) / (2 * m)), Real.one_lt_rpow ha (by positivity), ?_⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha0]
  have he : (1 : ℝ) / (2 * m) * m = 1 / 2 := by field_simp
  rw [he]
  calc a ^ ((1 : ℝ) / 2) < a ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt ha (by norm_num)
    _ = a := Real.rpow_one a

theorem iterateModeGrowth_of_zero_left (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod) (y : P₂.carrier) (α₁ α₂ : ℂ) :
    IterateModeGrowth Y₃ Y₄ 0 y α₁ α₂ := fun a _ =>
  ⟨0, 0, le_rfl, le_rfl, fun n k => by
    simp [iterateLevelCoeff, iterateModeTrace, VOA.gradedTraceOp, VOA.weightBlock]⟩

theorem iterateModeGrowth_of_zero_right (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod) (x : P₁.carrier) (α₁ α₂ : ℂ) :
    IterateModeGrowth Y₃ Y₄ x 0 α₁ α₂ := fun a _ =>
  ⟨0, 0, le_rfl, le_rfl, fun n k => by
    simp [iterateLevelCoeff, iterateModeTrace, VOA.gradedTraceOp, VOA.weightBlock]⟩

/-- **`IterateModeGrowth` holds**: uniform two-level growth of the genus-one iterate
coefficients, for strongly rational `W`, irreducible modules and homogeneous insertions. -/
theorem iterateModeGrowth_holds (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (iQ : Q.IsIrreducibleLW)
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) :
    IterateModeGrowth Y₃ Y₄ x y α₁ α₂ := by
  classical
  rcases FusionTop.eq_zero_or_level P₁ hx with rfl | ⟨a₀, rfl⟩
  · exact iterateModeGrowth_of_zero_left Y₃ Y₄ y _ α₂
  rcases FusionTop.eq_zero_or_level P₂ hy with rfl | ⟨b₀, rfl⟩
  · exact iterateModeGrowth_of_zero_right Y₃ Y₄ x _ _
  obtain ⟨κ, hκ, xs, ys, a, b, f₀, Cc, E, c, d, Pol, hxs, hys, hx0, hy0, ha0, hb0, hCr, hdeg,
    hnum, hsys⟩ := iterate_formal_system hV i₁ i₂ iN iQ Y₃ Y₄ x y a₀ b₀ hx hy
  intro A hA
  obtain ⟨μ, hμ, hμA⟩ := exists_root_lt hA (3 * c + 3) (by omega)
  have hμ0 : 0 < μ := by linarith
  -- uniform `Sub2` constant at rate `μ`
  choose D hD using fun fg : κ × κ => (mem_RatSub.mp (hCr fg.1 fg.2)).1 μ hμ
  set Dt := ∑ fg : κ × κ, max (D fg) 0 with hDt
  have hDt0 : 0 ≤ Dt := Finset.sum_nonneg fun _ _ => le_max_right _ _
  have hDle : ∀ f g p k, ‖c2 (Cc f g) p k‖ ≤ Dt * μ ^ (p + k) := by
    intro f g p k
    refine (hD (f, g) p k).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact (le_max_left _ _).trans (Finset.single_le_sum
      (f := fun fg : κ × κ => max (D fg) 0) (fun _ _ => le_max_right _ _)
      (Finset.mem_univ (f, g)))
  obtain ⟨A₁, hA₁⟩ := kerOf_normLe a hdeg hnum hμ hDt0 hDle
  set r := 1 - μ⁻¹ with hr
  have hr0 : 0 < r := by
    rw [hr]; have := inv_lt_one_of_one_lt₀ hμ; linarith
  have hr1 : r < 1 := by rw [hr]; linarith [inv_pos.mpr hμ0]
  have hrow : ∀ f n, ∃ B : ℝ, ∀ i, ‖PowerSeries.coeff i
      (iterRow Y₃ Y₄ (xs f) (ys f) (P₁.h + a f) (P₂.h + b f) n)‖ * r ^ i ≤ B :=
    fun f n => iterRow_bound hV i₁ i₂ iN Y₃ Y₄ (hxs f) (hys f) n hr0.le hr1
  obtain ⟨C, hC0, hbound⟩ := euler_laurent_bound
    (Γ := fun f n => iterRow Y₃ Y₄ (xs f) (ys f) (P₁.h + a f) (P₂.h + b f) n)
    hr0 hr1.le (by positivity) hμA hsys hA₁ hrow
  refine ⟨C, r⁻¹, hC0, inv_nonneg.mpr hr0.le, fun n k => ?_⟩
  have h := hbound f₀ n k
  simp only at h
  rw [hx0, hy0, ha0, hb0, coeff_iterRow] at h
  have hrk : 0 < r ^ k := pow_pos hr0 k
  rw [inv_pow, mul_assoc, ← div_eq_mul_inv, ← mul_div_assoc, le_div_iff₀ hrk]
  exact h

/-- **Genus-one iterate sewing**: at every `τ` there is a positive collision radius on
which the iterate double series converges absolutely. -/
theorem exists_iterateSewingRadius_holds (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (iQ : Q.IsIrreducibleLW)
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (z₀ z₂ : ℂ), z₀ ≠ 0 → z₂ ≠ 0 →
      ‖z₀ / z₂‖ < δ → IterateSewingSummable Y₃ Y₄ x y α₁ α₂ z₀ z₂ τ :=
  GenusTwoPoint.exists_iterateSewingRadius_of_modeGrowth Y₃ Y₄ x y α₁ α₂
    (iterateModeGrowth_holds hV i₁ i₂ iN iQ Y₃ Y₄ hx hy) τ

end VOA.Huang.GenusOneG1b
