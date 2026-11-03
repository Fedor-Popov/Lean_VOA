import VOA.Huang.GenusTwoPointSepModifiedDerivative

/-!
# Spatial insertion and the mode-shift boundary term

These are identities for the actual geometrically modified two-mode trace.
The telescoping result states its summability hypotheses explicitly. It does
not identify a summed trace with a convergent genus-one correlation function.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA GenusOne
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

theorem productTracePair_Lm1_left
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (n₁ n₂ e : ℂ) :
    productTracePair Y₁ Y₂ n₁ n₂ e (P₁.isMod.Lm1 w₁) w₂ =
      -n₁ * productTracePair Y₁ Y₂ (n₁ - 1) n₂ e w₁ w₂ := by
  change gradedTraceOp N.isMod ((Y₁.val n₁ (P₁.isMod.Lm1 w₁)).comp
    (Y₂.val n₂ w₂)) e = _
  rw [Y₁.property.L_neg_one, LinearMap.smul_comp, gradedTraceOp_smul]
  rfl

theorem productTracePair_Lm1_right
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (n₁ n₂ e : ℂ) :
    productTracePair Y₁ Y₂ n₁ n₂ e w₁ (P₂.isMod.Lm1 w₂) =
      -n₂ * productTracePair Y₁ Y₂ n₁ (n₂ - 1) e w₁ w₂ := by
  change gradedTraceOp N.isMod ((Y₁.val n₁ w₁).comp
    (Y₂.val n₂ (P₂.isMod.Lm1 w₂))) e = _
  rw [Y₂.property.L_neg_one, LinearMap.comp_smul, gradedTraceOp_smul]
  rfl

/-- Exact first-coordinate insertion law. The last two terms telescope
only after summing the whole mode coset. -/
theorem huangModifiedModeTrace_Lm1_left
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (n₁ n₂ t₁ t₂ e : ℂ) :
    huangModifiedModeTrace Y₁ Y₂ (P₁.isMod.Lm1 w₁) w₂ n₁ n₂ t₁ t₂ e =
      Complex.exp logTwoPiI *
        (_root_.deriv (fun s => huangModifiedModeTrace Y₁ Y₂ w₁ w₂ n₁ n₂ s t₂ e) t₁ +
          (n₁ + 1) * huangModifiedModeTrace Y₁ Y₂ w₁ w₂ n₁ n₂ t₁ t₂ e -
          n₁ * huangModifiedModeTrace Y₁ Y₂ w₁ w₂ (n₁ - 1) n₂ t₁ t₂ e) := by
  rw [(hasDerivAt_huangModifiedModeTrace_left Y₁ Y₂ w₁ w₂ n₁ n₂ t₁ t₂ e).deriv]
  simp only [huangModifiedModeTrace, modifiedProductModeTrace]
  change Complex.exp _ * productTracePair Y₁ Y₂ n₁ n₂ e
    (huangU P₁ t₁ (P₁.isMod.Lm1 w₁)) (huangU P₂ t₂ w₂) = _
  rw [huangU_Lm1]
  simp only [map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply,
    smul_eq_mul, productTracePair_Lm1_left]
  dsimp only [huangU]
  have hex : Complex.exp (-t₁ * (n₁ + 1) - t₂ * (n₂ + 1)) * Complex.exp t₁ =
      Complex.exp (-t₁ * (n₁ - 1 + 1) - t₂ * (n₂ + 1)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  linear_combination Complex.exp logTwoPiI * (-n₁) *
    productTracePair Y₁ Y₂ (n₁ - 1) n₂ e
      (coordinateModification P₁ huangA t₁ w₁) (coordinateModification P₂ huangA t₂ w₂) * hex

/-- The opposite spatial insertion law, with no cyclic permutation of the
two intertwiners assumed. -/
theorem huangModifiedModeTrace_Lm1_right
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (n₁ n₂ t₁ t₂ e : ℂ) :
    huangModifiedModeTrace Y₁ Y₂ w₁ (P₂.isMod.Lm1 w₂) n₁ n₂ t₁ t₂ e =
      Complex.exp logTwoPiI *
        (_root_.deriv (fun s => huangModifiedModeTrace Y₁ Y₂ w₁ w₂ n₁ n₂ t₁ s e) t₂ +
          (n₂ + 1) * huangModifiedModeTrace Y₁ Y₂ w₁ w₂ n₁ n₂ t₁ t₂ e -
          n₂ * huangModifiedModeTrace Y₁ Y₂ w₁ w₂ n₁ (n₂ - 1) t₁ t₂ e) := by
  rw [(hasDerivAt_huangModifiedModeTrace_right Y₁ Y₂ w₁ w₂ n₁ n₂ t₁ t₂ e).deriv]
  simp only [huangModifiedModeTrace, modifiedProductModeTrace]
  change Complex.exp _ * productTracePair Y₁ Y₂ n₁ n₂ e
    (huangU P₁ t₁ w₁) (huangU P₂ t₂ (P₂.isMod.Lm1 w₂)) = _
  rw [huangU_Lm1]
  simp only [map_smul, map_add, smul_eq_mul, productTracePair_Lm1_right]
  dsimp only [huangU]
  have hex : Complex.exp (-t₁ * (n₁ + 1) - t₂ * (n₂ + 1)) * Complex.exp t₂ =
      Complex.exp (-t₁ * (n₁ + 1) - t₂ * (n₂ - 1 + 1)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  linear_combination Complex.exp logTwoPiI * (-n₂) *
    productTracePair Y₁ Y₂ n₁ (n₂ - 1) e
      (coordinateModification P₁ huangA t₁ w₁) (coordinateModification P₂ huangA t₂ w₂) * hex

/-- Absolute/summable mode control justifies the telescoping step; a total
tsum alone is not used to distribute an infinite difference. -/
theorem tsum_mode_difference (b : ℂ) (f : ℤ → ℂ)
    (hf : Summable (fun j : ℤ => (b + j + 1) * f j)) :
    (∑' j : ℤ, ((b + j + 1) * f j - (b + j) * f (j - 1))) = 0 := by
  let g : ℤ → ℂ := fun j => (b + j + 1) * f j
  have he (j : ℤ) : (b + j) * f (j - 1) = g (j - 1) := by
    dsimp [g]
    push_cast
    congr 1
    ring
  have hs : Summable (fun j : ℤ => g (j - 1)) :=
    ((Equiv.subRight (1 : ℤ)).summable_iff).mpr hf
  simp only [he]
  rw [hf.tsum_sub hs]
  have ht := (Equiv.subRight (1 : ℤ)).tsum_eq g
  exact sub_eq_zero.mpr ht.symm

/-- A summable derivative family and weighted mode family suffice to sum
the exact spatial law. This lemma also proves summability of the insertion. -/
theorem sum_spatial_law (b c : ℂ) (f d l : ℤ → ℂ)
    (hf : Summable (fun j : ℤ => (b + j + 1) * f j)) (hd : Summable d)
    (hl : ∀ j, l j = c * (d j + (b + j + 1) * f j - (b + j) * f (j - 1))) :
    Summable l ∧ (∑' j, l j) = c * ∑' j, d j := by
  let g : ℤ → ℂ := fun j => (b + j + 1) * f j
  have he (j : ℤ) : (b + j) * f (j - 1) = g (j - 1) := by
    dsimp [g]
    push_cast
    congr 1
    ring
  have hs : Summable (fun j : ℤ => g (j - 1)) :=
    ((Equiv.subRight (1 : ℤ)).summable_iff).mpr hf
  have hdiff : Summable (fun j => (b + j + 1) * f j - (b + j) * f (j - 1)) := by
    simpa only [he] using hf.sub hs
  have hl' : l = fun j => c * (d j + ((b + j + 1) * f j - (b + j) * f (j - 1))) := by
    funext j
    rw [hl]
    ring
  rw [hl']
  refine ⟨(hd.add hdiff).mul_left c, ?_⟩
  rw [tsum_mul_left, hd.tsum_add hdiff, tsum_mode_difference b f hf, add_zero]

/-- First-coordinate spatial insertion, summed on the full complex mode
coset. Differentiation of a further trace sum still requires analytic control. -/
theorem huangModifiedModeTrace_sum_Lm1_left
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (b n₂ t₁ t₂ e : ℂ)
    (hf : Summable (fun j : ℤ => (b + j + 1) *
      huangModifiedModeTrace Y₁ Y₂ w₁ w₂ (b + j) n₂ t₁ t₂ e))
    (hd : Summable (fun j : ℤ => _root_.deriv (fun s =>
      huangModifiedModeTrace Y₁ Y₂ w₁ w₂ (b + j) n₂ s t₂ e) t₁)) :
    Summable (fun j : ℤ =>
      huangModifiedModeTrace Y₁ Y₂ (P₁.isMod.Lm1 w₁) w₂ (b + j) n₂ t₁ t₂ e) ∧
    (∑' j : ℤ, huangModifiedModeTrace Y₁ Y₂ (P₁.isMod.Lm1 w₁) w₂
      (b + j) n₂ t₁ t₂ e) = Complex.exp logTwoPiI *
        ∑' j : ℤ, _root_.deriv (fun s =>
          huangModifiedModeTrace Y₁ Y₂ w₁ w₂ (b + j) n₂ s t₂ e) t₁ := by
  apply sum_spatial_law b (Complex.exp logTwoPiI) _ _ _ hf hd
  intro j
  have h := huangModifiedModeTrace_Lm1_left Y₁ Y₂ w₁ w₂ (b + j) n₂ t₁ t₂ e
  simpa only [Int.cast_sub, Int.cast_one, add_sub_assoc] using h

/-- Right-coordinate analogue; its summation hypotheses are independent. -/
theorem huangModifiedModeTrace_sum_Lm1_right
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (n₁ b t₁ t₂ e : ℂ)
    (hf : Summable (fun j : ℤ => (b + j + 1) *
      huangModifiedModeTrace Y₁ Y₂ w₁ w₂ n₁ (b + j) t₁ t₂ e))
    (hd : Summable (fun j : ℤ => _root_.deriv (fun s =>
      huangModifiedModeTrace Y₁ Y₂ w₁ w₂ n₁ (b + j) t₁ s e) t₂)) :
    Summable (fun j : ℤ =>
      huangModifiedModeTrace Y₁ Y₂ w₁ (P₂.isMod.Lm1 w₂) n₁ (b + j) t₁ t₂ e) ∧
    (∑' j : ℤ, huangModifiedModeTrace Y₁ Y₂ w₁ (P₂.isMod.Lm1 w₂)
      n₁ (b + j) t₁ t₂ e) = Complex.exp logTwoPiI *
        ∑' j : ℤ, _root_.deriv (fun s =>
          huangModifiedModeTrace Y₁ Y₂ w₁ w₂ n₁ (b + j) t₁ s e) t₂ := by
  apply sum_spatial_law b (Complex.exp logTwoPiI) _ _ _ hf hd
  intro j
  have h := huangModifiedModeTrace_Lm1_right Y₁ Y₂ w₁ w₂ n₁ (b + j) t₁ t₂ e
  simpa only [Int.cast_sub, Int.cast_one, add_sub_assoc] using h

end VOA.Huang.GenusTwoPoint.Separate
