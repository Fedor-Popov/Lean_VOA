import VOA.Huang.FusionTop

/-! # Reconstructing the FHL axioms from grading and Jacobi

This supplies a reconstruction step for a scalar-pairing approach to Li's
converse (Li, J. Algebra 212 (1999), Corollary 2.13, as cited in Miyamoto,
arXiv:math/0010180, Theorem 2.10). It does not construct the extension of a
top datum. For ordinary modules, grading gives truncation; the conformal Jacobi
identity then gives the derivative identity. Neither condition needs to be
included in the remaining scalar extension problem.
-/
namespace VOA.Huang.LiFusion
open VOA FusionTop
open scoped BigOperators
universe u
variable {V M₁ M₂ M₃ : Type u}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  {W : VertexOperatorAlgebra V}
  {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃}

/-- The coefficient of index `n` has output weight `α + β - n - 1`. -/
def WeightCompatible (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂)
    (A₃ : OrdVModule W M₃) (Y : IntertwiningModes M₁ M₂ M₃) : Prop :=
  ∀ (α β : ℂ) (x : M₁) (y : M₂), x ∈ A₁.weight α → y ∈ A₂.weight β →
    ∀ n, Y n x y ∈ A₃.weight (α + β - n - 1)

/-- Only the Jacobi equations, without presupposing an intertwiner. -/
def ModeJacobi (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂)
    (A₃ : OrdVModule W M₃) (Y : IntertwiningModes M₁ M₂ M₃) : Prop :=
  ∀ (a : V) (x : M₁) (y : M₂) (l m : ℤ) (n : ℂ),
    (∑ᶠ i : ℤ, IsIntertwiningOperator.jacL A₂ A₃ Y a x y l m n i) =
      ∑ᶠ i : ℤ, IsIntertwiningOperator.jacR A₁ Y a x y l m n i

theorem truncation_of_weightCompatible {Y : IntertwiningModes M₁ M₂ M₃}
    (hw : WeightCompatible A₁ A₂ A₃ Y) :
    ∀ x y n, ∃ N : ℤ, ∀ k : ℤ, N ≤ k → Y (n + k) x y = 0 := by
  intro x
  induction x using induction_weight A₁ with
  | h0 => intro y n; exact ⟨0, fun _ _ => by simp⟩
  | hadd x x' hx hx' =>
    intro y n
    obtain ⟨N, hN⟩ := hx y n
    obtain ⟨N', hN'⟩ := hx' y n
    exact ⟨max N N', fun k hk => by
      simp [hN k (le_trans (le_max_left _ _) hk),
        hN' k (le_trans (le_max_right _ _) hk)]⟩
  | hhom α x hx =>
    intro y
    induction y using induction_weight A₂ with
    | h0 => intro n; exact ⟨0, fun _ _ => by simp⟩
    | hadd y y' hy hy' =>
      intro n
      obtain ⟨N, hN⟩ := hy n
      obtain ⟨N', hN'⟩ := hy' n
      exact ⟨max N N', fun k hk => by
        simp [hN k (le_trans (le_max_left _ _) hk),
          hN' k (le_trans (le_max_right _ _) hk)]⟩
    | hhom β y hy =>
      intro n
      obtain ⟨B, hB⟩ := A₃.boundedBelow
      obtain ⟨N, hN⟩ := exists_int_gt (α.re + β.re - n.re - 1 - B)
      refine ⟨N, fun k hk => ?_⟩
      have hbot : A₃.weight (α + β - (n + k) - 1) = ⊥ := by
        by_contra hn
        have hb := hB _ hn
        have hnk : (N : ℝ) ≤ k := by exact_mod_cast hk
        simp only [Complex.sub_re, Complex.add_re, Complex.intCast_re, Complex.one_re] at hb
        linarith
      simpa only [hbot, Submodule.mem_bot] using hw α β x y hx hy (n + k)

theorem ModeJacobi.commutator {Y : IntertwiningModes M₁ M₂ M₃}
    (hj : ModeJacobi A₁ A₂ A₃ Y) (a : V) (x : M₁) (y : M₂) (m : ℤ) (n : ℂ) :
    mode (A₃.YM a) m (Y n x y) - Y n x (mode (A₂.YM a) m y) =
      ∑ᶠ i : ℤ, cbz m i • Y (m + n - i) (mode (A₁.YM a) i x) y := by
  have h := hj a x y 0 m n
  dsimp only [IsIntertwiningOperator.jacL, IsIntertwiningOperator.jacR] at h
  rw [finsum_eq_single _ (0 : ℤ)] at h
  · simpa [IsIntertwiningOperator.jacR, cbz_zero_left, negOnePow] using h
  · intro i hi
    simp [cbz_zero_left, hi]

/-- The conformal Jacobi identity recovers `L(-1)` from the weight rule. -/
theorem derivative_of_weightCompatible_jacobi {Y : IntertwiningModes M₁ M₂ M₃}
    (hw : WeightCompatible A₁ A₂ A₃ Y) (hj : ModeJacobi A₁ A₂ A₃ Y) :
    ∀ x n, Y n (A₁.Lm1 x) = (-n) • Y (n - 1) x := by
  have hom (α β : ℂ) (x : M₁) (y : M₂) (hx : x ∈ A₁.weight α)
      (hy : y ∈ A₂.weight β) (n : ℂ) :
      Y n (A₁.Lm1 x) y = (-n) • Y (n - 1) x y := by
    have hc := hj.commutator W.conformalVector x y 1 (n - 1)
    rw [finsum_eq_sum_of_support_subset _ (s := ({0, 1} : Finset ℤ))] at hc
    · rw [Finset.sum_pair (by norm_num)] at hc
      have hb : gBinom 1 1 = 1 := by simp [gBinom]
      simp only [cbz_apply_nonneg 1 le_rfl, cbz_apply_nonneg 1 zero_le_one,
        Int.toNat_zero, Int.toNat_one, gBinom_zero, hb, one_smul,
        Int.cast_one, Int.cast_zero, sub_zero] at hc
      rw [show (1 : ℂ) + (n - 1) = n by ring,
        A₃.L0_weight _ _ (hw α β x y hx hy (n - 1)),
        A₂.L0_weight _ _ hy, A₁.L0_weight _ _ hx, map_smul, map_smul,
        LinearMap.smul_apply] at hc
      change Y n (mode (A₁.YM W.conformalVector) 0 x) y = _
      have he : α + β - (n - 1) - 1 = α + β - n := by ring
      rw [he] at hc
      rw [eq_sub_of_add_eq hc.symm]
      module
    · intro i hi
      rw [Function.mem_support] at hi
      by_contra hn
      have hn' : i ≠ 0 ∧ i ≠ 1 := by simpa using hn
      apply hi
      have hz : cbz 1 i = 0 := by
        rcases lt_or_ge i 0 with hneg | hnonneg
        · exact cbz_apply_neg 1 hneg
        · rw [cbz_apply_nonneg 1 hnonneg, gBinom]
          rw [Finset.prod_eq_zero (i := 1) (Finset.mem_range.mpr (by omega))
            (by push_cast; ring)]
          simp
      rw [hz, zero_smul]
  intro x n
  apply LinearMap.ext
  intro y
  induction x using induction_weight A₁ with
  | h0 => simp
  | hadd x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', smul_add]
  | hhom α x hx =>
    induction y using induction_weight A₂ with
    | h0 => simp
    | hadd y y' hy hy' => simp only [map_add, hy, hy', LinearMap.smul_apply]
    | hhom β y hy => exact hom α β x y hx hy n

/-- Reconstruction requires just grading and Jacobi. Both other FHL axioms
are proved here, rather than assumed in a scalar extension interface. -/
theorem isIntertwiningOperator_of_weightCompatible_jacobi
    {Y : IntertwiningModes M₁ M₂ M₃}
    (hw : WeightCompatible A₁ A₂ A₃ Y) (hj : ModeJacobi A₁ A₂ A₃ Y) :
    IsIntertwiningOperator A₁ A₂ A₃ Y :=
  ⟨truncation_of_weightCompatible hw, derivative_of_weightCompatible_jacobi hw hj, hj⟩

end VOA.Huang.LiFusion
