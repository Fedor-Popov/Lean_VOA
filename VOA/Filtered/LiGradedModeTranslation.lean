import VOA.Filtered.LiGradedModes

/-!
# Translation of the descended nonnegative Li modes

Sesquilinearity is proved from the vertex-algebra derivative identity, keeping
track of both Li and conformal indices and their vanishing boundary cases.
-/

namespace VOA

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Insert the class of a homogeneous Li representative into the total associated graded. -/
noncomputable def liGradedClass (W : VertexOperatorAlgebra V) (p N : ℕ)
    (x : V) (hx : x ∈ liWeightPiece W p N) : liAssociatedGraded W :=
  DirectSum.lof ℂ (ℕ × ℕ) (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N)
    (((liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype).mkQ ⟨x, hx⟩)

theorem liGradedClass_reindex (W : VertexOperatorAlgebra V) {p N q M : ℕ}
    (hp : p = q) (hN : N = M) {x : V}
    (hx : x ∈ liWeightPiece W p N) (hx' : x ∈ liWeightPiece W q M) :
    liGradedClass W p N x hx = liGradedClass W q M x hx' := by
  subst q; subst M; rfl

@[simp] theorem liGradedClass_smul (W : VertexOperatorAlgebra V) (p N : ℕ)
    (c : ℂ) (x : V) (hx : x ∈ liWeightPiece W p N) :
    liGradedClass W p N (c • x) ((liWeightPiece W p N).smul_mem c hx) =
      c • liGradedClass W p N x hx := by
  unfold liGradedClass
  rw [← map_smul, ← map_smul]
  rfl

@[simp] theorem liGradedClass_zero (W : VertexOperatorAlgebra V) (p N : ℕ) :
    liGradedClass W p N 0 (Submodule.zero_mem _) = 0 := by
  change (DirectSum.lof ℂ (ℕ × ℕ) (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N))
    (((liWeightPiece W (p + 1) N).comap (liWeightPiece W p N).subtype).mkQ 0) = 0
  simp

@[simp] theorem liGradedClass_translation (W : VertexOperatorAlgebra V) (p N : ℕ)
    (x : V) (hx : x ∈ liWeightPiece W p N) :
    liAssociatedGradedTranslation W (liGradedClass W p N x hx) =
      liGradedClass W (p + 1) (N + 1) (W.L (-1) x)
        (liWeightPiece_L_neg_one_mem W hx) := by
  unfold liGradedClass
  rw [DirectSum.lof_eq_of, liAssociatedGradedTranslation_of, liWeightLayerTranslation_mk]
  rfl

/-- Evaluation of a total mode on classes, when its target bidegree is nonnegative. -/
theorem liGradedClass_mode (W : VertexOperatorAlgebra V) (p q N M n : ℕ)
    (hn : n ≤ p + q) (hN : n + 1 ≤ N + M)
    (x y : V) (hx : x ∈ liWeightPiece W p N) (hy : y ∈ liWeightPiece W q M) :
    liAssociatedGradedMode W n (liGradedClass W p N x hx) (liGradedClass W q M y hy) =
      liGradedClass W (p + q - n) (N + M - (n + 1)) (W.smul x (n : ℤ) y)
        (liWeightPiece_smul_nonneg_mem W hn hN hx hy) := by
  unfold liGradedClass
  simp only [DirectSum.lof_eq_of]
  rw [liAssociatedGradedMode_of_of]
  simp only [liWeightLayerModeToGraded, hn, hN, dite_true, LinearMap.compr₂_apply,
    liWeightLayerMode_mk, DirectSum.lof_eq_of]

/-- The state-level derivative identity with natural mode index and complex scalar. -/
theorem smul_translation_succ (W : VertexOperatorAlgebra V) (x y : V) (n : ℕ) :
    W.smul (W.L (-1) x) ((n + 1 : ℕ) : ℤ) y =
      (-((n + 1 : ℕ) : ℂ)) • W.smul x (n : ℤ) y := by
  have h := congrArg (fun f : Module.End ℂ V => f y)
    (W.mode_Y_T x ((n + 1 : ℕ) : ℤ))
  rw [VertexOperatorAlgebra.T_eq_Lneg1] at h
  simpa only [PreVertexAlgebra.smul_def, LinearMap.smul_apply, Nat.cast_add, Nat.cast_one,
    add_sub_cancel_right, ← Int.cast_smul_eq_zsmul ℂ, Int.cast_neg, Int.cast_add,
    Int.cast_natCast, Int.cast_one] using h

/-- The positive-index left sesquilinearity law on homogeneous Li classes. -/
theorem liGradedClass_mode_translation_succ (W : VertexOperatorAlgebra V)
    (p q N M n : ℕ) (x y : V)
    (hx : x ∈ liWeightPiece W p N) (hy : y ∈ liWeightPiece W q M) :
    liAssociatedGradedMode W (n + 1)
        (liAssociatedGradedTranslation W (liGradedClass W p N x hx))
        (liGradedClass W q M y hy) =
      (-((n + 1 : ℕ) : ℂ)) •
        liAssociatedGradedMode W n (liGradedClass W p N x hx) (liGradedClass W q M y hy) := by
  rw [liGradedClass_translation]
  by_cases hn : n ≤ p + q
  · by_cases hN : n + 1 ≤ N + M
    · rw [liGradedClass_mode W (p + 1) q (N + 1) M (n + 1) (by omega) (by omega),
        liGradedClass_mode W p q N M n hn hN]
      have hp : p + 1 + q - (n + 1) = p + q - n := by omega
      have hw : N + 1 + M - (n + 1 + 1) = N + M - (n + 1) := by omega
      simp only [hp, hw, smul_translation_succ]
      exact liGradedClass_smul W _ _ _ _ _
    · have hN' : ¬ n + 1 + 1 ≤ N + 1 + M := by omega
      have hn' : n + 1 ≤ p + 1 + q := by omega
      unfold liGradedClass
      simp only [DirectSum.lof_eq_of]
      rw [liAssociatedGradedMode_of_of, liAssociatedGradedMode_of_of]
      simp [liWeightLayerModeToGraded, hn, hn', hN, hN']
  · have hn' : ¬ n + 1 ≤ p + 1 + q := by omega
    unfold liGradedClass
    simp only [DirectSum.lof_eq_of]
    rw [liAssociatedGradedMode_of_of, liAssociatedGradedMode_of_of]
    simp [liWeightLayerModeToGraded, hn, hn']

/-- Left sesquilinearity in every positive mode, for arbitrary graded elements. -/
theorem liAssociatedGradedMode_translation_succ (W : VertexOperatorAlgebra V)
    (n : ℕ) (x y : liAssociatedGraded W) :
    liAssociatedGradedMode W (n + 1) (liAssociatedGradedTranslation W x) y =
      (-((n + 1 : ℕ) : ℂ)) • liAssociatedGradedMode W n x y := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of d x =>
      induction y using DirectSum.induction_on with
      | zero => simp
      | of e y =>
          refine Submodule.Quotient.induction_on _ x fun x => ?_
          refine Submodule.Quotient.induction_on _ y fun y => ?_
          exact liGradedClass_mode_translation_succ W d.1 e.1 d.2 e.2 n
            x.1 y.1 x.2 y.2
      | add y z hy hz => simp only [map_add, smul_add, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, smul_add, hx, hz]

/-- The zero mode of a translated state vanishes already in the original VOA. -/
theorem smul_translation_zero (W : VertexOperatorAlgebra V) (x y : V) :
    W.smul (W.L (-1) x) 0 y = 0 := by
  have h := congrArg (fun f : Module.End ℂ V => f y) (W.mode_Y_T x 0)
  rw [VertexOperatorAlgebra.T_eq_Lneg1] at h
  simpa only [PreVertexAlgebra.smul_def, neg_zero, zero_smul, LinearMap.zero_apply] using h

/-- The zero-mode left sesquilinearity law on homogeneous Li classes. -/
theorem liGradedClass_mode_translation_zero (W : VertexOperatorAlgebra V)
    (p q N M : ℕ) (x y : V)
    (hx : x ∈ liWeightPiece W p N) (hy : y ∈ liWeightPiece W q M) :
    liAssociatedGradedMode W 0
        (liAssociatedGradedTranslation W (liGradedClass W p N x hx))
        (liGradedClass W q M y hy) = 0 := by
  rw [liGradedClass_translation,
    liGradedClass_mode W (p + 1) q (N + 1) M 0 (by omega) (by omega)]
  simp only [Nat.cast_zero, smul_translation_zero]
  exact liGradedClass_zero W _ _

/-- The zero mode of a translated first argument vanishes on the whole graded algebra. -/
theorem liAssociatedGradedMode_translation_zero (W : VertexOperatorAlgebra V)
    (x y : liAssociatedGraded W) :
    liAssociatedGradedMode W 0 (liAssociatedGradedTranslation W x) y = 0 := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of d x =>
      induction y using DirectSum.induction_on with
      | zero => simp
      | of e y =>
          refine Submodule.Quotient.induction_on _ x fun x => ?_
          refine Submodule.Quotient.induction_on _ y fun y => ?_
          exact liGradedClass_mode_translation_zero W d.1 e.1 d.2 e.2
            x.1 y.1 x.2 y.2
      | add y z hy hz => simp only [map_add, hy, hz, add_zero]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz, add_zero]

/-- Left sesquilinearity of the actual polynomial lambda bracket. -/
theorem liLambdaBracket_translation_left (W : VertexOperatorAlgebra V)
    (x y : liAssociatedGraded W) :
    liLambdaBracket W (liAssociatedGradedTranslation W x) y =
      -(Polynomial.X * liLambdaBracket W x y) := by
  apply Polynomial.ext
  intro n
  cases n with
  | zero =>
      simp [liAssociatedGradedMode_translation_zero, Polynomial.coeff_X_mul]
  | succ n =>
      simp only [coeff_liLambdaBracket, liAssociatedGradedMode_translation_succ,
        Polynomial.coeff_neg, Polynomial.coeff_X_mul, Nat.add_sub_cancel,
        Nat.succ_eq_add_one, smul_smul]
      have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      have heq : ((n + 1).factorial : ℂ)⁻¹ * (-((n + 1 : ℕ) : ℂ)) =
          -(n.factorial : ℂ)⁻¹ := by
        rw [Nat.factorial_succ, Nat.cast_mul]
        field_simp
      rw [heq, neg_smul]

end VOA
