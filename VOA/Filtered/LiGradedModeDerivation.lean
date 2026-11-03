import VOA.Filtered.LiGradedModeTranslation

/-!
# Translation is a derivation of every descended Li mode

The one-step boundary where the original mode has negative Li degree is handled
using translation of the zeroth filtration piece, rather than dropping that case.
-/

namespace VOA
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

@[simp] theorem liGradedClass_add (W : VertexOperatorAlgebra V) (p N : ℕ)
    (x y : V) (hx : x ∈ liWeightPiece W p N) (hy : y ∈ liWeightPiece W p N) :
    liGradedClass W p N (x + y) ((liWeightPiece W p N).add_mem hx hy) =
      liGradedClass W p N x hx + liGradedClass W p N y hy := by
  unfold liGradedClass
  rw [← map_add, ← map_add]
  rfl

/-- A representative one step higher in the filtration has zero graded class. -/
theorem liGradedClass_eq_zero_of_mem (W : VertexOperatorAlgebra V) (p N : ℕ)
    (x : V) (hx : x ∈ liWeightPiece W p N) (hx' : x ∈ liWeightPiece W (p + 1) N) :
    liGradedClass W p N x hx = 0 := by
  unfold liGradedClass
  have hz : ((liWeightPiece W (p + 1) N).comap
      (liWeightPiece W p N).subtype).mkQ ⟨x, hx⟩ = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hx'
  rw [hz, map_zero]

/-- Explicit vanishing when either target index would be negative. -/
theorem liGradedClass_mode_eq_zero (W : VertexOperatorAlgebra V) (p q N M n : ℕ)
    (h : ¬ n ≤ p + q ∨ ¬ n + 1 ≤ N + M)
    (x y : V) (hx : x ∈ liWeightPiece W p N) (hy : y ∈ liWeightPiece W q M) :
    liAssociatedGradedMode W n (liGradedClass W p N x hx) (liGradedClass W q M y hy) = 0 := by
  unfold liGradedClass
  simp only [DirectSum.lof_eq_of]
  rw [liAssociatedGradedMode_of_of]
  rcases h with hn | hN
  · simp [liWeightLayerModeToGraded, hn]
  · unfold liWeightLayerModeToGraded
    split_ifs <;> simp_all

/-- A state mode with negative conformal output weight is zero by VOA positivity. -/
theorem smul_eq_zero_of_conformal_lt (W : VertexOperatorAlgebra V)
    {N M n : ℕ} {x y : V} (hx : x ∈ W.grading N) (hy : y ∈ W.grading M)
    (h : ¬ n + 1 ≤ N + M) : W.smul x (n : ℤ) y = 0 := by
  have hg := W.smul_mem_grading hx hy (n : ℤ)
  rw [W.positivity _ (by omega)] at hg
  exact hg

/-- Translation is a derivation of a mode on homogeneous graded classes. -/
theorem liGradedClass_translation_mode (W : VertexOperatorAlgebra V)
    (p q N M n : ℕ) (x y : V)
    (hx : x ∈ liWeightPiece W p N) (hy : y ∈ liWeightPiece W q M) :
    liAssociatedGradedTranslation W
        (liAssociatedGradedMode W n (liGradedClass W p N x hx) (liGradedClass W q M y hy)) =
      liAssociatedGradedMode W n
          (liAssociatedGradedTranslation W (liGradedClass W p N x hx))
          (liGradedClass W q M y hy) +
        liAssociatedGradedMode W n (liGradedClass W p N x hx)
          (liAssociatedGradedTranslation W (liGradedClass W q M y hy)) := by
  rw [liGradedClass_translation, liGradedClass_translation]
  by_cases ha : n ≤ p + q + 1
  · by_cases hb : n + 1 ≤ N + M + 1
    · have hl := liWeightPiece_smul_nonneg_mem W
        (show n ≤ p + 1 + q by omega) (show n + 1 ≤ N + 1 + M by omega)
        (liWeightPiece_L_neg_one_mem W hx) hy
      have hr := liWeightPiece_smul_nonneg_mem W
        (show n ≤ p + (q + 1) by omega) (show n + 1 ≤ N + (M + 1) by omega)
        hx (liWeightPiece_L_neg_one_mem W hy)
      have hl' : W.smul (W.L (-1) x) (n : ℤ) y ∈
          liWeightPiece W (p + q + 1 - n) (N + M + 1 - (n + 1)) := by
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hl
      have hr' : W.smul x (n : ℤ) (W.L (-1) y) ∈
          liWeightPiece W (p + q + 1 - n) (N + M + 1 - (n + 1)) := by
        simpa only [Nat.add_assoc] using hr
      have hd : W.L (-1) (W.smul x (n : ℤ) y) =
          W.smul (W.L (-1) x) (n : ℤ) y + W.smul x (n : ℤ) (W.L (-1) y) := by
        have h := W.L_neg_one_deriv x y (n : ℤ)
        rw [sub_eq_iff_eq_add] at h
        simpa only [add_comm] using h
      have ht : W.L (-1) (W.smul x (n : ℤ) y) ∈
          liWeightPiece W (p + q + 1 - n) (N + M + 1 - (n + 1)) := by
        rw [hd]
        exact (liWeightPiece W _ _).add_mem hl' hr'
      rw [liGradedClass_mode W (p + 1) q (N + 1) M n (by omega) (by omega),
        liGradedClass_mode W p (q + 1) N (M + 1) n (by omega) (by omega)]
      rw [liGradedClass_reindex W (show p + 1 + q - n = p + q + 1 - n by omega)
        (show N + 1 + M - (n + 1) = N + M + 1 - (n + 1) by omega) hl hl',
        liGradedClass_reindex W (show p + (q + 1) - n = p + q + 1 - n by omega)
        (show N + (M + 1) - (n + 1) = N + M + 1 - (n + 1) by omega) hr hr']
      rw [← liGradedClass_add]
      have heq : liGradedClass W (p + q + 1 - n) (N + M + 1 - (n + 1))
          (W.smul (W.L (-1) x) (n : ℤ) y + W.smul x (n : ℤ) (W.L (-1) y))
          ((liWeightPiece W _ _).add_mem hl' hr') =
          liGradedClass W (p + q + 1 - n) (N + M + 1 - (n + 1))
            (W.L (-1) (W.smul x (n : ℤ) y)) ht := by
        congr 1
        exact hd.symm
      rw [heq]
      by_cases hn : n ≤ p + q
      · by_cases hN : n + 1 ≤ N + M
        · rw [liGradedClass_mode W p q N M n hn hN, liGradedClass_translation]
          exact liGradedClass_reindex W (by omega) (by omega) _ _
        · rw [liGradedClass_mode_eq_zero W p q N M n (Or.inr hN), map_zero]
          have hz := smul_eq_zero_of_conformal_lt W hx.2 hy.2 hN
          simp only [hz, map_zero]
          exact (liGradedClass_zero W _ _).symm
      · rw [liGradedClass_mode_eq_zero W p q N M n (Or.inl hn), map_zero]
        symm
        apply liGradedClass_eq_zero_of_mem
        refine ⟨?_, ht.2⟩
        have hzero : W.smul x (n : ℤ) y ∈ liFiltration W 0 := by
          rw [liFiltration_zero_eq_top]
          trivial
        have hh := liFiltration_L_neg_one_mem W hzero
        have hp : p + q + 1 - n = 0 := by omega
        simpa only [hp] using hh
    · rw [liGradedClass_mode_eq_zero W p q N M n (Or.inr (by omega)), map_zero,
        liGradedClass_mode_eq_zero W (p + 1) q (N + 1) M n (Or.inr (by omega)),
        liGradedClass_mode_eq_zero W p (q + 1) N (M + 1) n (Or.inr (by omega)), add_zero]
  · rw [liGradedClass_mode_eq_zero W p q N M n (Or.inl (by omega)), map_zero,
      liGradedClass_mode_eq_zero W (p + 1) q (N + 1) M n (Or.inl (by omega)),
      liGradedClass_mode_eq_zero W p (q + 1) N (M + 1) n (Or.inl (by omega)), add_zero]

/-- Translation is a derivation of every mode on the full Li associated graded. -/
theorem liAssociatedGradedTranslation_mode (W : VertexOperatorAlgebra V)
    (n : ℕ) (x y : liAssociatedGraded W) :
    liAssociatedGradedTranslation W (liAssociatedGradedMode W n x y) =
      liAssociatedGradedMode W n (liAssociatedGradedTranslation W x) y +
        liAssociatedGradedMode W n x (liAssociatedGradedTranslation W y) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of d x =>
      induction y using DirectSum.induction_on with
      | zero => simp
      | of e y =>
          refine Submodule.Quotient.induction_on _ x fun x => ?_
          refine Submodule.Quotient.induction_on _ y fun y => ?_
          exact liGradedClass_translation_mode W d.1 e.1 d.2 e.2 n x.1 y.1 x.2 y.2
      | add y z hy hz =>
          simp only [map_add, hy, hz]
          abel
  | add x z hx hz =>
      simp only [map_add, LinearMap.add_apply, hx, hz]
      abel

/-- Coefficientwise Li translation of a polynomial, keeping its formal variable fixed. -/
noncomputable def liPolynomialTranslation (W : VertexOperatorAlgebra V)
    (p : Polynomial (liAssociatedGraded W)) : Polynomial (liAssociatedGraded W) :=
  Polynomial.ofFinsupp (p.toFinsupp.mapRange (liAssociatedGradedTranslation W)
    (map_zero (liAssociatedGradedTranslation W)))

@[simp] theorem coeff_liPolynomialTranslation (W : VertexOperatorAlgebra V)
    (p : Polynomial (liAssociatedGraded W)) (n : ℕ) :
    (liPolynomialTranslation W p).coeff n = liAssociatedGradedTranslation W (p.coeff n) := by
  rfl

/-- Coefficientwise translation is a derivation of the lambda bracket. -/
theorem liPolynomialTranslation_lambdaBracket (W : VertexOperatorAlgebra V)
    (x y : liAssociatedGraded W) :
    liPolynomialTranslation W (liLambdaBracket W x y) =
      liLambdaBracket W (liAssociatedGradedTranslation W x) y +
        liLambdaBracket W x (liAssociatedGradedTranslation W y) := by
  apply Polynomial.ext
  intro n
  simp only [coeff_liPolynomialTranslation, Polynomial.coeff_add, coeff_liLambdaBracket,
    map_smul, liAssociatedGradedTranslation_mode, smul_add]

/-- Right sesquilinearity of the polynomial lambda bracket. -/
theorem liLambdaBracket_translation_right (W : VertexOperatorAlgebra V)
    (x y : liAssociatedGraded W) :
    liLambdaBracket W x (liAssociatedGradedTranslation W y) =
      liPolynomialTranslation W (liLambdaBracket W x y) +
        Polynomial.X * liLambdaBracket W x y := by
  have h := liPolynomialTranslation_lambdaBracket W x y
  rw [liLambdaBracket_translation_left] at h
  rw [h]
  ring

end VOA
