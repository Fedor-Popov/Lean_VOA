import VOA.Filtered.LiGradedModeJacobi
import VOA.Filtered.LiGeneratorWords

/-!
# Skew-symmetry of the nonnegative Li modes

The state-level skew formula descends term by term; terms crossing the Li-degree
boundary are killed by the extra translation degree.
-/

namespace VOA
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Iterated translation raises the conformal degree by the iteration count. -/
theorem li_T_pow_mem_grading (W : VertexOperatorAlgebra V) {k : ℤ} {x : V}
    (hx : x ∈ W.grading k) (j : ℕ) :
    (W.toPreVertexAlgebra.T ^ j) x ∈ W.grading (k + j) := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
      rw [pow_succ', Module.End.mul_apply]
      have h := W.toPreVertexAlgebra.T_mem_grading ih
      simpa only [Nat.cast_succ, add_assoc] using h

/-- Powers of the actual graded translation agree with powers on representatives. -/
theorem liGradedClass_T_pow (W : VertexOperatorAlgebra V) (p N j : ℕ)
    (x : V) (hx : x ∈ liWeightPiece W p N) :
    (liAssociatedGradedTranslation W ^ j) (liGradedClass W p N x hx) =
      liGradedClass W (p + j) (N + j) ((W.toPreVertexAlgebra.T ^ j) x)
        (liWeightPiece_T_pow_mem W hx j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih, liGradedClass_translation]
      simp only [pow_succ', Module.End.mul_apply, VertexOperatorAlgebra.T_eq_Lneg1]
      exact liGradedClass_reindex W (by omega) (by omega) _ _

/-- Every translated skew summand belongs to the total output bidegree. -/
theorem liWeightPiece_skew_term_mem (W : VertexOperatorAlgebra V)
    {p q N M n : ℕ} (hn : n ≤ p + q) (hN : n + 1 ≤ N + M)
    {x y : V} (hx : x ∈ liWeightPiece W p N) (hy : y ∈ liWeightPiece W q M) (j : ℕ) :
    (W.toPreVertexAlgebra.T ^ j) (W.smul y ((n + j : ℕ) : ℤ) x) ∈
      liWeightPiece W (p + q - n) (N + M - (n + 1)) := by
  refine ⟨?_, ?_⟩
  · by_cases hj : n + j ≤ q + p
    · have h := liFiltration_T_pow_mem W j (liFiltration_smul_nonneg_mem W hj hy.1 hx.1)
      have heq : q + p - (n + j) + j = p + q - n := by omega
      simpa only [heq] using h
    · have hzero : W.smul y ((n + j : ℕ) : ℤ) x ∈ liFiltration W 0 := by
        rw [liFiltration_zero_eq_top]
        trivial
      exact liFiltration_antitone W (by omega) (liFiltration_T_pow_mem W j hzero)
  · have hg := li_T_pow_mem_grading W (W.smul_mem_grading hy.2 hx.2 ((n + j : ℕ) : ℤ)) j
    have heq : ((N + M - (n + 1) : ℕ) : ℤ) =
        ((M : ℤ) + N - ((n + j : ℕ) : ℤ) - 1) + j := by
      rw [Nat.cast_sub hN]
      push_cast
      ring
    simpa only [heq] using hg

/-- Translated descended modes agree with the classes of the original skew summands. -/
theorem liGradedClass_skew_term (W : VertexOperatorAlgebra V)
    (p q N M n j : ℕ) (hn : n ≤ p + q) (hN : n + 1 ≤ N + M)
    (x y : V) (hx : x ∈ liWeightPiece W p N) (hy : y ∈ liWeightPiece W q M) :
    (liAssociatedGradedTranslation W ^ j)
        (liAssociatedGradedMode W (n + j) (liGradedClass W q M y hy) (liGradedClass W p N x hx)) =
      liGradedClass W (p + q - n) (N + M - (n + 1))
        ((W.toPreVertexAlgebra.T ^ j) (W.smul y ((n + j : ℕ) : ℤ) x))
        (liWeightPiece_skew_term_mem W hn hN hx hy j) := by
  by_cases hj : n + j ≤ q + p
  · by_cases hjN : n + j + 1 ≤ M + N
    · rw [liGradedClass_mode W q p M N (n + j) hj hjN, liGradedClass_T_pow]
      exact liGradedClass_reindex W (by omega) (by omega) _ _
    · rw [liGradedClass_mode_eq_zero W q p M N (n + j) (Or.inr hjN), map_zero]
      have hzero := smul_eq_zero_of_conformal_lt W hy.2 hx.2 hjN
      simp only [hzero, map_zero]
      exact (liGradedClass_zero W _ _).symm
  · rw [liGradedClass_mode_eq_zero W q p M N (n + j) (Or.inl hj), map_zero]
    symm
    apply liGradedClass_eq_zero_of_mem
    refine ⟨?_, (liWeightPiece_skew_term_mem W hn hN hx hy j).2⟩
    have hzero : W.smul y ((n + j : ℕ) : ℤ) x ∈ liFiltration W 0 := by
      rw [liFiltration_zero_eq_top]
      trivial
    exact liFiltration_antitone W (by omega) (liFiltration_T_pow_mem W j hzero)

/-- Factorial-normalized translated term in the graded skew formula. -/
noncomputable def liSkewTerm (W : VertexOperatorAlgebra V) (n : ℕ)
    (x y : liAssociatedGraded W) (j : ℕ) : liAssociatedGraded W :=
  (j.factorial : ℂ)⁻¹ • sgn (-(n : ℤ) - 1 - j) •
    ((liAssociatedGradedTranslation W ^ j) (liAssociatedGradedMode W (n + j) y x))

/-- The graded skew sum is genuinely finite on every input pair. -/
theorem liSkewTerm_support_finite (W : VertexOperatorAlgebra V) (n : ℕ)
    (x y : liAssociatedGraded W) : (Function.support (liSkewTerm W n x y)).Finite := by
  obtain ⟨B, hB⟩ := liAssociatedGradedMode_eventually_zero W y x
  apply (Finset.finite_toSet (Finset.range B)).subset
  intro j hj
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  apply hj
  change liSkewTerm W n x y j = 0
  simp only [liSkewTerm, hB (n + j) (by omega), map_zero, smul_zero]

/-- Skew-symmetry on homogeneous Li classes, descended from the genuine VOA skew formula. -/
theorem liGradedClass_mode_skew (W : VertexOperatorAlgebra V)
    (p q N M n : ℕ) (x y : V)
    (hx : x ∈ liWeightPiece W p N) (hy : y ∈ liWeightPiece W q M) :
    liAssociatedGradedMode W n (liGradedClass W p N x hx) (liGradedClass W q M y hy) =
      ∑ᶠ j : ℕ, liSkewTerm W n (liGradedClass W p N x hx) (liGradedClass W q M y hy) j := by
  by_cases hn : n ≤ p + q
  · by_cases hN : n + 1 ≤ N + M
    · let F (j : ℕ) : liWeightPiece W (p + q - n) (N + M - (n + 1)) :=
        (j.factorial : ℂ)⁻¹ • sgn (-(n : ℤ) - 1 - j) •
          ⟨(W.toPreVertexAlgebra.T ^ j) (W.smul y ((n + j : ℕ) : ℤ) x),
            liWeightPiece_skew_term_mem W hn hN hx hy j⟩
      have hfin : (Function.support F).Finite := by
        apply (Finset.finite_toSet (Finset.range (N + M + 1))).subset
        intro j hj
        simp only [Finset.mem_coe, Finset.mem_range]
        by_contra hj'
        apply hj
        apply Subtype.ext
        have hz := smul_eq_zero_of_conformal_lt W hy.2 hx.2
          (show ¬ n + j + 1 ≤ M + N by omega)
        simp only [F, Submodule.coe_smul, hz, map_zero, smul_zero, ZeroMemClass.coe_zero]
      have hcoeff (j : ℕ) : (W.Y y (-(n : ℤ) - 1 - j)) x =
          W.smul y ((n + j : ℕ) : ℤ) x := by
        rw [PreVertexAlgebra.smul_eq_coeff]
        congr 2
        push_cast
        ring
      have hskew := W.skew_mode x y (n : ℤ)
      simp_rw [hcoeff] at hskew
      have hrep : (⟨W.smul x (n : ℤ) y,
          liWeightPiece_smul_nonneg_mem W hn hN hx hy⟩ :
          liWeightPiece W (p + q - n) (N + M - (n + 1))) = ∑ᶠ j : ℕ, F j := by
        apply Subtype.ext
        change W.smul x (n : ℤ) y =
          (liWeightPiece W (p + q - n) (N + M - (n + 1))).subtype (∑ᶠ j : ℕ, F j)
        have hmap : (liWeightPiece W (p + q - n) (N + M - (n + 1))).subtype
            (∑ᶠ j : ℕ, F j) = ∑ᶠ j : ℕ,
              (liWeightPiece W (p + q - n) (N + M - (n + 1))).subtype (F j) :=
          (liWeightPiece W (p + q - n) (N + M - (n + 1))).subtype.toAddMonoidHom.map_finsum hfin
        rw [hmap]
        simpa only [F, Submodule.coe_smul] using hskew
      let π : liWeightPiece W (p + q - n) (N + M - (n + 1)) →ₗ[ℂ]
          liAssociatedGraded W :=
        (DirectSum.lof ℂ (ℕ × ℕ) (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2)
          (p + q - n, N + M - (n + 1))).comp
          (((liWeightPiece W (p + q - n + 1) (N + M - (n + 1))).comap
            (liWeightPiece W (p + q - n) (N + M - (n + 1))).subtype).mkQ)
      have hπ (j : ℕ) : π (F j) =
          liSkewTerm W n (liGradedClass W p N x hx) (liGradedClass W q M y hy) j := by
        simp only [F, map_smul]
        change (j.factorial : ℂ)⁻¹ • sgn (-(n : ℤ) - 1 - j) •
          liGradedClass W (p + q - n) (N + M - (n + 1))
            ((W.toPreVertexAlgebra.T ^ j) (W.smul y ((n + j : ℕ) : ℤ) x)) _ = _
        rw [← liGradedClass_skew_term W p q N M n j hn hN]
        rfl
      rw [liGradedClass_mode W p q N M n hn hN]
      change π ⟨W.smul x (n : ℤ) y, liWeightPiece_smul_nonneg_mem W hn hN hx hy⟩ = _
      have hmap : π (∑ᶠ j : ℕ, F j) = ∑ᶠ j : ℕ, π (F j) :=
        π.toAddMonoidHom.map_finsum hfin
      rw [hrep, hmap]
      exact finsum_congr hπ
    · rw [liGradedClass_mode_eq_zero W p q N M n (Or.inr hN)]
      symm
      apply finsum_eq_zero_of_forall_eq_zero
      intro j
      rw [liSkewTerm, liGradedClass_mode_eq_zero W q p M N (n + j) (Or.inr (by omega))]
      simp
  · rw [liGradedClass_mode_eq_zero W p q N M n (Or.inl hn)]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    rw [liSkewTerm, liGradedClass_mode_eq_zero W q p M N (n + j) (Or.inl (by omega))]
    simp

theorem liSkewTerm_add_left (W : VertexOperatorAlgebra V) (n j : ℕ)
    (x z y : liAssociatedGraded W) :
    liSkewTerm W n (x + z) y j = liSkewTerm W n x y j + liSkewTerm W n z y j := by
  simp only [liSkewTerm, map_add, smul_add]

theorem liSkewTerm_add_right (W : VertexOperatorAlgebra V) (n j : ℕ)
    (x y z : liAssociatedGraded W) :
    liSkewTerm W n x (y + z) j = liSkewTerm W n x y j + liSkewTerm W n x z j := by
  simp only [liSkewTerm, map_add, LinearMap.add_apply, smul_add]

/-- Skew-symmetry of the actual Li nonnegative modes on arbitrary graded inputs. -/
theorem liAssociatedGradedMode_skew (W : VertexOperatorAlgebra V)
    (n : ℕ) (x y : liAssociatedGraded W) :
    liAssociatedGradedMode W n x y = ∑ᶠ j : ℕ, liSkewTerm W n x y j := by
  induction x using DirectSum.induction_on with
  | zero => simp [liSkewTerm]
  | of d x =>
      induction y using DirectSum.induction_on with
      | zero => simp [liSkewTerm]
      | of e y =>
          refine Submodule.Quotient.induction_on _ x fun x => ?_
          refine Submodule.Quotient.induction_on _ y fun y => ?_
          exact liGradedClass_mode_skew W d.1 e.1 d.2 e.2 n x.1 y.1 x.2 y.2
      | add y z hy hz =>
          simp only [map_add, hy, hz]
          simp_rw [liSkewTerm_add_right]
          exact (finsum_add_distrib (liSkewTerm_support_finite W n _ y)
            (liSkewTerm_support_finite W n _ z)).symm
  | add x z hx hz =>
      simp only [map_add, LinearMap.add_apply, hx, hz]
      simp_rw [liSkewTerm_add_left]
      exact (finsum_add_distrib (liSkewTerm_support_finite W n x y)
        (liSkewTerm_support_finite W n z y)).symm

end VOA
