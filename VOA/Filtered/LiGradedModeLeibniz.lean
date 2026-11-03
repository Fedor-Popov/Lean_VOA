import VOA.Filtered.LiGradedModeDerivation
import VOA.Filtered.LiModeLeibniz

/-!
# Leibniz descent for the Li lambda bracket

The state-level one-step estimate is compared with the independently descended
multiplication and nonnegative modes, including vanishing intermediate degrees.
-/

namespace VOA
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Homogeneous representatives multiply by the original minus-one vertex mode. -/
theorem liGradedClass_mul (W : VertexOperatorAlgebra V) (p q N M : ℕ)
    (x y : V) (hx : x ∈ liWeightPiece W p N) (hy : y ∈ liWeightPiece W q M) :
    liGradedClass W p N x hx * liGradedClass W q M y hy =
      liGradedClass W (p + q) (N + M) (W.smul x (-1) y)
        (liWeightPiece_smul_neg_one_mem W hx hy) := by
  unfold liGradedClass
  simp only [DirectSum.lof_eq_of]
  rw [liAssociatedGraded_of_mul_of, liWeightLayerMul_mk]

/-- Nested mode-product representatives have the total predicted bidegree even when
an intermediate mode has negative formal Li degree. -/
theorem liWeightPiece_mode_mul_mem (W : VertexOperatorAlgebra V)
    {p q r N M L n : ℕ} (hn : n ≤ p + q + r) (hN : n + 1 ≤ N + M + L)
    {x y z : V} (hx : x ∈ liWeightPiece W p N)
    (hy : y ∈ liWeightPiece W q M) (hz : z ∈ liWeightPiece W r L) :
    W.smul (W.smul x (n : ℤ) y) (-1) z ∈
      liWeightPiece W (p + q + r - n) (N + M + L - (n + 1)) := by
  refine ⟨?_, ?_⟩
  · have hxy := adjointGfil_smul_nonneg_mem W n hx.1 hy.1
    have hprod := adjointGfil_smul_mem W (lwGenerated_adjoint W) hxy hz.1 (N := -1)
    change W.smul (W.smul x (n : ℤ) y) (-1) z ∈
      Gfil (adjointWeakModule W) ({W.vacuum} : Set V) (p + q - (n : ℤ) + r - (-1) - 1)
      at hprod
    change W.smul (W.smul x (n : ℤ) y) (-1) z ∈
      Gfil (adjointWeakModule W) ({W.vacuum} : Set V) ((p + q + r - n : ℕ) : ℤ)
    have heq : ((p + q + r - n : ℕ) : ℤ) =
        (p : ℤ) + q - (n : ℤ) + r - (-1) - 1 := by
      rw [Nat.cast_sub hn, Nat.cast_add, Nat.cast_add]
      ring
    rw [heq]
    exact hprod
  · have hgr := W.smul_mem_grading (W.smul_mem_grading hx.2 hy.2 (n : ℤ)) hz.2 (-1)
    have heq : ((N + M + L - (n + 1) : ℕ) : ℤ) =
        ((N : ℤ) + M - n - 1) + L - (-1) - 1 := by
      rw [Nat.cast_sub hN, Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_one]
      ring
    simpa only [heq] using hgr

/-- Multiplying a descended mode agrees with the total-bidegree class of the original
nested vertex products, even if the intermediate graded mode is forced to vanish. -/
theorem liGradedClass_mode_mul (W : VertexOperatorAlgebra V)
    (p q r N M L n : ℕ) (hn : n ≤ p + q + r) (hN : n + 1 ≤ N + M + L)
    (x y z : V) (hx : x ∈ liWeightPiece W p N)
    (hy : y ∈ liWeightPiece W q M) (hz : z ∈ liWeightPiece W r L) :
    liAssociatedGradedMode W n (liGradedClass W p N x hx) (liGradedClass W q M y hy) *
        liGradedClass W r L z hz =
      liGradedClass W (p + q + r - n) (N + M + L - (n + 1))
        (W.smul (W.smul x (n : ℤ) y) (-1) z)
        (liWeightPiece_mode_mul_mem W hn hN hx hy hz) := by
  by_cases hn' : n ≤ p + q
  · by_cases hN' : n + 1 ≤ N + M
    · rw [liGradedClass_mode W p q N M n hn' hN', liGradedClass_mul]
      exact liGradedClass_reindex W (by omega) (by omega) _ _
    · rw [liGradedClass_mode_eq_zero W p q N M n (Or.inr hN'), zero_mul]
      have hzero := smul_eq_zero_of_conformal_lt W hx.2 hy.2 hN'
      simp only [hzero, PreVertexAlgebra.smul_zero_left]
      exact (liGradedClass_zero W _ _).symm
  · rw [liGradedClass_mode_eq_zero W p q N M n (Or.inl hn'), zero_mul]
    symm
    apply liGradedClass_eq_zero_of_mem
    refine ⟨?_, (liWeightPiece_mode_mul_mem W hn hN hx hy hz).2⟩
    have hxy : W.smul x (n : ℤ) y ∈ liFiltration W 0 := by
      rw [liFiltration_zero_eq_top]
      trivial
    have hprod := liFiltration_smul_neg_one_mem W hxy hz.1
    exact liFiltration_antitone W (by omega) hprod

/-- Nested mode-product representatives have the total predicted bidegree even when
an intermediate mode has negative formal Li degree. -/
theorem liWeightPiece_mul_mode_mem (W : VertexOperatorAlgebra V)
    {p q r N M L n : ℕ} (hn : n ≤ p + q + r) (hN : n + 1 ≤ N + M + L)
    {x y z : V} (hx : x ∈ liWeightPiece W p N)
    (hy : y ∈ liWeightPiece W q M) (hz : z ∈ liWeightPiece W r L) :
    W.smul z (-1) (W.smul x (n : ℤ) y) ∈
      liWeightPiece W (p + q + r - n) (N + M + L - (n + 1)) := by
  refine ⟨?_, ?_⟩
  · have hxy := adjointGfil_smul_nonneg_mem W n hx.1 hy.1
    have hprod := adjointGfil_smul_mem W (lwGenerated_adjoint W) hz.1 hxy (N := -1)
    change W.smul z (-1) (W.smul x (n : ℤ) y) ∈
      Gfil (adjointWeakModule W) ({W.vacuum} : Set V) (r + (p + q - (n : ℤ)) - (-1) - 1)
      at hprod
    change W.smul z (-1) (W.smul x (n : ℤ) y) ∈
      Gfil (adjointWeakModule W) ({W.vacuum} : Set V) ((p + q + r - n : ℕ) : ℤ)
    have heq : ((p + q + r - n : ℕ) : ℤ) =
        (r : ℤ) + ((p : ℤ) + q - (n : ℤ)) - (-1) - 1 := by
      rw [Nat.cast_sub hn, Nat.cast_add, Nat.cast_add]
      ring
    rw [heq]
    exact hprod
  · have hgr := W.smul_mem_grading hz.2 (W.smul_mem_grading hx.2 hy.2 (n : ℤ)) (-1)
    have heq : ((N + M + L - (n + 1) : ℕ) : ℤ) =
        (L : ℤ) + ((N : ℤ) + M - n - 1) - (-1) - 1 := by
      rw [Nat.cast_sub hN, Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_one]
      ring
    simpa only [heq] using hgr

/-- Multiplying a descended mode agrees with the total-bidegree class of the original
nested vertex products, even if the intermediate graded mode is forced to vanish. -/
theorem liGradedClass_mul_mode (W : VertexOperatorAlgebra V)
    (p q r N M L n : ℕ) (hn : n ≤ p + q + r) (hN : n + 1 ≤ N + M + L)
    (x y z : V) (hx : x ∈ liWeightPiece W p N)
    (hy : y ∈ liWeightPiece W q M) (hz : z ∈ liWeightPiece W r L) :
    liGradedClass W r L z hz *
        liAssociatedGradedMode W n (liGradedClass W p N x hx) (liGradedClass W q M y hy) =
      liGradedClass W (p + q + r - n) (N + M + L - (n + 1))
        (W.smul z (-1) (W.smul x (n : ℤ) y))
        (liWeightPiece_mul_mode_mem W hn hN hx hy hz) := by
  by_cases hn' : n ≤ p + q
  · by_cases hN' : n + 1 ≤ N + M
    · rw [liGradedClass_mode W p q N M n hn' hN', liGradedClass_mul]
      exact liGradedClass_reindex W (by omega) (by omega) _ _
    · rw [liGradedClass_mode_eq_zero W p q N M n (Or.inr hN'), mul_zero]
      have hzero := smul_eq_zero_of_conformal_lt W hx.2 hy.2 hN'
      simp only [hzero, PreVertexAlgebra.smul_zero_right]
      exact (liGradedClass_zero W _ _).symm
  · rw [liGradedClass_mode_eq_zero W p q N M n (Or.inl hn'), mul_zero]
    symm
    apply liGradedClass_eq_zero_of_mem
    refine ⟨?_, (liWeightPiece_mul_mode_mem W hn hN hx hy hz).2⟩
    have hxy : W.smul x (n : ℤ) y ∈ liFiltration W 0 := by
      rw [liFiltration_zero_eq_top]
      trivial
    have hprod := liFiltration_smul_neg_one_mem W hz.1 hxy
    exact liFiltration_antitone W (by omega) hprod

/-- Equality of a homogeneous class with a sum from a one-step filtration defect. -/
theorem liGradedClass_eq_add_of_defect (W : VertexOperatorAlgebra V) (p N : ℕ)
    (x y z : V) (hx : x ∈ liWeightPiece W p N)
    (hy : y ∈ liWeightPiece W p N) (hz : z ∈ liWeightPiece W p N)
    (hdef : x - y - z ∈ liFiltration W (p + 1)) :
    liGradedClass W p N x hx = liGradedClass W p N y hy + liGradedClass W p N z hz := by
  rw [← liGradedClass_add]
  unfold liGradedClass
  apply congrArg (DirectSum.lof ℂ (ℕ × ℕ)
    (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2) (p, N))
  apply (Submodule.Quotient.eq _).mpr
  change x - (y + z) ∈ liWeightPiece W (p + 1) N
  refine ⟨?_, (W.grading N).sub_mem hx.2 ((W.grading N).add_mem hy.2 hz.2)⟩
  simpa only [sub_sub] using hdef

/-- The Leibniz rule for every mode on homogeneous classes. -/
theorem liGradedClass_mode_leibniz (W : VertexOperatorAlgebra V)
    (p q r N M L n : ℕ) (x y z : V)
    (hx : x ∈ liWeightPiece W p N) (hy : y ∈ liWeightPiece W q M)
    (hz : z ∈ liWeightPiece W r L) :
    liAssociatedGradedMode W n (liGradedClass W p N x hx)
        (liGradedClass W q M y hy * liGradedClass W r L z hz) =
      liAssociatedGradedMode W n (liGradedClass W p N x hx) (liGradedClass W q M y hy) *
          liGradedClass W r L z hz +
        liGradedClass W q M y hy *
          liAssociatedGradedMode W n (liGradedClass W p N x hx) (liGradedClass W r L z hz) := by
  rw [liGradedClass_mul]
  by_cases hn : n ≤ p + q + r
  · by_cases hN : n + 1 ≤ N + M + L
    · rw [liGradedClass_mode W p (q + r) N (M + L) n (by omega) (by omega),
        liGradedClass_mode_mul W p q r N M L n hn hN,
        liGradedClass_mul_mode W p r q N L M n (by omega) (by omega)]
      have hl := liWeightPiece_smul_nonneg_mem W
        (show n ≤ p + (q + r) by omega) (show n + 1 ≤ N + (M + L) by omega)
        hx (liWeightPiece_smul_neg_one_mem W hy hz)
      have hl' : W.smul x (n : ℤ) (W.smul y (-1) z) ∈
          liWeightPiece W (p + q + r - n) (N + M + L - (n + 1)) := by
        simpa only [Nat.add_assoc] using hl
      have hr := liWeightPiece_mul_mode_mem W
        (show n ≤ p + r + q by omega) (show n + 1 ≤ N + L + M by omega) hx hz hy
      have hr' : W.smul y (-1) (W.smul x (n : ℤ) z) ∈
          liWeightPiece W (p + q + r - n) (N + M + L - (n + 1)) := by
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hr
      rw [liGradedClass_reindex W (show p + (q + r) - n = p + q + r - n by omega)
        (show N + (M + L) - (n + 1) = N + M + L - (n + 1) by omega) hl hl',
        liGradedClass_reindex W (show p + r + q - n = p + q + r - n by omega)
        (show N + L + M - (n + 1) = N + M + L - (n + 1) by omega) hr hr']
      apply liGradedClass_eq_add_of_defect
      exact liFiltration_mode_leibniz_defect W hn hx.1 hy.1 hz.1
    · rw [liGradedClass_mode_eq_zero W p (q + r) N (M + L) n (Or.inr (by omega)),
        liGradedClass_mode_eq_zero W p q N M n (Or.inr (by omega)),
        liGradedClass_mode_eq_zero W p r N L n (Or.inr (by omega))]
      simp
  · rw [liGradedClass_mode_eq_zero W p (q + r) N (M + L) n (Or.inl (by omega)),
      liGradedClass_mode_eq_zero W p q N M n (Or.inl (by omega)),
      liGradedClass_mode_eq_zero W p r N L n (Or.inl (by omega))]
    simp

/-- Every nonnegative mode is a derivation of the Li graded commutative multiplication. -/
theorem liAssociatedGradedMode_leibniz (W : VertexOperatorAlgebra V)
    (n : ℕ) (x y z : liAssociatedGraded W) :
    liAssociatedGradedMode W n x (y * z) =
      liAssociatedGradedMode W n x y * z + y * liAssociatedGradedMode W n x z := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of d x =>
      induction y using DirectSum.induction_on with
      | zero => simp
      | of e y =>
          induction z using DirectSum.induction_on with
          | zero => simp
          | of f z =>
              refine Submodule.Quotient.induction_on _ x fun x => ?_
              refine Submodule.Quotient.induction_on _ y fun y => ?_
              refine Submodule.Quotient.induction_on _ z fun z => ?_
              exact liGradedClass_mode_leibniz W d.1 e.1 f.1 d.2 e.2 f.2 n
                x.1 y.1 z.1 x.2 y.2 z.2
          | add z t hz ht =>
              simp only [mul_add, map_add, hz, ht]
              ring
      | add y t hy ht =>
          simp only [add_mul, map_add, hy, ht]
          ring
  | add x t hx ht =>
      simp only [map_add, LinearMap.add_apply, hx, ht]
      ring

/-- The polynomial lambda bracket satisfies the Poisson vertex Leibniz identity. -/
theorem liLambdaBracket_leibniz (W : VertexOperatorAlgebra V)
    (x y z : liAssociatedGraded W) :
    liLambdaBracket W x (y * z) =
      liLambdaBracket W x y * Polynomial.C z + Polynomial.C y * liLambdaBracket W x z := by
  apply Polynomial.ext
  intro n
  simp only [Polynomial.coeff_add, Polynomial.coeff_mul_C, Polynomial.coeff_C_mul,
    coeff_liLambdaBracket, liAssociatedGradedMode_leibniz, smul_add,
    smul_mul_assoc, mul_smul_comm]

end VOA
