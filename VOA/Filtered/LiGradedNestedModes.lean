import VOA.Filtered.LiModeJacobi

/-!
# Nested vertex modes on Li classes

A nested mode is represented in its total bidegree even when the formal
intermediate Li degree is negative: the actual term then lies one step higher
and vanishes in that total associated-graded piece.
-/

namespace VOA
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Total-bidegree membership of a left-nested pair of nonnegative modes. -/
theorem liWeightPiece_mode_mode_mem (W : VertexOperatorAlgebra V)
    {p q r N M L m n : ℕ} (hn : n + m ≤ p + q + r)
    (hN : n + m + 2 ≤ N + M + L) {x y z : V}
    (hx : x ∈ liWeightPiece W p N) (hy : y ∈ liWeightPiece W q M)
    (hz : z ∈ liWeightPiece W r L) :
    W.smul (W.smul x (n : ℤ) y) (m : ℤ) z ∈
      liWeightPiece W (p + q + r - (n + m)) (N + M + L - (n + m + 2)) := by
  refine ⟨?_, ?_⟩
  · have hxy := adjointGfil_smul_nonneg_mem W n hx.1 hy.1
    have hprod := adjointGfil_smul_nonneg_mem W m hxy hz.1
    change W.smul (W.smul x (n : ℤ) y) (m : ℤ) z ∈
      Gfil (adjointWeakModule W) ({W.vacuum} : Set V)
        ((p : ℤ) + q - n + r - m) at hprod
    change W.smul (W.smul x (n : ℤ) y) (m : ℤ) z ∈
      Gfil (adjointWeakModule W) ({W.vacuum} : Set V)
        ((p + q + r - (n + m) : ℕ) : ℤ)
    have heq : ((p + q + r - (n + m) : ℕ) : ℤ) =
        (p : ℤ) + q - n + r - m := by
      rw [Nat.cast_sub hn, Nat.cast_add, Nat.cast_add, Nat.cast_add]
      ring
    rw [heq]
    exact hprod
  · have hgr := W.smul_mem_grading (W.smul_mem_grading hx.2 hy.2 (n : ℤ)) hz.2 (m : ℤ)
    have heq : ((N + M + L - (n + m + 2) : ℕ) : ℤ) =
        ((N : ℤ) + M - n - 1) + L - m - 1 := by
      rw [Nat.cast_sub hN]
      push_cast
      ring
    simpa only [heq] using hgr

/-- A left-nested pair of descended modes agrees with its total-bidegree state class. -/
theorem liGradedClass_mode_mode (W : VertexOperatorAlgebra V)
    (p q r N M L m n : ℕ) (hn : n + m ≤ p + q + r)
    (hN : n + m + 2 ≤ N + M + L) (x y z : V)
    (hx : x ∈ liWeightPiece W p N) (hy : y ∈ liWeightPiece W q M)
    (hz : z ∈ liWeightPiece W r L) :
    liAssociatedGradedMode W m
        (liAssociatedGradedMode W n (liGradedClass W p N x hx) (liGradedClass W q M y hy))
        (liGradedClass W r L z hz) =
      liGradedClass W (p + q + r - (n + m)) (N + M + L - (n + m + 2))
        (W.smul (W.smul x (n : ℤ) y) (m : ℤ) z)
        (liWeightPiece_mode_mode_mem W hn hN hx hy hz) := by
  by_cases hn' : n ≤ p + q
  · by_cases hN' : n + 1 ≤ N + M
    · rw [liGradedClass_mode W p q N M n hn' hN',
        liGradedClass_mode W (p + q - n) r (N + M - (n + 1)) L m (by omega) (by omega)]
      exact liGradedClass_reindex W (by omega) (by omega) _ _
    · rw [liGradedClass_mode_eq_zero W p q N M n (Or.inr hN')]
      simp only [map_zero, LinearMap.zero_apply]
      have hzero := smul_eq_zero_of_conformal_lt W hx.2 hy.2 hN'
      simp only [hzero, PreVertexAlgebra.smul_zero_left]
      exact (liGradedClass_zero W _ _).symm
  · rw [liGradedClass_mode_eq_zero W p q N M n (Or.inl hn')]
    simp only [map_zero, LinearMap.zero_apply]
    symm
    apply liGradedClass_eq_zero_of_mem
    refine ⟨?_, (liWeightPiece_mode_mode_mem W hn hN hx hy hz).2⟩
    have hxy : W.smul x (n : ℤ) y ∈ liFiltration W 0 := by
      rw [liFiltration_zero_eq_top]
      trivial
    have hprod := liFiltration_smul_nonneg_mem W (show m ≤ 0 + r by omega) hxy hz.1
    exact liFiltration_antitone W (by omega) hprod

/-- A left-nested pair vanishes when either of its total output degrees is negative. -/
theorem liGradedClass_mode_mode_eq_zero (W : VertexOperatorAlgebra V)
    (p q r N M L m n : ℕ)
    (h : ¬ n + m ≤ p + q + r ∨ ¬ n + m + 2 ≤ N + M + L)
    (x y z : V) (hx : x ∈ liWeightPiece W p N)
    (hy : y ∈ liWeightPiece W q M) (hz : z ∈ liWeightPiece W r L) :
    liAssociatedGradedMode W m
        (liAssociatedGradedMode W n (liGradedClass W p N x hx) (liGradedClass W q M y hy))
        (liGradedClass W r L z hz) = 0 := by
  by_cases hn : n ≤ p + q
  · by_cases hN : n + 1 ≤ N + M
    · rw [liGradedClass_mode W p q N M n hn hN]
      apply liGradedClass_mode_eq_zero
      rcases h with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    · rw [liGradedClass_mode_eq_zero W p q N M n (Or.inr hN)]
      simp
  · rw [liGradedClass_mode_eq_zero W p q N M n (Or.inl hn)]
    simp

/-- Total-bidegree membership of a right-nested pair of nonnegative modes. -/
theorem liWeightPiece_mode_nested_mem (W : VertexOperatorAlgebra V)
    {p q r N M L m n : ℕ} (hn : n + m ≤ p + q + r)
    (hN : n + m + 2 ≤ N + M + L) {x y z : V}
    (hx : x ∈ liWeightPiece W p N) (hy : y ∈ liWeightPiece W q M)
    (hz : z ∈ liWeightPiece W r L) :
    W.smul z (m : ℤ) (W.smul x (n : ℤ) y) ∈
      liWeightPiece W (p + q + r - (n + m)) (N + M + L - (n + m + 2)) := by
  refine ⟨?_, ?_⟩
  · have hxy := adjointGfil_smul_nonneg_mem W n hx.1 hy.1
    have hprod := adjointGfil_smul_nonneg_mem W m hz.1 hxy
    change W.smul z (m : ℤ) (W.smul x (n : ℤ) y) ∈
      Gfil (adjointWeakModule W) ({W.vacuum} : Set V)
        ((r : ℤ) + ((p : ℤ) + q - n) - m) at hprod
    change W.smul z (m : ℤ) (W.smul x (n : ℤ) y) ∈
      Gfil (adjointWeakModule W) ({W.vacuum} : Set V)
        ((p + q + r - (n + m) : ℕ) : ℤ)
    have heq : ((p + q + r - (n + m) : ℕ) : ℤ) =
        (r : ℤ) + ((p : ℤ) + q - n) - m := by
      rw [Nat.cast_sub hn, Nat.cast_add, Nat.cast_add, Nat.cast_add]
      ring
    rw [heq]
    exact hprod
  · have hgr := W.smul_mem_grading hz.2 (W.smul_mem_grading hx.2 hy.2 (n : ℤ)) (m : ℤ)
    have heq : ((N + M + L - (n + m + 2) : ℕ) : ℤ) =
        (L : ℤ) + ((N : ℤ) + M - n - 1) - m - 1 := by
      rw [Nat.cast_sub hN]
      push_cast
      ring
    simpa only [heq] using hgr

/-- A right-nested pair of descended modes agrees with its total-bidegree state class. -/
theorem liGradedClass_mode_nested (W : VertexOperatorAlgebra V)
    (p q r N M L m n : ℕ) (hn : n + m ≤ p + q + r)
    (hN : n + m + 2 ≤ N + M + L) (x y z : V)
    (hx : x ∈ liWeightPiece W p N) (hy : y ∈ liWeightPiece W q M)
    (hz : z ∈ liWeightPiece W r L) :
    liAssociatedGradedMode W m (liGradedClass W r L z hz)
        (liAssociatedGradedMode W n (liGradedClass W p N x hx) (liGradedClass W q M y hy)) =
      liGradedClass W (p + q + r - (n + m)) (N + M + L - (n + m + 2))
        (W.smul z (m : ℤ) (W.smul x (n : ℤ) y))
        (liWeightPiece_mode_nested_mem W hn hN hx hy hz) := by
  by_cases hn' : n ≤ p + q
  · by_cases hN' : n + 1 ≤ N + M
    · rw [liGradedClass_mode W p q N M n hn' hN',
        liGradedClass_mode W r (p + q - n) L (N + M - (n + 1)) m (by omega) (by omega)]
      exact liGradedClass_reindex W (by omega) (by omega) _ _
    · rw [liGradedClass_mode_eq_zero W p q N M n (Or.inr hN')]
      simp only [map_zero, LinearMap.zero_apply]
      have hzero := smul_eq_zero_of_conformal_lt W hx.2 hy.2 hN'
      simp only [hzero, PreVertexAlgebra.smul_zero_right]
      exact (liGradedClass_zero W _ _).symm
  · rw [liGradedClass_mode_eq_zero W p q N M n (Or.inl hn')]
    simp only [map_zero, LinearMap.zero_apply]
    symm
    apply liGradedClass_eq_zero_of_mem
    refine ⟨?_, (liWeightPiece_mode_nested_mem W hn hN hx hy hz).2⟩
    have hxy : W.smul x (n : ℤ) y ∈ liFiltration W 0 := by
      rw [liFiltration_zero_eq_top]
      trivial
    have hprod := liFiltration_smul_nonneg_mem W (show m ≤ r + 0 by omega) hz.1 hxy
    exact liFiltration_antitone W (by omega) hprod

/-- A right-nested pair vanishes when either of its total output degrees is negative. -/
theorem liGradedClass_mode_nested_eq_zero (W : VertexOperatorAlgebra V)
    (p q r N M L m n : ℕ)
    (h : ¬ n + m ≤ p + q + r ∨ ¬ n + m + 2 ≤ N + M + L)
    (x y z : V) (hx : x ∈ liWeightPiece W p N)
    (hy : y ∈ liWeightPiece W q M) (hz : z ∈ liWeightPiece W r L) :
    liAssociatedGradedMode W m (liGradedClass W r L z hz)
        (liAssociatedGradedMode W n (liGradedClass W p N x hx) (liGradedClass W q M y hy)) = 0 := by
  by_cases hn : n ≤ p + q
  · by_cases hN : n + 1 ≤ N + M
    · rw [liGradedClass_mode W p q N M n hn hN]
      apply liGradedClass_mode_eq_zero
      rcases h with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    · rw [liGradedClass_mode_eq_zero W p q N M n (Or.inr hN)]
      simp
  · rw [liGradedClass_mode_eq_zero W p q N M n (Or.inl hn)]
    simp


end VOA
