import VOA.Filtered.LiGradedNestedModes

/-!
# Jacobi identity for the actual Li graded modes

The fixed finite VOA commutator identity descends through both nested mode
operations, including all vanishing intermediate and total degree cases.
-/

namespace VOA
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Jacobi for homogeneous Li classes in the standard nonnegative-mode form. -/
theorem liGradedClass_mode_jacobi (W : VertexOperatorAlgebra V)
    (p q r N M L m n : ℕ) (x y z : V)
    (hx : x ∈ liWeightPiece W p N) (hy : y ∈ liWeightPiece W q M)
    (hz : z ∈ liWeightPiece W r L) :
    liAssociatedGradedMode W m (liGradedClass W p N x hx)
        (liAssociatedGradedMode W n (liGradedClass W q M y hy) (liGradedClass W r L z hz)) -
      liAssociatedGradedMode W n (liGradedClass W q M y hy)
        (liAssociatedGradedMode W m (liGradedClass W p N x hx) (liGradedClass W r L z hz)) =
      ∑ j : Fin (m + 1), (m.choose j.val : ℂ) •
        liAssociatedGradedMode W (m + n - j.val)
          (liAssociatedGradedMode W j.val (liGradedClass W p N x hx)
            (liGradedClass W q M y hy)) (liGradedClass W r L z hz) := by
  by_cases hn : m + n ≤ p + q + r
  · by_cases hN : m + n + 2 ≤ N + M + L
    · have hA := liWeightPiece_mode_nested_mem W
        (show n + m ≤ q + r + p by omega) (show n + m + 2 ≤ M + L + N by omega) hy hz hx
      have hB := liWeightPiece_mode_nested_mem W
        (show m + n ≤ p + r + q by omega) (show m + n + 2 ≤ N + L + M by omega) hx hz hy
      have hA' : W.smul x (m : ℤ) (W.smul y (n : ℤ) z) ∈
          liWeightPiece W (p + q + r - (m + n)) (N + M + L - (m + n + 2)) := by
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hA
      have hB' : W.smul y (n : ℤ) (W.smul x (m : ℤ) z) ∈
          liWeightPiece W (p + q + r - (m + n)) (N + M + L - (m + n + 2)) := by
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hB
      let A : liWeightPiece W (p + q + r - (m + n)) (N + M + L - (m + n + 2)) :=
        ⟨W.smul x (m : ℤ) (W.smul y (n : ℤ) z), hA'⟩
      let B : liWeightPiece W (p + q + r - (m + n)) (N + M + L - (m + n + 2)) :=
        ⟨W.smul y (n : ℤ) (W.smul x (m : ℤ) z), hB'⟩
      have hF : ∀ j : Fin (m + 1), W.smul (W.smul x (j.val : ℤ) y)
          ((m + n - j.val : ℕ) : ℤ) z ∈
          liWeightPiece W (p + q + r - (m + n)) (N + M + L - (m + n + 2)) := by
        intro j
        have hj : j.val + (m + n - j.val) = m + n := by omega
        have h := liWeightPiece_mode_mode_mem W
          (show j.val + (m + n - j.val) ≤ p + q + r by omega)
          (show j.val + (m + n - j.val) + 2 ≤ N + M + L by omega) hx hy hz
        simpa only [hj] using h
      let F (j : Fin (m + 1)) :
          liWeightPiece W (p + q + r - (m + n)) (N + M + L - (m + n + 2)) :=
        ⟨W.smul (W.smul x (j.val : ℤ) y) ((m + n - j.val : ℕ) : ℤ) z, hF j⟩
      let π : liWeightPiece W (p + q + r - (m + n)) (N + M + L - (m + n + 2)) →ₗ[ℂ]
          liAssociatedGraded W :=
        (DirectSum.lof ℂ (ℕ × ℕ) (fun d : ℕ × ℕ => liWeightLayer W d.1 d.2)
          (p + q + r - (m + n), N + M + L - (m + n + 2))).comp
          (((liWeightPiece W (p + q + r - (m + n) + 1) (N + M + L - (m + n + 2))).comap
            (liWeightPiece W (p + q + r - (m + n)) (N + M + L - (m + n + 2))).subtype).mkQ)
      have hrep : A - B = ∑ j : Fin (m + 1), (m.choose j.val : ℂ) • F j := by
        apply Subtype.ext
        simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul]
        change W.smul x (m : ℤ) (W.smul y (n : ℤ) z) -
          W.smul y (n : ℤ) (W.smul x (m : ℤ) z) =
          ∑ j : Fin (m + 1), (m.choose j.val : ℂ) •
            W.smul (W.smul x (j.val : ℤ) y) ((m + n - j.val : ℕ) : ℤ) z
        rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (m.choose j : ℂ) •
          W.smul (W.smul x (j : ℤ) y) ((m + n - j : ℕ) : ℤ) z) (m + 1)]
        exact smul_nonneg_commutator W m n x y z
      have heA : liAssociatedGradedMode W m (liGradedClass W p N x hx)
          (liAssociatedGradedMode W n (liGradedClass W q M y hy) (liGradedClass W r L z hz)) =
          π A := by
        rw [liGradedClass_mode_nested W q r p M L N m n (by omega) (by omega)]
        exact liGradedClass_reindex W (by omega) (by omega) _ _
      have heB : liAssociatedGradedMode W n (liGradedClass W q M y hy)
          (liAssociatedGradedMode W m (liGradedClass W p N x hx) (liGradedClass W r L z hz)) =
          π B := by
        rw [liGradedClass_mode_nested W p r q N L M n m (by omega) (by omega)]
        exact liGradedClass_reindex W (by omega) (by omega) _ _
      have heF (j : Fin (m + 1)) : liAssociatedGradedMode W (m + n - j.val)
          (liAssociatedGradedMode W j.val (liGradedClass W p N x hx)
            (liGradedClass W q M y hy)) (liGradedClass W r L z hz) = π (F j) := by
        rw [liGradedClass_mode_mode W p q r N M L (m + n - j.val) j.val
          (by omega) (by omega)]
        exact liGradedClass_reindex W (by omega) (by omega) _ _
      rw [heA, heB]
      simp_rw [heF]
      simpa only [map_sub, map_sum, map_smul] using congrArg π hrep
    · rw [liGradedClass_mode_nested_eq_zero W q r p M L N m n (Or.inr (by omega)),
        liGradedClass_mode_nested_eq_zero W p r q N L M n m (Or.inr (by omega)), sub_self]
      symm
      apply Finset.sum_eq_zero
      intro j _
      rw [liGradedClass_mode_mode_eq_zero W p q r N M L (m + n - j.val) j.val
        (Or.inr (by omega)), smul_zero]
  · rw [liGradedClass_mode_nested_eq_zero W q r p M L N m n (Or.inl (by omega)),
      liGradedClass_mode_nested_eq_zero W p r q N L M n m (Or.inl (by omega)), sub_self]
    symm
    apply Finset.sum_eq_zero
    intro j _
    rw [liGradedClass_mode_mode_eq_zero W p q r N M L (m + n - j.val) j.val
      (Or.inl (by omega)), smul_zero]

/-- The Jacobi identity for all nonnegative modes on the complete Li associated graded. -/
theorem liAssociatedGradedMode_jacobi (W : VertexOperatorAlgebra V)
    (m n : ℕ) (x y z : liAssociatedGraded W) :
    liAssociatedGradedMode W m x (liAssociatedGradedMode W n y z) -
        liAssociatedGradedMode W n y (liAssociatedGradedMode W m x z) =
      ∑ j : Fin (m + 1), (m.choose j.val : ℂ) •
        liAssociatedGradedMode W (m + n - j.val) (liAssociatedGradedMode W j.val x y) z := by
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
              exact liGradedClass_mode_jacobi W d.1 e.1 f.1 d.2 e.2 f.2 m n
                x.1 y.1 z.1 x.2 y.2 z.2
          | add z t hz ht =>
              simp only [map_add, smul_add, Finset.sum_add_distrib]
              rw [← hz, ← ht]
              abel
      | add y t hy ht =>
          simp only [map_add, LinearMap.add_apply, smul_add, Finset.sum_add_distrib]
          rw [← hy, ← ht]
          abel
  | add x t hx ht =>
      simp only [map_add, LinearMap.add_apply, smul_add, Finset.sum_add_distrib]
      rw [← hx, ← ht]
      abel

end VOA
