import VOA.Huang.DLNBridge
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# The elementary character and determinant part of DLN lifting

Every character of `SL₂(ℤ)` into a commutative group has exponent dividing 12.
This is an exponent statement, not a proof that the character kills `Γ(12)`.
For a projectively congruent matrix representation it bounds each scalar on
`Γ(N)` by `12 * Fintype.card κ`, without cancelling the dimension.
-/

namespace VOA.Huang.DLNLifting

open VOA.Huang.DLN VOA.Huang.DLNBridge

private theorem S_four : ModularGroup.S ^ 4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.S, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

private theorem ST_three : (ModularGroup.S * ModularGroup.T) ^ 3 = ModularGroup.S ^ 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.S, ModularGroup.T, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Every character into a commutative group has exponent dividing 12. -/
theorem character_pow_twelve {A : Type*} [CommGroup A] (χ : SL2Z →* A) (γ : SL2Z) :
    χ γ ^ 12 = 1 := by
  have hS : χ ModularGroup.S ^ 4 = 1 := by rw [← map_pow, S_four, map_one]
  have hST : χ ModularGroup.S * χ ModularGroup.T ^ 3 = 1 := by
    have h := congrArg χ ST_three
    simp only [map_pow, map_mul, mul_pow] at h
    apply mul_left_cancel (a := χ ModularGroup.S ^ 2)
    calc
      χ ModularGroup.S ^ 2 * (χ ModularGroup.S * χ ModularGroup.T ^ 3) =
          χ ModularGroup.S ^ 3 * χ ModularGroup.T ^ 3 := by
            rw [← mul_assoc, ← pow_succ]
      _ = χ ModularGroup.S ^ 2 * 1 := by simpa using h
  have hT : χ ModularGroup.T ^ 12 = 1 := by
    have h := congrArg (fun a : A => a ^ 4) hST
    simpa only [mul_pow, hS, one_mul, ← pow_mul, one_pow] using h
  have hγ : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]
    exact Subgroup.mem_top γ
  induction hγ using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · calc
        χ ModularGroup.S ^ 12 = (χ ModularGroup.S ^ 4) ^ 3 := by rw [← pow_mul]
        _ = 1 := by rw [hS, one_pow]
    · exact hT
  | one => simp
  | mul x y _ _ hx hy => simp [map_mul, mul_pow, hx, hy]
  | inv x _ hx => simp [map_inv, inv_pow, hx]

/-- Equivalently, the order of every character value divides 12. -/
theorem character_orderOf_dvd_twelve {A : Type*} [CommGroup A]
    (χ : SL2Z →* A) (γ : SL2Z) : orderOf (χ γ) ∣ 12 :=
  orderOf_dvd_of_pow_eq_one (character_pow_twelve χ γ)

/-- The determinant of any matrix representation is a character of exponent dividing 12. -/
theorem det_pow_twelve {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : SL2Z →* Matrix κ κ ℂ) (γ : SL2Z) : (Matrix.det (ρ γ)) ^ 12 = 1 := by
  have h := character_pow_twelve (Matrix.detMonoidHom.comp ρ).toHomUnits γ
  exact congrArg (fun a : ℂˣ => (a : ℂ)) h

/-- The determinant bound on a scalar value, valid also in dimension zero. -/
theorem scalar_pow_card_mul_twelve {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : SL2Z →* Matrix κ κ ℂ) (γ : SL2Z) {c : ℂ}
    (hc : ρ γ = c • (1 : Matrix κ κ ℂ)) : c ^ (Fintype.card κ * 12) = 1 := by
  have h := det_pow_twelve ρ γ
  simpa [hc, Matrix.det_smul, ← pow_mul] using h

/-- A dimension-dependent power of every matrix on the projective kernel is the identity. -/
theorem projective_pow_card_mul_twelve {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : SL2Z →* Matrix κ κ ℂ) {N : ℕ} (hp : MatrixProjectiveCongruence ρ N)
    (γ : SL2Z) (hγ : γ ∈ CongruenceSubgroup.Gamma N) :
    ρ γ ^ (Fintype.card κ * 12) = 1 := by
  obtain ⟨c, hc⟩ := hp γ hγ
  rw [hc, smul_pow, one_pow, scalar_pow_card_mul_twelve ρ γ hc, one_smul]

/-- Empty matrix index sets have trivial representations, at every level. -/
theorem kernelContainsGamma_of_isEmpty {κ : Type*} [Fintype κ] [DecidableEq κ] [IsEmpty κ]
    (ρ : SL2Z →* Matrix κ κ ℂ) (N : ℕ) : KernelContainsGamma ρ N := by
  intro γ _
  exact Subsingleton.elim _ _

/-- Projective congruence bounds the order of `ρ(T)` by a dimension-dependent multiple of `N`.
The exponent is positive when both `N` and the dimension are positive. -/
theorem projective_T_pow {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : SL2Z →* Matrix κ κ ℂ) {N : ℕ} (hp : MatrixProjectiveCongruence ρ N) :
    ρ ModularGroup.T ^ (N * (Fintype.card κ * 12)) = 1 := by
  have hmem : ModularGroup.T ^ N ∈ CongruenceSubgroup.Gamma N := by
    simpa only [zpow_natCast] using NSFinish.T_pow_mem_Gamma N
  have h := projective_pow_card_mul_twelve ρ hp (ModularGroup.T ^ N) hmem
  simpa only [map_pow, ← pow_mul] using h

/-- Finite order of `ρ(T)` follows without assuming genuine congruence in advance. -/
theorem projective_T_isOfFinOrder {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : SL2Z →* Matrix κ κ ℂ) {N : ℕ} (hN : 0 < N)
    (hp : MatrixProjectiveCongruence ρ N) : IsOfFinOrder (ρ ModularGroup.T) := by
  cases isEmpty_or_nonempty κ with
  | inl h =>
    have he : ρ ModularGroup.T = 1 := Subsingleton.elim _ _
    rw [he]
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨1, by norm_num, one_pow 1⟩
  | inr h =>
    exact isOfFinOrder_iff_pow_eq_one.mpr
      ⟨N * (Fintype.card κ * 12),
        Nat.mul_pos hN (Nat.mul_pos Fintype.card_pos (by norm_num)), projective_T_pow ρ hp⟩

/-- Once genuine congruence is separately known, Wohlfahrt's lemma turns the elementary
power bound into a congruence level. The existence of that genuine congruence is an explicit
hypothesis; finite order of `ρ(T)` alone does not supply it. -/
theorem kernel_dimension_bound_of_congruence {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : SL2Z →* Matrix κ κ ℂ) {N L : ℕ} (hp : MatrixProjectiveCongruence ρ N)
    (hL : 0 < L) (hk : KernelContainsGamma ρ L) :
    KernelContainsGamma ρ (N * (Fintype.card κ * 12)) :=
  (congruenceAtOrder_of_kernel ρ hL hk).at_level (projective_T_pow ρ hp)

end VOA.Huang.DLNLifting
