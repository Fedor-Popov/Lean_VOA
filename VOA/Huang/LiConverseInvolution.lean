import VOA.Huang.LiRegularOpp
import VOA.Huang.BraidingSkew

/-! # The opposite of the opposite vertex operator

For an ordinary module and a homogeneous state `u` of weight `K`, the twist
`e^{xL(1)}(−x⁻²)^{L(0)}` is an involution, so the ordinary modes are recovered from the opposite
modes by the same formula that defines the opposite modes from the ordinary ones:

  `mode_eq_oppB_twist`: `uₙ = (−1)^K Σⱼ (1/j!) (L(1)ʲu)°_{2K − n − 2 − j}`.

No `sorry`, no axioms beyond Lean's.
-/

namespace VOA.Huang.LiRegular

open VOA VOA.VertexOperatorAlgebra
open scoped BigOperators

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {M : Type u} [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M)

/-- **`(Y°)° = Y`** in modes. -/
theorem mode_eq_oppB_twist {k : ℤ} {u : V} (hu : u ∈ W.grading k) (n : ℤ) :
    mode (N.YM u) n = (-1 : ℂ) ^ k • ∑ j ∈ Finset.range (k.toNat + 1),
      ((j.factorial : ℂ)⁻¹) • oppB N ((W.L 1 ^ j) u) (2 * k - n - 2 - (j : ℤ)) := by
  rcases lt_or_ge k 0 with hk | hk
  · have hu0 : u = 0 := by
      have := VOA.VertexOperatorAlgebra.L_one_pow_eq_zero W hu (j := 0) (by omega)
      simpa using this
    subst hu0; simp; rfl
  obtain ⟨K, rfl⟩ : ∃ K : ℕ, k = K := ⟨k.toNat, (Int.toNat_of_nonneg hk).symm⟩
  simp only [Int.toNat_natCast]
  have hterm : ∀ j ∈ Finset.range (K + 1),
      (-1 : ℂ) ^ (K : ℤ) • (((j.factorial : ℂ)⁻¹) •
        oppB N ((W.L 1 ^ j) u) (2 * (K : ℤ) - n - 2 - (j : ℤ)))
      = ∑ i ∈ Finset.range (K - j + 1),
          ((-1 : ℂ) ^ j * ((j.factorial : ℂ)⁻¹ * (i.factorial : ℂ)⁻¹)) •
            mode (N.YM ((W.L 1 ^ (i + j)) u)) (n - ((i + j : ℕ) : ℤ)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hmem : (W.L 1 ^ j) u ∈ W.grading ((K - j : ℕ) : ℤ) := by
      have := L_one_pow_mem W hu j
      rwa [show ((K : ℤ) - (j : ℤ)) = ((K - j : ℕ) : ℤ) by omega] at this
    rw [oppB_homog N hmem, Int.toNat_natCast]
    simp only [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, smul_smul, smul_smul, ← Module.End.mul_apply, ← pow_add,
      show 2 * ((K - j : ℕ) : ℤ) - (2 * (K : ℤ) - n - 2 - (j : ℤ)) - 2 - (i : ℤ)
        = n - ((i + j : ℕ) : ℤ) by push_cast [Nat.cast_sub (by omega : j ≤ K)]; ring]
    congr 1
    rw [zpow_natCast, zpow_natCast]
    have hsign : (-1 : ℂ) ^ K * (-1 : ℂ) ^ (K - j) = (-1 : ℂ) ^ j := by
      rw [← pow_add, show K + (K - j) = 2 * (K - j) + j by omega, pow_add, pow_mul]
      norm_num
    linear_combination ((j.factorial : ℂ)⁻¹ * (i.factorial : ℂ)⁻¹) * hsign
  rw [Finset.smul_sum, Finset.sum_congr rfl hterm]
  have := VOA.Huang.BraidingSkew.triangle_sum K
    (fun r => mode (N.YM ((W.L 1 ^ r) u)) (n - (r : ℤ)))
  simpa using this.symm

end VOA.Huang.LiRegular
