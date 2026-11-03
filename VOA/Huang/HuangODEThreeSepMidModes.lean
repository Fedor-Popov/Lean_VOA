import VOA.Huang.HuangODEThreeSepMidBase

/-!
# The five slot relations for the middle (iterate-in-product) shape

Finite mode identities for `f(𝒴₁(w₁)_p 𝒴_B(𝒴₃(w₃)_r w₄)_q w₂)`, moving a VOA mode between the
four vector slots and the output functional (commutator, iterate and `u₋₁`-iterate formulas).
Slot names follow the product convention: `w₁` outer insertion, `w₂` terminal, `w₃` the
first argument of the inner intertwiner, `w₄` its second argument.
-/

noncomputable section
namespace VOA.Huang.FivePointSep
open VOA VOA.Huang.HuangODEModes
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₀ M₁ M₂ M₃ M₄ M₅ M₆ : Type u}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup M₅] [Module ℂ M₅]
  [AddCommGroup M₆] [Module ℂ M₆]
variable {A₀ : OrdVModule W M₀} {A₁ : OrdVModule W M₁}
  {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃} {A₄ : OrdVModule W M₄}
  {A₅ : OrdVModule W M₅} {A₆ : OrdVModule W M₆}
variable {Y₁ : IntertwiningModes M₁ M₆ M₀} {YB : IntertwiningModes M₅ M₂ M₆}
  {Y₃ : IntertwiningModes M₃ M₄ M₅}
variable (hY₁ : IsIntertwiningOperator A₁ A₆ A₀ Y₁)
  (hYB : IsIntertwiningOperator A₅ A₂ A₆ YB) (hY₃ : IsIntertwiningOperator A₃ A₄ A₅ Y₃)

include hY₃ in
/-- `u_k` on the inner vector `𝒴₃(w₃)_r w₄`. -/
theorem mid_inner_comm (u : V) (w₃ : M₃) (w₄ : M₄) (r : ℂ) (k : ℤ) (K : ℕ)
    (hK₃ : ∀ l : ℤ, (K : ℤ) ≤ l → mode (A₃.YM u) l w₃ = 0) :
    mode (A₅.YM u) k (Y₃ r w₃ w₄) = Y₃ r w₃ (mode (A₄.YM u) k w₄)
      + ∑ l ∈ Finset.range K, cbz k l • Y₃ (k + r - l) (mode (A₃.YM u) l w₃) w₄ := by
  rw [comm_range hY₃ u w₃ w₄ k r K hK₃]; abel

include hY₁ hYB hY₃ in
/-- **Terminal slot** (`u₋₁ w₂`). -/
theorem mid_terminal_mode (u : V) (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    (p q r : ℂ) (K : ℕ) (hK₁ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₁.YM u) k w₁ = 0)
    (hK₃ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₃.YM u) k w₃ = 0)
    (hKV : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₅.YM u) k (Y₃ r w₃ w₄) = 0) :
    f (Y₁ p w₁ (YB q (Y₃ r w₃ w₄) (mode (A₂.YM u) (-1) w₂))) =
      f (mode (A₀.YM u) (-1) (Y₁ p w₁ (YB q (Y₃ r w₃ w₄) w₂)))
      - ∑ k ∈ Finset.range K, cbz (-1) k *
          f (Y₁ (-1 + p - k) (mode (A₁.YM u) k w₁) (YB q (Y₃ r w₃ w₄) w₂))
      - ∑ k ∈ Finset.range K, cbz (-1) k *
          (f (Y₁ p w₁ (YB (-1 + q - k) (Y₃ r w₃ (mode (A₄.YM u) k w₄)) w₂))
          + ∑ l ∈ Finset.range K, cbz k l *
            f (Y₁ p w₁ (YB (-1 + q - k) (Y₃ (k + r - l) (mode (A₃.YM u) l w₃) w₄) w₂))) := by
  have hin : ∀ k : ℤ, mode (A₅.YM u) k (Y₃ r w₃ w₄) = Y₃ r w₃ (mode (A₄.YM u) k w₄)
      + ∑ l ∈ Finset.range K, cbz k l • Y₃ (k + r - l) (mode (A₃.YM u) l w₃) w₄ :=
    fun k => mid_inner_comm hY₃ u w₃ w₄ r k K hK₃
  rw [comm_range hYB u (Y₃ r w₃ w₄) w₂ (-1) q K hKV, map_sub,
    comm_range hY₁ u w₁ _ (-1) p K hK₁]
  simp only [hin, map_sub, map_sum, map_smul, map_add, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  all_goals (push_cast; ring)

include hY₁ hYB hY₃ in
/-- **Second inner slot** (`u₋₁ w₄`). -/
theorem mid_four_mode (u : V) (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    (p q r : ℂ) (K I : ℕ) (hK₁ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₁.YM u) k w₁ = 0)
    (hK₃ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₃.YM u) k w₃ = 0)
    (hI : ∀ i : ℤ, (I : ℤ) ≤ i → YB (q + i) (Y₃ r w₃ w₄) w₂ = 0 ∧
      mode (A₂.YM u) i w₂ = 0) :
    f (Y₁ p w₁ (YB q (Y₃ r w₃ (mode (A₄.YM u) (-1) w₄)) w₂)) =
      ∑ i ∈ Finset.range I,
        (f (mode (A₀.YM u) (-1 - i) (Y₁ p w₁ (YB (q + i) (Y₃ r w₃ w₄) w₂)))
        - ∑ k ∈ Finset.range K, cbz (-1 - i) k *
          f (Y₁ ((-1 - i : ℤ) + p - k) (mode (A₁.YM u) k w₁) (YB (q + i) (Y₃ r w₃ w₄) w₂))
        + f (Y₁ p w₁ (YB (q - 1 - i) (Y₃ r w₃ w₄) (mode (A₂.YM u) i w₂))))
      - ∑ k ∈ Finset.range K, cbz (-1) k *
          f (Y₁ p w₁ (YB q (Y₃ (-1 + r - k) (mode (A₃.YM u) k w₃) w₄) w₂)) := by
  have hc : ∀ (i : ℕ) (X : M₆), f (Y₁ p w₁ (mode (A₆.YM u) (-1 - i) X)) =
      f (mode (A₀.YM u) (-1 - i) (Y₁ p w₁ X)) - ∑ k ∈ Finset.range K, cbz (-1 - i) k *
        f (Y₁ ((-1 - i : ℤ) + p - k) (mode (A₁.YM u) k w₁) X) := by
    intro i X
    rw [comm_range hY₁ u w₁ X (-1 - i) p K hK₁]
    simp only [map_sub, map_sum, map_smul, smul_eq_mul]
  rw [comm_range hY₃ u w₃ w₄ (-1) r K hK₃, map_sub, LinearMap.sub_apply,
    negOneLeft_range hYB u (Y₃ r w₃ w₄) w₂ q I hI]
  simp only [map_sub, map_sum, map_smul, map_add, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, hc]
  all_goals (push_cast; ring)

include hY₁ hYB hY₃ in
/-- **First inner slot** (`u₋₁ w₃`): a `u₋₁`-iterate, an iterate and a commutator. -/
theorem mid_three_mode (u : V) (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    (p q r : ℂ) (K I J : ℕ) (hK₁ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₁.YM u) k w₁ = 0)
    (hI : ∀ i : ℤ, (I : ℤ) ≤ i → Y₃ (r + i) w₃ w₄ = 0 ∧ mode (A₄.YM u) i w₄ = 0)
    (hJ : ∀ i : ℕ, i < I → ∀ j : ℤ, (J : ℤ) ≤ j → YB (q + j) (Y₃ (r + i) w₃ w₄) w₂ = 0 ∧
      mode (A₂.YM u) j w₂ = 0) :
    f (Y₁ p w₁ (YB q (Y₃ r (mode (A₃.YM u) (-1) w₃) w₄) w₂)) =
      ∑ i ∈ Finset.range I,
        (∑ j ∈ Finset.range J, (negOnePow j * cbz (-1 - i) j) *
          (f (mode (A₀.YM u) (-1 - i - j) (Y₁ p w₁ (YB (q + j) (Y₃ (r + i) w₃ w₄) w₂)))
          - ∑ k ∈ Finset.range K, cbz (-1 - i - j) k *
            f (Y₁ ((-1 - i - j : ℤ) + p - k) (mode (A₁.YM u) k w₁)
              (YB (q + j) (Y₃ (r + i) w₃ w₄) w₂))
          - negOnePow (-1 - i) *
            f (Y₁ p w₁ (YB ((-1 - i : ℤ) + q - j) (Y₃ (r + i) w₃ w₄) (mode (A₂.YM u) j w₂))))
        + f (Y₁ p w₁ (YB q (Y₃ (r - 1 - i) w₃ (mode (A₄.YM u) i w₄)) w₂))) := by
  have hc : ∀ (n : ℤ) (X : M₆), f (Y₁ p w₁ (mode (A₆.YM u) n X)) =
      f (mode (A₀.YM u) n (Y₁ p w₁ X)) - ∑ k ∈ Finset.range K, cbz n k *
        f (Y₁ (n + p - k) (mode (A₁.YM u) k w₁) X) := by
    intro n X
    rw [comm_range hY₁ u w₁ X n p K hK₁]
    simp only [map_sub, map_sum, map_smul, smul_eq_mul]
  rw [negOneLeft_range hY₃ u w₃ w₄ r I hI]
  simp only [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [map_add, LinearMap.add_apply, map_add, map_add,
    iterate_range hYB u (Y₃ (r + i) w₃ w₄) w₂ (-1 - i) q J (hJ i hi')]
  simp only [map_sub, map_sum, map_smul, smul_eq_mul, hc]


include hY₁ hYB hY₃ in
/-- **Outer slot** (`u₋₁ w₁`): a `u₋₁`-iterate and two commutators. -/
theorem mid_one_mode (u : V) (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    (p q r : ℂ) (K I : ℕ) (hK₃ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₃.YM u) k w₃ = 0)
    (hKV : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₅.YM u) k (Y₃ r w₃ w₄) = 0)
    (hI : ∀ i : ℤ, (I : ℤ) ≤ i → Y₁ (p + i) w₁ (YB q (Y₃ r w₃ w₄) w₂) = 0 ∧
      mode (A₆.YM u) i (YB q (Y₃ r w₃ w₄) w₂) = 0) :
    f (Y₁ p (mode (A₁.YM u) (-1) w₁) (YB q (Y₃ r w₃ w₄) w₂)) =
      ∑ i ∈ Finset.range I,
        (f (mode (A₀.YM u) (-1 - i) (Y₁ (p + i) w₁ (YB q (Y₃ r w₃ w₄) w₂)))
        + f (Y₁ (p - 1 - i) w₁ (YB q (Y₃ r w₃ w₄) (mode (A₂.YM u) i w₂)))
        + ∑ k ∈ Finset.range K, cbz i k *
          (f (Y₁ (p - 1 - i) w₁ (YB ((i : ℤ) + q - k) (Y₃ r w₃ (mode (A₄.YM u) k w₄)) w₂))
          + ∑ l ∈ Finset.range K, cbz k l *
            f (Y₁ (p - 1 - i) w₁ (YB ((i : ℤ) + q - k)
              (Y₃ (k + r - l) (mode (A₃.YM u) l w₃) w₄) w₂)))) := by
  have hin : ∀ k : ℤ, mode (A₅.YM u) k (Y₃ r w₃ w₄) = Y₃ r w₃ (mode (A₄.YM u) k w₄)
      + ∑ l ∈ Finset.range K, cbz k l • Y₃ (k + r - l) (mode (A₃.YM u) l w₃) w₄ :=
    fun k => mid_inner_comm hY₃ u w₃ w₄ r k K hK₃
  have hc : ∀ i : ℕ, mode (A₆.YM u) i (YB q (Y₃ r w₃ w₄) w₂) =
      YB q (Y₃ r w₃ w₄) (mode (A₂.YM u) i w₂) + ∑ k ∈ Finset.range K,
        cbz i k • YB ((i : ℤ) + q - k) (mode (A₅.YM u) k (Y₃ r w₃ w₄)) w₂ := by
    intro i
    rw [comm_range hYB u (Y₃ r w₃ w₄) w₂ (i : ℤ) q K hKV]; abel
  rw [negOneLeft_range hY₁ u w₁ _ p I hI]
  simp only [hc, hin, map_sum, map_smul, map_add, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  push_cast
  simp only [add_assoc]

include hY₁ hYB hY₃ in
/-- **Output slot** (dual mode `u_m`). -/
theorem mid_dual_mode (u : V) (g : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    (p q r : ℂ) (m : ℤ) (K : ℕ) (hK₁ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₁.YM u) k w₁ = 0)
    (hK₃ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₃.YM u) k w₃ = 0)
    (hKV : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₅.YM u) k (Y₃ r w₃ w₄) = 0) :
    g (mode (A₀.YM u) m (Y₁ p w₁ (YB q (Y₃ r w₃ w₄) w₂))) =
      g (Y₁ p w₁ (YB q (Y₃ r w₃ w₄) (mode (A₂.YM u) m w₂)))
      + ∑ k ∈ Finset.range K, cbz m k *
          (g (Y₁ p w₁ (YB (m + q - k) (Y₃ r w₃ (mode (A₄.YM u) k w₄)) w₂))
          + ∑ l ∈ Finset.range K, cbz k l *
            g (Y₁ p w₁ (YB (m + q - k) (Y₃ (k + r - l) (mode (A₃.YM u) l w₃) w₄) w₂)))
      + ∑ k ∈ Finset.range K, cbz m k *
          g (Y₁ (m + p - k) (mode (A₁.YM u) k w₁) (YB q (Y₃ r w₃ w₄) w₂)) := by
  have hin : ∀ k : ℤ, mode (A₅.YM u) k (Y₃ r w₃ w₄) = Y₃ r w₃ (mode (A₄.YM u) k w₄)
      + ∑ l ∈ Finset.range K, cbz k l • Y₃ (k + r - l) (mode (A₃.YM u) l w₃) w₄ :=
    fun k => mid_inner_comm hY₃ u w₃ w₄ r k K hK₃
  have h1 := comm_range hY₁ u w₁ (YB q (Y₃ r w₃ w₄) w₂) m p K hK₁
  have h2 := comm_range hYB u (Y₃ r w₃ w₄) w₂ m q K hKV
  rw [eq_sub_iff_add_eq] at h1 h2
  rw [← h1, ← h2]
  simp only [hin, map_sum, map_smul, map_add, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  all_goals (push_cast; ring)

end VOA.Huang.FivePointSep
