import VOA.Huang.GenusOneRecursion
import VOA.Modularity.ZhuBlockConditions

/-!
# Square-bracket modes on the insertion module

The coordinate change is pointwise finite by module truncation. These are actual
module modes, with the same coefficients as Zhu's adjoint square modes.
-/

namespace VOA.Huang.GenusOne
open VOA Module
open scoped BigOperators
universe u
variable {V M₁ M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V}

theorem sqAct_support_finite (A : OrdVModule W M₁) (a : V) (k : ℕ) (m : ℤ) (w : M₁) :
    (Function.support fun i : ℤ => sqBracketCoeffZ k m i • mode (A.YM a) i w).Finite := by
  obtain ⟨K, hK⟩ := A.truncation a w
  refine (Set.finite_Ico m K).subset fun i hi => ?_
  simp only [Function.mem_support] at hi
  constructor
  · by_contra h
    exact hi (by rw [sqBracketCoeffZ_of_lt k (lt_of_not_ge h), zero_smul])
  · by_contra h
    exact hi (by rw [hK i (le_of_not_gt h), smul_zero])

noncomputable def sqAct (A : OrdVModule W M₁) (a : V) (k : ℕ) (m : ℤ) : M₁ →ₗ[ℂ] M₁ where
  toFun w := ∑ᶠ i : ℤ, sqBracketCoeffZ k m i • mode (A.YM a) i w
  map_add' x y := by
    simp only [map_add, smul_add]
    exact finsum_add_distrib (sqAct_support_finite A a k m x) (sqAct_support_finite A a k m y)
  map_smul' c x := by
    change (∑ᶠ i : ℤ, sqBracketCoeffZ k m i • mode (A.YM a) i (c • x)) =
      c • ∑ᶠ i : ℤ, sqBracketCoeffZ k m i • mode (A.YM a) i x
    rw [smul_finsum' c (sqAct_support_finite A a k m x)]
    exact finsum_congr fun i => by rw [map_smul, smul_comm]

@[simp] theorem sqAct_apply (A : OrdVModule W M₁) (a : V) (k : ℕ) (m : ℤ) (w : M₁) :
    sqAct A a k m w = ∑ᶠ i : ℤ, sqBracketCoeffZ k m i • mode (A.YM a) i w := rfl

theorem sqAct_eventually_zero (A : OrdVModule W M₁) (a : V) (k : ℕ) (w : M₁) :
    ∃ K : ℤ, ∀ m : ℤ, K ≤ m → sqAct A a k m w = 0 := by
  obtain ⟨K, hK⟩ := A.truncation a w
  refine ⟨K, fun m hm => finsum_eq_zero_of_forall_eq_zero fun i => ?_⟩
  by_cases hi : i < m
  · rw [sqBracketCoeffZ_of_lt k hi, zero_smul]
  · rw [hK i (by omega), smul_zero]

theorem sqAct_add_left (A : OrdVModule W M₁) (a b : V) (k : ℕ) (m : ℤ) :
    sqAct A (a + b) k m = sqAct A a k m + sqAct A b k m := by
  ext w
  simp only [sqAct_apply, map_add, mode_add, LinearMap.add_apply, smul_add]
  exact finsum_add_distrib (sqAct_support_finite A a k m w) (sqAct_support_finite A b k m w)

theorem sqAct_smul_left (A : OrdVModule W M₁) (c : ℂ) (a : V) (k : ℕ) (m : ℤ) :
    sqAct A (c • a) k m = c • sqAct A a k m := by
  ext w
  simp only [sqAct_apply, map_smul, mode_smul, LinearMap.smul_apply]
  rw [smul_finsum' c (sqAct_support_finite A a k m w)]
  exact finsum_congr fun i => by simp only [smul_smul]; congr 1; ring

/-- Shifted conformal vector in the square coordinate. -/
noncomputable def sqL (A : OrdVModule W M₁) (n : ℤ) : Module.End ℂ M₁ :=
  sqAct A W.conformalVector 2 (n + 1) -
    (if n = -2 then W.centralCharge / 24 else 0) • LinearMap.id

variable {A : OrdVModule W M₁} {N : OrdVModule W M}

theorem trace_sqAct_expand (Y : IntertwiningOperator A N N) (a : V) (k : ℕ)
    (m : ℤ) (w : M₁) (e : ℂ) :
    trace Y (sqAct A a k m w) e =
      ∑ᶠ i : ℤ, sqBracketCoeffZ k m i * trace Y (mode (A.YM a) i w) e := by
  rw [sqAct_apply, map_finsum (trace Y) (sqAct_support_finite A a k m w)]
  rw [finsum_apply ((sqAct_support_finite A a k m w).subset (fun i hi => by
    simp only [Function.mem_support] at hi ⊢
    intro h; exact hi (by rw [h, map_zero])))]
  exact finsum_congr fun i => by simp only [map_smul, Pi.smul_apply, smul_eq_mul]

/-- The collected zero-square-mode trace identity, for every insertion vector. -/
theorem trace_sqAct_zero (Y : IntertwiningOperator A N N) {a : V} {k : ℕ}
    (ha : a ∈ W.grading (k : ℤ)) (hk : 1 ≤ k) (w : M₁) :
    trace Y (sqAct A a k 0 w) = 0 := by
  refine FusionTop.induction_weight A w (by simp) (fun x y hx hy => ?_) ?_
  · simp only [map_add, hx, hy, add_zero]
  · intro α x hx
    funext e
    rw [trace_sqAct_expand]
    simp_rw [← cbz_eq_sqBracketCoeffZ_zero k hk]
    exact trace_zero_bracket Y ha hx e

end VOA.Huang.GenusOne
