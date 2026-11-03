import VOA.Huang.LogAssocFivePointPairBase
import VOA.Huang.LogAssocFivePointMidModes

/-!
# The five slot relations for the pair shape

Finite mode identities for `f(𝒴_P(p) (𝒴_{XY}(r) x y) (𝒴_{ZT}(q) z t))`: a VOA mode moves
between the four vectors `t, z, x, y` (product slots `w₁ … w₄`) and the output functional.
-/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePointGraded
open VOA VOA.C2Rigid VOA.Huang.LogHuangODEModes
open VOA.Huang.FivePointSep
open VOA.Huang.LogHuangODEProduct
open VOA.Huang.HuangODEProduct (sum_range_trim)
open VOA.Huang.HuangODEModes (cbz_neg_one_sub cbz_nat)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₀ M₁ M₂ M₃ M₄ MU MV : Type u}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup MU] [Module ℂ MU]
  [AddCommGroup MV] [Module ℂ MV]
variable {A₀ : C2Rigid.GWModule W M₀} {A₁ : C2Rigid.GWModule W M₁}
  {A₂ : C2Rigid.GWModule W M₂} {A₃ : C2Rigid.GWModule W M₃} {A₄ : C2Rigid.GWModule W M₄}
  {AU : C2Rigid.GWModule W MU} {AV : C2Rigid.GWModule W MV}
variable {P : IntertwiningModes MU MV M₀} {ZT : IntertwiningModes M₂ M₁ MV}
  {XY : IntertwiningModes M₃ M₄ MU}
variable (hP : LogHuangODEProduct.IsGradedJacobiFamily AU AV A₀ P)
  (hZT : LogHuangODEProduct.IsGradedJacobiFamily A₂ A₁ AV ZT) (hXY : LogHuangODEProduct.IsGradedJacobiFamily A₃ A₄ AU XY)

include hP hZT hXY in
/-- **Terminal slot** (`u₋₁ t`). -/
theorem pair_terminal_mode (u : V) (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    (p q r : ℂ) (K : ℕ) (hK₂ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₂.YM u) k w₂ = 0)
    (hK₃ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₃.YM u) k w₃ = 0)
    (hKU : ∀ k : ℤ, (K : ℤ) ≤ k → mode (AU.YM u) k (XY r w₃ w₄) = 0) :
    f (P p (XY r w₃ w₄) (ZT q w₂ (mode (A₁.YM u) (-1) w₁))) =
      f (mode (A₀.YM u) (-1) (P p (XY r w₃ w₄) (ZT q w₂ w₁)))
      - ∑ k ∈ Finset.range K, cbz (-1) k *
          (f (P (-1 + p - k) (XY r w₃ (mode (A₄.YM u) k w₄)) (ZT q w₂ w₁))
          + ∑ l ∈ Finset.range K, cbz k l *
            f (P (-1 + p - k) (XY (k + r - l) (mode (A₃.YM u) l w₃) w₄) (ZT q w₂ w₁)))
      - ∑ k ∈ Finset.range K, cbz (-1) k *
          f (P p (XY r w₃ w₄) (ZT (-1 + q - k) (mode (A₂.YM u) k w₂) w₁)) := by
  have hin : ∀ k : ℤ, mode (AU.YM u) k (XY r w₃ w₄) = XY r w₃ (mode (A₄.YM u) k w₄)
      + ∑ l ∈ Finset.range K, cbz k l • XY (k + r - l) (mode (A₃.YM u) l w₃) w₄ :=
    fun k => mid_inner_comm hXY u w₃ w₄ r k K hK₃
  rw [comm_range hZT.toIsJacobiFamily u w₂ w₁ (-1) q K hK₂, map_sub,
    comm_range hP.toIsJacobiFamily u (XY r w₃ w₄) (ZT q w₂ w₁) (-1) p K hKU]
  simp only [hin, map_sub, map_sum, map_smul, map_add, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  push_cast
  ring

include hP hZT hXY in
/-- **Second slot** (`u₋₁ z`). -/
theorem pair_z_mode (u : V) (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    (p q r : ℂ) (K I : ℕ) (hK₃ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₃.YM u) k w₃ = 0)
    (hKU : ∀ k : ℤ, (K : ℤ) ≤ k → mode (AU.YM u) k (XY r w₃ w₄) = 0)
    (hI : ∀ i : ℤ, (I : ℤ) ≤ i → ZT (q + i) w₂ w₁ = 0 ∧ mode (A₁.YM u) i w₁ = 0) :
    f (P p (XY r w₃ w₄) (ZT q (mode (A₂.YM u) (-1) w₂) w₁)) =
      ∑ i ∈ Finset.range I,
        (f (mode (A₀.YM u) (-1 - i) (P p (XY r w₃ w₄) (ZT (q + i) w₂ w₁)))
        - ∑ k ∈ Finset.range K, cbz (-1 - i) k *
          (f (P ((-1 - i : ℤ) + p - k) (XY r w₃ (mode (A₄.YM u) k w₄)) (ZT (q + i) w₂ w₁))
          + ∑ l ∈ Finset.range K, cbz k l *
            f (P ((-1 - i : ℤ) + p - k) (XY (k + r - l) (mode (A₃.YM u) l w₃) w₄)
              (ZT (q + i) w₂ w₁)))
        + f (P p (XY r w₃ w₄) (ZT (q - 1 - i) w₂ (mode (A₁.YM u) i w₁)))) := by
  have hin : ∀ k : ℤ, mode (AU.YM u) k (XY r w₃ w₄) = XY r w₃ (mode (A₄.YM u) k w₄)
      + ∑ l ∈ Finset.range K, cbz k l • XY (k + r - l) (mode (A₃.YM u) l w₃) w₄ :=
    fun k => mid_inner_comm hXY u w₃ w₄ r k K hK₃
  have hc : ∀ (i : ℕ) (Vv : MV), P p (XY r w₃ w₄) (mode (AV.YM u) (-1 - i) Vv) =
      mode (A₀.YM u) (-1 - i) (P p (XY r w₃ w₄) Vv) - ∑ k ∈ Finset.range K, cbz (-1 - i) k •
        P ((-1 - i : ℤ) + p - k) (mode (AU.YM u) k (XY r w₃ w₄)) Vv := by
    intro i Vv
    rw [comm_range hP.toIsJacobiFamily u (XY r w₃ w₄) Vv (-1 - i) p K hKU]
  rw [negOneLeft_range hZT.toIsJacobiFamily u w₂ w₁ q I hI]
  simp only [map_sum, map_add, hc, hin, map_sub, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

include hP hZT hXY in
/-- **Third slot** (`u₋₁ x`): a `u₋₁`-iterate, an iterate and a commutator. -/
theorem pair_x_mode (u : V) (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    (p q r : ℂ) (K I J : ℕ) (hK₂ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₂.YM u) k w₂ = 0)
    (hI : ∀ i : ℤ, (I : ℤ) ≤ i → XY (r + i) w₃ w₄ = 0 ∧ mode (A₄.YM u) i w₄ = 0)
    (hJ : ∀ i : ℕ, i < I → ∀ j : ℤ, (J : ℤ) ≤ j → P (p + j) (XY (r + i) w₃ w₄) (ZT q w₂ w₁) = 0 ∧
      mode (AV.YM u) j (ZT q w₂ w₁) = 0) :
    f (P p (XY r (mode (A₃.YM u) (-1) w₃) w₄) (ZT q w₂ w₁)) =
      ∑ i ∈ Finset.range I,
        (∑ j ∈ Finset.range J, (negOnePow j * cbz (-1 - i) j) *
          (f (mode (A₀.YM u) (-1 - i - j) (P (p + j) (XY (r + i) w₃ w₄) (ZT q w₂ w₁)))
          - negOnePow (-1 - i) *
            (f (P ((-1 - i : ℤ) + p - j) (XY (r + i) w₃ w₄) (ZT q w₂ (mode (A₁.YM u) j w₁)))
            + ∑ k ∈ Finset.range K, cbz j k *
              f (P ((-1 - i : ℤ) + p - j) (XY (r + i) w₃ w₄)
                (ZT (j + q - k) (mode (A₂.YM u) k w₂) w₁))))
        + f (P p (XY (r - 1 - i) w₃ (mode (A₄.YM u) i w₄)) (ZT q w₂ w₁))) := by
  have hin : ∀ j : ℤ, mode (AV.YM u) j (ZT q w₂ w₁) = ZT q w₂ (mode (A₁.YM u) j w₁)
      + ∑ k ∈ Finset.range K, cbz j k • ZT (j + q - k) (mode (A₂.YM u) k w₂) w₁ :=
    fun j => mid_inner_comm hZT u w₂ w₁ q j K hK₂
  rw [negOneLeft_range hXY.toIsJacobiFamily u w₃ w₄ r I hI]
  simp only [map_sum, map_add, LinearMap.add_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [iterate_range hP.toIsJacobiFamily u (XY (r + i) w₃ w₄) (ZT q w₂ w₁) (-1 - i) p J (hJ i hi')]
  simp only [hin, map_sub, map_sum, map_smul, map_add, smul_eq_mul]
  push_cast
  ring

include hP hZT hXY in
/-- **Fourth slot** (`u₋₁ y`). -/
theorem pair_y_mode (u : V) (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    (p q r : ℂ) (K J : ℕ) (hK₂ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₂.YM u) k w₂ = 0)
    (hK₃ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₃.YM u) k w₃ = 0)
    (hJ : ∀ j : ℤ, (J : ℤ) ≤ j → P (p + j) (XY r w₃ w₄) (ZT q w₂ w₁) = 0 ∧
      mode (AV.YM u) j (ZT q w₂ w₁) = 0) :
    f (P p (XY r w₃ (mode (A₄.YM u) (-1) w₄)) (ZT q w₂ w₁)) =
      ∑ j ∈ Finset.range J, (negOnePow j * cbz (-1) j) *
        (f (mode (A₀.YM u) (-1 - j) (P (p + j) (XY r w₃ w₄) (ZT q w₂ w₁)))
        - negOnePow (-1) *
          (f (P (-1 + p - j) (XY r w₃ w₄) (ZT q w₂ (mode (A₁.YM u) j w₁)))
          + ∑ k ∈ Finset.range K, cbz j k *
            f (P (-1 + p - j) (XY r w₃ w₄) (ZT (j + q - k) (mode (A₂.YM u) k w₂) w₁))))
      - ∑ k ∈ Finset.range K, cbz (-1) k *
          f (P p (XY (-1 + r - k) (mode (A₃.YM u) k w₃) w₄) (ZT q w₂ w₁)) := by
  have hin : ∀ j : ℤ, mode (AV.YM u) j (ZT q w₂ w₁) = ZT q w₂ (mode (A₁.YM u) j w₁)
      + ∑ k ∈ Finset.range K, cbz j k • ZT (j + q - k) (mode (A₂.YM u) k w₂) w₁ :=
    fun j => mid_inner_comm hZT u w₂ w₁ q j K hK₂
  rw [comm_range hXY.toIsJacobiFamily u w₃ w₄ (-1) r K hK₃, map_sub, LinearMap.sub_apply, map_sub,
    iterate_range hP.toIsJacobiFamily u (XY r w₃ w₄) (ZT q w₂ w₁) (-1) p J hJ]
  simp only [hin, map_sub, map_sum, map_smul, map_add, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]
  push_cast
  ring

include hP hZT hXY in
/-- **Output slot** (dual mode `u_m`). -/
theorem pair_dual_mode (u : V) (g : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    (p q r : ℂ) (m : ℤ) (K : ℕ) (hK₂ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₂.YM u) k w₂ = 0)
    (hK₃ : ∀ k : ℤ, (K : ℤ) ≤ k → mode (A₃.YM u) k w₃ = 0)
    (hKU : ∀ k : ℤ, (K : ℤ) ≤ k → mode (AU.YM u) k (XY r w₃ w₄) = 0) :
    g (mode (A₀.YM u) m (P p (XY r w₃ w₄) (ZT q w₂ w₁))) =
      g (P p (XY r w₃ w₄) (ZT q w₂ (mode (A₁.YM u) m w₁)))
      + ∑ k ∈ Finset.range K, cbz m k *
          g (P p (XY r w₃ w₄) (ZT (m + q - k) (mode (A₂.YM u) k w₂) w₁))
      + ∑ k ∈ Finset.range K, cbz m k *
          (g (P (m + p - k) (XY r w₃ (mode (A₄.YM u) k w₄)) (ZT q w₂ w₁))
          + ∑ l ∈ Finset.range K, cbz k l *
            g (P (m + p - k) (XY (k + r - l) (mode (A₃.YM u) l w₃) w₄) (ZT q w₂ w₁))) := by
  have hin : ∀ k : ℤ, mode (AU.YM u) k (XY r w₃ w₄) = XY r w₃ (mode (A₄.YM u) k w₄)
      + ∑ l ∈ Finset.range K, cbz k l • XY (k + r - l) (mode (A₃.YM u) l w₃) w₄ :=
    fun k => mid_inner_comm hXY u w₃ w₄ r k K hK₃
  have h1 := comm_range hP.toIsJacobiFamily u (XY r w₃ w₄) (ZT q w₂ w₁) m p K hKU
  have h2 := comm_range hZT.toIsJacobiFamily u w₂ w₁ m q K hK₂
  rw [eq_sub_iff_add_eq] at h1 h2
  rw [← h1, ← h2]
  simp only [hin, map_sum, map_smul, map_add, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  push_cast
  ring

end VOA.Huang.LogAssocFivePointGraded
