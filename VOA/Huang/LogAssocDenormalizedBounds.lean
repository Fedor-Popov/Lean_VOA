import VOA.Huang.LogAssocUniformCollisionLog
import VOA.Huang.LogAssocUniformCollisionWeight
import VOA.Huang.LogAssocExpansionVectors

/-! Collision bounds for the literal full integer product, including its
original logarithms. Renormalization is undone by convergent holomorphic
factors and an explicit collision exponent shift. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.C2Rigid VOA.LogTensor PowerSeries VOA.Huang.HuangODEAlgebra
open VOA.Huang.LogHuangODEProduct VOA.Huang.LogHuangODEIterPoint
open VOA.Huang.AssocExpansion VOA.Huang.AssocCoeffRules VOA.Huang.MatrixCoeff VOA.Huang.FrobeniusLog
open VOA.Huang.HuangODEIterPoint
open VOA.Huang.LogRemovalCoeff VOA.Huang.LogRemovalBound VOA.Huang.LogRemovalWeightBound
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- The actual normalized series is the ordinary power-series row after the
true integer coset has been shifted to a genuine truncation base. -/
theorem QT_eq_prodSeries (Y₁ : IntertwiningModes M₁ M₅ M₄)
    (Y₂ : IntertwiningModes M₂ M₃ M₅) (f : M₄ →ₗ[ℂ] ℂ)
    (x : M₁) (y : M₂) (z : M₃) (c ν : ℂ) (n₄ s : ℕ) :
    QT Y₁ Y₂ c ν f x y z n₄ s=
      prodSeries Y₁ Y₂ f x y z (c+s-2*n₄) (ν+s) := by
  ext n
  simp only [QT,coeff_prodQ,coeff_prodSeries,prodCoeff]
  congr 2
  ring

/-- Genuine original log powers are holomorphic factors at collision, so
multiplication preserves the collision log degree. -/
theorem LogDegLE.logOneAdd_mul {K : ℕ} {F : ℂ → ℂ} (hF : LogDegLE K F) (k : ℕ) :
    LogDegLE K (fun t => (Complex.log (1+Complex.exp t))^k*F t) := by
  refine (hF.psEval_mul (SubexpPS.pow_mem logOneAddSeries_subexp k)).congr fun t ht => ?_
  rw [psEval_pow logOneAddSeries_subexp (norm_exp_lt_one ht),
    psEval_logOneAddSeries (norm_exp_lt_one ht)]

/-- Genuine original log powers do not lower collision exponents. -/
theorem ExpGE.logOneAdd_mul {M : ℝ} {F : ℂ → ℂ} (hF : ExpGE M F) (k : ℕ) :
    ExpGE M (fun t => (Complex.log (1+Complex.exp t))^k*F t) := by
  refine (hF.psEval_mul (SubexpPS.pow_mem logOneAddSeries_subexp k)).congr fun t ht => ?_
  rw [psEval_pow logOneAddSeries_subexp (norm_exp_lt_one ht),
    psEval_logOneAddSeries (norm_exp_lt_one ht)]

/-- Undoing the actual level renormalization preserves collision log degree. -/
theorem logDegLE_denormalize {Y₁ : IntertwiningModes M₁ M₅ M₄}
    {Y₂ : IntertwiningModes M₂ M₃ M₅} {f : M₄ →ₗ[ℂ] ℂ}
    {x : M₁} {y : M₂} {z : M₃} {c ν : ℂ} {n₄ s K : ℕ}
    (hG : QT Y₁ Y₂ c ν f x y z n₄ s∈SubexpPS)
    (hK : LogDegLE K (Phi (c-ν) ((1-X)^s*QT Y₁ Y₂ c ν f x y z n₄ s))) :
    LogDegLE K (prodFun Y₁ Y₂ f x y z (c+s-2*n₄) (ν+s)) := by
  have he := QT_eq_prodSeries Y₁ Y₂ f x y z c ν n₄ s
  have hG' := he ▸ hG
  refine ((hK.psEval_mul (binPS_mem ((2*n₄ : ℕ)+s))).exp_mul (-(s : ℂ))).congr fun t ht => ?_
  have hh := prodFun_eq_Phi Y₁ Y₂ f x y z (c+s-2*n₄) (ν+s) (c-ν)
    0 (2*n₄) s 0 (by push_cast; ring) hG' ht
  simp only [Nat.cast_zero,sub_zero,add_zero,pow_zero,one_mul] at hh
  rw [← he] at hh
  exact hh.symm

/-- Undoing level renormalization lowers the exponent bound by exactly the
sum of the four genuine generalized weight levels. -/
theorem expGE_denormalize {Y₁ : IntertwiningModes M₁ M₅ M₄}
    {Y₂ : IntertwiningModes M₂ M₃ M₅} {f : M₄ →ₗ[ℂ] ℂ}
    {x : M₁} {y : M₂} {z : M₃} {c ν : ℂ} {n₄ s : ℕ} {M : ℝ}
    (hG : QT Y₁ Y₂ c ν f x y z n₄ s∈SubexpPS)
    (hM : ExpGE M (Phi (c-ν) ((1-X)^s*QT Y₁ Y₂ c ν f x y z n₄ s))) :
    ExpGE (M-s) (prodFun Y₁ Y₂ f x y z (c+s-2*n₄) (ν+s)) := by
  have he := QT_eq_prodSeries Y₁ Y₂ f x y z c ν n₄ s
  have hG' := he ▸ hG
  have hb := (hM.psEval_mul (binPS_mem ((2*n₄ : ℕ)+s))).exp_mul (-(s : ℂ))
  have hr : M+(-(s : ℂ)).re=M-s := by simp [sub_eq_add_neg]
  rw [hr] at hb
  refine hb.congr fun t ht => ?_
  have hh := prodFun_eq_Phi Y₁ Y₂ f x y z (c+s-2*n₄) (ν+s) (c-ν)
    0 (2*n₄) s 0 (by push_cast; ring) hG' ht
  simp only [Nat.cast_zero,sub_zero,add_zero,pow_zero,one_mul] at hh
  rw [← he] at hh
  exact hh.symm

/-- Finite sums preserve a common genuine collision log degree. -/
theorem logDegLE_sum {ι : Type*} (S : Finset ι) {K : ℕ} {F : ι → ℂ → ℂ}
    (h : ∀ i∈S,LogDegLE K (F i)) : LogDegLE K (fun t => ∑ i∈S,F i t) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using logDegLE_zero K
  | @insert a S ha ih =>
    simpa only [Finset.sum_insert ha,Pi.add_apply] using
      (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Finite sums preserve a common genuine collision exponent bound. -/
theorem expGE_sum {ι : Type*} (S : Finset ι) {M : ℝ} {F : ι → ℂ → ℂ}
    (h : ∀ i∈S,ExpGE M (F i)) : ExpGE M (fun t => ∑ i∈S,F i t) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using expGE_zero M
  | @insert a S ha ih =>
    simpa only [Finset.sum_insert ha,Pi.add_apply] using
      (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end VOA.Huang.LogAssocExpansion
