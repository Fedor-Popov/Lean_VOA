import VOA.Huang.LogAssocCoefficientL0Ward
import VOA.Huang.LogAssocCoefficientBounds

/-! Actual collision coefficients have their stated generalized L(0) weight.
Uniform genuine source Jordan bounds and the proved finite collision log
bound supply a common annihilating power. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocCoefficientL0
open VOA VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.Contra
open VOA.Huang.LogAssocCoefficients VOA.Huang.LogAssocCoefficientCompatibility
open Module (End)
open scoped BigOperators
universe u

/-- A genuine successor recurrence gives its exact iterated operator formula. -/
theorem successor_pow {X : Type*} [AddCommGroup X] [Module ℂ X]
    (D : End ℂ X) (C : ℕ → X) (h : ∀ k,D (C k)=((k:ℂ)+1) • C (k+1)) (j k : ℕ) :
    (D^j) (C k) = (∏ i∈Finset.range j,(((k+i:ℕ):ℂ)+1)) • C (k+j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ',Module.End.mul_apply,ih,map_smul,h,smul_smul,Finset.prod_range_succ]
    simp only [Nat.add_assoc]

/-- A commuting global nilpotent term can be added to a genuinely nilpotent orbit. -/
theorem add_pow_apply_zero {X : Type*} [AddCommGroup X] [Module ℂ X]
    {D S : End ℂ X} (h : Commute D S) {j q : ℕ} {v : X}
    (hj : (D^j) v=0) (hq : S^q=0) : ((D+S)^(j+q)) v=0 := by
  rw [h.add_pow',LinearMap.coe_sum,Finset.sum_apply]
  apply Finset.sum_eq_zero
  rintro ⟨a,b⟩ hab
  suffices ((D^a)*(S^b)) v=0 by rw [LinearMap.smul_apply,this,smul_zero]
  obtain ha | hb : j≤a ∨ q≤b := by have := Finset.mem_antidiagonal.mp hab; omega
  · rw [(h.pow_pow a b).eq,Module.End.mul_apply,Module.End.pow_map_zero_of_le ha hj,map_zero]
  · rw [pow_eq_zero_of_le hb hq,mul_zero,LinearMap.zero_apply]

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
  (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
  (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
  (hfg₅ : FinGen N₅.toWeakModule)
  (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
  (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)
include hC2 hfg₁ hfg₂ hfg₃ hfg₄ hfg₅

/-- One genuine power annihilates the full L(0)-gamma defect of every actual
coefficient with homogeneous outside data. No grading witness is assumed. -/
theorem exists_coefficient_L0_bound :
    ∃ Q : ℕ,∀ (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ),
      SupportedAt N₄ f β → z∈N₃.weight c →
      ((dualL0 N₁ N₂-γ • (1 : End ℂ (BilinearDual (M₁ := M₁) (M₂ := M₂))))^Q)
        (coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k)=0 := by
  obtain ⟨q₁,hq₁⟩ := firstNil_isNilpotent_of_finGen (M₂ := M₂) N₁ hfg₁
  obtain ⟨q₂,hq₂⟩ := secondNil_isNilpotent_of_finGen (M₁ := M₁) N₂ hfg₂
  obtain ⟨K,M,hB⟩ := exists_coefficient_bounds hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
  refine ⟨K+1+(q₁+q₂),?_⟩
  intro f z c β γ k hf hz
  let T := dualL0 N₁ N₂-γ • (1 : End ℂ (BilinearDual (M₁ := M₁) (M₂ := M₂)))
  let A := preFirst (M₂ := M₂) N₁.L0nil
  let B := preSecond (M₁ := M₁) N₂.L0nil
  let S := A+B
  let D := T-A-B
  let C : ℕ → BilinearDual (M₁ := M₁) (M₂ := M₂) := fun k =>
    coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k
  have hAB : Commute A B := preFirstSecond_commute N₁.L0nil N₂.L0nil
  have hTA : Commute T A := by
    refine (dualL0_commute_firstNil N₁ N₂).sub_left ?_
    exact (Commute.one_left _).smul_left γ
  have hTB : Commute T B := by
    refine (dualL0_commute_secondNil N₁ N₂).sub_left ?_
    exact (Commute.one_left _).smul_left γ
  have hDA : Commute D A := (hTA.sub_left (Commute.refl A)).sub_left hAB.symm
  have hDB : Commute D B := (hTB.sub_left hAB).sub_left (Commute.refl B)
  have hDS : Commute D S := hDA.add_right hDB
  have hS : S^(q₁+q₂)=0 :=
    hAB.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero hq₁ hq₂ (by omega)
  have hrec : ∀ k,D (C k)=((k:ℂ)+1) • C (k+1) := by
    intro k
    have hw := coefficient_L0_Ward hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
      Y₁ Y₂ f z c β γ k
    change T (C k)=((k:ℂ)+1) • C (k+1)+A (C k)+B (C k) at hw
    change T (C k)-A (C k)-B (C k)=_
    rw [hw]
    abel
  have hD : (D^(K+1)) (C k)=0 := by
    rw [successor_pow D C hrec]
    dsimp only [C]
    rw [hB c β z f hz hf γ (k+(K+1)) (Or.inl (by omega)),smul_zero]
  have hsum : T=D+S := by dsimp only [D,S]; abel
  change (T^(K+1+(q₁+q₂))) (C k)=0
  rw [hsum]
  exact add_pow_apply_zero hDS hD hS

/-- Each actual collision coefficient belongs to the generalized gamma eigenspace
of the genuine P(1) conformal operator. -/
theorem coefficient_mem_maxGenEigenspace (f : M₄ →ₗ[ℂ] ℂ) (z : M₃) (c β γ : ℂ) (k : ℕ)
    (hf : SupportedAt N₄ f β) (hz : z∈N₃.weight c) :
    coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k ∈
      (dualL0 N₁ N₂).maxGenEigenspace γ := by
  obtain ⟨Q,hQ⟩ := exists_coefficient_L0_bound hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
  exact (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨Q,hQ f z c β γ k hf hz⟩

end VOA.Huang.LogAssocCoefficientL0
