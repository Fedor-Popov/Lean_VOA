import VOA.Huang.LogAssocOutsideJacobiCommutator

/-! Actual outside Borcherds identity for the full-log collision coefficients.
The two proved boundary identities propagate by finite-support Pascal algebra. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocOutsideJacobi
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocCoefficients VOA.Huang.LogAssocCoefficientCoproduct
open VOA.Huang.LogAssocCoefficientCompatibility VOA.Huang.PzTensorRho
open VOA.Huang.PzTensorOutside VOA.Huang.PzTensorHatBridge
open scoped BigOperators
universe u
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

/-- The literal coefficient vanishes for zero outside input. -/
theorem coefficient_zero_z (f : M₄ →ₗ[ℂ] ℂ) (c β γ : ℂ) (k : ℕ) :
    coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f 0 c β γ k=0 := by
  change outsideCoefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ c β γ k f 0=0
  exact map_zero _

/-- The genuine full outside Jacobi identity, on arbitrary true generalized
homogeneous inside vectors. Every collision logarithmic degree is retained. -/
theorem coefficient_outside_borcherds_homogeneous (f : M₄ →ₗ[ℂ] ℂ) (z : M₃)
    (c β γ : ℂ) (k : ℕ) (hf : SupportedAt N₄ f β) (hz : z∈N₃.weight c)
    {d : ℤ} {u : V} (hu : u∈W.grading d)
    {a b : ℂ} {x : M₁} {y : M₂} (hx : x∈N₁.weight a) (hy : y∈N₂.weight b)
    (ell m : ℤ) :
    OE
      (fun q => coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
        (f ∘ₗ mode (N₄.YM u) q) z c (β-d+q+1) γ k x y)
      (fun q => coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
        f (mode (N₃.YM u) q z) (c+d-q-1) β γ k x y)
      (fun q => rhoL N₁.toWeakModule N₂.toWeakModule u q
        (coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
          f z c β (γ+d-q-1) k) x y) ell m=0 := by
  classical
  refine outer_vanish ?_ ?_ ?_ ?_ ?_ ell m
  · obtain ⟨Q,hQ⟩ := exists_comp_mode_vanish_below hf hu
    refine ⟨Q,fun q hq => ?_⟩
    rw [hQ q hq,coefficient_zero_f hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂,LinearMap.zero_apply,LinearMap.zero_apply]
  · obtain ⟨Q,hQ⟩ := N₃.toWeakModule.truncation u z
    refine ⟨Q,fun q hq => ?_⟩
    rw [hQ q hq,coefficient_zero_z hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂,LinearMap.zero_apply,LinearMap.zero_apply]
  · obtain ⟨I,hI⟩ := coefficient_shift_vanish hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hf hz d
    refine ⟨I,fun i hi => ?_⟩
    rw [hI i hi,map_zero,LinearMap.zero_apply,LinearMap.zero_apply]
  · intro L
    unfold OE
    beta_reduce
    have hZ0 : (∑ᶠ i : ℤ,cbz 0 i*rhoL N₁.toWeakModule N₂.toWeakModule u (L+i)
      (coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
        f z c β (γ+d-(L+i : ℤ)-1) k) x y)=
      rhoL N₁.toWeakModule N₂.toWeakModule u L
        (coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
          f z c β (γ+d-L-1) k) x y := by
      rw [finsum_eq_single _ 0 (fun i hi => by rw [cbz_zero_left,if_neg hi,zero_mul])]
      simp only [cbz_zero,add_zero,one_mul]
    rw [hZ0]
    simp only [add_zero,zero_add]
    obtain ⟨NA,hA⟩ := exists_comp_mode_vanish hf hu L
    obtain ⟨NZ,hZ⟩ := exists_nat_truncation N₃ u z
    have he := congrArg (fun B : BilinearDual (M₁ := M₁) (M₂ := M₂) => B x y)
      (coefficient_coproduct hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
        Y₁ Y₂ hu L f z c β (γ+d-L-1) k hA hZ)
    simp only [LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.sum_apply,
      LinearMap.coe_sum,Finset.sum_apply,smul_eq_mul] at he
    rw [show γ+(d : ℂ)-L-1-d+L+1=γ by ring] at he
    rw [he]
    rw [finsum_int_eq_range (fun i : ℤ => (negOnePow i*cbz L i)*
      coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
        (f ∘ₗ mode (N₄.YM u) (L-i)) z c (β-d+(L-i : ℤ)+1) γ k x y) NA
      (fun i hi => by
        beta_reduce
        rcases hi with hi | hi
        · rw [cbz_neg hi]; ring
        · have ha := hA i.toNat (by omega)
          rw [Int.toNat_of_nonneg (by omega)] at ha
          rw [ha,coefficient_zero_f hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
            Y₁ Y₂,LinearMap.zero_apply,LinearMap.zero_apply]; ring),
      finsum_int_eq_range (fun i : ℤ => (negOnePow i*cbz L i)*
        coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
          f (mode (N₃.YM u) i z) (c+d-i-1) β γ k x y) NZ
      (fun i hi => by
        beta_reduce
        rcases hi with hi | hi
        · rw [cbz_neg hi]; ring
        · obtain ⟨j,rfl⟩ : ∃ j : ℕ,i=(j : ℤ) := ⟨i.toNat,by omega⟩
          rw [hZ j (by exact_mod_cast hi),coefficient_zero_z hC2 N₁ N₂ N₃ N₄ N₅
            hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂,LinearMap.zero_apply,LinearMap.zero_apply]; ring)]
    simp only [Int.cast_natCast]
    ring
  · intro M
    unfold OE
    beta_reduce
    have hX0 : (∑ᶠ i : ℤ,(negOnePow i*cbz 0 i)*
      coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
        (f ∘ₗ mode (N₄.YM u) (0+M-i)) z c (β-d+(0+M-i : ℤ)+1) γ k x y)=
      coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
        (f ∘ₗ mode (N₄.YM u) M) z c (β-d+M+1) γ k x y := by
      rw [finsum_eq_single _ 0 (fun i hi => by rw [cbz_zero_left,if_neg hi]; ring)]
      simp [negOnePow]
    have hY0 : (∑ᶠ i : ℤ,(negOnePow i*cbz 0 i)*
      coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
        f (mode (N₃.YM u) (M+i) z) (c+d-(M+i : ℤ)-1) β γ k x y)=
      coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
        f (mode (N₃.YM u) M z) (c+d-M-1) β γ k x y := by
      rw [finsum_eq_single _ 0 (fun i hi => by rw [cbz_zero_left,if_neg hi]; ring)]
      simp [negOnePow]
    rw [hX0,hY0,show negOnePow 0=1 by simp [negOnePow],one_mul,
      coefficient_commutator_homogeneous_rho hC2 N₁ N₂ N₃ N₄ N₅
        hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hf hz hu M hx hy]
    simp only [zero_add,sub_self]

end VOA.Huang.LogAssocOutsideJacobi
