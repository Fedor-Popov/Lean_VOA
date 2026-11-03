import VOA.Classification.COne.McRaeM2LogPentagonLeftArrays

/-! # The pentagon for the logarithmic tensor product (HLZ)

For every C₂-cofinite VOA `W`, the actual logarithmic associator `associatorIso`
on `LogModuleCat W` satisfies the pentagon. The two pentagon paths agree after
completed five-point evaluation on the common chart (all five literal expansions
converge absolutely and every single reassociation is the proved three-point
associativity fiber). Two-scale power-log uniqueness of the left expansion then
kills every literal nested canonical coefficient of the difference, and these
coefficients span the fourfold tensor (`tensorPentagon_eq_iff_canonical`). -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePoint
open VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.LogModuleCat VOA.LogSkew
open VOA.C2Rigid.LocalInjective VOA.Huang.LogAssocFivePointGraded VOA.Huang.HuangODEThree
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

/-- Three nested bilinear maps vanish when the innermost one vanishes. -/
theorem nested_zero_inner {A B C D E F : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F] {G : Type*} [AddCommGroup G]
    [Module ℂ G] (Y₁ : A →ₗ[ℂ] B →ₗ[ℂ] C) (Y₂ : C →ₗ[ℂ] D →ₗ[ℂ] E) (Y₃ : E →ₗ[ℂ] F →ₗ[ℂ] G)
    (g : G →ₗ[ℂ] ℂ) (x : A) (y : B) (z : D) (w : F) (h : Y₁=0) :
    g (Y₃ (Y₂ (Y₁ x y) z) w)=0 := by
  subst h; simp

/-- Three nested bilinear maps vanish when the middle one vanishes. -/
theorem nested_zero_middle {A B C D E F : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F] {G : Type*} [AddCommGroup G]
    [Module ℂ G] (Y₁ : A →ₗ[ℂ] B →ₗ[ℂ] C) (Y₂ : C →ₗ[ℂ] D →ₗ[ℂ] E) (Y₃ : E →ₗ[ℂ] F →ₗ[ℂ] G)
    (g : G →ₗ[ℂ] ℂ) (x : A) (y : B) (z : D) (w : F) (h : Y₂=0) :
    g (Y₃ (Y₂ (Y₁ x y) z) w)=0 := by
  subst h; simp

-- Actual fourfold point-block signatures require a larger elaboration budget.
set_option maxHeartbeats 8000000 in
/-- Vanishing completed left evaluations kill every literal left coefficient. -/
theorem leftCoeff_eq_zero (N P Q R : LogModuleCat W)
    (g : fivePointObject hC2 N P Q R .left →ₗ[ℂ] ℂ) (a b c d β : ℂ)
    (x : N.act.weight a) (y : P.act.weight b) (z : Q.act.weight c) (w : R.act.weight d)
    (hz : ∀ r s : ℝ, FivePointDomain r s →
      fivePointEvaluation hC2 N P Q R .left a b c d β x y z w r s g=0)
    (γ δ : ℂ) (k l : ℕ) :
    leftCoeff hC2 N P Q R g a b c d β x y z w γ δ k l=0 := by
  obtain ⟨K,hK⟩ := uniform_log_degree_of_finGen N.act P.act (tensorObject hC2 N P).act
    N.finiteGeneration P.finiteGeneration (tensorObject hC2 N P).finiteGeneration
  obtain ⟨L,hL⟩ := uniform_log_degree_of_finGen (tensorObject hC2 N P).act Q.act
    (tensorObject hC2 (tensorObject hC2 N P) Q).act
    (tensorObject hC2 N P).finiteGeneration Q.finiteGeneration
    (tensorObject hC2 (tensorObject hC2 N P) Q).finiteGeneration
  have hK' : ∀ n k, K≤k → (tensorIntertwiner hC2 N.act P.act
      N.finiteGeneration P.finiteGeneration).1 n k=0 := fun n k hk => hK _ n k hk
  have hL' : ∀ n l, L≤l → (tensorIntertwiner hC2 (tensorObject hC2 N P).act Q.act
      (tensorObject hC2 N P).finiteGeneration Q.finiteGeneration).1 n l=0 :=
    fun n l hl => hL _ n l hl
  obtain ⟨S,hS⟩ := finite_lower_weight_spectrum hC2 (tensorObject hC2 N P)
  obtain ⟨S',hS'⟩ := finite_lower_weight_spectrum hC2 (tensorObject hC2 (tensorObject hC2 N P) Q)
  have main := twoScale_loggps_zero S S' (a+b) c
    (fun γ δ k l => leftCoeff hC2 N P Q R g a b c d β x y z w γ δ k l) K L
    (fun γ δ k l h => hS γ
      (leftCoeff_support hC2 N P Q R g a b c d β w x.2 y.2 z.2 γ δ k l h).1)
    (fun γ δ k l h => hS' δ
      (leftCoeff_support hC2 N P Q R g a b c d β w x.2 y.2 z.2 γ δ k l h).2)
    (fun r s hD k l => leftCoeff_summable hC2 N P Q R g a b c d β x y z w r s hD k l)
    (fun r s hD => by
      have h0 := hz r s hD
      unfold fivePointEvaluation at h0
      rw [← h0]
      apply tsum_congr
      intro p
      exact (fivePointTerm_left_expand hC2 N P Q R a b c d β x y z w r s hD.1
        (hD.1.trans hD.2.1) g K L hK' hL' p.1 p.2).symm)
  by_cases hk : k<K
  · by_cases hl : l<L
    · exact main γ δ k hk l hl
    · unfold leftCoeff
      exact nested_zero_middle _ _ _ g _ _ _ _ (hL' _ l (not_lt.mp hl))
  · unfold leftCoeff
    exact nested_zero_inner _ _ _ g _ _ _ _ (hK' _ k (not_lt.mp hk))

-- Actual fourfold tensor signatures require a larger elaboration budget.
set_option maxHeartbeats 4000000 in
/-- The literal log-free left coefficient at matched modes is a nested
canonical fourfold coefficient. -/
theorem leftCoeff_zero_zero (N P Q R : LogModuleCat W)
    (g : fivePointObject hC2 N P Q R .left →ₗ[ℂ] ℂ) (a b c d β : ℂ)
    (x : N) (y : P) (z : Q) (w : R) (γ δ n m p : ℂ)
    (hγ : a+b-γ-1=p) (hδ : γ+c-δ-1=m) (hβ : δ+d-β-1=n) :
    leftCoeff hC2 N P Q R g a b c d β x y z w γ δ 0 0=
      g (leftFourCoefficient hC2 N.act P.act N.finiteGeneration P.finiteGeneration
        Q.act Q.finiteGeneration R.act R.finiteGeneration n m p x y z w) := by
  unfold leftCoeff
  rw [hγ, hδ, hβ]
  rfl

/-- Homogeneous vanishing of a functional of three nested bilinear maps on
finite logarithmic modules propagates to all inputs. -/
theorem nested_eq_zero_of_homogeneous {A B D F C E G : Type u}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup D] [Module ℂ D] [AddCommGroup F] [Module ℂ F]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup E] [Module ℂ E]
    [AddCommGroup G] [Module ℂ G]
    (NA : LogVModule W A) (NB : LogVModule W B) (ND : LogVModule W D) (NF : LogVModule W F)
    (Y₁ : A →ₗ[ℂ] B →ₗ[ℂ] C) (Y₂ : C →ₗ[ℂ] D →ₗ[ℂ] E) (Y₃ : E →ₗ[ℂ] F →ₗ[ℂ] G)
    (g : G →ₗ[ℂ] ℂ)
    (hhom : ∀ (a b c d : ℂ) (x : A) (y : B) (z : D) (w : F), x∈NA.weight a →
      y∈NB.weight b → z∈ND.weight c → w∈NF.weight d → g (Y₃ (Y₂ (Y₁ x y) z) w)=0)
    (x : A) (y : B) (z : D) (w : F) : g (Y₃ (Y₂ (Y₁ x y) z) w)=0 := by
  refine LogFin.induction_on NA (C := fun x => ∀ y z w, g (Y₃ (Y₂ (Y₁ x y) z) w)=0)
    x ?_ ?_ ?_ y z w
  · intro a x hx y z w
    refine LogFin.induction_on NB (C := fun y => ∀ z w, g (Y₃ (Y₂ (Y₁ x y) z) w)=0)
      y ?_ ?_ ?_ z w
    · intro b y hy z w
      refine LogFin.induction_on ND (C := fun z => ∀ w, g (Y₃ (Y₂ (Y₁ x y) z) w)=0)
        z ?_ ?_ ?_ w
      · intro c z hz w
        refine LogFin.induction_on NF (C := fun w => g (Y₃ (Y₂ (Y₁ x y) z) w)=0) w ?_ ?_ ?_
        · intro d w hw
          exact hhom a b c d x y z w hx hy hz hw
        · simp
        · intro w w' h h'
          simp only [map_add, h, h', add_zero] at *
      · intro w; simp
      · intro z z' h h' w
        simp only [map_add, LinearMap.add_apply, h, h', add_zero]
    · intro z w; simp
    · intro y y' h h' z w
      simp only [map_add, LinearMap.add_apply, h, h', add_zero]
  · intro y z w; simp
  · intro x x' h h' y z w
    simp only [map_add, LinearMap.add_apply, h, h', add_zero]

-- Actual fourfold tensor signatures require a larger elaboration budget.
set_option maxHeartbeats 4000000 in
/-- Faithfulness of the completed left five-point evaluation: a functional
on `((N ⊠ P) ⊠ Q) ⊠ R` whose completed left evaluations vanish on the common
chart annihilates every literal nested canonical coefficient. -/
theorem leftFour_functional_eq_zero (N P Q R : LogModuleCat W)
    (g : fivePointObject hC2 N P Q R .left →ₗ[ℂ] ℂ)
    (hz : ∀ (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
      (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ), FivePointDomain r s →
      fivePointEvaluation hC2 N P Q R .left a b c d β x y z w r s g=0)
    (n m p : ℂ) (x : N) (y : P) (z : Q) (w : R) :
    g (leftFourCoefficient hC2 N.act P.act N.finiteGeneration P.finiteGeneration
      Q.act Q.finiteGeneration R.act R.finiteGeneration n m p x y z w)=0 := by
  refine nested_eq_zero_of_homogeneous N.act P.act Q.act R.act
    ((tensorIntertwiner hC2 N.act P.act N.finiteGeneration P.finiteGeneration).1 p 0)
    ((tensorIntertwiner hC2 (tensorObject hC2 N P).act Q.act
      (tensorObject hC2 N P).finiteGeneration Q.finiteGeneration).1 m 0)
    ((tensorIntertwiner hC2 (tensorObject hC2 (tensorObject hC2 N P) Q).act R.act
      (tensorObject hC2 (tensorObject hC2 N P) Q).finiteGeneration R.finiteGeneration).1 n 0)
    g ?_ x y z w
  intro a b c d x y z w hx hy hz' hw
  have h := leftCoeff_eq_zero hC2 N P Q R g a b c d (a+b-p-1+c-m-1+d-n-1)
    ⟨x,hx⟩ ⟨y,hy⟩ ⟨z,hz'⟩ ⟨w,hw⟩ (fun r s hD => hz _ _ _ _ _ _ _ _ _ r s hD)
    (a+b-p-1) (a+b-p-1+c-m-1) 0 0
  rw [leftCoeff_zero_zero hC2 N P Q R g a b c d _ x y z w _ _ n m p
    (by ring) (by ring) (by ring)] at h
  exact h

end VOA.Huang.LogAssocFivePoint

namespace VOA.LogTensor.LogModuleCat
open CategoryTheory VOA.C2Rigid.LocalInjective VOA.Huang.LogAssocFivePoint
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

-- Actual fourfold categorical path types require a larger elaboration budget.
set_option maxHeartbeats 8000000 in
/-- **The pentagon** for the actual logarithmic associator of the tensor
product of finite logarithmic modules of a C₂-cofinite VOA. -/
theorem tensorPentagon (N P Q R : LogModuleCat W) :
    tensorPentagonLong hC2 N P Q R=tensorPentagonShort hC2 N P Q R := by
  rw [tensorPentagon_eq_iff_canonical]
  intro n m p x y z w
  rw [← sub_eq_zero, ← LinearMap.sub_apply]
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro f
  refine leftFour_functional_eq_zero hC2 N P Q R
    (f ∘ₗ ((tensorPentagonLong hC2 N P Q R).1-(tensorPentagonShort hC2 N P Q R).1)) ?_ n m p x y z w
  intro a b c d β x y z w r s hD
  have hLs := (fivePointTerm_summable_norm hC2 N P Q R .left a b c d β x y z w r s hD
    (f ∘ₗ (tensorPentagonLong hC2 N P Q R).1)).of_norm
  have hSs := (fivePointTerm_summable_norm hC2 N P Q R .left a b c d β x y z w r s hD
    (f ∘ₗ (tensorPentagonShort hC2 N P Q R).1)).of_norm
  have he := pentagon_evaluation hC2 N P Q R a b c d β x y z w r s hD f
  unfold fivePointEvaluation at he ⊢
  refine (tsum_congr fun q => ?_).trans ((Summable.tsum_sub hLs hSs).trans (sub_eq_zero.mpr he))
  simp only [fivePointTerm]
  exact map_sub f _ _

end VOA.LogTensor.LogModuleCat
