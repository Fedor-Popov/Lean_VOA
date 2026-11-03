import VOA.Classification.COne.McRaeM2LogBraidedCurves
import VOA.Classification.COne.McRaeM2LogBraidedGlue
import VOA.Classification.COne.McRaeM2LogBraidedIso
import VOA.Huang.LogAssocTensorAssociatorEvaluation
import VOA.Huang.LogAssocTensorIterateFaithful

/-! # The four expansions of the logarithmic hexagon

For finite logarithmic modules `X = N₁`, `Y = N₂`, `Z = N₃` and a branch `r` of the
swap, the two hexagon paths `(X ⊠ Y) ⊠ Z → Y ⊠ (Z ⊠ X)` are `hexLeft r`
(`α ≫ c_{X,Y⊠Z} ≫ α`) and `hexRight r` (`(c_{X,Y} ▷ Z) ≫ α ≫ (Y ◁ c_{X,Z})`).
Tested on a completed canonical iterate with `x` at `1+u`, `y` at `1`, `z` at `0`:

* the left path is `hexFA` (iterates of `Y⊠Z` with `X`, outer branch
  `log(1+u)+κ_r`), via associativity and the product side of skew-symmetry
  (`hexLeft_iterate`);
* the right path is `hexFD` (iterates of `Y⊠X` with `Z`, inner branch
  `log u + κ_r`, outer `log(1+u)`), via the inner translation theorem, for
  `|u| < 1/2` (`hexRight_iterate`);
* `hexFB` and `hexFC` are the two product expansions into `Y ⊠ (Z ⊠ X)`, related to
  `hexFA` and `hexFD` by associativity at shifted branches (`hexFA_eq_hexFB`,
  `hexFC_eq_hexFD`). -/
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 4000000
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open VOA.Classification.COne VOA.Classification.COne.McRaeM1
open VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.LogAssocExpansion VOA.Huang.LogBraided
open VOA.Huang.AssocExpansion
open scoped BigOperators
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule) (h₃ : FinGen N₃.toWeakModule)

/-- The left hexagon path `α_{Y,Z,X} ∘ c_{X,Y⊠Z} ∘ α_{X,Y,Z}`. -/
def hexLeft (r : ℤ) : (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃).toWeakModule.Hom
    (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁).toWeakModule :=
  homComp (tensorAssociatorHom hC2 N₂ N₃ N₁ h₂ h₃ h₁)
    (homComp (tensorBraid hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃) h₁
      (tensorModule_finGen hC2 N₂ N₃ h₂ h₃) r) (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃))

/-- `Y ◁ c_{X,Z}`. -/
def hexWhiskerLeft (r : ℤ) : (tensorModule hC2 N₂ (tensorModule hC2 N₁ N₃ h₁ h₃) h₂
      (tensorModule_finGen hC2 N₁ N₃ h₁ h₃)).toWeakModule.Hom
    (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁).toWeakModule :=
  tensorMap hC2 N₂ (tensorModule hC2 N₁ N₃ h₁ h₃) h₂ (tensorModule_finGen hC2 N₁ N₃ h₁ h₃)
    N₂ (tensorModule hC2 N₃ N₁ h₃ h₁) h₂ (tensorModule_finGen hC2 N₃ N₁ h₃ h₁)
    (weakIdentity N₂.toWeakModule) (tensorBraid hC2 N₁ N₃ h₁ h₃ r)

/-- `c_{X,Y} ▷ Z`. -/
def hexWhiskerRight (r : ℤ) : (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃).toWeakModule.Hom
    (leftTripleModule hC2 N₂ N₁ h₂ h₁ N₃ h₃).toWeakModule :=
  tensorMap hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃ (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃
    (tensorModule hC2 N₂ N₁ h₂ h₁) N₃ (tensorModule_finGen hC2 N₂ N₁ h₂ h₁) h₃
    (tensorBraid hC2 N₁ N₂ h₁ h₂ r) (weakIdentity N₃.toWeakModule)

/-- The right hexagon path `(Y ◁ c_{X,Z}) ∘ α_{Y,X,Z} ∘ (c_{X,Y} ▷ Z)`. -/
def hexRight (r : ℤ) : (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃).toWeakModule.Hom
    (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁).toWeakModule :=
  homComp (hexWhiskerLeft hC2 N₁ N₂ N₃ h₁ h₂ h₃ r)
    (homComp (tensorAssociatorHom hC2 N₂ N₁ N₃ h₂ h₁ h₃) (hexWhiskerRight hC2 N₁ N₂ N₃ h₁ h₂ h₃ r))

/-- The outer branch `λ₂(u) = log(1+u) + κ_r` of the left path. -/
def hexL2 (r : ℤ) (u : ℂ) : ℂ := Complex.log (1+u) + kap r

/-- The first branch `λ₁(u) = log(1 + e^{-λ₂}) + λ₂` of the left products. -/
def hexL1 (r : ℤ) (u : ℂ) : ℂ := Complex.log (1+Complex.exp (-hexL2 r u)) + hexL2 r u

/-- The left path expansion: `L(−1)`-sums of iterates of `Y ⊠ Z` with `X`. -/
def hexFA (r : ℤ) (f : RestrictedDual (rightTripleDual hC2 N₂ N₃ h₂ h₃ N₁ h₁).toGW →ₗ[ℂ] ℂ)
    {a : ℂ} (β : ℂ) {x : M₁} (y : M₂) (z : M₃) (hx : x∈N₁.weight a) (J : ℕ) (u : ℂ) : ℂ :=
  ∑ j∈Finset.range J, transCoeff (Complex.log (1+u)) j *
    completedLogIterate N₂ N₃ N₁ (leftTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁)
      (tensorModule hC2 N₂ N₃ h₂ h₃)
      (tensorIntertwiner hC2 (tensorModule hC2 N₂ N₃ h₂ h₃) N₁
        (tensorModule_finGen hC2 N₂ N₃ h₂ h₃) h₁)
      (tensorIntertwiner hC2 N₂ N₃ h₂ h₃) 0 (hexL2 r u) a (β-j)
      ((f ∘ₗ (Lm1 (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁).toWeakModule ^ j)) ∘ₗ
        (tensorAssociatorHom hC2 N₂ N₃ N₁ h₂ h₃ h₁).toLinearMap) y z ⟨x,hx⟩

/-- The left path products into `Y ⊠ (Z ⊠ X)`. -/
def hexFB (r : ℤ) (f : RestrictedDual (rightTripleDual hC2 N₂ N₃ h₂ h₃ N₁ h₁).toGW →ₗ[ℂ] ℂ)
    {b : ℂ} (β : ℂ) (x : M₁) {y : M₂} (z : M₃) (hy : y∈N₂.weight b) (J : ℕ) (u : ℂ) : ℂ :=
  ∑ j∈Finset.range J, transCoeff (Complex.log (1+u)) j *
    completedLogProduct N₂ N₃ N₁ (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁)
      (tensorModule hC2 N₃ N₁ h₃ h₁)
      (tensorIntertwiner hC2 N₂ (tensorModule hC2 N₃ N₁ h₃ h₁) h₂
        (tensorModule_finGen hC2 N₃ N₁ h₃ h₁))
      (tensorIntertwiner hC2 N₃ N₁ h₃ h₁) (hexL1 r u) (hexL2 r u) b (β-j)
      (f ∘ₗ (Lm1 (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁).toWeakModule ^ j)) ⟨y,hy⟩ z x

/-- The right path product into `Y ⊠ (Z ⊠ X)`, with the braided inner operator. -/
def hexFC (r : ℤ) (f : RestrictedDual (rightTripleDual hC2 N₂ N₃ h₂ h₃ N₁ h₁).toGW →ₗ[ℂ] ℂ)
    {b : ℂ} (β : ℂ) (x : M₁) {y : M₂} (z : M₃) (hy : y∈N₂.weight b) (u : ℂ) : ℂ :=
  completedLogProduct N₂ N₁ N₃ (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁)
    (tensorModule hC2 N₃ N₁ h₃ h₁)
    (tensorIntertwiner hC2 N₂ (tensorModule hC2 N₃ N₁ h₃ h₁) h₂
      (tensorModule_finGen hC2 N₃ N₁ h₃ h₁))
    (omegaEquiv N₃.toWeakModule N₁.toWeakModule (tensorModule hC2 N₃ N₁ h₃ h₁).toWeakModule r
      (tensorIntertwiner hC2 N₃ N₁ h₃ h₁)) 0 (Complex.log (1+u)) b β f ⟨y,hy⟩ x z

/-- The right path expansion: iterates of `Y ⊠ X` with `Z`. -/
def hexFD (r : ℤ) (f : RestrictedDual (rightTripleDual hC2 N₂ N₃ h₂ h₃ N₁ h₁).toGW →ₗ[ℂ] ℂ)
    {c : ℂ} (β : ℂ) (x : M₁) (y : M₂) {z : M₃} (hz : z∈N₃.weight c) (u : ℂ) : ℂ :=
  completedLogIterate N₂ N₁ N₃ (leftTripleModule hC2 N₂ N₁ h₂ h₁ N₃ h₃)
    (tensorModule hC2 N₂ N₁ h₂ h₁)
    (tensorIntertwiner hC2 (tensorModule hC2 N₂ N₁ h₂ h₁) N₃
      (tensorModule_finGen hC2 N₂ N₁ h₂ h₁) h₃)
    (tensorIntertwiner hC2 N₂ N₁ h₂ h₁) (Complex.log u + kap r) (Complex.log (1+u)) c β
    ((f ∘ₗ (hexWhiskerLeft hC2 N₁ N₂ N₃ h₁ h₂ h₃ r).toLinearMap) ∘ₗ
      (tensorAssociatorHom hC2 N₂ N₁ N₃ h₂ h₁ h₃).toLinearMap) y x ⟨z,hz⟩

/-! ## Elementary facts about the test points -/

theorem re_exp_pos_of_overlap {t : ℂ} (ht : t∈overlapDomain) : 0 < (Complex.exp t).re := by
  rw [Complex.exp_re]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
  · have := (abs_lt.mp ht.2).1; linarith
  · exact (abs_lt.mp ht.2).2

theorem one_lt_norm_one_add_exp {t : ℂ} (ht : t∈overlapDomain) : 1 < ‖1+Complex.exp t‖ := by
  have h := re_exp_pos_of_overlap ht
  refine lt_of_lt_of_le ?_ (Complex.re_le_norm _)
  simp only [Complex.add_re, Complex.one_re]; linarith

theorem log_exp_of_overlap {t : ℂ} (ht : t∈overlapDomain) : Complex.log (Complex.exp t) = t := by
  have h := abs_lt.mp ht.2
  refine Complex.log_exp ?_ ?_
  · linarith [Real.pi_pos]
  · linarith [Real.pi_pos]

/-! ## The two paths on a completed iterate -/

theorem homComp_toLinearMap {X₁ X₂ X₃ : Type u} [AddCommGroup X₁] [Module ℂ X₁]
    [AddCommGroup X₂] [Module ℂ X₂] [AddCommGroup X₃] [Module ℂ X₃]
    {A : WeakModule W X₁} {B : WeakModule W X₂} {C : WeakModule W X₃}
    (g : B.Hom C) (f : A.Hom B) : (homComp g f).toLinearMap = g.toLinearMap ∘ₗ f.toLinearMap :=
  rfl

/-- **The left path on a completed iterate** is `hexFA` at `u = e^t`. -/
theorem hexLeft_iterate (r : ℤ)
    (f : RestrictedDual (rightTripleDual hC2 N₂ N₃ h₂ h₃ N₁ h₁).toGW →ₗ[ℂ] ℂ)
    {a b c : ℂ} (β : ℂ) {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c) (J : ℕ)
    (hJ : ∀ j : ℕ, J ≤ j → (leftTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁).weight (β-j) = ⊥)
    {t : ℂ} (ht : t∈overlapDomain) :
    completedLogIterate N₁ N₂ N₃ (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
        (tensorModule hC2 N₁ N₂ h₁ h₂)
        (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
          (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃)
        (tensorIntertwiner hC2 N₁ N₂ h₁ h₂) t 0 c β
        (f ∘ₗ (hexLeft hC2 N₁ N₂ N₃ h₁ h₂ h₃ r).toLinearMap) x y ⟨z,hz⟩ =
      hexFA hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β y z hx J (Complex.exp t) := by
  have hA := tensorAssociatorHom_completed_shift (β := β) hC2 N₁ N₂ N₃ h₁ h₂ h₃ hx hy hz
    (f ∘ₗ (homComp (tensorAssociatorHom hC2 N₂ N₃ N₁ h₂ h₃ h₁)
      (tensorBraid hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃) h₁
        (tensorModule_finGen hC2 N₂ N₃ h₂ h₃) r)).toLinearMap) ht 0
  simp only [add_zero] at hA
  have hL : f ∘ₗ (hexLeft hC2 N₁ N₂ N₃ h₁ h₂ h₃ r).toLinearMap =
      (f ∘ₗ (homComp (tensorAssociatorHom hC2 N₂ N₃ N₁ h₂ h₃ h₁)
        (tensorBraid hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃) h₁
          (tensorModule_finGen hC2 N₂ N₃ h₂ h₃) r)).toLinearMap) ∘ₗ
        (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap := rfl
  rw [hL, ← hA]
  have hP := completedLogProduct_postcompose N₁ N₂ N₃
    (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃) (tensorModule hC2 N₂ N₃ h₂ h₃)
    (leftTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁)
    (tensorBraid hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃) h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃) r)
    (tensorIntertwiner hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃) h₁
      (tensorModule_finGen hC2 N₂ N₃ h₂ h₃))
    (tensorIntertwiner hC2 N₂ N₃ h₂ h₃) (Complex.log (1+Complex.exp t)) 0 a β
    (f ∘ₗ (tensorAssociatorHom hC2 N₂ N₃ N₁ h₂ h₃ h₁).toLinearMap) ⟨x,hx⟩ y z
  rw [tensorBraid_intertwiner] at hP
  rw [homComp_toLinearMap, ← LinearMap.comp_assoc, ← hP]
  have hlt : (0 : ℂ).re < (Complex.log (1+Complex.exp t)).re := by
    rw [Complex.zero_re, Complex.log_re]
    exact Real.log_pos (one_lt_norm_one_add_exp ht)
  rw [completedLogProduct_omega hC2 N₁ N₂ N₃ (leftTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁)
    (tensorModule hC2 N₂ N₃ h₂ h₃) h₁ h₂ h₃ (tensorModule_finGen hC2 _ N₁
      (tensorModule_finGen hC2 N₂ N₃ h₂ h₃) h₁) (tensorModule_finGen hC2 N₂ N₃ h₂ h₃)
    _ _ r hx hy hz _ β hlt J hJ]
  unfold hexFA
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  apply LinearMap.ext
  intro q
  simp only [LinearMap.comp_apply]
  rw [hom_Lm1_pow]

/-- **The right path on a completed iterate** is `hexFD` at `u = e^t`, for `|e^t| < 1/2`. -/
theorem hexRight_iterate (r : ℤ)
    (f : RestrictedDual (rightTripleDual hC2 N₂ N₃ h₂ h₃ N₁ h₁).toGW →ₗ[ℂ] ℂ)
    {a b c : ℂ} (β : ℂ) {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    {t : ℂ} (ht : t∈overlapDomain) (ht2 : ‖Complex.exp t‖ < 1/2) :
    completedLogIterate N₁ N₂ N₃ (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
        (tensorModule hC2 N₁ N₂ h₁ h₂)
        (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
          (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃)
        (tensorIntertwiner hC2 N₁ N₂ h₁ h₂) t 0 c β
        (f ∘ₗ (hexRight hC2 N₁ N₂ N₃ h₁ h₂ h₃ r).toLinearMap) x y ⟨z,hz⟩ =
      hexFD hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β x y hz (Complex.exp t) := by
  have hR : f ∘ₗ (hexRight hC2 N₁ N₂ N₃ h₁ h₂ h₃ r).toLinearMap =
      ((f ∘ₗ (hexWhiskerLeft hC2 N₁ N₂ N₃ h₁ h₂ h₃ r).toLinearMap) ∘ₗ
        (tensorAssociatorHom hC2 N₂ N₁ N₃ h₂ h₁ h₃).toLinearMap) ∘ₗ
        (hexWhiskerRight hC2 N₁ N₂ N₃ h₁ h₂ h₃ r).toLinearMap := rfl
  rw [hR, ← completedLogIterate_postcompose]
  rw [hexWhiskerRight, tensorMap_intertwiner, completedLogIterate_precompose_left,
    tensorBraid_intertwiner]
  rw [completedLogIterate_omega_inner hC2 N₁ N₂ N₃ (leftTripleModule hC2 N₂ N₁ h₂ h₁ N₃ h₃)
    (tensorModule hC2 N₂ N₁ h₂ h₁) h₁ h₂ h₃
    (tensorModule_finGen hC2 _ N₃ (tensorModule_finGen hC2 N₂ N₁ h₂ h₁) h₃)
    (tensorModule_finGen hC2 N₂ N₁ h₂ h₁) _ _ r hx hy hz _ β (by simpa using ht2)]
  unfold hexFD
  rw [log_exp_of_overlap ht]
  simp only [sub_zero, zero_add]

/-! ## Associativity between the expansions -/

/-- `hexFA = hexFB` where the rotated outer branch lies in the overlap chart. -/
theorem hexFA_eq_hexFB (r : ℤ)
    (f : RestrictedDual (rightTripleDual hC2 N₂ N₃ h₂ h₃ N₁ h₁).toGW →ₗ[ℂ] ℂ)
    {a b c : ℂ} (β : ℂ) {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c) (J : ℕ) {u : ℂ}
    (hu : -hexL2 r u∈overlapDomain) :
    hexFA hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β y z hx J u =
      hexFB hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β x z hy J u := by
  unfold hexFA hexFB
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have h := tensorAssociatorHom_completed_shift (β := β-j) hC2 N₂ N₃ N₁ h₂ h₃ h₁ hy hz hx
    (f ∘ₗ (Lm1 (rightTripleModule hC2 N₂ N₃ h₂ h₃ N₁ h₁).toWeakModule ^ j)) hu (hexL2 r u)
  rw [neg_add_cancel] at h
  exact h.symm

/-- `hexFC = hexFD` where the right path branch lies in the overlap chart. -/
theorem hexFC_eq_hexFD (r : ℤ)
    (f : RestrictedDual (rightTripleDual hC2 N₂ N₃ h₂ h₃ N₁ h₁).toGW →ₗ[ℂ] ℂ)
    {a b c : ℂ} (β : ℂ) {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c) {u : ℂ}
    (hu : Complex.log u + kap r - Complex.log (1+u)∈overlapDomain)
    (hbr : Complex.log (1+Complex.exp (Complex.log u + kap r - Complex.log (1+u))) +
      Complex.log (1+u) = 0) :
    hexFC hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β x z hy u =
      hexFD hC2 N₁ N₂ N₃ h₁ h₂ h₃ r f β x y hz u := by
  have h := tensorAssociatorHom_completed_shift (β := β) hC2 N₂ N₁ N₃ h₂ h₁ h₃ hy hx hz
    (f ∘ₗ (hexWhiskerLeft hC2 N₁ N₂ N₃ h₁ h₂ h₃ r).toLinearMap) hu (Complex.log (1+u))
  rw [show Complex.log u + kap r - Complex.log (1+u) + Complex.log (1+u) =
    Complex.log u + kap r by ring, hbr] at h
  unfold hexFD
  rw [← h, ← completedLogProduct_postcompose, hexWhiskerLeft, tensorMap_intertwiner,
    completedLogProduct_precompose_right, tensorBraid_intertwiner]
  rfl

end VOA.C2Rigid.LocalInjective
