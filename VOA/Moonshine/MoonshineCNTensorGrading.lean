import VOA.Moonshine.MoonshineCNTensorConformal
import VOA.Core.TensorVOA
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! The internal convolution weight grading, including infinite weight spaces. -/

namespace VOA.Moonshine.ConwayNorton

open scoped TensorProduct
open Module (End)
open TensorFieldLift

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

theorem tensorFinsum_mem {ι M : Type*} [AddCommGroup M] [Module ℂ M]
    (S : Submodule ℂ M) (f : ι → M) (hf : ∀ i, f i ∈ S) : (∑ᶠ i, f i) ∈ S := by
  classical
  by_cases h : (Function.support f).Finite
  · rw [finsum_eq_finsetSum_of_support_subset f (s := h.toFinset) (by rw [h.coe_toFinset])]
    exact Submodule.sum_mem _ fun i _ => hf i
  · rw [finsum_of_infinite_support h]; exact S.zero_mem

/-- The span of pure tensors whose two integer weights add to `n`. -/
def nearTensorGrading (V : NearVOA A) (W : NearVOA B) (n : ℤ) :
    Submodule ℂ (A ⊗[ℂ] B) :=
  Submodule.span ℂ {t | ∃ (i j : ℤ) (a : A) (b : B),
    a ∈ V.grading i ∧ b ∈ W.grading j ∧ i + j = n ∧ a ⊗ₜ[ℂ] b = t}

theorem nearTensorGrading_tmul (V : NearVOA A) (W : NearVOA B)
    {i j : ℤ} {a : A} {b : B} (ha : a ∈ V.grading i) (hb : b ∈ W.grading j) :
    a ⊗ₜ[ℂ] b ∈ nearTensorGrading V W (i + j) :=
  Submodule.subset_span ⟨i, j, a, b, ha, hb, rfl, rfl⟩

theorem nearTensorGrading_induction (V : NearVOA A) (W : NearVOA B) {n : ℤ}
    {P : A ⊗[ℂ] B → Prop} (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (c : ℂ) x, P x → P (c • x))
    (hpure : ∀ (i j : ℤ) (a : A) (b : B), a ∈ V.grading i → b ∈ W.grading j →
      i + j = n → P (a ⊗ₜ[ℂ] b)) {u : A ⊗[ℂ] B} (hu : u ∈ nearTensorGrading V W n) : P u := by
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨i, j, a, b, ha, hb, hij, rfl⟩ := hx; exact hpure i j a b ha hb hij
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsmul c x hx

theorem nearTensorGrading_top (V : NearVOA A) (W : NearVOA B) :
    (⨆ n, nearTensorGrading V W n) = ⊤ := by
  apply TensorVA.eq_top_of_tmul_mem
    ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp V.isInternal).2
    ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp W.isInternal).2
  intro i j a ha b hb
  exact Submodule.mem_iSup_of_mem (i + j) (nearTensorGrading_tmul V W ha hb)

theorem nearTensorGrading_energy (V : NearVOA A) (W : NearVOA B)
    {n : ℤ} {u : A ⊗[ℂ] B} (hu : u ∈ nearTensorGrading V W n) :
    tensorTranslation (nearVirasoroMode V 0) (nearVirasoroMode W 0) u = (n : ℂ) • u := by
  refine nearTensorGrading_induction V W (P := fun u =>
    tensorTranslation (nearVirasoroMode V 0) (nearVirasoroMode W 0) u = (n : ℂ) • u)
    ?_ ?_ ?_ ?_ hu
  · simp
  · intro x y hx hy; simp only [map_add, hx, hy, smul_add]
  · intro c x hx; simp only [map_smul, hx, smul_comm c]
  · intro i j a b ha hb hij
    dsimp only
    simp only [tensorTranslation, LinearMap.add_apply, LinearMap.rTensor_tmul,
      LinearMap.lTensor_tmul, nearVirasoroMode, zero_add, V.L0_grading a ha,
      W.L0_grading b hb, TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    rw [← TensorProduct.add_tmul, ← add_smul, ← Int.cast_add, hij]

/-- Eigenvalues of the total `L₀` prove independence without a finite-fiber assumption. -/
theorem nearTensorGrading_isInternal (V : NearVOA A) (W : NearVOA B) :
    DirectSum.IsInternal (nearTensorGrading V W) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top _ (nearTensorGrading_top V W)
  have hi : iSupIndep (fun n : ℤ =>
      (tensorTranslation (nearVirasoroMode V 0) (nearVirasoroMode W 0)).eigenspace (n : ℂ)) :=
    (Module.End.eigenspaces_iSupIndep _).comp (fun i j h => by exact_mod_cast h)
  exact hi.mono fun n u hu => Module.End.mem_eigenspace_iff.mpr (nearTensorGrading_energy V W hu)

/-- Evaluating a state field at one formal exponent is linear in its state. -/
noncomputable def nearTensorCoefficient (V : NearVOA A) (W : NearVOA B) (s : ℤ) :
    A ⊗[ℂ] B →ₗ[ℂ] End ℂ (A ⊗[ℂ] B) where
  toFun u := nearTensorField V W u s
  map_add' u v := congrArg (fun f => f s) ((nearTensorField V W).map_add u v)
  map_smul' c u := congrArg (fun f => f s) ((nearTensorField V W).map_smul c u)

/-- Every tensor coefficient has the required total-weight shift. -/
theorem nearTensorGrading_mode (V : NearVOA A) (W : NearVOA B)
    {k l : ℤ} (u : A ⊗[ℂ] B) (hu : u ∈ nearTensorGrading V W k)
    (v : A ⊗[ℂ] B) (hv : v ∈ nearTensorGrading V W l) (n : ℤ) :
    mode (nearTensorField V W u) n v ∈ nearTensorGrading V W (k + l - n - 1) := by
  change nearTensorCoefficient V W (-n - 1) u v ∈ _
  refine nearTensorGrading_induction V W
    (P := fun u => nearTensorCoefficient V W (-n - 1) u v ∈
      nearTensorGrading V W (k + l - n - 1)) ?_ ?_ ?_ ?_ hu
  · dsimp only
    rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  · intro x y hx hy
    rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hy
  · intro c x hx
    rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ c hx
  · intro i j a b ha hb hij
    refine nearTensorGrading_induction V W
      (P := fun v => nearTensorCoefficient V W (-n - 1) (a ⊗ₜ b) v ∈
        nearTensorGrading V W (k + l - n - 1)) ?_ ?_ ?_ ?_ hv
    · dsimp only
      rw [map_zero]; exact Submodule.zero_mem _
    · intro x y hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro c x hx; rw [map_smul]; exact Submodule.smul_mem _ c hx
    · intro i' j' a' b' ha' hb' hij'
      change nearTensorField V W (a ⊗ₜ b) (-n - 1) (a' ⊗ₜ b') ∈ _
      rw [nearTensorField_tmul_apply]
      apply tensorFinsum_mem
      intro m
      have hA := V.grading_mode a ha a' ha' (-m - 1)
      have hB := W.grading_mode b hb b' hb' (-(-n - 1 - m) - 1)
      simp only [mode_apply, show -(-m - 1) - 1 = m from by omega] at hA
      simp only [mode_apply, show -(-(-n - 1 - m) - 1) - 1 = -n - 1 - m from by omega] at hB
      convert nearTensorGrading_tmul V W hA hB using 1 <;> congr 1 <;> omega

end VOA.Moonshine.ConwayNorton
