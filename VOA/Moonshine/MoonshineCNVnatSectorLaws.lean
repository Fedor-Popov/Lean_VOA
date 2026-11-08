import VOA.Moonshine.MoonshineCNVnatSectorGrading

/-! # Weight and form laws for the concrete string operators -/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open AutMonster TensorFieldLift
open scoped TensorProduct

def vnatHypLongitudinal (a : Fin 2) (κ ell : ℂ) (n : ℤ) :
    Module.End ℂ (Vnat ⊗[ℂ] hypFock) :=
  (hypOscillator a (if a = 0 then κ else ell) n).lTensor Vnat

theorem vnatSectorWeight_mode (x y n N : ℤ) (u : Vnat ⊗[ℂ] hypFock)
    (hu : u ∈ vnatSectorWeight x y N) :
    vnatHypMode x y n u ∈ vnatSectorWeight x y (N - n) := by
  rw [vnatSectorWeight_eq_eigenspace, Module.End.mem_eigenspace_iff]
  have h := LinearMap.congr_fun (vnatHypMode_virasoro x y 0 n) u
  simp only [Int.cast_zero, zero_pow (by decide : (3 : ℕ) ≠ 0), sub_self, zero_div,
    zero_mul, zero_smul, ite_self, zero_sub, zero_add, add_zero,
    LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
  rw [vnatSectorWeight_energy x y N u hu, map_smul] at h
  calc
    _ = -(n : ℂ) • vnatHypMode x y n u + (N : ℂ) • vnatHypMode x y n u :=
      sub_eq_iff_eq_add.mp h
    _ = _ := by rw [← add_smul]; congr 1; push_cast; ring

theorem vnatSectorWeight_oscillator (x y n N : ℤ) (a : Fin 2)
    (u : Vnat ⊗[ℂ] hypFock) (hu : u ∈ vnatSectorWeight x y N) :
    vnatHypLongitudinal a x y n u ∈ vnatSectorWeight x y (N - n) := by
  induction hu using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨i, j, v, p, hv, hp, hij, rfl⟩ := ht
    change v ⊗ₜ[ℂ] hypOscillator a _ n p ∈ _
    convert vnatSectorWeight_tmul x y i (j - n) v _ hv
      (hypOscillator_mem_level a _ n j p hp) using 1
    congr 1
    omega
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [map_smul]; exact Submodule.smul_mem _ c hu

theorem vnatSectorWeight_orthogonal (x y N Q : ℤ) (u v : Vnat ⊗[ℂ] hypFock)
    (hNQ : N ≠ Q) (hu : u ∈ vnatSectorWeight x y N)
    (hv : v ∈ vnatSectorWeight x y Q) : vnatHypForm u v = 0 := by
  have h := vnatHypForm_adjoint x y 0 u v
  rw [neg_zero, vnatSectorWeight_energy x y N u hu,
    vnatSectorWeight_energy x y Q v hv, LinearMap.map_smul₂, map_smul,
    smul_eq_mul, smul_eq_mul] at h
  exact (mul_eq_zero.mp (show ((N : ℂ) - Q) * vnatHypForm u v = 0 by
    rw [sub_mul, h, sub_self])).resolve_left (sub_ne_zero.mpr (by exact_mod_cast hNQ))

theorem vnatSectorWeight_nondegenerate (x y N : ℤ) (u : Vnat ⊗[ℂ] hypFock)
    (hu : u ∈ vnatSectorWeight x y N)
    (hB : ∀ v ∈ vnatSectorWeight x y N, vnatHypForm u v = 0) : u = 0 := by
  by_contra h
  obtain ⟨v, hv⟩ := vnatHypForm_nondegenerate u h
  apply hv
  have hvtop : v ∈ ⨆ Q, vnatSectorWeight x y Q := by rw [vnatSectorWeight_top]; trivial
  refine Submodule.iSup_induction _ (motive := fun v => vnatHypForm u v = 0)
    hvtop ?_ (by simp) ?_
  · intro Q v hv
    by_cases hQ : N = Q
    · subst Q; exact hB v hv
    · exact vnatSectorWeight_orthogonal x y N Q u v hQ hu hv
  · intro v w hv hw; rw [map_add, hv, hw, add_zero]

theorem vnatHypLongitudinal_comm (a : Fin 2) (κ ell : ℂ) (m n : ℤ) :
    vnatHypLongitudinal a κ ell m * vnatHypLongitudinal a κ ell n =
      vnatHypLongitudinal a κ ell n * vnatHypLongitudinal a κ ell m := by
  have h : hypOscillator a (if a = 0 then κ else ell) m *
      hypOscillator a (if a = 0 then κ else ell) n =
    hypOscillator a (if a = 0 then κ else ell) n *
      hypOscillator a (if a = 0 then κ else ell) m := by
    apply sub_eq_zero.mp
    have h := hypOscillator_comm a a (if a = 0 then κ else ell)
      (if a = 0 then κ else ell) m n
    have ha : a ≠ a.rev := by fin_cases a <;> decide
    simpa only [ha, false_and, if_false, zero_smul] using h
  apply TensorProduct.ext'
  intro v p
  exact congrArg (fun f : Module.End ℂ hypFock => v ⊗ₜ[ℂ] f p) h

theorem vnatHypLongitudinal_mixed (a : Fin 2) (κ ell : ℂ) (m n : ℤ) :
    vnatHypMode κ ell m * vnatHypLongitudinal a κ ell n -
      vnatHypLongitudinal a κ ell n * vnatHypMode κ ell m =
      -(n : ℂ) • vnatHypLongitudinal a κ ell (m + n) := by
  have h := hypSugawara_oscillator_comm κ ell m a n
  apply TensorProduct.ext'
  intro v p
  have hp := LinearMap.congr_fun h p
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply] at hp
  simp only [vnatHypMode, vnatHypLongitudinal, tensorTranslation, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.add_apply, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul, map_add, LinearMap.smul_apply]
  rw [add_sub_add_left_eq_sub, ← TensorProduct.tmul_sub, hp, TensorProduct.tmul_smul]

theorem vnatHypLongitudinal_adjoint (a : Fin 2) (κ ell : ℂ) (n : ℤ)
    (u v : Vnat ⊗[ℂ] hypFock) :
    vnatHypForm (vnatHypLongitudinal a κ ell n u) v =
      vnatHypForm u (vnatHypLongitudinal a κ ell (-n) v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u w hu hw => simp only [map_add, LinearMap.add_apply, hu, hw]
  | tmul u p =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add v w hv hw => simp only [map_add, hv, hw]
    | tmul v q =>
      change hypForm (hypOscillator a _ n p) q * SimpleNat.natForm u v =
        hypForm p (hypOscillator a _ (-n) q) * SimpleNat.natForm u v
      rw [hypForm_oscillator_adjoint]

end VOA.Moonshine.ConwayNorton
