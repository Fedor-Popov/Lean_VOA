import VOA.Moonshine.MoonshineCNSectorVirasoroOperators

/-! All-mode Virasoro intertwining and exact weight compatibility for actual sectors. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

open IntegralLattice HeisenbergN LatGen Nondeg MvPolynomial AutMonster TensorFieldLift
open scoped TensorProduct

theorem hypLorentzianPolynomial_virasoro_nonnegative (x y n : ℤ) (hn : 0 ≤ n)
    (p : hypFock) :
    hypLorentzianPolynomialEquiv (hypSugawara x y n p) =
      lorentzianSectorVirasoro ![x, y] n (hypLorentzianPolynomialEquiv p) := by
  have hv : hypSugawara x y n 1 = if n = 0 then ((x : ℂ) * y) • 1 else 0 := by
    by_cases h : n = 0
    · subst n; simp [hypSugawara_zero_vacuum]
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = (j + 1 : ℤ) := ⟨(n - 1).toNat, by omega⟩
      rw [hypSugawara_positive_vacuum, if_neg (by omega)]
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [C_eq_smul_one, LinearMap.map_smul, map_smul hypLorentzianPolynomialEquiv,
      map_smul hypLorentzianPolynomialEquiv,
      map_one hypLorentzianPolynomialEquiv, LinearMap.map_smul,
      lorentzianSectorVirasoro_nonnegative_one x y n hn, hv]
    split_ifs <;> simp only [map_smul, map_one, map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [mul_comm p (X v), lorentzianSectorVirasoro_creation]
    have hh := LinearMap.congr_fun
      (hypSugawara_oscillator_comm x y n v.2 (-(v.1 + 1 : ℤ))) p
    simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
      hypOscillator_negative_apply, LinearMap.smul_apply,
      Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, neg_neg,
      ← sub_eq_add_neg] at hh
    rw [sub_eq_iff_eq_add] at hh
    rw [hh, map_add, map_smul, ← hp]
    congr 1
    simpa only [hypOscillator_negative_apply] using
      (hypLorentzianPolynomial_creation v.2 0 v.1 (hypSugawara x y n p))

/-- Every integer mode, with negative modes recovered by the proved bilinear adjoints. -/
theorem hypLorentzianPolynomial_virasoro (x y n : ℤ) (p : hypFock) :
    hypLorentzianPolynomialEquiv (hypSugawara x y n p) =
      lorentzianSectorVirasoro ![x, y] n (hypLorentzianPolynomialEquiv p) := by
  by_cases hn : 0 ≤ n
  · exact hypLorentzianPolynomial_virasoro_nonnegative x y n hn p
  have hall (q : hypFock) :
      hypForm (hypLorentzianPolynomialEquiv.symm
        (lorentzianSectorVirasoro ![x, y] n (hypLorentzianPolynomialEquiv p))) q =
      hypForm (hypSugawara x y n p) q := by
    rw [← hypLorentzianPolynomial_form, AlgEquiv.apply_symm_apply,
      lorentzianSectorVirasoro_adjoint,
      ← hypLorentzianPolynomial_virasoro_nonnegative x y (-n) (by omega),
      hypLorentzianPolynomial_form, hypForm_sugawara_adjoint]
  have he : hypLorentzianPolynomialEquiv.symm
      (lorentzianSectorVirasoro ![x, y] n (hypLorentzianPolynomialEquiv p)) =
        hypSugawara x y n p := by
    apply sub_eq_zero.mp
    by_contra h
    obtain ⟨q, hq⟩ := hypForm_nondegenerate _ h
    apply hq
    rw [map_sub, LinearMap.sub_apply, hall, sub_self]
  have he' := congrArg hypLorentzianPolynomialEquiv he
  simpa only [AlgEquiv.apply_symm_apply] using he'.symm

theorem moonshineMatterSectorMap_virasoro (x y n : ℤ) (u : Vnat ⊗[ℂ] hypFock) :
    moonshineMatterSectorMap ![x, y] (vnatHypMode x y n u) =
      moonshineMatterNearVOA.L n (moonshineMatterSectorMap ![x, y] u) := by
  have he : moonshineMatterNearVOA.L n =
      tensorTranslation (nearVirasoroMode VnatVOA.toNearVOA n)
        (nearVirasoroMode lorentzianNearVOA n) := nearTensorField_conformal_mode _ _ n
  rw [he]
  induction u using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero]
  | add u v hu hv => simp only [LinearMap.map_add, hu, hv]
  | tmul v p =>
    simp only [vnatHypMode, tensorTranslation, LinearMap.add_apply,
      LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, LinearMap.map_add,
      moonshineMatterSectorMap_tmul]
    congr 1
    rw [hypLorentzianPolynomial_virasoro]
    exact congrArg (fun z => v ⊗ₜ[ℂ] z) (lorentzianSectorVirasoro_tmul ![x, y] n _).symm

/-- The requested intertwining on the concrete matter equivalence. -/
theorem moonshineMatterSectorEquiv_virasoro (x y n : ℤ) (u : Vnat ⊗[ℂ] hypFock) :
    (moonshineMatterSectorEquiv ![x, y] (vnatHypMode x y n u) : moonshineMatterSpace) =
      moonshineMatterNearVOA.L n (moonshineMatterSectorEquiv ![x, y] u) :=
  moonshineMatterSectorMap_virasoro x y n u

theorem moonshineMatterSectorMap_injective (α : lorentzianLattice.carrier) :
    Function.Injective (moonshineMatterSectorMap α) :=
  (show Function.LeftInverse (moonshineMatterSectorInverse α) (moonshineMatterSectorMap α)
    from moonshineMatterSector_leftInverse α).injective

end VOA.Moonshine.ConwayNorton

namespace VOA.NearVOA

theorem grading_eq_virasoroZero_eigenspace {H : Type*} [AddCommGroup H] [Module ℂ H]
    (W : NearVOA H) (N : ℤ) : W.grading N = (W.L 0).eigenspace (N : ℂ) := by
  have h := VOA.Deform.iSup_inf_eq_of_le_independent (p := W.grading)
    (q := fun Q : ℤ => (W.L 0).eigenspace (Q : ℂ))
    (fun Q u hu => Module.End.mem_eigenspace_iff.mpr (W.L0_grading u hu))
    ((Module.End.eigenspaces_iSupIndep _).comp
      (show Function.Injective (fun n : ℤ => (n : ℂ)) from Int.cast_injective)) N
  simpa only [W.isInternal.submodule_iSup_eq_top, top_inf_eq] using h.symm

end VOA.NearVOA

namespace VOA.Moonshine.ConwayNorton
open AutMonster
open scoped TensorProduct

/-- Exact equivalence of weights, with the half-norm shift `x*y`. -/
theorem moonshineMatterSector_weight_iff (x y N : ℤ) (u : Vnat ⊗[ℂ] hypFock) :
    moonshineMatterSectorMap ![x, y] u ∈ moonshineMatterNearVOA.grading N ↔
      u ∈ vnatSectorWeight x y N := by
  rw [moonshineMatterNearVOA.grading_eq_virasoroZero_eigenspace,
    vnatSectorWeight_eq_eigenspace, Module.End.mem_eigenspace_iff,
    Module.End.mem_eigenspace_iff, ← moonshineMatterSectorMap_virasoro,
    ← LinearMap.map_smul]
  exact (moonshineMatterSectorMap_injective ![x, y]).eq_iff

end VOA.Moonshine.ConwayNorton
