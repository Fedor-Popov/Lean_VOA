/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeTwistedJacobi
import VOA.Moonshine.HeisenbergTwistedModuleInstance

/-!
# The `L₀`-grading of the lattice twisted module  (Moonshine step M6)

* `prod_rTFld` — tensoring a field with `T` is a homomorphism for **all** field products
  (the nonnegative ones were `prod_rTFld_nonneg`); hence for the twisted products
  (`rTFld_star`).
* `FL_charge_zero` — on the charge-zero sector the lattice twisted vertex operator is the
  Heisenberg one tensored with `T`: `F_e(p ⊗ e^0) = F_e^{Heis}(p) ⊗ 1`.
* `YML_omega_two` — `Y^T(ω)₍₁₎ = L0T ⊗ 1` (the twisted Virasoro zero mode, with the `r/16`
  of the twisted vacuum).
* `GT d = S[θ]_d ⊗ T`, `weightLT α` — the `L₀`-eigenspace decomposition of `S[θ] ⊗ T`: internal
  (`weightLT_isInternal`), finite-dimensional (`T` is), bounded below by `rank/16`.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA.Moonshine.LatticeTwisted

open MvPolynomial TwistedHeisenberg TwistedReduction HeisenbergN
open Module (End)
open scoped BigOperators TensorProduct

section RT

variable {r : ℕ} {Tm : Type*} [AddCommGroup Tm] [Module ℂ Tm]

theorem mode_rTFld (A : Fld (FockT r)) (n : ℤ) :
    mode (rTFld (Tm := Tm) A).1 n = (mode A.1 n).rTensor Tm := rfl

theorem rTFld_add (A B : Fld (FockT r)) :
    rTFld (Tm := Tm) (A + B) = rTFld A + rTFld B := by
  apply Subtype.ext; funext n
  change ((A.1 n + B.1 n)).rTensor Tm = (A.1 n).rTensor Tm + (B.1 n).rTensor Tm
  rw [LinearMap.rTensor_add]

theorem rTFld_sum {ι : Type*} (s : Finset ι) (f : ι → Fld (FockT r)) :
    rTFld (Tm := Tm) (∑ i ∈ s, f i) = ∑ i ∈ s, rTFld (f i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, rTFld_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, rTFld_add, ih]

/-- Tensoring with `T` is a homomorphism for all field products. -/
theorem prod_rTFld (ℓ : ℤ) (A B : Fld (FockT r)) :
    Fld.prod ℓ (rTFld (Tm := Tm) A) (rTFld B) = rTFld (Fld.prod ℓ A B) := by
  apply fld_ext_mode
  intro N x
  rw [mode_rTFld]
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul y t =>
      obtain ⟨K1, hK1⟩ := Fld.mode_eventually_zero B y
      obtain ⟨K2, hK2⟩ := Fld.mode_eventually_zero A y
      set J : ℕ := (K1 - N).toNat + K2.toNat + 1 with hJ
      rw [Fld.mode_prod_iterate, LinearMap.rTensor_tmul, Fld.mode_prod_iterate,
        finsum_eq_sum_of_support_subset _ (s := Finset.range J) (by
          intro j hj
          rw [Function.mem_support] at hj
          simp only [Finset.coe_range, Set.mem_Iio]
          by_contra hc
          refine hj ?_
          simp only [mode_rTFld, LinearMap.rTensor_tmul]
          rw [hK1 _ (by omega), hK2 _ (by omega)]
          simp),
        finsum_eq_sum_of_support_subset _ (s := Finset.range J) (by
          intro j hj
          rw [Function.mem_support] at hj
          simp only [Finset.coe_range, Set.mem_Iio]
          by_contra hc
          refine hj ?_
          rw [hK1 _ (by omega), hK2 _ (by omega)]
          simp),
        TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [mode_rTFld, LinearMap.rTensor_tmul]
      rw [← TensorProduct.smul_tmul', TensorProduct.sub_tmul, ← TensorProduct.smul_tmul']

theorem rTFld_star (α : ℂ) {A X : Fld (FockT r)} (h : Local A.1 X.1) (p : ℤ) :
    star α (rTFld (Tm := Tm) A) p (rTFld X) = rTFld (star α A p X) := by
  obtain ⟨K, hK⟩ := exists_prod_offset_zero h p
  rw [star_eq_sum_range α A p X K hK, star_eq_sum_range α (rTFld A) p (rTFld X) K
    (fun i hi => by rw [prod_rTFld, hK i hi, rTFld_zero]), rTFld_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rTFld_smul, rTFld_fzmul, prod_rTFld]

end RT

section Grading

variable (r : ℕ) (Tm : Type*) [AddCommGroup Tm] [Module ℂ Tm]

/-- The doubled-weight-`d` piece `S[θ]_d ⊗ T`. -/
noncomputable def GT (d : ℕ) : Submodule ℂ (FockT r ⊗[ℂ] Tm) :=
  LinearMap.range ((gradingT r d).subtype.rTensor Tm)

theorem GT_le_eigenspace (d : ℕ) :
    GT r Tm d ≤ Module.End.eigenspace ((L0T r).rTensor Tm) ((levelT r d : ℚ) : ℂ) := by
  rintro x ⟨y, rfl⟩
  have h : L0T r ∘ₗ (gradingT r d).subtype = ((levelT r d : ℚ) : ℂ) • (gradingT r d).subtype := by
    exact LinearMap.ext fun p => L0T_of_mem_gradingT p.2
  rw [Module.End.mem_eigenspace_iff, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, h,
    LinearMap.rTensor_smul, LinearMap.smul_apply]

theorem GT_iSup : ⨆ d, GT r Tm d = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul y t =>
      have hy : y ∈ ⨆ d, gradingT r d := by
        rw [(gradingT_isInternal r).submodule_iSup_eq_top]; trivial
      refine Submodule.iSup_induction (gradingT r)
        (motive := fun y => y ⊗ₜ[ℂ] t ∈ ⨆ d, GT r Tm d) hy ?_ ?_ ?_
      · intro d y hy
        exact Submodule.mem_iSup_of_mem d ⟨⟨y, hy⟩ ⊗ₜ[ℂ] t, by
          rw [LinearMap.rTensor_tmul]; rfl⟩
      · simp only [TensorProduct.zero_tmul]; exact Submodule.zero_mem _
      · intro y₁ y₂ h₁ h₂
        simp only [TensorProduct.add_tmul]; exact Submodule.add_mem _ h₁ h₂

theorem GT_isInternal : DirectSum.IsInternal (GT r Tm) := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ (GT_iSup r Tm)
  exact ((Module.End.eigenspaces_iSupIndep ((L0T r).rTensor Tm)).comp
    (levelC_injective r)).mono (GT_le_eigenspace r Tm)

/-- The `L₀`-eigenspace of `S[θ] ⊗ T` of eigenvalue `α ∈ ℂ`. -/
noncomputable def weightLT (α : ℂ) : Submodule ℂ (FockT r ⊗[ℂ] Tm) :=
  ⨆ (d : ℕ) (_ : ((levelT r d : ℚ) : ℂ) = α), GT r Tm d

theorem weightLT_level (d : ℕ) : weightLT r Tm ((levelT r d : ℚ) : ℂ) = GT r Tm d := by
  apply le_antisymm
  · refine iSup₂_le fun e he => ?_
    rw [levelC_injective r he]
  · exact le_iSup₂_of_le d rfl le_rfl

theorem weightLT_eq_bot {α : ℂ} (hα : ∀ d : ℕ, ((levelT r d : ℚ) : ℂ) ≠ α) :
    weightLT r Tm α = ⊥ := by
  rw [weightLT, eq_bot_iff]
  exact iSup₂_le fun d hd => absurd hd (hα d)

theorem weightLT_isInternal : DirectSum.IsInternal (weightLT r Tm) := by
  have hA := GT_isInternal r Tm
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rw [← iSupIndep_ne_bot]
    have hex : ∀ α : {α : ℂ // weightLT r Tm α ≠ ⊥}, ∃ d : ℕ, ((levelT r d : ℚ) : ℂ) = α.1 := by
      rintro ⟨α, hα⟩
      by_contra h
      push Not at h
      exact hα (weightLT_eq_bot r Tm h)
    choose g hg using hex
    have hginj : Function.Injective g := by
      intro a b h
      exact Subtype.ext (by rw [← hg a, ← hg b, h])
    have hcomp : (fun α : {α : ℂ // weightLT r Tm α ≠ ⊥} => weightLT r Tm α.1) = GT r Tm ∘ g := by
      funext α
      simp only [Function.comp_apply]
      rw [← weightLT_level, hg α]
    rw [hcomp]
    exact hA.submodule_iSupIndep.comp hginj
  · rw [eq_top_iff, ← hA.submodule_iSup_eq_top]
    exact iSup_le fun d => (weightLT_level r Tm d) ▸ le_iSup (weightLT r Tm) ((levelT r d : ℚ) : ℂ)

theorem weightLT_finiteDimensional [FiniteDimensional ℂ Tm] (α : ℂ) :
    FiniteDimensional ℂ (weightLT r Tm α) := by
  by_cases h : ∃ d : ℕ, ((levelT r d : ℚ) : ℂ) = α
  · obtain ⟨d, rfl⟩ := h
    rw [weightLT_level, GT]
    infer_instance
  · push Not at h
    rw [weightLT_eq_bot r Tm h]
    infer_instance

theorem L0T_rTensor_weightLT {α : ℂ} {x : FockT r ⊗[ℂ] Tm} (hx : x ∈ weightLT r Tm α) :
    (L0T r).rTensor Tm x = α • x := by
  by_cases h : ∃ d : ℕ, ((levelT r d : ℚ) : ℂ) = α
  · obtain ⟨d, rfl⟩ := h
    rw [weightLT_level] at hx
    exact Module.End.mem_eigenspace_iff.mp (GT_le_eigenspace r Tm d hx)
  · push Not at h
    rw [weightLT_eq_bot r Tm h, Submodule.mem_bot] at hx
    rw [hx, map_zero, smul_zero]

theorem weightLT_boundedBelow :
    ∃ B : ℝ, ∀ α : ℂ, weightLT r Tm α ≠ ⊥ → B ≤ α.re := by
  refine ⟨(r : ℝ) / 16, fun α hα => ?_⟩
  by_contra hlt
  apply hα
  refine weightLT_eq_bot r Tm fun d hd => hlt ?_
  rw [← hd, Complex.ratCast_re, levelT]
  push_cast
  have : (0 : ℝ) ≤ d := d.cast_nonneg
  linarith

end Grading

section Lattice

open IntegralLattice LatGen Extraspecial

variable (L : IntegralLattice.{0}) (hEven : L.Even) (hU : IsUnit (gramMat L).det) (hPos : L.PosDef)

theorem YTLFld_zero_eq (e : ℤ) :
    YTLFld L hEven hU 0 e
      = rTFld (Tm := Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) (FT (rank L) e (vacuumN _)) := by
  apply fld_ext_mode
  intro n x
  rw [mode_YTLFld, mode_rTFld, FT_val, mode_resc, YTL_zero, YT_vacuum]
  push_cast
  split_ifs <;> simp [Module.End.one_eq_id, LinearMap.rTensor_id]

include hPos in
/-- **The charge-zero sector**: `F_e(p ⊗ e^0) = F_e^{Heis}(p) ⊗ 1`. -/
theorem FL_charge_zero (p : FockN (rank L)) (e : ℤ) :
    FL L hEven hU e (p ⊗ₜ[ℂ] eGen L 0)
      = rTFld (Tm := Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) (FT (rank L) e p) := by
  induction p using MvPolynomial.induction_on generalizing e with
  | C a =>
      rw [MvPolynomial.C_eq_smul_one, ← TensorProduct.smul_tmul', map_smul, FT_smul, rTFld_smul,
        ← echg_eq, FL_echg L hEven hU hPos, YTLFld_zero_eq]
      rfl
  | add p q hp hq => rw [TensorProduct.add_tmul, map_add, hp, hq, FT_add, rTFld_add]
  | mul_X p c hp =>
      have h1 := FL_mul_X L hEven hU hPos (e - 1) c p (eGen L 0)
      have h2 := FT_mul_X (rank L) (e - 1) c p
      rw [sub_add_cancel] at h1 h2
      have hloc : Local (FgenFld (rank L) c.2).1 (FT (rank L) (e - 1) p).1 := by
        rw [← FT_one_X]
        exact FT_local (rank L) 1 (e - 1) _ p
      rw [mul_comm, h1, h2, hp, FgT, rTFld_star _ hloc]

include hPos in
/-- **`L₀` of the lattice twisted module**: `Y^T(ω)₍₁₎ = L0T ⊗ 1`. -/
theorem YML_omega_two :
    YML L hEven hU (omegaLatGen L) 2
      = (L0T (rank L)).rTensor (Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) := by
  rw [YML_apply, omegaLatGen, mkEα_apply, FL_charge_zero L hEven hU hPos, mode_rTFld, FT_val,
    mode_resc]
  rw [show ((2 : ℕ) : ℤ) * 0 + 2 = 2 by norm_num]
  exact congrArg (fun f => LinearMap.rTensor _ f) (YT_omega_two (rank L))

end Lattice

end VOA.Moonshine.LatticeTwisted
