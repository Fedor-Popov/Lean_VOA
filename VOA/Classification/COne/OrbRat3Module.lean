import VOA.Classification.COne.OrbRat3Eval
import VOA.Classification.COne.OrbRat2Vacuum
import VOA.Classification.COne.OrbC2fTetra

/-! # A weight-one top for the tetrahedral model, and table characters from a top witness

* Generic (any VOA `W`, any character table saturating `dim A(W)`):
  `exists_table_eq` — every character of `A(W)` is a table character;
  `table_value_of_top` — if some weak module has a nonzero top vector `y` with `L₀ y = c y` and
  `z · y = λ y`, then the table character of weight `c` (when unique) takes the value `λ` on `z`.
* Concrete: `cubicSign`, the sign module `V_L⁻` of `V₈⁺` restricted to the transported cubic
  fixed algebra `(V₈⁺)^{plusCubic}` and pulled back to `cubicModel` along the VOA isomorphism
  `fixedEquivKlein`.  Its vector `h(-1)1` is a top vector of `L₀`-weight one, and the
  weight-nine generator `cubicU = fixedEquivKlein fixedNine` acts through the `V₈` modes of
  `OrbC2e.weightNine` (`cubicSign_act_U`).
* `cubicVacuumTelescope_of_V8` reduces `CubicVacuumTelescope` (given the Zhu inputs) to one
  nonzero number in `V₈`; the number is certified in `OrbRat3Telescope`.
-/
set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Classification.COne.OrbRat3

open VOA VertexOperatorAlgebra PlusSplitting PlusRational ABDWeakAdmissible
  VOA.Huang.LogRemovalAdmissible PlusUnitary PlusRatTelescope OrbRat2

/-! ## Generic table arguments -/

section Generic

variable {V : Type} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Every character of `A(W)` is one of the table characters. -/
theorem exists_table_eq (hC2 : C2Cofinite W) {n : ℕ}
    (hdim : Module.finrank ℂ (VOA.A W) ≤ n)
    (χ : Fin n → (letI := instRingA W; letI := instAlgebraA W; VOA.A W →ₐ[ℂ] ℂ))
    (hχ : Function.Injective χ)
    (ψ : (letI := instRingA W; letI := instAlgebraA W; VOA.A W →ₐ[ℂ] ℂ)) :
    ∃ j, ψ = χ j := by
  letI := instRingA W
  letI := instAlgebraA W
  obtain ⟨ε, hsum, hmul, -⟩ := charTable_idempotents hC2 hdim χ hχ
  have h1 : ∑ i, ψ (ε i) = 1 := by rw [← map_sum, hsum, map_one]
  obtain ⟨j, hj⟩ : ∃ j, ψ (ε j) ≠ 0 := by
    by_contra hc
    push Not at hc
    simp [hc] at h1
  refine ⟨j, ?_⟩
  ext a
  have h := congrArg ψ (hmul a j)
  rw [map_mul, map_smul, smul_eq_mul] at h
  exact mul_right_cancel₀ hj h

/-- A top witness determines the value of the unique table character of its weight. -/
theorem table_value_of_top (hC2 : C2Cofinite W) {n : ℕ} {wt : Fin n → ℂ}
    (hdim : Module.finrank ℂ (VOA.A W) ≤ n)
    (χ : Fin n → (letI := instRingA W; letI := instAlgebraA W; VOA.A W →ₐ[ℂ] ℂ))
    (hχ : Function.Injective χ) (hω : ∀ i, χ i (VOA.mk W W.conformalVector) = wt i)
    {M : Type} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M) {y : M}
    (hy : y ∈ Omega A) (hy0 : y ≠ 0) {c : ℂ} (hL : L0 A y = c • y) (z : VOA.A W) {l : ℂ}
    (hz : topEvaluation A y hy z = l • y) {i : Fin n}
    (huniq : ∀ j, wt j = c → j = i) : χ i z = l := by
  letI := instRingA W
  letI := instAlgebraA W
  by_contra hne
  apply hy0
  refine top_eq_zero_of_table hC2 hdim χ hχ hω A hy hL (z - algebraMap ℂ _ l) ?_ ?_
  · rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, PlusRatSign.topEvaluation_one, hz,
      sub_self]
  · intro j hj
    rw [huniq j hj, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    exact sub_ne_zero.mpr hne

end Generic

/-! ## The sign top of the tetrahedral model -/

section Cubic

open OrbC2b OrbC2e OrbC2f PlusCharacterTable ConverseUniverse

/-- The sign module `V_L⁻` of `V₈⁺`, restricted to the transported cubic fixed algebra. -/
def signW' : WeakModule (orbifoldVOA (Subgroup.zpowers plusCubic))
    (signSubmodule 4 four_ge_one).carrier :=
  (orbifold (Subgroup.zpowers plusCubic)).restrictWeakModule
    (signModule 4 four_ge_one).toWeakModule

theorem fixedEquivKlein_symm_hom :
    IsVOAHom cubicModel (orbifoldVOA (Subgroup.zpowers plusCubic))
      fixedEquivKlein.symm.toLinearMap :=
  isVOAHom_symm' fixedEquivKlein fixedEquivKlein_hom

theorem fixedEquivKlein_symm_omega :
    fixedEquivKlein.symm cubicModel.conformalVector =
      (orbifoldVOA (Subgroup.zpowers plusCubic)).conformalVector := by
  rw [← fixedEquivKlein_omega, LinearEquiv.symm_apply_apply]

/-- The sign module as a weak `cubicModel`-module. -/
def cubicSign : WeakModule cubicModel (signSubmodule 4 four_ge_one).carrier :=
  pullWeak fixedEquivKlein_symm_hom signW'

/-- The weight-nine generator of `cubicModel`. -/
def cubicU : (orbifold (Subgroup.zpowers kleinCubic)).carrier := fixedEquivKlein fixedNine

theorem cubicU_mem : cubicU ∈ cubicModel.grading 9 :=
  voaHom_map_grading fixedEquivKlein_hom fixedEquivKlein_omega fixedNine_nonzero_primary.2.1

theorem cubicU_ne_zero : cubicU ≠ 0 := fun h =>
  fixedNine_nonzero_primary.1 (fixedEquivKlein.map_eq_zero_iff.mp h)

theorem cubicSign_YM (v : (orbifold (Subgroup.zpowers kleinCubic)).carrier) :
    cubicSign.YM v = (signModule 4 four_ge_one).toWeakModule.YM
      ((fixedEquivKlein.symm v : (orbifold (Subgroup.zpowers plusCubic)).carrier) :
        PlusC2.VP 4 four_ge_one) := rfl

/-- The generator acts through the `V₈` modes of the weight-nine state. -/
theorem cubicSign_act_U (k : ℤ) (x : (signSubmodule 4 four_ge_one).carrier) :
    ((mode (cubicSign.YM cubicU) k x : (signSubmodule 4 four_ge_one).carrier) :
      VOA.LatGen.LatModuleGen (VOA.LatGen.Triplet.latP 4)) =
      (V2m 4 four_ge_one).smul Uc k x := by
  rw [cubicSign_YM, cubicU, LinearEquiv.symm_apply_apply]
  rfl

/-- The sign vector is a top vector of `cubicSign`. -/
theorem signVector_mem_Omega_cubic :
    signVector 4 four_ge_one ∈ Omega cubicSign := by
  intro β v hv n hn
  have hv' := voaHom_map_grading fixedEquivKlein_symm_hom fixedEquivKlein_symm_omega hv
  rw [cubicSign_YM]
  exact PlusRatSign.signVector_mem_Omega 4 four_ge_one β _ hv' n hn

theorem cubicSign_L0 : L0 cubicSign (signVector 4 four_ge_one) =
    (1 : ℂ) • signVector 4 four_ge_one := by
  change mode (cubicSign.YM cubicModel.conformalVector) 1 _ = _
  rw [cubicSign_YM, fixedEquivKlein_symm_omega]
  have hw := (signModule 4 four_ge_one).L0_weight 1 _ (signVector_mem 4 four_ge_one)
  exact hw

theorem signVector_ne_zero' : signVector 4 four_ge_one ≠ 0 := signVector_ne_zero 4 four_ge_one

/-- The tetrahedral weight `1` occurs exactly once in the table. -/
theorem tetraWeight_eq_one (j : Fin 21) (h : tetraWeight j = 1) : j = 1 := by
  have hq : tetraWeightQ j = 1 := by
    have : ((tetraWeightQ j : ℚ) : ℂ) = ((1 : ℚ) : ℂ) := by rw [Rat.cast_one]; exact h
    exact_mod_cast this
  have key : ∀ k : Fin 21, tetraWeightQ k = 1 → k = 1 := by decide +kernel
  exact key j hq

theorem tetraWeight_one : tetraWeight 1 = 1 := by
  simp [tetraWeight, tetraWeightQ]

/-- Reduction of `CubicVacuumTelescope` (given the Zhu inputs) to one nonzero number in `V₈`:
the `V₈` telescope of the weight-nine state on `h(-1)1`. -/
theorem cubicVacuumTelescope_of_V8 (hC2 : C2Cofinite cubicModel)
    (hdim : CubicZhuDimensionBound) (htab : CubicZhuCharacterTable) {l : ℂ} (hl : l ≠ 0)
    (htel : ∑ n ∈ Finset.range 9, ((-1 : ℂ) ^ n * ((16 : ℕ).choose n : ℂ)) •
      (V2m 4 four_ge_one).smul Uc (((16 : ℕ) : ℤ) - n) ((V2m 4 four_ge_one).smul Uc n hV) =
        l • hV) :
    CubicVacuumTelescope := by
  letI := instRingA cubicModel
  letI := instAlgebraA cubicModel
  obtain ⟨χ, hχ, hω⟩ := htab
  refine ⟨cubicU, cubicU, 9, 9, 9, 16, cubicU_mem, cubicU_mem, rfl, by norm_num, by norm_num,
    by norm_num, ?_⟩
  intro ψ hψ
  have hy := signVector_mem_Omega_cubic
  have hz : topEvaluation cubicSign _ hy (zeta cubicModel cubicU cubicU 9 16) =
      l • signVector 4 four_ge_one := by
    rw [← telescope_eq_topEvaluation cubicSign cubicU_mem cubicU_mem hy 9 16 rfl (by norm_num)
      (by norm_num) (by norm_num)]
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, cubicSign_act_U]
    exact htel
  have hval := table_value_of_top hC2 hdim χ hχ hω cubicSign hy signVector_ne_zero'
    cubicSign_L0 _ hz (fun j hj => tetraWeight_eq_one j hj)
  obtain ⟨j, rfl⟩ := exists_table_eq hC2 hdim χ hχ ψ
  have hj : j = 1 := tetraWeight_eq_one j (by rw [← hω]; exact hψ)
  subst hj
  rw [hval]
  exact hl

end Cubic

end VOA.Classification.COne.OrbRat3
