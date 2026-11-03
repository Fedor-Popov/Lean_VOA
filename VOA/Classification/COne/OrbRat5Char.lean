import VOA.Classification.COne.OrbRat3Module
import VOA.Classification.COne.PlusSplitLatticeCharacters
import VOA.Classification.COne.PlusSplitSignCharacter

/-! # Zhu characters of the tetrahedral model from tops of `V₈⁺`-modules

* Generic (any VOA `W`, any weak module): `exists_character_of_top_line` — a nonzero top vector
  `y ∈ Ω(M)` that is an eigenvector of every homogeneous zero mode defines a genuine algebra
  character of `A(W)` (no `C₂`, no ordinary-module structure, no finiteness).
* `cubicRestrict`: a weak `V₈⁺`-module restricted to the cubic fixed points
  `(V₈⁺)^{plusCubic}` and pulled back to `cubicModel` along `fixedEquivKlein.symm`.
* `cubic_character_of_plus_top`: a top vector of an ordinary `V₈⁺`-module which is a common
  eigenvector of the three Zhu generators `ω, W, E` of `A(V₈⁺)` gives a `cubicModel` character
  with `[ω] ↦ h`.
* Five such characters, from the actual modules `V₈⁺` (weight `0`), `V_L⁻` (`1`) and the three
  charged lattice modules `V_{L+λ_j}`, `j = 1,2,3` (`1/16, 1/4, 9/16`).
-/

set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Classification.COne.OrbRat5

open VOA VertexOperatorAlgebra PlusSplitting PlusRational ABDWeakAdmissible
  VOA.Huang.LogRemovalAdmissible PlusUnitary OrbRat2 OrbRat3

/-! ## Generic: a top eigenline gives a character -/

section Generic

variable {V : Type} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {M : Type} [AddCommGroup M] [Module ℂ M]

/-- A nonzero top vector which is an eigenvector of every homogeneous zero mode defines an
algebra character of `A(W)`, realised on it through `topEvaluation`. -/
theorem exists_character_of_top_line (A : WeakModule W M) {y : M} (hy : y ∈ Omega A)
    (hy0 : y ≠ 0)
    (hline : ∀ (k : ℤ) (a : V), a ∈ W.grading k → ∃ c : ℂ, mode (A.YM a) (k - 1) y = c • y) :
    letI := instRingA W; letI := instAlgebraA W
    ∃ χ : VOA.A W →ₐ[ℂ] ℂ, ∀ z, topEvaluation A y hy z = χ z • y := by
  letI := instRingA W
  letI := instAlgebraA W
  set f := topEvaluation A y hy with hf
  let S : Submodule ℂ V :=
    { carrier := {a | ∃ c : ℂ, f (VOA.mk W a) = c • y}
      add_mem' := by
        rintro a b ⟨c, hc⟩ ⟨d, hd⟩
        refine ⟨c + d, ?_⟩
        change f (VOA.mk W (a + b)) = _
        rw [show VOA.mk W (a + b) = VOA.mk W a + VOA.mk W b from map_add _ a b, map_add, hc, hd,
          add_smul]
      zero_mem' := ⟨0, by
        change f (VOA.mk W 0) = _
        rw [show VOA.mk W (0 : V) = 0 from map_zero _, map_zero, zero_smul]⟩
      smul_mem' := by
        rintro t a ⟨c, hc⟩
        refine ⟨t * c, ?_⟩
        change f (VOA.mk W (t • a)) = _
        rw [show VOA.mk W (t • a) = t • VOA.mk W a from map_smul _ t a, map_smul, hc, smul_smul] }
  have hle : (⨆ k, W.grading k) ≤ S := by
    refine iSup_le fun k a hk => ?_
    obtain ⟨c, hc⟩ := hline k a hk
    refine ⟨c, ?_⟩
    rw [hf, topEvaluation_mk, oLevW_homogeneous A 0 hk, add_zero]
    exact hc
  have hS : ∀ a, a ∈ S := by
    intro a
    apply hle
    rw [W.isInternal.submodule_iSup_eq_top]; trivial
  have hall : ∀ z, ∃ c : ℂ, f z = c • y := by
    intro z
    obtain ⟨a, rfl⟩ := VOA.mk_surjective W z
    exact hS a
  obtain ⟨ell, hell⟩ := Module.Projective.exists_dual_eq_one ℂ hy0
  let g : VOA.A W →ₗ[ℂ] ℂ := ell.comp f
  have hg : ∀ z, f z = g z • y := by
    intro z
    obtain ⟨c, hc⟩ := hall z
    have : g z = c := by
      change ell (f z) = c
      rw [hc, map_smul, hell, smul_eq_mul, mul_one]
    rw [this]; exact hc
  have h1 : g 1 = 1 := by
    change ell (f 1) = 1
    rw [hf, PlusRatSign.topEvaluation_one, hell]
  have hmul : ∀ a b, g (a * b) = g a * g b := by
    intro a b
    obtain ⟨u, rfl⟩ := VOA.mk_surjective W a
    have hab : f (VOA.mk W u * b) = (g b * g (VOA.mk W u)) • y := by
      rw [hf, topEvaluation_mk_mul, ← hf, hg b, map_smul, ← topEvaluation_mk A y hy u, ← hf,
        hg (VOA.mk W u), smul_smul]
    change ell (f _) = _
    rw [hab, map_smul, hell, smul_eq_mul, mul_one, mul_comm]
  exact ⟨AlgHom.ofLinearMap g h1 hmul, hg⟩

/-- The `[ω]`-value of such a character is the `L₀`-eigenvalue of the top vector. -/
theorem character_omega_of_top (A : WeakModule W M) {y : M} (hy : y ∈ Omega A)
    (hy0 : y ≠ 0) {c : ℂ} (hL : mode (A.YM W.conformalVector) 1 y = c • y)
    (χ : letI := instRingA W; letI := instAlgebraA W; VOA.A W →ₐ[ℂ] ℂ)
    (hχ : letI := instRingA W; ∀ z, topEvaluation A y hy z = χ z • y) :
    χ (VOA.mk W W.conformalVector) = c := by
  letI := instRingA W
  have h := hχ (VOA.mk W W.conformalVector)
  rw [topEvaluation_mk, oLevW_homogeneous A 0 W.conformal_mem,
    show (2 : ℤ) - 1 + 0 = 1 by norm_num, hL] at h
  have h2 : (χ (VOA.mk W W.conformalVector) - c) • y = 0 := by
    rw [sub_smul, ← h, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact (sub_eq_zero.mp h3)
  · exact absurd h3 hy0

end Generic

/-! ## Restriction of `V₈⁺`-modules to the tetrahedral model -/

section Cubic

open OrbC2b OrbC2e OrbC2f PlusCharacterTable ConverseUniverse PlusC2

variable {M : Type} [AddCommGroup M] [Module ℂ M]

/-- A weak `V₈⁺`-module restricted to the cubic fixed points and pulled back to `cubicModel`. -/
def cubicRestrict (A : WeakModule (V2mPlus 4 four_ge_one) M) : WeakModule cubicModel M :=
  pullWeak fixedEquivKlein_symm_hom
    ((orbifold (Subgroup.zpowers plusCubic)).restrictWeakModule A)

theorem cubicRestrict_YM (A : WeakModule (V2mPlus 4 four_ge_one) M)
    (v : (orbifold (Subgroup.zpowers kleinCubic)).carrier) :
    (cubicRestrict A).YM v =
      A.YM ((fixedEquivKlein.symm v : (orbifold (Subgroup.zpowers plusCubic)).carrier) :
        VP 4 four_ge_one) := rfl

theorem cubic_grading_symm {k : ℤ} {v : (orbifold (Subgroup.zpowers kleinCubic)).carrier}
    (hv : v ∈ cubicModel.grading k) :
    ((fixedEquivKlein.symm v : (orbifold (Subgroup.zpowers plusCubic)).carrier) :
      VP 4 four_ge_one) ∈ (V2mPlus 4 four_ge_one).grading k :=
  voaHom_map_grading fixedEquivKlein_symm_hom fixedEquivKlein_symm_omega hv

/-- A lowest-weight vector of an ordinary `V₈⁺`-module is a top vector for `cubicModel`. -/
theorem mem_Omega_cubicRestrict (N : OrdVModule (V2mPlus 4 four_ge_one) M) {h : ℂ}
    (hlow : IsLowestWeight N h) {y : M} (hy : y ∈ N.weight h) :
    y ∈ Omega (cubicRestrict N.toWeakModule) := by
  intro β v hv n hn
  rw [cubicRestrict_YM]
  exact mode_lowering_vanish N hlow (cubic_grading_symm hv) hy hn

/-- A common eigenvector of the Zhu generators of `A(V₈⁺)` on a lowest-weight space is an
eigenvector of every zero mode. -/
theorem plus_top_eigen (N : OrdVModule (V2mPlus 4 four_ge_one) M) {h : ℂ}
    (hlow : IsLowestWeight N h) {x : M} (hx : x ∈ N.weight h) (v : Fin 3 → ℂ)
    (hv : ∀ i, oMod N (gP 4 four_ge_one i) x = v i • x) (b : VP 4 four_ge_one) :
    ∃ c : ℂ, oMod N b x = c • x := by
  letI := instRingA (V2mPlus 4 four_ge_one)
  letI := instAlgebraA (V2mPlus 4 four_ge_one)
  let ρ : VOA.A (V2mPlus 4 four_ge_one) →ₐ[ℂ] Module.End ℂ (N.weight h) :=
    AlgHom.ofLinearMap (actA N hlow) (actA_one N hlow)
      (actA_mul (zhuRingData_holds _) hlow)
  let x' : N.weight h := ⟨x, hx⟩
  have hgen := V2mPlus_zhu_adjoin_generators 4 four_ge_one (by norm_num)
  have hall : ∀ a : VOA.A (V2mPlus 4 four_ge_one), ∃ c : ℂ, ρ a x' = c • x' := by
    intro a
    have ha : a ∈ Algebra.adjoin ℂ (Set.range (fun i : Fin 3 =>
        VOA.mk (V2mPlus 4 four_ge_one) (gP 4 four_ge_one i))) := by rw [hgen]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨i, rfl⟩ := ha
      refine ⟨v i, ?_⟩
      apply Subtype.ext
      change (actA N hlow (VOA.mk (V2mPlus 4 four_ge_one) (gP 4 four_ge_one i)) x' : M) = _
      rw [actA_mk_apply_coe]
      exact hv i
    | algebraMap c => exact ⟨c, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨c, hc⟩ := ha; obtain ⟨d, hd⟩ := hb
      exact ⟨c + d, by simp [hc, hd, add_smul]⟩
    | mul a b _ _ ha hb =>
      obtain ⟨c, hc⟩ := ha; obtain ⟨d, hd⟩ := hb
      exact ⟨c * d, by simp [Module.End.mul_apply, hd, hc, smul_smul, mul_comm]⟩
  obtain ⟨c, hc⟩ := hall (VOA.mk (V2mPlus 4 four_ge_one) b)
  refine ⟨c, ?_⟩
  have h2 := congrArg Subtype.val hc
  change (actA N hlow (VOA.mk (V2mPlus 4 four_ge_one) b) x' : M) = _ at h2
  rw [actA_mk_apply_coe] at h2
  exact h2

@[reducible] local instance zhuRingCubic : Ring (VOA.A cubicModel) := instRingA _
@[reducible] local instance zhuAlgebraCubic : Algebra ℂ (VOA.A cubicModel) := instAlgebraA _

/-- A `V₈⁺` top vector that is a common eigenvector of `ω, W, E` gives a character of the
Zhu algebra of the tetrahedral model with `[ω] ↦ h`. -/
theorem cubic_character_of_plus_top (N : OrdVModule (V2mPlus 4 four_ge_one) M) {h : ℂ}
    (hlow : IsLowestWeight N h) {x : M} (hx : x ∈ N.weight h) (hx0 : x ≠ 0) (v : Fin 3 → ℂ)
    (hv : ∀ i, oMod N (gP 4 four_ge_one i) x = v i • x) :
    ∃ χ : VOA.A cubicModel →ₐ[ℂ] ℂ,
      χ (VOA.mk cubicModel cubicModel.conformalVector) = h := by
  have hΩ := mem_Omega_cubicRestrict N hlow hx
  obtain ⟨χ, hχ⟩ := exists_character_of_top_line (cubicRestrict N.toWeakModule) hΩ hx0 (by
    intro k a ha
    obtain ⟨c, hc⟩ := plus_top_eigen N hlow hx v hv
      ((fixedEquivKlein.symm a : (orbifold (Subgroup.zpowers plusCubic)).carrier) :
        VP 4 four_ge_one)
    refine ⟨c, ?_⟩
    rw [cubicRestrict_YM, ← oMod_homogeneous N (cubic_grading_symm ha)]
    exact hc)
  refine ⟨χ, character_omega_of_top _ hΩ hx0 ?_ χ hχ⟩
  rw [cubicRestrict_YM, fixedEquivKlein_symm_omega]
  exact N.L0_weight h x hx

/-! ## Five characters -/

open LatMod VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice

/-- The vacuum character (weight `0`), from the adjoint `V₈⁺`-module. -/
theorem cubic_character_vacuum :
    ∃ χ : VOA.A cubicModel →ₐ[ℂ] ℂ,
      χ (VOA.mk cubicModel cubicModel.conformalVector) = 0 :=
  cubic_character_of_plus_top (adjointModule (V2mPlus 4 four_ge_one))
    (isLowestWeight_adjoint _) (vacuum_mem_adjoint_weight _)
    (fun hz => latVacuumGen_ne_zero' 4 four_ge_one (congrArg Subtype.val hz))
    (fun _ => 0) (by
      intro i
      simpa using oMod_adjoint_vacuum (V2mPlus 4 four_ge_one)
        (show 1 ≤ (wtP 4 i : ℤ) by fin_cases i <;> simp [wtP])
        (gP_mem_grading 4 four_ge_one i))

/-- The sign character (weight `1`), from `V_L⁻`. -/
theorem cubic_character_sign :
    ∃ χ : VOA.A cubicModel →ₐ[ℂ] ℂ,
      χ (VOA.mk cubicModel cubicModel.conformalVector) = 1 :=
  cubic_character_of_plus_top (signModule 4 four_ge_one)
    (signModule_isLowestWeight 4 four_ge_one) (signVector_mem 4 four_ge_one)
    (signVector_ne_zero 4 four_ge_one) ![1, 12, 0] (by
      intro i; fin_cases i
      · change oMod (signModule 4 four_ge_one) (V2mPlus 4 four_ge_one).conformalVector _ = _
        rw [oMod_conformalVector]
        exact (signModule 4 four_ge_one).L0_weight _ _ (signVector_mem 4 four_ge_one)
      · exact signVector_W 4 four_ge_one
      · simpa using signVector_E 4 four_ge_one (by norm_num))

/-- The charged characters (weight `j²/16`), from `V_{L+λ_j}`, `|j| < 4`. -/
theorem cubic_character_charged (j : ℤ) (hj : |j| < 4) :
    ∃ χ : VOA.A cubicModel →ₐ[ℂ] ℂ,
      χ (VOA.mk cubicModel cubicModel.conformalVector) =
        ((((j : ℝ) ^ 2 / (4 * (4 : ℕ)) : ℝ)) : ℂ) := by
  have hj' : |j| < ((4 : ℕ) : ℤ) := by exact_mod_cast hj
  let h : ℂ := ((((j : ℝ) ^ 2 / (4 * (4 : ℕ)) : ℝ)) : ℂ)
  let N := resN 4 four_ge_one (latticeModule 4 four_ge_one j)
  have hlow : IsLowestWeight N h := latticeModule_isLowestWeight 4 four_ge_one j hj'.le
  have hx : latVacuumGen (latP 4) ∈ N.weight h := latticeModule_vacuum_mem 4 four_ge_one j
  have hW : oMod N (WP 4 four_ge_one) (latVacuumGen (latP 4)) =
      (2 * h) • latVacuumGen (latP 4) := by
    rw [oMod_resN 4 four_ge_one _ (WP_mem_grading 4 four_ge_one), WP_coe]
    exact oMod_W_V2m 4 four_ge_one _ hlow hx
  have hE : oMod N (EP 4 four_ge_one) (latVacuumGen (latP 4)) = 0 := by
    rw [oMod_resN 4 four_ge_one _ (EP_mem_grading 4 four_ge_one)]
    exact oMod_E_lat_vac 4 four_ge_one j hj'
  exact cubic_character_of_plus_top N hlow hx (latVacuumGen_ne_zero' 4 four_ge_one)
    ![h, 2 * h, 0] (by
      intro i; fin_cases i
      · change oMod N (V2mPlus 4 four_ge_one).conformalVector _ = h • _
        rw [oMod_conformalVector]; exact N.L0_weight _ _ hx
      · exact hW
      · simpa using hE)

theorem cubic_character_weight (w : ℚ) (j : ℤ) (hj : |j| < 4) (hw : (j : ℚ) ^ 2 / 16 = w) :
    ∃ χ : VOA.A cubicModel →ₐ[ℂ] ℂ,
      χ (VOA.mk cubicModel cubicModel.conformalVector) = (w : ℂ) := by
  obtain ⟨χ, hχ⟩ := cubic_character_charged j hj
  refine ⟨χ, ?_⟩
  rw [hχ, ← hw]
  push_cast
  norm_num

/-- Five characters of `A(W)`, at the five non-doubled table weights `0, 1, 1/4, 1/16, 9/16`. -/
theorem cubic_five_characters :
    ∀ w ∈ ({0, 1, 1/4, 1/16, 9/16} : Finset ℚ),
      ∃ χ : VOA.A cubicModel →ₐ[ℂ] ℂ,
        χ (VOA.mk cubicModel cubicModel.conformalVector) = (w : ℂ) := by
  intro w hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · simpa using cubic_character_vacuum
  · simpa using cubic_character_sign
  · exact cubic_character_weight _ 2 (by norm_num) (by norm_num)
  · exact cubic_character_weight _ 1 (by norm_num) (by norm_num)
  · exact cubic_character_weight _ 3 (by norm_num) (by norm_num)

end Cubic

end VOA.Classification.COne.OrbRat5
