/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.LatticeNice

/-!
# Transport between VOA carriers in different universes

The algebraic invariants do not quantify over module carriers. Their transport proofs from
`LatticeNice` therefore generalize directly to independently chosen carrier universes.
Rationality and pseudo-unitarity require separate arguments about module universes.
-/

namespace VOA.Classification.COne.ConverseUniverse

open VOA Module

section Transport

universe u v

variable {𝒱 : Type u} {𝒲 : Type v} [AddCommGroup 𝒱] [Module ℂ 𝒱] [AddCommGroup 𝒲] [Module ℂ 𝒲]
  {V : VertexOperatorAlgebra 𝒱} {T : VertexOperatorAlgebra 𝒲}

theorem isVOAHom_symm' (e : 𝒱 ≃ₗ[ℂ] 𝒲) (he : IsVOAHom V T e.toLinearMap) :
    IsVOAHom T V e.symm.toLinearMap where
  map_vacuum := by
    apply e.injective
    simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
    exact he.map_vacuum.symm
  map_smul u n x := by
    apply e.injective
    simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
    have := he.map_smul (e.symm u) n (e.symm x)
    simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply] at this
    exact this.symm

/-- A VOA homomorphism preserving the conformal vector intertwines every `L n`. -/
theorem voaHom_map_L {φ : 𝒱 →ₗ[ℂ] 𝒲} (hφ : IsVOAHom V T φ)
    (hω : φ V.conformalVector = T.conformalVector) (n : ℤ) (v : 𝒱) :
    φ (V.L n v) = T.L n (φ v) := by
  have := hφ.map_smul V.conformalVector (n + 1) v
  rw [hω] at this
  exact this

theorem voaHom_map_L_pow {φ : 𝒱 →ₗ[ℂ] 𝒲} (hφ : IsVOAHom V T φ)
    (hω : φ V.conformalVector = T.conformalVector) (n : ℤ) (j : ℕ) (v : 𝒱) :
    φ (((V.L n) ^ j) v) = ((T.L n) ^ j) (φ v) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ', Module.End.mul_apply, voaHom_map_L hφ hω, ih, pow_succ',
      Module.End.mul_apply]

/-- In a VOA, an `L₀`-eigenvector of integer eigenvalue `n` lies in `𝒱_n`. -/
theorem mem_grading_of_L0 (W : VertexOperatorAlgebra 𝒲) {n : ℤ} {y : 𝒲}
    (hy : W.L 0 y = (n : ℂ) • y) : y ∈ W.grading n := by
  have htop : (⊤ : Submodule ℂ 𝒲) ≤ W.grading n ⊔ ⨆ (k : ℤ) (_ : k ≠ n), W.grading k := by
    rw [← W.isInternal.submodule_iSup_eq_top, iSup_split_single _ n]
  obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.mp (htop (Submodule.mem_top (x := y)))
  have hgr : ∀ k : ℤ, W.grading k ≤ (W.L 0).eigenspace (k : ℂ) := fun k x hx =>
    Module.End.mem_eigenspace_iff.mpr (W.L_zero_grading x hx)
  have hz1 : z ∈ (W.L 0).eigenspace (n : ℂ) := by
    have h1 : a + z ∈ (W.L 0).eigenspace (n : ℂ) := Module.End.mem_eigenspace_iff.mpr hy
    have h2 := hgr n ha
    simpa using Submodule.sub_mem _ h1 h2
  have hle : (⨆ (k : ℤ) (_ : k ≠ n), W.grading k)
      ≤ ⨆ (μ : ℂ) (_ : μ ≠ (n : ℂ)), (W.L 0).eigenspace μ :=
    iSup₂_le fun k hk =>
      le_trans (hgr k) (le_iSup₂_of_le (k : ℂ) (by exact_mod_cast hk) le_rfl)
  have hz2 := hle hz
  have := Submodule.disjoint_def.mp (Module.End.eigenspaces_iSupIndep (W.L 0) (n : ℂ)) z hz1 hz2
  rw [this, add_zero]; exact ha

theorem voaHom_map_grading {φ : 𝒱 →ₗ[ℂ] 𝒲} (hφ : IsVOAHom V T φ)
    (hω : φ V.conformalVector = T.conformalVector) {n : ℤ} {v : 𝒱} (hv : v ∈ V.grading n) :
    φ v ∈ T.grading n := by
  refine mem_grading_of_L0 T ?_
  rw [← voaHom_map_L hφ hω, V.L_zero_grading v hv, map_smul]

/-- Pulling a weak module back along a VOA homomorphism. -/
def pullWeak {φ : 𝒱 →ₗ[ℂ] 𝒲} (hφ : IsVOAHom V T φ) {M : Type*} [AddCommGroup M] [Module ℂ M]
    (B : WeakModule T M) : WeakModule V M where
  YM := B.YM ∘ₗ φ
  vacuum_YM := by simp [hφ.map_vacuum, B.vacuum_YM]
  truncation u x := B.truncation (φ u) x
  jacobi u v x ℓ m n := by
    simp only [LinearMap.comp_apply, hφ.map_smul]
    exact B.jacobi (φ u) (φ v) x ℓ m n

@[simp] theorem pullWeak_act {φ : 𝒱 →ₗ[ℂ] 𝒲} (hφ : IsVOAHom V T φ) {M : Type*}
    [AddCommGroup M] [Module ℂ M] (B : WeakModule T M) (u : 𝒱) (n : ℤ) (x : M) :
    (pullWeak hφ B).act u n x = B.act (φ u) n x := rfl

variable (e : 𝒱 ≃ₗ[ℂ] 𝒲) (he : IsVOAHom V T e.toLinearMap)
  (hω : e V.conformalVector = T.conformalVector)

include hω in
theorem symm_conformal : e.symm T.conformalVector = V.conformalVector := by
  rw [← hω, LinearEquiv.symm_apply_apply]

theorem virasoro_central_vacuum : ∀ {𝒰 : Type*} [AddCommGroup 𝒰] [Module ℂ 𝒰]
    (W : VertexOperatorAlgebra 𝒰),
    W.L 2 (W.L (-2) W.vacuum) = (W.centralCharge / 2) • W.vacuum := by
  intro 𝒰 _ _ W
  have h := LinearMap.congr_fun (W.L_virasoro 2 (-2)) W.vacuum
  have h2 : W.L 2 W.vacuum = 0 := (W.creation W.conformalVector).2 3 (by norm_num)
  have h0 : W.L 0 W.vacuum = 0 := by
    rw [W.L_zero_grading _ W.vacuum_mem]; simp
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.add_apply, LinearMap.smul_apply, h2, map_zero, sub_zero] at h
  rw [h, if_pos (by norm_num), show (2 : ℤ) + -2 = 0 by norm_num, h0]
  simp only [smul_zero, zero_add, LinearMap.smul_apply, Module.End.one_apply]
  congr 1
  push_cast; ring

include he hω in
/-- Central charge is an isomorphism invariant (for a nonzero vacuum). -/
theorem centralCharge_eq_of_iso (hT : T.vacuum ≠ 0) : V.centralCharge = T.centralCharge := by
  have hV := virasoro_central_vacuum V
  have hTk := virasoro_central_vacuum T
  have hL : ∀ (n : ℤ) (v : 𝒱), e (V.L n v) = T.L n (e v) := fun n v => by
    simpa using voaHom_map_L he hω n v
  have hvac : e V.vacuum = T.vacuum := by simpa using he.map_vacuum
  have h1 := congrArg e hV
  rw [hL, hL, hvac, map_smul, hvac, hTk] at h1
  have h3 : ((T.centralCharge / 2) - (V.centralCharge / 2)) • T.vacuum = 0 := by
    rw [sub_smul, h1, sub_self]
  have := (smul_eq_zero.mp h3).resolve_right hT
  linear_combination -2 * this

include he in
theorem isSimple_of_iso (hT : T.IsSimple) : V.IsSimple := by
  refine ⟨fun h => hT.1 ?_, fun I hI => ?_⟩
  · rw [eq_bot_iff]
    intro y _
    have : e.symm y ∈ (⊤ : Submodule ℂ 𝒱) := Submodule.mem_top
    rw [h, Submodule.mem_bot] at this
    rw [Submodule.mem_bot, ← e.apply_symm_apply y, this, map_zero]
  · have hJ : T.IsIdeal (I.map e.toLinearMap) := by
      intro u v n hv
      obtain ⟨v', hv', rfl⟩ := hv
      refine ⟨V.smul (e.symm u) n v', hI _ _ _ hv', ?_⟩
      have := he.map_smul (e.symm u) n v'
      simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply] at this
      exact this
    have hc : I = (I.map e.toLinearMap).comap e.toLinearMap :=
      (Submodule.comap_map_eq_of_injective e.injective I).symm
    rcases hT.2 _ hJ with h | h
    · left; rw [hc, h, Submodule.comap_bot]; exact LinearMap.ker_eq_bot.mpr e.injective
    · right; rw [hc, h, Submodule.comap_top]

include he hω in
theorem selfDual_of_iso (hT : T.SelfDual) : V.SelfDual := by
  obtain ⟨B, hBf, hBr⟩ := hT
  let B' : VertexOperatorAlgebra.InvariantForm V :=
    { form := B.form.compl₁₂ e.toLinearMap e.toLinearMap
      virasoro_adj := by
        intro n a b
        simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_toLinearMap]
        have h1 := voaHom_map_L he hω n a
        have h2 := voaHom_map_L he hω (-n) b
        simp only [LinearEquiv.coe_toLinearMap] at h1 h2
        rw [h1, h2, B.virasoro_adj] }
  refine ⟨B', ?_, ?_⟩
  · intro wt u hu n a b
    have hu' := voaHom_map_grading he hω hu
    simp only [B', LinearMap.compl₁₂_apply, LinearEquiv.coe_toLinearMap]
    have hs := he.map_smul u n a
    simp only [LinearEquiv.coe_toLinearMap] at hs hu'
    rw [hs, hBf wt (e u) hu' n (e a) (e b)]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have hp := voaHom_map_L_pow he hω 1 j u
    have hs2 := he.map_smul (((V.L 1) ^ j) u) (2 * wt - n - 2 - (j : ℤ)) b
    simp only [LinearEquiv.coe_toLinearMap] at hp hs2
    rw [hs2, hp]
  · rw [eq_bot_iff]
    intro a ha
    rw [VertexOperatorAlgebra.InvariantForm.mem_leftRadical] at ha
    have hea : e a ∈ VertexOperatorAlgebra.InvariantForm.leftRadical B := by
      rw [VertexOperatorAlgebra.InvariantForm.mem_leftRadical]
      refine LinearMap.ext fun y => ?_
      have := LinearMap.congr_fun ha (e.symm y)
      simpa [B'] using this
    rw [hBr, Submodule.mem_bot] at hea
    rw [Submodule.mem_bot]
    exact e.injective (by rw [hea, map_zero])

include he in
theorem c2Cofinite_of_iso (hT : C2Cofinite T) : C2Cofinite V := by
  have hmap : (O₂ V).map e.toLinearMap = O₂ T := by
    rw [O₂, O₂, Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨u, v, rfl⟩, rfl⟩
      exact ⟨e u, e v, he.map_smul u (-2) v⟩
    · rintro ⟨u, v, rfl⟩
      refine ⟨V.smul (e.symm u) (-2) (e.symm v), ⟨_, _, rfl⟩, ?_⟩
      have := he.map_smul (e.symm u) (-2) (e.symm v)
      simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply] at this
      exact this
  unfold C2Cofinite at hT ⊢
  exact LinearEquiv.finiteDimensional (Submodule.Quotient.equiv (O₂ V) (O₂ T) e hmap).symm

include he hω in
theorem admissiblyRational_of_iso (hT : ∀ {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : AdmissibleModule T M), N.IsCompletelyReducible) : AdmissiblyRational V := by
  intro M _ _ N P
  have hs := isVOAHom_symm' e he
  have hωs := symm_conformal e hω
  let N' : AdmissibleModule T M :=
    { toWeakModule := pullWeak hs N.toWeakModule
      lev := N.lev
      lev_eq_bot_of_neg := N.lev_eq_bot_of_neg
      isInternal := N.isInternal
      act_lev := fun w p k a ha x hx => N.act_lev (voaHom_map_grading hs hωs ha) hx }
  let P' : WeakModule.Submodule' N'.toWeakModule :=
    ⟨P.carrier, fun u n x hx => P.act_mem (e.symm u) n hx⟩
  obtain ⟨Q', hQ'⟩ := hT N' P'
  refine ⟨⟨Q'.carrier, fun u n x hx => ?_⟩, hQ'⟩
  have := Q'.act_mem (e u) n hx
  simpa [N', pullWeak] using this

end Transport

end VOA.Classification.COne.ConverseUniverse
