/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.M8hKey

/-!
# SigmaKey, part 1: invariant-form facts used by the adjunction reduction

Generic and Leech-specific facts about the canonical invariant forms that the reduction of
`M8hKey.SigmaKey` (`SigmaKeyAdj.lean`) needs:

* `mem_grading_of_L0` — an `L₀`-eigenvector of integral eigenvalue `n` lies in `𝒱ₙ`;
* `Aut.map_L` — automorphisms commute with every Virasoro mode;
* `aut_isometry` — every automorphism of a CFT-type VOA (`L₁V₁ = 0`) is an isometry of every
  fully invariant normalised form (uniqueness of the invariant form, `invariantForm_unique_FHL`);
* `leechBV_frame_orth` — `V₀⁺ ⟂ V₃⁺` for the canonical form `leechBV` of `V_Λ⁺`;
* `leechBV_sig` — `v0Sigma` is an isometry of `leechBV` on `V₀⁺`.

All unconditional; no `pbw`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.SigmaKey

open Module (End)
open VertexOperatorAlgebra InvForm SkewAdjoint TrialityTw

universe u

section Generic

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- An `L₀`-eigenvector with integral eigenvalue `n` lies in the weight space `𝒱ₙ`. -/
theorem mem_grading_of_L0 (W : VertexOperatorAlgebra 𝒱) {n : ℤ} {x : 𝒱}
    (hL : W.L 0 x = (n : ℂ) • x) : x ∈ W.grading n := by
  classical
  have hcomp : ∀ m : ℤ, m ≠ n → piHom W m x = 0 := by
    intro m hm
    have h1 : piHom W m (W.L 0 x) = (m : ℂ) • piHom W m x := by
      conv_lhs => rw [← DirectSum.sum_support_decompose W.grading x]
      rw [map_sum, map_sum]
      conv_rhs => rw [← DirectSum.sum_support_decompose W.grading x, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hj := (DirectSum.decompose W.grading x j).2
      rw [W.L_zero_grading _ hj, LinearMap.map_smul]
      by_cases hjm : j = m
      · subst hjm; rfl
      · rw [piHom_of_mem_ne W hjm hj, smul_zero, smul_zero]
    rw [hL, LinearMap.map_smul] at h1
    have : ((m : ℂ) - n) • piHom W m x = 0 := by rw [sub_smul, h1, sub_self]
    have hmn : ((m : ℂ) - n) ≠ 0 := by rw [sub_ne_zero]; exact_mod_cast hm
    exact (smul_eq_zero.mp this).resolve_left hmn
  rw [← DirectSum.sum_support_decompose W.grading x]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  by_cases hjn : j = n
  · subst hjn; exact (DirectSum.decompose W.grading x j).2
  · have := hcomp j hjn
    rw [piHom_apply] at this
    rw [this]; exact Submodule.zero_mem _

/-- Automorphisms commute with every Virasoro mode. -/
theorem Aut.map_L {W : VertexOperatorAlgebra 𝒱} (α : Aut W) (n : ℤ) (v : 𝒱) :
    α (W.L n v) = W.L n (α v) := by
  change α (W.smul W.conformalVector (n + 1) v) = W.smul W.conformalVector (n + 1) (α v)
  rw [α.map_smul]
  congr 1
  exact α.map_omega

theorem Aut.map_L_pow {W : VertexOperatorAlgebra 𝒱} (α : Aut W) (n : ℤ) (j : ℕ) (v : 𝒱) :
    α (((W.L n) ^ j) v) = ((W.L n) ^ j) (α v) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, Aut.map_L, ih]

/-- The pull-back of an invariant form along an automorphism. -/
def pullForm {W : VertexOperatorAlgebra 𝒱} (B : InvariantForm W) (α : Aut W) : InvariantForm W where
  form := B.form.compl₁₂ α.toLinearEquiv.toLinearMap α.toLinearEquiv.toLinearMap
  virasoro_adj := by
    intro n a b
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]
    rw [Aut.map_L, Aut.map_L, B.virasoro_adj]

theorem pullForm_isFullyInvariant {W : VertexOperatorAlgebra 𝒱} {B : InvariantForm W}
    (hB : B.IsFullyInvariant) (α : Aut W) : (pullForm B α).IsFullyInvariant := by
  intro wt u hu n a b
  change B.form (α (W.smul u n a)) (α b) = (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1),
      ((j.factorial : ℂ)⁻¹) • B.form (α a) (α (W.smul (((W.L 1) ^ j) u) (2 * wt - n - 2 - (j : ℤ)) b))
  rw [α.map_smul, hB wt (α u) (α.map_grading hu) n (α a) (α b)]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [α.map_smul, Aut.map_L_pow]

/-- **Automorphisms are isometries** of every fully invariant, unit-normalised form on a
CFT-type VOA with `L₁V₁ = 0` (both forms equal the canonical one, `invariantForm_unique_FHL`). -/
theorem aut_isometry {W : VertexOperatorAlgebra 𝒱} (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {B : InvariantForm W}
    (hB : B.IsFullyInvariant) (hn : B.Normalized) (α : Aut W) (a b : 𝒱) :
    B.form (α a) (α b) = B.form a b := by
  have hn' : (pullForm B α).Normalized := by
    change B.form (α W.vacuum) (α W.vacuum) = 1
    rw [show α W.vacuum = W.vacuum from α.map_vacuum]
    exact hn
  have e1 := invariantForm_unique_FHL hne hqp (pullForm_isFullyInvariant hB α) hn'
  have e2 := invariantForm_unique_FHL hne hqp hB hn
  have := congrArg (fun f : LinearMap.BilinForm ℂ 𝒱 => f a b) (e1.trans e2.symm)
  simpa [pullForm] using this

end Generic

/-! ## `V₀⁺ ⟂ V₃⁺` for `leechBV` -/

theorem leechBV_plusFrame (a b : VPlus) :
    leechBV (plusFrameAut a) (plusFrameAut b) = leechBV a b :=
  aut_isometry leechVOAPlus_vacuum_ne_zero leechVOAPlus_L1_one
    (canonicalInvariantForm_isFullyInvariant _ _) leechBV_normalized plusFrameAut a b

/-- **`V₀⁺ ⟂ V₃⁺`** for the canonical form of `V_Λ⁺`. -/
theorem leechBV_frame_orth {a b : VPlus} (ha : a ∈ frameSector 0) (hb : b ∈ frameSector 1) :
    leechBV a b = 0 := by
  have h := leechBV_plusFrame a b
  rw [mem_frameSector'.mp ha, mem_frameSector'.mp hb, Moonshine.Extraspecial.sgn_zero,
    Moonshine.Extraspecial.sgn_one] at h
  have h' : leechBV a b = -leechBV a b := by simpa using h.symm
  linear_combination h' / 2

theorem leechBV_frame_orth' {a b : VPlus} (ha : a ∈ frameSector 1) (hb : b ∈ frameSector 0) :
    leechBV a b = 0 := by
  have h := leechBV_plusFrame a b
  rw [mem_frameSector'.mp ha, mem_frameSector'.mp hb, Moonshine.Extraspecial.sgn_zero,
    Moonshine.Extraspecial.sgn_one] at h
  have h' : leechBV a b = -leechBV a b := by simpa using h.symm
  linear_combination h' / 2

/-! ## `v0Sigma` is an isometry of `leechBV` on `V₀⁺` -/

theorem V0P_coe_smul (u a : V0Sub.carrier) (n : ℤ) :
    ((V0P.smul u n a : V0Sub.carrier) : VPlus) = leechVOAPlus.smul (u : VPlus) n a := by
  rw [PreVertexAlgebra.smul_def]
  change ((mode (V0Sub.YS u) n a : V0Sub.carrier) : VPlus) = _
  rw [VOASubalgebra.mode_YS_coe]
  rfl

theorem V0P_coe_L (n : ℤ) (a : V0Sub.carrier) :
    ((V0P.L n a : V0Sub.carrier) : VPlus) = leechVOAPlus.L n a := by
  change ((V0P.smul V0P.conformalVector (n + 1) a : V0Sub.carrier) : VPlus) = _
  rw [V0P_coe_smul]
  rfl

theorem V0P_coe_L_pow (n : ℤ) (j : ℕ) (a : V0Sub.carrier) :
    ((((V0P.L n) ^ j) a : V0Sub.carrier) : VPlus) = ((leechVOAPlus.L n) ^ j) a := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ', Module.End.mul_apply, V0P_coe_L, ih, pow_succ', Module.End.mul_apply]

/-- `leechBV` restricted to `V₀⁺`, as an invariant form of `V0P`. -/
noncomputable def bv0 : InvariantForm V0P where
  form := leechBV.compl₁₂ V0Sub.carrier.subtype V0Sub.carrier.subtype
  virasoro_adj := by
    intro n a b
    simp only [LinearMap.compl₁₂_apply, Submodule.subtype_apply, V0P_coe_L]
    exact leechBVForm.virasoro_adj n a b

theorem bv0_apply (a b : V0Sub.carrier) : bv0.form a b = leechBV (a : VPlus) b := rfl

theorem bv0_isFullyInvariant : bv0.IsFullyInvariant := by
  intro wt u hu n a b
  rw [bv0_apply, V0P_coe_smul, leechBV_inv wt u hu n a b]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [bv0_apply, V0P_coe_smul, V0P_coe_L_pow]

theorem bv0_normalized : bv0.Normalized := by
  change leechBV ((V0P.vacuum : V0Sub.carrier) : VPlus) (V0P.vacuum : V0Sub.carrier) = 1
  exact leechBV_normalized

theorem V0P_vacuum_ne_zero : V0P.vacuum ≠ 0 := by
  intro h
  apply leechVOAPlus_vacuum_ne_zero
  have := congrArg (fun x : V0Sub.carrier => (x : VPlus)) h
  exact this

theorem V0P_L1_one : ∀ v, v ∈ V0P.grading 1 → V0P.L 1 v = 0 := by
  intro v hv
  apply Subtype.ext
  rw [V0P_coe_L]
  exact leechVOAPlus_L1_one (v : VPlus) hv

/-- **`v0Sigma` is an isometry of `leechBV`** on `V₀⁺`. -/
theorem leechBV_sig (a b : V0Sub.carrier) :
    leechBV ((sig a : V0Sub.carrier) : VPlus) (sig b : V0Sub.carrier) = leechBV (a : VPlus) b :=
  aut_isometry V0P_vacuum_ne_zero V0P_L1_one bv0_isFullyInvariant bv0_normalized v0Sigma a b

/-- `sig0` is self-adjoint on `V₀⁺` for `leechBV`. -/
theorem leechBV_sig_adj (a b : V0Sub.carrier) :
    leechBV ((sig a : V0Sub.carrier) : VPlus) (b : VPlus)
      = leechBV (a : VPlus) (sig b : V0Sub.carrier) := by
  conv_lhs => rw [← sig_sig b]
  exact leechBV_sig a (sig b)

end VOA.Moonshine.SigmaKey
