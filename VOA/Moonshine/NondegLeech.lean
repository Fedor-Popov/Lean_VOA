/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.NondegLattice
import VOA.Moonshine.WbarLeech

/-!
# Nondegeneracy of the canonical form on `V_Λ^+`, and the unconditional `W̄`  (M8c, `hnd`)

Discharges the residual `hnd : GradedNondeg leechVOAPlus leechBV` of `Moonshine.WbarLeech`.

Route (no simplicity of `V_Λ^+` is used):

1. `plusForm` — the restriction to `V_Λ^+` of the explicit form `Nondeg.latForm leech` on `V_Λ`
   (`(p ⊗ e^α, q ⊗ e^β) = δ_{α+β,0} (−1)^{⟨α,α⟩/2} ε(α,α) F(p,q)`, `NondegLattice.lean`).
2. `plusForm_fhlInv_frameX0P` — FHL invariance at the generators `e^β + e^{−β}` (from
   `latForm_Yeαvec`); `plusForm_fhlInv` — invariance for **every** homogeneous `u ∈ V_Λ^+`, by
   the generator reduction `InvForm.fhlInv_of_generates` for the adjoint module and
   `leechPlus_generated`.
3. `plusInvForm : InvariantForm leechVOAPlus` — fully invariant (`plusInvForm_isFullyInvariant`)
   and unit-normalised (`plusInvForm_normalized`); the Virasoro adjointness is the `u = ω` slice
   (`L₁ω ∈ (V_Λ^+)₁ = 0`).
4. `leechBV_eq_plusForm` — by the unconditional uniqueness `invariantForm_unique_FHL`, the
   library's canonical form `leechBV` **is** `plusForm`.
5. `leechBVForm_leftRadical` — the radical is `0`: `latForm` is nondegenerate on `V_Λ`
   (`latForm_nondeg`) and `θ` is an isometry (`latForm_thetaLat`), so `x ∈ V_Λ^+` pairs with
   `½(y + θy) ∈ V_Λ^+` exactly as with `y`.
6. `leechBV_gradedNondeg : GradedNondeg leechVOAPlus leechBV` (via `gradedNondeg_of_radical`).

Unconditional `W̄` theorems (the conditional ones of `WbarLeech` applied to step 6):
`leechWbar_adj'`, `leechWbar_comm'`, `leechWbar_local'`, `leechWbar_homCov'`.

## Status
All declarations proved; no `sorry`/axioms.  `#print axioms` of `leechBV_gradedNondeg` and of the
four primed `W̄` theorems: `[propext, Classical.choice, Quot.sound]` (not even `VOA.pbw`).
Unconditional: no hypotheses remain on any of the listed theorems.  The file is imported by the
umbrella `VOA/Moonshine.lean`.  This does **not** prove simplicity of
`V_Λ^+` (it is not needed here), nor anything about the twisted×twisted block (M8h).
-/

set_option linter.style.longLine false

namespace VOA.Moonshine

open SkewAdjoint SkewIntertwiner InvForm VertexOperatorAlgebra LatGen IntegralLattice

/-! ## The restricted form -/

/-- The explicit form on `V_Λ^+`: the restriction of `Nondeg.latForm leech`. -/
noncomputable def plusForm : LinearMap.BilinForm ℂ VPlus :=
  (Nondeg.latForm leech).compl₁₂ (orbifold (Subgroup.zpowers leechTheta)).carrier.subtype
    (orbifold (Subgroup.zpowers leechTheta)).carrier.subtype

@[simp] theorem plusForm_apply (x y : VPlus) :
    plusForm x y = Nondeg.latForm leech (x : LatModuleGen leech) (y : LatModuleGen leech) := rfl

/-- Distinct weight spaces of the adjoint module `V_Λ^+` are `plusForm`-orthogonal. -/
theorem plusForm_weightOrth : WeightOrth (adjointModule leechVOAPlus) plusForm := by
  intro α β hαβ x hx y hy
  change x ∈ adjWeight leechVOAPlus α at hx
  change y ∈ adjWeight leechVOAPlus β at hy
  by_cases hα : ∃ m : ℤ, (m : ℂ) = α
  · by_cases hβ : ∃ m : ℤ, (m : ℂ) = β
    · obtain ⟨m, rfl⟩ := hα
      obtain ⟨k, rfl⟩ := hβ
      rw [adjWeight_cast] at hx hy
      have hmk : m ≠ k := fun h => hαβ (by rw [h])
      exact Nondeg.latForm_orth_grading leech hmk hx hy
    · rw [adjWeight_eq_bot leechVOAPlus (not_exists.mp hβ), Submodule.mem_bot] at hy
      rw [hy, map_zero]
  · rw [adjWeight_eq_bot leechVOAPlus (not_exists.mp hα), Submodule.mem_bot] at hx
    rw [hx, map_zero, LinearMap.zero_apply]

theorem leechVOA_smul_latChargeGen_mode (γ : leech.carrier) (n : ℤ) (x : LatModuleGen leech) :
    leechVOA.smul (latChargeGen leech γ) n x = mode (Yeαvec leech γ) n x := by
  rw [PreVertexAlgebra.smul_def, leechVOA_Y_latChargeGen]

theorem coe_mode_frameX0P (β : leech.carrier) (n : ℤ) (a : VPlus) :
    ((mode ((adjointModule leechVOAPlus).YM (frameX0P β)) n a : VPlus) : LatModuleGen leech)
      = mode (Yeαvec leech β) n a + mode (Yeαvec leech (-β)) n a := by
  change leechVOA.smul (frameX0 β) n (a : LatModuleGen leech) = _
  rw [frameX0, PreVertexAlgebra.smul_add_left, leechVOA_smul_latChargeGen_mode,
    leechVOA_smul_latChargeGen_mode]

/-- Invariance at `e^β + e^{−β}` in the primary form `(u₍ₙ₎a, b) = (−1)^N (a, u₍₂N−n−2₎ b)`. -/
theorem plusForm_invariant_frameX0P (β : leech.carrier) (n : ℤ) (a b : VPlus) :
    plusForm (mode ((adjointModule leechVOAPlus).YM (frameX0P β)) n a) b
      = (-1 : ℂ) ^ (LatGen.halfNorm leech β) *
          plusForm a (mode ((adjointModule leechVOAPlus).YM (frameX0P β))
            (2 * LatGen.halfNorm leech β - n - 2) b) := by
  rw [plusForm_apply, plusForm_apply, coe_mode_frameX0P, coe_mode_frameX0P, map_add,
    LinearMap.add_apply, map_add, Nondeg.latForm_Yeαvec leech leech_even,
    Nondeg.latForm_Yeαvec leech leech_even, LatGen.halfNorm_neg, mul_add]

/-- **FHL invariance of `plusForm` at the generators `e^β + e^{−β}`**. -/
theorem plusForm_fhlInv_frameX0P (β : leech.carrier) :
    FHLInv (adjointModule leechVOAPlus) plusForm (LatGen.halfNorm leech β) (frameX0P β) := by
  intro n a b
  rw [Finset.sum_eq_single 0]
  · rw [plusForm_invariant_frameX0P, pow_zero, Module.End.one_apply, Nat.factorial_zero,
      Nat.cast_one, inv_one, one_smul, Nat.cast_zero, sub_zero, smul_eq_mul]
  · intro j _ hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    rw [pow_succ, Module.End.mul_apply, L_one_frameX0P, map_zero, map_zero, mode_zero,
      LinearMap.zero_apply, map_zero, smul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **Full FHL invariance of `plusForm`** for every homogeneous `u ∈ V_Λ^+` (unconditional,
via `leechPlus_generated`). -/
theorem plusForm_fhlInv {wt : ℤ} {u : VPlus} (hu : u ∈ leechVOAPlus.grading wt) :
    FHLInv (adjointModule leechVOAPlus) plusForm wt u :=
  fhlInv_of_generates plusForm_weightOrth (Set.range frameX0P)
    (fun S h0 h1 hG => leechPlus_generated S h0 h1 (fun β => hG ⟨β, rfl⟩))
    (by rintro _ ⟨β, rfl⟩; exact ⟨_, frameX0P_mem_grading β, plusForm_fhlInv_frameX0P β⟩) hu

/-! ## The invariant form and its identification with the canonical one -/

theorem leechVOAPlus_L1_omega : leechVOAPlus.L 1 leechVOAPlus.conformalVector = 0 := by
  have h := VertexOperatorAlgebra.L_one_lower leechVOAPlus leechVOAPlus.conformal_mem
  rw [show (2 : ℤ) - 1 = 1 by norm_num, leechVOAPlus_grading_one] at h
  exact (Submodule.mem_bot ℂ).1 h

/-- `plusForm` as an `InvariantForm` of `V_Λ^+`. -/
noncomputable def plusInvForm : InvariantForm leechVOAPlus where
  form := plusForm
  virasoro_adj := by
    intro n a b
    have h := plusForm_fhlInv leechVOAPlus.conformal_mem (n + 1) a b
    rw [Finset.sum_eq_single 0] at h
    · rw [VertexOperatorAlgebra.L_def, VertexOperatorAlgebra.L_def]
      refine h.trans ?_
      rw [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one,
        one_smul, Nat.cast_zero, sub_zero, show (2 : ℤ) * 2 - (n + 1) - 2 = -n + 1 by ring]
      norm_num
      rfl
    · intro j _ hj
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
      rw [pow_succ, Module.End.mul_apply, leechVOAPlus_L1_omega, map_zero, map_zero, mode_zero,
        LinearMap.zero_apply, map_zero, smul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (by norm_num)) h

theorem plusInvForm_form : plusInvForm.form = plusForm := rfl

theorem plusInvForm_isFullyInvariant : plusInvForm.IsFullyInvariant :=
  fun _ _ hu n a b => plusForm_fhlInv hu n a b

theorem plusInvForm_normalized : plusInvForm.Normalized := by
  change plusForm leechVOAPlus.vacuum leechVOAPlus.vacuum = 1
  rw [plusForm_apply, plus_vacuum_coe, latVacuumGen, Nondeg.latForm_state, add_zero,
    if_pos rfl, Nondeg.chSign_zero, one_mul, HeisenbergN.vacuumN, Nondeg.uForm_one, MvPolynomial.coeff_zero_one]

/-- **The library's canonical invariant form on `V_Λ^+` is the explicit `plusForm`**
(uniqueness of the normalised fully-invariant form, `invariantForm_unique_FHL`). -/
theorem leechBV_eq_plusForm : leechBV = plusForm :=
  (invariantForm_unique_FHL leechVOAPlus_vacuum_ne_zero leechVOAPlus_L1_one
    plusInvForm_isFullyInvariant plusInvForm_normalized).symm

/-! ## Nondegeneracy -/

/-- `plusForm` has trivial radical: every nonzero `x ∈ V_Λ^+` pairs nontrivially with
`½(y + θy) ∈ V_Λ^+`, where `latForm x y ≠ 0`. -/
theorem plusForm_nondeg (x : VPlus) (hx : x ≠ 0) : ∃ y : VPlus, plusForm x y ≠ 0 := by
  have hx' : (x : LatModuleGen leech) ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨y, hy⟩ := Nondeg.latForm_nondeg leech _ hx'
  refine ⟨plusProj y, ?_⟩
  have hθx : thetaLat leech (x : LatModuleGen leech) = x := (mem_leechVOAPlus_iff _).mp x.2
  have hθ : Nondeg.latForm leech (x : LatModuleGen leech) (thetaLat leech y)
      = Nondeg.latForm leech (x : LatModuleGen leech) y := by
    rw [← Nondeg.latForm_thetaLat leech (x : LatModuleGen leech) y, hθx]
  rw [plusForm_apply, plusProj_coe, map_smul, map_add, hθ, ← two_mul, smul_eq_mul, ← mul_assoc]
  norm_num
  exact hy

/-- **The canonical invariant form on `V_Λ^+` is nondegenerate** (trivial radical). -/
theorem leechBVForm_leftRadical : InvariantForm.leftRadical leechBVForm = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [InvariantForm.mem_leftRadical] at hx
  rw [Submodule.mem_bot]
  by_contra h0
  obtain ⟨y, hy⟩ := plusForm_nondeg x h0
  apply hy
  have h := DFunLike.congr_fun hx y
  rw [LinearMap.zero_apply] at h
  rw [← h, ← leechBV_eq_plusForm]

/-- **The residual `hnd`, discharged**: the canonical invariant form of `V_Λ^+` is
nondegenerate on every weight space. -/
theorem leechBV_gradedNondeg : GradedNondeg leechVOAPlus leechBV :=
  gradedNondeg_of_radical _ leechBVForm_leftRadical

/-! ## The unconditional `W̄` theorems -/

/-- **The DGM (4.3) adjunction for `W̄`, unconditional.** -/
theorem leechWbar_adj' (n : ℤ) {w : ℤ} {t : TP} (ht : t ∈ plusModule.weight (w : ℂ)) (R : ℕ)
    (hR : ∀ j : ℕ, R ≤ j → (Lp1 plusModule ^ j) t = 0) (a : TP) (φ : SkewVP) :
    leechBV (leechWbarMode n t a) φ = (-1 : ℂ) ^ w • ∑ j ∈ Finset.range R,
      ((j.factorial : ℂ)⁻¹) • TPForm a (mode (leechWsk ((Lp1 plusModule ^ j) t))
        (2 * w - n - 2 - j) φ) :=
  leechWbar_adj leechBV_gradedNondeg n ht R hR a φ

/-- **The intertwining commutator formula for `W̄`, unconditional**:
`u₍ₘ₎ W̄(t)₍ₙ₎a − W̄(t)₍ₙ₎(u₍ₘ₎a) = ∑_{r<J} C(m,r) W̄(u₍ᵣ₎t)₍ₘ₊ₙ₋ᵣ₎a` for all `u ∈ V_Λ^+`. -/
theorem leechWbar_comm' (u : SkewVP) (m : ℤ) (t : TP) (n : ℤ) (a : TP) (J : ℕ)
    (hJ : ∀ j : ℕ, J ≤ j → mode (plusModule.YM u) j t = 0) :
    leechVOAPlus.smul u m (leechWbarMode n t a) - leechWbarMode n t (mode (plusModule.YM u) m a)
      = ∑ r ∈ Finset.range J,
          gBinom m r • leechWbarMode (m + n - r) (mode (plusModule.YM u) r t) a :=
  leechWbar_comm leechBV_gradedNondeg u m t n a J hJ

/-- **Locality of `Y_VP(u,z₁)` and `W̄(t,z₂)`, unconditional.** -/
theorem leechWbar_local' (u : SkewVP) (t : TP) :
    ∃ N : ℕ, mulBySubPow N
      (fun a b => (leechVOAPlus.Y u a).comp (leechWbar t b)
        - (leechWbar t b).comp (plusModule.YM u a) : FormalDist₂ (TP →ₗ[ℂ] SkewVP)) = 0 :=
  leechWbar_local leechBV_gradedNondeg u t

/-- **Translation covariance of `W̄`, unconditional.** -/
theorem leechWbar_homCov' (t : TP) (k : ℤ) :
    leechVOAPlus.L (-1) ∘ₗ leechWbar t k - leechWbar t k ∘ₗ leechLTP
      = (k + 1 : ℤ) • leechWbar t (k + 1) :=
  leechWbar_homCov leechBV_gradedNondeg t k

end VOA.Moonshine
