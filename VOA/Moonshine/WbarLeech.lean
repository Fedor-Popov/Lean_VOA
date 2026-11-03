/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.WbarComm
import VOA.Moonshine.SkewLeech
import VOA.Moonshine.Generation
import VOA.Moonshine.PlusWeightOne
import VOA.Moonshine.PlusWeightTwo

/-!
# M8c: the twisted→untwisted block `W̄` of the moonshine vertex operator

For `t ∈ TP = (V_Λ^T)^+` the operator `W̄(t,z) : TP → VP = V_Λ^+` is the adjoint of the skew
intertwiner `W(t,z) = leechWsk t` (DGM CMP 1996, eq. (4.3)) with respect to

* on `VP`: the **canonical Li/FHL invariant form** `leechBV := (canonicalInvariantForm hne hqp).form`
  (`Core.InvariantFormFHL2`; `V_Λ^+` is of CFT type, `V_1 = 0` so `L₁V₁ = 0`), normalised
  `B(𝟙,𝟙) = 1`, fully invariant (`canonicalInvariantForm_isFullyInvariant`);
* on `TP`: `InvForm.TPForm`, weight-orthogonal (`TPForm_weightOrth`), nondegenerate per weight space,
  and FHL-invariant for **every** homogeneous `u ∈ V_Λ^+` (`TPForm_fhlInv`, `Moonshine.Generation`).

`BV(W̄(t,z)a, φ) = TPForm(a, W(e^{zL₁}(−z⁻²)^{L₀}t, z⁻¹)φ)`.

## Main results

Unconditional:
* `leechWbar t : FormalDist (TP →ₗ VP)` (definition needs no hypothesis);
* `leechWbar_mem` — `t ∈ TP_w`, `a ∈ TP_b` ⟹ `W̄(t)₍ₙ₎a ∈ (V_Λ^+)_{b+w−n−1}`;
* `leechWbar_trunc` — `W̄(t,z)a ∈ VP((z))` (lower truncation);
* `leechWbar_deriv` — `W̄(L₋₁t, z) = ∂_z W̄(t,z)`.

Conditional on **one** named hypothesis `hnd : GradedNondeg leechVOAPlus leechBV` (the canonical
form is nondegenerate on each `(V_Λ^+)_k`; it follows from simplicity of `V_Λ^+`,
`leechBV_gradedNondeg_of_isSimple`):
* `leechWbar_adj` — the defining DGM (4.3) adjunction in modes;
* `leechWbar_comm` — `u₍ₘ₎W̄(t)₍ₙ₎ − W̄(t)₍ₙ₎u₍ₘ₎ = ∑_{r<J} C(m,r) W̄(u₍ᵣ₎t)₍ₘ₊ₙ₋ᵣ₎` for all
  `u ∈ V_Λ^+`;
* `leechWbar_local` — `(z₁−z₂)ᴺ[Y_VP(u,z₁)W̄(t,z₂) − W̄(t,z₂)Y_TP(u,z₁)] = 0`;
* `leechWbar_homCov` — translation covariance `L₋₁W̄ₖ − W̄ₖL₋₁ = (k+1)W̄ₖ₊₁`.

## Status
All declarations proved; no `sorry`/axioms.  The only open input is `hnd` (equivalently, by
`leechBV_gradedNondeg_of_isSimple`, `leechVOAPlus.IsSimple`), which the library does not have:
there is no simplicity theorem for lattice VOAs or their orbifolds in the library.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine

open SkewAdjoint SkewIntertwiner InvForm VertexOperatorAlgebra

theorem leechVOAPlus_vacuum_ne_zero : leechVOAPlus.vacuum ≠ 0 := by
  intro h0
  have hall : ∀ x : VPlus, x = 0 := fun x => by
    rw [← (leechVOAPlus.smul_vacuum_right x).1, h0, leechVOAPlus.smul_zero_right]
  have hb : leechVOAPlus.grading 2 = ⊥ :=
    eq_bot_iff.2 fun x _ => (Submodule.mem_bot ℂ).2 (hall x)
  have h2 := leechVOAPlus_finrank_grading_two
  rw [hb, finrank_bot] at h2
  norm_num at h2

/-- `L₁V₁ = 0` for `V_Λ^+` (since `V₁ = 0`). -/
theorem leechVOAPlus_L1_one : ∀ v, v ∈ leechVOAPlus.grading 1 → leechVOAPlus.L 1 v = 0 := by
  intro v hv
  rw [leechVOAPlus_grading_one, Submodule.mem_bot] at hv
  rw [hv, map_zero]

/-- The canonical (Li/FHL) invariant form on `V_Λ^+`, normalised `(𝟙|𝟙) = 1`. -/
noncomputable def leechBVForm : InvariantForm leechVOAPlus :=
  canonicalInvariantForm leechVOAPlus_vacuum_ne_zero leechVOAPlus_L1_one

/-- The bilinear form `B_V` on `VP`. -/
noncomputable abbrev leechBV : LinearMap.BilinForm ℂ SkewVP := leechBVForm.form

theorem leechBV_normalized : leechBV leechVOAPlus.vacuum leechVOAPlus.vacuum = 1 :=
  canonicalInvariantForm_normalized leechVOAPlus_vacuum_ne_zero leechVOAPlus_L1_one

theorem leechBV_orth : GradedOrth leechVOAPlus leechBV := gradedOrth_of_invariantForm _

theorem leechBV_inv : VInv leechVOAPlus leechBV :=
  vInv_of_isFullyInvariant _ (canonicalInvariantForm_isFullyInvariant _ _)

/-- Weight-space nondegeneracy of `B_V` follows from simplicity of `V_Λ^+`. -/
theorem leechBV_gradedNondeg_of_isSimple (hsimple : leechVOAPlus.IsSimple) :
    GradedNondeg leechVOAPlus leechBV :=
  gradedNondeg_of_radical _ (invariantForm_nondegenerate_FHL _ _ hsimple)

/-- **The field `W̄(t,z) ∈ Hom(TP, VP)⟦z^±⟧`**, the adjoint of `leechWsk t`. -/
noncomputable def leechWbar (t : TP) : FormalDist (TP →ₗ[ℂ] SkewVP) :=
  Wbar leechBV plusModule TPForm TPForm_weightOrth t

/-- The modes `W̄(t)₍ₙ₎`. -/
noncomputable def leechWbarMode (n : ℤ) (t : TP) : TP →ₗ[ℂ] SkewVP :=
  WbarMode leechBV plusModule TPForm TPForm_weightOrth n t

theorem mode_leechWbar (t : TP) (n : ℤ) : mode (leechWbar t) n = leechWbarMode n t :=
  mode_Wbar _ _ _ _ t n

theorem leechWbar_coeff (t : TP) (k : ℤ) : leechWbar t k = leechWbarMode (-k - 1) t := rfl

/-- `W̄` is linear in `t`. -/
theorem leechWbarMode_add (n : ℤ) (t t' : TP) :
    leechWbarMode n (t + t') = leechWbarMode n t + leechWbarMode n t' := WbarMode_add _ _ _ _ n t t'

theorem leechWbarMode_smul (n : ℤ) (c : ℂ) (t : TP) :
    leechWbarMode n (c • t) = c • leechWbarMode n t := WbarMode_smul _ _ _ _ n c t

/-! ## Unconditional properties -/

/-- **Grading**: `t ∈ TP_w`, `a ∈ TP_b` ⟹ `W̄(t)₍ₙ₎a ∈ (V_Λ^+)_{b+w−n−1}`. -/
theorem leechWbar_mem (n : ℤ) {w b : ℤ} {t a : TP} (ht : t ∈ plusModule.weight (w : ℂ))
    (ha : a ∈ plusModule.weight (b : ℂ)) :
    leechWbarMode n t a ∈ leechVOAPlus.grading (b + w - n - 1) :=
  WbarMode_mem n ht ha

/-- **Lower truncation**: `W̄(t,z)a ∈ VP((z))`. -/
theorem leechWbar_trunc (t : TP) :
    ∀ a : TP, ∃ B : ℤ, ∀ k : ℤ, k < B → leechWbar t k a = 0 :=
  Wbar_trunc t

/-- **`leechWbar_deriv`**: `W̄(L₋₁t, z) = ∂_z W̄(t, z)`. -/
theorem leechWbar_deriv (t : TP) : leechWbar (leechLTP t) = deriv (leechWbar t) :=
  Wbar_deriv _ _ _ _ t

/-! ## Properties conditional on weight-space nondegeneracy of `B_V` -/

variable (hnd : GradedNondeg leechVOAPlus leechBV)
include hnd

/-- **The DGM (4.3) adjunction**, for `t ∈ TP_w` and any sufficient `j`-bound `R`:
`B_V(W̄(t)₍ₙ₎a, φ) = (−1)^w ∑_{j<R} (1/j!) TPForm(a, W(L₁ʲt)₍₂w−n−2−j₎φ)`. -/
theorem leechWbar_adj (n : ℤ) {w : ℤ} {t : TP} (ht : t ∈ plusModule.weight (w : ℂ)) (R : ℕ)
    (hR : ∀ j : ℕ, R ≤ j → (Lp1 plusModule ^ j) t = 0) (a : TP) (φ : SkewVP) :
    leechBV (leechWbarMode n t a) φ = (-1 : ℂ) ^ w • ∑ j ∈ Finset.range R,
      ((j.factorial : ℂ)⁻¹) • TPForm a (mode (leechWsk ((Lp1 plusModule ^ j) t))
        (2 * w - n - 2 - j) φ) := by
  simp only [leechWsk, mode_Wsk, wModeLin_apply]
  exact form_WbarMode_int leechBV_orth hnd n ht R hR a φ

/-- **`leechWbar_comm`**: the intertwining commutator formula of `W̄`, for every
`u ∈ V_Λ^+` and `J` past the truncation of `u` on `t`:
`u₍ₘ₎ W̄(t)₍ₙ₎a − W̄(t)₍ₙ₎(u₍ₘ₎a) = ∑_{r<J} C(m,r) W̄(u₍ᵣ₎t)₍ₘ₊ₙ₋ᵣ₎a`. -/
theorem leechWbar_comm (u : SkewVP) (m : ℤ) (t : TP) (n : ℤ) (a : TP) (J : ℕ)
    (hJ : ∀ j : ℕ, J ≤ j → mode (plusModule.YM u) j t = 0) :
    leechVOAPlus.smul u m (leechWbarMode n t a) - leechWbarMode n t (mode (plusModule.YM u) m a)
      = ∑ r ∈ Finset.range J,
          gBinom m r • leechWbarMode (m + n - r) (mode (plusModule.YM u) r t) a :=
  WbarMode_comm leechBV_orth hnd leechBV_inv (fun _ _ hu => TPForm_fhlInv hu) leechVOAPlus_L1_one
    u m t n a J hJ

/-- **`leechWbar_local`**: `Y_VP(u,z₁)` and `W̄(t,z₂)` are mutually local,
`(z₁−z₂)ᴺ [Y_VP(u,z₁) W̄(t,z₂) − W̄(t,z₂) Y_TP(u,z₁)] = 0` in `Hom(TP,VP)⟦z₁^±,z₂^±⟧` — the
`c'`-hypothesis of `VnatBlock.local_diag_off` with `a = Y_VP(u)`, `b = Y_TP(u)`, `c' = W̄(t)`. -/
theorem leechWbar_local (u : SkewVP) (t : TP) :
    ∃ N : ℕ, mulBySubPow N
      (fun a b => (leechVOAPlus.Y u a).comp (leechWbar t b)
        - (leechWbar t b).comp (plusModule.YM u a) : FormalDist₂ (TP →ₗ[ℂ] SkewVP)) = 0 :=
  Wbar_local leechBV_orth hnd leechBV_inv (fun _ _ hu => TPForm_fhlInv hu) leechVOAPlus_L1_one u t

/-- **Translation covariance** (`VnatBlock.HomCov (leechLTP) (L₋₁) (leechWbar t)` shape):
`L₋₁ ∘ W̄(t)ₖ − W̄(t)ₖ ∘ L₋₁ᵀᴾ = (k+1) • W̄(t)ₖ₊₁`. -/
theorem leechWbar_homCov (t : TP) (k : ℤ) :
    leechVOAPlus.L (-1) ∘ₗ leechWbar t k - leechWbar t k ∘ₗ leechLTP
      = (k + 1 : ℤ) • leechWbar t (k + 1) :=
  Wbar_homCov leechBV_orth hnd leechBV_inv (fun _ _ hu => TPForm_fhlInv hu) leechVOAPlus_L1_one t k

end VOA.Moonshine
