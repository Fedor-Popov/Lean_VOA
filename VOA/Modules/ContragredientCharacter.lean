/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ContragredientJacobi
import VOA.Modules.ZhuAlgebra

/-!
# The contragredient one-point function for quasi-primary states  (Gannon §5.3.1)

The one-point refinement `χ_{M*}(τ,v) = (-1)ⁿ χ_M(τ,v)` of the contragredient, proved here
**exactly** for **quasi-primary** `v ∈ 𝒱ₙ` (`L₁v = 0`) — riding on the full contragredient module
`contragredient N hJac` (parametric in `ContragredientJacobi N`, the module Jacobi 5.3.1b).

For `v ∈ 𝒱ₙ` the contragredient zero mode `o_{M*}(v)` is weight-preserving (`dualOutIdx n (n−1) = id`)
and, when `L₁v = 0`, its companion functional `dualCompMap N n v (n−1)` collapses to the single
`j = 0` term `(-1)ⁿ·(g ∘ proj ∘ v₍n−1₎)` (`dualCompMap_quasiprimary`). Hence on each weight block
`o_{M*}(v)` is exactly `(-1)ⁿ` times the **transpose** of `o_M(v)` (`weightBlock_contra_eq_conj`),
and since trace is transpose-invariant and conjugation-invariant
(`LinearMap.trace_transpose'`/`trace_conj'`) the graded traces satisfy
`tr_{(M*)_α} o_{M*}(v) = (-1)ⁿ tr_{M_α} o_M(v)` (`trace_weightBlock_contra`), i.e.
**`onePoint_contragredient`**: `χ_{M*}(τ,v) = (-1)ⁿ χ_M(τ,v)`.

For a *non*-quasi-primary `v` the identity acquires explicit `L₁`-correction terms
`∑_{j≥1}(1/j!) tr o((L₁ʲv))` (the `j ≥ 1` tail of `dualCompMap`), so the bare `(-1)ⁿ` form is
specific to `L₁v = 0`; the general one-point refinement rides on the same action and is not
proved here.

## Status
Axiom-clean for the **quasi-primary** one-point function `onePoint_contragredient` and its
supporting block/trace identities. The single hypothesis `ContragredientJacobi N` they were
parametric in is proved unconditionally (`Modules.ContragredientClose`,
`contragredientJacobi_holds`), so `onePoint_contragredient … (contragredientJacobi_holds N)` is
unconditional. (The *general*-`v` one-point refinement, with `L₁`-correction tail, is not proved
here.)

## References
* Gannon §5.3.1, eqs. (5.3.4)–(5.3.5), (5.3.13); Frenkel–Huang–Lepowsky [199]; Li [380].
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End Dual)
open scoped BigOperators
open Classical

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M] {v : 𝒱}

/-! ## Step 1: the quasi-primary collapse of `dualCompMap`.

For `v ∈ 𝒱ₙ` with `W.L 1 v = 0`, `dualCompMap N n v (n-1) γ g` collapses to its single
`j = 0` term: `(-1)^n • (g ∘ proj_γ ∘ v₍n-1₎)`. -/

/-- `(W.L 1)^(j+1) v = 0` whenever `W.L 1 v = 0`. -/
theorem L_one_pow_succ_eq_zero (hv : W.L 1 v = 0) (j : ℕ) :
    ((W.L 1) ^ (j + 1)) v = 0 := by
  rw [pow_succ, Module.End.mul_apply, hv, map_zero]

/-- **Quasi-primary collapse.** For `v ∈ 𝒱ₙ` quasi-primary (`L₁v = 0`), the contragredient
companion functional at the weight-preserving index `n-1` is `(-1)^n • (g ∘ proj_γ ∘ v₍n-1₎)`. -/
theorem dualCompMap_quasiprimary (N : OrdVModule W M) {n : ℤ} (hv : W.L 1 v = 0) (γ : ℂ)
    (g : Module.Dual ℂ (N.weight γ)) (x : M) :
    dualCompMap N n v (n - 1) γ g x
      = (-1 : ℂ) ^ n • g (internalProjTo N.isInternal γ (mode (N.YM v) (n - 1) x)) := by
  rw [dualCompMap_apply]
  -- index: 2n - (n-1) - 2 - j = n - 1 - j; only j = 0 survives since (W.L 1)^j v = 0 for j ≥ 1
  congr 1
  rcases le_or_gt n 0 with hn | hn
  · -- n ≤ 0 ⟹ n.toNat = 0 ⟹ range is {0}
    rw [show n.toNat + 1 = 1 from by omega, Finset.sum_range_one]
    simp only [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
    congr 2
    rw [show (2 * n - (n - 1) - 2 - ((0 : ℕ) : ℤ) : ℤ) = n - 1 from by push_cast; ring]
  · -- n ≥ 1 : split off the j = 0 term, kill the rest
    rw [Finset.sum_eq_single 0 (fun j _ hj => ?_) (fun h => ?_)]
    · simp only [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
      congr 2
      rw [show (2 * n - (n - 1) - 2 - ((0 : ℕ) : ℤ) : ℤ) = n - 1 from by push_cast; ring]
    · -- j ≠ 0 : (W.L 1)^j v = 0
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [L_one_pow_succ_eq_zero hv, map_zero,
        show mode (0 : (Module.End ℂ M)⟦z^±⟧) (2 * n - (n - 1) - 2 - ((j' + 1 : ℕ) : ℤ)) = 0 from rfl,
        LinearMap.zero_apply, map_zero, map_zero, smul_zero]
    · exact absurd (Finset.mem_range.mpr (by omega)) h

/-! ## Step 2: the contragredient zero mode on a graded generator `lof α g`.

For `v ∈ 𝒱ₙ` quasi-primary, `o_{M*}(v)` is weight-preserving and acts on `lof α g` by
`lof α ((-1)^n • (g ∘ B))` where `B = weightBlock N (oMod N v) α : End (M_α)`. -/

/-- The contragredient zero mode on a graded generator, for quasi-primary `v ∈ 𝒱ₙ`. -/
theorem oMod_contra_lof (N : OrdVModule W M) (hJac : ContragredientJacobi N) {n : ℤ}
    (hvn : v ∈ W.grading n) (hv : W.L 1 v = 0) (α : ℂ) (g : Module.Dual ℂ (N.weight α)) :
    oMod (contragredient N hJac) v
        (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α g)
      = DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α
          ((-1 : ℂ) ^ n • Module.Dual.transpose (weightBlock N (oMod N v) α) g) := by
  -- the contragredient zero mode is mode (YMdual N v) (n-1) on lof, landing in slot α
  rw [oMod_homogeneous (contragredient N hJac) hvn]
  -- (contragredient N hJac).YM = YMdual N definitionally
  show mode (YMdual N v) (n - 1)
      (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α g) = _
  rw [mode_YMdual_homogeneous N hvn (n - 1), dualModeEndo_lof,
    show dualOutIdx n (n - 1) α = α from by simp only [dualOutIdx]; push_cast; ring]
  -- now compute restrictToWeight α (dualCompMap N n v (n-1) α g) = (-1)^n • transpose B g
  congr 1
  refine LinearMap.ext (fun y => ?_)
  show restrictToWeight N α (dualCompMap N n v (n - 1) α g) y
      = ((-1 : ℂ) ^ n • Module.Dual.transpose (weightBlock N (oMod N v) α) g) y
  unfold restrictToWeight
  rw [LinearMap.lcomp_apply, Submodule.subtype_apply, dualCompMap_quasiprimary N hv α g]
  -- RHS: ((-1)^n • (g ∘ B)) y = (-1)^n • g (B y)
  rw [LinearMap.smul_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
  -- B y = weightBlock N (oMod N v) α y = proj_α (oMod N v (incl y))
  congr 2
  show internalProjTo N.isInternal α (mode (N.YM v) (n - 1) ((N.weight α).subtype y))
      = weightBlock N (oMod N v) α y
  rw [show weightBlock N (oMod N v) α y
      = internalProjTo N.isInternal α (oMod N v ((N.weight α).subtype y)) from rfl,
    oMod_homogeneous N hvn]

/-! ## Step 3: the `range(lof α) ≃ Dual(M_α)` identification and the trace. -/

/-- `lof α` is injective (its component projection is a left inverse). -/
theorem lof_injective (N : OrdVModule W M) (α : ℂ) :
    Function.Injective (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α) := by
  have h : Function.LeftInverse
      (DirectSum.component ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α)
      (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α) := fun g =>
    DirectSum.component.lof_self (R := ℂ) (ι := ℂ)
      (M := fun β => Module.Dual ℂ (N.weight β)) α g
  exact h.injective

/-- The linear equivalence `(M_α)* ≃ (M*)_α` realizing the contragredient's `α`-weight space
as the dual of `M_α`. -/
noncomputable def lofEquiv (N : OrdVModule W M) (α : ℂ) :
    Module.Dual ℂ (N.weight α) ≃ₗ[ℂ] (RestrictedDual.weight N α) :=
  LinearEquiv.ofInjective _ (lof_injective N α)

@[simp] theorem lofEquiv_coe (N : OrdVModule W M) (α : ℂ) (g : Module.Dual ℂ (N.weight α)) :
    ((lofEquiv N α g : RestrictedDual.weight N α) : RestrictedDual N)
      = DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α g := rfl

/-- The contragredient projection back onto its `α`-weight space, applied to `lof α h`,
is `lofEquiv N α h`. -/
theorem internalProjTo_contra_lof (N : OrdVModule W M) (hJac : ContragredientJacobi N) (α : ℂ)
    (h : Module.Dual ℂ (N.weight α)) :
    internalProjTo (contragredient N hJac).isInternal α
        (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α h)
      = lofEquiv N α h := by
  apply Subtype.ext
  have hmem : DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α h
      ∈ (contragredient N hJac).weight α := ⟨h, rfl⟩
  have hkey := internalProjTo_coe (contragredient N hJac).isInternal α
    ⟨DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α h, hmem⟩
  show ((internalProjTo (contragredient N hJac).isInternal α
      (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α h)) : RestrictedDual N)
      = ((lofEquiv N α h : RestrictedDual.weight N α) : RestrictedDual N)
  rw [lofEquiv_coe]
  exact congrArg Subtype.val hkey

/-- **The weight block of the contragredient zero mode is the conjugate of `(-1)ⁿ`-transpose**
of the block of `N`'s zero mode (for quasi-primary `v ∈ 𝒱ₙ`). -/
theorem weightBlock_contra_eq_conj (N : OrdVModule W M) (hJac : ContragredientJacobi N) {n : ℤ}
    (hvn : v ∈ W.grading n) (hv : W.L 1 v = 0) (α : ℂ) :
    weightBlock (contragredient N hJac) (oMod (contragredient N hJac) v) α
      = (lofEquiv N α).conj
          ((-1 : ℂ) ^ n • Module.Dual.transpose (weightBlock N (oMod N v) α)) := by
  refine LinearMap.ext (fun y => ?_)
  -- write y = lof α g' for g' = (lofEquiv N α).symm y
  obtain ⟨g', rfl⟩ : ∃ g', lofEquiv N α g' = y := ⟨(lofEquiv N α).symm y, by simp⟩
  -- LHS
  show internalProjTo (contragredient N hJac).isInternal α
      (oMod (contragredient N hJac) v
        (((contragredient N hJac).weight α).subtype (lofEquiv N α g'))) = _
  rw [show (((contragredient N hJac).weight α).subtype (lofEquiv N α g'))
      = DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α g' from rfl,
    oMod_contra_lof N hJac hvn hv α g', internalProjTo_contra_lof N hJac α]
  -- RHS: (conj F) (lofEquiv g') is defeq to lofEquiv (F ((lofEquiv).symm (lofEquiv g')))
  show _ = lofEquiv N α
      (((-1 : ℂ) ^ n • Module.Dual.transpose (weightBlock N (oMod N v) α))
        ((lofEquiv N α).symm (lofEquiv N α g')))
  rw [LinearEquiv.symm_apply_apply, LinearMap.smul_apply]

/-- **Coefficientwise trace identity.** For quasi-primary `v ∈ 𝒱ₙ`, the graded trace of the
contragredient zero-mode block equals `(-1)ⁿ` times the graded trace of `N`'s zero-mode block. -/
theorem trace_weightBlock_contra (N : OrdVModule W M) (hJac : ContragredientJacobi N) {n : ℤ}
    (hvn : v ∈ W.grading n) (hv : W.L 1 v = 0) (α : ℂ)
    [FiniteDimensional ℂ (N.weight α)] :
    LinearMap.trace ℂ (RestrictedDual.weight N α)
        (weightBlock (contragredient N hJac) (oMod (contragredient N hJac) v) α)
      = (-1 : ℂ) ^ n • LinearMap.trace ℂ _ (weightBlock N (oMod N v) α) := by
  rw [weightBlock_contra_eq_conj N hJac hvn hv α, LinearMap.trace_conj', map_smul,
    LinearMap.trace_transpose', smul_eq_mul]

/-! ## Step 4: the one-point function identity (the goal). -/

/-- **Contragredient one-point function for quasi-primary states** (Gannon §5.3.1).
For a homogeneous quasi-primary `v ∈ 𝒱ₙ` (`W.L 1 v = 0`, so `n ≥ 0`),
`χ_{M*}(τ, v) = (-1)ⁿ χ_M(τ, v)`. -/
theorem onePoint_contragredient (N : OrdVModule W M) (hJac : ContragredientJacobi N) {n : ℤ}
    (hvn : v ∈ W.grading n) (hv : W.L 1 v = 0) :
    onePoint (contragredient N hJac) v = (-1 : ℂ) ^ n.toNat • onePoint N v := by
  -- Quasi-primary ⟹ either n ≥ 0, or n < 0 forcing v = 0 (positivity 𝒱ₙ = ⊥).
  rcases le_or_gt 0 n with hn0 | hn0
  · funext e
    set α : ℂ := e + W.centralCharge / 24 with hα
    haveI := N.finrank α
    haveI : FiniteDimensional ℂ ((contragredient N hJac).weight α) :=
      (contragredient N hJac).finrank α
    show LinearMap.trace ℂ (RestrictedDual.weight N α)
        (weightBlock (contragredient N hJac) (oMod (contragredient N hJac) v) α) = _
    rw [trace_weightBlock_contra N hJac hvn hv α]
    show ((-1 : ℂ) ^ n) * LinearMap.trace ℂ _ (weightBlock N (oMod N v) α)
        = ((-1 : ℂ) ^ n.toNat) • LinearMap.trace ℂ _ (weightBlock N (oMod N v) α)
    rw [smul_eq_mul]
    congr 1
    rw [← zpow_natCast (-1 : ℂ) n.toNat, Int.toNat_of_nonneg hn0]
  · -- n < 0 ⟹ 𝒱ₙ = ⊥ ⟹ v = 0 ⟹ both one-point functions vanish.
    have hbot := W.positivity n hn0
    rw [hbot, Submodule.mem_bot] at hvn
    subst hvn
    have hz1 : onePoint N (0 : 𝒱) = 0 := by
      have := onePoint_smul N 0 (0 : 𝒱); simpa using this
    have hz2 : onePoint (contragredient N hJac) (0 : 𝒱) = 0 := by
      have := onePoint_smul (contragredient N hJac) 0 (0 : 𝒱); simpa using this
    rw [hz1, hz2, smul_zero]

end VOA
