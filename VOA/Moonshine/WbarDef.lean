/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.WbarRiesz
import VOA.Moonshine.SkewIntertwiner
import VOA.Moonshine.InvFormClosure

/-!
# The adjoint `W̄` of the skew intertwiner  (Moonshine step M8c, `W̄` part 2)

For a VOA `𝒱`, an ordinary module `N : OrdVModule W M`, a bilinear form `BV` on `𝒱` and a
bilinear form `BM` on `M` with orthogonal weight spaces, the **adjoint** of the skew
intertwiner `W(t,z)φ = e^{zL₋₁}Y_M(φ,−z)t` (`SkewIntertwiner.Wsk`) is defined by
(DGM CMP 1996, eq. (4.3); FHL §5.5)

  `BV(W̄(t,z)a, φ) = BM(a, W(e^{zL₁}(−z⁻²)^{L₀} t, z⁻¹) φ)`,

i.e. in modes, for `t ∈ M_w` (`w ∈ ℤ`),

  `BV(W̄(t)₍ₙ₎a, φ) = (−1)^w ∑_{j≥0} (1/j!) BM(a, W(L₁ʲt)₍₂w−n−2−j₎ φ)`.

The right-hand side is `BM(a, W†(t)₍ₙ₎φ)` with the **dagger** `W†(t)₍ₙ₎ := Wdag n t`; the vector
`W̄(t)₍ₙ₎a` is its graded Riesz representative (`Moonshine.WbarRiesz`).

## Main definitions and results

* `Lp1 N = L₁` on `M`; `lowB N` — an integer below every nonzero weight.
* `Wdag n : M →ₗ 𝒱 →ₗ M` — the dagger, linear in `t` (non-integral weight components are sent to
  `0`); `Wdag_int_eq_sum` — its value on `t ∈ M_w` for any sufficient `j`-bound.
* `Phi BM n t a := BM a ∘ Wdag n t`, with finite graded support (`gsupp_Phi_finite`).
* `WbarMode BV BM hO n t : M →ₗ 𝒱`, `WbarBil`, `Wbar t : FormalDist (M →ₗ 𝒱)`
  (`Wbar t k = W̄(t)₍₋ₖ₋₁₎`).
* `form_WbarMode` — the defining adjunction `BV(W̄(t)₍ₙ₎a, φ) = BM(a, W†(t)₍ₙ₎φ)`;
  `form_WbarMode_int` — the explicit FHL/DGM sum for `t ∈ M_w`.
* `WbarMode_mem` — `t ∈ M_w`, `a ∈ M_b` ⟹ `W̄(t)₍ₙ₎a ∈ 𝒱_{b+w−n−1}` (well-definedness: `W̄`
  maps each `M_b` into a single weight space of `𝒱`).
* `WbarMode_trunc` / `Wbar_trunc` — lower truncation: `W̄(t)₍ₙ₎a = 0` for `n ≫ 0`.

## Status
All declarations proved; no `sorry`/axioms.  The definitions need only `hO : WeightOrth N BM`.
The adjunction needs in addition `GradedOrth W BV` and `GradedNondeg W BV` (displayed).
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.SkewAdjoint

open Module (End Dual)
open VertexOperatorAlgebra SkewIntertwiner InvForm
open scoped BigOperators
open Classical

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## `L₁`, `L₋₁` on `M` and the lower weight bound -/

/-- `L₁ = ω₍₂₎` on the module. -/
noncomputable def Lp1 (N : OrdVModule W M) : End ℂ M := mode (N.YM W.conformalVector) 2

theorem Lm1_mem (N : OrdVModule W M) {α : ℂ} {x : M} (hx : x ∈ N.weight α) :
    Lm1 N.toWeakModule x ∈ N.weight (α + 1) := by
  have h := mode_mem_weight N W.conformal_mem hx 0
  convert h using 2; push_cast; ring

theorem Lm1_pow_mem (N : OrdVModule W M) {α : ℂ} {x : M} (hx : x ∈ N.weight α) (i : ℕ) :
    (Lm1 N.toWeakModule ^ i) x ∈ N.weight (α + i) := by
  induction i with
  | zero => simpa using hx
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply]
    convert Lm1_mem N ih using 2; push_cast; ring

theorem Lp1_mem (N : OrdVModule W M) {α : ℂ} {x : M} (hx : x ∈ N.weight α) :
    Lp1 N x ∈ N.weight (α - 1) := by
  have h := mode_mem_weight N W.conformal_mem hx 2
  convert h using 2; push_cast; ring

theorem Lp1_pow_mem (N : OrdVModule W M) {α : ℂ} {x : M} (hx : x ∈ N.weight α) (j : ℕ) :
    (Lp1 N ^ j) x ∈ N.weight (α - j) := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    convert Lp1_mem N ih using 2; push_cast; ring

/-- An integer strictly below which every weight space vanishes. -/
noncomputable def lowB (N : OrdVModule W M) : ℤ := ⌈N.boundedBelow.choose⌉

theorem weight_eq_bot_of_lt (N : OrdVModule W M) {k : ℤ} (hk : k < lowB N) :
    N.weight (k : ℂ) = ⊥ := by
  by_contra h
  have h1 := N.boundedBelow.choose_spec _ h
  have h2 : (k : ℝ) < N.boundedBelow.choose := Int.lt_ceil.mp hk
  simp only [Complex.intCast_re] at h1
  linarith

theorem eq_zero_of_lt (N : OrdVModule W M) {k : ℤ} (hk : k < lowB N) {x : M}
    (hx : x ∈ N.weight (k : ℂ)) : x = 0 := by
  rw [weight_eq_bot_of_lt N hk] at hx; exact (Submodule.mem_bot ℂ).mp hx

theorem Lp1_pow_eq_zero (N : OrdVModule W M) {w : ℤ} {x : M} (hx : x ∈ N.weight (w : ℂ)) {j : ℕ}
    (hj : w - j < lowB N) : (Lp1 N ^ j) x = 0 :=
  eq_zero_of_lt N hj (by have := Lp1_pow_mem N hx j; push_cast; exact this)

/-! ## Weights of the skew modes -/

theorem wMode_mem (N : OrdVModule W M) {σ : ℂ} {s : M} (hs : s ∈ N.weight σ) {k : ℤ} {φ : 𝒱}
    (hφ : φ ∈ W.grading k) (m : ℤ) :
    wMode N.toWeakModule s m φ ∈ N.weight (σ + k - m - 1) := by
  obtain ⟨K, hK⟩ := exists_bound N.toWeakModule s m φ
  rw [wMode_eq_sum N.toWeakModule K hK]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have h1 := mode_mem_weight N hφ hs (m + i)
  convert Lm1_pow_mem N h1 i using 2; push_cast; ring

/-! ## The dagger `W†(t)₍ₙ₎ = (−1)^w ∑ⱼ (1/j!) W(L₁ʲt)₍₂w−n−2−j₎` -/

/-- The `j`-range used in the definition: `L₁ʲ t = 0` for `j ≥ dagBound N w` when `t ∈ M_w`. -/
noncomputable def dagBound (N : OrdVModule W M) (w : ℤ) : ℕ := (w - lowB N).toNat + 1

theorem Lp1_pow_eq_zero_of_dagBound (N : OrdVModule W M) {w : ℤ} {x : M}
    (hx : x ∈ N.weight (w : ℂ)) {j : ℕ} (hj : dagBound N w ≤ j) : (Lp1 N ^ j) x = 0 :=
  Lp1_pow_eq_zero N hx (by unfold dagBound at hj; omega)

/-- The dagger at a fixed integral weight `w`, as a bilinear map. -/
noncomputable def dagHom (N : OrdVModule W M) (n w : ℤ) : M →ₗ[ℂ] 𝒱 →ₗ[ℂ] M :=
  (-1 : ℂ) ^ w • ∑ j ∈ Finset.range (dagBound N w),
    ((j.factorial : ℂ)⁻¹) • (wBil N.toWeakModule (2 * w - n - 2 - j)) ∘ₗ (Lp1 N ^ j)

theorem dagHom_apply (N : OrdVModule W M) (n w : ℤ) (t : M) (φ : 𝒱) :
    dagHom N n w t φ = (-1 : ℂ) ^ w • ∑ j ∈ Finset.range (dagBound N w),
      ((j.factorial : ℂ)⁻¹) • wMode N.toWeakModule ((Lp1 N ^ j) t) (2 * w - n - 2 - j) φ := by
  simp [dagHom, LinearMap.sum_apply, Finset.smul_sum]

/-- The dagger family on the weight spaces (zero on non-integral weights). -/
noncomputable def dagFam (N : OrdVModule W M) (n : ℤ) (α : ℂ) :
    N.weight α →ₗ[ℂ] 𝒱 →ₗ[ℂ] M :=
  if h : ∃ w : ℤ, (w : ℂ) = α then (dagHom N n (Classical.choose h)) ∘ₗ (N.weight α).subtype
  else 0

/-- **The dagger** `W†(·)₍ₙ₎ : M →ₗ 𝒱 →ₗ M`. -/
noncomputable def Wdag (N : OrdVModule W M) (n : ℤ) : M →ₗ[ℂ] 𝒱 →ₗ[ℂ] M :=
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
  (DFinsupp.lsum ℂ (dagFam N n)).comp (DirectSum.decomposeLinearEquiv N.weight).toLinearMap

theorem Wdag_homog (N : OrdVModule W M) (n : ℤ) {α : ℂ} {t : M} (ht : t ∈ N.weight α) :
    Wdag N n t = dagFam N n α ⟨t, ht⟩ := by
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.isInternal
  change (DFinsupp.lsum ℂ (dagFam N n)) (DirectSum.decompose N.weight t) = _
  rw [DirectSum.decompose_of_mem N.weight ht]
  exact DFinsupp.lsum_single ℂ (dagFam N n) α ⟨t, ht⟩

theorem Wdag_int (N : OrdVModule W M) (n : ℤ) {w : ℤ} {t : M} (ht : t ∈ N.weight (w : ℂ)) :
    Wdag N n t = dagHom N n w t := by
  rw [Wdag_homog N n ht, dagFam]
  have h : ∃ w' : ℤ, (w' : ℂ) = (w : ℂ) := ⟨w, rfl⟩
  rw [dif_pos h]
  have hc : Classical.choose h = w := by exact_mod_cast Classical.choose_spec h
  rw [LinearMap.comp_apply, Submodule.subtype_apply, hc]

theorem Wdag_nonint (N : OrdVModule W M) (n : ℤ) {α : ℂ} {t : M} (ht : t ∈ N.weight α)
    (hα : ∀ w : ℤ, (w : ℂ) ≠ α) : Wdag N n t = 0 := by
  rw [Wdag_homog N n ht, dagFam, dif_neg (fun ⟨w, hw⟩ => hα w hw)]; rfl

/-- The dagger on `t ∈ M_w`, with any `j`-bound `R` past the vanishing of `L₁ʲt`. -/
theorem Wdag_int_eq_sum (N : OrdVModule W M) (n : ℤ) {w : ℤ} {t : M}
    (ht : t ∈ N.weight (w : ℂ)) (R : ℕ) (hR : ∀ j : ℕ, R ≤ j → (Lp1 N ^ j) t = 0) (φ : 𝒱) :
    Wdag N n t φ = (-1 : ℂ) ^ w • ∑ j ∈ Finset.range R,
      ((j.factorial : ℂ)⁻¹) • wMode N.toWeakModule ((Lp1 N ^ j) t) (2 * w - n - 2 - j) φ := by
  rw [Wdag_int N n ht, dagHom_apply]
  congr 1
  have key : ∀ R1 R2 : ℕ, R1 ≤ R2 → (∀ j : ℕ, R1 ≤ j → (Lp1 N ^ j) t = 0) →
      ∑ j ∈ Finset.range R1, ((j.factorial : ℂ)⁻¹) •
          wMode N.toWeakModule ((Lp1 N ^ j) t) (2 * w - n - 2 - j) φ
        = ∑ j ∈ Finset.range R2, ((j.factorial : ℂ)⁻¹) •
          wMode N.toWeakModule ((Lp1 N ^ j) t) (2 * w - n - 2 - j) φ := by
    intro R1 R2 h12 hR'
    refine Finset.sum_subset (Finset.range_subset_range.2 h12) fun j _ hj => ?_
    rw [Finset.mem_range, not_lt] at hj
    rw [hR' j hj, wMode_zero_right, smul_zero]
  rw [key _ _ (le_max_right R (dagBound N w))
      (fun j hj => Lp1_pow_eq_zero_of_dagBound N ht hj),
    key _ _ (le_max_left R (dagBound N w)) hR]

theorem Wdag_mem (N : OrdVModule W M) (n : ℤ) {w : ℤ} {t : M} (ht : t ∈ N.weight (w : ℂ))
    {k : ℤ} {φ : 𝒱} (hφ : φ ∈ W.grading k) :
    Wdag N n t φ ∈ N.weight (((k - w + n + 1 : ℤ)) : ℂ) := by
  rw [Wdag_int N n ht, dagHom_apply]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
  have h := wMode_mem N (Lp1_pow_mem N ht j) hφ (2 * w - n - 2 - j)
  convert h using 2; push_cast; ring

/-! ## The functional `φ ↦ BM(a, W†(t)₍ₙ₎φ)` -/

/-- The functional `φ ↦ BM(a, W†(t)₍ₙ₎φ)`. -/
noncomputable def Phi (N : OrdVModule W M) (BM : LinearMap.BilinForm ℂ M) (n : ℤ) (t a : M) :
    𝒱 →ₗ[ℂ] ℂ :=
  (BM a) ∘ₗ (Wdag N n t)

theorem Phi_add_left (N : OrdVModule W M) (BM : LinearMap.BilinForm ℂ M) (n : ℤ) (t t' a : M) :
    Phi N BM n (t + t') a = Phi N BM n t a + Phi N BM n t' a := by
  simp [Phi, LinearMap.comp_add]

theorem Phi_smul_left (N : OrdVModule W M) (BM : LinearMap.BilinForm ℂ M) (n : ℤ) (c : ℂ)
    (t a : M) : Phi N BM n (c • t) a = c • Phi N BM n t a := by
  simp [Phi, LinearMap.comp_smul]

theorem Phi_add_right (N : OrdVModule W M) (BM : LinearMap.BilinForm ℂ M) (n : ℤ) (t a a' : M) :
    Phi N BM n t (a + a') = Phi N BM n t a + Phi N BM n t a' := by
  simp [Phi, LinearMap.add_comp]

theorem Phi_smul_right (N : OrdVModule W M) (BM : LinearMap.BilinForm ℂ M) (n : ℤ) (c : ℂ)
    (t a : M) : Phi N BM n t (c • a) = c • Phi N BM n t a := by
  simp [Phi, LinearMap.smul_comp]

theorem Phi_zero_left (N : OrdVModule W M) (BM : LinearMap.BilinForm ℂ M) (n : ℤ) (a : M) :
    Phi N BM n 0 a = 0 := by simp [Phi]

theorem Phi_zero_right (N : OrdVModule W M) (BM : LinearMap.BilinForm ℂ M) (n : ℤ) (t : M) :
    Phi N BM n t 0 = 0 := by simp [Phi]

/-- For `t ∈ M_w`, `a ∈ M_β`, the functional vanishes on `𝒱ₖ` unless `k − w + n + 1 = β`. -/
theorem restr_Phi_eq_zero (N : OrdVModule W M) {BM : LinearMap.BilinForm ℂ M}
    (hO : WeightOrth N BM) (n : ℤ) {w : ℤ} {t : M} (ht : t ∈ N.weight (w : ℂ)) {β : ℂ} {a : M}
    (ha : a ∈ N.weight β) {k : ℤ} (hk : (((k - w + n + 1 : ℤ)) : ℂ) ≠ β) :
    restr W k (Phi N BM n t a) = 0 := by
  refine LinearMap.ext fun ⟨φ, hφ⟩ => ?_
  change BM a (Wdag N n t φ) = 0
  exact hO β _ (Ne.symm hk) a ha _ (Wdag_mem N n ht hφ)

theorem gsupp_Phi_finite (N : OrdVModule W M) {BM : LinearMap.BilinForm ℂ M}
    (hO : WeightOrth N BM) (n : ℤ) (t a : M) : (gsupp W (Phi N BM n t a)).Finite := by
  have ht : t ∈ ⨆ α, N.weight α := by rw [N.isInternal.submodule_iSup_eq_top]; trivial
  have ha : a ∈ ⨆ α, N.weight α := by rw [N.isInternal.submodule_iSup_eq_top]; trivial
  induction ht using Submodule.iSup_induction' with
  | mem α t ht =>
    induction ha using Submodule.iSup_induction' with
    | mem β a ha =>
      by_cases hα : ∃ w : ℤ, (w : ℂ) = α
      · obtain ⟨w, rfl⟩ := hα
        refine Set.Subsingleton.finite ?_
        · intro k hk k' hk'
          by_contra hne
          by_cases h1 : (((k - w + n + 1 : ℤ)) : ℂ) = β
          · apply hk'
            refine restr_Phi_eq_zero N hO n ht ha ?_
            rw [← h1]; intro h; apply hne
            have := Int.cast_injective (α := ℂ) h; omega
          · exact hk (restr_Phi_eq_zero N hO n ht ha h1)
      · have h0 : Phi N BM n t a = 0 := by
          rw [Phi, Wdag_nonint N n ht (fun w hw => hα ⟨w, hw⟩), LinearMap.comp_zero]
        rw [h0, gsupp_zero]; exact Set.finite_empty
    | zero => rw [Phi_zero_right, gsupp_zero]; exact Set.finite_empty
    | add a a' _ _ h1 h2 => rw [Phi_add_right]; exact (h1.union h2).subset (gsupp_add _ _)
  | zero => rw [Phi_zero_left, gsupp_zero]; exact Set.finite_empty
  | add t t' _ _ h1 h2 => rw [Phi_add_left]; exact (h1.union h2).subset (gsupp_add _ _)

/-! ## `W̄` -/

variable (BV : LinearMap.BilinForm ℂ 𝒱) (N : OrdVModule W M) (BM : LinearMap.BilinForm ℂ M)
  (hO : WeightOrth N BM)

/-- **The modes of `W̄`**: `W̄(t)₍ₙ₎ : M →ₗ 𝒱`, `W̄(t)₍ₙ₎a = riesz (φ ↦ BM(a, W†(t)₍ₙ₎φ))`. -/
noncomputable def WbarMode (n : ℤ) (t : M) : M →ₗ[ℂ] 𝒱 where
  toFun a := riesz W BV (Phi N BM n t a)
  map_add' a a' := by
    rw [Phi_add_right, riesz_add BV (gsupp_Phi_finite N hO n t a) (gsupp_Phi_finite N hO n t a')]
  map_smul' c a := by
    rw [Phi_smul_right, riesz_smul BV c (gsupp_Phi_finite N hO n t a)]; rfl

theorem WbarMode_apply (n : ℤ) (t a : M) :
    WbarMode BV N BM hO n t a = riesz W BV (Phi N BM n t a) := rfl

theorem WbarMode_add (n : ℤ) (t t' : M) :
    WbarMode BV N BM hO n (t + t') = WbarMode BV N BM hO n t + WbarMode BV N BM hO n t' := by
  refine LinearMap.ext fun a => ?_
  rw [LinearMap.add_apply, WbarMode_apply, WbarMode_apply, WbarMode_apply, Phi_add_left,
    riesz_add BV (gsupp_Phi_finite N hO n t a) (gsupp_Phi_finite N hO n t' a)]

theorem WbarMode_smul (n : ℤ) (c : ℂ) (t : M) :
    WbarMode BV N BM hO n (c • t) = c • WbarMode BV N BM hO n t := by
  refine LinearMap.ext fun a => ?_
  rw [LinearMap.smul_apply, WbarMode_apply, WbarMode_apply, Phi_smul_left,
    riesz_smul BV c (gsupp_Phi_finite N hO n t a)]

theorem WbarMode_zero (n : ℤ) : WbarMode BV N BM hO n 0 = 0 := by
  have h := WbarMode_smul BV N BM hO n 0 0
  rwa [zero_smul, zero_smul] at h

/-- `W̄(·)₍ₙ₎(·)` as a bilinear map `M →ₗ M →ₗ 𝒱`. -/
noncomputable def WbarBil (n : ℤ) : M →ₗ[ℂ] M →ₗ[ℂ] 𝒱 where
  toFun t := WbarMode BV N BM hO n t
  map_add' := WbarMode_add BV N BM hO n
  map_smul' c t := WbarMode_smul BV N BM hO n c t

/-- **The field `W̄(t,z) = ∑ₙ W̄(t)₍ₙ₎ z^{−n−1}`** (coefficient of `zᵏ` is `W̄(t)₍₋ₖ₋₁₎`). -/
noncomputable def Wbar (t : M) : FormalDist (M →ₗ[ℂ] 𝒱) :=
  fun k => WbarMode BV N BM hO (-k - 1) t

theorem mode_Wbar (t : M) (n : ℤ) : mode (Wbar BV N BM hO t) n = WbarMode BV N BM hO n t := by
  rw [mode_apply, Wbar, show -(-n - 1) - 1 = n by ring]

/-! ## The defining adjunction -/

variable {BV N BM hO}

/-- **The defining adjunction** `BV(W̄(t)₍ₙ₎a, φ) = BM(a, W†(t)₍ₙ₎φ)`. -/
theorem form_WbarMode (hVo : GradedOrth W BV) (hVnd : GradedNondeg W BV) (n : ℤ) (t a : M)
    (φ : 𝒱) : BV (WbarMode BV N BM hO n t a) φ = BM a (Wdag N n t φ) :=
  riesz_spec hVo hVnd (gsupp_Phi_finite N hO n t a) φ

/-- **The DGM (4.3) adjunction in modes**, for `t ∈ M_w` and any sufficient `j`-bound `R`:
`BV(W̄(t)₍ₙ₎a, φ) = (−1)^w ∑_{j<R} (1/j!) BM(a, W(L₁ʲt)₍₂w−n−2−j₎ φ)`. -/
theorem form_WbarMode_int (hVo : GradedOrth W BV) (hVnd : GradedNondeg W BV) (n : ℤ) {w : ℤ}
    {t : M} (ht : t ∈ N.weight (w : ℂ)) (R : ℕ) (hR : ∀ j : ℕ, R ≤ j → (Lp1 N ^ j) t = 0)
    (a : M) (φ : 𝒱) :
    BV (WbarMode BV N BM hO n t a) φ = (-1 : ℂ) ^ w • ∑ j ∈ Finset.range R,
      ((j.factorial : ℂ)⁻¹) • BM a (wMode N.toWeakModule ((Lp1 N ^ j) t) (2 * w - n - 2 - j) φ) := by
  rw [form_WbarMode hVo hVnd, Wdag_int_eq_sum N n ht R hR, map_smul, map_sum]
  simp only [map_smul]

/-- Uniqueness: `W̄` is determined by the adjunction. -/
theorem WbarMode_eq_of_form (hVo : GradedOrth W BV) (hVnd : GradedNondeg W BV) {n : ℤ} {t a : M}
    {x : 𝒱} (h : ∀ φ, BV x φ = BM a (Wdag N n t φ)) : WbarMode BV N BM hO n t a = x :=
  eq_of_form hVo hVnd fun φ => by rw [form_WbarMode hVo hVnd, h]

/-! ## Grading and truncation (no hypothesis on `BV`) -/

/-- **`W̄` is graded**: `t ∈ M_w`, `a ∈ M_b` ⟹ `W̄(t)₍ₙ₎a ∈ 𝒱_{b+w−n−1}`. -/
theorem WbarMode_mem (n : ℤ) {w b : ℤ} {t a : M} (ht : t ∈ N.weight (w : ℂ))
    (ha : a ∈ N.weight (b : ℂ)) : WbarMode BV N BM hO n t a ∈ W.grading (b + w - n - 1) := by
  refine riesz_mem BV fun k hk => restr_Phi_eq_zero N hO n ht ha ?_
  intro h; apply hk
  have := Int.cast_injective (α := ℂ) h; omega

theorem WbarMode_nonint_left (n : ℤ) {α : ℂ} {t : M} (ht : t ∈ N.weight α)
    (hα : ∀ w : ℤ, (w : ℂ) ≠ α) : WbarMode BV N BM hO n t = 0 := by
  refine LinearMap.ext fun a => ?_
  rw [WbarMode_apply, Phi, Wdag_nonint N n ht hα, LinearMap.comp_zero, riesz_zero,
    LinearMap.zero_apply]

theorem WbarMode_nonint_right (n : ℤ) {w : ℤ} {t : M} (ht : t ∈ N.weight (w : ℂ)) {β : ℂ}
    {a : M} (ha : a ∈ N.weight β) (hβ : ∀ b : ℤ, (b : ℂ) ≠ β) : WbarMode BV N BM hO n t a = 0 := by
  rw [WbarMode_apply, riesz]
  refine finsum_eq_zero_of_forall_eq_zero fun k => ?_
  rw [restr_Phi_eq_zero N hO n ht ha (hβ _), map_zero]

/-- **Lower truncation of `W̄`**: for all `t, a`, `W̄(t)₍ₙ₎a = 0` for `n ≫ 0`. -/
theorem WbarMode_trunc (t a : M) : ∃ N₀ : ℤ, ∀ n : ℤ, N₀ ≤ n → WbarMode BV N BM hO n t a = 0 := by
  have ht : t ∈ ⨆ α, N.weight α := by rw [N.isInternal.submodule_iSup_eq_top]; trivial
  have ha : a ∈ ⨆ α, N.weight α := by rw [N.isInternal.submodule_iSup_eq_top]; trivial
  induction ht using Submodule.iSup_induction' with
  | mem α t ht =>
    induction ha using Submodule.iSup_induction' with
    | mem β a ha =>
      by_cases hα : ∃ w : ℤ, (w : ℂ) = α
      · obtain ⟨w, rfl⟩ := hα
        by_cases hβ : ∃ b : ℤ, (b : ℂ) = β
        · obtain ⟨b, rfl⟩ := hβ
          refine ⟨b + w, fun n hn => ?_⟩
          have h := WbarMode_mem (BV := BV) (hO := hO) n ht ha
          rw [W.positivity _ (by omega)] at h
          exact (Submodule.mem_bot ℂ).mp h
        · exact ⟨0, fun n _ => WbarMode_nonint_right n ht ha (fun b hb => hβ ⟨b, hb⟩)⟩
      · exact ⟨0, fun n _ => by
          rw [WbarMode_nonint_left n ht (fun w hw => hα ⟨w, hw⟩), LinearMap.zero_apply]⟩
    | zero => exact ⟨0, fun n _ => map_zero _⟩
    | add a a' _ _ h1 h2 =>
      obtain ⟨N1, hN1⟩ := h1
      obtain ⟨N2, hN2⟩ := h2
      exact ⟨max N1 N2, fun n hn => by
        rw [map_add, hN1 n (le_of_max_le_left hn), hN2 n (le_of_max_le_right hn), add_zero]⟩
  | zero => exact ⟨0, fun n _ => by rw [WbarMode_zero, LinearMap.zero_apply]⟩
  | add t t' _ _ h1 h2 =>
    obtain ⟨N1, hN1⟩ := h1
    obtain ⟨N2, hN2⟩ := h2
    exact ⟨max N1 N2, fun n hn => by
      rw [WbarMode_add, LinearMap.add_apply, hN1 n (le_of_max_le_left hn),
        hN2 n (le_of_max_le_right hn), add_zero]⟩

/-- **`W̄(t,z)` is lower-truncated** in the field sense: `W̄(t,z)a ∈ 𝒱((z))`. -/
theorem Wbar_trunc (t : M) : ∀ a : M, ∃ B : ℤ, ∀ k : ℤ, k < B → Wbar BV N BM hO t k a = 0 := by
  intro a
  obtain ⟨N₀, hN₀⟩ := WbarMode_trunc (BV := BV) (hO := hO) t a
  exact ⟨-N₀, fun k hk => hN₀ (-k - 1) (by omega)⟩

end VOA.Moonshine.SkewAdjoint
