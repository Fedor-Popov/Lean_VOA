/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.M8h0Gap
import VOA.Moonshine.Generation
import VOA.Core.InvariantFormRadical

/-!
# The invariant form of `V♮`: full FHL invariance and nondegeneracy

On `Vnat = V_Λ^+ × TP` (`TP = (V_Λ^T)^+`) take the block-diagonal form

  `B♮((u,t),(u',t')) = B_V(u,u') + TPForm(t,t')`        (`natForm`),

`B_V = leechBV` the canonical invariant form of `V_Λ^+` (`= plusForm`, symmetric) and `TPForm` the
explicit form on `TP`.  For `vnatVOA htt` (block vertex map `[[Y, W̄], [W, Y^T]]`):

* `natForm_fhl` — full FHL invariance (`IsFullyInvariant` mode form)
  `B♮(x₍ₙ₎a, b) = (−1)^{wt} ∑_j (1/j!) B♮(a, (L₁ʲx)₍₂wt−n−2−j₎ b)` for **every** homogeneous
  `x ∈ V♮_wt`.  Its four blocks:
  - `Y`-block: `canonicalInvariantForm_isFullyInvariant` for `V_Λ^+`;
  - `Y^T`-block: `TPForm_fhlInv` (unconditional);
  - `W̄`-block: the defining DGM (4.3) adjunction `leechWbar_adj'`, verbatim;
  - `W`-block: `pieceD`, the adjunction read backwards: symmetry of both forms, the adjunction
    at `L₁ʲt ∈ TP_{w−j}`, and the cancellation `double_sum_cancel`
    `∑_{j,i} (−1)^j/(j! i!) f(i+j) = f(0)` (involutivity of `x ↦ e^{zL₁}(−z⁻²)^{L₀}x`, `z ↦ z⁻¹`;
    from `alt_antidiag`, `(1−1)^k = δ_{k0}`).  The signs `(−1)^w (−1)^{w−j} = (−1)^j` come from
    `negOne_zpow_mul_sub`.
* `natInvForm htt : InvariantForm (vnatVOA htt)` (Virasoro adjointness from the `ω` slice,
  `L₁ω = 0`), `natInvForm_isFullyInvariant`, `natInvForm_normalized` (`(𝟙|𝟙) = 1`).
* `natInvForm_leftRadical` — trivial radical, from `leechBVForm_leftRadical` and
  `TPForm_eq_zero_of_forall` (global nondegeneracy of `TPForm` from `TPForm_nondegenerate` on
  weight spaces + `form_proj_left`).

Consumed by `SimpleVnat` (simplicity via Li's theorem).

## Status
`sorry`-free, no new axioms; the only hypothesis is `htt` (that of `vnatVOA`).
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.SimpleNat

open scoped BigOperators

/-- `∑_{i+j=k} (−1)^i/(i! j!) = δ_{k,0}`. -/
theorem alt_antidiag (k : ℕ) :
    ∑ p ∈ Finset.antidiagonal k,
      (-1 : ℂ) ^ p.1 * (((p.1.factorial : ℂ))⁻¹ * ((p.2.factorial : ℂ))⁻¹)
      = if k = 0 then 1 else 0 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have h : ∀ i ∈ Finset.range (k + 1),
      (-1 : ℂ) ^ (i, k - i).1 * ((((i, k - i).1.factorial : ℂ))⁻¹ * (((i, k - i).2.factorial : ℂ))⁻¹)
        = ((k.factorial : ℂ))⁻¹ * ((-1 : ℂ) ^ i * (1 : ℂ) ^ (k - i) * (k.choose i : ℂ)) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hc : (k.choose i : ℂ) * i.factorial * (k - i).factorial = k.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hik
    have h1 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
    have h2 : ((k - i).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k - i)
    have h3 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have h4 : (k.choose i : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hik).ne'
    simp only [one_pow, mul_one]
    rw [← hc]
    field_simp
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, ← add_pow]
  split_ifs with hk
  · subst hk; simp
  · simp [zero_pow hk]

/-- The double-sum cancellation `∑_{j,i<R} (−1)^j/(j! i!) f(i+j) = f 0` for `f` vanishing past
`R` — the involutivity of `e^{zL₁}(−z⁻²)^{L₀}`, `z ↦ z⁻¹`. -/
theorem double_sum_cancel (R : ℕ) (f : ℕ → ℂ) (hf : ∀ k, R ≤ k → f k = 0) :
    ∑ j ∈ Finset.range R, ∑ i ∈ Finset.range R,
      (-1 : ℂ) ^ j * (((j.factorial : ℂ))⁻¹ * ((i.factorial : ℂ))⁻¹) * f (j + i) = f 0 := by
  rw [← Finset.sum_product' (f := fun j i =>
    (-1 : ℂ) ^ j * (((j.factorial : ℂ))⁻¹ * ((i.factorial : ℂ))⁻¹) * f (j + i))]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 + p.2)
    (t := Finset.range (2 * R)) (fun p hp => by
      simp only [Finset.mem_product, Finset.mem_range] at hp ⊢; omega)]
  have hfib : ∀ k ∈ Finset.range (2 * R),
      ∑ p ∈ (Finset.range R ×ˢ Finset.range R).filter (fun p : ℕ × ℕ => p.1 + p.2 = k),
        (-1 : ℂ) ^ p.1 * (((p.1.factorial : ℂ))⁻¹ * ((p.2.factorial : ℂ))⁻¹) * f (p.1 + p.2)
        = if k = 0 then f 0 else 0 := by
    intro k _
    by_cases hkR : R ≤ k
    · rw [Finset.sum_eq_zero]
      · split_ifs with h0
        · subst h0; exact (hf 0 hkR).symm
        · rfl
      · intro p hp
        rw [Finset.mem_filter] at hp
        rw [hp.2, hf k hkR, mul_zero]
    · have hset : (Finset.range R ×ˢ Finset.range R).filter (fun p : ℕ × ℕ => p.1 + p.2 = k)
          = Finset.antidiagonal k := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
          Finset.mem_antidiagonal]
        omega
      rw [hset]
      have : ∀ p ∈ Finset.antidiagonal k,
          (-1 : ℂ) ^ p.1 * (((p.1.factorial : ℂ))⁻¹ * ((p.2.factorial : ℂ))⁻¹) * f (p.1 + p.2)
            = (-1 : ℂ) ^ p.1 * (((p.1.factorial : ℂ))⁻¹ * ((p.2.factorial : ℂ))⁻¹) * f k := by
        intro p hp
        rw [Finset.mem_antidiagonal.mp hp]
      rw [Finset.sum_congr rfl this, ← Finset.sum_mul, alt_antidiag]
      split_ifs with h0
      · subst h0; rw [one_mul]
      · rw [zero_mul]
  rw [Finset.sum_congr rfl hfib, Finset.sum_ite_eq' (Finset.range (2 * R)) 0]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt, Nat.le_zero, mul_eq_zero] at h
    exact (hf 0 (by omega)).symm


/-! ## The block form `B♮ = B_V ⊕ TPForm` -/

open Module (End)
open VertexOperatorAlgebra VnatBlock VnatAxioms SkewIntertwiner SkewAdjoint InvForm

/-- `B_V` (the canonical invariant form of `V_Λ^+`) is symmetric. -/
theorem leechBV_symm (x y : SkewVP) : leechBV x y = leechBV y x := by
  rw [leechBV_eq_plusForm, plusForm_apply, plusForm_apply, Nondeg.latForm_symm]

/-- **The block-diagonal form on `V♮ = V_Λ^+ × TP`**: `B♮((u,t),(u',t')) = B_V(u,u') + TPForm(t,t')`. -/
noncomputable def natForm : LinearMap.BilinForm ℂ Vnat :=
  leechBV.compl₁₂ (LinearMap.fst ℂ SkewVP TP) (LinearMap.fst ℂ SkewVP TP)
    + TPForm.compl₁₂ (LinearMap.snd ℂ SkewVP TP) (LinearMap.snd ℂ SkewVP TP)

@[simp] theorem natForm_apply (x y : Vnat) : natForm x y = leechBV x.1 y.1 + TPForm x.2 y.2 := rfl

theorem natForm_symm (x y : Vnat) : natForm x y = natForm y x := by
  rw [natForm_apply, natForm_apply, leechBV_symm, TPForm_symm]

/-- `TP` has no negative weights. -/
theorem TP_eq_zero_of_neg {w : ℤ} (hw : w < 0) {t : TP} (ht : t ∈ plusModule.weight (w : ℂ)) :
    t = 0 := by
  have h : ((0 : SkewVP), t) ∈ gradingNat w := mem_gradingNat.2 ⟨Submodule.zero_mem _, ht⟩
  rw [gradingNat_neg hw, Submodule.mem_bot] at h
  exact congrArg Prod.snd h

theorem Lp1_pow_mem_int {wt : ℤ} {t : TP} (ht : t ∈ plusModule.weight (wt : ℂ)) (j : ℕ) :
    (Lp1 plusModule ^ j) t ∈ plusModule.weight (((wt - j : ℤ)) : ℂ) := by
  have h := Lp1_pow_mem plusModule ht j
  push_cast; exact h

theorem Lp1_pow_vanish {wt : ℤ} {t : TP} (ht : t ∈ plusModule.weight (wt : ℂ)) (j : ℕ)
    (hj : wt.toNat + 1 ≤ j) : (Lp1 plusModule ^ j) t = 0 :=
  TP_eq_zero_of_neg (by omega) (Lp1_pow_mem_int ht j)

theorem negOne_zpow_mul_sub (wt : ℤ) (j : ℕ) :
    (-1 : ℂ) ^ wt * (-1 : ℂ) ^ (wt - (j : ℤ)) = (-1 : ℂ) ^ j := by
  rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    show wt + (wt - (j : ℤ)) = (j : ℤ) + 2 * (wt - j) by ring,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul]
  norm_num

/-- **The `W`-block of FHL invariance** (the adjunction of `W̄` read backwards):
`TPForm(W(t)₍ₙ₎a, b) = (−1)^w ∑_j (1/j!) B_V(a, W̄(L₁ʲt)₍₂w−n−2−j₎ b)`.  Proof: symmetry of both
forms, the defining adjunction `leechWbar_adj'` once more, and `double_sum_cancel`. -/
theorem pieceD {wt : ℤ} {t : TP} (ht : t ∈ plusModule.weight (wt : ℂ)) (n : ℤ) (a : SkewVP)
    (b : TP) :
    TPForm (mode (leechWsk t) n a) b = (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1),
      ((j.factorial : ℂ)⁻¹) • leechBV a (leechWbarMode (2 * wt - n - 2 - j)
        ((Lp1 plusModule ^ j) t) b) := by
  set R := wt.toNat + 1 with hR
  set f : ℕ → ℂ := fun k => TPForm b (mode (leechWsk ((Lp1 plusModule ^ k) t)) (n - k) a) with hf
  have hfv : ∀ k, R ≤ k → f k = 0 := by
    intro k hk
    simp only [hf]
    rw [Lp1_pow_vanish ht k hk]
    have h0 : leechWsk (0 : TP) = 0 := by
      have := map_zero leechWskLin
      exact this
    rw [h0]
    simp [mode_apply]
  have hterm : ∀ j ∈ Finset.range R,
      ((j.factorial : ℂ)⁻¹) • leechBV a (leechWbarMode (2 * wt - n - 2 - j) ((Lp1 plusModule ^ j) t) b)
        = ((j.factorial : ℂ)⁻¹) • ((-1 : ℂ) ^ (wt - (j : ℤ)) • ∑ i ∈ Finset.range R,
            ((i.factorial : ℂ)⁻¹) • f (j + i)) := by
    intro j _
    congr 1
    rw [leechBV_symm, leechWbar_adj' (2 * wt - n - 2 - j) (Lp1_pow_mem_int ht j) R
      (fun i hi => by
        rw [← Module.End.mul_apply, ← pow_add]
        exact Lp1_pow_vanish ht _ (by omega)) b a]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hf]
    rw [← Module.End.mul_apply, ← pow_add, add_comm i j]
    rw [show 2 * (wt - (j : ℤ)) - (2 * wt - n - 2 - j) - 2 - i = n - ((j + i : ℕ) : ℤ) by push_cast; ring]
  rw [Finset.sum_congr rfl hterm]
  have hds := double_sum_cancel R f hfv
  have hlhs : TPForm (mode (leechWsk t) n a) b = f 0 := by
    simp only [hf, pow_zero, Module.End.one_apply, Nat.cast_zero, sub_zero]
    exact TPForm_symm _ _
  rw [hlhs, ← hds, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [smul_eq_mul]
  linear_combination (-(((j.factorial : ℂ))⁻¹ * ((i.factorial : ℂ))⁻¹ * f (j + i))) *
    negOne_zpow_mul_sub wt j


/-! ## FHL invariance of `B♮` under every field of `V♮` -/

section Vnat

variable (htt : ∀ t t' : TP, Local (YnatT leechWbar t) (YnatT leechWbar t'))

theorem vnat_smul (x : Vnat) (n : ℤ) (y : Vnat) : (vnatVOA htt).smul x n y = mode (YN x) n y := rfl

/-- `L₁` on `V♮` is block-diagonal. -/
theorem vnat_L1 (x : Vnat) : (vnatVOA htt).L 1 x = (leechVOAPlus.L 1 x.1, Lp1 plusModule x.2) := by
  change mode (YN omegaNat) (1 + 1) x = _
  rw [show (1 : ℤ) + 1 = 2 by norm_num, mode_YN_omega, blockOp_apply]
  simp only [LinearMap.zero_apply, add_zero, zero_add]
  rfl

theorem vnat_L1_pow (j : ℕ) (x : Vnat) :
    (((vnatVOA htt).L 1) ^ j) x = ((leechVOAPlus.L 1 ^ j) x.1, (Lp1 plusModule ^ j) x.2) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, vnat_L1, ih, pow_succ, pow_succ, Module.End.mul_apply,
      Module.End.mul_apply]

/-- **Full FHL invariance of `B♮` for every homogeneous state of `V♮`** (Gannon 5.1.11a in the
mode form `IsFullyInvariant`): the `V_Λ^+`-diagonal blocks by the canonical form and
`TPForm_fhlInv`, the `W̄` block by the defining adjunction `leechWbar_adj'`, the `W` block by
`pieceD`. -/
theorem natForm_fhl (wt : ℤ) (x : Vnat) (hx : x ∈ gradingNat wt) (n : ℤ) (a b : Vnat) :
    natForm ((vnatVOA htt).smul x n a) b
      = (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
          natForm a ((vnatVOA htt).smul ((((vnatVOA htt).L 1) ^ j) x) (2 * wt - n - 2 - (j : ℤ)) b) := by
  rw [mem_gradingNat] at hx
  have hR : ∀ j : ℕ, wt.toNat + 1 ≤ j → (Lp1 plusModule ^ j) x.2 = 0 :=
    fun j hj => Lp1_pow_vanish hx.2 j hj
  have hA : leechBV (leechVOAPlus.smul x.1 n a.1) b.1
      = (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
          leechBV a.1 (mode (leechVOAPlus.Y ((leechVOAPlus.L 1 ^ j) x.1)) (2 * wt - n - 2 - (j : ℤ)) b.1) :=
    canonicalInvariantForm_isFullyInvariant leechVOAPlus_vacuum_ne_zero
      leechVOAPlus_L1_one wt x.1 hx.1 n a.1 b.1
  have hB := TPForm_fhlInv hx.1 n a.2 b.2
  have hC := leechWbar_adj' n hx.2 (wt.toNat + 1) hR a.2 b.1
  have hD := pieceD hx.2 n a.1 b.2
  simp only [vnat_smul, vnat_L1_pow, mode_YN, natForm_apply, map_add, LinearMap.add_apply,
    mode_leechWbar]
  change leechBV (leechVOAPlus.smul x.1 n a.1) b.1 + _ + _ = _
  rw [hA, hC, hD, hB]
  simp only [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [smul_add]
  abel

theorem vnat_L1_omega : (vnatVOA htt).L 1 omegaNat = 0 := by
  rw [vnat_L1]
  change (leechVOAPlus.L 1 leechVOAPlus.conformalVector, Lp1 plusModule 0) = 0
  rw [leechVOAPlus_L1_omega, map_zero]
  rfl

/-- **`B♮` as an invariant form of `V♮`** (Virasoro adjointness = the `u = ω` slice of
`natForm_fhl`, using `L₁ω = 0`). -/
theorem vnat_L (n : ℤ) (a : Vnat) : (vnatVOA htt).L n a = mode (YN omegaNat) (n + 1) a := rfl

theorem natForm_virasoro_adj (n : ℤ) (a b : Vnat) :
    natForm ((vnatVOA htt).L n a) b = natForm a ((vnatVOA htt).L (-n) b) := by
  have h := natForm_fhl htt 2 omegaNat omegaNat_mem (n + 1) a b
  rw [Finset.sum_eq_single 0] at h
  · rw [vnat_L, vnat_L, ← vnat_smul htt, h, pow_zero, Module.End.one_apply, Nat.factorial_zero,
      Nat.cast_one, inv_one, one_smul, Nat.cast_zero, sub_zero, vnat_smul,
      show (2 : ℤ) * 2 - (n + 1) - 2 = -n + 1 by ring, show ((-1 : ℂ) ^ (2 : ℤ)) = 1 by norm_num,
      one_smul]
  · intro j _ hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    rw [pow_succ, Module.End.mul_apply, vnat_L1_omega, map_zero, vnat_smul, map_zero, mode_zero,
      LinearMap.zero_apply, map_zero, smul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (by norm_num)) h

/-- **`B♮` as an invariant form of `V♮`** (Virasoro adjointness = the `u = ω` slice of
`natForm_fhl`, using `L₁ω = 0`). -/
noncomputable def natInvForm : InvariantForm (vnatVOA htt) where
  form := natForm
  virasoro_adj := natForm_virasoro_adj htt

theorem natInvForm_form : (natInvForm htt).form = natForm := rfl

/-- **`B♮` is fully (FHL) invariant** on `V♮`. -/
theorem natInvForm_isFullyInvariant : (natInvForm htt).IsFullyInvariant :=
  fun wt x hx n a b => natForm_fhl htt wt x hx n a b

/-- `B♮(𝟙, 𝟙) = 1`. -/
theorem natInvForm_normalized : (natInvForm htt).Normalized := by
  change natForm vacNat vacNat = 1
  rw [natForm_apply]
  change leechBV leechVOAPlus.vacuum leechVOAPlus.vacuum + TPForm 0 0 = 1
  rw [leechBV_normalized, map_zero, add_zero]

end Vnat

/-! ## Nondegeneracy -/

/-- `TPForm` has trivial (left) radical on all of `TP` (from weight-space nondegeneracy
`TPForm_nondegenerate` and weight orthogonality). -/
theorem TPForm_eq_zero_of_forall (t : TP) (h : ∀ y : TP, TPForm t y = 0) : t = 0 := by
  have hproj : ∀ α : ℂ, internalProjTo plusModule.isInternal α t = 0 := by
    intro α
    by_contra hne
    have hne' : ((internalProjTo plusModule.isInternal α t : plusModule.weight α) : TP) ≠ 0 :=
      fun h0 => hne (Subtype.ext h0)
    obtain ⟨y, hy, hxy⟩ := TPForm_nondegenerate α _ (internalProjTo plusModule.isInternal α t).2 hne'
    exact hxy (by rw [form_proj_left TPForm_weightOrth α t hy, h y])
  letI := DirectSum.IsInternal.chooseDecomposition plusModule.weight plusModule.isInternal
  have hdec : DirectSum.decompose plusModule.weight t = 0 := by
    refine DFinsupp.ext fun α => ?_
    exact hproj α
  have := congrArg (DirectSum.decompose plusModule.weight).symm hdec
  rwa [Equiv.symm_apply_apply, DirectSum.decompose_symm_zero] at this

section Vnat

variable (htt : ∀ t t' : TP, Local (YnatT leechWbar t) (YnatT leechWbar t'))

/-- **`B♮` is nondegenerate on `V♮`**: its (left) radical is `0`. -/
theorem natInvForm_leftRadical : InvariantForm.leftRadical (natInvForm htt) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [InvariantForm.mem_leftRadical] at hx
  rw [Submodule.mem_bot]
  have h1 : x.1 = 0 := by
    have hr : x.1 ∈ InvariantForm.leftRadical leechBVForm := by
      rw [InvariantForm.mem_leftRadical]
      refine LinearMap.ext fun y => ?_
      have := DFunLike.congr_fun hx ((y, 0) : Vnat)
      change natForm x (y, 0) = 0 at this
      rw [natForm_apply] at this
      change leechBV x.1 y + TPForm x.2 0 = 0 at this
      rw [map_zero, add_zero] at this
      exact this
    rw [leechBVForm_leftRadical, Submodule.mem_bot] at hr
    exact hr
  have h2 : x.2 = 0 := by
    refine TPForm_eq_zero_of_forall _ fun y => ?_
    have := DFunLike.congr_fun hx ((0, y) : Vnat)
    change natForm x (0, y) = 0 at this
    rw [natForm_apply] at this
    change leechBV x.1 0 + TPForm x.2 y = 0 at this
    rw [map_zero, zero_add] at this
    exact this
  exact Prod.ext h1 h2

end Vnat

end VOA.Moonshine.SimpleNat
