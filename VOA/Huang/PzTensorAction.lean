/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.PzTensorBilin
import VOA.Core.InvariantFormFHL2

/-!
# The Huang–Lepowsky `P(1)`-action on functions of homogeneous pairs (definitions)

For homogeneous `u ∈ V_β` and `m ∈ ℤ` the **`P(1)`-action** on a function `G` of homogeneous
pairs `(w₁, w₂) ∈ P₁ × P₂` is the transpose of the coproduct `Δ(a_p) = Σ_r C(p,r) a_r ⊗ 1 + 1 ⊗ a_p`
(the `w₂`-centred coproduct, `w₁` at distance `1`) applied to the **opposite (contragredient)
mode** `(u°)_m = (−1)^β Σ_j (1/j!) (L₁ʲu)_{2β−m−2−j}`:

`τ(u,m) G (w₁, w₂) = (−1)^β Σ_j (1/j!) [ G(w₁, (L₁ʲu)_{k_j} w₂)`
`  + Σ_r C(k_j, r) G((L₁ʲu)_r w₁, w₂) ]`,
`k_j = 2β − m − 2 − j`.

This is `Y'_{P(1)}(u, x)` of Huang–Lepowsky–Zhang IV (5.87) (with `z = 1`) written in modes: the
`δ`-function `z^{−1}δ((x^{−1} − x₀)/z)` produces exactly the binomial coefficients `C(k_j, r)`.  The
twist is the library's contragredient twist (`Modules.ContragredientTransport.dualAdj_clean`).

## Main definitions and results
* `lowBound`, `mode_eq_zero_of_lowBound` — a truncation bound depending only on the weight label.
* `copT` (the transposed coproduct), `tauHom` (the twisted action), `tauLin` (as a linear map).
* `copT_mem_bilin`, `tauHom_mem_bilin` — bilinear functions are preserved.
* `tauHom_add_u`, `tauHom_smul_u` — linearity in `u` on bilinear functions.
* `tauHom_vacuum` — `τ(𝟙, m) = δ_{m,−1}` on bilinear functions.
* `tauHom_conformal_one` — `τ(ω, 1) = L'(0)` (the transpose operator `L0T`) on bilinear
  functions.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.PzTensorAction

open VOA VOA.Huang.MatrixCoeff VOA.Huang.FusionTop VOA.Huang.AssocTarget
open VOA.Huang.LogRemovalSemisimple VOA.Huang.AssocTauStable VOA.Huang.PzTensorBilin
open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## A truncation bound depending only on the weight label -/

/-- `r ≥ lowBound h α γ` forces `α + γ − r − 1` strictly below `h` (real parts). -/
noncomputable def lowBound (h α : ℂ) (γ : ℤ) : ℕ := (⌈(α - h).re + γ⌉).toNat

theorem mode_eq_zero_of_lowBound {M : Type u} [AddCommGroup M] [Module ℂ M]
    {A : OrdVModule W M} {h : ℂ} (hl : IsLowestWeight A h) {α : ℂ} {w : M}
    (hw : w ∈ A.weight α) {γ : ℤ} {a : 𝒱} (ha : a ∈ W.grading γ) {r : ℕ}
    (hr : lowBound h α γ ≤ r) : mode (A.YM a) (r : ℤ) w = 0 := by
  have hmem := VOA.mode_mem_weight A ha hw (r : ℤ)
  have hbot : A.weight (α + (γ : ℂ) - ((r : ℤ) : ℂ) - 1) = ⊥ := by
    by_contra hne
    obtain ⟨n, hn⟩ := hl _ hne
    have hre := congrArg Complex.re hn
    simp only [Complex.add_re, Complex.sub_re, Complex.intCast_re, Complex.one_re,
      Complex.natCast_re] at hre
    have hc : (⌈(α - h).re + γ⌉ : ℤ) ≤ (r : ℤ) := by
      unfold lowBound at hr; omega
    have hc' : (α - h).re + γ ≤ (r : ℝ) := by
      have := Int.le_ceil ((α - h).re + γ)
      have h2 : ((⌈(α - h).re + γ⌉ : ℤ) : ℝ) ≤ ((r : ℤ) : ℝ) := by exact_mod_cast hc
      push_cast at h2
      linarith
    simp only [Complex.sub_re] at hc'
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast at hre
    linarith
  rw [hbot] at hmem
  exact (Submodule.mem_bot ℂ).mp hmem

/-! ## The transposed coproduct and the twisted action -/

section Action

variable {P₁ P₂ : LWModule W}

/-- **The transposed coproduct** `Δᵀ(a_p) G (w₁, w₂) = G(w₁, a_p w₂) + Σ_r C(p,r) G(a_r w₁, w₂)`,
with the sum truncated at `lowBound` (past which `a_r w₁ = 0`). -/
noncomputable def copT {γ : ℤ} {a : 𝒱} (ha : a ∈ W.grading γ) (p : ℤ)
    (G : HomPair P₁ P₂ → ℂ) (x : HomPair P₁ P₂) : ℂ :=
  G (pairRight x ha p)
    + ∑ r ∈ Finset.range (lowBound P₁.h x.α₁ γ), cbz p r * G (pairLeft x ha r)

/-- The twisted index `k_j = 2β − m − 2 − j`. -/
def twIdx (β m : ℤ) (j : ℕ) : ℤ := 2 * β - m - 2 - (j : ℤ)

/-- **The `P(1)`-action** `τ(u, m)` on functions of homogeneous pairs (homogeneous `u ∈ V_β`). -/
noncomputable def tauHom {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) (m : ℤ)
    (G : HomPair P₁ P₂ → ℂ) : HomPair P₁ P₂ → ℂ :=
  fun x => (-1 : ℂ) ^ β * ∑ j ∈ Finset.range (β.toNat + 1),
    ((j.factorial : ℂ)⁻¹) * copT (VOA.VertexOperatorAlgebra.L_one_pow_mem W hu j) (twIdx β m j) G x

theorem copT_add {γ : ℤ} {a : 𝒱} (ha : a ∈ W.grading γ) (p : ℤ) (G G' : HomPair P₁ P₂ → ℂ)
    (x : HomPair P₁ P₂) : copT ha p (G + G') x = copT ha p G x + copT ha p G' x := by
  simp only [copT, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem copT_smul {γ : ℤ} {a : 𝒱} (ha : a ∈ W.grading γ) (p : ℤ) (c : ℂ)
    (G : HomPair P₁ P₂ → ℂ) (x : HomPair P₁ P₂) : copT ha p (c • G) x = c * copT ha p G x := by
  simp only [copT, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

/-- `τ(u, m)` as a linear map on all functions. -/
noncomputable def tauLin {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) (m : ℤ) :
    (HomPair P₁ P₂ → ℂ) →ₗ[ℂ] (HomPair P₁ P₂ → ℂ) where
  toFun := tauHom hu m
  map_add' G G' := by
    funext x
    simp only [tauHom, Pi.add_apply, copT_add, mul_add, Finset.sum_add_distrib]
  map_smul' c G := by
    funext x
    simp only [tauHom, Pi.smul_apply, smul_eq_mul, copT_smul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

@[simp] theorem tauLin_apply {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) (m : ℤ)
    (G : HomPair P₁ P₂ → ℂ) : tauLin hu m G = tauHom hu m G := rfl

/-! ### Bilinear functions are preserved -/

theorem copT_mem_bilin {G : HomPair P₁ P₂ → ℂ} (hG : G ∈ bilin P₁ P₂) {γ : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading γ) (p : ℤ) : copT ha p G ∈ bilin P₁ P₂ := by
  have hB : IsBilin G := hG
  refine isBilin_of ?_ ?_ ?_ ?_
  · intro x y z h1 h2 h3 h4 h5 h6 h7
    have ey : lowBound P₁.h y.α₁ γ = lowBound P₁.h x.α₁ γ := by rw [h1]
    have ez : lowBound P₁.h z.α₁ γ = lowBound P₁.h x.α₁ γ := by rw [h2]
    simp only [copT, ey, ez]
    rw [hB.addL (pairRight x ha p) (pairRight y ha p) (pairRight z ha p)
      (by simp [pairRight, h1]) (by simp [pairRight, h2]) (by simp [pairRight, h3])
      (by simp [pairRight, h4]) (by simp [pairRight, h5]) (by simp [pairRight, h6])
      (by simp [pairRight, h7]), add_add_add_comm, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← mul_add, hB.addL (pairLeft x ha r) (pairLeft y ha r) (pairLeft z ha r)
      (by simp [pairLeft, h1]) (by simp [pairLeft, h2]) (by simp [pairLeft, h3])
      (by simp [pairLeft, h4]) (by simp [pairLeft, h5]) (by simp [pairLeft, h6])
      (by simp [pairLeft, h7, map_add])]
  · intro x y c h1 h3 h5 h7
    have ey : lowBound P₁.h y.α₁ γ = lowBound P₁.h x.α₁ γ := by rw [h1]
    simp only [copT, ey]
    rw [hB.smulL (pairRight x ha p) (pairRight y ha p) c
      (by simp [pairRight, h1]) (by simp [pairRight, h3]) (by simp [pairRight, h5])
      (by simp [pairRight, h7]), mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hB.smulL (pairLeft x ha r) (pairLeft y ha r) c
      (by simp [pairLeft, h1]) (by simp [pairLeft, h3]) (by simp [pairLeft, h5])
      (by simp [pairLeft, h7, map_smul])]
    ring
  · intro x y z h1 h2 h3 h4 h5 h6 h7
    have ey : lowBound P₁.h y.α₁ γ = lowBound P₁.h x.α₁ γ := by rw [h1]
    have ez : lowBound P₁.h z.α₁ γ = lowBound P₁.h x.α₁ γ := by rw [h2]
    simp only [copT, ey, ez]
    rw [hB.addR (pairRight x ha p) (pairRight y ha p) (pairRight z ha p)
      (by simp [pairRight, h1]) (by simp [pairRight, h2]) (by simp [pairRight, h3])
      (by simp [pairRight, h4]) (by simp [pairRight, h5]) (by simp [pairRight, h6])
      (by simp [pairRight, h7, map_add]), add_add_add_comm, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← mul_add, hB.addR (pairLeft x ha r) (pairLeft y ha r) (pairLeft z ha r)
      (by simp [pairLeft, h1]) (by simp [pairLeft, h2]) (by simp [pairLeft, h3])
      (by simp [pairLeft, h4]) (by simp [pairLeft, h5]) (by simp [pairLeft, h6])
      (by simp [pairLeft, h7])]
  · intro x y c h1 h3 h5 h7
    have ey : lowBound P₁.h y.α₁ γ = lowBound P₁.h x.α₁ γ := by rw [h1]
    simp only [copT, ey]
    rw [hB.smulR (pairRight x ha p) (pairRight y ha p) c
      (by simp [pairRight, h1]) (by simp [pairRight, h3]) (by simp [pairRight, h5])
      (by simp [pairRight, h7, map_smul]), mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hB.smulR (pairLeft x ha r) (pairLeft y ha r) c
      (by simp [pairLeft, h1]) (by simp [pairLeft, h3]) (by simp [pairLeft, h5])
      (by simp [pairLeft, h7])]
    ring

theorem tauHom_mem_bilin {G : HomPair P₁ P₂ → ℂ} (hG : G ∈ bilin P₁ P₂) {β : ℤ} {u : 𝒱}
    (hu : u ∈ W.grading β) (m : ℤ) : tauHom hu m G ∈ bilin P₁ P₂ := by
  have key : tauHom hu m G = (-1 : ℂ) ^ β • ∑ j ∈ Finset.range (β.toNat + 1),
      ((j.factorial : ℂ)⁻¹) •
        copT (VOA.VertexOperatorAlgebra.L_one_pow_mem W hu j) (twIdx β m j) G := by
    funext x
    simp only [tauHom, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [key]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
  exact copT_mem_bilin hG _ _

/-! ### Linearity in the state -/

theorem copT_add_u {G : HomPair P₁ P₂ → ℂ} (hG : G ∈ bilin P₁ P₂) {γ : ℤ} {a a' b : 𝒱}
    (ha : a ∈ W.grading γ) (ha' : a' ∈ W.grading γ) (hb : b ∈ W.grading γ) (hab : b = a + a')
    (p : ℤ) (x : HomPair P₁ P₂) : copT hb p G x = copT ha p G x + copT ha' p G x := by
  have hB : IsBilin G := hG
  subst hab
  simp only [copT]
  rw [hB.addR (pairRight x hb p) (pairRight x ha p) (pairRight x ha' p) rfl rfl rfl rfl rfl rfl
    (by simp only [pairRight, map_add, mode_add, LinearMap.add_apply]), add_add_add_comm,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← mul_add, hB.addL (pairLeft x hb r) (pairLeft x ha r) (pairLeft x ha' r) rfl rfl rfl rfl
    rfl rfl (by simp only [pairLeft, map_add, mode_add, LinearMap.add_apply])]

theorem copT_smul_u {G : HomPair P₁ P₂ → ℂ} (hG : G ∈ bilin P₁ P₂) {γ : ℤ} {a b : 𝒱} (c : ℂ)
    (ha : a ∈ W.grading γ) (hb : b ∈ W.grading γ) (hab : b = c • a)
    (p : ℤ) (x : HomPair P₁ P₂) : copT hb p G x = c * copT ha p G x := by
  have hB : IsBilin G := hG
  subst hab
  simp only [copT]
  rw [hB.smulR (pairRight x hb p) (pairRight x ha p) c rfl rfl rfl
    (by simp only [pairRight, map_smul, mode_smul, LinearMap.smul_apply]), mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hB.smulL (pairLeft x hb r) (pairLeft x ha r) c rfl rfl rfl
    (by simp only [pairLeft, map_smul, mode_smul, LinearMap.smul_apply])]
  ring

theorem tauHom_add_u {G : HomPair P₁ P₂ → ℂ} (hG : G ∈ bilin P₁ P₂) {β : ℤ} {u u' : 𝒱}
    (hu : u ∈ W.grading β) (hu' : u' ∈ W.grading β) (m : ℤ) :
    tauHom (add_mem hu hu') m G = tauHom hu m G + tauHom hu' m G := by
  funext x
  simp only [tauHom, Pi.add_apply, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [copT_add_u hG (VOA.VertexOperatorAlgebra.L_one_pow_mem W hu j)
    (VOA.VertexOperatorAlgebra.L_one_pow_mem W hu' j) _ (map_add _ u u')]

theorem tauHom_smul_u {G : HomPair P₁ P₂ → ℂ} (hG : G ∈ bilin P₁ P₂) {β : ℤ} {u : 𝒱} (c : ℂ)
    (hu : u ∈ W.grading β) (m : ℤ) :
    tauHom (Submodule.smul_mem _ c hu) m G = c • tauHom hu m G := by
  funext x
  simp only [tauHom, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [copT_smul_u hG c (VOA.VertexOperatorAlgebra.L_one_pow_mem W hu j) _ (map_smul _ c u)]
  ring

/-- `tauHom` depends on the membership proof only through the state. -/
theorem tauHom_congr {β : ℤ} {u u' : 𝒱} (hu : u ∈ W.grading β) (hu' : u' ∈ W.grading β)
    (h : u = u') (m : ℤ) (G : HomPair P₁ P₂ → ℂ) : tauHom hu m G = tauHom hu' m G := by
  subst h; rfl

/-! ### The vacuum and the conformal vector -/

theorem copT_zero_state {G : HomPair P₁ P₂ → ℂ} (hG : G ∈ bilin P₁ P₂) {γ : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading γ) (h0 : a = 0) (p : ℤ) (x : HomPair P₁ P₂) : copT ha p G x = 0 := by
  have hB : IsBilin G := hG
  subst h0
  simp only [copT]
  rw [hB.zero_right _ (by simp [pairRight]), zero_add]
  exact Finset.sum_eq_zero fun r _ => by rw [hB.zero_left _ (by simp [pairLeft]), mul_zero]

/-- **Vacuum**: `τ(𝟙, m) G = δ_{m,−1} G` on bilinear functions. -/
theorem tauHom_vacuum {G : HomPair P₁ P₂ → ℂ} (hG : G ∈ bilin P₁ P₂) (m : ℤ) :
    tauHom (W.vacuum_mem_grading_zero) m G = if m = -1 then G else 0 := by
  have hB : IsBilin G := hG
  funext x
  simp only [tauHom, show ((0 : ℤ).toNat + 1) = 1 from rfl, Finset.sum_range_one, zpow_zero,
    Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, copT, twIdx]
  have hv : ((W.L 1) ^ (0 : ℕ)) W.vacuum = W.vacuum := by simp
  have hL : ∀ r : ℕ, (pairLeft x (VOA.VertexOperatorAlgebra.L_one_pow_mem W
      W.vacuum_mem_grading_zero 0) (r : ℤ)).w₁ = 0 := by
    intro r
    simp only [pairLeft, hv]
    have := P₁.isMod.toWeakModule.act_vacuum (r : ℤ) x.w₁
    rw [WeakModule.act_def, if_neg (by omega)] at this
    exact this
  rw [Finset.sum_eq_zero fun r _ => by rw [hB.zero_left _ (hL r), mul_zero], add_zero]
  have hR := P₂.isMod.toWeakModule.act_vacuum (2 * 0 - m - 2 - ((0 : ℕ) : ℤ)) x.w₂
  rw [WeakModule.act_def] at hR
  split_ifs with hm
  · subst hm
    rw [if_pos (by norm_num)] at hR
    exact G_congr G rfl rfl (by simp only [pairRight, hv]; exact hR)
      (by simp only [pairRight]; push_cast; ring)
  · rw [if_neg (by omega)] at hR
    rw [Pi.zero_apply]
    exact hB.zero_right _ (by simp only [pairRight, hv]; exact hR)

theorem L_one_pow_conformal (j : ℕ) (hj : 1 ≤ j) :
    ((W.L 1) ^ j) W.conformalVector = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [pow_succ, Module.End.mul_apply, VOA.L1_conformal_zero, map_zero]

/-- **`τ(ω, 1) = L'(0)`** on bilinear functions: the transpose of `(L₋₁ + L₀) ⊗ 1 + 1 ⊗ L₀`. -/
theorem tauHom_conformal_one {G : HomPair P₁ P₂ → ℂ} (hG : G ∈ bilin P₁ P₂) :
    tauHom (W.conformalVector_mem_grading_two) 1 G = L0T P₁ P₂ G := by
  have hB : IsBilin G := hG
  funext x
  rw [L0T_apply]
  simp only [tauHom, show ((2 : ℤ).toNat + 1) = 3 from rfl]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    copT_zero_state hG _ (L_one_pow_conformal 1 le_rfl),
    copT_zero_state hG _ (L_one_pow_conformal 2 (by norm_num))]
  simp only [mul_zero, add_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul]
  rw [show ((-1 : ℂ) ^ (2 : ℤ)) = 1 by norm_num, one_mul]
  have hω : ((W.L 1) ^ (0 : ℕ)) W.conformalVector = W.conformalVector := by simp
  simp only [copT, twIdx]
  -- the right term: `L₀ w₂ = α₂ w₂`
  rw [hB.smulR (pairRight x _ _) x x.α₂ rfl rfl (by simp only [pairRight]; push_cast; ring)
    (by simp only [pairRight, hω]
        have := P₂.isMod.L0_weight x.α₂ x.w₂ x.h₂
        convert this using 3)]
  -- the left terms
  set L := lowBound P₁.h x.α₁ (2 - ((0 : ℕ) : ℤ)) with hLdef
  have hzero : ∀ r : ℕ, L ≤ r → G (pairLeft x (VOA.VertexOperatorAlgebra.L_one_pow_mem W
      W.conformalVector_mem_grading_two 0) (r : ℤ)) = 0 := fun r hr =>
    hB.zero_left _ (mode_eq_zero_of_lowBound P₁.isLow x.h₁
      (VOA.VertexOperatorAlgebra.L_one_pow_mem W W.conformalVector_mem_grading_two 0) hr)
  have hc2 : ∀ r : ℕ, 2 ≤ r → cbz (2 * 2 - 1 - 2 - ((0 : ℕ) : ℤ)) (r : ℤ) = 0 := by
    intro r hr
    rw [cbz_apply_nonneg _ (Int.natCast_nonneg r), Int.toNat_natCast,
      show (2 * 2 - 1 - 2 - ((0 : ℕ) : ℤ)) = ((1 : ℕ) : ℤ) by norm_num]
    exact VOA.VertexOperatorAlgebra.gBinom_natCast_eq_zero (by omega)
  have hsum : ∑ r ∈ Finset.range L, cbz (2 * 2 - 1 - 2 - ((0 : ℕ) : ℤ)) (r : ℤ)
      * G (pairLeft x (VOA.VertexOperatorAlgebra.L_one_pow_mem W
        W.conformalVector_mem_grading_two 0) (r : ℤ))
      = ∑ r ∈ Finset.range 2, cbz (2 * 2 - 1 - 2 - ((0 : ℕ) : ℤ)) (r : ℤ)
      * G (pairLeft x (VOA.VertexOperatorAlgebra.L_one_pow_mem W
        W.conformalVector_mem_grading_two 0) (r : ℤ)) := by
    rw [Finset.sum_subset (Finset.range_subset_range.2 (le_max_left L 2)) (fun r _ hr => by
        rw [Finset.mem_range, not_lt] at hr; rw [hzero r hr, mul_zero]),
      Finset.sum_subset (Finset.range_subset_range.2 (le_max_right L 2)) (fun r _ hr => by
        rw [Finset.mem_range, not_lt] at hr; rw [hc2 r hr, zero_mul])]
  rw [hsum, Finset.sum_range_succ, Finset.sum_range_one]
  have c0 : cbz (2 * 2 - 1 - 2 - ((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ) = 1 := by
    rw [cbz_apply_nonneg _ (by norm_num)]; simp
  have c1 : cbz (2 * 2 - 1 - 2 - ((0 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = 1 := by
    rw [cbz_apply_nonneg _ (by norm_num)]; simp [gBinom]
  rw [c0, c1, one_mul, one_mul]
  have e0 : G (pairLeft x (VOA.VertexOperatorAlgebra.L_one_pow_mem W
      W.conformalVector_mem_grading_two 0) ((0 : ℕ) : ℤ)) = G x.lm1 :=
    G_congr G (by simp only [pairLeft, HomPair.lm1, hω]; rfl)
      (by simp only [pairLeft, HomPair.lm1]; push_cast; ring) rfl rfl
  have e1 : G (pairLeft x (VOA.VertexOperatorAlgebra.L_one_pow_mem W
      W.conformalVector_mem_grading_two 0) ((1 : ℕ) : ℤ)) = x.α₁ * G x :=
    hB.smulL _ x x.α₁ (by simp only [pairLeft]; push_cast; ring) rfl rfl
      (by simp only [pairLeft, hω]; push_cast; exact P₁.isMod.L0_weight x.α₁ x.w₁ x.h₁)
  rw [e0, e1]
  ring

end Action

end VOA.Huang.PzTensorAction
