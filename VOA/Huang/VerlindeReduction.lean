/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.IModDataReduced

/-!
# `HuangSInput` from the Verlinde formula

`Huang/IModDataReduced.lean` leaves `HuangSInput`: for Zhu's `ρ(S)` on a complete irredundant
family, `S₀₀ ≠ 0`, `S₀ₐ = Sₐ₀`, `d_a ≥ 1` and Gannon's bound `‖S_ab‖ ≤ S₀₀ d_a d_b`. Two of its four
clauses (`d_a ≥ 1`, Gannon's bound) are *consequences* of the Verlinde formula plus the positivity
of the vacuum column already proved in `Huang/CardyPositivity.lean`; this file proves that.

## The narrower input

`VerlindeInput` asks only for Huang's Verlinde theorem in its eigenvalue form:

* `Sₒₓ ≠ 0` for every label `x` (part of Huang's Verlinde theorem, 2008);
* the vacuum row equals the vacuum column, `S₀ₐ = Sₐ₀` (a consequence of Huang's symmetry of `S`);
* there are natural numbers `N_ab^c` (the fusion rules) with
  `S_ax S_bx = S₀ₓ Σ_c N_ab^c S_cx` (i.e. `N_a S = S diag(S_ax/S₀ₓ)`, Verlinde).

It is a *weakening* of Huang's theorem (only vacuum-row symmetry, and `N` existentially
quantified), hence true for every nice VOA.

## What is proved (pure algebra, `Fintype ι`)

* `le_of_fusion` — `d_a ≥ 1`. From `s_a s_b = s₀ Σ_c N_ab^c s_c` with all `s > 0`: choose `b`
  minimising `s_b`; the sum is positive, so some `N_ab^c ≥ 1`, whence `s_a s_b ≥ s₀ s_c ≥ s₀ s_b`.
* `norm_mul_le_of_fusion` — Gannon's bound `‖S_ax‖ ≤ s_a s_x / s₀`, by the Perron–Frobenius
  comparison `|eigenvalue| ≤ d_a` (maximise `‖S_cx‖ / s_c` over `c`).
* `huangSInput_of_verlinde` : `DLMRationalityInput → VerlindeInput → HuangSInput`.
-/

open Complex Finset

noncomputable section

namespace VOA.Huang.VerlindeReduction

open VOA VOA.Classification.COne VOA.Huang.ZhuModData VOA.Huang.CardyPositivity
  VOA.Huang.IModDataReduced

universe u w

/-! ## §1 Pure algebra: Frobenius–Perron consequences of the Verlinde relation -/

section Algebra

variable {ι : Type w} [Fintype ι]

/-- **`d_a ≥ 1` from integral fusion.** If `s > 0` on a finite nonempty set and
`s_a s_b = s₀ Σ_c N_ab^c s_c` with `N` natural-number valued, then `s₀ ≤ s_a`. -/
theorem le_of_fusion (s : ι → ℝ) (hs : ∀ c, 0 < s c) (v0 : ι) (N : ι → ι → ι → ℕ)
    (hfus : ∀ a b, s a * s b = s v0 * ∑ c, (N a b c : ℝ) * s c) (a : ι) : s v0 ≤ s a := by
  haveI : Nonempty ι := ⟨a⟩
  obtain ⟨b, -, hb⟩ := Finset.exists_min_image Finset.univ s Finset.univ_nonempty
  have hpos : 0 < ∑ c, (N a b c : ℝ) * s c := by
    have h := hfus a b
    have h1 : 0 < s a * s b := mul_pos (hs a) (hs b)
    rw [h] at h1
    exact pos_of_mul_pos_right h1 (hs v0).le
  obtain ⟨c, -, hc⟩ : ∃ c ∈ Finset.univ, 0 < (N a b c : ℝ) * s c := by
    by_contra hne
    push Not at hne
    exact absurd (Finset.sum_nonpos hne) (not_le.2 hpos)
  have hN : (1 : ℝ) ≤ N a b c := by
    have : 0 < (N a b c : ℝ) := pos_of_mul_pos_left hc (hs c).le
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by exact_mod_cast this.ne')
  have hge : s b ≤ ∑ c, (N a b c : ℝ) * s c := by
    calc s b ≤ s c := hb c (Finset.mem_univ _)
      _ = 1 * s c := (one_mul _).symm
      _ ≤ (N a b c : ℝ) * s c := mul_le_mul_of_nonneg_right hN (hs c).le
      _ ≤ ∑ c, (N a b c : ℝ) * s c :=
          Finset.single_le_sum (f := fun c => (N a b c : ℝ) * s c)
            (fun c _ => mul_nonneg (Nat.cast_nonneg _) (hs c).le) (Finset.mem_univ c)
  have key : s v0 * s b ≤ s a * s b := by
    rw [hfus a b]; exact mul_le_mul_of_nonneg_left hge (hs v0).le
  exact le_of_mul_le_mul_right key (hs b)

/-- **Gannon's bound from integral fusion** (Perron–Frobenius comparison). Let `s > 0` with
`S c v0 = s c`, `S v0 x = s x` (the vacuum row and column), and the Verlinde relation
`S_ax S_bx = S₀ₓ Σ_c N_ab^c S_cx`. Then `‖S_ax‖ * s v0 ≤ s a * s x`. -/
theorem norm_mul_le_of_fusion (S : ι → ι → ℂ) (s : ι → ℝ) (hs : ∀ c, 0 < s c) (v0 : ι)
    (hcol : ∀ c, S c v0 = s c) (hrow : ∀ x, S v0 x = s x) (N : ι → ι → ι → ℕ)
    (hfus : ∀ a b x, S a x * S b x = S v0 x * ∑ c, (N a b c : ℂ) * S c x) (a x : ι) :
    ‖S a x‖ * s v0 ≤ s a * s x := by
  haveI : Nonempty ι := ⟨a⟩
  -- real fusion on the vacuum column
  have hfusR : ∀ a b, s a * s b = s v0 * ∑ c, (N a b c : ℝ) * s c := by
    intro a b
    have h := hfus a b v0
    simp only [hcol] at h
    exact_mod_cast h
  -- maximise `‖S_cx‖ / s_c`
  obtain ⟨b, -, hb⟩ := Finset.exists_max_image Finset.univ (fun c => ‖S c x‖ / s c)
    Finset.univ_nonempty
  set m := ‖S b x‖ / s b with hm
  have hle : ∀ c, ‖S c x‖ ≤ m * s c := fun c => by
    have := hb c (Finset.mem_univ _)
    rwa [div_le_iff₀ (hs c)] at this
  have hbx : ‖S b x‖ = m * s b := by rw [hm, div_mul_cancel₀ _ (hs b).ne']
  have hm0 : 0 ≤ m := div_nonneg (norm_nonneg _) (hs b).le
  rcases hm0.eq_or_lt with h0 | h0
  · have : ‖S a x‖ = 0 := le_antisymm (by simpa [← h0] using hle a) (norm_nonneg _)
    rw [this, zero_mul]; exact (mul_pos (hs a) (hs x)).le
  -- the Verlinde relation at `(a, b, x)`, in norms
  have h1 : ‖S a x‖ * ‖S b x‖ ≤ s x * (m * (s a * s b / s v0)) := by
    rw [← norm_mul, hfus a b x, norm_mul, hrow x, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hs x)]
    refine mul_le_mul_of_nonneg_left ?_ (hs x).le
    calc ‖∑ c, (N a b c : ℂ) * S c x‖ ≤ ∑ c, ‖(N a b c : ℂ) * S c x‖ := norm_sum_le _ _
      _ ≤ ∑ c, (N a b c : ℝ) * (m * s c) := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [norm_mul, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left (hle c) (Nat.cast_nonneg _)
      _ = m * ∑ c, (N a b c : ℝ) * s c := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
      _ = m * (s a * s b / s v0) := by
          rw [hfusR a b]; field_simp [(hs v0).ne']
  rw [hbx] at h1
  have hmb : 0 < m * s b := mul_pos h0 (hs b)
  have h2 : ‖S a x‖ * (m * s b) ≤ (s x * s a / s v0) * (m * s b) := by
    calc ‖S a x‖ * (m * s b) ≤ s x * (m * (s a * s b / s v0)) := h1
      _ = (s x * s a / s v0) * (m * s b) := by ring
  have h3 := le_of_mul_le_mul_right h2 hmb
  rw [le_div_iff₀ (hs v0)] at h3
  linarith [mul_comm (s x) (s a)]

end Algebra

/-! ## §2 The Verlinde input and the reduction -/

/-- The Verlinde data of an `S`-matrix at vacuum label `v0`: nonvanishing vacuum row, vacuum row
equal to vacuum column, and an `ℕ`-valued fusion matrix diagonalised by `S` with eigenvalues
`S_ax / S₀ₓ` (Huang's Verlinde formula in the form `N_a S = S · diag(S_ax/S₀ₓ)`). -/
structure VerlindeData {ι : Type w} [Fintype ι] (S : ι → ι → ℂ) (v0 : ι) : Prop where
  vac_row_ne : ∀ x, S v0 x ≠ 0
  symm_vac : ∀ a, S v0 a = S a v0
  fusion : ∃ N : ι → ι → ι → ℕ, ∀ a b x, S a x * S b x = S v0 x * ∑ c, (N a b c : ℂ) * S c x

/-- **Huang's Verlinde theorem (eigenvalue form, weakened).** For a nice VOA, Zhu's `ρ(S)` on a
complete irredundant family with vacuum label `v0` has `VerlindeData`.

*Source.* Y.-Z. Huang, *Vertex operator algebras and the Verlinde conjecture*, Commun. Contemp.
Math. 10 (2008) 103–154, main theorem: `S` is symmetric, `S₀ₓ ≠ 0`, and the fusion
rules `N_ab^c = dim 𝒱_{ab}^c ∈ ℕ` satisfy `N_ab^c = Σ_x S_ax S_bx (S⁻¹)_xc / S₀ₓ`, equivalently
`Σ_c N_ab^c S_cx = S_ax S_bx / S₀ₓ`. Here only the vacuum-row symmetry is asked for and `N` is
existentially quantified, so the Prop is implied by Huang's theorem.

*Not vacuous.* `ρ(S)` is pinned by `ZhuModularityAnalytic` together with linear independence of
trace functions of inequivalent irreducibles (Zhu 1996; DLM 2000), so the conclusion constrains the
actual matrix. -/
def VerlindeInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι),
      ZhuModularityAnalytic D → Irredundant D.Mfam → Complete D.Mfam →
      ∀ v0 : ι, Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)) →
        VerlindeData D.repS v0

/-- The real part of a quotient of two real complex numbers. -/
theorem div_re_of_im_eq_zero {z w : ℂ} (hz : z.im = 0) (hw : w.im = 0) :
    (z / w).re = z.re / w.re := by
  have ez : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz])
  have ew : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [hw])
  rw [ez, ew, ← Complex.ofReal_div, Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re]

/-- **The `S`-matrix consequences**, abstractly: vacuum column real non-negative (`K`) plus
Verlinde data give the reduced Huang package. -/
theorem huangSData_of_verlindeData {ι : Type w} [Fintype ι] (S : ι → ι → ℂ) (v0 : ι)
    (hK : ∀ a, S a v0 ∈ K) (hV : VerlindeData S v0) : HuangSData S v0 := by
  obtain ⟨N, hfus⟩ := hV.fusion
  set s : ι → ℝ := fun a => (S a v0).re with hs_def
  have hcol : ∀ c, S c v0 = s c := fun c => Complex.ext (by simp [s]) (by simp [s, (hK c).1])
  have hrow : ∀ x, S v0 x = s x := fun x => by rw [hV.symm_vac, hcol]
  have hs : ∀ c, 0 < s c := by
    intro c
    refine lt_of_le_of_ne (hK c).2 (fun h => hV.vac_row_ne c ?_)
    rw [hrow c, ← h]; simp
  have hfusR : ∀ a b, s a * s b = s v0 * ∑ c, (N a b c : ℝ) * s c := by
    intro a b
    have h := hfus a b v0
    simp only [hcol] at h
    exact_mod_cast h
  have hq : ∀ a, qdimOf S v0 a = s a / s v0 := fun a => by
    rw [qdimOf, div_re_of_im_eq_zero (hK a).1 (hK v0).1]
  refine
    { vac_ne_zero := hV.vac_row_ne v0
      symm_vac := hV.symm_vac
      qdim_ge_one := fun a => ?_
      bound := fun a b => ?_ }
  · rw [hq, le_div_iff₀ (hs v0), one_mul]
    exact le_of_fusion s hs v0 N hfusR a
  · have h := norm_mul_le_of_fusion S s hs v0 hcol hrow N hfus a b
    have e0 : (S v0 v0).re = s v0 := rfl
    rw [hq, hq, e0]
    rw [← le_div_iff₀ (hs v0)] at h
    calc ‖S a b‖ ≤ s a * s b / s v0 := h
      _ = s v0 * (s a / s v0) * (s b / s v0) := by field_simp [(hs v0).ne']

/-- **`HuangSInput` from the Verlinde formula.** Given rationality of `c` and `h` (for the
reality of the vacuum column, `vacColumn_mem_K`), the Verlinde input implies the reduced Huang
input: `d_a ≥ 1` and Gannon's bound are *proved*. -/
theorem huangSInput_of_verlinde (hRat : DLMRationalityInput.{u}) (hV : VerlindeInput.{u, w}) :
    HuangSInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D hZ hirr hcomp v0 hv0
  obtain ⟨⟨qc, hqc⟩, hqh⟩ := hRat 𝒱 W hNice.1
  have hc : W.centralCharge.im = 0 := by rw [← hqc]; simp
  have hreal : ∀ i, (D.h i).im = 0 := by
    intro i
    obtain ⟨q, hq⟩ := hqh _ (D.Mfam i).isMod (D.Mfam i).irreducible _ (D.hasWeight i)
    rw [← hq]; simp
  exact huangSData_of_verlindeData D.repS v0
    (fun a => vacColumn_mem_K hNice D hZ hirr v0 hv0 hreal hc a)
    (hV 𝒱 W hNice ι D hZ hirr hcomp v0 hv0)

end VOA.Huang.VerlindeReduction
