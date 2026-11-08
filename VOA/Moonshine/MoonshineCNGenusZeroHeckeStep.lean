/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroDiscrete

/-!
# Genus zero on the abstract interface: Hecke closure of the symmetry group

The Hecke-closure hypothesis of Cummins (2002), Prop. 2.1, at primes (blueprint
`Notes/moonshine/MOON_M8_LEAN.md`). Let `F` satisfy the prime Hecke identity at a prime `p`,
`f = qSeriesFun (F.c k)` and `G = symmetryGroup f`. For `g = (a b; c d) ∈ G` the pairing on the
connected domain `ℍ` (`exists_heckeAffine_partner`, with `u = g`, `v = id`, `M = (p 0; 0 1)`)
gives a partner `β ∈ Δ(p)` with `f (p · g z) = f (β z)` on `ℍ`, i.e. `(p 0; 0 1) g β⁻¹ ∈ G`
after normalising the determinant:

* `β = (p 0; 0 1)` gives `(a, p b; c / p, d) ∈ G`;
* `β = (1 j; 0 p)` gives `(p a, b - j a; c, (d - j c) / p) ∈ G`.

If `0 < |c| < p`, Shimizu's lemma excludes the first case (its lower-left entry `c / p` has
absolute value in `(0, 1)`), so the **Hecke step** `exists_heckeStep_mem_symmetryGroup` holds:
`(p a, b - j a; c, (d - j c) / p) ∈ G` for some `j < p`. The lower-left entry is unchanged.
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology Set

/-- **The Hecke step**. Let `F` satisfy the prime Hecke identity at the prime `p`, and let
`g = (a b; c d)` be a symmetry of `f = qSeriesFun (F.c k)` with `0 < |c| < p`. Then for some
`j < p` the matrix `(p a, b - j a; c, (d - j c) / p)` is again a symmetry of `f`. -/
theorem exists_heckeStep_mem_symmetryGroup {N : ℕ} (F : ReplicableFamily N) (k : ℕ) {p : ℕ}
    (hp : p.Prime) (hB1 : PrimeHeckeIdentityAt F k p hp.pos) {g : GL (Fin 2) ℝ}
    (hg : g ∈ symmetryGroup (qSeriesFun (F.c k))) (hc0 : g 1 0 ≠ 0) (hcp : |g 1 0| < p) :
    ∃ j : ℕ, j < p ∧ ∃ h ∈ symmetryGroup (qSeriesFun (F.c k)), h 0 0 = p * g 0 0 ∧
      h 0 1 = g 0 1 - j * g 0 0 ∧ h 1 0 = g 1 0 ∧ h 1 1 = (g 1 1 - j * g 1 0) / p := by
  have hc := F.isJDominated k
  have hdet := det_entries_of_mem_symmetryGroup hg
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hp0 : (p : ℝ) ≠ 0 := hpR.ne'
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
  set a := g 0 0 with ha
  set b := g 0 1 with hb
  set c₀ := g 1 0 with hc₀
  set d := g 1 1 with hd
  -- the Möbius map of `g` on `ℂ`
  set u : ℂ → ℂ := fun z => ((a : ℂ) * z + b) / ((c₀ : ℂ) * z + d) with hu_def
  have huτ : ∀ τ : ℍ, u τ = ((g • τ : ℍ) : ℂ) := by
    intro τ
    rw [coe_smul_of_det_pos (by rw [det_val_eq_one_of_mem_symmetryGroup hg]; exact one_pos)]
    simp [num, denom, hu_def, ha, hb, hc₀, hd]
  have hu : DifferentiableOn ℂ u upperHalfPlaneSet := by
    intro z hz
    have h1 : DifferentiableAt ℂ (fun z : ℂ => (a : ℂ) * z + b) z := by fun_prop
    have h2 : DifferentiableAt ℂ (fun z : ℂ => (c₀ : ℂ) * z + d) z := by fun_prop
    exact (h1.div h2 (moebius_denom_ne_zero hdet hz)).differentiableWithinAt
  have huU : ∀ z ∈ upperHalfPlaneSet, 0 < (u z).im := by
    intro z hz
    have := huτ ⟨z, hz⟩
    rw [this]
    exact (g • (⟨z, hz⟩ : ℍ)).im_pos
  have huv : ∀ z ∈ upperHalfPlaneSet,
      qSeriesExt (F.c k) (u z) = qSeriesExt (F.c k) (id z) := by
    intro z hz
    have := huτ ⟨z, hz⟩
    rw [this, qSeriesExt_coe, hg.2, id, qSeriesExt_of_im_pos _ hz]
  obtain ⟨β, hβ⟩ := exists_heckeAffine_partner F k p hp.pos hB1 isOpen_upperHalfPlaneSet
    (convex_halfSpace_im_gt 0).isPreconnected ⟨Complex.I, by simp⟩ hu differentiableOn_id huU
    (fun z hz => hz) huv none
  cases β with
  | none =>
    -- the partner `z ↦ p z`: `(a, p b; c / p, d)` is a symmetry, against Shimizu
    exfalso
    have hdet' : a * d - p * b * (c₀ / p) = 1 := by
      field_simp
      linear_combination hdet
    have hmem : glOfDetOne a (p * b) (c₀ / p) d hdet' ∈ symmetryGroup (qSeriesFun (F.c k)) := by
      refine glOfDetOne_mem_symmetryGroup_of hdet' fun τ => ?_
      have hz : 0 < ((τ : ℂ) / p).im := by
        rw [Complex.div_natCast_im]; exact div_pos τ.im_pos hpR
      have hrel := hβ ((τ : ℂ) / p) hz
      simp only [id_eq] at hrel
      have hD : (c₀ : ℂ) * ((τ : ℂ) / p) + d = ((c₀ / p : ℝ) : ℂ) * τ + (d : ℂ) := by
        push_cast; ring
      have key : (p : ℂ) * ((τ : ℂ) / p) = τ := by field_simp
      have e1 : heckeAffine p none (u ((τ : ℂ) / p)) =
          (((a : ℝ) : ℂ) * τ + ((p * b : ℝ) : ℂ)) / (((c₀ / p : ℝ) : ℂ) * τ + (d : ℂ)) := by
        simp only [heckeAffine, affC, heckeDil, heckeTr, hu_def, Complex.ofReal_zero, add_zero,
          Complex.ofReal_natCast]
        rw [hD, mul_div_assoc']
        congr 1
        push_cast
        linear_combination (a : ℂ) * key
      have e2 : heckeAffine p none ((τ : ℂ) / p) = τ := by
        simp only [heckeAffine, affC, heckeDil, heckeTr, Complex.ofReal_zero, add_zero,
          Complex.ofReal_natCast]
        exact key
      rw [← e1, hrel, e2]
    have hlow := one_le_abs_lowerLeft_qSeriesFun hc hmem (by
      rw [glOfDetOne_apply_one_zero]; exact div_ne_zero hc0 hp0)
    rw [glOfDetOne_apply_one_zero, abs_div, Nat.abs_cast, le_div_iff₀ hpR, one_mul] at hlow
    exact absurd hcp (not_lt.mpr hlow)
  | some j =>
    set jn : ℕ := (j : ℕ) with hjn
    have hdet' : (p * a) * ((d - jn * c₀) / p) - (b - jn * a) * c₀ = 1 := by
      field_simp
      linear_combination hdet
    refine ⟨jn, j.isLt, glOfDetOne (p * a) (b - jn * a) c₀ ((d - jn * c₀) / p) hdet', ?_,
      by simp, by simp, by simp, by simp⟩
    refine glOfDetOne_mem_symmetryGroup_of hdet' fun τ => ?_
    have hz : 0 < ((p : ℂ) * τ - jn).im := by
      simp only [Complex.sub_im, Complex.natCast_im, sub_zero, Complex.mul_im,
        Complex.natCast_re, zero_mul, add_zero]
      exact mul_pos hpR τ.im_pos
    have hrel := hβ ((p : ℂ) * τ - jn) hz
    simp only [id_eq] at hrel
    have k1 : (p : ℂ) * (((d : ℂ) - (jn : ℂ) * c₀) / p) = d - (jn : ℂ) * c₀ := by field_simp
    have hD : (c₀ : ℂ) * ((p : ℂ) * τ - jn) + d =
        (p : ℂ) * (((c₀ : ℝ) : ℂ) * τ + (((d - jn * c₀) / p : ℝ) : ℂ)) := by
      push_cast
      rw [mul_add, k1]
      ring
    have e1 : heckeAffine p none (u ((p : ℂ) * τ - jn)) =
        (((p * a : ℝ) : ℂ) * τ + ((b - jn * a : ℝ) : ℂ)) /
          (((c₀ : ℝ) : ℂ) * τ + (((d - jn * c₀) / p : ℝ) : ℂ)) := by
      simp only [heckeAffine, affC, heckeDil, heckeTr, hu_def, Complex.ofReal_zero, add_zero,
        Complex.ofReal_natCast]
      rw [hD, mul_div_assoc', mul_div_mul_left _ _ hpC]
      congr 1
      push_cast
      ring
    have e2 : heckeAffine p (some j) ((p : ℂ) * τ - jn) = τ := by
      simp only [heckeAffine, affC, heckeDil, heckeTr]
      push_cast
      field_simp
      ring
    rw [← e1, hrel, e2]

end VOA.Moonshine.ConwayNorton
