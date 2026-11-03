import VOA.Classification.COne.PlusRat4Transfer

/-! # Degree-two transfer with an extra single mode (general VOA)

`wv3 y t k u j a b c = t₍ₖ₋₃₎y - a L(-1)²y - b L(-2)y - c u₍ⱼ₋₃₎y`.  If this vanishes in a model
`e` with the same top data as `x`, it is a top vector at `x` (`transfer3`).  This extends
`transfer2` (the case `c = 0`) and is needed when `L(-1)²e, L(-2)e` do not span the model's
degree-two space (e.g. at `h = 1/4`).
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusRat4
open VOA VertexOperatorAlgebra PlusSplitting PlusRatTelescope VOA.Huang.LogRemovalAdmissible
  ABDWeakAdmissible PlusRatSign PlusRat3
universe u
variable {V M N : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] {W : VertexOperatorAlgebra V}

namespace TopData
variable {A : WeakModule W M} {χ : VOA.A W → ℂ} {h : ℂ} {y : M}

/-- The corrected degree-two vector with an extra single mode. -/
abbrev wv3 (A : WeakModule W M) (y : M) (t : V) (k : ℤ) (u : V) (j : ℤ) (a b c : ℂ) : M :=
  wv A y t k a b - c • wv A y u j 0 0

theorem wv_zero (A : WeakModule W M) (y : M) (u : V) (j : ℤ) :
    wv A y u j 0 0 = mode (A.YM u) (j - 3) y := by
  simp [wv]

theorem lower2_3 (hy : TopData A χ h y) {k j : ℤ} {t u : V} (ht : t ∈ W.grading k)
    (hu : u ∈ W.grading j) (a b c : ℂ) {c' : V} {P : ℕ} (hc : c' ∈ W.grading (P : ℤ)) :
    mode (A.YM c') ((P : ℤ) + 1) (wv3 A y t k u j a b c) =
      (Fdeg2 χ t a b c' P - c * Fdeg2 χ u 0 0 c' P) • y := by
  rw [wv3, map_sub, map_smul, hy.lower2 ht a b hc, hy.lower2 hu 0 0 hc, smul_smul, ← sub_smul]

theorem lower1_3 (hy : TopData A χ h y) (hh : h ≠ 0) (hy0 : y ≠ 0) {k j : ℤ} {t u : V}
    (ht : t ∈ W.grading k) (hu : u ∈ W.grading j) (a b c : ℂ) {c' : V} {P : ℕ}
    (hc : c' ∈ W.grading (P : ℤ)) :
    mode (A.YM c') (P : ℤ) (wv3 A y t k u j a b c) =
      (Fdeg1 χ h t a b c' P - c * Fdeg1 χ h u 0 0 c' P) •
        mode (A.YM W.conformalVector) 0 y := by
  rw [wv3, map_sub, map_smul, hy.lower1 hh hy0 ht a b hc, hy.lower1 hh hy0 hu 0 0 hc, smul_smul,
    ← sub_smul]

end TopData

/-- **Degree-two transfer with an extra single mode.** -/
theorem transfer3 (A : WeakModule W M) (B : WeakModule W N) (χ : VOA.A W → ℂ) {h : ℂ}
    {x : M} {e : N} (hx : TopData A χ h x) (he : TopData B χ h e) (hx0 : x ≠ 0) (he0 : e ≠ 0)
    (hh : h ≠ 0)
    (hlow : ∀ μ : ℂ, μ.re < h.re → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0)
    {k j : ℤ} {t u : V} (ht : t ∈ W.grading k) (hu : u ∈ W.grading j) {a b c : ℂ}
    (hc : TopData.wv3 B e t k u j a b c = 0) :
    TopData.wv3 A x t k u j a b c ∈ Omega A := by
  intro β c' hc' n hn
  by_cases hβ0 : β < 0
  · rw [W.positivity β hβ0, Submodule.mem_bot] at hc'
    subst hc'
    rw [map_zero, mode_zero, LinearMap.zero_apply]
  obtain ⟨P, rfl⟩ : ∃ P : ℕ, β = P := ⟨β.toNat, by omega⟩
  rcases eq_or_lt_of_le hn with hnβ | hnβ
  · subst hnβ
    rw [hx.lower1_3 hh hx0 ht hu a b c hc']
    have he1 := he.lower1_3 hh he0 ht hu a b c hc'
    rw [hc, map_zero] at he1
    rcases smul_eq_zero.mp he1.symm with h0 | h0
    · rw [h0, zero_smul]
    · exact absurd h0 (he.Lm1_ne_zero hh he0)
  rcases eq_or_lt_of_le (show (P : ℤ) + 1 ≤ n by omega) with hn1 | hn1
  · subst hn1
    rw [hx.lower2_3 ht hu a b c hc']
    have he2 := he.lower2_3 ht hu a b c hc'
    rw [hc, map_zero] at he2
    rcases smul_eq_zero.mp he2.symm with h0 | h0
    · rw [h0, zero_smul]
    · exact absurd h0 he0
  · have hxg : x ∈ (L0 A).maxGenEigenspace h :=
      Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hx.L0)
    have hgen : ∀ {k' : ℤ} {s : V}, s ∈ W.grading k' → ∀ a' b' : ℂ,
        TopData.wv A x s k' a' b' ∈ (L0 A).maxGenEigenspace (h + 2) := by
      intro k' s hs a' b'
      have h1 := mode_mem_maxGenEigenspace A hs (k' - 3) hxg
      have h2 := mode_mem_maxGenEigenspace A W.conformal_mem 0
        (mode_mem_maxGenEigenspace A W.conformal_mem 0 hxg)
      have h3 := mode_mem_maxGenEigenspace A W.conformal_mem (-1) hxg
      have hc1 : h + ((k' - (k' - 3) - 1 : ℤ) : ℂ) = h + 2 := by push_cast; ring
      have hc2 : h + ((2 - 0 - 1 : ℤ) : ℂ) + ((2 - 0 - 1 : ℤ) : ℂ) = h + 2 := by push_cast; ring
      have hc3 : h + ((2 - (-1) - 1 : ℤ) : ℂ) = h + 2 := by push_cast; ring
      rw [hc1] at h1
      rw [hc2] at h2
      rw [hc3] at h3
      exact Submodule.sub_mem _ (Submodule.sub_mem _ h1 (Submodule.smul_mem _ _ h2))
        (Submodule.smul_mem _ _ h3)
    have hv : TopData.wv3 A x t k u j a b c ∈ (L0 A).maxGenEigenspace (h + 2) :=
      Submodule.sub_mem _ (hgen ht a b) (Submodule.smul_mem _ _ (hgen hu 0 0))
    have h3 := mode_mem_maxGenEigenspace A hc' n hv
    apply hlow _ _ _ h3
    have : (((P : ℤ) - n - 1 : ℤ) : ℝ) ≤ -3 := by exact_mod_cast (show (P : ℤ) - n - 1 ≤ -3 by omega)
    rw [Complex.add_re, Complex.add_re, Complex.intCast_re]
    have h2re : (2 : ℂ).re = 2 := by norm_num
    rw [h2re]
    linarith

end VOA.Classification.COne.PlusRat4
