import VOA.Classification.COne.PlusRat4Degree

/-! # The degree-two transfer lemma (general VOA)

`TopData A χ h y`: `y ∈ Ω`, Zhu's algebra acts on `y` through `χ`, `L(0)y = h y`, and every
degree-one single mode on `y` is a multiple of `L(-1)y` (`Deg1Line`).

For such `y` (with `y ≠ 0`, `h ≠ 0`) every degree-one single mode is pinned down by `χ`:
`u₍ⱼ₋₂₎y = κ(u) L(-1)y` with `κ(u) = χ(zstate u ω 2)/(2h)` (`TopData.deg1`).  Hence for the
corrected degree-two vector `w_y = t₍ₖ₋₃₎y - a L(-1)²y - b L(-2)y`, every lowering mode of degree
`-2` acts by an explicit scalar `Fdeg2` and every lowering mode of degree `-1` by an explicit
multiple `Fdeg1` of `L(-1)y`, both depending only on `(χ, h)`.

`transfer2`: if `x` (in `A`) and `e ≠ 0` (in a model `B`) carry the same data, and
`t₍ₖ₋₃₎e = a L(-1)²e + b L(-2)e` in the model, then `t₍ₖ₋₃₎x - a L(-1)²x - b L(-2)x ∈ Ω(A)`
(given no generalized weights of `A` below `h`).
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusRat4
open VOA VertexOperatorAlgebra PlusSplitting PlusRatTelescope VOA.Huang.LogRemovalAdmissible
  ABDWeakAdmissible PlusRatSign PlusRat3
universe u
variable {V M N : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] {W : VertexOperatorAlgebra V}

/-- Top data: `Ω`, Zhu character `χ`, `L(0) = h`, degree-one line. -/
structure TopData (A : WeakModule W M) (χ : VOA.A W → ℂ) (h : ℂ) (y : M) : Prop where
  omega : y ∈ Omega A
  char : ∀ r, topEvaluation A y omega r = χ r • y
  L0 : L0 A y = h • y
  line : Deg1Line A y

/-- The degree-one coefficient `κ(u) = χ(zstate u ω 2)/(2h)`. -/
def kap (χ : VOA.A W → ℂ) (h : ℂ) (u : V) : ℂ :=
  χ (VOA.mk W (zstate W u W.conformalVector 2)) / (2 * h)

namespace TopData
variable {A : WeakModule W M} {χ : VOA.A W → ℂ} {h : ℂ} {y : M}

theorem zero (hy : TopData A χ h y) {k : ℤ} {a : V} (ha : a ∈ W.grading k) :
    mode (A.YM a) (k - 1) y = χ (VOA.mk W a) • y := by
  have h1 := hy.char (VOA.mk W a)
  rw [topEvaluation_mk, oLevW_homogeneous A 0 ha, add_zero] at h1
  exact h1

theorem lower (hy : TopData A χ h y) {α β : ℤ} {a b : V} (ha : a ∈ W.grading α)
    (hb : b ∈ W.grading β) (P : ℕ) (q : ℤ) (hP : β ≤ (P : ℤ)) (hq : (P : ℤ) + q = α + β - 2) :
    mode (A.YM b) (P : ℤ) (mode (A.YM a) q y) = χ (VOA.mk W (zstate W a b P)) • y := by
  rw [lowering_composite_eq A ha hb hy.omega P q hP hq, ← topEvaluation_mk A y hy.omega, hy.char]

theorem L1L (hy : TopData A χ h y) :
    mode (A.YM W.conformalVector) 2 (mode (A.YM W.conformalVector) 0 y) = (2 * h) • y := by
  rw [mode_translation, Omega_mode_vanish hy.omega W.conformal_mem (show (2 : ℤ) ≤ 2 by norm_num),
    map_zero, zero_add, show (2 : ℤ) - 1 = 1 by norm_num]
  have hL : mode (A.YM W.conformalVector) 1 y = h • y := hy.L0
  rw [hL, smul_smul]
  norm_num

theorem Lm1_ne_zero (hy : TopData A χ h y) (hh : h ≠ 0) (hy0 : y ≠ 0) :
    mode (A.YM W.conformalVector) 0 y ≠ 0 := by
  intro h0
  have h1 := hy.L1L
  rw [h0, map_zero] at h1
  rcases smul_eq_zero.mp h1.symm with h2 | h2
  · exact hh (by linear_combination h2 / 2)
  · exact hy0 h2

/-- Degree-one modes are pinned down by `χ`. -/
theorem deg1 (hy : TopData A χ h y) (hh : h ≠ 0) (hy0 : y ≠ 0) {j : ℤ} {u : V}
    (hu : u ∈ W.grading j) :
    mode (A.YM u) (j - 2) y = kap χ h u • mode (A.YM W.conformalVector) 0 y := by
  obtain ⟨κ, hκ⟩ := hy.line j u hu
  have h1 := hy.lower hu W.conformal_mem 2 (j - 2) (by norm_num) (by ring)
  rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hκ, map_smul, hy.L1L, smul_smul] at h1
  have hk : κ = kap χ h u := by
    have h2 : (κ * (2 * h) - χ (VOA.mk W (zstate W u W.conformalVector 2))) • y = 0 := by
      rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · rw [kap, eq_div_iff (mul_ne_zero two_ne_zero hh)]
      linear_combination h3
    · exact absurd h3 hy0
  rw [hκ, hk]

end TopData

/-! ## The lowering scalars -/

/-- The degree `-2` scalar. -/
def Fdeg2 (χ : VOA.A W → ℂ) (t : V) (a b : ℂ) (c : V) (P : ℕ) : ℂ :=
  χ (VOA.mk W (zstate W t c (P + 1))) -
    a * (((P : ℂ) + 1) * χ (VOA.mk W (zstate W W.conformalVector c P))) -
    b * χ (VOA.mk W (zstate W W.conformalVector c (P + 1)))

/-- The degree `-1` coefficient. -/
def Fdeg1 (χ : VOA.A W → ℂ) (h : ℂ) (t : V) (a b : ℂ) (c : V) (P : ℕ) : ℂ :=
  (∑ j ∈ Finset.range (P + 1), (P.choose j : ℂ) * kap χ h (W.smul c j t)) -
    a * ((P : ℂ) * (2 * χ (VOA.mk W c) + ((P : ℂ) - 1) * kap χ h c)) -
    b * (∑ j ∈ Finset.range (P + 1), (P.choose j : ℂ) * kap χ h (W.smul c j W.conformalVector))

namespace TopData
variable {A : WeakModule W M} {χ : VOA.A W → ℂ} {h : ℂ} {y : M}

/-- The corrected degree-two vector. -/
abbrev wv (A : WeakModule W M) (y : M) (t : V) (k : ℤ) (a b : ℂ) : M :=
  mode (A.YM t) (k - 3) y -
    a • mode (A.YM W.conformalVector) 0 (mode (A.YM W.conformalVector) 0 y) -
    b • mode (A.YM W.conformalVector) (-1) y

theorem lower2 (hy : TopData A χ h y) {k : ℤ} {t : V} (ht : t ∈ W.grading k) (a b : ℂ)
    {c : V} {P : ℕ} (hc : c ∈ W.grading (P : ℤ)) :
    mode (A.YM c) ((P : ℤ) + 1) (wv A y t k a b) = Fdeg2 χ t a b c P • y := by
  have h1 := hy.lower ht hc (P + 1) (k - 3) (by push_cast; omega) (by push_cast; ring)
  have h2 := hy.lower W.conformal_mem hc (P + 1) (-1) (by push_cast; omega) (by push_cast; ring)
  have h3 := hy.lower W.conformal_mem hc P 0 le_rfl (by ring)
  push_cast at h1 h2
  have h4 : mode (A.YM c) ((P : ℤ) + 1) (mode (A.YM W.conformalVector) 0 y) = 0 := by
    rw [mode_translation, Omega_mode_vanish hy.omega hc (by omega), map_zero, zero_add,
      Omega_mode_vanish hy.omega hc (by omega), smul_zero]
  have h5 : mode (A.YM c) ((P : ℤ) + 1)
      (mode (A.YM W.conformalVector) 0 (mode (A.YM W.conformalVector) 0 y)) =
      (((P : ℂ) + 1) * χ (VOA.mk W (zstate W W.conformalVector c P))) • y := by
    rw [mode_translation, h4, map_zero, zero_add, show (P : ℤ) + 1 - 1 = P by ring, h3, smul_smul]
    push_cast; ring_nf
  simp only [wv, map_sub, map_smul, h1, h2, h5, Fdeg2, smul_smul, sub_smul]

theorem lower1 (hy : TopData A χ h y) (hh : h ≠ 0) (hy0 : y ≠ 0) {k : ℤ} {t : V}
    (ht : t ∈ W.grading k) (a b : ℂ) {c : V} {P : ℕ} (hc : c ∈ W.grading (P : ℤ)) :
    mode (A.YM c) (P : ℤ) (wv A y t k a b) =
      Fdeg1 χ h t a b c P • mode (A.YM W.conformalVector) 0 y := by
  -- `c_P t_{k-3} y`
  have h1 : mode (A.YM c) (P : ℤ) (mode (A.YM t) (k - 3) y) =
      (∑ j ∈ Finset.range (P + 1), (P.choose j : ℂ) * kap χ h (W.smul c j t)) • mode (A.YM W.conformalVector) 0 y := by
    have hc1 := mode_commutator A c t y (P : ℤ) (k - 3)
    rw [Omega_mode_vanish hy.omega hc le_rfl, map_zero, sub_zero, finsum_cbz_nat] at hc1
    rw [hc1, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro j _
    have hg := W.toPreVertexAlgebra.smul_mem_grading hc ht (j : ℤ)
    have := hy.deg1 hh hy0 hg
    rw [show (P : ℤ) + k - (j : ℤ) - 1 - 2 = (P : ℤ) + (k - 3) - (j : ℤ) by ring] at this
    rw [this, smul_smul]
  -- `c_P L(-2) y`
  have h2 : mode (A.YM c) (P : ℤ) (mode (A.YM W.conformalVector) (-1) y) =
      (∑ j ∈ Finset.range (P + 1), (P.choose j : ℂ) *
        kap χ h (W.smul c j W.conformalVector)) • mode (A.YM W.conformalVector) 0 y := by
    have hc1 := mode_commutator A c W.conformalVector y (P : ℤ) (-1)
    rw [Omega_mode_vanish hy.omega hc le_rfl, map_zero, sub_zero, finsum_cbz_nat] at hc1
    rw [hc1, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro j _
    have hg := W.toPreVertexAlgebra.smul_mem_grading hc W.conformal_mem (j : ℤ)
    have := hy.deg1 hh hy0 hg
    rw [show (P : ℤ) + 2 - (j : ℤ) - 1 - 2 = (P : ℤ) + -1 - (j : ℤ) by ring] at this
    rw [this, smul_smul]
  -- `c_P L(-1)² y`
  have h3 : mode (A.YM c) (P : ℤ) (mode (A.YM W.conformalVector) 0 y) =
      ((P : ℂ) * χ (VOA.mk W c)) • y := by
    rw [mode_translation, Omega_mode_vanish hy.omega hc le_rfl, map_zero, zero_add,
      show (P : ℤ) - 1 = (P : ℤ) - 1 from rfl, hy.zero hc, smul_smul]
    push_cast; ring_nf
  have h4 : mode (A.YM c) ((P : ℤ) - 1) (mode (A.YM W.conformalVector) 0 y) =
      (χ (VOA.mk W c) + ((P : ℂ) - 1) * kap χ h c) • mode (A.YM W.conformalVector) 0 y := by
    rw [mode_translation, hy.zero hc, map_smul, show (P : ℤ) - 1 - 1 = (P : ℤ) - 2 by ring,
      hy.deg1 hh hy0 hc, smul_smul, ← add_smul]
    congr 1; push_cast; ring
  have h5 : mode (A.YM c) (P : ℤ) (mode (A.YM W.conformalVector) 0 (mode (A.YM W.conformalVector) 0 y)) =
      ((P : ℂ) * (2 * χ (VOA.mk W c) + ((P : ℂ) - 1) * kap χ h c)) • mode (A.YM W.conformalVector) 0 y := by
    rw [mode_translation, h3, map_smul, h4, smul_smul, ← add_smul]
    congr 1; push_cast; ring
  simp only [wv, map_sub, map_smul, h1, h2, h5, Fdeg1, smul_smul, sub_smul]

end TopData

/-- **Degree-two transfer** (any VOA). -/
theorem transfer2 (A : WeakModule W M) (B : WeakModule W N) (χ : VOA.A W → ℂ) {h : ℂ}
    {x : M} {e : N} (hx : TopData A χ h x) (he : TopData B χ h e) (hx0 : x ≠ 0) (he0 : e ≠ 0)
    (hh : h ≠ 0)
    (hlow : ∀ μ : ℂ, μ.re < h.re → ∀ v ∈ (L0 A).maxGenEigenspace μ, v = 0)
    {k : ℤ} {t : V} (ht : t ∈ W.grading k) {a b : ℂ}
    (hc : TopData.wv B e t k a b = 0) :
    TopData.wv A x t k a b ∈ Omega A := by
  intro β c hc' n hn
  by_cases hβ0 : β < 0
  · rw [W.positivity β hβ0, Submodule.mem_bot] at hc'
    subst hc'
    rw [map_zero, mode_zero, LinearMap.zero_apply]
  obtain ⟨P, rfl⟩ : ∃ P : ℕ, β = P := ⟨β.toNat, by omega⟩
  rcases eq_or_lt_of_le hn with hnβ | hnβ
  · -- degree `-1`
    subst hnβ
    rw [hx.lower1 hh hx0 ht a b hc']
    have he1 := he.lower1 hh he0 ht a b hc'
    rw [hc, map_zero] at he1
    rcases smul_eq_zero.mp he1.symm with h0 | h0
    · rw [h0, zero_smul]
    · exact absurd h0 (he.Lm1_ne_zero hh he0)
  rcases eq_or_lt_of_le (show (P : ℤ) + 1 ≤ n by omega) with hn1 | hn1
  · -- degree `-2`
    subst hn1
    rw [hx.lower2 ht a b hc']
    have he2 := he.lower2 ht a b hc'
    rw [hc, map_zero] at he2
    rcases smul_eq_zero.mp he2.symm with h0 | h0
    · rw [h0, zero_smul]
    · exact absurd h0 he0
  · -- degree `≤ -3`
    have hxg : x ∈ (L0 A).maxGenEigenspace h :=
      Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hx.L0)
    have hv : TopData.wv A x t k a b ∈ (L0 A).maxGenEigenspace (h + 2) := by
      have h1 := mode_mem_maxGenEigenspace A ht (k - 3) hxg
      have h2 := mode_mem_maxGenEigenspace A W.conformal_mem 0
        (mode_mem_maxGenEigenspace A W.conformal_mem 0 hxg)
      have h3 := mode_mem_maxGenEigenspace A W.conformal_mem (-1) hxg
      have hc1 : h + ((k - (k - 3) - 1 : ℤ) : ℂ) = h + 2 := by push_cast; ring
      have hc2 : h + ((2 - 0 - 1 : ℤ) : ℂ) + ((2 - 0 - 1 : ℤ) : ℂ) = h + 2 := by push_cast; ring
      have hc3 : h + ((2 - (-1) - 1 : ℤ) : ℂ) = h + 2 := by push_cast; ring
      rw [hc1] at h1
      rw [hc2] at h2
      rw [hc3] at h3
      exact Submodule.sub_mem _ (Submodule.sub_mem _ h1 (Submodule.smul_mem _ _ h2))
        (Submodule.smul_mem _ _ h3)
    have h3 := mode_mem_maxGenEigenspace A hc' n hv
    apply hlow _ _ _ h3
    have : (((P : ℤ) - n - 1 : ℤ) : ℝ) ≤ -3 := by exact_mod_cast (show (P : ℤ) - n - 1 ≤ -3 by omega)
    rw [Complex.add_re, Complex.add_re, Complex.intCast_re]
    have h2re : (2 : ℂ).re = 2 := by norm_num
    rw [h2re]
    linarith

end VOA.Classification.COne.PlusRat4
