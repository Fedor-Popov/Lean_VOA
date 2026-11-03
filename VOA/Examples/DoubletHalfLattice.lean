/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.DoubletGenerators
import VOA.Examples.LatticeQuadRefine
import VOA.Examples.TripletLattice

/-!
# The concrete doublet **half lattice** `½ℤγ` and its ℚ-valued quadratic refinement

`Examples.DoubletGenerators` works with an *abstract* ambient lattice `L` carrying a vector `g`
(playing the role of `γ/2`) subject to the denominator-free hypothesis

  `hgg : 2 * ⟨g,g⟩ = p`.

This file supplies the **concrete** lattice realizing that hypothesis, together with the ℚ-valued
quadratic refinement carrying the doublet background charge.  Everything here is pure lattice
arithmetic — no vertex algebra.

## Contents

* `hlatP p` — the rank-one lattice with carrier `ℤ` and Gram form `⟨m,n⟩ = (p/2)·m·n`
  (**natural** division; the arithmetic is kept exact by carrying `hp2 : 2 * k = p`).
  Its generator `gHalf p = 1` satisfies `2⟨g,g⟩ = p` on the nose (`hgg_hlatP`), so it unifies
  *literally* with `Doublet.hgg`; `hlatP_form_gamma_gHalf` etc. are proved by feeding
  `hgg_hlatP` to the `Doublet.*` lemmas, which is a machine-checked unification test.
* `hlatP_doubling_isometry` / `qH_two_mul` — `hlatP p` really is the **index-two overlattice**
  of the triplet lattice `Triplet.latP p`: doubling `m ↦ 2m` is an isometry `latP p ↪ hlatP p`,
  and it pulls the doublet weight `qH` back to the triplet weight `Triplet.qZP`.
* `hlatP_posDef` — positive-definite for `2 ≤ p` (i.e. `p > 0` once `p` is even, as it must be).
* `hlatP_even_iff` — **`hlatP p` is an even lattice iff `4 ∣ p`.**  Both directions are proved
  separately as `hlatP_even_of_four_dvd` and `hlatP_not_even_of_not_four_dvd`; evenness is *not*
  assumed globally.  This matches `Doublet.form_gg_even_iff` on the nose.
* `qH p m = (p·m²)/4 − ((p−1)·m)/2` — the ℚ-valued deformed weight of `e^{mg}`, and
  `qrH p k hp2 : QuadRefine (hlatP p)` (the polarization axiom needs `p` even, hence `hp2`).
  `qZH k m = k·m² − (2k−1)·m` is the integral numerator: `qH p m = qZH k m / 2`.
* `qH_one : q(1) = (2−p)/4` and `qH_neg_one : q(−1) = (3p−2)/4` — the doublet weights
  `wt(e^{+g})` and `wt(e^{−g})` of `Doublet.LBG_zero_eG` / `Doublet.LBG_zero_aMinus`.
* `not_posQuad_qrH` — **`PosQuad` genuinely FAILS for `p > 2`**, witnessed by `q(1) < 0`.
  This is a theorem, not a remark: it is exactly why the doublet ambient cannot be routed through
  `PosQuad` and must instead go through `SuperNearVOA.BoundedBelow`.
* `qH_bddBelow` / `qH_ge` — the refinement *is* bounded below: `q(m) ≥ (1−k)/2` for all `m`, with
  equality at `m = 1`.  So the deformed grading is bounded below even though it is not positive.
* `qFinite_qrH` — `QFinite`, via `|m| ≤ qZH k m + k`.
* `qH_neg_one_int_iff` / `qH_neg_one_halfInt_iff` — the **mod-4 dichotomy at the level of this
  lattice**: `(3p−2)/4 ∈ ℤ` iff `p ≡ 2 mod 4`, and `(3p−2)/4 ∈ ℤ + ½` iff `4 ∣ p`.  Combined with
  `hlatP_even_iff` this says: the half lattice is even (bosonic ambient) exactly when the doublet
  weight is a half-integer, and odd (super ambient) exactly when it is an integer.

## Status
All `sorry`-free and axiom-clean.  Nothing here needs `4 ∣ p`; each result states the `p`-range it
needs (`2 ≤ p` for positive-definiteness, `1 ≤ k` for the bounds, `2 < p` for the failure of
`PosQuad`, `4 ∣ p` only for evenness).
-/

set_option linter.style.longLine false

open scoped BigOperators TensorProduct
open VOA VOA.IntegralLattice
open VOA.LatGen

namespace VOA.LatGen.HalfLat

/-! ## §1  (a)  The half lattice `½ℤγ`

The triplet lattice is `L_p = ℤα`, `⟨α,α⟩ = 2p` (`Triplet.latP`).  The doublet needs the lattice
*half* as large: a rank-one lattice containing `g = γ/2` with `⟨g,g⟩ = p/2`.  Since
`IntegralLattice.form` is **ℤ-valued**, `p/2` must be an integer, so `p` is even — which is
forced anyway (`Doublet.p_even`).

We write the Gram form with **natural** division `p / 2`, and keep every computation exact by
carrying the witness `hp2 : 2 * k = p`.  (Writing `(p : ℤ) / 2` would be equally lossy and much
harder to reason about; `hp2` makes all the arithmetic `omega`-decidable.) -/

/-- **The doublet half lattice** `½ℤγ`: the ℤ-module `ℤ` with Gram form `⟨m,n⟩ = (p/2)·m·n`
(natural division).  Its generator is `g = γ/2`, so `⟨g,g⟩ = p/2` and `⟨γ,γ⟩ = 2p`, matching the
triplet normalization of `Triplet.latP`.  It is the *index-two overlattice* of `Triplet.latP p`
after the rescaling `α ↦ γ = 2g`. -/
noncomputable def hlatP (p : ℕ) : IntegralLattice where
  carrier := ℤ
  form := ((p / 2 : ℕ) : ℤ) • LinearMap.mul ℤ ℤ
  isSymm := by
    rw [LinearMap.BilinForm.isSymm_def]
    intro v w
    simp only [LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
    ring

/-- The Gram form of the half lattice: `⟨m,n⟩ = (p/2)·m·n` with **natural** division. -/
theorem hlatP_form (p : ℕ) (m n : ℤ) : (hlatP p).form m n = ((p / 2 : ℕ) : ℤ) * m * n := by
  change ((((p / 2 : ℕ)) : ℤ) • LinearMap.mul ℤ ℤ) m n = _
  simp only [LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
  ring

/-- With the exactness witness `2 * k = p` the form is `⟨m,n⟩ = k·m·n`, division-free. -/
theorem hlatP_form_k (p k : ℕ) (hp2 : 2 * k = p) (m n : ℤ) :
    (hlatP p).form m n = (k : ℤ) * m * n := by
  rw [hlatP_form]
  have h : p / 2 = k := by omega
  rw [h]

/-- The generator `g = γ/2 = 1 ∈ ½ℤγ`. -/
def gHalf (p : ℕ) : (hlatP p).carrier := (1 : ℤ)

/-- `⟨g,g⟩ = p/2` (natural division). -/
theorem hlatP_form_gHalf (p : ℕ) :
    (hlatP p).form (gHalf p) (gHalf p) = ((p / 2 : ℕ) : ℤ) := by
  rw [gHalf, hlatP_form]; ring

/-- **The defining hypothesis of `Examples.DoubletGenerators`, realized concretely.**
`2⟨g,g⟩ = p`.  This is *syntactically* `Doublet.hgg` with `L := hlatP p` and `g := gHalf p`, so
every `Doublet.*` lemma applies to the half lattice by feeding it this term. -/
theorem hgg_hlatP (p k : ℕ) (hp2 : 2 * k = p) :
    2 * (hlatP p).form (gHalf p) (gHalf p) = (p : ℤ) := by
  rw [hlatP_form_gHalf]
  have h : p / 2 = k := by omega
  rw [h, ← hp2]
  push_cast
  ring

/-- The half lattice has rank `1`. -/
theorem rank_hlatP (p : ℕ) : rank (hlatP p) = 1 := Module.finrank_self ℤ

/-! ### Unification test against `Examples.DoubletGenerators`

The following are *not* new mathematics: each is a `Doublet.*` lemma applied to `hlatP p` with
`hgg := hgg_hlatP`.  They compile only if the hypothesis shapes match literally, so they are the
machine-checked statement that this lattice is the intended ambient. -/

/-- `⟨γ,g⟩ = ⟨2g,g⟩ = p` on the concrete half lattice (integrality of the screening mode index). -/
theorem hlatP_form_gamma_gHalf (p k : ℕ) (hp2 : 2 * k = p) :
    (hlatP p).form (gHalf p + gHalf p) (gHalf p) = (p : ℤ) :=
  Doublet.form_gamma_g (hlatP p) (gHalf p) p (hgg_hlatP p k hp2)

/-- `⟨γ,γ⟩ = 2p` on the concrete half lattice — the triplet normalization. -/
theorem hlatP_form_gamma_gamma (p k : ℕ) (hp2 : 2 * k = p) :
    (hlatP p).form (gHalf p + gHalf p) (gHalf p + gHalf p) = 2 * (p : ℤ) :=
  Doublet.form_gamma_gamma (hlatP p) (gHalf p) p (hgg_hlatP p k hp2)

/-- `γ = 2g ≠ 0` on the concrete half lattice, for `p ≥ 1`. -/
theorem hlatP_gamma_ne_zero (p k : ℕ) (hp2 : 2 * k = p) (hp : 1 ≤ p) :
    (gHalf p + gHalf p) ≠ 0 :=
  Doublet.gamma_ne_zero (hlatP p) (gHalf p) p hp (hgg_hlatP p k hp2)

/-- `⟨g,g⟩ = p/2` as a complex number, on the concrete half lattice. -/
theorem hlatP_form_gHalf_cast (p k : ℕ) (hp2 : 2 * k = p) :
    (((hlatP p).form (gHalf p) (gHalf p) : ℤ) : ℂ) = (p : ℂ) / 2 :=
  Doublet.form_gg_cast (hlatP p) (gHalf p) p (hgg_hlatP p k hp2)

/-! ## §2  (b)  Positive-definiteness (always) and evenness (iff `4 ∣ p`) -/

/-- **The half lattice is positive definite** as soon as `2 ≤ p`: `⟨m,m⟩ = (p/2)m² > 0` for
`m ≠ 0`.  Since `p` is forced to be even (`Doublet.p_even`), `2 ≤ p` is exactly `0 < p`; the
hypothesis is stated as `2 ≤ p` so that it is checkable without the evenness witness.
(At `p = 0` — and at the degenerate odd `p = 1` — the form is identically zero.) -/
theorem hlatP_posDef (p : ℕ) (hp : 2 ≤ p) : (hlatP p).PosDef := by
  have h : ∀ v : ℤ, v ≠ 0 → 0 < (hlatP p).form v v := by
    intro v hv
    rw [hlatP_form]
    have hp' : (1 : ℤ) ≤ ((p / 2 : ℕ) : ℤ) := by
      have : 1 ≤ p / 2 := by omega
      exact_mod_cast this
    have h2 : 0 < v * v := mul_self_pos.mpr hv
    have he : ((p / 2 : ℕ) : ℤ) * v * v = ((p / 2 : ℕ) : ℤ) * (v * v) := by ring
    rw [he]
    exact mul_pos (by omega) h2
  exact h

/-- Same statement, phrased with the exactness witness: positive definite for `1 ≤ k`. -/
theorem hlatP_posDef_k (p k : ℕ) (hp2 : 2 * k = p) (hk : 1 ≤ k) : (hlatP p).PosDef :=
  hlatP_posDef p (by omega)

/-- **Evenness, `⇐`**: if `4 ∣ p` then `⟨m,m⟩ = (p/2)m²` is always even, i.e. the half lattice is
an *even* lattice and the ambient VOA is honestly **bosonic**. -/
theorem hlatP_even_of_four_dvd (p : ℕ) (h4 : 4 ∣ p) : (hlatP p).Even := by
  obtain ⟨j, rfl⟩ := h4
  have hdiv : 4 * j / 2 = 2 * j := by omega
  have h : ∀ v : ℤ, (2 : ℤ) ∣ (hlatP (4 * j)).form v v := by
    intro v
    refine ⟨(j : ℤ) * v * v, ?_⟩
    rw [hlatP_form, hdiv]
    push_cast
    ring
  exact h

/-- **Evenness, `⇒`**: if `p` is even but `4 ∤ p` (i.e. `p ≡ 2 mod 4`) then the half lattice is
**odd** — `⟨g,g⟩ = p/2` is an odd integer — so the ambient must be a *super* vertex algebra. -/
theorem hlatP_not_even_of_not_four_dvd (p k : ℕ) (hp2 : 2 * k = p) (h4 : ¬ (4 ∣ p)) :
    ¬ (hlatP p).Even := by
  intro hEven
  have h := hEven (gHalf p)
  rw [hlatP_form_gHalf] at h
  have hk : p / 2 = k := by omega
  rw [hk] at h
  have h' : (2 : ℤ) ∣ (k : ℤ) := h
  have h'' : 2 ∣ k := by exact_mod_cast h'
  exact h4 (by omega)

/-- **The mod-4 dichotomy for the half lattice**: `½ℤγ` is an **even** lattice iff `4 ∣ p`.
This is `Doublet.form_gg_even_iff` made concrete.  It is *not* assumed anywhere: the two cases
`4 ∣ p` (bosonic ambient) and `p ≡ 2 mod 4` (super ambient) are both live. -/
theorem hlatP_even_iff (p k : ℕ) (hp2 : 2 * k = p) : (hlatP p).Even ↔ 4 ∣ p := by
  constructor
  · intro hEven
    by_contra h4
    exact hlatP_not_even_of_not_four_dvd p k hp2 h4 hEven
  · exact hlatP_even_of_four_dvd p

/-- The abstract `Doublet.form_gg_even_iff` instantiated at the concrete half lattice: the two
formulations agree. -/
theorem hlatP_form_gHalf_even_iff (p k : ℕ) (hp2 : 2 * k = p) :
    2 ∣ (hlatP p).form (gHalf p) (gHalf p) ↔ 4 ∣ p :=
  Doublet.form_gg_even_iff (hlatP p) (gHalf p) p (hgg_hlatP p k hp2)

/-! ## §3  (c)  The ℚ-valued quadratic refinement `q(m) = (p m²)/4 − ((p−1)m)/2`

The doublet deformed weight of `e^{mg}` is `½⟨mg,mg⟩ − ⟨λ, mg⟩` with `⟨g,g⟩ = p/2` and
`⟨λ,g⟩ = (p−1)/2` (that is `Doublet.hlam`), i.e.

  `q(m) = (p m²)/4 − ((p−1) m)/2`.

It is genuinely ℚ-valued: at `m = 1` it is `(2−p)/4`, a quarter-integer in general. -/

/-- **The deformed weight** `q(m) = (p m²)/4 − ((p−1)m)/2` of `e^{mg}` on the half lattice. -/
noncomputable def qH (p : ℕ) (m : ℤ) : ℚ :=
  ((p : ℚ) * (m : ℚ) ^ 2) / 4 - (((p : ℚ) - 1) * (m : ℚ)) / 2

/-- The **integral numerator** of the deformed weight: `q(m) = qZH k m / 2` when `p = 2k`. -/
def qZH (k : ℕ) (m : ℤ) : ℤ := (k : ℤ) * m ^ 2 - (2 * (k : ℤ) - 1) * m

/-- `q(m) = qZH k m / 2`: the deformed weight is a **half**-integer multiple, never worse. -/
theorem qH_eq_qZH (p k : ℕ) (hp2 : 2 * k = p) (m : ℤ) :
    qH p m = ((qZH k m : ℤ) : ℚ) / 2 := by
  have hpk : (p : ℚ) = 2 * (k : ℚ) := by
    rw [← hp2]; push_cast; ring
  simp only [qH, qZH, hpk]
  push_cast
  ring

/-- **The polarization axiom**: `q(a+b) − q a − q b = ⟨a,b⟩`.  This is where `p` even is needed —
the left side is `(p/2)·a·b` in ℚ, the right side is `(p/2 : ℕ)·a·b`. -/
theorem qH_polarization (p k : ℕ) (hp2 : 2 * k = p) (a b : ℤ) :
    qH p (a + b) - qH p a - qH p b = (((hlatP p).form a b : ℤ) : ℚ) := by
  have hpk : (p : ℚ) = 2 * (k : ℚ) := by
    rw [← hp2]; push_cast; ring
  rw [hlatP_form_k p k hp2]
  simp only [qH, hpk]
  push_cast
  ring

/-- **The ℚ-valued quadratic refinement of the half lattice** carrying the doublet background
charge.  Needs `hp2 : 2 * k = p` (equivalently: `p` even), nothing more. -/
noncomputable def qrH (p k : ℕ) (hp2 : 2 * k = p) : QuadRefine (hlatP p) where
  q := qH p
  polarization := qH_polarization p k hp2

@[simp] theorem qrH_q (p k : ℕ) (hp2 : 2 * k = p) (m : ℤ) :
    (qrH p k hp2).q m = qH p m := rfl

/-! ## §4  (d)  The two doublet weights `q(1) = (2−p)/4` and `q(−1) = (3p−2)/4` -/

@[simp] theorem qH_zero (p : ℕ) : qH p 0 = 0 := by
  simp only [qH]; push_cast; ring

/-- **`wt(e^{+g}) = (2−p)/4`** — the weight appearing in `Doublet.LBG_zero_eG`. -/
@[simp] theorem qH_one (p : ℕ) : qH p 1 = (2 - (p : ℚ)) / 4 := by
  simp only [qH]; push_cast; ring

/-- **`wt(e^{−g}) = (3p−2)/4`** — the weight of `a⁻` in `Doublet.LBG_zero_aMinus`. -/
@[simp] theorem qH_neg_one (p : ℕ) : qH p (-1) = (3 * (p : ℚ) - 2) / 4 := by
  simp only [qH]; push_cast; ring

/-! ## §5  (e)  `PosQuad` **FAILS** for `p > 2`

This negative result is the whole reason the doublet ambient cannot be handled by the `PosQuad`
route of `Examples.LatticeQuadRefine` (which would give `𝒱_h = 0` for `Re h < 0` and
`𝒱₀ = ℂ𝟙`) and must instead be routed through `SuperNearVOA.BoundedBelow`. -/

/-- `q(1) < 0` for `p > 2`: the state `e^{+g}` has strictly **negative** conformal weight. -/
theorem qH_one_neg (p : ℕ) (hp : 2 < p) : qH p 1 < 0 := by
  rw [qH_one]
  have : (2 : ℚ) < (p : ℚ) := by exact_mod_cast hp
  linarith

/-- **`PosQuad` fails on the doublet half lattice for every `p > 2`.**  Witness: `q(1) < 0`.
(At `p = 2` the weight `q(1) = 0` also violates strict positivity at `m = 1 ≠ 0`; see
`not_posQuad_qrH_two`.) -/
theorem not_posQuad_qrH (p k : ℕ) (hp2 : 2 * k = p) (hp : 2 < p) :
    ¬ PosQuad (hlatP p) (qrH p k hp2) := by
  intro hpos
  have h1 : ((1 : ℤ) : (hlatP p).carrier) ≠ 0 := by
    show (1 : ℤ) ≠ 0
    norm_num
  have := hpos ((1 : ℤ) : (hlatP p).carrier) h1
  rw [qrH_q] at this
  exact absurd this (not_lt.mpr (le_of_lt (qH_one_neg p hp)))

/-- `PosQuad` also fails at `p = 2`, where `q(1) = 0` (not `> 0`).  So `PosQuad` holds for **no**
`p ≥ 2` on the half lattice; combined with `not_posQuad_qrH` this covers every relevant `p`. -/
theorem not_posQuad_qrH_two (k : ℕ) (hp2 : 2 * k = 2) :
    ¬ PosQuad (hlatP 2) (qrH 2 k hp2) := by
  intro hpos
  have h1 : ((1 : ℤ) : (hlatP 2).carrier) ≠ 0 := by
    show (1 : ℤ) ≠ 0
    norm_num
  have h := hpos ((1 : ℤ) : (hlatP 2).carrier) h1
  rw [qrH_q, qH_one] at h
  norm_num at h

/-! ## §6  (f)  The refinement **is** bounded below, and `QFinite`

`PosQuad` fails, but the deformed weight is still a positive-definite quadratic in `m`, hence
bounded below and proper.  The minimum over `ℤ` is attained at `m = 1` and equals `(1−k)/2`,
i.e. `(2−p)/4` — exactly `wt(e^{+g})`. -/

/-- The **exact minimum**: `qZH k m ≥ 1 − k` for all `m ∈ ℤ` (`k ≥ 1`), with equality at `m = 1`.
Key factorization: `qZH k m − (1 − k) = (m − 1)(k m − k + 1)`. -/
theorem qZH_ge (k : ℕ) (hk : 1 ≤ k) (m : ℤ) : (1 : ℤ) - (k : ℤ) ≤ qZH k m := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hfac : qZH k m - ((1 : ℤ) - (k : ℤ)) = (m - 1) * ((k : ℤ) * m - (k : ℤ) + 1) := by
    simp only [qZH]; ring
  have hnn : 0 ≤ (m - 1) * ((k : ℤ) * m - (k : ℤ) + 1) := by
    rcases le_or_gt 1 m with h | h
    · refine mul_nonneg (by omega) ?_
      nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ (k : ℤ)) (by omega : (0 : ℤ) ≤ m - 1)]
    · have hm0 : m ≤ 0 := by omega
      have h1 : m - 1 ≤ 0 := by omega
      have h2 : (k : ℤ) * m - (k : ℤ) + 1 ≤ 0 := by
        nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ (k : ℤ)) (by omega : (0 : ℤ) ≤ -m)]
      nlinarith
  linarith

/-- `qZH k 1 = 1 − k`: the bound of `qZH_ge` is **attained**. -/
@[simp] theorem qZH_one (k : ℕ) : qZH k 1 = 1 - (k : ℤ) := by
  simp only [qZH]; ring

/-- **The deformed weight is bounded below** by `(1−k)/2 = (2−p)/4` for every `m`. -/
theorem qH_ge (p k : ℕ) (hp2 : 2 * k = p) (hk : 1 ≤ k) (m : ℤ) :
    ((1 : ℚ) - (k : ℚ)) / 2 ≤ qH p m := by
  rw [qH_eq_qZH p k hp2]
  have h : ((1 : ℤ) - (k : ℤ) : ℤ) ≤ qZH k m := qZH_ge k hk m
  have h' : (((1 : ℤ) - (k : ℤ) : ℤ) : ℚ) ≤ ((qZH k m : ℤ) : ℚ) := by exact_mod_cast h
  push_cast at h'
  linarith

/-- **(f)  `q` is bounded below** — the existential form used by `SuperNearVOA.BoundedBelow`. -/
theorem qH_bddBelow (p k : ℕ) (hp2 : 2 * k = p) (hk : 1 ≤ k) :
    ∃ B : ℚ, ∀ m : ℤ, B ≤ qH p m :=
  ⟨((1 : ℚ) - (k : ℚ)) / 2, qH_ge p k hp2 hk⟩

/-- The bound in the `QuadRefine` packaging. -/
theorem qrH_bddBelow (p k : ℕ) (hp2 : 2 * k = p) (hk : 1 ≤ k) :
    ∃ B : ℚ, ∀ α : (hlatP p).carrier, B ≤ (qrH p k hp2).q α :=
  ⟨((1 : ℚ) - (k : ℚ)) / 2, fun m => qH_ge p k hp2 hk m⟩

/-- **Properness**: `|m| ≤ qZH k m + k`.  For `m ≥ 0` this is `k(m−1)² ≥ 0`; for `m < 0` it is
`(k−1)(m−1)² + (m²+1) ≥ 0`. -/
theorem abs_le_qZH (k : ℕ) (hk : 1 ≤ k) (m : ℤ) : |m| ≤ qZH k m + (k : ℤ) := by
  have hk' : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  rcases le_or_gt 0 m with h | h
  · rw [abs_of_nonneg h]
    simp only [qZH]
    nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ (k : ℤ)) (sq_nonneg (m - 1))]
  · rw [abs_of_neg h]
    simp only [qZH]
    nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ (k : ℤ) - 1) (sq_nonneg (m - 1)), sq_nonneg m]

/-- **(f)  `QFinite`** for the doublet refinement: only finitely many charges lie below any bound,
because `q` grows quadratically.  Needs only `1 ≤ k` (i.e. `2 ≤ p`). -/
theorem qFinite_qrH (p k : ℕ) (hp2 : 2 * k = p) (hk : 1 ≤ k) :
    QFinite (hlatP p) (qrH p k hp2) := by
  have h : ∀ N : ℚ, {m : ℤ | qH p m ≤ N}.Finite := by
    intro N
    refine Set.Finite.subset (Set.finite_Icc (-(⌈2 * N⌉ + (k : ℤ))) (⌈2 * N⌉ + (k : ℤ))) ?_
    intro m hm
    have hmq : qH p m ≤ N := hm
    rw [qH_eq_qZH p k hp2] at hmq
    have h1 : ((qZH k m : ℤ) : ℚ) ≤ 2 * N := by linarith
    have h2 : ((qZH k m : ℤ) : ℚ) ≤ ((⌈2 * N⌉ : ℤ) : ℚ) := le_trans h1 (Int.le_ceil (2 * N))
    have h3 : qZH k m ≤ ⌈2 * N⌉ := by exact_mod_cast h2
    have h4 : |m| ≤ ⌈2 * N⌉ + (k : ℤ) := le_trans (abs_le_qZH k hk m) (by omega)
    exact Set.mem_Icc.mpr (abs_le.mp h4)
  exact h

/-! ## §7  (g)  The mod-4 dichotomy for the doublet weight `(3p−2)/4`

`wt(a⁻) = wt(e^{−g}) = q(−1) = (3p−2)/4`.  It is an **integer** exactly when `p ≡ 2 mod 4` — and
by `hlatP_even_iff` that is exactly when the half lattice is **odd**, so the ambient is a genuine
*super* vertex algebra.  Complementarily it is a **half-integer** exactly when `4 ∣ p`, i.e.
exactly when the half lattice is **even** and the ambient is bosonic.  Super and half-integer
weight are therefore complementary and never occur together. -/

/-- The arithmetic core: `4 ∣ 3p − 2` iff `p ≡ 2 mod 4`. -/
theorem four_dvd_three_mul_sub_two_iff (p : ℕ) :
    (4 : ℤ) ∣ (3 * (p : ℤ) - 2) ↔ p % 4 = 2 := by
  omega

/-- **`q(−1) = (3p−2)/4` is an integer iff `p ≡ 2 mod 4`.**  By `hlatP_even_iff` this is exactly
the case in which the half lattice is **odd** (super ambient). -/
theorem qH_neg_one_int_iff (p : ℕ) :
    (∃ n : ℤ, qH p (-1) = (n : ℚ)) ↔ p % 4 = 2 := by
  rw [← four_dvd_three_mul_sub_two_iff]
  constructor
  · rintro ⟨n, hn⟩
    rw [qH_neg_one] at hn
    refine ⟨n, ?_⟩
    have h : (3 * (p : ℚ) - 2) = 4 * (n : ℚ) := by
      field_simp at hn
      linarith
    have h' : ((3 * (p : ℤ) - 2 : ℤ) : ℚ) = ((4 * n : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast h'
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [qH_neg_one]
    have h : (3 * (p : ℚ) - 2) = 4 * (n : ℚ) := by
      have := congrArg (fun z : ℤ => (z : ℚ)) hn
      push_cast at this
      linarith
    rw [h]
    ring

/-- **`q(−1) = (3p−2)/4` is a half-integer (in `ℤ + ½`) iff `4 ∣ p`.**  By `hlatP_even_iff` this
is exactly the case in which the half lattice is **even** (bosonic ambient). -/
theorem qH_neg_one_halfInt_iff (p : ℕ) :
    (∃ n : ℤ, qH p (-1) = (n : ℚ) + 1 / 2) ↔ 4 ∣ p := by
  constructor
  · rintro ⟨n, hn⟩
    rw [qH_neg_one] at hn
    have h : (3 * (p : ℚ) - 2) = 4 * (n : ℚ) + 2 := by
      field_simp at hn
      linarith
    have h' : ((3 * (p : ℤ) - 2 : ℤ) : ℚ) = ((4 * n + 2 : ℤ) : ℚ) := by push_cast; linarith
    have h'' : (3 * (p : ℤ) - 2 : ℤ) = (4 * n + 2 : ℤ) := by exact_mod_cast h'
    omega
  · rintro ⟨j, rfl⟩
    refine ⟨3 * (j : ℤ) - 1, ?_⟩
    rw [qH_neg_one]
    push_cast
    ring

/-- The two branches, packaged: the half lattice is even **iff** the doublet weight is a
half-integer, and (for even `p`) odd **iff** the doublet weight is an integer. -/
theorem hlatP_even_iff_halfInt (p k : ℕ) (hp2 : 2 * k = p) :
    (hlatP p).Even ↔ (∃ n : ℤ, qH p (-1) = (n : ℚ) + 1 / 2) := by
  rw [hlatP_even_iff p k hp2, qH_neg_one_halfInt_iff]

/-- For even `p`: the half lattice is **odd** (hence the ambient is a super vertex algebra) exactly
when the doublet weight `(3p−2)/4` is an **integer**. -/
theorem hlatP_not_even_iff_int (p k : ℕ) (hp2 : 2 * k = p) :
    ¬ (hlatP p).Even ↔ (∃ n : ℤ, qH p (-1) = (n : ℚ)) := by
  rw [hlatP_even_iff p k hp2, qH_neg_one_int_iff]
  omega

/-! ## §7b  Compatibility with the triplet lattice `Triplet.latP p`

`hlatP p` is the **index-two overlattice** of the triplet lattice: `γ = 2g` generates a copy of
`Triplet.latP p` inside it, and the doublet weight restricts to the triplet weight there.  These
two lemmas are the precise statement that nothing has been renormalized along the way. -/

/-- **Doubling `m ↦ 2m` is an isometry `Triplet.latP p ↪ hlatP p`**: `⟨2m,2n⟩_half = ⟨m,n⟩_triplet`
(written additively, `γ = g + g`, as in `Examples.DoubletGenerators`).  So `γ = 2g` generates a
copy of `ℤα`, `⟨α,α⟩ = 2p`, and `hlatP p` has index two over it. -/
theorem hlatP_doubling_isometry (p k : ℕ) (hp2 : 2 * k = p) (m n : ℤ) :
    (hlatP p).form (m + m) (n + n) = (Triplet.latP p).form m n := by
  rw [hlatP_form_k p k hp2, Triplet.latP_form, ← hp2]
  push_cast
  ring

/-- The isometry on the generators: `⟨γ,γ⟩_half = ⟨α,α⟩_triplet = 2p`. -/
theorem hlatP_doubling_isometry_gen (p k : ℕ) (hp2 : 2 * k = p) :
    (hlatP p).form (gHalf p + gHalf p) (gHalf p + gHalf p)
      = (Triplet.latP p).form (Triplet.alphaP p) (Triplet.alphaP p) :=
  hlatP_doubling_isometry p k hp2 1 1

/-- **The doublet weight restricts to the triplet weight**: `qH p (2m) = Triplet.qZP p m`.
In particular the doublet weights on the *sublattice* `ℤγ` are the honest integers `p m² − (p−1)m`;
all the quarter-integrality lives in the odd coset `g + ℤγ`. -/
theorem qH_two_mul (p : ℕ) (m : ℤ) : qH p (2 * m) = ((Triplet.qZP p m : ℤ) : ℚ) := by
  simp only [qH, Triplet.qZP]
  push_cast
  ring

/-- `PosQuad` **does** hold on the sublattice generated by `γ`: the failure of positivity is
entirely a phenomenon of the coset `g + ℤγ` (where `q(1) = (2−p)/4 < 0`). -/
theorem qH_two_mul_pos (p : ℕ) (hp : 1 ≤ p) {m : ℤ} (hm : m ≠ 0) : 0 < qH p (2 * m) := by
  rw [qH_two_mul]
  exact_mod_cast Triplet.qZP_pos p hp hm

/-! ## §8  Sanity checks at small `p` -/

/-- At `p = 2` the half lattice is `ℤ` with `⟨m,n⟩ = mn` (the odd unimodular line): `⟨g,g⟩ = 1`. -/
theorem hlatP_two_form (m n : ℤ) : (hlatP 2).form m n = m * n := by
  rw [hlatP_form_k 2 1 (by norm_num)]
  push_cast
  ring

/-- At `p = 2` the half lattice is **not** even (`4 ∤ 2`), so the ambient is a super vertex algebra
— consistent with `wt(a⁻) = (3·2−2)/4 = 1 ∈ ℤ`. -/
theorem hlatP_two_not_even : ¬ (hlatP 2).Even :=
  hlatP_not_even_of_not_four_dvd 2 1 (by norm_num) (by omega)

/-- At `p = 4` the half lattice is `√2ℤ` (`⟨m,n⟩ = 2mn`), which **is** even, so the ambient is
bosonic — consistent with `wt(a⁻) = (3·4−2)/4 = 5/2 ∈ ℤ + ½`. -/
theorem hlatP_four_even : (hlatP 4).Even :=
  hlatP_even_of_four_dvd 4 (by norm_num)

end VOA.LatGen.HalfLat
