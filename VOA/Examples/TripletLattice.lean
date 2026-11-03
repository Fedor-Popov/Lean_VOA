/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.LatticeQuadRefine
import VOA.Examples.LatticeBackgroundChargeA
import VOA.Examples.LatticeCharge

/-!
# The deformed rank-one lattice VOA `V_{L_p}` — the ambient of the `(1,p)` triplet

The rank-one even positive-definite lattice `L_p = ℤα` with `⟨α,α⟩ = 2p`, the Feigin–Fuchs
background charge `λ_p = ((p−1)/(2p))·α`, the quadratic refinement `q_p` it defines, and the
resulting **`VertexOperatorAlgebra` instance** on `V_{L_p}` with central charge `1 − 6(p−1)²/p`.

## Main definitions

* `latP p` — the lattice `L_p`: carrier `ℤ`, form `⟨m,n⟩ = 2p·mn` (generalizing `sqrt2Lattice`,
  which is the case `p = 1`, cf. `latP_one_form`).  `latP_even`, `latP_posDef` (for `p ≥ 1`),
  `rank_latP : rank (latP p) = 1`, `halfNorm_latP : ½⟨m,m⟩ = p m²`.
* `cP p = (p−1)/(2p)`, `lamP p = cP p · α` — the background charge as a frame-coordinate vector
  in the sense of `LatGen.BgA.latBg`.  `bgPair_lamP : ⟨λ_p, mα⟩ = (p−1)m`,
  `bgPair_lamP_alpha : ⟨λ_p, α⟩ = p−1`, `bgForm_lamP : ⟨λ_p,λ_p⟩ = (p−1)²/(2p)`.
* `qZP p m = p m² − (p−1)m` — the deformed weight of `e^{mα}`.  It is an **integer**, and
  `qZP_eq_halfNorm_sub_bgPair` identifies it with `½⟨β,β⟩ − ⟨λ_p,β⟩`.
* `qrP p : QuadRefine (latP p)` — the ℚ-valued quadratic refinement built from `qZP`.
* `wtZP`, `gradTrip p k` — the ℤ-indexed deformed grading (`gradTrip_eq` identifies it with the
  ℂ-indexed `gradingLatGenQ` at the integer points, so all the `QuadRefine` theory applies).
* `tripletLatticeVOA p hp : VertexOperatorAlgebra (LatModuleGen (latP p))` — **all 19 fields**.

## Main results

* `posQuad_qrP` — `PosQuad L_p q_p`: `q_p(m) = m(pm − p + 1) > 0` for `m ≠ 0`, `p ≥ 1`.
* `qFinite_qrP` — `QFinite L_p q_p`, via the bound `|m| ≤ q_p(m)` (`abs_le_qZP`).
* `centralCharge_latP` — `rank L_p − 12⟨λ_p,λ_p⟩ = 1 − 6(p−1)²/p`; at `p = 2` this is `−2`
  (`tripletLatticeVOA_centralCharge_two`).
* `LBg_weight_alpha` / `LBg_weight_neg_alpha` — `wt(e^α) = 1`, `wt(e^{−α}) = 2p−1`, and the
  grading forms `latChargeGen_alpha_mem_grade_one`, `latChargeGen_neg_alpha_mem_grade`,
  `latChargeGen_mem_gradTrip`.
* `gradTrip_grading_mode` — **VA1 for the deformed grading**.  The deformed weight differs from
  the undeformed one by `−⟨λ_p, charge⟩`, a *linear* function of the charge, so the correction
  cancels in `k + ℓ − n − 1`; the proof combines the undeformed `YfullGen_grading_mode` with the
  charge additivity `YfullGen_shiftsCharge` of `Examples.LatticeCharge`, glued by the new
  intersection lemma `mem_bigradα_of_grading_of_charge`
  (`gradingLatGen K ⊓ chargeSec γ ≤ bigradα (K − ½⟨γ,γ⟩, γ)`).
* `L0_gradTrip` — VOA2 for `ω_{λ_p}`; `LBg_zero_bigradα` is the bigraded computation
  (`L₀^λ = L₀ − λ(0)`, eigenvalue `(w + ½⟨β,β⟩) − ⟨λ_p,β⟩ = k`).
* `translation_gradTrip` — VOA3, **inherited verbatim** from the undeformed lattice VOA, because
  the deformation `Lₙ ↦ Lₙ − (n+1)λ(n)` vanishes at `n = −1` (`mode_omegaBg_zero_eq`).
* `virasoro_gradTrip` — VOA1, from `BgA.LBg_virasoro` and `BgA.mode_YfullGen_omegaBg`.
* `omegaBg_mem_bigradα` — `ω_λ ∈ bigradα (2,0)` for any background charge `λ` (the `conformal_mem`
  field); the deformed grade of `ω_{λ_p}` is `2` because its charge is `0`.
* `tripletLatticeVOA_L` — the Virasoro modes of the instance *are* `LBg λ_p n`.

Which fields change relative to `latticeVOAGen`: the conformal/grading half (`grading`,
`isInternal`, `finrank`, `vacuum_mem`, `grading_mode`, `conformalVector`, `conformal_mem`,
`centralCharge`, `virasoro`, `L0_grading`, `translation`, `vacuum_grade`, `positivity`).  `Y`,
`vacuum`, `vacuum_Y`, `creation`, `locality`, `regularity` are taken over unchanged.

All `sorry`-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

set_option linter.style.longLine false

namespace VOA.LatGen.Triplet

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN
open VOA.LatGen

/-! ## §1  (a)  The rank-one lattice `L_p = ℤα`, `⟨α,α⟩ = 2p` -/

/-- **The rank-one lattice `L_p`**: the ℤ-module `ℤ` with the form `⟨m,n⟩ = 2p·mn`.  For `p = 1`
this is `sqrt2Lattice` (the `A₁` lattice); `p` general is the ambient of the `(1,p)` triplet. -/
noncomputable def latP (p : ℕ) : IntegralLattice where
  carrier := ℤ
  form := ((2 * p : ℕ) : ℤ) • LinearMap.mul ℤ ℤ
  isSymm := by
    rw [LinearMap.BilinForm.isSymm_def]
    intro v w
    simp only [LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
    ring

/-- The Gram form of `L_p`: `⟨m,n⟩ = 2p·mn`. -/
theorem latP_form (p : ℕ) (m n : ℤ) : (latP p).form m n = 2 * (p : ℤ) * m * n := by
  show (((2 * p : ℕ) : ℤ) • LinearMap.mul ℤ ℤ) m n = _
  simp only [LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
  push_cast
  ring

/-- The generator `α = 1 ∈ L_p`. -/
def alphaP (p : ℕ) : (latP p).carrier := (1 : ℤ)

/-- `⟨α,α⟩ = 2p`. -/
theorem latP_form_alpha (p : ℕ) : (latP p).form (alphaP p) (alphaP p) = 2 * (p : ℤ) := by
  rw [alphaP, latP_form]; ring

/-- **`L_p` is even**: `⟨m,m⟩ = 2·(p m²)`. -/
theorem latP_even (p : ℕ) : (latP p).Even := by
  have h : ∀ v : ℤ, (2 : ℤ) ∣ (latP p).form v v := fun v =>
    ⟨(p : ℤ) * v * v, by rw [latP_form]; ring⟩
  exact h

/-- **`L_p` is positive definite** for `p ≥ 1`: `⟨m,m⟩ = 2p m² > 0` for `m ≠ 0`. -/
theorem latP_posDef (p : ℕ) (hp : 1 ≤ p) : (latP p).PosDef := by
  have h : ∀ v : ℤ, v ≠ 0 → 0 < (latP p).form v v := by
    intro v hv
    rw [latP_form]
    have hp' : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
    have h2 : 0 < v * v := mul_self_pos.mpr hv
    have he : 2 * (p : ℤ) * v * v = (2 * (p : ℤ)) * (v * v) := by ring
    rw [he]
    exact mul_pos (by omega) h2
  exact h

/-- `L_p` has rank `1`. -/
theorem rank_latP (p : ℕ) : rank (latP p) = 1 := Module.finrank_self ℤ

/-- `½⟨m,m⟩ = p m²`. -/
theorem halfNorm_latP (p : ℕ) (m : ℤ) : halfNorm (latP p) m = (p : ℤ) * m ^ 2 := by
  rw [halfNorm, latP_form,
    show 2 * (p : ℤ) * m * m = 2 * ((p : ℤ) * m ^ 2) from by ring,
    Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]

/-! ## §2  (b)  The background charge `λ_p = ((p−1)/(2p))·α` -/

/-- The background-charge coefficient `c_p = (p−1)/(2p)`. -/
noncomputable def cP (p : ℕ) : ℂ := ((p : ℂ) - 1) / (2 * (p : ℂ))

/-- **The background charge `λ_p = c_p·α`**, as a frame-coordinate vector in the sense of
`LatGen.BgA.latBg`. -/
noncomputable def lamP (p : ℕ) : Fin (rank (latP p)) → ℂ :=
  BgA.latBg (latP p) (cP p) (alphaP p)

/-- **The pairing of the background charge with a lattice vector**: `⟨λ_p, mα⟩ = (p−1)m`. -/
theorem bgPair_lamP (p : ℕ) (hp : 1 ≤ p) (m : ℤ) :
    BgA.bgPair (latP p) (lamP p) m = ((p : ℂ) - 1) * (m : ℂ) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [lamP, BgA.bgPair_latBg (latP p) (latP_posDef p hp), alphaP, latP_form, cP]
  push_cast
  field_simp

/-- **`⟨λ_p, α⟩ = p − 1`** — the defining normalization of the triplet background charge. -/
theorem bgPair_lamP_alpha (p : ℕ) (hp : 1 ≤ p) :
    BgA.bgPair (latP p) (lamP p) (alphaP p) = (p : ℂ) - 1 := by
  rw [alphaP, bgPair_lamP p hp]
  push_cast
  ring

/-- **`⟨λ_p, λ_p⟩ = (p−1)²/(2p)`** — the datum entering the central charge. -/
theorem bgForm_lamP (p : ℕ) (hp : 1 ≤ p) :
    BgA.bgForm (latP p) (lamP p) (lamP p) = ((p : ℂ) - 1) ^ 2 / (2 * (p : ℂ)) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [lamP, BgA.bgForm_latBg (latP p) (latP_posDef p hp), latP_form_alpha, cP]
  push_cast
  field_simp

/-- **The triplet central charge**: `rank L_p − 12⟨λ_p,λ_p⟩ = 1 − 6(p−1)²/p`
(`p = 2` gives `c = −2`, the symplectic-fermion value). -/
theorem centralCharge_latP (p : ℕ) (hp : 1 ≤ p) :
    ((rank (latP p) : ℂ)) - 12 * BgA.bgForm (latP p) (lamP p) (lamP p)
      = 1 - 6 * ((p : ℂ) - 1) ^ 2 / (p : ℂ) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [bgForm_lamP p hp, rank_latP]
  push_cast
  field_simp
  ring

/-! ## §3  (c)  The quadratic refinement `q_p(β) = ½⟨β,β⟩ − ⟨λ_p,β⟩` -/

/-- **The deformed weight of the charged vacuum `e^{mα}`**: `q_p(m) = p m² − (p−1)m`.
It is an *integer* (although `QuadRefine` only asks for a rational). -/
def qZP (p : ℕ) (m : ℤ) : ℤ := (p : ℤ) * m ^ 2 - ((p : ℤ) - 1) * m

/-- **(c)  The quadratic refinement of the `L_p`-grading defined by the background charge.**
The polarization axiom holds because `halfNorm` polarizes to the form while `⟨λ_p, ·⟩` is
linear, so the linear part cancels — this is `QuadRefine.bgCharge_add` read backwards. -/
theorem qZP_polarization (p : ℕ) (a b : ℤ) :
    ((qZP p (a + b) : ℤ) : ℚ) - ((qZP p a : ℤ) : ℚ) - ((qZP p b : ℤ) : ℚ)
      = (((latP p).form a b : ℤ) : ℚ) := by
  rw [latP_form]
  simp only [qZP]
  push_cast
  ring

def qrP (p : ℕ) : QuadRefine (latP p) where
  q := fun m => ((qZP p m : ℤ) : ℚ)
  polarization := qZP_polarization p

@[simp] theorem qrP_q (p : ℕ) (m : ℤ) : (qrP p).q m = ((qZP p m : ℤ) : ℚ) := rfl

/-- `q_p(β) = ½⟨β,β⟩ − ⟨λ_p,β⟩`: the refinement really *is* the background-charge deformation
of the standard weight.  (Stated in ℂ, where `bgPair` lives.) -/
theorem qZP_eq_halfNorm_sub_bgPair (p : ℕ) (hp : 1 ≤ p) (m : ℤ) :
    ((qZP p m : ℤ) : ℂ)
      = (1 / 2 : ℂ) * (((latP p).form m m : ℤ) : ℂ) - BgA.bgPair (latP p) (lamP p) m := by
  rw [bgPair_lamP p hp, latP_form, qZP]
  push_cast
  ring

/-- `q_p(β) = halfNorm β − (p−1)β` on the nose, over `ℤ`. -/
theorem qZP_eq_halfNorm_sub (p : ℕ) (m : ℤ) :
    qZP p m = halfNorm (latP p) m - ((p : ℤ) - 1) * m := by
  rw [halfNorm_latP, qZP]

/-- `⟨λ_p, β⟩ = ½⟨β,β⟩ − q_p(β)` — the background pairing as an *integer* cast. -/
theorem bgPair_lamP_eq (p : ℕ) (hp : 1 ≤ p) (m : ℤ) :
    BgA.bgPair (latP p) (lamP p) m = ((halfNorm (latP p) m - qZP p m : ℤ) : ℂ) := by
  rw [bgPair_lamP p hp, halfNorm_latP, qZP]
  push_cast
  ring

@[simp] theorem qZP_zero (p : ℕ) : qZP p 0 = 0 := by simp only [qZP]; ring

/-- **(g₁)  `wt(e^α) = 1`.** -/
@[simp] theorem qZP_one (p : ℕ) : qZP p 1 = 1 := by simp only [qZP]; ring

/-- **(g₂)  `wt(e^{−α}) = 2p − 1`.** -/
@[simp] theorem qZP_neg_one (p : ℕ) : qZP p (-1) = 2 * (p : ℤ) - 1 := by
  simp only [qZP]; ring

/-! ## §4  (d)  `PosQuad` — the deformed weights are strictly positive off the vacuum -/

/-- `q_p(m) = m·(pm − p + 1)`. -/
theorem qZP_factor (p : ℕ) (m : ℤ) : qZP p m = m * ((p : ℤ) * m - (p : ℤ) + 1) := by
  simp only [qZP]; ring

/-- **The arithmetic heart of `PosQuad`**: `q_p(m) = p m² − (p−1)m > 0` for `m ≠ 0`, `p ≥ 1`.
(`m = 1` gives `1`, `m = −1` gives `2p−1`, and `|m| ≥ 2` grows quadratically.) -/
theorem qZP_pos (p : ℕ) (hp : 1 ≤ p) {m : ℤ} (hm : m ≠ 0) : 0 < qZP p m := by
  have hp' : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  rw [qZP_factor]
  rcases lt_or_gt_of_ne hm with h | h
  · have key : (p : ℤ) * m - (p : ℤ) + 1 < 0 := by
      nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ (p : ℤ) - 1) (by omega : (0 : ℤ) ≤ 1 - m)]
    exact mul_pos_of_neg_of_neg h key
  · have key : 0 < (p : ℤ) * m - (p : ℤ) + 1 := by
      nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ (p : ℤ)) (by omega : (0 : ℤ) ≤ m - 1)]
    exact mul_pos h key

/-- **(d)  `PosQuad L_p q_p`.** -/
theorem posQuad_qrP (p : ℕ) (hp : 1 ≤ p) : PosQuad (latP p) (qrP p) := by
  have h : ∀ m : ℤ, m ≠ 0 → (0 : ℚ) < ((qZP p m : ℤ) : ℚ) := by
    intro m hm
    exact_mod_cast qZP_pos p hp hm
  exact h

/-! ## §5  (e)  `QFinite` — only finitely many charges below a given deformed weight -/

/-- `|m| ≤ q_p(m)`: the deformed weight dominates the charge, hence is proper. -/
theorem abs_le_qZP (p : ℕ) (hp : 1 ≤ p) (m : ℤ) : |m| ≤ qZP p m := by
  have hp' : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  rw [qZP_factor]
  rcases lt_trichotomy m 0 with h | h | h
  · rw [abs_of_neg h]
    have key : (p : ℤ) * m - (p : ℤ) + 1 ≤ -1 := by
      nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ (p : ℤ) - 1) (by omega : (0 : ℤ) ≤ 1 - m)]
    nlinarith
  · rw [h]; simp
  · rw [abs_of_pos h]
    have key : 1 ≤ (p : ℤ) * m - (p : ℤ) + 1 := by
      nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ (p : ℤ)) (by omega : (0 : ℤ) ≤ m - 1)]
    nlinarith

/-- **(e)  `QFinite L_p q_p`**: `{β | q_p β ≤ N}` is finite, since `q_p` grows quadratically. -/
theorem qFinite_qrP (p : ℕ) (hp : 1 ≤ p) : QFinite (latP p) (qrP p) := by
  have h : ∀ N : ℚ, {m : ℤ | ((qZP p m : ℤ) : ℚ) ≤ N}.Finite := by
    intro N
    refine Set.Finite.subset (Set.finite_Icc (-⌈N⌉) ⌈N⌉) ?_
    intro m hm
    have hmq : ((qZP p m : ℤ) : ℚ) ≤ N := hm
    have h1 : ((qZP p m : ℤ) : ℚ) ≤ ((⌈N⌉ : ℤ) : ℚ) := le_trans hmq (Int.le_ceil N)
    have h2 : qZP p m ≤ ⌈N⌉ := by exact_mod_cast h1
    have h3 : |m| ≤ ⌈N⌉ := le_trans (abs_le_qZP p hp m) h2
    exact Set.mem_Icc.mpr (abs_le.mp h3)
  exact h

/-! ## §6  (g)  The deformed conformal weights `wt(e^{±α})` -/

/-- **The deformed weight of `e^{mα}`** is `q_p(m) = p m² − (p−1)m`. -/
theorem LBg_weight_latP (p : ℕ) (hp : 1 ≤ p) (m : ℤ) :
    BgA.LBg (latP p) (lamP p) 0 (latChargeGen (latP p) m)
      = ((qZP p m : ℤ) : ℂ) • latChargeGen (latP p) m := by
  rw [BgA.LBg_weight_latChargeGen (latP p) (latP_posDef p hp), qZP_eq_halfNorm_sub_bgPair p hp]

/-- **(g)  `wt(e^α) = 1`.** -/
theorem LBg_weight_alpha (p : ℕ) (hp : 1 ≤ p) :
    BgA.LBg (latP p) (lamP p) 0 (latChargeGen (latP p) (alphaP p))
      = (1 : ℂ) • latChargeGen (latP p) (alphaP p) := by
  rw [alphaP, LBg_weight_latP p hp, qZP_one]
  norm_num

/-- **(g)  `wt(e^{−α}) = 2p − 1`.** -/
theorem LBg_weight_neg_alpha (p : ℕ) (hp : 1 ≤ p) :
    BgA.LBg (latP p) (lamP p) 0 (latChargeGen (latP p) (-alphaP p))
      = (2 * (p : ℂ) - 1) • latChargeGen (latP p) (-alphaP p) := by
  have h : (-alphaP p : (latP p).carrier) = (-1 : ℤ) := rfl
  rw [h, LBg_weight_latP p hp, qZP_neg_one]
  congr 1
  push_cast
  ring

/-! ## §7  (f)  The deformed grading `gradTrip` -/

/-- The **deformed (integer) weight** of the bigraded piece `(w, β)`: boson level `+ q_p(β)`. -/
def wtZP (p : ℕ) (x : ℤ × (latP p).carrier) : ℤ := x.1 + qZP p x.2

/-- **The deformed weight-`k` space of `V_{L_p}`** — the `ℤ`-indexed form of `gradingLatGenQ`
(available because `q_p` is integer-valued). -/
noncomputable def gradTrip (p : ℕ) (k : ℤ) : Submodule ℂ (LatModuleGen (latP p)) :=
  gradeCollapse (bigradα (latP p)) (wtZP p) k

theorem wtQ_latP (p : ℕ) (x : ℤ × (latP p).carrier) :
    wtQ (latP p) (qrP p) x = ((wtZP p x : ℤ) : ℂ) := by
  have h : wtQrat (latP p) (qrP p) x = ((wtZP p x : ℤ) : ℚ) := by
    show ((x.1 : ℤ) : ℚ) + ((qZP p x.2 : ℤ) : ℚ) = ((wtZP p x : ℤ) : ℚ)
    simp only [wtZP]
    push_cast
    ring
  rw [wtQ_eq, h]
  push_cast
  ring

/-- **The `ℤ`-indexed deformed grading is the `ℂ`-indexed `gradingLatGenQ`**, at the integer
points.  Everything proved for `QuadRefine` transports along this. -/
theorem gradTrip_eq (p : ℕ) (k : ℤ) :
    gradTrip p k = gradingLatGenQ (latP p) (qrP p) ((k : ℤ) : ℂ) := by
  have hset : (wtQ (latP p) (qrP p)) ⁻¹' {((k : ℤ) : ℂ)} = (wtZP p) ⁻¹' {k} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, wtQ_latP]
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast congrArg (fun t : ℤ => ((t : ℤ) : ℂ)) h
  rw [gradTrip, gradeCollapse_def, gradingLatGenQ_def, hset]

/-- Charge-sector description of the deformed grading: `𝒱_k = ⨆_β bigradα (k − q_p β, β)`. -/
theorem gradTrip_eq_iSup (p : ℕ) (k : ℤ) :
    gradTrip p k = ⨆ β : (latP p).carrier, bigradα (latP p) (k - qZP p β, β) := by
  rw [gradTrip, gradeCollapse_def]
  apply le_antisymm
  · refine iSup_le fun x => iSup_le fun hx => ?_
    have hx' : wtZP p x = k := hx
    have hx1 : x.1 = k - qZP p x.2 := by simp only [wtZP] at hx'; omega
    have hxe : x = (k - qZP p x.2, x.2) := by rw [Prod.ext_iff]; exact ⟨hx1, rfl⟩
    rw [hxe]
    exact le_iSup (fun β : (latP p).carrier => bigradα (latP p) (k - qZP p β, β)) x.2
  · refine iSup_le fun β => le_biSup (bigradα (latP p)) ?_
    show wtZP p (k - qZP p β, β) = k
    simp only [wtZP]
    omega

/-- Membership in a deformed weight space from membership in a bigraded piece. -/
theorem mem_gradTrip_of_bigradα (p : ℕ) (k w : ℤ) (β : (latP p).carrier)
    (hk : w + qZP p β = k) {x : LatModuleGen (latP p)} (hx : x ∈ bigradα (latP p) (w, β)) :
    x ∈ gradTrip p k := by
  rw [gradTrip, gradeCollapse_def]
  exact le_biSup (bigradα (latP p)) (show wtZP p (w, β) = k from hk) hx

/-! ### The `(weight, charge)` intersection lemma

The undeformed weight space intersected with a charge sector is a single bigraded piece.  This is
what lets the *undeformed* `VA1` axiom plus *charge additivity* produce the deformed `VA1`. -/

/-- `coordEα γ` maps the undeformed weight-`K` space into boson weight `K − ½⟨γ,γ⟩`. -/
theorem coordEα_gradingLatGen (L : IntegralLattice) (K : ℤ) (γ : L.carrier) :
    gradingLatGen L K
      ≤ Submodule.comap (coordEα L γ) (HeisenbergN.gradingZN (rank L) (K - halfNorm L γ)) := by
  classical
  rw [gradingLatGen]
  refine iSup_le fun α => ?_
  rintro _ ⟨q, hq, rfl⟩
  rw [Submodule.mem_comap]
  by_cases h : γ = α
  · subst h
    rw [show coordEα L γ (mkEα L γ q) = q from by rw [mkEα_apply, coordEα_apply, if_pos rfl]]
    exact hq
  · rw [show coordEα L γ (mkEα L α q) = 0 from by rw [mkEα_apply, coordEα_apply, if_neg h]]
    exact Submodule.zero_mem _

/-- **`gradingLatGen K ⊓ chargeSec γ = bigradα (K − ½⟨γ,γ⟩, γ)`** (the `≤` half, which is the one
that is used). -/
theorem mem_bigradα_of_grading_of_charge (L : IntegralLattice) (K : ℤ) (γ : L.carrier)
    {x : LatModuleGen L} (hg : x ∈ gradingLatGen L K) (hc : x ∈ chargeSec L γ) :
    x ∈ bigradα L (K - halfNorm L γ, γ) := by
  obtain ⟨q, rfl⟩ := hc
  have h := coordEα_gradingLatGen L K γ hg
  rw [Submodule.mem_comap,
    show coordEα L γ (mkEα L γ q) = q from by rw [mkEα_apply, coordEα_apply, if_pos rfl]] at h
  exact ⟨q, h, rfl⟩

/-- The polarization of `q_p` over `ℤ`: `q_p(β+β') = q_p β + q_p β' + ⟨β,β'⟩`. -/
theorem qZP_polar (p : ℕ) (a b : (latP p).carrier) :
    qZP p (a + b) = qZP p a + qZP p b + (latP p).form a b := by
  have h : ((qZP p (a + b) : ℤ) : ℚ) - ((qZP p a : ℤ) : ℚ) - ((qZP p b : ℤ) : ℚ)
      = (((latP p).form a b : ℤ) : ℚ) := (qrP p).polarization a b
  have h2 : ((qZP p (a + b) : ℤ) : ℚ)
      = ((qZP p a + qZP p b + (latP p).form a b : ℤ) : ℚ) := by
    push_cast at h ⊢
    linarith
  exact_mod_cast h2

/-! ### VA1 for the deformed grading -/

/-- **`grading_mode` (VA1) for the deformed grading.**  The deformed weight differs from the
undeformed one by `−⟨λ_p, charge⟩`, a *linear* function of the charge; since the charge is additive
under the `n`-th products (`YfullGen_shiftsCharge`) the linear correction cancels, and the axiom
follows from the undeformed `YfullGen_grading_mode`. -/
theorem gradTrip_grading_mode (p : ℕ) (hp : 1 ≤ p) {k l : ℤ}
    (u : LatModuleGen (latP p)) (hu : u ∈ gradTrip p k)
    (v : LatModuleGen (latP p)) (hv : v ∈ gradTrip p l) (n : ℤ) :
    mode (YfullGen (latP p) (latP_even p) (latP_posDef p hp) u) n v
      ∈ gradTrip p (k + l - n - 1) := by
  have key : ∀ (β : (latP p).carrier) (u' : LatModuleGen (latP p)),
      u' ∈ bigradα (latP p) (k - qZP p β, β) →
      ∀ (β' : (latP p).carrier) (v' : LatModuleGen (latP p)),
      v' ∈ bigradα (latP p) (l - qZP p β', β') →
      mode (YfullGen (latP p) (latP_even p) (latP_posDef p hp) u') n v'
        ∈ gradTrip p (k + l - n - 1) := by
    intro β u' hu' β' v' hv'
    have hug := bigradα_le_gradingLatGen (latP p) (k - qZP p β) β hu'
    have hvg := bigradα_le_gradingLatGen (latP p) (l - qZP p β') β' hv'
    have huc := bigradα_le_chargeSec (latP p) (k - qZP p β) β hu'
    have hvc := bigradα_le_chargeSec (latP p) (l - qZP p β') β' hv'
    have hmg := YfullGen_grading_mode (latP p) (latP_even p) (latP_posDef p hp) u' hug v' hvg n
    have hmc : mode (YfullGen (latP p) (latP_even p) (latP_posDef p hp) u') n v'
        ∈ chargeSec (latP p) (β + β') := by
      rw [mode_apply]
      exact YfullGen_shiftsCharge (latP p) (latP_even p) (latP_posDef p hp) β huc β' (-n - 1) v' hvc
    have hbig := mem_bigradα_of_grading_of_charge (latP p) _ (β + β') hmg hmc
    have hH := halfNorm_add (latP p) (latP_even p) β β'
    have hQ := qZP_polar p β β'
    rw [gradTrip_eq_iSup]
    refine Submodule.mem_iSup_of_mem (β + β') ?_
    rwa [show (k - qZP p β + halfNorm (latP p) β) + (l - qZP p β' + halfNorm (latP p) β') - n - 1
        - halfNorm (latP p) (β + β') = k + l - n - 1 - qZP p (β + β') from by omega] at hbig
  rw [gradTrip_eq_iSup] at hu hv
  refine Submodule.iSup_induction
    (fun β : (latP p).carrier => bigradα (latP p) (k - qZP p β, β))
    (motive := fun u' => mode (YfullGen (latP p) (latP_even p) (latP_posDef p hp) u') n v
      ∈ gradTrip p (k + l - n - 1)) hu ?_ ?_ ?_
  · intro β u' hu'
    refine Submodule.iSup_induction
      (fun β' : (latP p).carrier => bigradα (latP p) (l - qZP p β', β'))
      (motive := fun v' => mode (YfullGen (latP p) (latP_even p) (latP_posDef p hp) u') n v'
        ∈ gradTrip p (k + l - n - 1)) hv ?_ ?_ ?_
    · intro β' v' hv'; exact key β u' hu' β' v' hv'
    · simp only [map_zero]; exact Submodule.zero_mem _
    · intro x y hx hy; simp only [map_add]; exact Submodule.add_mem _ hx hy
  · simp only [map_zero]
    exact Submodule.zero_mem _
  · intro x y hx hy
    simp only [map_add, mode_add, LinearMap.add_apply]
    exact Submodule.add_mem _ hx hy

/-! ## §8  The deformed conformal vector `ω_{λ_p} = ω_L + λ_p(−2)|0⟩` -/

/-- **`ω_λ` sits in bidegree `(2, 0)`** — boson level `2`, charge `0` — for *any* background
charge `λ`.  (Both summands are charge-`0` and boson-level-`2`.) -/
theorem omegaBg_mem_bigradα (L : IntegralLattice) (lam : Fin (rank L) → ℂ) :
    BgA.omegaBg L lam ∈ bigradα L (2, 0) := by
  have h1 : HeisenbergN.ωN (rank L) 1 ∈ HeisenbergN.gradingZN (rank L) 2 :=
    HeisenbergN.ωN_mem_gradingZN_two (rank L) 1
  have h2 : BgA.bgOsc L lam (-2) (HeisenbergN.vacuumN (rank L))
      ∈ HeisenbergN.gradingZN (rank L) 2 := by
    rw [BgA.bgOsc_apply]
    refine Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ ?_)
    have h := HeisenbergN.oscN_mem_gradingZN (rank L) 1 a (-2)
      (HeisenbergN.vacuumN_mem_gradingWN (rank L))
    rwa [show ((0 : ℕ) : ℤ) - (-2) = 2 from by norm_num] at h
  exact ⟨_, Submodule.add_mem _ h1 h2, by rw [map_add]; rfl⟩

/-- **The deformed `L₀` acts by `k` on each bigraded piece of deformed weight `k`.** -/
theorem LBg_zero_bigradα (p : ℕ) (hp : 1 ≤ p) (k : ℤ) (β : (latP p).carrier)
    {x : LatModuleGen (latP p)} (hx : x ∈ bigradα (latP p) (k - qZP p β, β)) :
    BgA.LBg (latP p) (lamP p) 0 x = (k : ℂ) • x := by
  obtain ⟨q, hq, rfl⟩ := hx
  by_cases hw : 0 ≤ k - qZP p β
  · obtain ⟨w, hwz⟩ : ∃ w : ℕ, k - qZP p β = (w : ℤ) := ⟨(k - qZP p β).toNat, by omega⟩
    have hqW : q ∈ HeisenbergN.gradingWN (rank (latP p)) w := by
      rw [hwz, HeisenbergN.gradingZN_of_nonneg (by positivity), Int.toNat_natCast] at hq
      exact hq
    have hLL : LLGen (latP p) 0 = sugFieldGen (latP p) (-2) := by rw [LLGen]; norm_num
    have h1 : LLGen (latP p) 0 (mkEα (latP p) β q)
        = (((w : ℤ) + halfNorm (latP p) β : ℤ) : ℂ) • mkEα (latP p) β q := by
      rw [hLL]
      exact sugFieldGen_neg_two_bigradα (latP p) (latP_even p) (latP_posDef p hp) hqW
    have h2 : BgA.bgCur (latP p) (lamP p) 0 (mkEα (latP p) β q)
        = BgA.bgPair (latP p) (lamP p) β • mkEα (latP p) β q := by
      rw [show mkEα (latP p) β q = latStateGen (latP p) q β from rfl,
        BgA.bgCur_latStateGen, BgA.BetaSec_apply, BgA.bgOsc_zero, LinearMap.zero_apply,
        zero_add, BgA.scMom_zero, latStateGen_smul_boson]
    rw [show BgA.LBg (latP p) (lamP p) 0
        = LLGen (latP p) 0 - (((0 : ℤ) : ℂ) + 1) • BgA.bgCur (latP p) (lamP p) 0 from rfl,
      LinearMap.sub_apply, LinearMap.smul_apply, h1, h2, bgPair_lamP_eq p hp, smul_smul,
      ← sub_smul]
    congr 1
    rw [← hwz]
    push_cast
    ring
  · have hq0 : q = 0 := by
      rw [HeisenbergN.gradingZN_of_neg (by omega : k - qZP p β < 0)] at hq
      simpa using hq
    rw [hq0, map_zero, map_zero, smul_zero]

/-- The deformed `L₀` acts by `k` on the whole deformed weight-`k` space. -/
theorem LBg_zero_gradTrip (p : ℕ) (hp : 1 ≤ p) (k : ℤ) {x : LatModuleGen (latP p)}
    (hx : x ∈ gradTrip p k) : BgA.LBg (latP p) (lamP p) 0 x = (k : ℂ) • x := by
  rw [gradTrip_eq_iSup] at hx
  refine Submodule.iSup_induction
    (fun β : (latP p).carrier => bigradα (latP p) (k - qZP p β, β))
    (motive := fun y => BgA.LBg (latP p) (lamP p) 0 y = (k : ℂ) • y) hx ?_ ?_ ?_
  · intro β y hy; exact LBg_zero_bigradα p hp k β hy
  · simp only [map_zero, smul_zero]
  · intro y z hy hz; simp only [map_add]; rw [hy, hz, smul_add]

/-- **VOA2 for the deformed conformal vector.** -/
theorem L0_gradTrip (p : ℕ) (hp : 1 ≤ p) {k : ℤ} (v : LatModuleGen (latP p))
    (hv : v ∈ gradTrip p k) :
    mode (YfullGen (latP p) (latP_even p) (latP_posDef p hp)
      (BgA.omegaBg (latP p) (lamP p))) 1 v = (k : ℂ) • v := by
  have h := BgA.mode_YfullGen_omegaBg (latP p) (latP_even p) (latP_posDef p hp) (lamP p) 0
  rw [show (0 : ℤ) + 1 = 1 from by ring] at h
  rw [h]
  exact LBg_zero_gradTrip p hp k hv

/-- **`L₋₁` is undeformed**: the background-charge correction `−(n+1)λ(n)` vanishes at `n = −1`. -/
theorem mode_omegaBg_zero_eq (p : ℕ) (hp : 1 ≤ p) :
    mode (YfullGen (latP p) (latP_even p) (latP_posDef p hp)
      (BgA.omegaBg (latP p) (lamP p))) 0
      = mode (YfullGen (latP p) (latP_even p) (latP_posDef p hp) (omegaLatGen (latP p))) 0 := by
  have h1 := BgA.mode_YfullGen_omegaBg (latP p) (latP_even p) (latP_posDef p hp) (lamP p) (-1)
  have h2 := mode_YfullGen_omega_eq_LLGen (latP p) (latP_even p) (latP_posDef p hp) (-1)
  rw [show (-1 : ℤ) + 1 = 0 from by ring] at h1 h2
  rw [h1, h2, show BgA.LBg (latP p) (lamP p) (-1)
      = LLGen (latP p) (-1) - ((((-1 : ℤ)) : ℂ) + 1) • BgA.bgCur (latP p) (lamP p) (-1) from rfl]
  norm_num

/-- **VOA3 for the deformed conformal vector** — inherited verbatim from the undeformed one. -/
theorem translation_gradTrip (p : ℕ) (hp : 1 ≤ p) (v : LatModuleGen (latP p)) :
    YfullGen (latP p) (latP_even p) (latP_posDef p hp)
        (mode (YfullGen (latP p) (latP_even p) (latP_posDef p hp)
          (BgA.omegaBg (latP p) (lamP p))) 0 v)
      = deriv (YfullGen (latP p) (latP_even p) (latP_posDef p hp) v) := by
  rw [mode_omegaBg_zero_eq p hp]
  exact YfullGen_translation_omega (latP p) (latP_even p) (latP_posDef p hp) v

/-- **VOA1 for the deformed conformal vector**, central charge `1 − 6(p−1)²/p`. -/
theorem virasoro_gradTrip (p : ℕ) (hp : 1 ≤ p) (m n : ℤ) :
    ⁅mode (YfullGen (latP p) (latP_even p) (latP_posDef p hp)
        (BgA.omegaBg (latP p) (lamP p))) (m + 1),
      mode (YfullGen (latP p) (latP_even p) (latP_posDef p hp)
        (BgA.omegaBg (latP p) (lamP p))) (n + 1)⁆
      = ((m : ℂ) - n) • mode (YfullGen (latP p) (latP_even p) (latP_posDef p hp)
          (BgA.omegaBg (latP p) (lamP p))) (m + n + 1)
        + (if m + n = 0
           then (((m : ℂ) ^ 3 - m) / 12 * (1 - 6 * ((p : ℂ) - 1) ^ 2 / (p : ℂ)))
                  • (1 : End ℂ (LatModuleGen (latP p)))
           else 0) := by
  rw [BgA.mode_YfullGen_omegaBg, BgA.mode_YfullGen_omegaBg,
    show m + n + 1 = (m + n) + 1 from by ring, BgA.mode_YfullGen_omegaBg,
    LieRing.of_associative_ring_bracket, ← centralCharge_latP p hp]
  exact BgA.LBg_virasoro (latP p) (latP_posDef p hp) (lamP p) m n

/-! ## §9  (f)  THE INSTANCE -/

/-- **The deformed rank-one lattice vertex operator algebra `V_{L_p}^{λ_p}`**: the lattice VOA of
`L_p = ℤα`, `⟨α,α⟩ = 2p`, regraded by the background-charge weight `q_p(β) = ½⟨β,β⟩ − ⟨λ_p,β⟩`
and with the deformed conformal vector `ω_{λ_p} = ω_{L_p} + λ_p(−2)|0⟩`.  Central charge
`c = 1 − 6(p−1)²/p`; `wt(e^α) = 1` and `wt(e^{−α}) = 2p−1`.  This is the ambient inside which the
`(1,p)` triplet algebra `W(p)` sits as the kernel of the screening. -/
noncomputable def tripletLatticeVOA (p : ℕ) (hp : 1 ≤ p) :
    VertexOperatorAlgebra (LatModuleGen (latP p)) where
  grading := gradTrip p
  isInternal :=
    gradeCollapse_isInternal (bigradα_iSupIndep (latP p)) (bigradα_iSup_eq_top (latP p)) (wtZP p)
  finrank := fun n => by
    rw [gradTrip_eq]
    exact gradingLatGenQ_finrank (latP p) (qFinite_qrP p hp) _
  Y := YfullGen (latP p) (latP_even p) (latP_posDef p hp)
  vacuum := latVacuumGen (latP p)
  vacuum_mem := by
    rw [gradTrip_eq, Int.cast_zero]
    exact latVacuumGen_mem_gradingLatGenQ (latP p) (posQuad_qrP p hp)
  grading_mode := fun u hu v hv j => gradTrip_grading_mode p hp u hu v hv j
  vacuum_Y := YfullGen_vacuum (latP p) (latP_even p) (latP_posDef p hp)
  creation := YfullGen_creation (latP p) (latP_even p) (latP_posDef p hp)
  locality := YfullGen_local (latP p) (latP_even p) (latP_posDef p hp)
  regularity := YfullGen_regularity (latP p) (latP_even p) (latP_posDef p hp)
  conformalVector := BgA.omegaBg (latP p) (lamP p)
  conformal_mem :=
    mem_gradTrip_of_bigradα p 2 2 (0 : ℤ) (by rw [qZP_zero]; ring) (omegaBg_mem_bigradα (latP p) (lamP p))
  centralCharge := 1 - 6 * ((p : ℂ) - 1) ^ 2 / (p : ℂ)
  virasoro := virasoro_gradTrip p hp
  L0_grading := fun v hv => L0_gradTrip p hp v hv
  translation := translation_gradTrip p hp
  vacuum_grade := by
    rw [gradTrip_eq, Int.cast_zero]
    exact gradingLatGenQ_zero_eq_span_vacuum (latP p) (posQuad_qrP p hp)
  positivity := fun n hn => by
    rw [gradTrip_eq]
    refine gradingLatGenQ_eq_bot_of_re_neg (latP p) (posQuad_qrP p hp) _ ?_
    simp only [Complex.intCast_re]
    exact_mod_cast hn

/-- The deformed lattice VOA has central charge `c = 1 − 6(p−1)²/p`. -/
theorem tripletLatticeVOA_centralCharge (p : ℕ) (hp : 1 ≤ p) :
    (tripletLatticeVOA p hp).centralCharge = 1 - 6 * ((p : ℂ) - 1) ^ 2 / (p : ℂ) := rfl

/-- At `p = 2` the deformed lattice VOA has `c = −2` (the symplectic-fermion / `W(2)` value). -/
theorem tripletLatticeVOA_centralCharge_two (hp : 1 ≤ 2) :
    (tripletLatticeVOA 2 hp).centralCharge = -2 := by
  show (1 : ℂ) - 6 * (((2 : ℕ) : ℂ) - 1) ^ 2 / ((2 : ℕ) : ℂ) = -2
  norm_num

/-- **(g)  `wt(e^α) = 1`** inside the deformed VOA: `e^α` lies in deformed grade `1`. -/
theorem latChargeGen_alpha_mem_grade_one (p : ℕ) (hp : 1 ≤ p) :
    latChargeGen (latP p) (alphaP p) ∈ (tripletLatticeVOA p hp).grading 1 := by
  refine mem_gradTrip_of_bigradα p 1 0 (alphaP p) (by rw [alphaP, qZP_one]; ring) ?_
  exact ⟨HeisenbergN.vacuumN (rank (latP p)),
    HeisenbergN.mem_gradingZN_of_gradingWN (HeisenbergN.vacuumN_mem_gradingWN (rank (latP p))),
    rfl⟩

/-- **(g)  `wt(e^{−α}) = 2p−1`** inside the deformed VOA. -/
theorem latChargeGen_neg_alpha_mem_grade (p : ℕ) (hp : 1 ≤ p) :
    latChargeGen (latP p) (-alphaP p) ∈ (tripletLatticeVOA p hp).grading (2 * (p : ℤ) - 1) := by
  refine mem_gradTrip_of_bigradα p (2 * (p : ℤ) - 1) 0 (-alphaP p)
    (by rw [show (-alphaP p : (latP p).carrier) = (-1 : ℤ) from rfl, qZP_neg_one]; ring) ?_
  exact ⟨HeisenbergN.vacuumN (rank (latP p)),
    HeisenbergN.mem_gradingZN_of_gradingWN (HeisenbergN.vacuumN_mem_gradingWN (rank (latP p))),
    rfl⟩

/-! ### Accessors and the Virasoro modes of the instance -/

@[simp] theorem tripletLatticeVOA_grading (p : ℕ) (hp : 1 ≤ p) (k : ℤ) :
    (tripletLatticeVOA p hp).grading k = gradTrip p k := rfl

@[simp] theorem tripletLatticeVOA_Y (p : ℕ) (hp : 1 ≤ p) :
    (tripletLatticeVOA p hp).Y = YfullGen (latP p) (latP_even p) (latP_posDef p hp) := rfl

@[simp] theorem tripletLatticeVOA_vacuum (p : ℕ) (hp : 1 ≤ p) :
    (tripletLatticeVOA p hp).vacuum = latVacuumGen (latP p) := rfl

@[simp] theorem tripletLatticeVOA_conformalVector (p : ℕ) (hp : 1 ≤ p) :
    (tripletLatticeVOA p hp).conformalVector = BgA.omegaBg (latP p) (lamP p) := rfl

/-- **The Virasoro modes of the instance are the background-charge modes** `L_n^{λ_p}`. -/
theorem tripletLatticeVOA_L (p : ℕ) (hp : 1 ≤ p) (n : ℤ) :
    (tripletLatticeVOA p hp).L n = BgA.LBg (latP p) (lamP p) n :=
  BgA.mode_YfullGen_omegaBg (latP p) (latP_even p) (latP_posDef p hp) (lamP p) n

/-- `L_p` at `p = 1` is the `A₁` lattice `√2·ℤ` (`sqrt2Lattice`). -/
theorem latP_one_form (m n : ℤ) : (latP 1).form m n = sqrt2Lattice.form m n := by
  rw [latP_form]
  show _ = ((2 : ℤ) • LinearMap.mul ℤ ℤ) m n
  simp only [LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
  push_cast
  ring

/-- **The deformed weight of `e^{mα}` is `q_p(m) = p m² − (p−1)m`**, as a statement about the
grading of the instance. -/
theorem latChargeGen_mem_gradTrip (p : ℕ) (m : ℤ) :
    latChargeGen (latP p) m ∈ gradTrip p (qZP p m) := by
  refine mem_gradTrip_of_bigradα p (qZP p m) 0 m (by ring) ?_
  exact ⟨HeisenbergN.vacuumN (rank (latP p)),
    HeisenbergN.mem_gradingZN_of_gradingWN (HeisenbergN.vacuumN_mem_gradingWN (rank (latP p))),
    rfl⟩

end VOA.LatGen.Triplet
