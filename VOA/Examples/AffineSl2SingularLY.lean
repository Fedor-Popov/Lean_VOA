/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2Singular

/-!
# The weight-5 singular vector of `V^k(𝔰𝔩₂)`, and `k = -8/5` as a THEOREM

The Lee–Yang partner.  Under Drinfeld–Sokolov reduction the admissible level `k + 2 = p/q`
of `𝔰𝔩₂` maps to the Virasoro central charge `c_W = 1 - 6(p-q)²/(pq)`
(`VOA.DSsl2.dsCentralCharge_eq_minimalModel`).  The Lee–Yang model `(p,q) = (2,5)`,
`c_W = -22/5`, therefore comes from `k + 2 = 2/5`, i.e. **`k = -8/5`** — *not* from `k = -4/3`,
which is `(2,3)` and gives the trivial `c_W = 0`.  The affine central charge is
`3k/(k+2) = -12` (`Admissible.centralChargeA_neg_eight_fifths`).

This file is the exact analogue of `Examples/AffineSl2Singular.lean` one admissible level up.
**Nothing is transcribed from the literature.**  The singularity conditions are imposed on a
general element of the weight-5 charge-`+2` space and solved; the level drops out of the
elimination as the single equation `(5k + 8)·c₁ = 0`.

## §A  Where the weight comes from

For `k + 2 = u/v` in lowest terms with `u ≥ 2` the vacuum Verma module of `𝔰𝔩₂^` has its
singular vector at conformal weight `(u-1)v` and `𝔰𝔩₂`-weight `2(u-1)` (Kac–Kazhdan
determinant; see Creutzig–Ridout, arXiv:1306.4388 §3, and Malikov–Feigin–Fuchs).  Two checks:
`(u,v) = (2,3)` gives weight `3` and charge `+2`, which is exactly what
`Sl2Sing.sl2Singular_mem` and `Sl2Sing.sl2Singular_H0` prove; `(u,v) = (2,5)` gives
**weight 5, charge `+2`**, which is what is formalised here.

## §B  Conventions (identical to `Examples/AffineSl2Singular.lean`)

* Colours `colE = 0`, `colF = 1`, `colH = 2`; `⁅h,e⁆ = 2e`, `⁅h,f⁆ = -2f`, `⁅e,f⁆ = h`;
  normalised form `κ(e,f) = κ(f,e) = 1`, `κ(h,h) = 2`.
* `J k a m : End ℂ (WakModule k)` is the mode `x_a ⊗ tᵐ`, and `current_comm` reads
  `⁅J^a_m, J^b_n⁆ = ∑_c f^{ab}_c J^c_{m+n} + m·k·κ(a,b)·δ_{m+n,0}`; in particular the central
  term keeps the **left** mode `m`.  ⚠ For transferring coefficients computed elsewhere (e.g.
  with `OPEdefs`): the repository's `FormalDist` is indexed by the **z-exponent**, and the mode
  convention is `mode a m = a (-m-1)`.  Creation operators are `J k a (-p)` with `p ≥ 1`, and
  `J k a (-p) |0⟩` has conformal weight `p`.
* Normal order used throughout: mode indices weakly increasing left-to-right, ties broken
  `e < f < h`.  `N1, …, N21` below is that PBW basis of the weight-5 charge-`+2` space.

## §C  The 21-dimensional ansatz and the 25 equations

`N1 = e₋₁h₋₁h₋₁h₋₁h₋₁|0⟩`, …, `N21 = e₋₅|0⟩` (see §4).  `e₀` sends the space into the
12-dimensional weight-5 charge-`+4` span `T1, …, T12`, and `f₁` into the 13-dimensional
weight-4 charge-`0` span `U1, …, U13`.  Only `e₀` and `f₁` are imposed: they generate the
positive part `n̂₊` of `𝔰𝔩₂^` as a Lie algebra (`pos_ann5`).  `f₀` is *not* imposed — the vector
is the highest weight of an `𝔰𝔩₂` triplet, not a singlet.

## Main results

* `E0_ansatz5`, `F1_ansatz5`, `H0_ansatz5` — the images of the general ansatz, giving the
  25-equation system `SingSys5` (12 from `e₀`, 13 from `f₁`) and the charge `+2`.
* `SingSys5_param` — the elimination: `c₂ = 8c₁`, `c₃ = 16c₁`, `c₄ = (9k+12)c₁`,
  `c₅ = -(24k+64)c₁`, `c₇ = -16c₁`, `c₈ = kc₁`, `c₉ = (24k+48)c₁`, and `(5k + 8)·c₁ = 0`.
* `exists_nonzero_solution_iff` — **the level is a theorem**: the system has a nonzero
  solution iff `5k + 8 = 0`, i.e. `k = -8/5`.  (`SingSys5_level`,
  `SingSys5_trivial_of_level` are the two halves.)
* `sl2SingularLY : WakModule (-8/5)` — the explicit primitive integral vector

  ```
    625 e₋₁h₋₁h₋₁h₋₁h₋₁    5000 e₋₁e₋₁f₋₁h₋₁h₋₁   10000 e₋₁e₋₁e₋₁f₋₁f₋₁
  -1500 h₋₂e₋₁h₋₁h₋₁      -16000 h₋₂e₋₁e₋₁f₋₁        300 h₋₂h₋₂e₋₁
 -10000 f₋₂e₋₁e₋₁h₋₁       -1000 e₋₂h₋₁h₋₁h₋₁        6000 e₋₂e₋₁f₋₁h₋₁
   1200 e₋₂h₋₂h₋₁         -14400 e₋₂f₋₂e₋₁          -9600 e₋₂e₋₂f₋₁
 -19200 h₋₃e₋₁h₋₁         -14720 h₋₃e₋₂              1600 f₋₃e₋₁e₋₁
   4200 e₋₃h₋₁h₋₁          78400 e₋₃e₋₁f₋₁          -1680 e₋₃h₋₂
   2960 h₋₄e₋₁             17440 e₋₄h₋₁             25904 e₋₅
  ```

  together with `sl2SingularLY_E0`, `sl2SingularLY_F1`, `sl2SingularLY_E1`,
  `sl2SingularLY_H1`, `sl2SingularLY_H0 : h₀ s = 2·s`, `sl2SingularLY_mem : s ∈ gradingZA 5`
  and `sl2SingularLY_pos` — every mode of positive level annihilates `s`.
* `pos_ann5` — a weight-5 vector killed by `e₀` and `f₁` alone is killed by all of `n̂₊`.
  (Stronger than the weight-3 `Sl2Sing.pos_ann`, which assumes `e₁`, `f₁`, `h₁`.)
* `SingSys5_of_annihilated`, `ansatz5_eq_zero_of_level_ne`, `sl2SingularLY_ne_zero_of_indep` —
  the converse and the nonvanishing, each conditional on an **explicit named** independence
  hypothesis (`TIndep`, `UIndep`, `NIndep`).  These three hypotheses are *not* proved here; see
  §E below.
* `exists_singular_ansatz_iff` — the module-level form of the iff, modulo those three named
  hypotheses: the weight-5 charge-`+2` space contains a nonzero vector killed by `e₀` and `f₁`
  **iff** `5k + 8 = 0`.

All of the above are `#print axioms`-clean: every main result reports exactly
`[propext, Classical.choice, Quot.sound]`, so in particular none of them reaches `pbw`.

## §D  Consistency checks passed by the derived vector

Only `e₀ s = 0` and `f₁ s = 0` were imposed (25 equations, 21 unknowns — the system is
overdetermined by four equations).  The solution automatically satisfies `e₁ s = h₁ s = 0` and
`h₀ s = 2 s`, and the level it forces, `k = -8/5`, is the admissible level whose
Drinfeld–Sokolov image is Lee–Yang.  A separate computer-algebra sweep (not formalised)
confirms that weight-5 charge-`+2` is the *only* singular sector at `k = -8/5` for weight `≤ 5`,
so the vector is primitive rather than a descendant, and that the `21 × 21` subsystem obtained
by deleting four equations has determinant `-32768·(5k + 8)`.

## §E  What is NOT proved here (honest gaps)

1. **Weight-5 spanning.**  `gradingZA k 5 = span{PBW monomials}` is not proved, so the results
   read "within this 21-monomial ansatz", not "these are all weight-5 singular vectors".  The
   same caveat is recorded in `Examples/AffineSl2Singular.lean` §E for weight 3.
2. **Nonvanishing.**  Here only conditionally (`sl2SingularLY_ne_zero_of_indep`, hypothesis
   `NIndep`).  Proved unconditionally and `pbw`-free downstream: `WakLY.sl2SingularLY_ne_zero`
   (`Examples.WakimotoEightFifths`).  (`Examples/AffineSl2Indep.lean` discharges the analogous *target* independence at
   weight `≤ 3`; the weight-4 and weight-5 target independence `UIndep`/`TIndep` is a strictly
   larger computation and is left as a named hypothesis here.)
3. **The ideal / `L_{-8/5}(𝔰𝔩₂) ≠ V^{-8/5}(𝔰𝔩₂)`.**  Not in this file; proved downstream as
   `Sl2NotSimple85.maxGradedIdeal_85_ne_bot`, `Sl2NotSimple85.not_isSimple_85`.

## §F  Axioms

Everything below is `sorry`-free and introduces no axiom; in particular it does **not** reach
the theorem `VOA.pbw`, since the computational content rests
only on `current_comm` and `vacuum_pos_annihilate`.

## References
Creutzig–Ridout, arXiv:1306.4388 §3 (singular weight `(u-1)v`, charge `2(u-1)` for `k+2 = u/v`);
Kac–Kazhdan; Malikov–Feigin–Fuchs; Adamović–Milas on admissible `𝔰𝔩₂`;
Linshaw–Qi, arXiv:2601.12017 §5 (deformation rigidity).
-/

open Module (End)
open VOA VOA.AffineVOA VOA.AffineLie VOA.Sl2Sing

namespace VOA.Sl2SingLY

/-! ## §1  The Cartan charge -/

/-- `h₀` kills the vacuum, written as a charge-`0` eigenvalue equation. -/
theorem H0_vac (k : ℂ) : J k colH 0 (vacuumA k) = (0 : ℂ) • vacuumA k := by
  rw [H_vac0, zero_smul]

/-- Adding an `e`-mode raises the Cartan charge by `2`. -/
theorem H0_E {k : ℂ} {v : WakModule k} {q : ℂ} (m : ℤ)
    (hv : J k colH 0 v = q • v) (r : ℂ) (hr : q + 2 = r) :
    J k colH 0 (J k colE m v) = r • J k colE m v := by
  subst hr
  rw [HEs k 0 m m (zero_add m), hv, map_smul]
  module

/-- Adding an `f`-mode lowers the Cartan charge by `2`. -/
theorem H0_F {k : ℂ} {v : WakModule k} {q : ℂ} (m : ℤ)
    (hv : J k colH 0 v = q • v) (r : ℂ) (hr : q - 2 = r) :
    J k colH 0 (J k colF m v) = r • J k colF m v := by
  subst hr
  rw [HFs k 0 m m (zero_add m), hv, map_smul]
  module

/-- Adding an `h`-mode (of nonzero mode index) leaves the Cartan charge unchanged. -/
theorem H0_H {k : ℂ} {v : WakModule k} {q : ℂ} (m : ℤ) (hm : m ≠ 0)
    (hv : J k colH 0 v = q • v) :
    J k colH 0 (J k colH m v) = q • J k colH m v := by
  rw [HHs k 0 m (by omega), hv, map_smul]


/-! ## §2  Straightening lemmas (reordering a creation mode into normal order) -/

/-- Straightening: `h_{-1}` past `E1`. -/
theorem preH1_E1 (k : ℂ) (v : WakModule k) :
    J k colH (-1) (J k colE (-1) (v))
      = (2 : ℂ) • J k colE (-2) (v) + J k colE (-1) (J k colH (-1) (v)) := by
  simp only [HEs k (-1) (-1) (-2) (by norm_num) (v)]
  try module

/-- Straightening: `h_{-1}` past `E2`. -/
theorem preH1_E2 (k : ℂ) (v : WakModule k) :
    J k colH (-1) (J k colE (-2) (v))
      = (2 : ℂ) • J k colE (-3) (v) + J k colE (-2) (J k colH (-1) (v)) := by
  simp only [HEs k (-1) (-2) (-3) (by norm_num) (v)]
  try module

/-- Straightening: `h_{-1}` past `E1H1`. -/
theorem preH1_E1H1 (k : ℂ) (v : WakModule k) :
    J k colH (-1) (J k colE (-1) (J k colH (-1) (v)))
      = (2 : ℂ) • J k colE (-2) (J k colH (-1) (v))
        + J k colE (-1) (J k colH (-1) (J k colH (-1) (v))) := by
  simp only [HEs k (-1) (-1) (-2) (by norm_num) (J k colH (-1) (v))]
  try module

/-- Straightening: `h_{-1}` past `E3`. -/
theorem preH1_E3 (k : ℂ) (v : WakModule k) :
    J k colH (-1) (J k colE (-3) (v))
      = (2 : ℂ) • J k colE (-4) (v) + J k colE (-3) (J k colH (-1) (v)) := by
  simp only [HEs k (-1) (-3) (-4) (by norm_num) (v)]
  try module

/-- Straightening: `h_{-1}` past `E2H1`. -/
theorem preH1_E2H1 (k : ℂ) (v : WakModule k) :
    J k colH (-1) (J k colE (-2) (J k colH (-1) (v)))
      = (2 : ℂ) • J k colE (-3) (J k colH (-1) (v))
        + J k colE (-2) (J k colH (-1) (J k colH (-1) (v))) := by
  simp only [HEs k (-1) (-2) (-3) (by norm_num) (J k colH (-1) (v))]
  try module

/-- Straightening: `h_{-1}` past `E1H1H1`. -/
theorem preH1_E1H1H1 (k : ℂ) (v : WakModule k) :
    J k colH (-1) (J k colE (-1) (J k colH (-1) (J k colH (-1) (v))))
      = (2 : ℂ) • J k colE (-2) (J k colH (-1) (J k colH (-1) (v)))
        + J k colE (-1) (J k colH (-1) (J k colH (-1) (J k colH (-1) (v)))) := by
  simp only [HEs k (-1) (-1) (-2) (by norm_num) (J k colH (-1) (J k colH (-1) (v)))]
  try module

/-- Straightening: `e_{-1}` past `E4`. -/
theorem preE1_E4 (k : ℂ) (v : WakModule k) :
    J k colE (-1) (J k colE (-4) (v))
      = J k colE (-4) (J k colE (-1) (v)) := by
  simp only [EEs k (-1) (-4) (v)]
  try module

/-- Straightening: `e_{-1}` past `E3H1`. -/
theorem preE1_E3H1 (k : ℂ) (v : WakModule k) :
    J k colE (-1) (J k colE (-3) (J k colH (-1) (v)))
      = J k colE (-3) (J k colE (-1) (J k colH (-1) (v))) := by
  simp only [EEs k (-1) (-3) (J k colH (-1) (v))]
  try module

/-- Straightening: `e_{-1}` past `E2H1H1`. -/
theorem preE1_E2H1H1 (k : ℂ) (v : WakModule k) :
    J k colE (-1) (J k colE (-2) (J k colH (-1) (J k colH (-1) (v))))
      = J k colE (-2) (J k colE (-1) (J k colH (-1) (J k colH (-1) (v)))) := by
  simp only [EEs k (-1) (-2) (J k colH (-1) (J k colH (-1) (v)))]
  try module

/-- Straightening: `h_{-1}` past `F1`. -/
theorem preH1_F1 (k : ℂ) (v : WakModule k) :
    J k colH (-1) (J k colF (-1) (v))
      = (-2 : ℂ) • J k colF (-2) (v) + J k colF (-1) (J k colH (-1) (v)) := by
  simp only [HFs k (-1) (-1) (-2) (by norm_num) (v)]
  try module

/-- Straightening: `h_{-1}` past `F2`. -/
theorem preH1_F2 (k : ℂ) (v : WakModule k) :
    J k colH (-1) (J k colF (-2) (v))
      = (-2 : ℂ) • J k colF (-3) (v) + J k colF (-2) (J k colH (-1) (v)) := by
  simp only [HFs k (-1) (-2) (-3) (by norm_num) (v)]
  try module

/-- Straightening: `h_{-1}` past `F1H1`. -/
theorem preH1_F1H1 (k : ℂ) (v : WakModule k) :
    J k colH (-1) (J k colF (-1) (J k colH (-1) (v)))
      = (-2 : ℂ) • J k colF (-2) (J k colH (-1) (v))
        + J k colF (-1) (J k colH (-1) (J k colH (-1) (v))) := by
  simp only [HFs k (-1) (-1) (-2) (by norm_num) (J k colH (-1) (v))]
  try module

/-- Straightening: `e_{-1}` past `F3`. -/
theorem preE1_F3 (k : ℂ) (v : WakModule k) :
    J k colE (-1) (J k colF (-3) (v))
      = J k colH (-4) (v) + J k colF (-3) (J k colE (-1) (v)) := by
  simp only [EFs k (-1) (-3) (-4) (by norm_num) (by norm_num) (v)]
  try module

/-- Straightening: `e_{-1}` past `F2H1`. -/
theorem preE1_F2H1 (k : ℂ) (v : WakModule k) :
    J k colE (-1) (J k colF (-2) (J k colH (-1) (v)))
      = J k colH (-3) (J k colH (-1) (v))
        + J k colF (-2) (J k colE (-1) (J k colH (-1) (v))) := by
  simp only [EFs k (-1) (-2) (-3) (by norm_num) (by norm_num) (J k colH (-1) (v))]
  try module

/-- Straightening: `f_{-1}` past `E2`. -/
theorem preF1_E2 (k : ℂ) (v : WakModule k) :
    J k colF (-1) (J k colE (-2) (v))
      = (-1 : ℂ) • J k colH (-3) (v) + J k colE (-2) (J k colF (-1) (v)) := by
  simp only [FEs k (-1) (-2) (-3) (by norm_num) (by norm_num) (v)]
  try module

/-- Straightening: `f_{-1}` past `E1H1`. -/
theorem preF1_E1H1 (k : ℂ) (v : WakModule k) :
    J k colF (-1) (J k colE (-1) (J k colH (-1) (v)))
      = (-1 : ℂ) • J k colH (-2) (J k colH (-1) (v))
        + J k colE (-1) (J k colF (-1) (J k colH (-1) (v))) := by
  simp only [FEs k (-1) (-1) (-2) (by norm_num) (by norm_num) (J k colH (-1) (v))]
  try module

/-- Straightening: `e_{-1}` past `H3`. -/
theorem preE1_H3 (k : ℂ) (v : WakModule k) :
    J k colE (-1) (J k colH (-3) (v))
      = (-2 : ℂ) • J k colE (-4) (v) + J k colH (-3) (J k colE (-1) (v)) := by
  simp only [EHs k (-1) (-3) (-4) (by norm_num) (v)]
  try module

/-- Straightening: `e_{-1}` past `E2F1`. -/
theorem preE1_E2F1 (k : ℂ) (v : WakModule k) :
    J k colE (-1) (J k colE (-2) (J k colF (-1) (v)))
      = J k colE (-2) (J k colE (-1) (J k colF (-1) (v))) := by
  simp only [EEs k (-1) (-2) (J k colF (-1) (v))]
  try module

/-- Straightening: `e_{-1}` past `H2H1`. -/
theorem preE1_H2H1 (k : ℂ) (v : WakModule k) :
    J k colE (-1) (J k colH (-2) (J k colH (-1) (v)))
      = (-2 : ℂ) • J k colE (-3) (J k colH (-1) (v))
        + J k colH (-2) (J k colE (-1) (J k colH (-1) (v))) := by
  simp only [EHs k (-1) (-2) (-3) (by norm_num) (J k colH (-1) (v))]
  try module

/-- Straightening: `e_{-1}` past `H3E1`. -/
theorem preE1_H3E1 (k : ℂ) (v : WakModule k) :
    J k colE (-1) (J k colH (-3) (J k colE (-1) (v)))
      = (-2 : ℂ) • J k colE (-4) (J k colE (-1) (v))
        + J k colH (-3) (J k colE (-1) (J k colE (-1) (v))) := by
  simp only [EHs k (-1) (-3) (-4) (by norm_num) (J k colE (-1) (v))]
  try module

/-- Straightening: `e_{-1}` past `E2E1F1`. -/
theorem preE1_E2E1F1 (k : ℂ) (v : WakModule k) :
    J k colE (-1) (J k colE (-2) (J k colE (-1) (J k colF (-1) (v))))
      = J k colE (-2) (J k colE (-1) (J k colE (-1) (J k colF (-1) (v)))) := by
  simp only [EEs k (-1) (-2) (J k colE (-1) (J k colF (-1) (v)))]
  try module

/-- Straightening: `e_{-1}` past `H2E1H1`. -/
theorem preE1_H2E1H1 (k : ℂ) (v : WakModule k) :
    J k colE (-1) (J k colH (-2) (J k colE (-1) (J k colH (-1) (v))))
      = (-2 : ℂ) • J k colE (-3) (J k colE (-1) (J k colH (-1) (v)))
        + J k colH (-2) (J k colE (-1) (J k colE (-1) (J k colH (-1) (v)))) := by
  simp only [EHs k (-1) (-2) (-3) (by norm_num) (J k colE (-1) (J k colH (-1) (v)))]
  try module

/-- Straightening: `e_{-1}` past `F2`. -/
theorem preE1_F2 (k : ℂ) (v : WakModule k) :
    J k colE (-1) (J k colF (-2) (v))
      = J k colH (-3) (v) + J k colF (-2) (J k colE (-1) (v)) := by
  simp only [EFs k (-1) (-2) (-3) (by norm_num) (by norm_num) (v)]
  try module

/-- Straightening: `e_{-1}` past `F2E1`. -/
theorem preE1_F2E1 (k : ℂ) (v : WakModule k) :
    J k colE (-1) (J k colF (-2) (J k colE (-1) (v)))
      = J k colH (-3) (J k colE (-1) (v))
        + J k colF (-2) (J k colE (-1) (J k colE (-1) (v))) := by
  simp only [EFs k (-1) (-2) (-3) (by norm_num) (by norm_num) (J k colE (-1) (v))]
  try module

/-- Straightening: `e_{-1}` past `F2E1E1`. -/
theorem preE1_F2E1E1 (k : ℂ) (v : WakModule k) :
    J k colE (-1) (J k colF (-2) (J k colE (-1) (J k colE (-1) (v))))
      = J k colH (-3) (J k colE (-1) (J k colE (-1) (v)))
        + J k colF (-2) (J k colE (-1) (J k colE (-1) (J k colE (-1) (v)))) := by
  simp only [EFs k (-1) (-2) (-3) (by norm_num) (by norm_num) (J k colE (-1) ( J k colE (-1) (v)))]
  try module

/-- Straightening: `e_{-1}` past `E2`. -/
theorem preE1_E2 (k : ℂ) (v : WakModule k) :
    J k colE (-1) (J k colE (-2) (v))
      = J k colE (-2) (J k colE (-1) (v)) := by
  simp only [EEs k (-1) (-2) (v)]
  try module

/-- Straightening: `h_{-2}` past `E2E1`. -/
theorem preH2_E2E1 (k : ℂ) (v : WakModule k) :
    J k colH (-2) (J k colE (-2) (J k colE (-1) (v)))
      = (2 : ℂ) • J k colE (-4) (J k colE (-1) (v))
        + J k colE (-2) (J k colH (-2) (J k colE (-1) (v))) := by
  simp only [HEs k (-2) (-2) (-4) (by norm_num) (J k colE (-1) (v))]
  try module

/-- Straightening: `f_{-1}` past `E1H1H1`. -/
theorem preF1_E1H1H1 (k : ℂ) (v : WakModule k) :
    J k colF (-1) (J k colE (-1) (J k colH (-1) (J k colH (-1) (v))))
      = (-1 : ℂ) • J k colH (-2) (J k colH (-1) (J k colH (-1) (v)))
        + J k colE (-1) (J k colF (-1) (J k colH (-1) (J k colH (-1) (v)))) := by
  simp only [FEs k (-1) (-1) (-2) (by norm_num) (by norm_num) (J k colH (-1) ( J k colH (-1) (v)))]
  try module

/-- Straightening: `f_{-1}` past `E1F1`. -/
theorem preF1_E1F1 (k : ℂ) (v : WakModule k) :
    J k colF (-1) (J k colE (-1) (J k colF (-1) (v)))
      = (-1 : ℂ) • J k colH (-2) (J k colF (-1) (v))
        + J k colE (-1) (J k colF (-1) (J k colF (-1) (v))) := by
  simp only [FEs k (-1) (-1) (-2) (by norm_num) (by norm_num) (J k colF (-1) (v))]
  try module

/-- Straightening: `e_{-1}` past `H2F1`. -/
theorem preE1_H2F1 (k : ℂ) (v : WakModule k) :
    J k colE (-1) (J k colH (-2) (J k colF (-1) (v)))
      = (-2 : ℂ) • J k colE (-3) (J k colF (-1) (v))
        + J k colH (-2) (J k colE (-1) (J k colF (-1) (v))) := by
  simp only [EHs k (-1) (-2) (-3) (by norm_num) (J k colF (-1) (v))]
  try module

/-- Straightening: `f_{-1}` past `E1E1F1`. -/
theorem preF1_E1E1F1 (k : ℂ) (v : WakModule k) :
    J k colF (-1) (J k colE (-1) (J k colE (-1) (J k colF (-1) (v))))
      = (2 : ℂ) • J k colE (-3) (J k colF (-1) (v))
        + (-2 : ℂ) • J k colH (-2) (J k colE (-1) (J k colF (-1) (v)))
        + J k colE (-1) (J k colE (-1) (J k colF (-1) (J k colF (-1) (v)))) := by
  simp only [FEs k (-1) (-1) (-2) (by norm_num) (by norm_num) (J k colE (-1) ( J k colF (-1) (v))),
    preF1_E1F1, preE1_H2F1, map_add, map_smul]
  try module

/-- Straightening: `f_{-1}` past `E1`. -/
theorem preF1_E1 (k : ℂ) (v : WakModule k) :
    J k colF (-1) (J k colE (-1) (v))
      = (-1 : ℂ) • J k colH (-2) (v) + J k colE (-1) (J k colF (-1) (v)) := by
  simp only [FEs k (-1) (-1) (-2) (by norm_num) (by norm_num) (v)]
  try module

/-- Straightening: `f_{-1}` past `H2E1`. -/
theorem preF1_H2E1 (k : ℂ) (v : WakModule k) :
    J k colF (-1) (J k colH (-2) (J k colE (-1) (v)))
      = (2 : ℂ) • J k colF (-3) (J k colE (-1) (v))
        + (-1 : ℂ) • J k colH (-2) (J k colH (-2) (v))
        + J k colH (-2) (J k colE (-1) (J k colF (-1) (v))) := by
  simp only [FHs k (-1) (-2) (-3) (by norm_num) (J k colE (-1) (v)), preF1_E1, map_add, map_smul]
  try module

/-- Straightening: `e_{-2}` past `E3`. -/
theorem preE2_E3 (k : ℂ) (v : WakModule k) :
    J k colE (-2) (J k colE (-3) (v))
      = J k colE (-3) (J k colE (-2) (v)) := by
  simp only [EEs k (-2) (-3) (v)]
  try module

/-- Straightening: `e_{-1}` past `H2`. -/
theorem preE1_H2 (k : ℂ) (v : WakModule k) :
    J k colE (-1) (J k colH (-2) (v))
      = (-2 : ℂ) • J k colE (-3) (v) + J k colH (-2) (J k colE (-1) (v)) := by
  simp only [EHs k (-1) (-2) (-3) (by norm_num) (v)]
  try module

/-- Straightening: `h_{-1}` past `E1F1H1`. -/
theorem preH1_E1F1H1 (k : ℂ) (v : WakModule k) :
    J k colH (-1) (J k colE (-1) (J k colF (-1) (J k colH (-1) (v))))
      = (-2 : ℂ) • J k colH (-3) (J k colH (-1) (v))
        + (2 : ℂ) • J k colE (-2) (J k colF (-1) (J k colH (-1) (v)))
        + (-2 : ℂ) • J k colF (-2) (J k colE (-1) (J k colH (-1) (v)))
        + J k colE (-1) (J k colF (-1) (J k colH (-1) (J k colH (-1) (v)))) := by
  simp only [HEs k (-1) (-1) (-2) (by norm_num) (J k colF (-1) (J k colH (-1) (v))),
    preH1_F1H1, preE1_F2H1, map_add, map_smul]
  try module

/-- Straightening: `h_{-1}` past `H2H1`. -/
theorem preH1_H2H1 (k : ℂ) (v : WakModule k) :
    J k colH (-1) (J k colH (-2) (J k colH (-1) (v)))
      = J k colH (-2) (J k colH (-1) (J k colH (-1) (v))) := by
  simp only [HHs k (-1) (-2) (by norm_num) (J k colH (-1) (v))]
  try module

/-- Straightening: `f_{-2}` past `E2`. -/
theorem preF2_E2 (k : ℂ) (v : WakModule k) :
    J k colF (-2) (J k colE (-2) (v))
      = (-1 : ℂ) • J k colH (-4) (v) + J k colE (-2) (J k colF (-2) (v)) := by
  simp only [FEs k (-2) (-2) (-4) (by norm_num) (by norm_num) (v)]
  try module

/-- Straightening: `h_{-1}` past `F2E1`. -/
theorem preH1_F2E1 (k : ℂ) (v : WakModule k) :
    J k colH (-1) (J k colF (-2) (J k colE (-1) (v)))
      = (-2 : ℂ) • J k colH (-4) (v) + (-2 : ℂ) • J k colF (-3) (J k colE (-1) (v))
        + (2 : ℂ) • J k colE (-2) (J k colF (-2) (v))
        + J k colF (-2) (J k colE (-1) (J k colH (-1) (v))) := by
  simp only [HFs k (-1) (-2) (-3) (by norm_num) (J k colE (-1) (v)), preH1_E1, preF2_E2,
    map_add, map_smul]
  try module

/-- Straightening: `h_{-1}` past `E2F1`. -/
theorem preH1_E2F1 (k : ℂ) (v : WakModule k) :
    J k colH (-1) (J k colE (-2) (J k colF (-1) (v)))
      = (2 : ℂ) • J k colE (-3) (J k colF (-1) (v))
        + (-2 : ℂ) • J k colE (-2) (J k colF (-2) (v))
        + J k colE (-2) (J k colF (-1) (J k colH (-1) (v))) := by
  simp only [HEs k (-1) (-2) (-3) (by norm_num) (J k colF (-1) (v)), preH1_F1, map_add, map_smul]
  try module


/-! ## §3  The action of `e₀`, `f₁` and `h₀` on the sub-words -/

/-- Action of `e_{0}` on `H1`. -/
theorem actEp0_H1 (k : ℂ) :
    J k colE (0) (J k colH (-1) (vacuumA k))
      = (-2 : ℂ) • J k colE (-1) (vacuumA k) := by
  simp only [EHs k (0) (-1) (-1) (by norm_num) (vacuumA k), E_vac0, map_zero]
  try module

/-- Action of `e_{0}` on `H1H1`. -/
theorem actEp0_H1H1 (k : ℂ) :
    J k colE (0) (J k colH (-1) (J k colH (-1) (vacuumA k)))
      = (-4 : ℂ) • J k colE (-2) (vacuumA k)
        + (-4 : ℂ) • J k colE (-1) (J k colH (-1) (vacuumA k)) := by
  simp only [EHs k (0) (-1) (-1) (by norm_num) (J k colH (-1) (vacuumA k)), actEp0_H1,
    preH1_E1, map_smul]
  try module

/-- Action of `e_{0}` on `H1H1H1`. -/
theorem actEp0_H1H1H1 (k : ℂ) :
    J k colE (0) (J k colH (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))))
      = (-8 : ℂ) • J k colE (-3) (vacuumA k)
        + (-12 : ℂ) • J k colE (-2) (J k colH (-1) (vacuumA k))
        + (-6 : ℂ) • J k colE (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))) := by
  simp only [EHs k (0) (-1) (-1) (by norm_num) (J k colH (-1) (J k colH (-1) (vacuumA k))),
    actEp0_H1H1, preH1_E2, preH1_E1H1, map_add, map_smul]
  try module

/-- Action of `e_{0}` on `H1H1H1H1`. -/
theorem actEp0_H1H1H1H1 (k : ℂ) :
    J k colE (0) (J k colH (-1) (J k colH (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))))
      = (-16 : ℂ) • J k colE (-4) (vacuumA k)
        + (-32 : ℂ) • J k colE (-3) (J k colH (-1) (vacuumA k))
        + (-24 : ℂ) • J k colE (-2) (J k colH (-1) (J k colH (-1) (vacuumA k)))
        + (-8 : ℂ) • J k colE (-1) (J k colH (-1) (J k colH (-1) (
          J k colH (-1) (vacuumA k)))) := by
  simp only [EHs k (0) (-1) (-1) (by norm_num) (J k colH (-1) 
      (J k colH (-1) ( J k colH (-1) (vacuumA k)))),
    actEp0_H1H1H1, preH1_E3, preH1_E2H1, preH1_E1H1H1, map_add, map_smul]
  try module

/-- Action of `e_{0}` on `E1H1H1H1H1`. -/
theorem actEp0_E1H1H1H1H1 (k : ℂ) :
    J k colE (0) (J k colE (-1) (J k colH (-1) (J k colH (-1) (J k colH (-1) (
      J k colH (-1) (vacuumA k))))))
      = (-16 : ℂ) • J k colE (-4) (J k colE (-1) (vacuumA k))
        + (-32 : ℂ) • J k colE (-3) (J k colE (-1) (J k colH (-1) (vacuumA k)))
        + (-24 : ℂ) • J k colE (-2) (J k colE (-1) (J k colH (-1) (
          J k colH (-1) (vacuumA k))))
        + (-8 : ℂ) • J k colE (-1) (J k colE (-1) (J k colH (-1) (J k colH (-1) (
          J k colH (-1) (vacuumA k))))) := by
  simp only [EEs k (0) (-1) (J k colH (-1) (J k colH (-1) 
      (J k colH (-1) ( J k colH (-1) (vacuumA k))))),
    actEp0_H1H1H1H1, preE1_E4, preE1_E3H1, preE1_E2H1H1, map_add, map_smul]
  try module

/-- Action of `f_{1}` on `H1`. -/
theorem actFp1_H1 (k : ℂ) :
    J k colF (1) (J k colH (-1) (vacuumA k))
      = 0 := by
  simp only [FHs k (1) (-1) (0) (by norm_num) (vacuumA k), F_vac1, F_vac0, map_zero, smul_zero,
    add_zero]
  try module

/-- Action of `f_{0}` on `H1`. -/
theorem actFp0_H1 (k : ℂ) :
    J k colF (0) (J k colH (-1) (vacuumA k))
      = (2 : ℂ) • J k colF (-1) (vacuumA k) := by
  simp only [FHs k (0) (-1) (-1) (by norm_num) (vacuumA k), F_vac0, map_zero, zero_add]
  try module

/-- Action of `f_{1}` on `H1H1`. -/
theorem actFp1_H1H1 (k : ℂ) :
    J k colF (1) (J k colH (-1) (J k colH (-1) (vacuumA k)))
      = (4 : ℂ) • J k colF (-1) (vacuumA k) := by
  simp only [FHs k (1) (-1) (0) (by norm_num) (J k colH (-1) (vacuumA k)), actFp1_H1,
    actFp0_H1, map_zero, zero_add]
  try module

/-- Action of `f_{0}` on `H1H1`. -/
theorem actFp0_H1H1 (k : ℂ) :
    J k colF (0) (J k colH (-1) (J k colH (-1) (vacuumA k)))
      = (-4 : ℂ) • J k colF (-2) (vacuumA k)
        + (4 : ℂ) • J k colF (-1) (J k colH (-1) (vacuumA k)) := by
  simp only [FHs k (0) (-1) (-1) (by norm_num) (J k colH (-1) (vacuumA k)), actFp0_H1,
    preH1_F1, map_smul]
  try module

/-- Action of `f_{1}` on `H1H1H1`. -/
theorem actFp1_H1H1H1 (k : ℂ) :
    J k colF (1) (J k colH (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))))
      = (-16 : ℂ) • J k colF (-2) (vacuumA k)
        + (12 : ℂ) • J k colF (-1) (J k colH (-1) (vacuumA k)) := by
  simp only [FHs k (1) (-1) (0) (by norm_num) (J k colH (-1) (J k colH (-1) (vacuumA k))),
    actFp1_H1H1, preH1_F1, actFp0_H1H1, map_smul]
  try module

/-- Action of `f_{0}` on `H1H1H1`. -/
theorem actFp0_H1H1H1 (k : ℂ) :
    J k colF (0) (J k colH (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))))
      = (8 : ℂ) • J k colF (-3) (vacuumA k)
        + (-12 : ℂ) • J k colF (-2) (J k colH (-1) (vacuumA k))
        + (6 : ℂ) • J k colF (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))) := by
  simp only [FHs k (0) (-1) (-1) (by norm_num) (J k colH (-1) (J k colH (-1) (vacuumA k))),
    actFp0_H1H1, preH1_F2, preH1_F1H1, map_add, map_smul]
  try module

/-- Action of `f_{1}` on `H1H1H1H1`. -/
theorem actFp1_H1H1H1H1 (k : ℂ) :
    J k colF (1) (J k colH (-1) (J k colH (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))))
      = (48 : ℂ) • J k colF (-3) (vacuumA k)
        + (-64 : ℂ) • J k colF (-2) (J k colH (-1) (vacuumA k))
        + (24 : ℂ) • J k colF (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))) := by
  simp only [FHs k (1) (-1) (0) (by norm_num) (J k colH (-1) 
      (J k colH (-1) ( J k colH (-1) (vacuumA k)))),
    actFp1_H1H1H1, preH1_F2, preH1_F1H1, actFp0_H1H1H1, map_add, map_smul]
  try module

/-- Cartan charge of `H1` is `0`. -/
theorem actHp0_H1 (k : ℂ) :
    J k colH (0) (J k colH (-1) (vacuumA k))
      = (0 : ℂ) • J k colH (-1) (vacuumA k) := by
  exact H0_H (-1) (by norm_num) (H0_vac k)

/-- Cartan charge of `H1H1` is `0`. -/
theorem actHp0_H1H1 (k : ℂ) :
    J k colH (0) (J k colH (-1) (J k colH (-1) (vacuumA k)))
      = (0 : ℂ) • J k colH (-1) (J k colH (-1) (vacuumA k)) := by
  have g1 := H0_H (-1) (by norm_num) (H0_vac k)
  exact H0_H (-1) (by norm_num) g1

/-- Cartan charge of `H1H1H1` is `0`. -/
theorem actHp0_H1H1H1 (k : ℂ) :
    J k colH (0) (J k colH (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))))
      = (0 : ℂ) • J k colH (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))) := by
  have g1 := H0_H (-1) (by norm_num) (H0_vac k)
  have g2 := H0_H (-1) (by norm_num) g1
  exact H0_H (-1) (by norm_num) g2

/-- Cartan charge of `H1H1H1H1` is `0`. -/
theorem actHp0_H1H1H1H1 (k : ℂ) :
    J k colH (0) (J k colH (-1) (J k colH (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))))
      = (0 : ℂ) • J k colH (-1) (J k colH (-1) (J k colH (-1) (
        J k colH (-1) (vacuumA k)))) := by
  have g1 := H0_H (-1) (by norm_num) (H0_vac k)
  have g2 := H0_H (-1) (by norm_num) g1
  have g3 := H0_H (-1) (by norm_num) g2
  exact H0_H (-1) (by norm_num) g3

/-- Action of `f_{1}` on `E1H1H1H1H1`. -/
theorem actFp1_E1H1H1H1H1 (k : ℂ) :
    J k colF (1) (J k colE (-1) (J k colH (-1) (J k colH (-1) (J k colH (-1) (
      J k colH (-1) (vacuumA k))))))
      = (48 : ℂ) • J k colH (-4) (vacuumA k)
        + (48 : ℂ) • J k colF (-3) (J k colE (-1) (vacuumA k))
        + (-64 : ℂ) • J k colH (-3) (J k colH (-1) (vacuumA k))
        + (-64 : ℂ) • J k colF (-2) (J k colE (-1) (J k colH (-1) (vacuumA k)))
        + (24 : ℂ) • J k colE (-1) (J k colF (-1) (J k colH (-1) (
          J k colH (-1) (vacuumA k))))
        + (k) • J k colH (-1) (J k colH (-1) (J k colH (-1) (
          J k colH (-1) (vacuumA k)))) := by
  simp only [FEz k (1) (-1) (by norm_num) (J k colH (-1) (J k colH (-1) 
      (J k colH (-1) ( J k colH (-1) (vacuumA k))))),
    actFp1_H1H1H1H1, preE1_F3, preE1_F2H1, actHp0_H1H1H1H1, map_add, map_smul, zero_smul]
  push_cast
  try module

/-- Cartan charge of `E1H1H1H1H1` is `2`. -/
theorem actHp0_E1H1H1H1H1 (k : ℂ) :
    J k colH (0) (J k colE (-1) (J k colH (-1) (J k colH (-1) (J k colH (-1) (
      J k colH (-1) (vacuumA k))))))
      = (2 : ℂ) • J k colE (-1) (J k colH (-1) (J k colH (-1) (J k colH (-1) (
        J k colH (-1) (vacuumA k))))) := by
  have g1 := H0_H (-1) (by norm_num) (H0_vac k)
  have g2 := H0_H (-1) (by norm_num) g1
  have g3 := H0_H (-1) (by norm_num) g2
  have g4 := H0_H (-1) (by norm_num) g3
  exact H0_E (-1) g4 (2 : ℂ) (by norm_num)

/-- Action of `e_{0}` on `F1H1H1`. -/
theorem actEp0_F1H1H1 (k : ℂ) :
    J k colE (0) (J k colF (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))))
      = (4 : ℂ) • J k colH (-3) (vacuumA k)
        + (-4 : ℂ) • J k colE (-2) (J k colF (-1) (vacuumA k))
        + (4 : ℂ) • J k colH (-2) (J k colH (-1) (vacuumA k))
        + (-4 : ℂ) • J k colE (-1) (J k colF (-1) (J k colH (-1) (vacuumA k)))
        + J k colH (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))) := by
  simp only [EFs k (0) (-1) (-1) (by norm_num) (by norm_num) 
      (J k colH (-1) ( J k colH (-1) (vacuumA k))),
    actEp0_H1H1, preF1_E2, preF1_E1H1, map_add, map_smul]
  try module

/-- Action of `e_{0}` on `E1F1H1H1`. -/
theorem actEp0_E1F1H1H1 (k : ℂ) :
    J k colE (0) (J k colE (-1) (J k colF (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))))
      = (-8 : ℂ) • J k colE (-4) (vacuumA k)
        + (-8 : ℂ) • J k colE (-3) (J k colH (-1) (vacuumA k))
        + (4 : ℂ) • J k colH (-3) (J k colE (-1) (vacuumA k))
        + (-4 : ℂ) • J k colE (-2) (J k colE (-1) (J k colF (-1) (vacuumA k)))
        + (4 : ℂ) • J k colH (-2) (J k colE (-1) (J k colH (-1) (vacuumA k)))
        + (-4 : ℂ) • J k colE (-1) (J k colE (-1) (J k colF (-1) (
          J k colH (-1) (vacuumA k))))
        + J k colE (-1) (J k colH (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))) := by
  simp only [EEs k (0) (-1) (J k colF (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))),
    actEp0_F1H1H1, preE1_H3, preE1_E2F1, preE1_H2H1, map_add, map_smul]
  try module

/-- Action of `e_{0}` on `E1E1F1H1H1`. -/
theorem actEp0_E1E1F1H1H1 (k : ℂ) :
    J k colE (0) (J k colE (-1) (J k colE (-1) (J k colF (-1) (J k colH (-1) (
      J k colH (-1) (vacuumA k))))))
      = (-16 : ℂ) • J k colE (-4) (J k colE (-1) (vacuumA k))
        + (-16 : ℂ) • J k colE (-3) (J k colE (-1) (J k colH (-1) (vacuumA k)))
        + (4 : ℂ) • J k colH (-3) (J k colE (-1) (J k colE (-1) (vacuumA k)))
        + (-4 : ℂ) • J k colE (-2) (J k colE (-1) (J k colE (-1) (
          J k colF (-1) (vacuumA k))))
        + (4 : ℂ) • J k colH (-2) (J k colE (-1) (J k colE (-1) (
          J k colH (-1) (vacuumA k))))
        + (-4 : ℂ) • J k colE (-1) (J k colE (-1) (J k colE (-1) (J k colF (-1) (
          J k colH (-1) (vacuumA k)))))
        + J k colE (-1) (J k colE (-1) (J k colH (-1) (J k colH (-1) (
          J k colH (-1) (vacuumA k))))) := by
  simp only [EEs k (0) (-1) (J k colE (-1) (J k colF (-1) 
      (J k colH (-1) ( J k colH (-1) (vacuumA k))))),
    actEp0_E1F1H1H1, preE1_E4, preE1_E3H1, preE1_H3E1, preE1_E2E1F1, preE1_H2E1H1, map_add,
    map_smul]
  try module

/-- Action of `f_{1}` on `F1H1H1`. -/
theorem actFp1_F1H1H1 (k : ℂ) :
    J k colF (1) (J k colF (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))))
      = (4 : ℂ) • J k colF (-1) (J k colF (-1) (vacuumA k)) := by
  simp only [FFs k (1) (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))), actFp1_H1H1, map_smul]
  try module

/-- Cartan charge of `F1H1H1` is `-2`. -/
theorem actHp0_F1H1H1 (k : ℂ) :
    J k colH (0) (J k colF (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))))
      = (-2 : ℂ) • J k colF (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))) := by
  have g1 := H0_H (-1) (by norm_num) (H0_vac k)
  have g2 := H0_H (-1) (by norm_num) g1
  exact H0_F (-1) g2 (-2 : ℂ) (by norm_num)

/-- Action of `f_{1}` on `E1F1H1H1`. -/
theorem actFp1_E1F1H1H1 (k : ℂ) :
    J k colF (1) (J k colE (-1) (J k colF (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))))
      = (4 : ℂ) • J k colE (-1) (J k colF (-1) (J k colF (-1) (vacuumA k))) + (k
        + 2) • J k colF (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))) := by
  simp only [FEz k (1) (-1) (by norm_num) (J k colF (-1) 
      (J k colH (-1) ( J k colH (-1) (vacuumA k)))),
    actFp1_F1H1H1, actHp0_F1H1H1, map_smul]
  push_cast
  try module

/-- Cartan charge of `E1F1H1H1` is `0`. -/
theorem actHp0_E1F1H1H1 (k : ℂ) :
    J k colH (0) (J k colE (-1) (J k colF (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))))
      = (0 : ℂ) • J k colE (-1) (J k colF (-1) (J k colH (-1) (
        J k colH (-1) (vacuumA k)))) := by
  have g1 := H0_H (-1) (by norm_num) (H0_vac k)
  have g2 := H0_H (-1) (by norm_num) g1
  have g3 := H0_F (-1) g2 (-2 : ℂ) (by norm_num)
  exact H0_E (-1) g3 (0 : ℂ) (by norm_num)

/-- Action of `f_{1}` on `E1E1F1H1H1`. -/
theorem actFp1_E1E1F1H1H1 (k : ℂ) :
    J k colF (1) (J k colE (-1) (J k colE (-1) (J k colF (-1) (J k colH (-1) (
      J k colH (-1) (vacuumA k))))))
      = (4 : ℂ) • J k colE (-1) (J k colE (-1) (J k colF (-1) (
          J k colF (-1) (vacuumA k))))
        + (2*k
        + 2) • J k colE (-1) (J k colF (-1) (J k colH (-1) (
          J k colH (-1) (vacuumA k)))) := by
  simp only [FEz k (1) (-1) (by norm_num) (J k colE (-1) (J k colF (-1) 
      (J k colH (-1) ( J k colH (-1) (vacuumA k))))),
    actFp1_E1F1H1H1, actHp0_E1F1H1H1, map_add, map_smul, zero_smul]
  push_cast
  try module

/-- Cartan charge of `E1E1F1H1H1` is `2`. -/
theorem actHp0_E1E1F1H1H1 (k : ℂ) :
    J k colH (0) (J k colE (-1) (J k colE (-1) (J k colF (-1) (J k colH (-1) (
      J k colH (-1) (vacuumA k))))))
      = (2 : ℂ) • J k colE (-1) (J k colE (-1) (J k colF (-1) (J k colH (-1) (
        J k colH (-1) (vacuumA k))))) := by
  have g1 := H0_H (-1) (by norm_num) (H0_vac k)
  have g2 := H0_H (-1) (by norm_num) g1
  have g3 := H0_F (-1) g2 (-2 : ℂ) (by norm_num)
  have g4 := H0_E (-1) g3 (0 : ℂ) (by norm_num)
  exact H0_E (-1) g4 (2 : ℂ) (by norm_num)

/-- Action of `e_{0}` on `F1`. -/
theorem actEp0_F1 (k : ℂ) :
    J k colE (0) (J k colF (-1) (vacuumA k))
      = J k colH (-1) (vacuumA k) := by
  simp only [EFs k (0) (-1) (-1) (by norm_num) (by norm_num) (vacuumA k), E_vac0, map_zero,
    zero_add]
  try module

/-- Action of `e_{0}` on `F1F1`. -/
theorem actEp0_F1F1 (k : ℂ) :
    J k colE (0) (J k colF (-1) (J k colF (-1) (vacuumA k)))
      = (-2 : ℂ) • J k colF (-2) (vacuumA k)
        + (2 : ℂ) • J k colF (-1) (J k colH (-1) (vacuumA k)) := by
  simp only [EFs k (0) (-1) (-1) (by norm_num) (by norm_num) (J k colF (-1) (vacuumA k)),
    actEp0_F1, preH1_F1]
  try module

/-- Action of `e_{0}` on `E1F1F1`. -/
theorem actEp0_E1F1F1 (k : ℂ) :
    J k colE (0) (J k colE (-1) (J k colF (-1) (J k colF (-1) (vacuumA k))))
      = (-2 : ℂ) • J k colH (-3) (vacuumA k)
        + (-2 : ℂ) • J k colF (-2) (J k colE (-1) (vacuumA k))
        + (2 : ℂ) • J k colE (-1) (J k colF (-1) (J k colH (-1) (vacuumA k))) := by
  simp only [EEs k (0) (-1) (J k colF (-1) (J k colF (-1) (vacuumA k))), actEp0_F1F1, preE1_F2,
    map_add, map_smul]
  try module

/-- Action of `e_{0}` on `E1E1F1F1`. -/
theorem actEp0_E1E1F1F1 (k : ℂ) :
    J k colE (0) (J k colE (-1) (J k colE (-1) (J k colF (-1) (J k colF (-1) (vacuumA k)))))
      = (4 : ℂ) • J k colE (-4) (vacuumA k)
        + (-4 : ℂ) • J k colH (-3) (J k colE (-1) (vacuumA k))
        + (-2 : ℂ) • J k colF (-2) (J k colE (-1) (J k colE (-1) (vacuumA k)))
        + (2 : ℂ) • J k colE (-1) (J k colE (-1) (J k colF (-1) (
          J k colH (-1) (vacuumA k)))) := by
  simp only [EEs k (0) (-1) (J k colE (-1) (J k colF (-1) (J k colF (-1) (vacuumA k)))),
    actEp0_E1F1F1, preE1_H3, preE1_F2E1, map_add, map_smul]
  try module

/-- Action of `e_{0}` on `E1E1E1F1F1`. -/
theorem actEp0_E1E1E1F1F1 (k : ℂ) :
    J k colE (0) (J k colE (-1) (J k colE (-1) (J k colE (-1) (J k colF (-1) (
      J k colF (-1) (vacuumA k))))))
      = (12 : ℂ) • J k colE (-4) (J k colE (-1) (vacuumA k))
        + (-6 : ℂ) • J k colH (-3) (J k colE (-1) (J k colE (-1) (vacuumA k)))
        + (-2 : ℂ) • J k colF (-2) (J k colE (-1) (J k colE (-1) (
          J k colE (-1) (vacuumA k))))
        + (2 : ℂ) • J k colE (-1) (J k colE (-1) (J k colE (-1) (J k colF (-1) (
          J k colH (-1) (vacuumA k))))) := by
  simp only [EEs k (0) (-1) (J k colE (-1) (J k colE (-1) 
      (J k colF (-1) ( J k colF (-1) (vacuumA k))))),
    actEp0_E1E1F1F1, preE1_E4, preE1_H3E1, preE1_F2E1E1, map_add, map_smul]
  try module

/-- Action of `f_{1}` on `F1`. -/
theorem actFp1_F1 (k : ℂ) :
    J k colF (1) (J k colF (-1) (vacuumA k))
      = 0 := by
  simp only [FFs k (1) (-1) (vacuumA k), F_vac1, map_zero]
  try module

/-- Action of `f_{1}` on `F1F1`. -/
theorem actFp1_F1F1 (k : ℂ) :
    J k colF (1) (J k colF (-1) (J k colF (-1) (vacuumA k)))
      = 0 := by
  simp only [FFs k (1) (-1) (J k colF (-1) (vacuumA k)), actFp1_F1, map_zero]
  try module

/-- Cartan charge of `F1` is `-2`. -/
theorem actHp0_F1 (k : ℂ) :
    J k colH (0) (J k colF (-1) (vacuumA k))
      = (-2 : ℂ) • J k colF (-1) (vacuumA k) := by
  exact H0_F (-1) (H0_vac k) (-2 : ℂ) (by norm_num)

/-- Cartan charge of `F1F1` is `-4`. -/
theorem actHp0_F1F1 (k : ℂ) :
    J k colH (0) (J k colF (-1) (J k colF (-1) (vacuumA k)))
      = (-4 : ℂ) • J k colF (-1) (J k colF (-1) (vacuumA k)) := by
  have g1 := H0_F (-1) (H0_vac k) (-2 : ℂ) (by norm_num)
  exact H0_F (-1) g1 (-4 : ℂ) (by norm_num)

/-- Action of `f_{1}` on `E1F1F1`. -/
theorem actFp1_E1F1F1 (k : ℂ) :
    J k colF (1) (J k colE (-1) (J k colF (-1) (J k colF (-1) (vacuumA k))))
      = (k + 4) • J k colF (-1) (J k colF (-1) (vacuumA k)) := by
  simp only [FEz k (1) (-1) (by norm_num) (J k colF (-1) (J k colF (-1) (vacuumA k))),
    actFp1_F1F1, actHp0_F1F1, map_zero]
  push_cast
  try module

/-- Cartan charge of `E1F1F1` is `-2`. -/
theorem actHp0_E1F1F1 (k : ℂ) :
    J k colH (0) (J k colE (-1) (J k colF (-1) (J k colF (-1) (vacuumA k))))
      = (-2 : ℂ) • J k colE (-1) (J k colF (-1) (J k colF (-1) (vacuumA k))) := by
  have g1 := H0_F (-1) (H0_vac k) (-2 : ℂ) (by norm_num)
  have g2 := H0_F (-1) g1 (-4 : ℂ) (by norm_num)
  exact H0_E (-1) g2 (-2 : ℂ) (by norm_num)

/-- Action of `f_{1}` on `E1E1F1F1`. -/
theorem actFp1_E1E1F1F1 (k : ℂ) :
    J k colF (1) (J k colE (-1) (J k colE (-1) (J k colF (-1) (J k colF (-1) (vacuumA k)))))
      = (2*k + 6) • J k colE (-1) (J k colF (-1) (J k colF (-1) (vacuumA k))) := by
  simp only [FEz k (1) (-1) (by norm_num) (J k colE (-1) 
      (J k colF (-1) ( J k colF (-1) (vacuumA k)))),
    actFp1_E1F1F1, actHp0_E1F1F1, map_smul]
  push_cast
  try module

/-- Cartan charge of `E1E1F1F1` is `0`. -/
theorem actHp0_E1E1F1F1 (k : ℂ) :
    J k colH (0) (J k colE (-1) (J k colE (-1) (J k colF (-1) (J k colF (-1) (vacuumA k)))))
      = (0 : ℂ) • J k colE (-1) (J k colE (-1) (J k colF (-1) (
        J k colF (-1) (vacuumA k)))) := by
  have g1 := H0_F (-1) (H0_vac k) (-2 : ℂ) (by norm_num)
  have g2 := H0_F (-1) g1 (-4 : ℂ) (by norm_num)
  have g3 := H0_E (-1) g2 (-2 : ℂ) (by norm_num)
  exact H0_E (-1) g3 (0 : ℂ) (by norm_num)

/-- Action of `f_{1}` on `E1E1E1F1F1`. -/
theorem actFp1_E1E1E1F1F1 (k : ℂ) :
    J k colF (1) (J k colE (-1) (J k colE (-1) (J k colE (-1) (J k colF (-1) (
      J k colF (-1) (vacuumA k))))))
      = (3*k
        + 6) • J k colE (-1) (J k colE (-1) (J k colF (-1) (
          J k colF (-1) (vacuumA k)))) := by
  simp only [FEz k (1) (-1) (by norm_num) (J k colE (-1) (J k colE (-1) 
      (J k colF (-1) ( J k colF (-1) (vacuumA k))))),
    actFp1_E1E1F1F1, actHp0_E1E1F1F1, map_smul, zero_smul]
  push_cast
  try module

/-- Cartan charge of `E1E1E1F1F1` is `2`. -/
theorem actHp0_E1E1E1F1F1 (k : ℂ) :
    J k colH (0) (J k colE (-1) (J k colE (-1) (J k colE (-1) (J k colF (-1) (
      J k colF (-1) (vacuumA k))))))
      = (2 : ℂ) • J k colE (-1) (J k colE (-1) (J k colE (-1) (J k colF (-1) (
        J k colF (-1) (vacuumA k))))) := by
  have g1 := H0_F (-1) (H0_vac k) (-2 : ℂ) (by norm_num)
  have g2 := H0_F (-1) g1 (-4 : ℂ) (by norm_num)
  have g3 := H0_E (-1) g2 (-2 : ℂ) (by norm_num)
  have g4 := H0_E (-1) g3 (0 : ℂ) (by norm_num)
  exact H0_E (-1) g4 (2 : ℂ) (by norm_num)

/-- Action of `e_{0}` on `E1H1H1`. -/
theorem actEp0_E1H1H1 (k : ℂ) :
    J k colE (0) (J k colE (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))))
      = (-4 : ℂ) • J k colE (-2) (J k colE (-1) (vacuumA k))
        + (-4 : ℂ) • J k colE (-1) (J k colE (-1) (J k colH (-1) (vacuumA k))) := by
  simp only [EEs k (0) (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))), actEp0_H1H1, preE1_E2,
    map_add, map_smul]
  try module

/-- Action of `e_{0}` on `H2E1H1H1`. -/
theorem actEp0_H2E1H1H1 (k : ℂ) :
    J k colE (0) (J k colH (-2) (J k colE (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))))
      = (-8 : ℂ) • J k colE (-4) (J k colE (-1) (vacuumA k))
        + (-4 : ℂ) • J k colE (-2) (J k colH (-2) (J k colE (-1) (vacuumA k)))
        + (-2 : ℂ) • J k colE (-2) (J k colE (-1) (J k colH (-1) (
          J k colH (-1) (vacuumA k))))
        + (-4 : ℂ) • J k colH (-2) (J k colE (-1) (J k colE (-1) (
          J k colH (-1) (vacuumA k)))) := by
  simp only [EHs k (0) (-2) (-2) (by norm_num) (J k colE (-1) 
      (J k colH (-1) ( J k colH (-1) (vacuumA k)))),
    actEp0_E1H1H1, preH2_E2E1, map_add, map_smul]
  try module

/-- Action of `f_{1}` on `E1H1H1`. -/
theorem actFp1_E1H1H1 (k : ℂ) :
    J k colF (1) (J k colE (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))))
      = (4 : ℂ) • J k colE (-1) (J k colF (-1) (vacuumA k))
        + (k) • J k colH (-1) (J k colH (-1) (vacuumA k)) := by
  simp only [FEz k (1) (-1) (by norm_num) (J k colH (-1) (J k colH (-1) (vacuumA k))),
    actFp1_H1H1, actHp0_H1H1, map_smul, zero_smul]
  push_cast
  try module

/-- Action of `f_{1}` on `H2E1H1H1`. -/
theorem actFp1_H2E1H1H1 (k : ℂ) :
    J k colF (1) (J k colH (-2) (J k colE (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))))
      = (4 : ℂ) • J k colH (-2) (J k colE (-1) (J k colF (-1) (vacuumA k)))
        + (k - 2) • J k colH (-2) (J k colH (-1) (J k colH (-1) (vacuumA k)))
        + (2 : ℂ) • J k colE (-1) (J k colF (-1) (J k colH (-1) (
          J k colH (-1) (vacuumA k)))) := by
  simp only [FHs k (1) (-2) (-1) (by norm_num) (J k colE (-1) 
      (J k colH (-1) ( J k colH (-1) (vacuumA k)))),
    actFp1_E1H1H1, preF1_E1H1H1, map_add, map_smul]
  try module

/-- Cartan charge of `E1H1H1` is `2`. -/
theorem actHp0_E1H1H1 (k : ℂ) :
    J k colH (0) (J k colE (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))))
      = (2 : ℂ) • J k colE (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))) := by
  have g1 := H0_H (-1) (by norm_num) (H0_vac k)
  have g2 := H0_H (-1) (by norm_num) g1
  exact H0_E (-1) g2 (2 : ℂ) (by norm_num)

/-- Cartan charge of `H2E1H1H1` is `2`. -/
theorem actHp0_H2E1H1H1 (k : ℂ) :
    J k colH (0) (J k colH (-2) (J k colE (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))))
      = (2 : ℂ) • J k colH (-2) (J k colE (-1) (J k colH (-1) (
        J k colH (-1) (vacuumA k)))) := by
  have g1 := H0_H (-1) (by norm_num) (H0_vac k)
  have g2 := H0_H (-1) (by norm_num) g1
  have g3 := H0_E (-1) g2 (2 : ℂ) (by norm_num)
  exact H0_H (-2) (by norm_num) g3

/-- Action of `e_{0}` on `E1F1`. -/
theorem actEp0_E1F1 (k : ℂ) :
    J k colE (0) (J k colE (-1) (J k colF (-1) (vacuumA k)))
      = J k colE (-1) (J k colH (-1) (vacuumA k)) := by
  simp only [EEs k (0) (-1) (J k colF (-1) (vacuumA k)), actEp0_F1]
  try module

/-- Action of `e_{0}` on `E1E1F1`. -/
theorem actEp0_E1E1F1 (k : ℂ) :
    J k colE (0) (J k colE (-1) (J k colE (-1) (J k colF (-1) (vacuumA k))))
      = J k colE (-1) (J k colE (-1) (J k colH (-1) (vacuumA k))) := by
  simp only [EEs k (0) (-1) (J k colE (-1) (J k colF (-1) (vacuumA k))), actEp0_E1F1]
  try module

/-- Action of `e_{0}` on `H2E1E1F1`. -/
theorem actEp0_H2E1E1F1 (k : ℂ) :
    J k colE (0) (J k colH (-2) (J k colE (-1) (J k colE (-1) (J k colF (-1) (vacuumA k)))))
      = (-2 : ℂ) • J k colE (-2) (J k colE (-1) (J k colE (-1) (
          J k colF (-1) (vacuumA k))))
        + J k colH (-2) (J k colE (-1) (J k colE (-1) (J k colH (-1) (vacuumA k)))) := by
  simp only [EHs k (0) (-2) (-2) (by norm_num) (J k colE (-1) 
      (J k colE (-1) ( J k colF (-1) (vacuumA k)))),
    actEp0_E1E1F1]
  try module

/-- Action of `f_{1}` on `E1F1`. -/
theorem actFp1_E1F1 (k : ℂ) :
    J k colF (1) (J k colE (-1) (J k colF (-1) (vacuumA k)))
      = (k + 2) • J k colF (-1) (vacuumA k) := by
  simp only [FEz k (1) (-1) (by norm_num) (J k colF (-1) (vacuumA k)), actFp1_F1, actHp0_F1,
    map_zero]
  push_cast
  try module

/-- Cartan charge of `E1F1` is `0`. -/
theorem actHp0_E1F1 (k : ℂ) :
    J k colH (0) (J k colE (-1) (J k colF (-1) (vacuumA k)))
      = (0 : ℂ) • J k colE (-1) (J k colF (-1) (vacuumA k)) := by
  have g1 := H0_F (-1) (H0_vac k) (-2 : ℂ) (by norm_num)
  exact H0_E (-1) g1 (0 : ℂ) (by norm_num)

/-- Action of `f_{1}` on `E1E1F1`. -/
theorem actFp1_E1E1F1 (k : ℂ) :
    J k colF (1) (J k colE (-1) (J k colE (-1) (J k colF (-1) (vacuumA k))))
      = (2*k + 2) • J k colE (-1) (J k colF (-1) (vacuumA k)) := by
  simp only [FEz k (1) (-1) (by norm_num) (J k colE (-1) (J k colF (-1) (vacuumA k))),
    actFp1_E1F1, actHp0_E1F1, map_smul, zero_smul]
  push_cast
  try module

/-- Action of `f_{1}` on `H2E1E1F1`. -/
theorem actFp1_H2E1E1F1 (k : ℂ) :
    J k colF (1) (J k colH (-2) (J k colE (-1) (J k colE (-1) (J k colF (-1) (vacuumA k)))))
      = (4 : ℂ) • J k colE (-3) (J k colF (-1) (vacuumA k))
        + (2*k - 2) • J k colH (-2) (J k colE (-1) (J k colF (-1) (vacuumA k)))
        + (2 : ℂ) • J k colE (-1) (J k colE (-1) (J k colF (-1) (
          J k colF (-1) (vacuumA k)))) := by
  simp only [FHs k (1) (-2) (-1) (by norm_num) (J k colE (-1) 
      (J k colE (-1) ( J k colF (-1) (vacuumA k)))),
    actFp1_E1E1F1, preF1_E1E1F1, map_smul]
  try module

/-- Cartan charge of `E1E1F1` is `2`. -/
theorem actHp0_E1E1F1 (k : ℂ) :
    J k colH (0) (J k colE (-1) (J k colE (-1) (J k colF (-1) (vacuumA k))))
      = (2 : ℂ) • J k colE (-1) (J k colE (-1) (J k colF (-1) (vacuumA k))) := by
  have g1 := H0_F (-1) (H0_vac k) (-2 : ℂ) (by norm_num)
  have g2 := H0_E (-1) g1 (0 : ℂ) (by norm_num)
  exact H0_E (-1) g2 (2 : ℂ) (by norm_num)

/-- Cartan charge of `H2E1E1F1` is `2`. -/
theorem actHp0_H2E1E1F1 (k : ℂ) :
    J k colH (0) (J k colH (-2) (J k colE (-1) (J k colE (-1) (J k colF (-1) (vacuumA k)))))
      = (2 : ℂ) • J k colH (-2) (J k colE (-1) (J k colE (-1) (
        J k colF (-1) (vacuumA k)))) := by
  have g1 := H0_F (-1) (H0_vac k) (-2 : ℂ) (by norm_num)
  have g2 := H0_E (-1) g1 (0 : ℂ) (by norm_num)
  have g3 := H0_E (-1) g2 (2 : ℂ) (by norm_num)
  exact H0_H (-2) (by norm_num) g3

/-- Action of `e_{0}` on `E1`. -/
theorem actEp0_E1 (k : ℂ) :
    J k colE (0) (J k colE (-1) (vacuumA k))
      = 0 := by
  simp only [EEs k (0) (-1) (vacuumA k), E_vac0, map_zero]
  try module

/-- Action of `e_{0}` on `H2E1`. -/
theorem actEp0_H2E1 (k : ℂ) :
    J k colE (0) (J k colH (-2) (J k colE (-1) (vacuumA k)))
      = (-2 : ℂ) • J k colE (-2) (J k colE (-1) (vacuumA k)) := by
  simp only [EHs k (0) (-2) (-2) (by norm_num) (J k colE (-1) (vacuumA k)), actEp0_E1, map_zero]
  try module

/-- Action of `e_{0}` on `H2H2E1`. -/
theorem actEp0_H2H2E1 (k : ℂ) :
    J k colE (0) (J k colH (-2) (J k colH (-2) (J k colE (-1) (vacuumA k))))
      = (-4 : ℂ) • J k colE (-4) (J k colE (-1) (vacuumA k))
        + (-4 : ℂ) • J k colE (-2) (J k colH (-2) (J k colE (-1) (vacuumA k))) := by
  simp only [EHs k (0) (-2) (-2) (by norm_num) (J k colH (-2) (J k colE (-1) (vacuumA k))),
    actEp0_H2E1, preH2_E2E1, map_smul]
  try module

/-- Action of `f_{1}` on `E1`. -/
theorem actFp1_E1 (k : ℂ) :
    J k colF (1) (J k colE (-1) (vacuumA k))
      = (k) • vacuumA k := by
  simp only [FEz k (1) (-1) (by norm_num) (vacuumA k), F_vac1, H_vac0, map_zero]
  push_cast
  try module

/-- Action of `f_{1}` on `H2E1`. -/
theorem actFp1_H2E1 (k : ℂ) :
    J k colF (1) (J k colH (-2) (J k colE (-1) (vacuumA k)))
      = (k - 2) • J k colH (-2) (vacuumA k)
        + (2 : ℂ) • J k colE (-1) (J k colF (-1) (vacuumA k)) := by
  simp only [FHs k (1) (-2) (-1) (by norm_num) (J k colE (-1) (vacuumA k)), actFp1_E1,
    preF1_E1, map_smul]
  try module

/-- Action of `f_{1}` on `H2H2E1`. -/
theorem actFp1_H2H2E1 (k : ℂ) :
    J k colF (1) (J k colH (-2) (J k colH (-2) (J k colE (-1) (vacuumA k))))
      = (4 : ℂ) • J k colF (-3) (J k colE (-1) (vacuumA k))
        + (k - 4) • J k colH (-2) (J k colH (-2) (vacuumA k))
        + (4 : ℂ) • J k colH (-2) (J k colE (-1) (J k colF (-1) (vacuumA k))) := by
  simp only [FHs k (1) (-2) (-1) (by norm_num) (J k colH (-2) (J k colE (-1) (vacuumA k))),
    actFp1_H2E1, preF1_H2E1, map_add, map_smul]
  try module

/-- Cartan charge of `E1` is `2`. -/
theorem actHp0_E1 (k : ℂ) :
    J k colH (0) (J k colE (-1) (vacuumA k))
      = (2 : ℂ) • J k colE (-1) (vacuumA k) := by
  exact H0_E (-1) (H0_vac k) (2 : ℂ) (by norm_num)

/-- Cartan charge of `H2E1` is `2`. -/
theorem actHp0_H2E1 (k : ℂ) :
    J k colH (0) (J k colH (-2) (J k colE (-1) (vacuumA k)))
      = (2 : ℂ) • J k colH (-2) (J k colE (-1) (vacuumA k)) := by
  have g1 := H0_E (-1) (H0_vac k) (2 : ℂ) (by norm_num)
  exact H0_H (-2) (by norm_num) g1

/-- Cartan charge of `H2H2E1` is `2`. -/
theorem actHp0_H2H2E1 (k : ℂ) :
    J k colH (0) (J k colH (-2) (J k colH (-2) (J k colE (-1) (vacuumA k))))
      = (2 : ℂ) • J k colH (-2) (J k colH (-2) (J k colE (-1) (vacuumA k))) := by
  have g1 := H0_E (-1) (H0_vac k) (2 : ℂ) (by norm_num)
  have g2 := H0_H (-2) (by norm_num) g1
  exact H0_H (-2) (by norm_num) g2

/-- Action of `e_{0}` on `E1H1`. -/
theorem actEp0_E1H1 (k : ℂ) :
    J k colE (0) (J k colE (-1) (J k colH (-1) (vacuumA k)))
      = (-2 : ℂ) • J k colE (-1) (J k colE (-1) (vacuumA k)) := by
  simp only [EEs k (0) (-1) (J k colH (-1) (vacuumA k)), actEp0_H1, map_smul]
  try module

/-- Action of `e_{0}` on `E1E1H1`. -/
theorem actEp0_E1E1H1 (k : ℂ) :
    J k colE (0) (J k colE (-1) (J k colE (-1) (J k colH (-1) (vacuumA k))))
      = (-2 : ℂ) • J k colE (-1) (J k colE (-1) (J k colE (-1) (vacuumA k))) := by
  simp only [EEs k (0) (-1) (J k colE (-1) (J k colH (-1) (vacuumA k))), actEp0_E1H1, map_smul]
  try module

/-- Action of `e_{0}` on `F2E1E1H1`. -/
theorem actEp0_F2E1E1H1 (k : ℂ) :
    J k colE (0) (J k colF (-2) (J k colE (-1) (J k colE (-1) (J k colH (-1) (vacuumA k)))))
      = (-2 : ℂ) • J k colF (-2) (J k colE (-1) (J k colE (-1) (
          J k colE (-1) (vacuumA k))))
        + J k colH (-2) (J k colE (-1) (J k colE (-1) (J k colH (-1) (vacuumA k)))) := by
  simp only [EFs k (0) (-2) (-2) (by norm_num) (by norm_num) (J k colE (-1) 
      (J k colE (-1) ( J k colH (-1) (vacuumA k)))),
    actEp0_E1E1H1, map_smul]
  try module

/-- Action of `f_{1}` on `E1H1`. -/
theorem actFp1_E1H1 (k : ℂ) :
    J k colF (1) (J k colE (-1) (J k colH (-1) (vacuumA k)))
      = (k) • J k colH (-1) (vacuumA k) := by
  simp only [FEz k (1) (-1) (by norm_num) (J k colH (-1) (vacuumA k)), actFp1_H1, actHp0_H1,
    map_zero, zero_smul]
  push_cast
  try module

/-- Cartan charge of `E1H1` is `2`. -/
theorem actHp0_E1H1 (k : ℂ) :
    J k colH (0) (J k colE (-1) (J k colH (-1) (vacuumA k)))
      = (2 : ℂ) • J k colE (-1) (J k colH (-1) (vacuumA k)) := by
  have g1 := H0_H (-1) (by norm_num) (H0_vac k)
  exact H0_E (-1) g1 (2 : ℂ) (by norm_num)

/-- Action of `f_{1}` on `E1E1H1`. -/
theorem actFp1_E1E1H1 (k : ℂ) :
    J k colF (1) (J k colE (-1) (J k colE (-1) (J k colH (-1) (vacuumA k))))
      = (2*k - 2) • J k colE (-1) (J k colH (-1) (vacuumA k)) := by
  simp only [FEz k (1) (-1) (by norm_num) (J k colE (-1) (J k colH (-1) (vacuumA k))),
    actFp1_E1H1, actHp0_E1H1, map_smul]
  push_cast
  try module

/-- Action of `f_{1}` on `F2E1E1H1`. -/
theorem actFp1_F2E1E1H1 (k : ℂ) :
    J k colF (1) (J k colF (-2) (J k colE (-1) (J k colE (-1) (J k colH (-1) (vacuumA k)))))
      = (2*k - 2) • J k colF (-2) (J k colE (-1) (J k colH (-1) (vacuumA k))) := by
  simp only [FFs k (1) (-2) (J k colE (-1) (J k colE (-1) (J k colH (-1) (vacuumA k)))),
    actFp1_E1E1H1, map_smul]
  try module

/-- Cartan charge of `E1E1H1` is `4`. -/
theorem actHp0_E1E1H1 (k : ℂ) :
    J k colH (0) (J k colE (-1) (J k colE (-1) (J k colH (-1) (vacuumA k))))
      = (4 : ℂ) • J k colE (-1) (J k colE (-1) (J k colH (-1) (vacuumA k))) := by
  have g1 := H0_H (-1) (by norm_num) (H0_vac k)
  have g2 := H0_E (-1) g1 (2 : ℂ) (by norm_num)
  exact H0_E (-1) g2 (4 : ℂ) (by norm_num)

/-- Cartan charge of `F2E1E1H1` is `2`. -/
theorem actHp0_F2E1E1H1 (k : ℂ) :
    J k colH (0) (J k colF (-2) (J k colE (-1) (J k colE (-1) (J k colH (-1) (vacuumA k)))))
      = (2 : ℂ) • J k colF (-2) (J k colE (-1) (J k colE (-1) (
        J k colH (-1) (vacuumA k)))) := by
  have g1 := H0_H (-1) (by norm_num) (H0_vac k)
  have g2 := H0_E (-1) g1 (2 : ℂ) (by norm_num)
  have g3 := H0_E (-1) g2 (4 : ℂ) (by norm_num)
  exact H0_F (-2) g3 (2 : ℂ) (by norm_num)

/-- Action of `e_{0}` on `E2H1H1H1`. -/
theorem actEp0_E2H1H1H1 (k : ℂ) :
    J k colE (0) (J k colE (-2) (J k colH (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))))
      = (-8 : ℂ) • J k colE (-3) (J k colE (-2) (vacuumA k))
        + (-12 : ℂ) • J k colE (-2) (J k colE (-2) (J k colH (-1) (vacuumA k)))
        + (-6 : ℂ) • J k colE (-2) (J k colE (-1) (J k colH (-1) (
          J k colH (-1) (vacuumA k)))) := by
  simp only [EEs k (0) (-2) (J k colH (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))),
    actEp0_H1H1H1, preE2_E3, map_add, map_smul]
  try module

/-- Action of `f_{1}` on `E2H1H1H1`. -/
theorem actFp1_E2H1H1H1 (k : ℂ) :
    J k colF (1) (J k colE (-2) (J k colH (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))))
      = (-16 : ℂ) • J k colE (-2) (J k colF (-2) (vacuumA k))
        + (12 : ℂ) • J k colE (-2) (J k colF (-1) (J k colH (-1) (vacuumA k)))
        + (-1 : ℂ) • J k colH (-1) (J k colH (-1) (J k colH (-1) (
          J k colH (-1) (vacuumA k)))) := by
  simp only [FEs k (1) (-2) (-1) (by norm_num) (by norm_num) (J k colH (-1) 
      (J k colH (-1) ( J k colH (-1) (vacuumA k)))),
    actFp1_H1H1H1, map_add, map_smul]
  try module

/-- Cartan charge of `E2H1H1H1` is `2`. -/
theorem actHp0_E2H1H1H1 (k : ℂ) :
    J k colH (0) (J k colE (-2) (J k colH (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))))
      = (2 : ℂ) • J k colE (-2) (J k colH (-1) (J k colH (-1) (
        J k colH (-1) (vacuumA k)))) := by
  have g1 := H0_H (-1) (by norm_num) (H0_vac k)
  have g2 := H0_H (-1) (by norm_num) g1
  have g3 := H0_H (-1) (by norm_num) g2
  exact H0_E (-2) g3 (2 : ℂ) (by norm_num)

/-- Action of `e_{0}` on `F1H1`. -/
theorem actEp0_F1H1 (k : ℂ) :
    J k colE (0) (J k colF (-1) (J k colH (-1) (vacuumA k)))
      = (2 : ℂ) • J k colH (-2) (vacuumA k)
        + (-2 : ℂ) • J k colE (-1) (J k colF (-1) (vacuumA k))
        + J k colH (-1) (J k colH (-1) (vacuumA k)) := by
  simp only [EFs k (0) (-1) (-1) (by norm_num) (by norm_num) (J k colH (-1) (vacuumA k)),
    actEp0_H1, preF1_E1, map_smul]
  try module

/-- Action of `e_{0}` on `E1F1H1`. -/
theorem actEp0_E1F1H1 (k : ℂ) :
    J k colE (0) (J k colE (-1) (J k colF (-1) (J k colH (-1) (vacuumA k))))
      = (-4 : ℂ) • J k colE (-3) (vacuumA k)
        + (2 : ℂ) • J k colH (-2) (J k colE (-1) (vacuumA k))
        + (-2 : ℂ) • J k colE (-1) (J k colE (-1) (J k colF (-1) (vacuumA k)))
        + J k colE (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))) := by
  simp only [EEs k (0) (-1) (J k colF (-1) (J k colH (-1) (vacuumA k))), actEp0_F1H1, preE1_H2,
    map_add, map_smul]
  try module

/-- Action of `e_{0}` on `E2E1F1H1`. -/
theorem actEp0_E2E1F1H1 (k : ℂ) :
    J k colE (0) (J k colE (-2) (J k colE (-1) (J k colF (-1) (J k colH (-1) (vacuumA k)))))
      = (-4 : ℂ) • J k colE (-3) (J k colE (-2) (vacuumA k))
        + (2 : ℂ) • J k colE (-2) (J k colH (-2) (J k colE (-1) (vacuumA k)))
        + (-2 : ℂ) • J k colE (-2) (J k colE (-1) (J k colE (-1) (
          J k colF (-1) (vacuumA k))))
        + J k colE (-2) (J k colE (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))) := by
  simp only [EEs k (0) (-2) (J k colE (-1) (J k colF (-1) (J k colH (-1) (vacuumA k)))),
    actEp0_E1F1H1, preE2_E3, map_add, map_smul]
  try module

/-- Action of `f_{1}` on `F1H1`. -/
theorem actFp1_F1H1 (k : ℂ) :
    J k colF (1) (J k colF (-1) (J k colH (-1) (vacuumA k)))
      = 0 := by
  simp only [FFs k (1) (-1) (J k colH (-1) (vacuumA k)), actFp1_H1, map_zero]
  try module

/-- Cartan charge of `F1H1` is `-2`. -/
theorem actHp0_F1H1 (k : ℂ) :
    J k colH (0) (J k colF (-1) (J k colH (-1) (vacuumA k)))
      = (-2 : ℂ) • J k colF (-1) (J k colH (-1) (vacuumA k)) := by
  have g1 := H0_H (-1) (by norm_num) (H0_vac k)
  exact H0_F (-1) g1 (-2 : ℂ) (by norm_num)

/-- Action of `f_{1}` on `E1F1H1`. -/
theorem actFp1_E1F1H1 (k : ℂ) :
    J k colF (1) (J k colE (-1) (J k colF (-1) (J k colH (-1) (vacuumA k))))
      = (k + 2) • J k colF (-1) (J k colH (-1) (vacuumA k)) := by
  simp only [FEz k (1) (-1) (by norm_num) (J k colF (-1) (J k colH (-1) (vacuumA k))),
    actFp1_F1H1, actHp0_F1H1, map_zero]
  push_cast
  try module

/-- Action of `f_{1}` on `E2E1F1H1`. -/
theorem actFp1_E2E1F1H1 (k : ℂ) :
    J k colF (1) (J k colE (-2) (J k colE (-1) (J k colF (-1) (J k colH (-1) (vacuumA k)))))
      = (2 : ℂ) • J k colH (-3) (J k colH (-1) (vacuumA k))
        + (k) • J k colE (-2) (J k colF (-1) (J k colH (-1) (vacuumA k)))
        + (2 : ℂ) • J k colF (-2) (J k colE (-1) (J k colH (-1) (vacuumA k)))
        + (-1 : ℂ) • J k colE (-1) (J k colF (-1) (J k colH (-1) (
          J k colH (-1) (vacuumA k)))) := by
  simp only [FEs k (1) (-2) (-1) (by norm_num) (by norm_num) (J k colE (-1) 
      (J k colF (-1) ( J k colH (-1) (vacuumA k)))),
    actFp1_E1F1H1, preH1_E1F1H1, map_smul]
  try module

/-- Cartan charge of `E1F1H1` is `0`. -/
theorem actHp0_E1F1H1 (k : ℂ) :
    J k colH (0) (J k colE (-1) (J k colF (-1) (J k colH (-1) (vacuumA k))))
      = (0 : ℂ) • J k colE (-1) (J k colF (-1) (J k colH (-1) (vacuumA k))) := by
  have g1 := H0_H (-1) (by norm_num) (H0_vac k)
  have g2 := H0_F (-1) g1 (-2 : ℂ) (by norm_num)
  exact H0_E (-1) g2 (0 : ℂ) (by norm_num)

/-- Cartan charge of `E2E1F1H1` is `2`. -/
theorem actHp0_E2E1F1H1 (k : ℂ) :
    J k colH (0) (J k colE (-2) (J k colE (-1) (J k colF (-1) (J k colH (-1) (vacuumA k)))))
      = (2 : ℂ) • J k colE (-2) (J k colE (-1) (J k colF (-1) (
        J k colH (-1) (vacuumA k)))) := by
  have g1 := H0_H (-1) (by norm_num) (H0_vac k)
  have g2 := H0_F (-1) g1 (-2 : ℂ) (by norm_num)
  have g3 := H0_E (-1) g2 (0 : ℂ) (by norm_num)
  exact H0_E (-2) g3 (2 : ℂ) (by norm_num)

/-- Action of `e_{0}` on `H2H1`. -/
theorem actEp0_H2H1 (k : ℂ) :
    J k colE (0) (J k colH (-2) (J k colH (-1) (vacuumA k)))
      = (-2 : ℂ) • J k colE (-2) (J k colH (-1) (vacuumA k))
        + (-2 : ℂ) • J k colH (-2) (J k colE (-1) (vacuumA k)) := by
  simp only [EHs k (0) (-2) (-2) (by norm_num) (J k colH (-1) (vacuumA k)), actEp0_H1, map_smul]
  try module

/-- Action of `e_{0}` on `E2H2H1`. -/
theorem actEp0_E2H2H1 (k : ℂ) :
    J k colE (0) (J k colE (-2) (J k colH (-2) (J k colH (-1) (vacuumA k))))
      = (-2 : ℂ) • J k colE (-2) (J k colE (-2) (J k colH (-1) (vacuumA k)))
        + (-2 : ℂ) • J k colE (-2) (J k colH (-2) (J k colE (-1) (vacuumA k))) := by
  simp only [EEs k (0) (-2) (J k colH (-2) (J k colH (-1) (vacuumA k))), actEp0_H2H1, map_add,
    map_smul]
  try module

/-- Action of `f_{1}` on `H2H1`. -/
theorem actFp1_H2H1 (k : ℂ) :
    J k colF (1) (J k colH (-2) (J k colH (-1) (vacuumA k)))
      = (2 : ℂ) • J k colF (-1) (J k colH (-1) (vacuumA k)) := by
  simp only [FHs k (1) (-2) (-1) (by norm_num) (J k colH (-1) (vacuumA k)), actFp1_H1,
    map_zero, zero_add]
  try module

/-- Action of `f_{1}` on `E2H2H1`. -/
theorem actFp1_E2H2H1 (k : ℂ) :
    J k colF (1) (J k colE (-2) (J k colH (-2) (J k colH (-1) (vacuumA k))))
      = (2 : ℂ) • J k colE (-2) (J k colF (-1) (J k colH (-1) (vacuumA k)))
        + (-1 : ℂ) • J k colH (-2) (J k colH (-1) (J k colH (-1) (vacuumA k))) := by
  simp only [FEs k (1) (-2) (-1) (by norm_num) (by norm_num) 
      (J k colH (-2) ( J k colH (-1) (vacuumA k))),
    actFp1_H2H1, preH1_H2H1, map_smul]
  try module

/-- Cartan charge of `H2H1` is `0`. -/
theorem actHp0_H2H1 (k : ℂ) :
    J k colH (0) (J k colH (-2) (J k colH (-1) (vacuumA k)))
      = (0 : ℂ) • J k colH (-2) (J k colH (-1) (vacuumA k)) := by
  have g1 := H0_H (-1) (by norm_num) (H0_vac k)
  exact H0_H (-2) (by norm_num) g1

/-- Cartan charge of `E2H2H1` is `2`. -/
theorem actHp0_E2H2H1 (k : ℂ) :
    J k colH (0) (J k colE (-2) (J k colH (-2) (J k colH (-1) (vacuumA k))))
      = (2 : ℂ) • J k colE (-2) (J k colH (-2) (J k colH (-1) (vacuumA k))) := by
  have g1 := H0_H (-1) (by norm_num) (H0_vac k)
  have g2 := H0_H (-2) (by norm_num) g1
  exact H0_E (-2) g2 (2 : ℂ) (by norm_num)

/-- Action of `e_{0}` on `F2E1`. -/
theorem actEp0_F2E1 (k : ℂ) :
    J k colE (0) (J k colF (-2) (J k colE (-1) (vacuumA k)))
      = J k colH (-2) (J k colE (-1) (vacuumA k)) := by
  simp only [EFs k (0) (-2) (-2) (by norm_num) (by norm_num) (J k colE (-1) (vacuumA k)),
    actEp0_E1, map_zero, zero_add]
  try module

/-- Action of `e_{0}` on `E2F2E1`. -/
theorem actEp0_E2F2E1 (k : ℂ) :
    J k colE (0) (J k colE (-2) (J k colF (-2) (J k colE (-1) (vacuumA k))))
      = J k colE (-2) (J k colH (-2) (J k colE (-1) (vacuumA k))) := by
  simp only [EEs k (0) (-2) (J k colF (-2) (J k colE (-1) (vacuumA k))), actEp0_F2E1]
  try module

/-- Action of `f_{1}` on `F2E1`. -/
theorem actFp1_F2E1 (k : ℂ) :
    J k colF (1) (J k colF (-2) (J k colE (-1) (vacuumA k)))
      = (k) • J k colF (-2) (vacuumA k) := by
  simp only [FFs k (1) (-2) (J k colE (-1) (vacuumA k)), actFp1_E1, map_smul]
  try module

/-- Action of `f_{1}` on `E2F2E1`. -/
theorem actFp1_E2F2E1 (k : ℂ) :
    J k colF (1) (J k colE (-2) (J k colF (-2) (J k colE (-1) (vacuumA k))))
      = (2 : ℂ) • J k colH (-4) (vacuumA k)
        + (2 : ℂ) • J k colF (-3) (J k colE (-1) (vacuumA k))
        + (k - 2) • J k colE (-2) (J k colF (-2) (vacuumA k))
        + (-1 : ℂ) • J k colF (-2) (J k colE (-1) (J k colH (-1) (vacuumA k))) := by
  simp only [FEs k (1) (-2) (-1) (by norm_num) (by norm_num) 
      (J k colF (-2) ( J k colE (-1) (vacuumA k))),
    actFp1_F2E1, preH1_F2E1, map_smul]
  try module

/-- Cartan charge of `F2E1` is `0`. -/
theorem actHp0_F2E1 (k : ℂ) :
    J k colH (0) (J k colF (-2) (J k colE (-1) (vacuumA k)))
      = (0 : ℂ) • J k colF (-2) (J k colE (-1) (vacuumA k)) := by
  have g1 := H0_E (-1) (H0_vac k) (2 : ℂ) (by norm_num)
  exact H0_F (-2) g1 (0 : ℂ) (by norm_num)

/-- Cartan charge of `E2F2E1` is `2`. -/
theorem actHp0_E2F2E1 (k : ℂ) :
    J k colH (0) (J k colE (-2) (J k colF (-2) (J k colE (-1) (vacuumA k))))
      = (2 : ℂ) • J k colE (-2) (J k colF (-2) (J k colE (-1) (vacuumA k))) := by
  have g1 := H0_E (-1) (H0_vac k) (2 : ℂ) (by norm_num)
  have g2 := H0_F (-2) g1 (0 : ℂ) (by norm_num)
  exact H0_E (-2) g2 (2 : ℂ) (by norm_num)

/-- Action of `e_{0}` on `E2F1`. -/
theorem actEp0_E2F1 (k : ℂ) :
    J k colE (0) (J k colE (-2) (J k colF (-1) (vacuumA k)))
      = J k colE (-2) (J k colH (-1) (vacuumA k)) := by
  simp only [EEs k (0) (-2) (J k colF (-1) (vacuumA k)), actEp0_F1]
  try module

/-- Action of `e_{0}` on `E2E2F1`. -/
theorem actEp0_E2E2F1 (k : ℂ) :
    J k colE (0) (J k colE (-2) (J k colE (-2) (J k colF (-1) (vacuumA k))))
      = J k colE (-2) (J k colE (-2) (J k colH (-1) (vacuumA k))) := by
  simp only [EEs k (0) (-2) (J k colE (-2) (J k colF (-1) (vacuumA k))), actEp0_E2F1]
  try module

/-- Action of `f_{1}` on `E2F1`. -/
theorem actFp1_E2F1 (k : ℂ) :
    J k colF (1) (J k colE (-2) (J k colF (-1) (vacuumA k)))
      = (2 : ℂ) • J k colF (-2) (vacuumA k)
        + (-1 : ℂ) • J k colF (-1) (J k colH (-1) (vacuumA k)) := by
  simp only [FEs k (1) (-2) (-1) (by norm_num) (by norm_num) (J k colF (-1) (vacuumA k)),
    actFp1_F1, preH1_F1, map_zero]
  try module

/-- Action of `f_{1}` on `E2E2F1`. -/
theorem actFp1_E2E2F1 (k : ℂ) :
    J k colF (1) (J k colE (-2) (J k colE (-2) (J k colF (-1) (vacuumA k))))
      = (-2 : ℂ) • J k colE (-3) (J k colF (-1) (vacuumA k))
        + (4 : ℂ) • J k colE (-2) (J k colF (-2) (vacuumA k))
        + (-2 : ℂ) • J k colE (-2) (J k colF (-1) (J k colH (-1) (vacuumA k))) := by
  simp only [FEs k (1) (-2) (-1) (by norm_num) (by norm_num) 
      (J k colE (-2) ( J k colF (-1) (vacuumA k))),
    actFp1_E2F1, preH1_E2F1, map_add, map_smul]
  try module

/-- Cartan charge of `E2F1` is `0`. -/
theorem actHp0_E2F1 (k : ℂ) :
    J k colH (0) (J k colE (-2) (J k colF (-1) (vacuumA k)))
      = (0 : ℂ) • J k colE (-2) (J k colF (-1) (vacuumA k)) := by
  have g1 := H0_F (-1) (H0_vac k) (-2 : ℂ) (by norm_num)
  exact H0_E (-2) g1 (0 : ℂ) (by norm_num)

/-- Cartan charge of `E2E2F1` is `2`. -/
theorem actHp0_E2E2F1 (k : ℂ) :
    J k colH (0) (J k colE (-2) (J k colE (-2) (J k colF (-1) (vacuumA k))))
      = (2 : ℂ) • J k colE (-2) (J k colE (-2) (J k colF (-1) (vacuumA k))) := by
  have g1 := H0_F (-1) (H0_vac k) (-2 : ℂ) (by norm_num)
  have g2 := H0_E (-2) g1 (0 : ℂ) (by norm_num)
  exact H0_E (-2) g2 (2 : ℂ) (by norm_num)

/-- Action of `e_{0}` on `H3E1H1`. -/
theorem actEp0_H3E1H1 (k : ℂ) :
    J k colE (0) (J k colH (-3) (J k colE (-1) (J k colH (-1) (vacuumA k))))
      = (-2 : ℂ) • J k colE (-3) (J k colE (-1) (J k colH (-1) (vacuumA k)))
        + (-2 : ℂ) • J k colH (-3) (J k colE (-1) (J k colE (-1) (vacuumA k))) := by
  simp only [EHs k (0) (-3) (-3) (by norm_num) (J k colE (-1) (J k colH (-1) (vacuumA k))),
    actEp0_E1H1, map_smul]
  try module

/-- Action of `f_{1}` on `H3E1H1`. -/
theorem actFp1_H3E1H1 (k : ℂ) :
    J k colF (1) (J k colH (-3) (J k colE (-1) (J k colH (-1) (vacuumA k))))
      = (k) • J k colH (-3) (J k colH (-1) (vacuumA k))
        + (2 : ℂ) • J k colF (-2) (J k colE (-1) (J k colH (-1) (vacuumA k))) := by
  simp only [FHs k (1) (-3) (-2) (by norm_num) (J k colE (-1) (J k colH (-1) (vacuumA k))),
    actFp1_E1H1, map_smul]
  try module

/-- Cartan charge of `H3E1H1` is `2`. -/
theorem actHp0_H3E1H1 (k : ℂ) :
    J k colH (0) (J k colH (-3) (J k colE (-1) (J k colH (-1) (vacuumA k))))
      = (2 : ℂ) • J k colH (-3) (J k colE (-1) (J k colH (-1) (vacuumA k))) := by
  have g1 := H0_H (-1) (by norm_num) (H0_vac k)
  have g2 := H0_E (-1) g1 (2 : ℂ) (by norm_num)
  exact H0_H (-3) (by norm_num) g2

/-- Action of `e_{0}` on `E2`. -/
theorem actEp0_E2 (k : ℂ) :
    J k colE (0) (J k colE (-2) (vacuumA k))
      = 0 := by
  simp only [EEs k (0) (-2) (vacuumA k), E_vac0, map_zero]
  try module

/-- Action of `e_{0}` on `H3E2`. -/
theorem actEp0_H3E2 (k : ℂ) :
    J k colE (0) (J k colH (-3) (J k colE (-2) (vacuumA k)))
      = (-2 : ℂ) • J k colE (-3) (J k colE (-2) (vacuumA k)) := by
  simp only [EHs k (0) (-3) (-3) (by norm_num) (J k colE (-2) (vacuumA k)), actEp0_E2, map_zero]
  try module

/-- Action of `f_{1}` on `E2`. -/
theorem actFp1_E2 (k : ℂ) :
    J k colF (1) (J k colE (-2) (vacuumA k))
      = (-1 : ℂ) • J k colH (-1) (vacuumA k) := by
  simp only [FEs k (1) (-2) (-1) (by norm_num) (by norm_num) (vacuumA k), F_vac1, map_zero]
  try module

/-- Action of `f_{1}` on `H3E2`. -/
theorem actFp1_H3E2 (k : ℂ) :
    J k colF (1) (J k colH (-3) (J k colE (-2) (vacuumA k)))
      = (-2 : ℂ) • J k colH (-4) (vacuumA k)
        + (-1 : ℂ) • J k colH (-3) (J k colH (-1) (vacuumA k))
        + (2 : ℂ) • J k colE (-2) (J k colF (-2) (vacuumA k)) := by
  simp only [FHs k (1) (-3) (-2) (by norm_num) (J k colE (-2) (vacuumA k)), actFp1_E2,
    preF2_E2, map_smul]
  try module

/-- Cartan charge of `E2` is `2`. -/
theorem actHp0_E2 (k : ℂ) :
    J k colH (0) (J k colE (-2) (vacuumA k))
      = (2 : ℂ) • J k colE (-2) (vacuumA k) := by
  exact H0_E (-2) (H0_vac k) (2 : ℂ) (by norm_num)

/-- Cartan charge of `H3E2` is `2`. -/
theorem actHp0_H3E2 (k : ℂ) :
    J k colH (0) (J k colH (-3) (J k colE (-2) (vacuumA k)))
      = (2 : ℂ) • J k colH (-3) (J k colE (-2) (vacuumA k)) := by
  have g1 := H0_E (-2) (H0_vac k) (2 : ℂ) (by norm_num)
  exact H0_H (-3) (by norm_num) g1

/-- Action of `e_{0}` on `E1E1`. -/
theorem actEp0_E1E1 (k : ℂ) :
    J k colE (0) (J k colE (-1) (J k colE (-1) (vacuumA k)))
      = 0 := by
  simp only [EEs k (0) (-1) (J k colE (-1) (vacuumA k)), actEp0_E1, map_zero]
  try module

/-- Action of `e_{0}` on `F3E1E1`. -/
theorem actEp0_F3E1E1 (k : ℂ) :
    J k colE (0) (J k colF (-3) (J k colE (-1) (J k colE (-1) (vacuumA k))))
      = J k colH (-3) (J k colE (-1) (J k colE (-1) (vacuumA k))) := by
  simp only [EFs k (0) (-3) (-3) (by norm_num) (by norm_num) 
      (J k colE (-1) ( J k colE (-1) (vacuumA k))),
    actEp0_E1E1, map_zero, zero_add]
  try module

/-- Action of `f_{1}` on `E1E1`. -/
theorem actFp1_E1E1 (k : ℂ) :
    J k colF (1) (J k colE (-1) (J k colE (-1) (vacuumA k)))
      = (2*k - 2) • J k colE (-1) (vacuumA k) := by
  simp only [FEz k (1) (-1) (by norm_num) (J k colE (-1) (vacuumA k)), actFp1_E1, actHp0_E1,
    map_smul]
  push_cast
  try module

/-- Action of `f_{1}` on `F3E1E1`. -/
theorem actFp1_F3E1E1 (k : ℂ) :
    J k colF (1) (J k colF (-3) (J k colE (-1) (J k colE (-1) (vacuumA k))))
      = (2*k - 2) • J k colF (-3) (J k colE (-1) (vacuumA k)) := by
  simp only [FFs k (1) (-3) (J k colE (-1) (J k colE (-1) (vacuumA k))), actFp1_E1E1, map_smul]
  try module

/-- Cartan charge of `E1E1` is `4`. -/
theorem actHp0_E1E1 (k : ℂ) :
    J k colH (0) (J k colE (-1) (J k colE (-1) (vacuumA k)))
      = (4 : ℂ) • J k colE (-1) (J k colE (-1) (vacuumA k)) := by
  have g1 := H0_E (-1) (H0_vac k) (2 : ℂ) (by norm_num)
  exact H0_E (-1) g1 (4 : ℂ) (by norm_num)

/-- Cartan charge of `F3E1E1` is `2`. -/
theorem actHp0_F3E1E1 (k : ℂ) :
    J k colH (0) (J k colF (-3) (J k colE (-1) (J k colE (-1) (vacuumA k))))
      = (2 : ℂ) • J k colF (-3) (J k colE (-1) (J k colE (-1) (vacuumA k))) := by
  have g1 := H0_E (-1) (H0_vac k) (2 : ℂ) (by norm_num)
  have g2 := H0_E (-1) g1 (4 : ℂ) (by norm_num)
  exact H0_F (-3) g2 (2 : ℂ) (by norm_num)

/-- Action of `e_{0}` on `E3H1H1`. -/
theorem actEp0_E3H1H1 (k : ℂ) :
    J k colE (0) (J k colE (-3) (J k colH (-1) (J k colH (-1) (vacuumA k))))
      = (-4 : ℂ) • J k colE (-3) (J k colE (-2) (vacuumA k))
        + (-4 : ℂ) • J k colE (-3) (J k colE (-1) (J k colH (-1) (vacuumA k))) := by
  simp only [EEs k (0) (-3) (J k colH (-1) (J k colH (-1) (vacuumA k))), actEp0_H1H1, map_add,
    map_smul]
  try module

/-- Action of `f_{1}` on `E3H1H1`. -/
theorem actFp1_E3H1H1 (k : ℂ) :
    J k colF (1) (J k colE (-3) (J k colH (-1) (J k colH (-1) (vacuumA k))))
      = (4 : ℂ) • J k colE (-3) (J k colF (-1) (vacuumA k))
        + (-1 : ℂ) • J k colH (-2) (J k colH (-1) (J k colH (-1) (vacuumA k))) := by
  simp only [FEs k (1) (-3) (-2) (by norm_num) (by norm_num) 
      (J k colH (-1) ( J k colH (-1) (vacuumA k))),
    actFp1_H1H1, map_smul]
  try module

/-- Cartan charge of `E3H1H1` is `2`. -/
theorem actHp0_E3H1H1 (k : ℂ) :
    J k colH (0) (J k colE (-3) (J k colH (-1) (J k colH (-1) (vacuumA k))))
      = (2 : ℂ) • J k colE (-3) (J k colH (-1) (J k colH (-1) (vacuumA k))) := by
  have g1 := H0_H (-1) (by norm_num) (H0_vac k)
  have g2 := H0_H (-1) (by norm_num) g1
  exact H0_E (-3) g2 (2 : ℂ) (by norm_num)

/-- Action of `e_{0}` on `E3E1F1`. -/
theorem actEp0_E3E1F1 (k : ℂ) :
    J k colE (0) (J k colE (-3) (J k colE (-1) (J k colF (-1) (vacuumA k))))
      = J k colE (-3) (J k colE (-1) (J k colH (-1) (vacuumA k))) := by
  simp only [EEs k (0) (-3) (J k colE (-1) (J k colF (-1) (vacuumA k))), actEp0_E1F1]
  try module

/-- Action of `f_{1}` on `E3E1F1`. -/
theorem actFp1_E3E1F1 (k : ℂ) :
    J k colF (1) (J k colE (-3) (J k colE (-1) (J k colF (-1) (vacuumA k))))
      = (k + 2) • J k colE (-3) (J k colF (-1) (vacuumA k))
        + (-1 : ℂ) • J k colH (-2) (J k colE (-1) (J k colF (-1) (vacuumA k))) := by
  simp only [FEs k (1) (-3) (-2) (by norm_num) (by norm_num) 
      (J k colE (-1) ( J k colF (-1) (vacuumA k))),
    actFp1_E1F1, map_smul]
  try module

/-- Cartan charge of `E3E1F1` is `2`. -/
theorem actHp0_E3E1F1 (k : ℂ) :
    J k colH (0) (J k colE (-3) (J k colE (-1) (J k colF (-1) (vacuumA k))))
      = (2 : ℂ) • J k colE (-3) (J k colE (-1) (J k colF (-1) (vacuumA k))) := by
  have g1 := H0_F (-1) (H0_vac k) (-2 : ℂ) (by norm_num)
  have g2 := H0_E (-1) g1 (0 : ℂ) (by norm_num)
  exact H0_E (-3) g2 (2 : ℂ) (by norm_num)

/-- Action of `e_{0}` on `H2`. -/
theorem actEp0_H2 (k : ℂ) :
    J k colE (0) (J k colH (-2) (vacuumA k))
      = (-2 : ℂ) • J k colE (-2) (vacuumA k) := by
  simp only [EHs k (0) (-2) (-2) (by norm_num) (vacuumA k), E_vac0, map_zero]
  try module

/-- Action of `e_{0}` on `E3H2`. -/
theorem actEp0_E3H2 (k : ℂ) :
    J k colE (0) (J k colE (-3) (J k colH (-2) (vacuumA k)))
      = (-2 : ℂ) • J k colE (-3) (J k colE (-2) (vacuumA k)) := by
  simp only [EEs k (0) (-3) (J k colH (-2) (vacuumA k)), actEp0_H2, map_smul]
  try module

/-- Action of `f_{1}` on `H2`. -/
theorem actFp1_H2 (k : ℂ) :
    J k colF (1) (J k colH (-2) (vacuumA k))
      = (2 : ℂ) • J k colF (-1) (vacuumA k) := by
  simp only [FHs k (1) (-2) (-1) (by norm_num) (vacuumA k), F_vac1, map_zero, zero_add]
  try module

/-- Action of `f_{1}` on `E3H2`. -/
theorem actFp1_E3H2 (k : ℂ) :
    J k colF (1) (J k colE (-3) (J k colH (-2) (vacuumA k)))
      = (2 : ℂ) • J k colE (-3) (J k colF (-1) (vacuumA k))
        + (-1 : ℂ) • J k colH (-2) (J k colH (-2) (vacuumA k)) := by
  simp only [FEs k (1) (-3) (-2) (by norm_num) (by norm_num) (J k colH (-2) (vacuumA k)),
    actFp1_H2, map_smul]
  try module

/-- Cartan charge of `H2` is `0`. -/
theorem actHp0_H2 (k : ℂ) :
    J k colH (0) (J k colH (-2) (vacuumA k))
      = (0 : ℂ) • J k colH (-2) (vacuumA k) := by
  exact H0_H (-2) (by norm_num) (H0_vac k)

/-- Cartan charge of `E3H2` is `2`. -/
theorem actHp0_E3H2 (k : ℂ) :
    J k colH (0) (J k colE (-3) (J k colH (-2) (vacuumA k)))
      = (2 : ℂ) • J k colE (-3) (J k colH (-2) (vacuumA k)) := by
  have g1 := H0_H (-2) (by norm_num) (H0_vac k)
  exact H0_E (-3) g1 (2 : ℂ) (by norm_num)

/-- Action of `e_{0}` on `H4E1`. -/
theorem actEp0_H4E1 (k : ℂ) :
    J k colE (0) (J k colH (-4) (J k colE (-1) (vacuumA k)))
      = (-2 : ℂ) • J k colE (-4) (J k colE (-1) (vacuumA k)) := by
  simp only [EHs k (0) (-4) (-4) (by norm_num) (J k colE (-1) (vacuumA k)), actEp0_E1, map_zero]
  try module

/-- Action of `f_{1}` on `H4E1`. -/
theorem actFp1_H4E1 (k : ℂ) :
    J k colF (1) (J k colH (-4) (J k colE (-1) (vacuumA k)))
      = (k) • J k colH (-4) (vacuumA k)
        + (2 : ℂ) • J k colF (-3) (J k colE (-1) (vacuumA k)) := by
  simp only [FHs k (1) (-4) (-3) (by norm_num) (J k colE (-1) (vacuumA k)), actFp1_E1, map_smul]
  try module

/-- Cartan charge of `H4E1` is `2`. -/
theorem actHp0_H4E1 (k : ℂ) :
    J k colH (0) (J k colH (-4) (J k colE (-1) (vacuumA k)))
      = (2 : ℂ) • J k colH (-4) (J k colE (-1) (vacuumA k)) := by
  have g1 := H0_E (-1) (H0_vac k) (2 : ℂ) (by norm_num)
  exact H0_H (-4) (by norm_num) g1

/-- Action of `e_{0}` on `E4H1`. -/
theorem actEp0_E4H1 (k : ℂ) :
    J k colE (0) (J k colE (-4) (J k colH (-1) (vacuumA k)))
      = (-2 : ℂ) • J k colE (-4) (J k colE (-1) (vacuumA k)) := by
  simp only [EEs k (0) (-4) (J k colH (-1) (vacuumA k)), actEp0_H1, map_smul]
  try module

/-- Action of `f_{1}` on `E4H1`. -/
theorem actFp1_E4H1 (k : ℂ) :
    J k colF (1) (J k colE (-4) (J k colH (-1) (vacuumA k)))
      = (-1 : ℂ) • J k colH (-3) (J k colH (-1) (vacuumA k)) := by
  simp only [FEs k (1) (-4) (-3) (by norm_num) (by norm_num) (J k colH (-1) (vacuumA k)),
    actFp1_H1, map_zero]
  try module

/-- Cartan charge of `E4H1` is `2`. -/
theorem actHp0_E4H1 (k : ℂ) :
    J k colH (0) (J k colE (-4) (J k colH (-1) (vacuumA k)))
      = (2 : ℂ) • J k colE (-4) (J k colH (-1) (vacuumA k)) := by
  have g1 := H0_H (-1) (by norm_num) (H0_vac k)
  exact H0_E (-4) g1 (2 : ℂ) (by norm_num)

/-- Action of `e_{0}` on `E5`. -/
theorem actEp0_E5 (k : ℂ) :
    J k colE (0) (J k colE (-5) (vacuumA k))
      = 0 := by
  simp only [EEs k (0) (-5) (vacuumA k), E_vac0, map_zero]
  try module

/-- Action of `f_{1}` on `E5`. -/
theorem actFp1_E5 (k : ℂ) :
    J k colF (1) (J k colE (-5) (vacuumA k))
      = (-1 : ℂ) • J k colH (-4) (vacuumA k) := by
  simp only [FEs k (1) (-5) (-4) (by norm_num) (by norm_num) (vacuumA k), F_vac1, map_zero]
  try module

/-- Cartan charge of `E5` is `2`. -/
theorem actHp0_E5 (k : ℂ) :
    J k colH (0) (J k colE (-5) (vacuumA k))
      = (2 : ℂ) • J k colE (-5) (vacuumA k) := by
  exact H0_E (-5) (H0_vac k) (2 : ℂ) (by norm_num)


/-! ## §4  The 21 ansatz monomials and the 25 target monomials -/

/-- `e_{-1}h_{-1}h_{-1}h_{-1}h_{-1}|0⟩` (conformal weight 5, Cartan charge +2). -/
noncomputable def N1 (k : ℂ) : WakModule k :=
  J k colE (-1) (J k colH (-1) (J k colH (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))))

/-- Unfolding lemma for `N1`. -/
theorem N1_def (k : ℂ) :
    N1 k = J k colE (-1) (J k colH (-1) (J k colH (-1) (J k colH (-1) (
      J k colH (-1) (vacuumA k))))) := rfl

/-- `e_{-1}e_{-1}f_{-1}h_{-1}h_{-1}|0⟩` (conformal weight 5, Cartan charge +2). -/
noncomputable def N2 (k : ℂ) : WakModule k :=
  J k colE (-1) (J k colE (-1) (J k colF (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))))

/-- Unfolding lemma for `N2`. -/
theorem N2_def (k : ℂ) :
    N2 k = J k colE (-1) (J k colE (-1) (J k colF (-1) (J k colH (-1) (
      J k colH (-1) (vacuumA k))))) := rfl

/-- `e_{-1}e_{-1}e_{-1}f_{-1}f_{-1}|0⟩` (conformal weight 5, Cartan charge +2). -/
noncomputable def N3 (k : ℂ) : WakModule k :=
  J k colE (-1) (J k colE (-1) (J k colE (-1) (J k colF (-1) (J k colF (-1) (vacuumA k)))))

/-- Unfolding lemma for `N3`. -/
theorem N3_def (k : ℂ) :
    N3 k = J k colE (-1) (J k colE (-1) (J k colE (-1) (J k colF (-1) (
      J k colF (-1) (vacuumA k))))) := rfl

/-- `h_{-2}e_{-1}h_{-1}h_{-1}|0⟩` (conformal weight 5, Cartan charge +2). -/
noncomputable def N4 (k : ℂ) : WakModule k :=
  J k colH (-2) (J k colE (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))))

/-- Unfolding lemma for `N4`. -/
theorem N4_def (k : ℂ) :
    N4 k = J k colH (-2) (J k colE (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))) := rfl

/-- `h_{-2}e_{-1}e_{-1}f_{-1}|0⟩` (conformal weight 5, Cartan charge +2). -/
noncomputable def N5 (k : ℂ) : WakModule k :=
  J k colH (-2) (J k colE (-1) (J k colE (-1) (J k colF (-1) (vacuumA k))))

/-- Unfolding lemma for `N5`. -/
theorem N5_def (k : ℂ) :
    N5 k = J k colH (-2) (J k colE (-1) (J k colE (-1) (J k colF (-1) (vacuumA k)))) := rfl

/-- `h_{-2}h_{-2}e_{-1}|0⟩` (conformal weight 5, Cartan charge +2). -/
noncomputable def N6 (k : ℂ) : WakModule k :=
  J k colH (-2) (J k colH (-2) (J k colE (-1) (vacuumA k)))

/-- Unfolding lemma for `N6`. -/
theorem N6_def (k : ℂ) :
    N6 k = J k colH (-2) (J k colH (-2) (J k colE (-1) (vacuumA k))) := rfl

/-- `f_{-2}e_{-1}e_{-1}h_{-1}|0⟩` (conformal weight 5, Cartan charge +2). -/
noncomputable def N7 (k : ℂ) : WakModule k :=
  J k colF (-2) (J k colE (-1) (J k colE (-1) (J k colH (-1) (vacuumA k))))

/-- Unfolding lemma for `N7`. -/
theorem N7_def (k : ℂ) :
    N7 k = J k colF (-2) (J k colE (-1) (J k colE (-1) (J k colH (-1) (vacuumA k)))) := rfl

/-- `e_{-2}h_{-1}h_{-1}h_{-1}|0⟩` (conformal weight 5, Cartan charge +2). -/
noncomputable def N8 (k : ℂ) : WakModule k :=
  J k colE (-2) (J k colH (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))))

/-- Unfolding lemma for `N8`. -/
theorem N8_def (k : ℂ) :
    N8 k = J k colE (-2) (J k colH (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))) := rfl

/-- `e_{-2}e_{-1}f_{-1}h_{-1}|0⟩` (conformal weight 5, Cartan charge +2). -/
noncomputable def N9 (k : ℂ) : WakModule k :=
  J k colE (-2) (J k colE (-1) (J k colF (-1) (J k colH (-1) (vacuumA k))))

/-- Unfolding lemma for `N9`. -/
theorem N9_def (k : ℂ) :
    N9 k = J k colE (-2) (J k colE (-1) (J k colF (-1) (J k colH (-1) (vacuumA k)))) := rfl

/-- `e_{-2}h_{-2}h_{-1}|0⟩` (conformal weight 5, Cartan charge +2). -/
noncomputable def N10 (k : ℂ) : WakModule k :=
  J k colE (-2) (J k colH (-2) (J k colH (-1) (vacuumA k)))

/-- Unfolding lemma for `N10`. -/
theorem N10_def (k : ℂ) :
    N10 k = J k colE (-2) (J k colH (-2) (J k colH (-1) (vacuumA k))) := rfl

/-- `e_{-2}f_{-2}e_{-1}|0⟩` (conformal weight 5, Cartan charge +2). -/
noncomputable def N11 (k : ℂ) : WakModule k :=
  J k colE (-2) (J k colF (-2) (J k colE (-1) (vacuumA k)))

/-- Unfolding lemma for `N11`. -/
theorem N11_def (k : ℂ) :
    N11 k = J k colE (-2) (J k colF (-2) (J k colE (-1) (vacuumA k))) := rfl

/-- `e_{-2}e_{-2}f_{-1}|0⟩` (conformal weight 5, Cartan charge +2). -/
noncomputable def N12 (k : ℂ) : WakModule k :=
  J k colE (-2) (J k colE (-2) (J k colF (-1) (vacuumA k)))

/-- Unfolding lemma for `N12`. -/
theorem N12_def (k : ℂ) :
    N12 k = J k colE (-2) (J k colE (-2) (J k colF (-1) (vacuumA k))) := rfl

/-- `h_{-3}e_{-1}h_{-1}|0⟩` (conformal weight 5, Cartan charge +2). -/
noncomputable def N13 (k : ℂ) : WakModule k :=
  J k colH (-3) (J k colE (-1) (J k colH (-1) (vacuumA k)))

/-- Unfolding lemma for `N13`. -/
theorem N13_def (k : ℂ) :
    N13 k = J k colH (-3) (J k colE (-1) (J k colH (-1) (vacuumA k))) := rfl

/-- `h_{-3}e_{-2}|0⟩` (conformal weight 5, Cartan charge +2). -/
noncomputable def N14 (k : ℂ) : WakModule k :=
  J k colH (-3) (J k colE (-2) (vacuumA k))

/-- Unfolding lemma for `N14`. -/
theorem N14_def (k : ℂ) :
    N14 k = J k colH (-3) (J k colE (-2) (vacuumA k)) := rfl

/-- `f_{-3}e_{-1}e_{-1}|0⟩` (conformal weight 5, Cartan charge +2). -/
noncomputable def N15 (k : ℂ) : WakModule k :=
  J k colF (-3) (J k colE (-1) (J k colE (-1) (vacuumA k)))

/-- Unfolding lemma for `N15`. -/
theorem N15_def (k : ℂ) :
    N15 k = J k colF (-3) (J k colE (-1) (J k colE (-1) (vacuumA k))) := rfl

/-- `e_{-3}h_{-1}h_{-1}|0⟩` (conformal weight 5, Cartan charge +2). -/
noncomputable def N16 (k : ℂ) : WakModule k :=
  J k colE (-3) (J k colH (-1) (J k colH (-1) (vacuumA k)))

/-- Unfolding lemma for `N16`. -/
theorem N16_def (k : ℂ) :
    N16 k = J k colE (-3) (J k colH (-1) (J k colH (-1) (vacuumA k))) := rfl

/-- `e_{-3}e_{-1}f_{-1}|0⟩` (conformal weight 5, Cartan charge +2). -/
noncomputable def N17 (k : ℂ) : WakModule k :=
  J k colE (-3) (J k colE (-1) (J k colF (-1) (vacuumA k)))

/-- Unfolding lemma for `N17`. -/
theorem N17_def (k : ℂ) :
    N17 k = J k colE (-3) (J k colE (-1) (J k colF (-1) (vacuumA k))) := rfl

/-- `e_{-3}h_{-2}|0⟩` (conformal weight 5, Cartan charge +2). -/
noncomputable def N18 (k : ℂ) : WakModule k :=
  J k colE (-3) (J k colH (-2) (vacuumA k))

/-- Unfolding lemma for `N18`. -/
theorem N18_def (k : ℂ) :
    N18 k = J k colE (-3) (J k colH (-2) (vacuumA k)) := rfl

/-- `h_{-4}e_{-1}|0⟩` (conformal weight 5, Cartan charge +2). -/
noncomputable def N19 (k : ℂ) : WakModule k :=
  J k colH (-4) (J k colE (-1) (vacuumA k))

/-- Unfolding lemma for `N19`. -/
theorem N19_def (k : ℂ) :
    N19 k = J k colH (-4) (J k colE (-1) (vacuumA k)) := rfl

/-- `e_{-4}h_{-1}|0⟩` (conformal weight 5, Cartan charge +2). -/
noncomputable def N20 (k : ℂ) : WakModule k :=
  J k colE (-4) (J k colH (-1) (vacuumA k))

/-- Unfolding lemma for `N20`. -/
theorem N20_def (k : ℂ) :
    N20 k = J k colE (-4) (J k colH (-1) (vacuumA k)) := rfl

/-- `e_{-5}|0⟩` (conformal weight 5, Cartan charge +2). -/
noncomputable def N21 (k : ℂ) : WakModule k :=
  J k colE (-5) (vacuumA k)

/-- Unfolding lemma for `N21`. -/
theorem N21_def (k : ℂ) :
    N21 k = J k colE (-5) (vacuumA k) := rfl

/-- `e_{-1}e_{-1}h_{-1}h_{-1}h_{-1}|0⟩` (conformal weight 5, Cartan charge +4). -/
noncomputable def T1 (k : ℂ) : WakModule k :=
  J k colE (-1) (J k colE (-1) (J k colH (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))))

/-- Unfolding lemma for `T1`. -/
theorem T1_def (k : ℂ) :
    T1 k = J k colE (-1) (J k colE (-1) (J k colH (-1) (J k colH (-1) (
      J k colH (-1) (vacuumA k))))) := rfl

/-- `e_{-1}e_{-1}e_{-1}f_{-1}h_{-1}|0⟩` (conformal weight 5, Cartan charge +4). -/
noncomputable def T2 (k : ℂ) : WakModule k :=
  J k colE (-1) (J k colE (-1) (J k colE (-1) (J k colF (-1) (J k colH (-1) (vacuumA k)))))

/-- Unfolding lemma for `T2`. -/
theorem T2_def (k : ℂ) :
    T2 k = J k colE (-1) (J k colE (-1) (J k colE (-1) (J k colF (-1) (
      J k colH (-1) (vacuumA k))))) := rfl

/-- `h_{-2}e_{-1}e_{-1}h_{-1}|0⟩` (conformal weight 5, Cartan charge +4). -/
noncomputable def T3 (k : ℂ) : WakModule k :=
  J k colH (-2) (J k colE (-1) (J k colE (-1) (J k colH (-1) (vacuumA k))))

/-- Unfolding lemma for `T3`. -/
theorem T3_def (k : ℂ) :
    T3 k = J k colH (-2) (J k colE (-1) (J k colE (-1) (J k colH (-1) (vacuumA k)))) := rfl

/-- `f_{-2}e_{-1}e_{-1}e_{-1}|0⟩` (conformal weight 5, Cartan charge +4). -/
noncomputable def T4 (k : ℂ) : WakModule k :=
  J k colF (-2) (J k colE (-1) (J k colE (-1) (J k colE (-1) (vacuumA k))))

/-- Unfolding lemma for `T4`. -/
theorem T4_def (k : ℂ) :
    T4 k = J k colF (-2) (J k colE (-1) (J k colE (-1) (J k colE (-1) (vacuumA k)))) := rfl

/-- `e_{-2}e_{-1}h_{-1}h_{-1}|0⟩` (conformal weight 5, Cartan charge +4). -/
noncomputable def T5 (k : ℂ) : WakModule k :=
  J k colE (-2) (J k colE (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))))

/-- Unfolding lemma for `T5`. -/
theorem T5_def (k : ℂ) :
    T5 k = J k colE (-2) (J k colE (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))) := rfl

/-- `e_{-2}e_{-1}e_{-1}f_{-1}|0⟩` (conformal weight 5, Cartan charge +4). -/
noncomputable def T6 (k : ℂ) : WakModule k :=
  J k colE (-2) (J k colE (-1) (J k colE (-1) (J k colF (-1) (vacuumA k))))

/-- Unfolding lemma for `T6`. -/
theorem T6_def (k : ℂ) :
    T6 k = J k colE (-2) (J k colE (-1) (J k colE (-1) (J k colF (-1) (vacuumA k)))) := rfl

/-- `e_{-2}h_{-2}e_{-1}|0⟩` (conformal weight 5, Cartan charge +4). -/
noncomputable def T7 (k : ℂ) : WakModule k :=
  J k colE (-2) (J k colH (-2) (J k colE (-1) (vacuumA k)))

/-- Unfolding lemma for `T7`. -/
theorem T7_def (k : ℂ) :
    T7 k = J k colE (-2) (J k colH (-2) (J k colE (-1) (vacuumA k))) := rfl

/-- `e_{-2}e_{-2}h_{-1}|0⟩` (conformal weight 5, Cartan charge +4). -/
noncomputable def T8 (k : ℂ) : WakModule k :=
  J k colE (-2) (J k colE (-2) (J k colH (-1) (vacuumA k)))

/-- Unfolding lemma for `T8`. -/
theorem T8_def (k : ℂ) :
    T8 k = J k colE (-2) (J k colE (-2) (J k colH (-1) (vacuumA k))) := rfl

/-- `h_{-3}e_{-1}e_{-1}|0⟩` (conformal weight 5, Cartan charge +4). -/
noncomputable def T9 (k : ℂ) : WakModule k :=
  J k colH (-3) (J k colE (-1) (J k colE (-1) (vacuumA k)))

/-- Unfolding lemma for `T9`. -/
theorem T9_def (k : ℂ) :
    T9 k = J k colH (-3) (J k colE (-1) (J k colE (-1) (vacuumA k))) := rfl

/-- `e_{-3}e_{-1}h_{-1}|0⟩` (conformal weight 5, Cartan charge +4). -/
noncomputable def T10 (k : ℂ) : WakModule k :=
  J k colE (-3) (J k colE (-1) (J k colH (-1) (vacuumA k)))

/-- Unfolding lemma for `T10`. -/
theorem T10_def (k : ℂ) :
    T10 k = J k colE (-3) (J k colE (-1) (J k colH (-1) (vacuumA k))) := rfl

/-- `e_{-3}e_{-2}|0⟩` (conformal weight 5, Cartan charge +4). -/
noncomputable def T11 (k : ℂ) : WakModule k :=
  J k colE (-3) (J k colE (-2) (vacuumA k))

/-- Unfolding lemma for `T11`. -/
theorem T11_def (k : ℂ) :
    T11 k = J k colE (-3) (J k colE (-2) (vacuumA k)) := rfl

/-- `e_{-4}e_{-1}|0⟩` (conformal weight 5, Cartan charge +4). -/
noncomputable def T12 (k : ℂ) : WakModule k :=
  J k colE (-4) (J k colE (-1) (vacuumA k))

/-- Unfolding lemma for `T12`. -/
theorem T12_def (k : ℂ) :
    T12 k = J k colE (-4) (J k colE (-1) (vacuumA k)) := rfl

/-- `h_{-1}h_{-1}h_{-1}h_{-1}|0⟩` (conformal weight 4, Cartan charge 0). -/
noncomputable def U1 (k : ℂ) : WakModule k :=
  J k colH (-1) (J k colH (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))))

/-- Unfolding lemma for `U1`. -/
theorem U1_def (k : ℂ) :
    U1 k = J k colH (-1) (J k colH (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))) := rfl

/-- `e_{-1}f_{-1}h_{-1}h_{-1}|0⟩` (conformal weight 4, Cartan charge 0). -/
noncomputable def U2 (k : ℂ) : WakModule k :=
  J k colE (-1) (J k colF (-1) (J k colH (-1) (J k colH (-1) (vacuumA k))))

/-- Unfolding lemma for `U2`. -/
theorem U2_def (k : ℂ) :
    U2 k = J k colE (-1) (J k colF (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))) := rfl

/-- `e_{-1}e_{-1}f_{-1}f_{-1}|0⟩` (conformal weight 4, Cartan charge 0). -/
noncomputable def U3 (k : ℂ) : WakModule k :=
  J k colE (-1) (J k colE (-1) (J k colF (-1) (J k colF (-1) (vacuumA k))))

/-- Unfolding lemma for `U3`. -/
theorem U3_def (k : ℂ) :
    U3 k = J k colE (-1) (J k colE (-1) (J k colF (-1) (J k colF (-1) (vacuumA k)))) := rfl

/-- `h_{-2}h_{-1}h_{-1}|0⟩` (conformal weight 4, Cartan charge 0). -/
noncomputable def U4 (k : ℂ) : WakModule k :=
  J k colH (-2) (J k colH (-1) (J k colH (-1) (vacuumA k)))

/-- Unfolding lemma for `U4`. -/
theorem U4_def (k : ℂ) :
    U4 k = J k colH (-2) (J k colH (-1) (J k colH (-1) (vacuumA k))) := rfl

/-- `h_{-2}e_{-1}f_{-1}|0⟩` (conformal weight 4, Cartan charge 0). -/
noncomputable def U5 (k : ℂ) : WakModule k :=
  J k colH (-2) (J k colE (-1) (J k colF (-1) (vacuumA k)))

/-- Unfolding lemma for `U5`. -/
theorem U5_def (k : ℂ) :
    U5 k = J k colH (-2) (J k colE (-1) (J k colF (-1) (vacuumA k))) := rfl

/-- `h_{-2}h_{-2}|0⟩` (conformal weight 4, Cartan charge 0). -/
noncomputable def U6 (k : ℂ) : WakModule k :=
  J k colH (-2) (J k colH (-2) (vacuumA k))

/-- Unfolding lemma for `U6`. -/
theorem U6_def (k : ℂ) :
    U6 k = J k colH (-2) (J k colH (-2) (vacuumA k)) := rfl

/-- `f_{-2}e_{-1}h_{-1}|0⟩` (conformal weight 4, Cartan charge 0). -/
noncomputable def U7 (k : ℂ) : WakModule k :=
  J k colF (-2) (J k colE (-1) (J k colH (-1) (vacuumA k)))

/-- Unfolding lemma for `U7`. -/
theorem U7_def (k : ℂ) :
    U7 k = J k colF (-2) (J k colE (-1) (J k colH (-1) (vacuumA k))) := rfl

/-- `e_{-2}f_{-1}h_{-1}|0⟩` (conformal weight 4, Cartan charge 0). -/
noncomputable def U8 (k : ℂ) : WakModule k :=
  J k colE (-2) (J k colF (-1) (J k colH (-1) (vacuumA k)))

/-- Unfolding lemma for `U8`. -/
theorem U8_def (k : ℂ) :
    U8 k = J k colE (-2) (J k colF (-1) (J k colH (-1) (vacuumA k))) := rfl

/-- `e_{-2}f_{-2}|0⟩` (conformal weight 4, Cartan charge 0). -/
noncomputable def U9 (k : ℂ) : WakModule k :=
  J k colE (-2) (J k colF (-2) (vacuumA k))

/-- Unfolding lemma for `U9`. -/
theorem U9_def (k : ℂ) :
    U9 k = J k colE (-2) (J k colF (-2) (vacuumA k)) := rfl

/-- `h_{-3}h_{-1}|0⟩` (conformal weight 4, Cartan charge 0). -/
noncomputable def U10 (k : ℂ) : WakModule k :=
  J k colH (-3) (J k colH (-1) (vacuumA k))

/-- Unfolding lemma for `U10`. -/
theorem U10_def (k : ℂ) :
    U10 k = J k colH (-3) (J k colH (-1) (vacuumA k)) := rfl

/-- `f_{-3}e_{-1}|0⟩` (conformal weight 4, Cartan charge 0). -/
noncomputable def U11 (k : ℂ) : WakModule k :=
  J k colF (-3) (J k colE (-1) (vacuumA k))

/-- Unfolding lemma for `U11`. -/
theorem U11_def (k : ℂ) :
    U11 k = J k colF (-3) (J k colE (-1) (vacuumA k)) := rfl

/-- `e_{-3}f_{-1}|0⟩` (conformal weight 4, Cartan charge 0). -/
noncomputable def U12 (k : ℂ) : WakModule k :=
  J k colE (-3) (J k colF (-1) (vacuumA k))

/-- Unfolding lemma for `U12`. -/
theorem U12_def (k : ℂ) :
    U12 k = J k colE (-3) (J k colF (-1) (vacuumA k)) := rfl

/-- `h_{-4}|0⟩` (conformal weight 4, Cartan charge 0). -/
noncomputable def U13 (k : ℂ) : WakModule k :=
  J k colH (-4) (vacuumA k)

/-- Unfolding lemma for `U13`. -/
theorem U13_def (k : ℂ) :
    U13 k = J k colH (-4) (vacuumA k) := rfl


/-! ## §5  The action of `e₀`, `f₁`, `h₀` on the 21 monomials -/

/-- `e₀` on `N1`. -/
theorem E0_N1 (k : ℂ) :
    J k colE 0 (N1 k)
      = (-16 : ℂ) • T12 k + (-32 : ℂ) • T10 k + (-24 : ℂ) • T5 k
        + (-8 : ℂ) • T1 k :=
  actEp0_E1H1H1H1H1 k

/-- `e₀` on `N2`. -/
theorem E0_N2 (k : ℂ) :
    J k colE 0 (N2 k)
      = (-16 : ℂ) • T12 k + (-16 : ℂ) • T10 k + (4 : ℂ) • T9 k + (-4 : ℂ) • T6 k
        + (4 : ℂ) • T3 k + (-4 : ℂ) • T2 k + T1 k :=
  actEp0_E1E1F1H1H1 k

/-- `e₀` on `N3`. -/
theorem E0_N3 (k : ℂ) :
    J k colE 0 (N3 k)
      = (12 : ℂ) • T12 k + (-6 : ℂ) • T9 k + (-2 : ℂ) • T4 k + (2 : ℂ) • T2 k :=
  actEp0_E1E1E1F1F1 k

/-- `e₀` on `N4`. -/
theorem E0_N4 (k : ℂ) :
    J k colE 0 (N4 k)
      = (-8 : ℂ) • T12 k + (-4 : ℂ) • T7 k + (-2 : ℂ) • T5 k + (-4 : ℂ) • T3 k :=
  actEp0_H2E1H1H1 k

/-- `e₀` on `N5`. -/
theorem E0_N5 (k : ℂ) :
    J k colE 0 (N5 k)
      = (-2 : ℂ) • T6 k + T3 k :=
  actEp0_H2E1E1F1 k

/-- `e₀` on `N6`. -/
theorem E0_N6 (k : ℂ) :
    J k colE 0 (N6 k)
      = (-4 : ℂ) • T12 k + (-4 : ℂ) • T7 k :=
  actEp0_H2H2E1 k

/-- `e₀` on `N7`. -/
theorem E0_N7 (k : ℂ) :
    J k colE 0 (N7 k)
      = (-2 : ℂ) • T4 k + T3 k :=
  actEp0_F2E1E1H1 k

/-- `e₀` on `N8`. -/
theorem E0_N8 (k : ℂ) :
    J k colE 0 (N8 k)
      = (-8 : ℂ) • T11 k + (-12 : ℂ) • T8 k + (-6 : ℂ) • T5 k :=
  actEp0_E2H1H1H1 k

/-- `e₀` on `N9`. -/
theorem E0_N9 (k : ℂ) :
    J k colE 0 (N9 k)
      = (-4 : ℂ) • T11 k + (2 : ℂ) • T7 k + (-2 : ℂ) • T6 k + T5 k :=
  actEp0_E2E1F1H1 k

/-- `e₀` on `N10`. -/
theorem E0_N10 (k : ℂ) :
    J k colE 0 (N10 k)
      = (-2 : ℂ) • T8 k + (-2 : ℂ) • T7 k :=
  actEp0_E2H2H1 k

/-- `e₀` on `N11`. -/
theorem E0_N11 (k : ℂ) :
    J k colE 0 (N11 k)
      = T7 k :=
  actEp0_E2F2E1 k

/-- `e₀` on `N12`. -/
theorem E0_N12 (k : ℂ) :
    J k colE 0 (N12 k)
      = T8 k :=
  actEp0_E2E2F1 k

/-- `e₀` on `N13`. -/
theorem E0_N13 (k : ℂ) :
    J k colE 0 (N13 k)
      = (-2 : ℂ) • T10 k + (-2 : ℂ) • T9 k :=
  actEp0_H3E1H1 k

/-- `e₀` on `N14`. -/
theorem E0_N14 (k : ℂ) :
    J k colE 0 (N14 k)
      = (-2 : ℂ) • T11 k :=
  actEp0_H3E2 k

/-- `e₀` on `N15`. -/
theorem E0_N15 (k : ℂ) :
    J k colE 0 (N15 k)
      = T9 k :=
  actEp0_F3E1E1 k

/-- `e₀` on `N16`. -/
theorem E0_N16 (k : ℂ) :
    J k colE 0 (N16 k)
      = (-4 : ℂ) • T11 k + (-4 : ℂ) • T10 k :=
  actEp0_E3H1H1 k

/-- `e₀` on `N17`. -/
theorem E0_N17 (k : ℂ) :
    J k colE 0 (N17 k)
      = T10 k :=
  actEp0_E3E1F1 k

/-- `e₀` on `N18`. -/
theorem E0_N18 (k : ℂ) :
    J k colE 0 (N18 k)
      = (-2 : ℂ) • T11 k :=
  actEp0_E3H2 k

/-- `e₀` on `N19`. -/
theorem E0_N19 (k : ℂ) :
    J k colE 0 (N19 k)
      = (-2 : ℂ) • T12 k :=
  actEp0_H4E1 k

/-- `e₀` on `N20`. -/
theorem E0_N20 (k : ℂ) :
    J k colE 0 (N20 k)
      = (-2 : ℂ) • T12 k :=
  actEp0_E4H1 k

/-- `e₀` on `N21`. -/
theorem E0_N21 (k : ℂ) :
    J k colE 0 (N21 k)
      = 0 :=
  actEp0_E5 k

/-- `f₁` on `N1`. -/
theorem F1_N1 (k : ℂ) :
    J k colF 1 (N1 k)
      = (48 : ℂ) • U13 k + (48 : ℂ) • U11 k + (-64 : ℂ) • U10 k + (-64 : ℂ) • U7 k
        + (24 : ℂ) • U2 k + (k) • U1 k :=
  actFp1_E1H1H1H1H1 k

/-- `f₁` on `N2`. -/
theorem F1_N2 (k : ℂ) :
    J k colF 1 (N2 k)
      = (4 : ℂ) • U3 k + (2*k + 2) • U2 k :=
  actFp1_E1E1F1H1H1 k

/-- `f₁` on `N3`. -/
theorem F1_N3 (k : ℂ) :
    J k colF 1 (N3 k)
      = (3*k + 6) • U3 k :=
  actFp1_E1E1E1F1F1 k

/-- `f₁` on `N4`. -/
theorem F1_N4 (k : ℂ) :
    J k colF 1 (N4 k)
      = (4 : ℂ) • U5 k + (k - 2) • U4 k + (2 : ℂ) • U2 k :=
  actFp1_H2E1H1H1 k

/-- `f₁` on `N5`. -/
theorem F1_N5 (k : ℂ) :
    J k colF 1 (N5 k)
      = (4 : ℂ) • U12 k + (2*k - 2) • U5 k + (2 : ℂ) • U3 k :=
  actFp1_H2E1E1F1 k

/-- `f₁` on `N6`. -/
theorem F1_N6 (k : ℂ) :
    J k colF 1 (N6 k)
      = (4 : ℂ) • U11 k + (k - 4) • U6 k + (4 : ℂ) • U5 k :=
  actFp1_H2H2E1 k

/-- `f₁` on `N7`. -/
theorem F1_N7 (k : ℂ) :
    J k colF 1 (N7 k)
      = (2*k - 2) • U7 k :=
  actFp1_F2E1E1H1 k

/-- `f₁` on `N8`. -/
theorem F1_N8 (k : ℂ) :
    J k colF 1 (N8 k)
      = (-16 : ℂ) • U9 k + (12 : ℂ) • U8 k + (-1 : ℂ) • U1 k :=
  actFp1_E2H1H1H1 k

/-- `f₁` on `N9`. -/
theorem F1_N9 (k : ℂ) :
    J k colF 1 (N9 k)
      = (2 : ℂ) • U10 k + (k) • U8 k + (2 : ℂ) • U7 k + (-1 : ℂ) • U2 k :=
  actFp1_E2E1F1H1 k

/-- `f₁` on `N10`. -/
theorem F1_N10 (k : ℂ) :
    J k colF 1 (N10 k)
      = (2 : ℂ) • U8 k + (-1 : ℂ) • U4 k :=
  actFp1_E2H2H1 k

/-- `f₁` on `N11`. -/
theorem F1_N11 (k : ℂ) :
    J k colF 1 (N11 k)
      = (2 : ℂ) • U13 k + (2 : ℂ) • U11 k + (k - 2) • U9 k + (-1 : ℂ) • U7 k :=
  actFp1_E2F2E1 k

/-- `f₁` on `N12`. -/
theorem F1_N12 (k : ℂ) :
    J k colF 1 (N12 k)
      = (-2 : ℂ) • U12 k + (4 : ℂ) • U9 k + (-2 : ℂ) • U8 k :=
  actFp1_E2E2F1 k

/-- `f₁` on `N13`. -/
theorem F1_N13 (k : ℂ) :
    J k colF 1 (N13 k)
      = (k) • U10 k + (2 : ℂ) • U7 k :=
  actFp1_H3E1H1 k

/-- `f₁` on `N14`. -/
theorem F1_N14 (k : ℂ) :
    J k colF 1 (N14 k)
      = (-2 : ℂ) • U13 k + (-1 : ℂ) • U10 k + (2 : ℂ) • U9 k :=
  actFp1_H3E2 k

/-- `f₁` on `N15`. -/
theorem F1_N15 (k : ℂ) :
    J k colF 1 (N15 k)
      = (2*k - 2) • U11 k :=
  actFp1_F3E1E1 k

/-- `f₁` on `N16`. -/
theorem F1_N16 (k : ℂ) :
    J k colF 1 (N16 k)
      = (4 : ℂ) • U12 k + (-1 : ℂ) • U4 k :=
  actFp1_E3H1H1 k

/-- `f₁` on `N17`. -/
theorem F1_N17 (k : ℂ) :
    J k colF 1 (N17 k)
      = (k + 2) • U12 k + (-1 : ℂ) • U5 k :=
  actFp1_E3E1F1 k

/-- `f₁` on `N18`. -/
theorem F1_N18 (k : ℂ) :
    J k colF 1 (N18 k)
      = (2 : ℂ) • U12 k + (-1 : ℂ) • U6 k :=
  actFp1_E3H2 k

/-- `f₁` on `N19`. -/
theorem F1_N19 (k : ℂ) :
    J k colF 1 (N19 k)
      = (k) • U13 k + (2 : ℂ) • U11 k :=
  actFp1_H4E1 k

/-- `f₁` on `N20`. -/
theorem F1_N20 (k : ℂ) :
    J k colF 1 (N20 k)
      = (-1 : ℂ) • U10 k :=
  actFp1_E4H1 k

/-- `f₁` on `N21`. -/
theorem F1_N21 (k : ℂ) :
    J k colF 1 (N21 k)
      = (-1 : ℂ) • U13 k :=
  actFp1_E5 k

/-- Cartan charge of `N1` is `+2`. -/
theorem H0_N1 (k : ℂ) : J k colH 0 (N1 k) = (2 : ℂ) • N1 k :=
  actHp0_E1H1H1H1H1 k

/-- Cartan charge of `N2` is `+2`. -/
theorem H0_N2 (k : ℂ) : J k colH 0 (N2 k) = (2 : ℂ) • N2 k :=
  actHp0_E1E1F1H1H1 k

/-- Cartan charge of `N3` is `+2`. -/
theorem H0_N3 (k : ℂ) : J k colH 0 (N3 k) = (2 : ℂ) • N3 k :=
  actHp0_E1E1E1F1F1 k

/-- Cartan charge of `N4` is `+2`. -/
theorem H0_N4 (k : ℂ) : J k colH 0 (N4 k) = (2 : ℂ) • N4 k :=
  actHp0_H2E1H1H1 k

/-- Cartan charge of `N5` is `+2`. -/
theorem H0_N5 (k : ℂ) : J k colH 0 (N5 k) = (2 : ℂ) • N5 k :=
  actHp0_H2E1E1F1 k

/-- Cartan charge of `N6` is `+2`. -/
theorem H0_N6 (k : ℂ) : J k colH 0 (N6 k) = (2 : ℂ) • N6 k :=
  actHp0_H2H2E1 k

/-- Cartan charge of `N7` is `+2`. -/
theorem H0_N7 (k : ℂ) : J k colH 0 (N7 k) = (2 : ℂ) • N7 k :=
  actHp0_F2E1E1H1 k

/-- Cartan charge of `N8` is `+2`. -/
theorem H0_N8 (k : ℂ) : J k colH 0 (N8 k) = (2 : ℂ) • N8 k :=
  actHp0_E2H1H1H1 k

/-- Cartan charge of `N9` is `+2`. -/
theorem H0_N9 (k : ℂ) : J k colH 0 (N9 k) = (2 : ℂ) • N9 k :=
  actHp0_E2E1F1H1 k

/-- Cartan charge of `N10` is `+2`. -/
theorem H0_N10 (k : ℂ) : J k colH 0 (N10 k) = (2 : ℂ) • N10 k :=
  actHp0_E2H2H1 k

/-- Cartan charge of `N11` is `+2`. -/
theorem H0_N11 (k : ℂ) : J k colH 0 (N11 k) = (2 : ℂ) • N11 k :=
  actHp0_E2F2E1 k

/-- Cartan charge of `N12` is `+2`. -/
theorem H0_N12 (k : ℂ) : J k colH 0 (N12 k) = (2 : ℂ) • N12 k :=
  actHp0_E2E2F1 k

/-- Cartan charge of `N13` is `+2`. -/
theorem H0_N13 (k : ℂ) : J k colH 0 (N13 k) = (2 : ℂ) • N13 k :=
  actHp0_H3E1H1 k

/-- Cartan charge of `N14` is `+2`. -/
theorem H0_N14 (k : ℂ) : J k colH 0 (N14 k) = (2 : ℂ) • N14 k :=
  actHp0_H3E2 k

/-- Cartan charge of `N15` is `+2`. -/
theorem H0_N15 (k : ℂ) : J k colH 0 (N15 k) = (2 : ℂ) • N15 k :=
  actHp0_F3E1E1 k

/-- Cartan charge of `N16` is `+2`. -/
theorem H0_N16 (k : ℂ) : J k colH 0 (N16 k) = (2 : ℂ) • N16 k :=
  actHp0_E3H1H1 k

/-- Cartan charge of `N17` is `+2`. -/
theorem H0_N17 (k : ℂ) : J k colH 0 (N17 k) = (2 : ℂ) • N17 k :=
  actHp0_E3E1F1 k

/-- Cartan charge of `N18` is `+2`. -/
theorem H0_N18 (k : ℂ) : J k colH 0 (N18 k) = (2 : ℂ) • N18 k :=
  actHp0_E3H2 k

/-- Cartan charge of `N19` is `+2`. -/
theorem H0_N19 (k : ℂ) : J k colH 0 (N19 k) = (2 : ℂ) • N19 k :=
  actHp0_H4E1 k

/-- Cartan charge of `N20` is `+2`. -/
theorem H0_N20 (k : ℂ) : J k colH 0 (N20 k) = (2 : ℂ) • N20 k :=
  actHp0_E4H1 k

/-- Cartan charge of `N21` is `+2`. -/
theorem H0_N21 (k : ℂ) : J k colH 0 (N21 k) = (2 : ℂ) • N21 k :=
  actHp0_E5 k

/-! ## §6  Grading: every ansatz monomial has conformal weight `5` -/

/-- One step of the energy bookkeeping: `J k a m` lowers the energy label by `m`. -/
theorem mem_step {k : ℂ} (a : Fin 3) (m n p : ℤ) {v : WakModule k}
    (hv : v ∈ gradingZA k n) (hp : n - m = p) : J k a m v ∈ gradingZA k p := by
  have h := J_mem_gradingZA k a m n hv
  rwa [hp] at h

/-- `N1` has conformal weight `5`. -/
theorem N1_mem (k : ℂ) : N1 k ∈ gradingZA k 5 := by
  rw [N1_def]
  have g1 := mem_step colH (-1) 0 1 (vacuumA_mem_gradingZA_zero k) (by norm_num)
  have g2 := mem_step colH (-1) 1 2 g1 (by norm_num)
  have g3 := mem_step colH (-1) 2 3 g2 (by norm_num)
  have g4 := mem_step colH (-1) 3 4 g3 (by norm_num)
  exact mem_step colE (-1) 4 5 g4 (by norm_num)

/-- `N2` has conformal weight `5`. -/
theorem N2_mem (k : ℂ) : N2 k ∈ gradingZA k 5 := by
  rw [N2_def]
  have g1 := mem_step colH (-1) 0 1 (vacuumA_mem_gradingZA_zero k) (by norm_num)
  have g2 := mem_step colH (-1) 1 2 g1 (by norm_num)
  have g3 := mem_step colF (-1) 2 3 g2 (by norm_num)
  have g4 := mem_step colE (-1) 3 4 g3 (by norm_num)
  exact mem_step colE (-1) 4 5 g4 (by norm_num)

/-- `N3` has conformal weight `5`. -/
theorem N3_mem (k : ℂ) : N3 k ∈ gradingZA k 5 := by
  rw [N3_def]
  have g1 := mem_step colF (-1) 0 1 (vacuumA_mem_gradingZA_zero k) (by norm_num)
  have g2 := mem_step colF (-1) 1 2 g1 (by norm_num)
  have g3 := mem_step colE (-1) 2 3 g2 (by norm_num)
  have g4 := mem_step colE (-1) 3 4 g3 (by norm_num)
  exact mem_step colE (-1) 4 5 g4 (by norm_num)

/-- `N4` has conformal weight `5`. -/
theorem N4_mem (k : ℂ) : N4 k ∈ gradingZA k 5 := by
  rw [N4_def]
  have g1 := mem_step colH (-1) 0 1 (vacuumA_mem_gradingZA_zero k) (by norm_num)
  have g2 := mem_step colH (-1) 1 2 g1 (by norm_num)
  have g3 := mem_step colE (-1) 2 3 g2 (by norm_num)
  exact mem_step colH (-2) 3 5 g3 (by norm_num)

/-- `N5` has conformal weight `5`. -/
theorem N5_mem (k : ℂ) : N5 k ∈ gradingZA k 5 := by
  rw [N5_def]
  have g1 := mem_step colF (-1) 0 1 (vacuumA_mem_gradingZA_zero k) (by norm_num)
  have g2 := mem_step colE (-1) 1 2 g1 (by norm_num)
  have g3 := mem_step colE (-1) 2 3 g2 (by norm_num)
  exact mem_step colH (-2) 3 5 g3 (by norm_num)

/-- `N6` has conformal weight `5`. -/
theorem N6_mem (k : ℂ) : N6 k ∈ gradingZA k 5 := by
  rw [N6_def]
  have g1 := mem_step colE (-1) 0 1 (vacuumA_mem_gradingZA_zero k) (by norm_num)
  have g2 := mem_step colH (-2) 1 3 g1 (by norm_num)
  exact mem_step colH (-2) 3 5 g2 (by norm_num)

/-- `N7` has conformal weight `5`. -/
theorem N7_mem (k : ℂ) : N7 k ∈ gradingZA k 5 := by
  rw [N7_def]
  have g1 := mem_step colH (-1) 0 1 (vacuumA_mem_gradingZA_zero k) (by norm_num)
  have g2 := mem_step colE (-1) 1 2 g1 (by norm_num)
  have g3 := mem_step colE (-1) 2 3 g2 (by norm_num)
  exact mem_step colF (-2) 3 5 g3 (by norm_num)

/-- `N8` has conformal weight `5`. -/
theorem N8_mem (k : ℂ) : N8 k ∈ gradingZA k 5 := by
  rw [N8_def]
  have g1 := mem_step colH (-1) 0 1 (vacuumA_mem_gradingZA_zero k) (by norm_num)
  have g2 := mem_step colH (-1) 1 2 g1 (by norm_num)
  have g3 := mem_step colH (-1) 2 3 g2 (by norm_num)
  exact mem_step colE (-2) 3 5 g3 (by norm_num)

/-- `N9` has conformal weight `5`. -/
theorem N9_mem (k : ℂ) : N9 k ∈ gradingZA k 5 := by
  rw [N9_def]
  have g1 := mem_step colH (-1) 0 1 (vacuumA_mem_gradingZA_zero k) (by norm_num)
  have g2 := mem_step colF (-1) 1 2 g1 (by norm_num)
  have g3 := mem_step colE (-1) 2 3 g2 (by norm_num)
  exact mem_step colE (-2) 3 5 g3 (by norm_num)

/-- `N10` has conformal weight `5`. -/
theorem N10_mem (k : ℂ) : N10 k ∈ gradingZA k 5 := by
  rw [N10_def]
  have g1 := mem_step colH (-1) 0 1 (vacuumA_mem_gradingZA_zero k) (by norm_num)
  have g2 := mem_step colH (-2) 1 3 g1 (by norm_num)
  exact mem_step colE (-2) 3 5 g2 (by norm_num)

/-- `N11` has conformal weight `5`. -/
theorem N11_mem (k : ℂ) : N11 k ∈ gradingZA k 5 := by
  rw [N11_def]
  have g1 := mem_step colE (-1) 0 1 (vacuumA_mem_gradingZA_zero k) (by norm_num)
  have g2 := mem_step colF (-2) 1 3 g1 (by norm_num)
  exact mem_step colE (-2) 3 5 g2 (by norm_num)

/-- `N12` has conformal weight `5`. -/
theorem N12_mem (k : ℂ) : N12 k ∈ gradingZA k 5 := by
  rw [N12_def]
  have g1 := mem_step colF (-1) 0 1 (vacuumA_mem_gradingZA_zero k) (by norm_num)
  have g2 := mem_step colE (-2) 1 3 g1 (by norm_num)
  exact mem_step colE (-2) 3 5 g2 (by norm_num)

/-- `N13` has conformal weight `5`. -/
theorem N13_mem (k : ℂ) : N13 k ∈ gradingZA k 5 := by
  rw [N13_def]
  have g1 := mem_step colH (-1) 0 1 (vacuumA_mem_gradingZA_zero k) (by norm_num)
  have g2 := mem_step colE (-1) 1 2 g1 (by norm_num)
  exact mem_step colH (-3) 2 5 g2 (by norm_num)

/-- `N14` has conformal weight `5`. -/
theorem N14_mem (k : ℂ) : N14 k ∈ gradingZA k 5 := by
  rw [N14_def]
  have g1 := mem_step colE (-2) 0 2 (vacuumA_mem_gradingZA_zero k) (by norm_num)
  exact mem_step colH (-3) 2 5 g1 (by norm_num)

/-- `N15` has conformal weight `5`. -/
theorem N15_mem (k : ℂ) : N15 k ∈ gradingZA k 5 := by
  rw [N15_def]
  have g1 := mem_step colE (-1) 0 1 (vacuumA_mem_gradingZA_zero k) (by norm_num)
  have g2 := mem_step colE (-1) 1 2 g1 (by norm_num)
  exact mem_step colF (-3) 2 5 g2 (by norm_num)

/-- `N16` has conformal weight `5`. -/
theorem N16_mem (k : ℂ) : N16 k ∈ gradingZA k 5 := by
  rw [N16_def]
  have g1 := mem_step colH (-1) 0 1 (vacuumA_mem_gradingZA_zero k) (by norm_num)
  have g2 := mem_step colH (-1) 1 2 g1 (by norm_num)
  exact mem_step colE (-3) 2 5 g2 (by norm_num)

/-- `N17` has conformal weight `5`. -/
theorem N17_mem (k : ℂ) : N17 k ∈ gradingZA k 5 := by
  rw [N17_def]
  have g1 := mem_step colF (-1) 0 1 (vacuumA_mem_gradingZA_zero k) (by norm_num)
  have g2 := mem_step colE (-1) 1 2 g1 (by norm_num)
  exact mem_step colE (-3) 2 5 g2 (by norm_num)

/-- `N18` has conformal weight `5`. -/
theorem N18_mem (k : ℂ) : N18 k ∈ gradingZA k 5 := by
  rw [N18_def]
  have g1 := mem_step colH (-2) 0 2 (vacuumA_mem_gradingZA_zero k) (by norm_num)
  exact mem_step colE (-3) 2 5 g1 (by norm_num)

/-- `N19` has conformal weight `5`. -/
theorem N19_mem (k : ℂ) : N19 k ∈ gradingZA k 5 := by
  rw [N19_def]
  have g1 := mem_step colE (-1) 0 1 (vacuumA_mem_gradingZA_zero k) (by norm_num)
  exact mem_step colH (-4) 1 5 g1 (by norm_num)

/-- `N20` has conformal weight `5`. -/
theorem N20_mem (k : ℂ) : N20 k ∈ gradingZA k 5 := by
  rw [N20_def]
  have g1 := mem_step colH (-1) 0 1 (vacuumA_mem_gradingZA_zero k) (by norm_num)
  exact mem_step colE (-4) 1 5 g1 (by norm_num)

/-- `N21` has conformal weight `5`. -/
theorem N21_mem (k : ℂ) : N21 k ∈ gradingZA k 5 := by
  rw [N21_def]
  exact mem_step colE (-5) 0 5 (vacuumA_mem_gradingZA_zero k) (by norm_num)


/-! ## §7  The 21-parameter ansatz -/

/-- The general element of the span of the 21 weight-5, charge-`+2` monomials. -/
noncomputable def ansatz5 (k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : ℂ)
    (c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 : ℂ) : WakModule k :=
  c1 • N1 k + c2 • N2 k + c3 • N3 k + c4 • N4 k + c5 • N5 k + c6 • N6 k + c7 • N7 k
    + c8 • N8 k + c9 • N9 k + c10 • N10 k + c11 • N11 k + c12 • N12 k + c13 • N13 k
    + c14 • N14 k + c15 • N15 k + c16 • N16 k + c17 • N17 k + c18 • N18 k + c19 • N19 k
    + c20 • N20 k + c21 • N21 k

/-- Unfolding lemma for `ansatz5`. -/
theorem ansatz5_def (k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : ℂ)
    (c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 : ℂ) :
    ansatz5 k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
        c17 c18 c19 c20 c21
      = c1 • N1 k + c2 • N2 k + c3 • N3 k + c4 • N4 k + c5 • N5 k + c6 • N6 k + c7 • N7 k
        + c8 • N8 k + c9 • N9 k + c10 • N10 k + c11 • N11 k + c12 • N12 k + c13 • N13 k
        + c14 • N14 k + c15 • N15 k + c16 • N16 k + c17 • N17 k + c18 • N18 k + c19 • N19 k
        + c20 • N20 k + c21 • N21 k := rfl

/-- Every element of the ansatz has conformal weight `5`. -/
theorem ansatz5_mem (k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : ℂ)
    (c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 : ℂ) :
    ansatz5 k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
        c17 c18 c19 c20 c21 ∈ gradingZA k 5 := by
  rw [ansatz5_def]
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (N21_mem k))
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (N20_mem k))
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (N19_mem k))
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (N18_mem k))
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (N17_mem k))
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (N16_mem k))
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (N15_mem k))
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (N14_mem k))
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (N13_mem k))
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (N12_mem k))
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (N11_mem k))
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (N10_mem k))
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (N9_mem k))
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (N8_mem k))
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (N7_mem k))
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (N6_mem k))
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (N5_mem k))
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (N4_mem k))
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (N3_mem k))
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (N2_mem k))
  exact Submodule.smul_mem _ _ (N1_mem k)

/-- The image of the ansatz under `e₀`, in the 12 weight-5 charge-`+4` monomials. -/
theorem E0_ansatz5 (k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : ℂ)
    (c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 : ℂ) :
    J k colE 0 (ansatz5 k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
        c17 c18 c19 c20 c21)
      = (-8*c1 + c2) • T1 k + (-4*c2 + 2*c3) • T2 k + (4*c2 - 4*c4 + c5 + c7) • T3 k
        + (-2*c3 - 2*c7) • T4 k + (-24*c1 - 2*c4 - 6*c8 + c9) • T5 k + (-4*c2 - 2*c5 - 2*c9) • T6 k
        + (-2*c10 + c11 - 4*c4 - 4*c6 + 2*c9) • T7 k + (-2*c10 + c12 - 12*c8) • T8 k
        + (-2*c13 + c15 + 4*c2 - 6*c3) • T9 k + (-32*c1 - 2*c13 - 4*c16 + c17 - 16*c2) • T10 k
        + (-2*c14 - 4*c16 - 2*c18 - 8*c8 - 4*c9) • T11 k
        + (-16*c1 - 2*c19 - 16*c2 - 2*c20 + 12*c3 - 8*c4 - 4*c6) • T12 k := by
  rw [ansatz5_def]
  simp only [map_add, map_smul, E0_N1, E0_N2, E0_N3, E0_N4, E0_N5, E0_N6, E0_N7, E0_N8, E0_N9,
    E0_N10, E0_N11, E0_N12, E0_N13, E0_N14, E0_N15, E0_N16, E0_N17, E0_N18, E0_N19, E0_N20,
    E0_N21]
  module

/-- The image of the ansatz under `f₁`, in the 13 weight-4 charge-`0` monomials. -/
theorem F1_ansatz5 (k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : ℂ)
    (c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 : ℂ) :
    J k colF 1 (ansatz5 k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
        c17 c18 c19 c20 c21)
      = (c1*k - c8) • U1 k + (24*c1 + 2*c2*k + 2*c2 + 2*c4 - c9) • U2 k
        + (4*c2 + 3*c3*k + 6*c3 + 2*c5) • U3 k + (-c10 - c16 + c4*k - 2*c4) • U4 k
        + (-c17 + 4*c4 + 2*c5*k - 2*c5 + 4*c6) • U5 k + (-c18 + c6*k - 4*c6) • U6 k
        + (-64*c1 - c11 + 2*c13 + 2*c7*k - 2*c7 + 2*c9) • U7 k
        + (2*c10 - 2*c12 + 12*c8 + c9*k) • U8 k + (c11*k - 2*c11 + 4*c12 + 2*c14 - 16*c8) • U9 k
        + (-64*c1 + c13*k - c14 - c20 + 2*c9) • U10 k
        + (48*c1 + 2*c11 + 2*c15*k - 2*c15 + 2*c19 + 4*c6) • U11 k
        + (-2*c12 + 4*c16 + c17*k + 2*c17 + 2*c18 + 4*c5) • U12 k
        + (48*c1 + 2*c11 - 2*c14 + c19*k - c21) • U13 k := by
  rw [ansatz5_def]
  simp only [map_add, map_smul, F1_N1, F1_N2, F1_N3, F1_N4, F1_N5, F1_N6, F1_N7, F1_N8, F1_N9,
    F1_N10, F1_N11, F1_N12, F1_N13, F1_N14, F1_N15, F1_N16, F1_N17, F1_N18, F1_N19, F1_N20,
    F1_N21]
  module

/-- The whole ansatz has Cartan charge `+2`. -/
theorem H0_ansatz5 (k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : ℂ)
    (c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 : ℂ) :
    J k colH 0 (ansatz5 k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
        c17 c18 c19 c20 c21)
      = (2 : ℂ) • (ansatz5 k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
        c17 c18 c19 c20 c21) := by
  rw [ansatz5_def]
  simp only [map_add, map_smul, H0_N1, H0_N2, H0_N3, H0_N4, H0_N5, H0_N6, H0_N7, H0_N8, H0_N9,
    H0_N10, H0_N11, H0_N12, H0_N13, H0_N14, H0_N15, H0_N16, H0_N17, H0_N18, H0_N19, H0_N20,
    H0_N21]
  module

/-- **The singularity system.**  The 25 scalar equations obtained by setting to zero every
coefficient of `e₀ s` in `T1, …, T12` and every coefficient of `f₁ s` in `U1, …, U13`. -/
def SingSys5 (k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : ℂ)
    (c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 : ℂ) : Prop :=
  -8*c1 + c2 = 0 ∧
    -4*c2 + 2*c3 = 0 ∧
    4*c2 - 4*c4 + c5 + c7 = 0 ∧
    -2*c3 - 2*c7 = 0 ∧
    -24*c1 - 2*c4 - 6*c8 + c9 = 0 ∧
    -4*c2 - 2*c5 - 2*c9 = 0 ∧
    -2*c10 + c11 - 4*c4 - 4*c6 + 2*c9 = 0 ∧
    -2*c10 + c12 - 12*c8 = 0 ∧
    -2*c13 + c15 + 4*c2 - 6*c3 = 0 ∧
    -32*c1 - 2*c13 - 4*c16 + c17 - 16*c2 = 0 ∧
    -2*c14 - 4*c16 - 2*c18 - 8*c8 - 4*c9 = 0 ∧
    -16*c1 - 2*c19 - 16*c2 - 2*c20 + 12*c3 - 8*c4 - 4*c6 = 0 ∧
    c1*k - c8 = 0 ∧
    24*c1 + 2*c2*k + 2*c2 + 2*c4 - c9 = 0 ∧
    4*c2 + 3*c3*k + 6*c3 + 2*c5 = 0 ∧
    -c10 - c16 + c4*k - 2*c4 = 0 ∧
    -c17 + 4*c4 + 2*c5*k - 2*c5 + 4*c6 = 0 ∧
    -c18 + c6*k - 4*c6 = 0 ∧
    -64*c1 - c11 + 2*c13 + 2*c7*k - 2*c7 + 2*c9 = 0 ∧
    2*c10 - 2*c12 + 12*c8 + c9*k = 0 ∧
    c11*k - 2*c11 + 4*c12 + 2*c14 - 16*c8 = 0 ∧
    -64*c1 + c13*k - c14 - c20 + 2*c9 = 0 ∧
    48*c1 + 2*c11 + 2*c15*k - 2*c15 + 2*c19 + 4*c6 = 0 ∧
    -2*c12 + 4*c16 + c17*k + 2*c17 + 2*c18 + 4*c5 = 0 ∧
    48*c1 + 2*c11 - 2*c14 + c19*k - c21 = 0

/-- If the system holds then `e₀` annihilates the ansatz. -/
theorem E0_ansatz5_eq_zero {k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : ℂ}
    {c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 : ℂ}
    (h : SingSys5 k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
      c17 c18 c19 c20 c21) :
    J k colE 0 (ansatz5 k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
        c17 c18 c19 c20 c21) = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := h
  rw [E0_ansatz5, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  simp

/-- If the system holds then `f₁` annihilates the ansatz. -/
theorem F1_ansatz5_eq_zero {k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : ℂ}
    {c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 : ℂ}
    (h : SingSys5 k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
      c17 c18 c19 c20 c21) :
    J k colF 1 (ansatz5 k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
        c17 c18 c19 c20 c21) = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := h
  rw [F1_ansatz5, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
  simp

/-! ## §8  Solving the system: **the level is a theorem** -/

/-- **The elimination.**  Seven of the coefficients are pinned to `c1` by the system, and the
last equation used forces `(5k + 8)·c1 = 0`.  This is where the level `k = -8/5` is *derived*. -/
theorem SingSys5_param {k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : ℂ}
    {c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 : ℂ}
    (h : SingSys5 k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
      c17 c18 c19 c20 c21) :
    c2 = 8 * c1 ∧ c3 = 16 * c1 ∧ c4 = (9 * k + 12) * c1 ∧ c5 = (-24 * k - 64) * c1
      ∧ c7 = -16 * c1 ∧ c8 = k * c1 ∧ c9 = (24 * k + 48) * c1 ∧ (5 * k + 8) * c1 = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := h
  refine ⟨by linear_combination h1, by linear_combination (2) * h1 + (1/2) * h2, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · linear_combination (2*k + 2) * h1 + (-1/12) * h2 + (-1/6) * h3 + (-1/12) * h4 + (-7/6) * h5
      + (-1/12) * h6 + (7) * h13 - h14
  · linear_combination (-4*k - 6) * h1 + (1/6) * h2 + (1/3) * h3 + (1/6) * h4 + (4/3) * h5
      + (-1/3) * h6 + (-8) * h13 + (2) * h14
  · linear_combination (-2) * h1 + (-1/2) * h2 + (-1/2) * h4
  · linear_combination -h13
  · linear_combination (4*k + 4) * h1 + (-1/6) * h2 + (-1/3) * h3 + (-1/6) * h4 + (-4/3) * h5
      + (-1/6) * h6 + (8) * h13 + (-2) * h14
  · linear_combination (-k - 1) * h1 + (1/2) * h5 + (-3) * h13 + (1/2) * h14

/-- If a solution has `c1 ≠ 0` then the level is `-8/5`. -/
theorem SingSys5_level {k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : ℂ}
    {c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 : ℂ}
    (h : SingSys5 k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
      c17 c18 c19 c20 c21) (hc : c1 ≠ 0) : 5 * k + 8 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, hlvl⟩ := SingSys5_param h
  exact (mul_eq_zero.mp hlvl).resolve_right hc

/-- **Away from `k = -8/5` the system has only the zero solution.** -/
theorem SingSys5_trivial_of_level {k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : ℂ}
    {c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 : ℂ}
    (h : SingSys5 k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
      c17 c18 c19 c20 c21) (hk : 5 * k + 8 ≠ 0) :
    c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 ∧ c7 = 0 ∧ c8 = 0 ∧ c9 = 0 ∧ c10 = 0
      ∧ c11 = 0 ∧ c12 = 0 ∧ c13 = 0 ∧ c14 = 0 ∧ c15 = 0 ∧ c16 = 0 ∧ c17 = 0 ∧ c18 = 0
      ∧ c19 = 0 ∧ c20 = 0 ∧ c21 = 0 := by
  have hlvl := (SingSys5_param h).2.2.2.2.2.2.2
  have hc1 : c1 = 0 := (mul_eq_zero.mp hlvl).resolve_left hk
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := h
  have hz2 : c2 = 0 := by linear_combination h1 + (8) * hc1
  have hz3 : c3 = 0 := by linear_combination (1/2) * h2 + (2) * hz2
  have hz8 : c8 = 0 := by linear_combination -h13 + (k) * hc1
  have hz7 : c7 = 0 := by linear_combination (-1/2) * h4 -hz3
  have hz5 : c5 = 0 := by linear_combination (1/2) * h15 + (-2) * hz2 + (-3*k/2 - 3) * hz3
  have hz9 : c9 = 0 := by linear_combination (-1/2) * h6 + (-2) * hz2 -hz5
  have hz4 : c4 = 0 := by linear_combination (-1/2) * h5 + (-12) * hc1 + (-3) * hz8 + (1/2) * hz9
  have hz12 : c12 = 0 := by linear_combination -h8 -h20 + (k) * hz9
  have hz10 : c10 = 0 := by linear_combination (-1/2) * h8 + (1/2) * hz12 + (-6) * hz8
  have hz16 : c16 = 0 := by linear_combination -h16 -hz10 + (k - 2) * hz4
  have hd11 : c11 = 4 * c6 := by linear_combination h7 + (2) * hz10 + (4) * hz4 + (-2) * hz9
  have hd13 : c13 = 2 * c6 := by
    linear_combination (1/2) * h19 + (32) * hc1 + (1/2) * hd11 + (1 - k) * hz7 -hz9
  have hd15 : c15 = 4 * c6 := by linear_combination h9 + (2) * hd13 + (-4) * hz2 + (6) * hz3
  have hd17 : c17 = 4 * c6 := by linear_combination -h17 + (4) * hz4 + (2*k - 2) * hz5
  have hd18 : c18 = (k - 4) * c6 := by linear_combination -h18
  have hd14 : c14 = (4 - k) * c6 := by
    linear_combination (-1/2) * h11 + (-2) * hz16 -hd18 + (-4) * hz8 + (-2) * hz9
  have hk6 : k * c6 = 0 := by
    linear_combination (1/2) * h21 + (1 - k/2) * hd11 + (-2) * hz12 -hd14 + (8) * hz8
  have hd19 : c19 = (-4*k - 2) * c6 := by
    linear_combination (1/2) * h23 + (-24) * hc1 -hd11 + (1 - k) * hd15
  have hd20 : c20 = (3*k - 4) * c6 := by
    linear_combination -h22 + (-64) * hc1 + (k) * hd13 -hd14 + (2) * hz9
  have hd6 : (2*k + 8) * c6 = 0 := by
    linear_combination h12 + (16) * hc1 + (16) * hz2 + (-12) * hz3 + (8) * hz4 + (2) * hd19
      + (2) * hd20
  have hz6 : c6 = 0 := by linear_combination (1/8) * hd6 + (-1/4) * hk6
  have hz11 : c11 = 0 := by linear_combination hd11 + (4) * hz6
  have hz13 : c13 = 0 := by linear_combination hd13 + (2) * hz6
  have hz14 : c14 = 0 := by linear_combination hd14 + (4 - k) * hz6
  have hz15 : c15 = 0 := by linear_combination hd15 + (4) * hz6
  have hz17 : c17 = 0 := by linear_combination hd17 + (4) * hz6
  have hz18 : c18 = 0 := by linear_combination hd18 + (k - 4) * hz6
  have hz19 : c19 = 0 := by linear_combination hd19 + (-4*k - 2) * hz6
  have hz20 : c20 = 0 := by linear_combination hd20 + (3*k - 4) * hz6
  have hz21 : c21 = 0 := by
    linear_combination -h25 + (48) * hc1 + (2) * hz11 + (-2) * hz14 + (k) * hz19
  exact ⟨hc1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz9, hz10, hz11, hz12, hz13, hz14, hz15, hz16,
    hz17, hz18, hz19, hz20, hz21⟩

/-- At `k = -8/5` the explicit integral vector solves the system. -/
theorem SingSys5_of_level {k : ℂ} (hk : 5 * k + 8 = 0) :
    SingSys5 k 625 5000 10000 (-1500) (-16000) 300 (-10000) (-1000) 6000 1200 (-14400) (-9600)
      (-19200) (-14720) 1600 4200
      78400 (-1680) 2960 17440 25904 := by
  have hk' : k = -8 / 5 := by linear_combination hk / 5
  subst hk'
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **The level is a theorem, not an assumption.**  A nonzero solution of the weight-5,
charge-`+2` singularity system exists exactly when `5k + 8 = 0`, i.e. `k = -8/5`. -/
theorem exists_nonzero_solution_iff (k : ℂ) :
    (∃ c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 : ℂ,
        ¬(c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 ∧ c7 = 0 ∧ c8 = 0 ∧ c9 = 0
            ∧ c10 = 0 ∧ c11 = 0 ∧ c12 = 0 ∧ c13 = 0 ∧ c14 = 0 ∧ c15 = 0 ∧ c16 = 0 ∧ c17 = 0
            ∧ c18 = 0 ∧ c19 = 0 ∧ c20 = 0 ∧ c21 = 0)
          ∧ SingSys5 k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19
              c20 c21) ↔ 5 * k + 8 = 0 := by
  constructor
  · rintro ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18,
      c19, c20, c21, hne, h⟩
    by_contra hk
    exact hne (SingSys5_trivial_of_level h hk)
  · intro hk
    refine ⟨625, 5000, 10000, (-1500) , (-16000) , 300, (-10000) , (-1000) , 6000, 1200, (-14400)
      , (-9600) , (-19200) , (-14720) ,
      1600, 4200, 78400, (-1680), 2960, 17440, 25904, ?_, SingSys5_of_level hk⟩
    rintro ⟨hz, -⟩
    norm_num at hz


/-! ## §9  `e₀` and `f₁` generate the whole positive part -/

/-- **The whole positive part annihilates.**  A weight-5 vector killed by the two affine
Chevalley raising generators `e₀` and `f₁` is killed by every mode of positive level: `h₁` and
`e₁` follow by two brackets, levels `2, …, 5` by four more rounds of the same recursion, and
levels `≥ 6` by the energy grading. -/
theorem pos_ann5 {k : ℂ} {v : WakModule k} (hv : v ∈ gradingZA k 5)
    (hE0 : J k colE 0 v = 0) (hF1 : J k colF 1 v = 0)
    (a : Fin 3) {m : ℤ} (hm : 1 ≤ m) : J k a m v = 0 := by
  have hH1 : J k colH 1 v = 0 := by
    have h := FEs k 1 0 1 (by norm_num) (by norm_num) v
    rw [hE0, hF1, map_zero, map_zero, zero_sub] at h
    exact neg_eq_zero.mp h.symm
  have hE1 : J k colE 1 v = 0 := by
    have h := EHs k 0 1 1 (by norm_num) v
    rw [hH1, hE0, map_zero, map_zero, zero_sub] at h
    exact of_two_smul_eq_zero (neg_eq_zero.mp h.symm)
  have hE2 : J k colE 2 v = 0 := by
    have h := HEs k 1 1 2 (by norm_num) v
    rw [hE1, hH1, map_zero, map_zero, zero_add] at h
    exact of_two_smul_eq_zero h.symm
  have hF2 : J k colF 2 v = 0 := by
    have h := HFs k 1 1 2 (by norm_num) v
    rw [hF1, hH1, map_zero, map_zero, zero_sub] at h
    exact of_two_smul_eq_zero (neg_eq_zero.mp h.symm)
  have hH2 : J k colH 2 v = 0 := by
    have h := EFs k 1 1 2 (by norm_num) (by norm_num) v
    rw [hF1, hE1, map_zero, map_zero, zero_add] at h
    exact h.symm
  have hE3 : J k colE 3 v = 0 := by
    have h := HEs k 1 2 3 (by norm_num) v
    rw [hE2, hH1, map_zero, map_zero, zero_add] at h
    exact of_two_smul_eq_zero h.symm
  have hF3 : J k colF 3 v = 0 := by
    have h := HFs k 1 2 3 (by norm_num) v
    rw [hF2, hH1, map_zero, map_zero, zero_sub] at h
    exact of_two_smul_eq_zero (neg_eq_zero.mp h.symm)
  have hH3 : J k colH 3 v = 0 := by
    have h := EFs k 1 2 3 (by norm_num) (by norm_num) v
    rw [hF2, hE1, map_zero, map_zero, zero_add] at h
    exact h.symm
  have hE4 : J k colE 4 v = 0 := by
    have h := HEs k 1 3 4 (by norm_num) v
    rw [hE3, hH1, map_zero, map_zero, zero_add] at h
    exact of_two_smul_eq_zero h.symm
  have hF4 : J k colF 4 v = 0 := by
    have h := HFs k 1 3 4 (by norm_num) v
    rw [hF3, hH1, map_zero, map_zero, zero_sub] at h
    exact of_two_smul_eq_zero (neg_eq_zero.mp h.symm)
  have hH4 : J k colH 4 v = 0 := by
    have h := EFs k 1 3 4 (by norm_num) (by norm_num) v
    rw [hF3, hE1, map_zero, map_zero, zero_add] at h
    exact h.symm
  have hE5 : J k colE 5 v = 0 := by
    have h := HEs k 1 4 5 (by norm_num) v
    rw [hE4, hH1, map_zero, map_zero, zero_add] at h
    exact of_two_smul_eq_zero h.symm
  have hF5 : J k colF 5 v = 0 := by
    have h := HFs k 1 4 5 (by norm_num) v
    rw [hF4, hH1, map_zero, map_zero, zero_sub] at h
    exact of_two_smul_eq_zero (neg_eq_zero.mp h.symm)
  have hH5 : J k colH 5 v = 0 := by
    have h := EFs k 1 4 5 (by norm_num) (by norm_num) v
    rw [hF4, hE1, map_zero, map_zero, zero_add] at h
    exact h.symm
  rcases lt_or_ge m 6 with hlt | hge
  · have key : ∀ b : Fin 3, J k b 1 v = 0 ∧ J k b 2 v = 0 ∧ J k b 3 v = 0 ∧ J k b 4 v = 0
        ∧ J k b 5 v = 0 := by
      intro b
      fin_cases b
      · exact ⟨hE1, hE2, hE3, hE4, hE5⟩
      · exact ⟨hF1, hF2, hF3, hF4, hF5⟩
      · exact ⟨hH1, hH2, hH3, hH4, hH5⟩
    have hm5 : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
    rcases hm5 with rfl | rfl | rfl | rfl | rfl
    · exact (key a).1
    · exact (key a).2.1
    · exact (key a).2.2.1
    · exact (key a).2.2.2.1
    · exact (key a).2.2.2.2
  · exact J_gradingZA_eq_zero k a (by omega) hv


/-! ## §10  The singular vector at `k = -8/5` -/

/-- **The weight-5 singular vector of `V^{-8/5}(𝔰𝔩₂)`**, with primitive integral coefficients
in the normally ordered PBW basis `N1, …, N21`. -/
noncomputable def sl2SingularLY : WakModule (-8 / 5 : ℂ) :=
  ansatz5 (-8 / 5) 625 5000 10000 (-1500) (-16000) 300 (-10000) (-1000) 6000 1200 (-14400) (-9600)
    (-19200) (-14720) 1600 4200
    78400 (-1680) 2960 17440 25904

/-- Unfolding lemma for `sl2SingularLY`. -/
theorem sl2SingularLY_def :
    sl2SingularLY = ansatz5 (-8 / 5 : ℂ) 625 5000 10000 (-1500) (-16000) 300 (-10000) (-1000) 6000
      1200 (-14400) (-9600) (-19200) (-14720) 1600 4200
      78400 (-1680) 2960 17440 25904 := rfl

/-- The explicit coefficients satisfy the singularity system at `k = -8/5`. -/
theorem SingSys5_LY :
    SingSys5 (-8 / 5 : ℂ) 625 5000 10000 (-1500) (-16000) 300 (-10000) (-1000) 6000 1200 (-14400)
      (-9600) (-19200) (-14720) 1600 4200
      78400 (-1680) 2960 17440 25904 :=
  SingSys5_of_level (by norm_num)

/-- `e₀` annihilates the singular vector. -/
theorem sl2SingularLY_E0 : J (-8 / 5 : ℂ) colE 0 sl2SingularLY = 0 :=
  E0_ansatz5_eq_zero SingSys5_LY

/-- `f₁` annihilates the singular vector. -/
theorem sl2SingularLY_F1 : J (-8 / 5 : ℂ) colF 1 sl2SingularLY = 0 :=
  F1_ansatz5_eq_zero SingSys5_LY

/-- The singular vector has conformal weight `5`. -/
theorem sl2SingularLY_mem : sl2SingularLY ∈ gradingZA (-8 / 5 : ℂ) 5 :=
  ansatz5_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **`s` is a singular vector**: every mode of positive level kills it. -/
theorem sl2SingularLY_pos (a : Fin 3) {m : ℤ} (hm : 1 ≤ m) :
    J (-8 / 5 : ℂ) a m sl2SingularLY = 0 :=
  pos_ann5 sl2SingularLY_mem sl2SingularLY_E0 sl2SingularLY_F1 a hm

/-- `e₁` annihilates the singular vector. -/
theorem sl2SingularLY_E1 : J (-8 / 5 : ℂ) colE 1 sl2SingularLY = 0 :=
  sl2SingularLY_pos colE (by norm_num)

/-- `h₁` annihilates the singular vector. -/
theorem sl2SingularLY_H1 : J (-8 / 5 : ℂ) colH 1 sl2SingularLY = 0 :=
  sl2SingularLY_pos colH (by norm_num)

/-- **The Cartan charge of the singular vector is `+2`**: it is a highest-weight vector for the
horizontal `𝔰𝔩₂`, not an `𝔰𝔩₂`-invariant. -/
theorem sl2SingularLY_H0 :
    J (-8 / 5 : ℂ) colH 0 sl2SingularLY = (2 : ℂ) • sl2SingularLY :=
  H0_ansatz5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-! ## §11  The converse and nonvanishing, conditional on named independence hypotheses -/

/-- **Named hypothesis.**  Linear independence of the twelve weight-5, charge-`+4` PBW
monomials `T1, …, T12` — the target space of `e₀`.  This is *not* proved here: the theorem
`VOA.pbw` supplies `vacuumVector_ne_zero` and an induction
interface, not independence of creation monomials. -/
def TIndep (k : ℂ) : Prop :=
  ∀ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : ℂ,
    a1 • T1 k + a2 • T2 k + a3 • T3 k + a4 • T4 k + a5 • T5 k + a6 • T6 k + a7 • T7 k
      + a8 • T8 k + a9 • T9 k + a10 • T10 k + a11 • T11 k + a12 • T12 k = 0 →
      a1 = 0 ∧ a2 = 0 ∧ a3 = 0 ∧ a4 = 0 ∧ a5 = 0 ∧ a6 = 0 ∧ a7 = 0 ∧ a8 = 0 ∧ a9 = 0 ∧ a10 = 0
      ∧ a11 = 0 ∧ a12 = 0

/-- **Named hypothesis.**  Linear independence of the thirteen weight-4, charge-`0` PBW
monomials `U1, …, U13` — the target space of `f₁`. -/
def UIndep (k : ℂ) : Prop :=
  ∀ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : ℂ,
    a1 • U1 k + a2 • U2 k + a3 • U3 k + a4 • U4 k + a5 • U5 k + a6 • U6 k + a7 • U7 k
      + a8 • U8 k + a9 • U9 k + a10 • U10 k + a11 • U11 k + a12 • U12 k + a13 • U13 k = 0 →
      a1 = 0 ∧ a2 = 0 ∧ a3 = 0 ∧ a4 = 0 ∧ a5 = 0 ∧ a6 = 0 ∧ a7 = 0 ∧ a8 = 0 ∧ a9 = 0 ∧ a10 = 0
      ∧ a11 = 0 ∧ a12 = 0 ∧ a13 = 0

/-- **Named hypothesis.**  Linear independence of the twenty-one weight-5, charge-`+2` PBW
monomials `N1, …, N21` spanning the ansatz. -/
def NIndep (k : ℂ) : Prop :=
  ∀ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 : ℂ,
    a1 • N1 k + a2 • N2 k + a3 • N3 k + a4 • N4 k + a5 • N5 k + a6 • N6 k + a7 • N7 k
      + a8 • N8 k + a9 • N9 k + a10 • N10 k + a11 • N11 k + a12 • N12 k + a13 • N13 k
      + a14 • N14 k + a15 • N15 k + a16 • N16 k + a17 • N17 k + a18 • N18 k + a19 • N19 k
      + a20 • N20 k + a21 • N21 k = 0 →
      a1 = 0 ∧ a2 = 0 ∧ a3 = 0 ∧ a4 = 0 ∧ a5 = 0 ∧ a6 = 0 ∧ a7 = 0 ∧ a8 = 0 ∧ a9 = 0 ∧ a10 = 0
      ∧ a11 = 0 ∧ a12 = 0 ∧ a13 = 0 ∧ a14 = 0 ∧ a15 = 0 ∧ a16 = 0 ∧ a17 = 0 ∧ a18 = 0 ∧ a19 = 0
      ∧ a20 = 0 ∧ a21 = 0

/-- **Necessity of the system**, given independence of the target monomials: a vector of the
ansatz shape is killed by `e₀` and `f₁` only if the 25 equations hold. -/
theorem SingSys5_of_annihilated {k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : ℂ}
    {c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 : ℂ}
    (hT : TIndep k) (hU : UIndep k)
    (hE : J k colE 0 (ansatz5 k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
        c17 c18 c19 c20 c21) = 0)
    (hF : J k colF 1 (ansatz5 k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
        c17 c18 c19 c20 c21) = 0) :
    SingSys5 k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
      c17 c18 c19 c20 c21 := by
  rw [E0_ansatz5] at hE
  rw [F1_ansatz5] at hF
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ :=
    hT _ _ _ _ _ _ _ _ _ _ _ _ hE
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13⟩ :=
    hU _ _ _ _ _ _ _ _ _ _ _ _ _ hF
  exact ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, f1, f2, f3, f4, f5, f6, f7, f8, f9,
    f10, f11, f12, f13⟩

/-- **No singular vector away from `k = -8/5`.**  Modulo the same independence hypotheses, at any
level with `5k + 8 ≠ 0` the only weight-5 charge-`+2` vector killed by `e₀` and `f₁` is `0`. -/
theorem ansatz5_eq_zero_of_level_ne {k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : ℂ}
    {c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 : ℂ}
    (hT : TIndep k) (hU : UIndep k) (hk : 5 * k + 8 ≠ 0)
    (hE : J k colE 0 (ansatz5 k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
        c17 c18 c19 c20 c21) = 0)
    (hF : J k colF 1 (ansatz5 k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
        c17 c18 c19 c20 c21) = 0) :
    ansatz5 k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
      c17 c18 c19 c20 c21 = 0 := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19,
    z20, z21⟩ :=
    SingSys5_trivial_of_level (SingSys5_of_annihilated hT hU hE hF) hk
  rw [ansatz5_def, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17,
    z18, z19, z20, z21]
  simp

/-- **Nonvanishing, conditional on PBW independence** of the twenty-one monomials (`NIndep`).
The unconditional version is `WakLY.sl2SingularLY_ne_zero` (`Examples.WakimotoEightFifths`). -/
theorem sl2SingularLY_ne_zero_of_indep (hN : NIndep (-8 / 5 : ℂ)) : sl2SingularLY ≠ 0 := by
  intro h0
  rw [sl2SingularLY_def, ansatz5_def] at h0
  have h1 := (hN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0).1
  norm_num at h1


/-! ## §12  The singular vector exists exactly at `k = -8/5` -/

/-- **The module-level statement.**  Modulo the named independence hypotheses, the weight-5,
charge-`+2` subspace of `V^k(𝔰𝔩₂)` contains a nonzero vector annihilated by `e₀` and `f₁` — and
hence, by `pos_ann5`, by the whole positive part — **if and only if `5k + 8 = 0`**, i.e.
`k = -8/5`, the admissible level whose Drinfeld–Sokolov image is the Lee–Yang minimal model. -/
theorem exists_singular_ansatz_iff {k : ℂ} (hT : TIndep k) (hU : UIndep k) (hN : NIndep k) :
    (∃ c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 : ℂ,
        ansatz5 k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
            c17 c18 c19 c20 c21 ≠ 0
          ∧ J k colE 0 (ansatz5 k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
            c17 c18 c19 c20 c21) = 0
          ∧ J k colF 1 (ansatz5 k c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16
            c17 c18 c19 c20 c21) = 0)
      ↔ 5 * k + 8 = 0 := by
  constructor
  · rintro ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18,
      c19, c20, c21, hne, hE, hF⟩
    by_contra hk
    exact hne (ansatz5_eq_zero_of_level_ne hT hU hk hE hF)
  · intro hk
    have hk' : k = -8 / 5 := by linear_combination hk / 5
    subst hk'
    refine ⟨625, 5000, 10000, (-1500), (-16000), 300, (-10000), (-1000), 6000, 1200, (-14400),
      (-9600), (-19200), (-14720), 1600, 4200, 78400, (-1680), 2960, 17440, 25904, ?_, ?_, ?_⟩
    · exact sl2SingularLY_ne_zero_of_indep hN
    · exact sl2SingularLY_E0
    · exact sl2SingularLY_F1

end VOA.Sl2SingLY
