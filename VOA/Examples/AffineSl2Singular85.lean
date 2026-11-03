/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2SingularLY
import VOA.Examples.AdmissibleLevel
import VOA.Examples.DSReductionSl2

/-!
# The singular vector of `V^{-8/5}(𝔰𝔩₂)`: existence, in one place

At the admissible level `k = -8/5` — the level `k + 2 = 2/5`, i.e. `(u,v) = (2,5)`, whose
Drinfeld–Sokolov reduction is the **Lee–Yang** minimal model at `c = -22/5` — the universal
affine vertex algebra `V^k(𝔰𝔩₂) = WakModule k` has a singular vector at conformal weight `5`
and Cartan charge `+2`.  This file is the **existence** statement for that vector, packaged
under one set of names for the rigidity programme.

## §A  Provenance: what is proved here and what is imported

The heavy computation — the twenty-one straightening lemmas, the ≈ 200 mode actions, the
images `E0_ansatz5` / `F1_ansatz5` of the general 21-parameter ansatz, the elimination
`SingSys5_param`, and `pos_ann5` — lives in `Examples/AffineSl2SingularLY.lean` and is
**imported, not repeated**.  What this file adds is:

* the twenty-one monomials re-stated as explicit nested `J` applications, each pinned to its
  imported definition by a `rfl` lemma (`N01_eq`, …, `N21_eq`) — so the monomial list can be
  read off here, and every entry of it is machine-checked against the imported one;
* the vector `sl2Singular85` written out as an explicit integer combination of those
  twenty-one monomials, pinned to the imported `Sl2SingLY.sl2SingularLY` by `rfl`
  (`sl2Singular85_eq_LY`) — a machine-checked transcription check of the
  *coefficient-to-monomial pairing*, which is the single place a hand transcription can go
  wrong without any theorem noticing;
* the annihilation / charge / grading / positive-part statements under the `sl2Singular85_*`
  names, plus the `ℓ₀`-eigenvalue in explicit form and a single packaged
  `sl2Singular85_isSingular`;
* the arithmetic bridge to Lee–Yang (`sl2Singular85_level_admissible`,
  `sl2Singular85_dsCentralCharge`), which is why this level and not `-4/3` is the one the
  rigidity programme needs.

**Nothing here is transcribed from the literature**, and nothing here is `sorry`-ed.

## §B  Conventions

Inherited verbatim from `Examples/AffineSl2Singular.lean`:  colours `colE = 0`, `colF = 1`,
`colH = 2`; `⁅h,e⁆ = 2e`, `⁅h,f⁆ = -2f`, `⁅e,f⁆ = h`; normalised form `κ(e,f) = 1`,
`κ(h,h) = 2`; and
`⁅J^a_m, J^b_n⁆ = ∑_c f^{ab}_c J^c_{m+n} + m·k·κ(a,b)·δ_{m+n,0}`, the central term keeping the
**left** mode `m`.  Modes `J k a (-p)` with `p ≥ 1` are creation operators and
`J k a (-p) |0⟩` has conformal weight `p`.  Monomials are written **operator-first**
(outermost operator leftmost), in the normal order "mode indices weakly increasing
left-to-right, ties broken `e < f < h`".

⚠ The repository indexes `FormalDist` by the **z-exponent**, with `mode a m = a (-m-1)`.  Any
coefficient list imported from a CAS in field/OPE conventions must be converted before being
compared with the monomials below.

## §C  Where the weight comes from

For `k + 2 = u/v` in lowest terms the vacuum Verma module of `𝔰𝔩₂^` has its singular vector at
conformal weight `(u-1)v` and `𝔰𝔩₂`-weight `2(u-1)` (Kac–Kazhdan Shapovalov determinant;
Creutzig–Ridout, arXiv:1306.4388v2 §3, just after (3.1)).  At `k = -8/5`, `(u,v) = (2,5)`:
**weight 5, charge +2**.  The proved companion case `k = -4/3` is `(u,v) = (2,3)`: weight 3,
charge `+2`, which is exactly `Sl2Sing.sl2Singular_mem` / `Sl2Sing.sl2Singular_H0`.

## Main results

* `sl2Singular85` — the explicit weight-5, charge-`+2` vector of `V^{-8/5}(𝔰𝔩₂)`, with
  primitive integer coefficients in the twenty-one-monomial PBW basis `N01, …, N21`.
* `sl2Singular85_eq_LY` — the `rfl` identification with `Sl2SingLY.sl2SingularLY`, i.e. the
  transcription check on the coefficient-to-monomial pairing.
* `sl2Singular85_E0`, `sl2Singular85_F1` — annihilation by the two affine Chevalley raising
  generators `e₀` and `f₁`.  These are the only two conditions **imposed**; everything below
  is a consequence.
* `sl2Singular85_E1`, `sl2Singular85_H1`, `sl2Singular85_E2`, `sl2Singular85_F2`,
  `sl2Singular85_H2`, `sl2Singular85_E3` — the derived level-`1,2,3` annihilations.
* `sl2Singular85_pos` — annihilation by **every** mode of positive level.
* `sl2Singular85_H0` — the Cartan charge is `+2` (an `𝔰𝔩₂` highest weight, *not* a singlet).
* `sl2Singular85_mem`, `sl2Singular85_ell0` — conformal weight `5`, as membership in
  `gradingZA (-8/5) 5` and as the explicit `ℓ₀`-eigenvalue `-5`.
* `sl2Singular85_isSingular` — all of the above as one packaged statement.
* `sl2Singular85_level_admissible`, `sl2Singular85_dsCentralCharge` — the level is admissible
  and its Drinfeld–Sokolov central charge is the Lee–Yang value `-22/5`.
* `sl2Singular85_ne_zero_of_indep` — nonvanishing, conditional on the named PBW independence
  hypothesis `Sl2SingLY.NIndep`.  (Unconditional, `pbw`-free: `WakLY.sl2Singular85_ne_zero`.)

## §D  Independent re-verification of the coefficients (CAS, NOT formalised)

The twenty-one coefficients were re-derived from scratch, outside Lean, by a straightening
implementation written directly from `current_comm` in the convention of §B (normal order:
modes ascending, ties `e < f < h`; the central term keeping the left mode).  Applying each
raising mode to the symbolic-level combination gives

| mode | image of `s` at symbolic `k` |
|---|---|
| `e₀` | `0` identically in `k` (the `e₀` subsystem is level-independent) |
| `f₁` | `(5k + 8) ·` (13 monomials, integer coefficients `125, 592, 640, …`) |
| `e₁` | `(5k + 8) ·` (6 monomials) |
| `h₁` | `(5k + 8) ·` (10 monomials) |
| `e₂`, `f₂`, `h₂` | `(5k + 8) ·` (1, 6, 5 monomials) |
| `e₃`, `f₃`, `h₃` | `(5k + 8) ·` (1, 3, 2 monomials) |
| `h₀` | `2 s`, identically in `k` |

Every one of these is a *nonzero* multiple of `(5k + 8)`, so each vanishes exactly at
`k = -8/5` and at no other level: the level is over-determined, and the arithmetic agrees with
the formalised elimination `Sl2SingLY.SingSys5_param`, whose last equation is
`(5k + 8)·c₁ = 0`.  The same implementation reproduces the proved `k = -4/3` case
(`Sl2Sing.SingSys`, determinant `-4(3k+4)`, coefficients `(20, -12, -6, 36, 9)`) before being
run here.  This table is context only — it is a CAS computation, not a Lean theorem; the Lean
content is `sl2Singular85_E0` and `sl2Singular85_F1` and what follows from them.

## §E  What is NOT proved here (honest gaps, inherited)

1. **Weight-5 spanning.**  That `N01, …, N21` span the whole weight-5 charge-`+2` space is not
   proved; so "there is a singular vector of this shape" is the statement, not "these are all
   weight-5 singular vectors".
2. **Nonvanishing.**  Here only conditionally (`sl2Singular85_ne_zero_of_indep`).  Proved
   unconditionally and `pbw`-free downstream: `WakLY.sl2Singular85_ne_zero`
   (`Examples.WakimotoEightFifths`).
3. **Primitivity.**  That the weight-5 charge-`+2` sector is the *only* singular sector at
   `k = -8/5` for weight `≤ 5` — so that `s` is not a descendant — is a CAS sweep, not a
   theorem here.
4. **The ideal / `L_{-8/5}(𝔰𝔩₂) ≠ V^{-8/5}(𝔰𝔩₂)`.**  Not in this file; proved downstream as
   `Sl2NotSimple85.maxGradedIdeal_85_ne_bot` and `Sl2NotSimple85.not_isSimple_85`
   (`Examples.AffineSl2NotSimple85`).
5. **The converse (the level as a theorem).**  `Sl2SingLY.exists_nonzero_solution_iff` and
   `Sl2SingLY.exists_singular_ansatz_iff` prove that the ansatz has a nonzero singular solution
   iff `5k + 8 = 0`; this file deliberately states only the existence half at the fixed level.

## §F  Axioms

Everything here is `sorry`-free and introduces no axiom.  `#print axioms` on the main
results reports exactly `[propext, Classical.choice, Quot.sound]` — in particular **`pbw`-free**:
the computational content rests on `current_comm` and `vacuum_pos_annihilate`.

## Status

Complete as an existence statement at `k = -8/5`; §E items 1, 3 remain open, items 2, 4 are
proved downstream.

## References
Creutzig–Ridout, arXiv:1306.4388v2 §3; Kac, *Infinite Dimensional Lie Algebras* §9–§10;
Linshaw–Qi, arXiv:2601.12017 §5.
-/

open Module (End)
open VOA VOA.AffineVOA VOA.AffineLie

namespace VOA.Sl2Sing85

open VOA.Sl2SingLY

/-! ## §1  The twenty-one weight-5, charge-`+2` monomials

Each `N0i` is the imported `Sl2SingLY.Ni`, and the accompanying `N0i_eq` is a `rfl` lemma
spelling out the monomial as an explicit nested `J` application.  The `rfl` is the check: if
the imported definition were a different monomial, the lemma would not typecheck. -/

/-- `N01 = e₋₁h₋₁h₋₁h₋₁h₋₁|0⟩`. -/
noncomputable abbrev N01 (k : ℂ) : WakModule k := Sl2SingLY.N1 k

/-- `N01` spelled out. -/
theorem N01_eq (k : ℂ) :
    N01 k = J k colE (-1) (J k colH (-1) (J k colH (-1) (J k colH (-1)
      (J k colH (-1) (vacuumA k))))) := rfl

/-- `N02 = e₋₁e₋₁f₋₁h₋₁h₋₁|0⟩`. -/
noncomputable abbrev N02 (k : ℂ) : WakModule k := Sl2SingLY.N2 k

/-- `N02` spelled out. -/
theorem N02_eq (k : ℂ) :
    N02 k = J k colE (-1) (J k colE (-1) (J k colF (-1) (J k colH (-1)
      (J k colH (-1) (vacuumA k))))) := rfl

/-- `N03 = e₋₁e₋₁e₋₁f₋₁f₋₁|0⟩`. -/
noncomputable abbrev N03 (k : ℂ) : WakModule k := Sl2SingLY.N3 k

/-- `N03` spelled out. -/
theorem N03_eq (k : ℂ) :
    N03 k = J k colE (-1) (J k colE (-1) (J k colE (-1) (J k colF (-1)
      (J k colF (-1) (vacuumA k))))) := rfl

/-- `N04 = h₋₂e₋₁h₋₁h₋₁|0⟩`. -/
noncomputable abbrev N04 (k : ℂ) : WakModule k := Sl2SingLY.N4 k

/-- `N04` spelled out. -/
theorem N04_eq (k : ℂ) :
    N04 k = J k colH (-2) (J k colE (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))) := rfl

/-- `N05 = h₋₂e₋₁e₋₁f₋₁|0⟩`. -/
noncomputable abbrev N05 (k : ℂ) : WakModule k := Sl2SingLY.N5 k

/-- `N05` spelled out. -/
theorem N05_eq (k : ℂ) :
    N05 k = J k colH (-2) (J k colE (-1) (J k colE (-1) (J k colF (-1) (vacuumA k)))) := rfl

/-- `N06 = h₋₂h₋₂e₋₁|0⟩`. -/
noncomputable abbrev N06 (k : ℂ) : WakModule k := Sl2SingLY.N6 k

/-- `N06` spelled out. -/
theorem N06_eq (k : ℂ) :
    N06 k = J k colH (-2) (J k colH (-2) (J k colE (-1) (vacuumA k))) := rfl

/-- `N07 = f₋₂e₋₁e₋₁h₋₁|0⟩`. -/
noncomputable abbrev N07 (k : ℂ) : WakModule k := Sl2SingLY.N7 k

/-- `N07` spelled out. -/
theorem N07_eq (k : ℂ) :
    N07 k = J k colF (-2) (J k colE (-1) (J k colE (-1) (J k colH (-1) (vacuumA k)))) := rfl

/-- `N08 = e₋₂h₋₁h₋₁h₋₁|0⟩`. -/
noncomputable abbrev N08 (k : ℂ) : WakModule k := Sl2SingLY.N8 k

/-- `N08` spelled out. -/
theorem N08_eq (k : ℂ) :
    N08 k = J k colE (-2) (J k colH (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))) := rfl

/-- `N09 = e₋₂e₋₁f₋₁h₋₁|0⟩`. -/
noncomputable abbrev N09 (k : ℂ) : WakModule k := Sl2SingLY.N9 k

/-- `N09` spelled out. -/
theorem N09_eq (k : ℂ) :
    N09 k = J k colE (-2) (J k colE (-1) (J k colF (-1) (J k colH (-1) (vacuumA k)))) := rfl

/-- `N10 = e₋₂h₋₂h₋₁|0⟩`. -/
noncomputable abbrev N10 (k : ℂ) : WakModule k := Sl2SingLY.N10 k

/-- `N10` spelled out. -/
theorem N10_eq (k : ℂ) :
    N10 k = J k colE (-2) (J k colH (-2) (J k colH (-1) (vacuumA k))) := rfl

/-- `N11 = e₋₂f₋₂e₋₁|0⟩`. -/
noncomputable abbrev N11 (k : ℂ) : WakModule k := Sl2SingLY.N11 k

/-- `N11` spelled out. -/
theorem N11_eq (k : ℂ) :
    N11 k = J k colE (-2) (J k colF (-2) (J k colE (-1) (vacuumA k))) := rfl

/-- `N12 = e₋₂e₋₂f₋₁|0⟩`. -/
noncomputable abbrev N12 (k : ℂ) : WakModule k := Sl2SingLY.N12 k

/-- `N12` spelled out. -/
theorem N12_eq (k : ℂ) :
    N12 k = J k colE (-2) (J k colE (-2) (J k colF (-1) (vacuumA k))) := rfl

/-- `N13 = h₋₃e₋₁h₋₁|0⟩`. -/
noncomputable abbrev N13 (k : ℂ) : WakModule k := Sl2SingLY.N13 k

/-- `N13` spelled out. -/
theorem N13_eq (k : ℂ) :
    N13 k = J k colH (-3) (J k colE (-1) (J k colH (-1) (vacuumA k))) := rfl

/-- `N14 = h₋₃e₋₂|0⟩`. -/
noncomputable abbrev N14 (k : ℂ) : WakModule k := Sl2SingLY.N14 k

/-- `N14` spelled out. -/
theorem N14_eq (k : ℂ) : N14 k = J k colH (-3) (J k colE (-2) (vacuumA k)) := rfl

/-- `N15 = f₋₃e₋₁e₋₁|0⟩`. -/
noncomputable abbrev N15 (k : ℂ) : WakModule k := Sl2SingLY.N15 k

/-- `N15` spelled out. -/
theorem N15_eq (k : ℂ) :
    N15 k = J k colF (-3) (J k colE (-1) (J k colE (-1) (vacuumA k))) := rfl

/-- `N16 = e₋₃h₋₁h₋₁|0⟩`. -/
noncomputable abbrev N16 (k : ℂ) : WakModule k := Sl2SingLY.N16 k

/-- `N16` spelled out. -/
theorem N16_eq (k : ℂ) :
    N16 k = J k colE (-3) (J k colH (-1) (J k colH (-1) (vacuumA k))) := rfl

/-- `N17 = e₋₃e₋₁f₋₁|0⟩`. -/
noncomputable abbrev N17 (k : ℂ) : WakModule k := Sl2SingLY.N17 k

/-- `N17` spelled out. -/
theorem N17_eq (k : ℂ) :
    N17 k = J k colE (-3) (J k colE (-1) (J k colF (-1) (vacuumA k))) := rfl

/-- `N18 = e₋₃h₋₂|0⟩`. -/
noncomputable abbrev N18 (k : ℂ) : WakModule k := Sl2SingLY.N18 k

/-- `N18` spelled out. -/
theorem N18_eq (k : ℂ) : N18 k = J k colE (-3) (J k colH (-2) (vacuumA k)) := rfl

/-- `N19 = h₋₄e₋₁|0⟩`. -/
noncomputable abbrev N19 (k : ℂ) : WakModule k := Sl2SingLY.N19 k

/-- `N19` spelled out. -/
theorem N19_eq (k : ℂ) : N19 k = J k colH (-4) (J k colE (-1) (vacuumA k)) := rfl

/-- `N20 = e₋₄h₋₁|0⟩`. -/
noncomputable abbrev N20 (k : ℂ) : WakModule k := Sl2SingLY.N20 k

/-- `N20` spelled out. -/
theorem N20_eq (k : ℂ) : N20 k = J k colE (-4) (J k colH (-1) (vacuumA k)) := rfl

/-- `N21 = e₋₅|0⟩`. -/
noncomputable abbrev N21 (k : ℂ) : WakModule k := Sl2SingLY.N21 k

/-- `N21` spelled out. -/
theorem N21_eq (k : ℂ) : N21 k = J k colE (-5) (vacuumA k) := rfl

/-- Every one of the twenty-one monomials has conformal weight `5`. -/
theorem N_mem (k : ℂ) :
    N01 k ∈ gradingZA k 5 ∧ N02 k ∈ gradingZA k 5 ∧ N03 k ∈ gradingZA k 5
      ∧ N04 k ∈ gradingZA k 5 ∧ N05 k ∈ gradingZA k 5 ∧ N06 k ∈ gradingZA k 5
      ∧ N07 k ∈ gradingZA k 5 ∧ N08 k ∈ gradingZA k 5 ∧ N09 k ∈ gradingZA k 5
      ∧ N10 k ∈ gradingZA k 5 ∧ N11 k ∈ gradingZA k 5 ∧ N12 k ∈ gradingZA k 5
      ∧ N13 k ∈ gradingZA k 5 ∧ N14 k ∈ gradingZA k 5 ∧ N15 k ∈ gradingZA k 5
      ∧ N16 k ∈ gradingZA k 5 ∧ N17 k ∈ gradingZA k 5 ∧ N18 k ∈ gradingZA k 5
      ∧ N19 k ∈ gradingZA k 5 ∧ N20 k ∈ gradingZA k 5 ∧ N21 k ∈ gradingZA k 5 :=
  ⟨N1_mem k, N2_mem k, N3_mem k, N4_mem k, N5_mem k, N6_mem k, N7_mem k, N8_mem k, N9_mem k,
    N10_mem k, N11_mem k, N12_mem k, N13_mem k, N14_mem k, N15_mem k, N16_mem k, N17_mem k,
    N18_mem k, N19_mem k, N20_mem k, N21_mem k⟩

/-! ## §2  The singular vector -/

/-- **The weight-5 singular vector of `V^{-8/5}(𝔰𝔩₂)`**, with primitive integer coefficients:

`s = 625 e₋₁h₋₁h₋₁h₋₁h₋₁|0⟩ + 5000 e₋₁e₋₁f₋₁h₋₁h₋₁|0⟩ + 10000 e₋₁e₋₁e₋₁f₋₁f₋₁|0⟩`
`  - 1500 h₋₂e₋₁h₋₁h₋₁|0⟩ - 16000 h₋₂e₋₁e₋₁f₋₁|0⟩ + 300 h₋₂h₋₂e₋₁|0⟩`
`  - 10000 f₋₂e₋₁e₋₁h₋₁|0⟩ - 1000 e₋₂h₋₁h₋₁h₋₁|0⟩ + 6000 e₋₂e₋₁f₋₁h₋₁|0⟩`
`  + 1200 e₋₂h₋₂h₋₁|0⟩ - 14400 e₋₂f₋₂e₋₁|0⟩ - 9600 e₋₂e₋₂f₋₁|0⟩`
`  - 19200 h₋₃e₋₁h₋₁|0⟩ - 14720 h₋₃e₋₂|0⟩ + 1600 f₋₃e₋₁e₋₁|0⟩`
`  + 4200 e₋₃h₋₁h₋₁|0⟩ + 78400 e₋₃e₋₁f₋₁|0⟩ - 1680 e₋₃h₋₂|0⟩`
`  + 2960 h₋₄e₋₁|0⟩ + 17440 e₋₄h₋₁|0⟩ + 25904 e₋₅|0⟩.` -/
noncomputable def sl2Singular85 : WakModule (-8 / 5 : ℂ) :=
  (625 : ℂ) • N01 (-8 / 5) + (5000 : ℂ) • N02 (-8 / 5) + (10000 : ℂ) • N03 (-8 / 5)
    + (-1500 : ℂ) • N04 (-8 / 5) + (-16000 : ℂ) • N05 (-8 / 5) + (300 : ℂ) • N06 (-8 / 5)
    + (-10000 : ℂ) • N07 (-8 / 5) + (-1000 : ℂ) • N08 (-8 / 5) + (6000 : ℂ) • N09 (-8 / 5)
    + (1200 : ℂ) • N10 (-8 / 5) + (-14400 : ℂ) • N11 (-8 / 5) + (-9600 : ℂ) • N12 (-8 / 5)
    + (-19200 : ℂ) • N13 (-8 / 5) + (-14720 : ℂ) • N14 (-8 / 5) + (1600 : ℂ) • N15 (-8 / 5)
    + (4200 : ℂ) • N16 (-8 / 5) + (78400 : ℂ) • N17 (-8 / 5) + (-1680 : ℂ) • N18 (-8 / 5)
    + (2960 : ℂ) • N19 (-8 / 5) + (17440 : ℂ) • N20 (-8 / 5) + (25904 : ℂ) • N21 (-8 / 5)

/-- Unfolding lemma for `sl2Singular85`. -/
theorem sl2Singular85_def :
    sl2Singular85 =
      (625 : ℂ) • N01 (-8 / 5) + (5000 : ℂ) • N02 (-8 / 5) + (10000 : ℂ) • N03 (-8 / 5)
        + (-1500 : ℂ) • N04 (-8 / 5) + (-16000 : ℂ) • N05 (-8 / 5) + (300 : ℂ) • N06 (-8 / 5)
        + (-10000 : ℂ) • N07 (-8 / 5) + (-1000 : ℂ) • N08 (-8 / 5) + (6000 : ℂ) • N09 (-8 / 5)
        + (1200 : ℂ) • N10 (-8 / 5) + (-14400 : ℂ) • N11 (-8 / 5) + (-9600 : ℂ) • N12 (-8 / 5)
        + (-19200 : ℂ) • N13 (-8 / 5) + (-14720 : ℂ) • N14 (-8 / 5) + (1600 : ℂ) • N15 (-8 / 5)
        + (4200 : ℂ) • N16 (-8 / 5) + (78400 : ℂ) • N17 (-8 / 5) + (-1680 : ℂ) • N18 (-8 / 5)
        + (2960 : ℂ) • N19 (-8 / 5) + (17440 : ℂ) • N20 (-8 / 5)
        + (25904 : ℂ) • N21 (-8 / 5) := rfl

/-- **The transcription check.**  The explicit integer combination above is, on the nose, the
vector produced by the imported elimination.  Because this is `rfl`, it checks the *pairing* of
each of the twenty-one coefficients with its monomial — the one thing a hand transcription can
get wrong without any annihilation theorem noticing. -/
theorem sl2Singular85_eq_LY : sl2Singular85 = Sl2SingLY.sl2SingularLY := rfl

/-! ## §3  Annihilation

Only `e₀` and `f₁` are imposed: they generate the positive part `n̂₊` of `𝔰𝔩₂^` as a Lie
algebra, so everything else in §3 and §5 is a consequence (`Sl2SingLY.pos_ann5`). -/

/-- `e₀` annihilates the singular vector.  (Imposed condition.) -/
theorem sl2Singular85_E0 : J (-8 / 5 : ℂ) colE 0 sl2Singular85 = 0 :=
  Sl2SingLY.sl2SingularLY_E0

/-- `f₁` annihilates the singular vector.  (Imposed condition.) -/
theorem sl2Singular85_F1 : J (-8 / 5 : ℂ) colF 1 sl2Singular85 = 0 :=
  Sl2SingLY.sl2SingularLY_F1

/-- `e₁` annihilates the singular vector. -/
theorem sl2Singular85_E1 : J (-8 / 5 : ℂ) colE 1 sl2Singular85 = 0 :=
  Sl2SingLY.sl2SingularLY_E1

/-- `h₁` annihilates the singular vector. -/
theorem sl2Singular85_H1 : J (-8 / 5 : ℂ) colH 1 sl2Singular85 = 0 :=
  Sl2SingLY.sl2SingularLY_H1

/-! ## §4  Charge and conformal weight -/

/-- The Cartan charge of the singular vector is `+2`: it is a highest-weight vector for the
horizontal `𝔰𝔩₂`, **not** an `𝔰𝔩₂`-invariant (so `f₀ s ≠ 0`; imposing `f₀ s = 0` as well has no
nonzero solution). -/
theorem sl2Singular85_H0 :
    J (-8 / 5 : ℂ) colH 0 sl2Singular85 = (2 : ℂ) • sl2Singular85 :=
  Sl2SingLY.sl2SingularLY_H0

/-- The singular vector has conformal weight `5`. -/
theorem sl2Singular85_mem : sl2Singular85 ∈ gradingZA (-8 / 5 : ℂ) 5 :=
  Sl2SingLY.sl2SingularLY_mem

/-- The conformal weight in explicit eigenvalue form: `ℓ₀ s = -5 · s`, the grading convention
being that `gradingZA k n` is the `ℓ₀`-eigenspace of eigenvalue `-n`. -/
theorem sl2Singular85_ell0 :
    ell0OpA (-8 / 5 : ℂ) sl2Singular85 = (-5 : ℂ) • sl2Singular85 := by
  have h := sl2Singular85_mem
  rw [gradingZA_def, Module.End.mem_eigenspace_iff] at h
  have h5 : (-((5 : ℤ) : ℂ)) = (-5 : ℂ) := by norm_num
  rwa [h5] at h

/-! ## §5  The whole positive part -/

/-- **`s` is a singular vector**: every mode of positive level annihilates it.  Levels `1`
through `5` come from four rounds of the recursion `e_{s+1} = ½⁅h₁, e_s⁆`,
`f_{s+1} = -½⁅h₁, f_s⁆`, `h_{s+1} = ⁅e₁, f_s⁆` (no central terms, since `m + n ≠ 0`
throughout); levels `≥ 6` are killed by the energy grading, a mode of level `m > 5` landing in
degree `5 - m < 0`. -/
theorem sl2Singular85_pos (a : Fin 3) {m : ℤ} (hm : 1 ≤ m) :
    J (-8 / 5 : ℂ) a m sl2Singular85 = 0 :=
  Sl2SingLY.sl2SingularLY_pos a hm

/-- `e₂` annihilates the singular vector. -/
theorem sl2Singular85_E2 : J (-8 / 5 : ℂ) colE 2 sl2Singular85 = 0 :=
  sl2Singular85_pos colE (by norm_num)

/-- `f₂` annihilates the singular vector. -/
theorem sl2Singular85_F2 : J (-8 / 5 : ℂ) colF 2 sl2Singular85 = 0 :=
  sl2Singular85_pos colF (by norm_num)

/-- `h₂` annihilates the singular vector. -/
theorem sl2Singular85_H2 : J (-8 / 5 : ℂ) colH 2 sl2Singular85 = 0 :=
  sl2Singular85_pos colH (by norm_num)

/-- `e₃` annihilates the singular vector. -/
theorem sl2Singular85_E3 : J (-8 / 5 : ℂ) colE 3 sl2Singular85 = 0 :=
  sl2Singular85_pos colE (by norm_num)

/-! ## §6  The packaged statement, and the level -/

/-- **The complete affine highest-weight data of `s`, in one statement.**  At `k = -8/5` the
vector `sl2Singular85` has conformal weight `5`, is annihilated by the horizontal raising
operator `e₀` and by every mode of positive level, and has Cartan charge `+2`.  This is exactly
the input the deformation-rigidity programme consumes. -/
theorem sl2Singular85_isSingular :
    sl2Singular85 ∈ gradingZA (-8 / 5 : ℂ) 5
      ∧ J (-8 / 5 : ℂ) colE 0 sl2Singular85 = 0
      ∧ J (-8 / 5 : ℂ) colH 0 sl2Singular85 = (2 : ℂ) • sl2Singular85
      ∧ ∀ (a : Fin 3) (m : ℤ), 1 ≤ m → J (-8 / 5 : ℂ) a m sl2Singular85 = 0 :=
  ⟨sl2Singular85_mem, sl2Singular85_E0, sl2Singular85_H0,
    fun a _ hm => sl2Singular85_pos a hm⟩

/-- The level carrying this singular vector is admissible, with `(p,q) = (2,5)`. -/
theorem sl2Singular85_level_admissible : Admissible.AdmissibleLevel (-8 / 5 : ℂ) :=
  Admissible.admissibleLevel_neg_eight_fifths

/-- The affine central charge at this level is `3k/(k+2) = -12`. -/
theorem sl2Singular85_centralChargeA : centralChargeA (-8 / 5 : ℂ) = -12 :=
  Admissible.centralChargeA_neg_eight_fifths

/-- **Why this level and not `-4/3`.**  The Drinfeld–Sokolov central charge at `k = -8/5` is
the **Lee–Yang** value `c = -22/5`, the `(2,5)` minimal model.  The flagship level `k = -4/3` is
`(2,3)` and reduces to `c = 0`, the trivial model
(`DSsl2.dsCentralCharge_trivial`); so `k = -8/5`, not `k = -4/3`, is the Lee–Yang partner. -/
theorem sl2Singular85_dsCentralCharge :
    DSsl2.dsCentralCharge (-8 / 5 : ℂ) = -22 / 5 := by
  rw [DSsl2.dsCentralCharge]
  norm_num

/-! ## §7  Nonvanishing, conditional on PBW independence -/

/-- **Nonvanishing, conditional** on the independence of the twenty-one monomials
(`Sl2SingLY.NIndep`).  The unconditional version is `WakLY.sl2Singular85_ne_zero`
(`Examples.WakimotoEightFifths`). -/
theorem sl2Singular85_ne_zero_of_indep (hN : Sl2SingLY.NIndep (-8 / 5 : ℂ)) :
    sl2Singular85 ≠ 0 :=
  Sl2SingLY.sl2SingularLY_ne_zero_of_indep hN

end VOA.Sl2Sing85
