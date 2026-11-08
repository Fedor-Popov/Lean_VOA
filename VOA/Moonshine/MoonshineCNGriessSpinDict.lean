/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGriessTwistedTop
import VOA.Moonshine.MonsterGriess.SpinMatrixMap
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# The `W`-block of the Griess dictionary: `SpaceW → (T⁺)₂`, and its two module channels

Axiom's `SpaceW = Matrix SpinIdx (Fin 24) ℚ` is sent into the twisted weight-two space of `V♮` by

  `spinDict N = λ · spinTopVec (N^π)`,   `(N^π)_{s i} = N_{s, π i}`,

`π = piPerm` the Golay permutation of the untwisted block, `spinTopVec` the Conway/spin
coordinates of `(T⁺)₂` (`MoonshineCNGriessTwistedTop`), and `λ` a fixed square root of
`−1/(2κ)` (`κ = spinFormScale`), chosen so that the form comes out as `2·bform`.

**The phases.**  On `T` the vector `x_{α_c}` acts by `e_{α_c} = spinOp(c) = Z(c)·R_c`
(`Z = signRefinement`), so the dictionary must use `ζ'_c = Z(c)⁻¹` in front of `x_{α_c}` for the
`X·W` channel to produce Axiom's `R_c` exactly.  Since `Z(c)² = ε(α_c, α_c)` can be `−1`, this is
*not* the sign map `griessShortSign = Z` of the untwisted round; it is its inverse
(`fullShortSign`), which satisfies the same untwisted sign conditions
(`shortSignDictionary_fullShortSign`).

## Main results
* `fullShortSign`, ⭐ `shortSignDictionary_fullShortSign`, ⭐ `fullShortSign_smul_spinOp`
  (`ζ'_c spinOp(c) = R_c` read in `ℂ`, via the ported `map_qmatR`);
* `spinToConway`, `spinDictScale` (`λ² = −1/(2κ)`), `spinDict`, `spinDict_mem_weight_two`;
* ⭐ `TPForm_spinDict` — `TPForm (spinDict N) (spinDict M) = 2 Σ N_{ji} M_{ji}`;
* ⭐ `topAct_matDict_spinDict` — `A·W`: `Q(A)₍₁₎ spinDict N = spinDict ((tr A/8) N + N A)`;
* ⭐ `topAct_shortDict_spinDict` — `X·W`:
  `x₍₁₎ spinDict N = spinDict (⅛ Σ_c x_c (R_c N − ¼ R_c N U_c))`;
* the Axiom side of the `W·W` channel: `Rmat_transpose_of_short` (`R_cᵀ = R_c`),
  `qf_eq_trace_mul_Umat`, ⭐ `bform_gmul_spinBlock_spinBlock` — the invariance
  `bform (N·M) u = bform (M, u·N)` for `u` with zero `W`-part, proved from the formulas.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.GriessDictionary

open VOA VOA.Moonshine VOA.Moonshine.AutMonster VOA.Moonshine.SigmaTop
open VOA.LatGen VOA.IntegralLattice
open VOA.Moonshine.InvForm
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Spin
open VOA.Moonshine.MonsterGriess.LeechMatch (piPerm)
open Matrix

/-! ## §1  The phases of the full dictionary -/

/-- The cocycle takes the values `±1`. -/
theorem latticeCocycle_mul_self (α β : leech.carrier) :
    latticeCocycle leech α β * latticeCocycle leech α β = 1 := by
  rw [latticeCocycle_eq_coc, Extraspecial.coc]
  exact Extraspecial.sgn_mul_self _

/-- `sgn t · sgn t = 1` for Axiom's rational sign, read in `ℂ`. -/
theorem ratSgn_mul_self (t : ZMod 2) :
    ((MonsterGriess.sgn t : ℚ) : ℂ) * ((MonsterGriess.sgn t : ℚ) : ℂ) = 1 := by
  rw [ratSgn_cast]
  exact Extraspecial.sgn_mul_self t

/-- **The phases of the full Griess dictionary**: `ζ'_c = Z(c)⁻¹`, the inverse of the sign map
`griessShortSign` of the untwisted round. -/
noncomputable def fullShortSign (c : ShortIdx) : ℂ := (griessShortSign c)⁻¹

theorem fullShortSign_ne_zero (c : ShortIdx) : fullShortSign c ≠ 0 :=
  inv_ne_zero (griessShortSign_ne_zero c)

/-- **The two sign maps differ by the cocycle on the diagonal**: `ζ'_c = ζ_c · ε(α_c, α_c)`.
So `untwistedDict ζ' x = untwistedDict ζ (c ↦ ε(α_c,α_c) x_c)`. -/
theorem fullShortSign_eq (c : ShortIdx) :
    fullShortSign c = griessShortSign c * latticeCocycle leech (shortVec c) (shortVec c) := by
  rw [fullShortSign]
  apply inv_eq_of_mul_eq_one_right
  linear_combination griessShortSign_sq c

/-- Inverting the sign conditions of the untwisted round. -/
theorem fullShortSign_sign {s ε : ℂ} (hs : s * s = 1) (hε : ε * ε = 1) {d e c : ShortIdx}
    (h : s * griessShortSign c = griessShortSign d * griessShortSign e * ε) :
    s * fullShortSign c = fullShortSign d * fullShortSign e * ε := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hεi : ε⁻¹ = ε := inv_eq_of_mul_eq_one_right hε
  have h' := congrArg (fun z : ℂ => z⁻¹) h
  simp only [mul_inv, hsi, hεi] at h'
  exact h'

/-- ⭐ **The untwisted sign conditions hold for `ζ' = Z⁻¹`.** -/
theorem shortSignDictionary_fullShortSign : ShortSignDictionary fullShortSign where
  sq c := by
    have h := griessShortSign_sq c
    have hε := latticeCocycle_mul_self (shortVec c) (shortVec c)
    have h2 : griessShortSign c ^ 2 = latticeCocycle leech (shortVec c) (shortVec c) := by
      linear_combination latticeCocycle leech (shortVec c) (shortVec c) * h
        - griessShortSign c ^ 2 * hε
    have hε0 : latticeCocycle leech (shortVec c) (shortVec c) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hε
      exact zero_ne_one hε
    rw [fullShortSign, inv_pow, h2, inv_mul_cancel₀ hε0]
  pm_injective := shortSignDictionary_griessShortSign.pm_injective
  sum_shape := shortSignDictionary_griessShortSign.sum_shape
  sum_exists := shortSignDictionary_griessShortSign.sum_exists
  sign_neg_two d e c h hf :=
    fullShortSign_sign (ratSgn_mul_self _) (latticeCocycle_mul_self _ _)
      (shortSignDictionary_griessShortSign.sign_neg_two d e c h hf)
  sign_two d e c h hf :=
    fullShortSign_sign (ratSgn_mul_self _) (latticeCocycle_mul_self _ _)
      (shortSignDictionary_griessShortSign.sign_two d e c h hf)

/-- The Axiom coordinates of the class of `α_c` are `c`. -/
theorem coordOfRed_red_shortVec (c : ShortIdx) : coordOfRed (red leech (shortVec c)) = c.1 := by
  rw [← latRedLin_shortIdx]
  exact latRedEquiv.symm_apply_apply c.1

/-- Axiom's `R_c`, read in `ℂ`. -/
theorem Rmat_map (c : ShortIdx) : (Rmat c).map (Rat.castHom ℂ) = qmatR ℂ 0 c.1.1 c.1.2 := by
  rw [Rmat]
  exact map_qmatR _ _ _ _

/-- ⭐ **The phased spin matrix of a short class is Axiom's `R_c`**: `ζ'_c · spinOp(ᾱ_c) = R_c`. -/
theorem fullShortSign_smul_spinOp (c : ShortIdx) :
    fullShortSign c • spinOp (coordOfRed (red leech (shortVec c))) = (Rmat c).map (Rat.castHom ℂ) := by
  rw [coordOfRed_red_shortVec, spinOp, smul_smul, show signRefinement c.1 = griessShortSign c from rfl,
    fullShortSign, inv_mul_cancel₀ (griessShortSign_ne_zero c), one_smul, Rmat_map]

/-! ## §2  Axiom's spin matrices in Conway columns -/

/-- `N ↦ N^π`: the columns of a `SpaceW` matrix moved to Conway's coordinates, read in `ℂ`. -/
noncomputable def spinToConway : SpaceW →+ Matrix SpinIdx (Fin 24) ℂ where
  toFun N := Matrix.of fun s i => (N s (piPerm i) : ℂ)
  map_zero' := by
    ext s i
    simp
  map_add' N M := by
    ext s i
    simp

theorem spinToConway_apply (N : SpaceW) (s : SpinIdx) (i : Fin 24) :
    spinToConway N s i = (N s (piPerm i) : ℂ) := rfl

theorem spinToConway_smul (q : ℚ) (N : SpaceW) :
    spinToConway (q • N) = (q : ℂ) • spinToConway N := by
  ext s i
  simp [spinToConway_apply]

theorem spinToConway_mul_right (N : SpaceW) (A : Matrix (Fin 24) (Fin 24) ℚ) :
    spinToConway (N * A) = spinToConway N * axiomToConway A := by
  ext s i
  simp only [spinToConway_apply, axiomToConway_apply, Matrix.mul_apply]
  push_cast
  exact (Equiv.sum_comp piPerm (fun k => (N s k : ℂ) * (A k (piPerm i) : ℂ))).symm

theorem spinToConway_mul_left (R : Matrix SpinIdx SpinIdx ℚ) (N : SpaceW) :
    spinToConway (R * N) = R.map (Rat.castHom ℂ) * spinToConway N := by
  ext s i
  simp only [spinToConway_apply, Matrix.mul_apply, Matrix.map_apply, Rat.coe_castHom]
  push_cast
  rfl

/-- `U_c^π = y yᵀ`, `y` the Conway coordinates of `α_c`. -/
theorem axiomToConway_Umat (c : ShortIdx) :
    axiomToConway (Umat c) = vecMulVec (fun i => (LeechMatch.vec (shortVec c) i : ℂ))
      (fun i => (LeechMatch.vec (shortVec c) i : ℂ)) := by
  ext i j
  simp only [axiomToConway_apply, Umat, vecMulVec_apply, uQ, vec_shortVec]
  push_cast
  rfl

/-! ## §3  The dictionary on `SpaceW` -/

/-- The scale `λ` of the `W`-block: a square root of `−1/(2κ)`. -/
noncomputable def spinDictScale : ℂ := (-(2 * spinFormScale)⁻¹) ^ (((2 : ℕ) : ℂ)⁻¹)

theorem spinDictScale_sq : spinDictScale ^ 2 = -(2 * spinFormScale)⁻¹ :=
  Complex.cpow_nat_inv_pow _ two_ne_zero

/-- **The `W`-dictionary** `N ↦ λ · spinTopVec (N^π) ∈ (T⁺)₂`. -/
noncomputable def spinDict : SpaceW →+ TP where
  toFun N := spinDictScale • spinTopVec (spinToConway N)
  map_zero' := by rw [map_zero, map_zero, smul_zero]
  map_add' N M := by rw [map_add, map_add, smul_add]

theorem spinDict_apply (N : SpaceW) : spinDict N = spinDictScale • spinTopVec (spinToConway N) :=
  rfl

theorem spinDict_smul (q : ℚ) (N : SpaceW) : spinDict (q • N) = (q : ℂ) • spinDict N := by
  rw [spinDict_apply, spinDict_apply, spinToConway_smul, map_smul, smul_comm]

theorem spinDict_mem_weight_two (N : SpaceW) : spinDict N ∈ plusModule.weight (2 : ℂ) :=
  Submodule.smul_mem _ _ (spinTopVec_mem_weight_two _)

/-- ⭐ **The form on the `W`-block**: `TPForm (spinDict N) (spinDict M) = 2 Σ N_{ji} M_{ji}`. -/
theorem TPForm_spinDict (N M : SpaceW) :
    TPForm (spinDict N) (spinDict M) = 2 * ((∑ j, ∑ i, N j i * M j i : ℚ) : ℂ) := by
  rw [spinDict_apply, spinDict_apply]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [TPForm_spinTopVec]
  have hsum : ∑ s, ∑ i, spinToConway N s i * spinToConway M s i
      = ((∑ j, ∑ i, N j i * M j i : ℚ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [spinToConway_apply]
    exact Equiv.sum_comp piPerm (fun i => (N s i : ℂ) * (M s i : ℂ))
  rw [hsum]
  have hκ := spinFormScale_ne_zero
  have hlam := spinDictScale_sq
  rw [sq] at hlam
  rw [← mul_assoc, hlam]
  field_simp
  ring

/-! ## §4  The module channels `A·W` and `X·W` in Axiom's coordinates -/

/-- ⭐ **The `A·W` channel**: `Q(A)₍₁₎ (spinDict N) = spinDict ((tr A / 8) N + N A)`. -/
theorem topAct_matDict_spinDict (A : symMat) (N : SpaceW) :
    topAct (matDict A) (spinDict N)
      = spinDict ((trace (A : Matrix (Fin 24) (Fin 24) ℚ) / 8) • N + N * (A : Matrix (Fin 24) (Fin 24) ℚ)) := by
  rw [spinDict_apply, spinDict_apply, map_smul, matDict_apply,
    topAct_conwayQuad_spinTopVec (axiomToConway_symm A), map_add spinToConway, spinToConway_smul,
    spinToConway_mul_right, trace_axiomToConway, add_comm,
    show ((trace (A : Matrix (Fin 24) (Fin 24) ℚ) / 8 : ℚ) : ℂ)
      = ((trace (A : Matrix (Fin 24) (Fin 24) ℚ) : ℚ) : ℂ) / 8 by push_cast; ring]

/-- The `x_{α_c}`-action on the `W`-dictionary, one short class at a time:
`ζ'_c x_{α_c}₍₁₎ (spinDict N) = ⅛ spinDict (R_c N − ¼ R_c N U_c)`. -/
theorem topAct_frameX0P_spinDict (c : ShortIdx) (N : SpaceW) :
    fullShortSign c • topAct (frameX0P (shortVec c)) (spinDict N)
      = (8 : ℂ)⁻¹ • spinDict (Rmat c * N - (4 : ℚ)⁻¹ • (Rmat c * N * Umat c)) := by
  have harg : spinToConway (Rmat c * N - (4 : ℚ)⁻¹ • (Rmat c * N * Umat c))
      = fullShortSign c • (spinOp (coordOfRed (red leech (shortVec c))) * spinToConway N
          - (4 : ℂ)⁻¹ • (spinOp (coordOfRed (red leech (shortVec c))) * spinToConway N
            * vecMulVec (fun i => (LeechMatch.vec (shortVec c) i : ℂ))
                (fun i => (LeechMatch.vec (shortVec c) i : ℂ)))) := by
    rw [map_sub, spinToConway_smul, spinToConway_mul_right, spinToConway_mul_left,
      axiomToConway_Umat, ← fullShortSign_smul_spinOp c]
    simp only [Matrix.smul_mul, smul_sub, smul_smul]
    rw [show ((4⁻¹ : ℚ) : ℂ) * fullShortSign c = fullShortSign c * (4 : ℂ)⁻¹ by push_cast; ring]
  rw [spinDict_apply, spinDict_apply, map_smul, topAct_frameX0P_spinTopVec (shortVec_norm c), harg,
    map_smul]
  simp only [smul_smul]
  congr 1
  ring

/-- ⭐ **The `X·W` channel**:
`(Σ_c x_c ζ'_c x_{α_c})₍₁₎ (spinDict N) = spinDict (⅛ Σ_c x_c (R_c N − ¼ R_c N U_c))`. -/
theorem topAct_shortDict_spinDict (x : SpaceX) (N : SpaceW) :
    topAct (shortDict fullShortSign x) (spinDict N)
      = spinDict ((8 : ℚ)⁻¹ • ∑ c, x c • (Rmat c * N - (4 : ℚ)⁻¹ • (Rmat c * N * Umat c))) := by
  rw [shortDict_apply, topAct_sum, LinearMap.sum_apply, spinDict_smul, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [topAct_smul, LinearMap.smul_apply, spinDict_smul, mul_smul, topAct_frameX0P_spinDict,
    smul_comm ((x c : ℚ) : ℂ), show ((8⁻¹ : ℚ) : ℂ) = (8 : ℂ)⁻¹ by norm_num]

/-- Axiom's action of an untwisted vector `u` on `W`:
`u·N = (tr A/8) N + N A + ⅛ Σ_c x_c (R_c N − ¼ R_c N U_c)`, `A = u.1`, `x = u.2.1`. -/
noncomputable def spinBlockAction (u : SpaceB) (N : SpaceW) : SpaceW :=
  (trace (u.1 : Matrix (Fin 24) (Fin 24) ℚ) / 8) • N + N * (u.1 : Matrix (Fin 24) (Fin 24) ℚ)
    + (8 : ℚ)⁻¹ • ∑ c, u.2.1 c • (Rmat c * N - (4 : ℚ)⁻¹ • (Rmat c * N * Umat c))

/-- ⭐ **The untwisted action on the `W`-dictionary**:
`(untwistedDict ζ' u)₍₁₎ (spinDict N) = spinDict (u·N)`. -/
theorem topAct_untwistedDict_spinDict (u : SpaceB) (N : SpaceW) :
    topAct (untwistedDict fullShortSign u) (spinDict N) = spinDict (spinBlockAction u N) := by
  rw [untwistedDict_apply, topAct_add, LinearMap.add_apply, topAct_matDict_spinDict,
    topAct_shortDict_spinDict, ← map_add spinDict]
  rfl

/-! ## §5  Axiom's product of an untwisted vector with a `W`-vector, and the `W·W` invariance -/

theorem spinBlock_add (a b : SpaceW) : spinBlock (a + b) = spinBlock a + spinBlock b := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [spinBlock]

theorem gmul_symBlock_spinBlock (A : symMat) (N : SpaceW) :
    gmul (symBlock A) (spinBlock N)
      = spinBlock ((trace (A : Matrix (Fin 24) (Fin 24) ℚ) / 8) • N + N * (A : Matrix (Fin 24) (Fin 24) ℚ)) := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
  · exact gmul_symBlock_spinBlock_fst A N
  · exact gmul_symBlock_spinBlock_snd_fst A N
  · exact gmul_symBlock_spinBlock_snd_snd A N

theorem gmul_spinBlock_symBlock (N : SpaceW) (A : symMat) :
    gmul (spinBlock N) (symBlock A)
      = spinBlock ((trace (A : Matrix (Fin 24) (Fin 24) ℚ) / 8) • N + N * (A : Matrix (Fin 24) (Fin 24) ℚ)) := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
  · exact gmul_spinBlock_symBlock_fst N A
  · exact gmul_spinBlock_symBlock_snd_fst N A
  · exact gmul_spinBlock_symBlock_snd_snd N A

theorem gmul_shortBlock_spinBlock (x : SpaceX) (N : SpaceW) :
    gmul (shortBlock x) (spinBlock N)
      = spinBlock ((8 : ℚ)⁻¹ • ∑ c, x c • (Rmat c * N - (4 : ℚ)⁻¹ • (Rmat c * N * Umat c))) := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
  · exact gmul_shortBlock_spinBlock_fst x N
  · exact gmul_shortBlock_spinBlock_snd_fst x N
  · exact gmul_shortBlock_spinBlock_snd_snd x N

theorem gmul_spinBlock_shortBlock (N : SpaceW) (x : SpaceX) :
    gmul (spinBlock N) (shortBlock x)
      = spinBlock ((8 : ℚ)⁻¹ • ∑ c, x c • (Rmat c * N - (4 : ℚ)⁻¹ • (Rmat c * N * Umat c))) := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
  · exact gmul_spinBlock_shortBlock_fst N x
  · exact gmul_spinBlock_shortBlock_snd_fst N x
  · exact gmul_spinBlock_shortBlock_snd_snd N x

/-- For `u` with zero `W`-part: `u·(0,0,N) = (0, 0, u·N)`. -/
theorem gmul_untwisted_spinBlock {u : SpaceB} (hu : u.2.2 = 0) (N : SpaceW) :
    gmul u (spinBlock N) = spinBlock (spinBlockAction u N) := by
  conv_lhs => rw [eq_symBlock_add_shortBlock hu]
  rw [map_add, LinearMap.add_apply, gmul_symBlock_spinBlock, gmul_shortBlock_spinBlock,
    ← spinBlock_add]
  rfl

/-- For `u` with zero `W`-part: `(0,0,N)·u = (0, 0, u·N)`. -/
theorem gmul_spinBlock_untwisted {u : SpaceB} (hu : u.2.2 = 0) (N : SpaceW) :
    gmul (spinBlock N) u = spinBlock (spinBlockAction u N) := by
  conv_lhs => rw [eq_symBlock_add_shortBlock hu]
  rw [map_add, gmul_spinBlock_symBlock, gmul_spinBlock_shortBlock, ← spinBlock_add]
  rfl

/-- `R_c` is symmetric on short classes (`pair a δ = 0`). -/
theorem Rmat_transpose_of_short (c : ShortIdx) : (Rmat c)ᵀ = Rmat c := by
  rw [Rmat, qmatR_transpose, pair_eq_zero_of_isShortCoord c.2, add_zero]

/-- `qf c X = tr(X U_c)`. -/
theorem qf_eq_trace_mul_Umat (c : ShortIdx) (X : Matrix (Fin 24) (Fin 24) ℚ) :
    qf c X = trace (X * Umat c) := by
  simp only [qf, Umat, trace, diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The `SpaceW` pairing as a trace: `Σ_{j,i} M_{ji} K_{ji} = tr(Mᵀ K)`. -/
theorem sum_mul_eq_trace (M K : SpaceW) : ∑ j, ∑ i, M j i * K j i = trace (Mᵀ * K) := by
  simp only [trace, diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

/-- ⭐ **Invariance of Axiom's form on `W × W × (A ⊕ X)`**: for `u` with zero `W`-part,
`bform (N·M) u = bform M (u·N)`. -/
theorem bform_gmul_spinBlock_spinBlock (N M : SpaceW) {u : SpaceB} (hu : u.2.2 = 0) :
    bform (gmul (spinBlock N) (spinBlock M)) u
      = bform (spinBlock M) (spinBlock (spinBlockAction u N)) := by
  have hA : (u.1 : Matrix (Fin 24) (Fin 24) ℚ)ᵀ = (u.1 : Matrix (Fin 24) (Fin 24) ℚ) := u.1.2
  have t1 : trace (Nᵀ * M) = trace (Mᵀ * N) := by
    rw [← trace_transpose, transpose_mul, transpose_transpose]
  have t2 : trace (Nᵀ * M * (u.1 : Matrix (Fin 24) (Fin 24) ℚ))
      = trace (Mᵀ * N * (u.1 : Matrix (Fin 24) (Fin 24) ℚ)) := by
    rw [← trace_transpose, transpose_mul, transpose_mul, transpose_transpose, hA, trace_mul_comm]
  have t3 : ∀ c, trace (Nᵀ * Rmat c * M) = trace (Mᵀ * Rmat c * N) := fun c => by
    rw [← trace_transpose, transpose_mul, transpose_mul, transpose_transpose,
      Rmat_transpose_of_short, Matrix.mul_assoc]
  have t4 : ∀ c, qf c (Nᵀ * Rmat c * M) = trace (Mᵀ * Rmat c * N * Umat c) := fun c => by
    rw [qf_eq_trace_mul_Umat, ← trace_transpose, transpose_mul, transpose_mul, transpose_mul,
      transpose_transpose, Rmat_transpose_of_short, Umat_symm, trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [bform_spinBlock_spinBlock, sum_mul_eq_trace, bform_apply, gmul_spinBlock_spinBlock_fst,
    gmul_spinBlock_spinBlock_snd_fst, gmul_spinBlock_spinBlock_snd_snd, hu]
  simp only [Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  rw [spinBlockAction, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul,
    Matrix.add_mul, trace_add, trace_smul, trace_smul, trace_add, t1, t2]
  rw [Matrix.mul_add, Matrix.mul_add, trace_add, trace_add, Matrix.mul_smul, trace_smul,
    ← Matrix.mul_assoc, Matrix.mul_smul, trace_smul, Matrix.mul_sum, trace_sum]
  have hsum : ∑ c, (trace (Nᵀ * Rmat c * M) - qf c (Nᵀ * Rmat c * M) / 4) / 8 * u.2.1 c
      = (8 : ℚ)⁻¹ • ∑ c, trace (Mᵀ * (u.2.1 c • (Rmat c * N - (4 : ℚ)⁻¹ • (Rmat c * N * Umat c)))) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mul_smul, trace_smul, Matrix.mul_sub, trace_sub, Matrix.mul_smul, trace_smul, t3, t4]
    simp only [← Matrix.mul_assoc, smul_eq_mul]
    ring
  rw [hsum]
  simp only [smul_eq_mul]
  ring

end VOA.Moonshine.GriessDictionary
