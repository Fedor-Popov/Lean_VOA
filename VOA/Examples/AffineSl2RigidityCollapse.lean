/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.AffineSl2Rigidity43
import VOA.Examples.NonzeroDeformation
import VOA.Examples.TripletW2
import VOA.Examples.HeisenbergC2

/-!
# ⚠ Two dead ends in Linshaw–Qi §5, and the certificates that the SPLIT avoids both

This file records, **as theorems**, that two successive readings of Linshaw–Qi §5 fail — the
first by being *refutable*, the second by being a *tautology* — and it supplies the formal
certificates that the current split hypotheses (`LQ43.Sl2BasisOnWeightOne` +
`LQ43.NormalisedPoleVanishes`) avoid both failures.  It is the deformation-theoretic analogue of
`Modularity/UniCollapse.lean`: nothing here is used downstream, and that is the point.

* §1–§3: the **first** dead end.  `GradedImpliesRegular L43` and its weakening
  `GradedImpliesPoleZero L43` are **false**, so a main theorem stated over them is *vacuous*.
* §4: the **second** dead end, and the repair.  `LQ43.GradedRegularUpToCoboundary` — not part of
  the library — removes the vacuity but is *uniformly derivable from its own conclusion*, so a main
  theorem stated over it is a *tautology*.  §4 proves that PIECE 2 of the split has no such derivation, by refuting
  it at the rank-1 free boson.

## The refuted readings

* `GradedImpliesRegular W` — "every graded first-order deformation of `W` is regular", i.e.
  `Y₁(a,x)b` has no negative powers of `x` for all weight-one `a, b`.
* `GradedImpliesPoleZero W` — the weakening to the `x^{-2}` coefficient alone, i.e. "the paper's
  pole constant `c` vanishes for every graded deformation".

Both are refuted for `L₋₄⁄₃(𝔰𝔩₂)`.

## The mechanism, in one line

**Coboundaries are themselves graded first-order deformations, and they are not regular.**

The witness was in the repository the whole time: `NonzeroDeform.scalingDeformation = δ(L₀)`, the
coboundary of the grading operator.  `L₀` is grade-preserving and kills `𝟙`, so `δL₀` is a
legitimate — indeed *trivial* — first-order deformation, it is graded
(`NonzeroDeform.isGraded_scalingDeformation`), and its products are computed outright:

`u¹₍ₙ₎v = (L₀u)₍ₙ₎v - L₀(u₍ₙ₎v) + u₍ₙ₎(L₀v) = (n+1)·u₍ₙ₎v`

on homogeneous `u, v` (`NonzeroDeform.smul₁_scalingDeformation_homog`: the weights cancel,
`a - (a+b-n-1) + b = n+1`, independently of `a` and `b`).  Hence

* at `n = 0` the factor is `1`, so regularity of `δL₀` would force `a₍₀₎b = 0` for **all**
  weight-one `a, b` — "the weight-one Lie bracket of `W` vanishes identically";
* at `n = 1` the factor is `2`, so vanishing of the pole coefficient would force `a₍₁₎b = 0` for
  all weight-one `a, b` — "the level is zero".

For `L₋₄⁄₃(𝔰𝔩₂)` both fail, at `h₍₀₎e = 2e` and at `f₍₁₎e = k𝟙 = -(4/3)𝟙`.  The nonvanishing of
`e` in the quotient is `currentE_not_mem`, proved through Li's radical theorem from
`form_f_e : (f|e) = -k ≠ 0`.

## ⚠⚠ What this file refutes — and what it does **not**

It does **not** refute Linshaw–Qi.  Their §5 never claims that every graded `Y₁` is regular on the
nose.  Their equation (3) — "the singular part of `Y₁(a,x)b` is `c⟨a,b⟩𝟙 x^{-2}`" — already
*asserts* that the `x^{-1}` coefficient `a¹₍₀₎b` vanishes, and that is a **normalisation of the
representative inside its cohomology class**, not a theorem about an arbitrary graded `Y₁`.  It is
licensed by [KQ] §6.2 / Whitehead's `H²(𝔤,𝔤) = 0`: for graded `D` the map `(a,b) ↦ a¹₍₀₎b` is a
2-cochain on `𝔤 = 𝒱₁` valued in `𝒱_{1+1-0-1} = 𝒱₁ = 𝔤`, the cocycle condition makes it a
Chevalley–Eilenberg 2-cocycle, and `H²(𝔤,𝔤) = 0` lets one subtract `δφ` with `φ = ψ ∘ P₁` to kill
it.  Only *then* is the single constant `c` defined, and only then is it gauge-invariant: a
coboundary with `φ|_{𝒱₁} = ψ` shifts `(x^{-1}, x^{-2})` by
`((δ_Lie ψ)(a,b), k(⟨ψa,b⟩ + ⟨a,ψb⟩))`, so preserving `x^{-1} = 0` forces `ψ ∈ Der(𝔤) = ad(𝔤)`
and invariance of `⟨,⟩` gives `Δc = 0`.  Without the normalisation `c` is not an invariant at
all — `δL₀` moves it by `2k`, which is exactly what `not_gradedImpliesPoleZero_L43` detects.

So the defect was one of **generality**, not of encoding.  Specifically it was **not**:

* a bad encoding of "regular" — `Deform.FirstOrderDeformation.Regular` is faithful to "no
  negative powers of `x`" (`Deform.FirstOrderDeformation.regular_iff` checks the index
  arithmetic `mode f n = f (-n-1)`), and since `smul₁` is bilinear, quantifying over all of
  `W.grading 1` is equivalent to quantifying over the paper's generators `a(-1)𝟙, b(-1)𝟙`;
* a bad encoding of "graded" — `Deform.FirstOrderDeformation.IsGraded` is a faithful
  transcription of order-`t` VA1, and the extra constraint the paper implicitly uses is a
  normalisation of the representative, not a gradedness condition.

It was the third possibility: §5's conclusion, which the paper reaches only *after* the [KQ]
normalisation, was asserted for **every** graded cocycle.  Since coboundaries are graded cocycles
(`Deform.coboundaries_le_gradedCochains`) and are generically non-regular, the over-general
statement is not merely unproved but refutable.

**The correct repair is to SPLIT**, not to weaken.  The normalisation is
`VertexOperatorAlgebra.WeightOneH2Vanishes` (PIECE 1, a statement about `𝒱₁` alone, *discharged*
from an `𝔰𝔩₂`-triple basis by Whitehead's second lemma) and the computation is
`LQ43.NormalisedPoleVanishes` (PIECE 2, stated for a deformation *already in pole form*).  The
intermediate repair `LQ43.GradedRegularUpToCoboundary` — "every graded deformation is regular
modulo a coboundary" — is **not used**: it removes the vacuity but is uniformly derivable from
`Deform.IsRigidGraded` with witness `E = 0`, which makes a main theorem stated over it a tautology.  §4 below is
the certificate that the split does not repeat that.

## Main results

* `weightOne_bracket_eq_zero_of_gradedImpliesRegular` — the general `n = 0` collapse;
* `weightOne_pole_eq_zero_of_gradedImpliesPoleZero` — the general `n = 1` collapse;
* `not_gradedImpliesRegular_L43` — `¬ GradedImpliesRegular L43`;
* `not_gradedImpliesPoleZero_L43` — `¬ GradedImpliesPoleZero L43`, so the weakening fails too;
* `oldHeadline_hypothesis_unsatisfiable` — a main theorem over `GradedImpliesRegular` is visibly empty;
* `not_normalisedPoleVanishes_heisenberg` — PIECE 2 of the split is **false** at the rank-1
  free boson, so it is a genuine constraint on `W`;
* `scalingDeformation_not_inPoleForm_L43` — and at `L43` the same `δ(L₀)` **cannot** refute it,
  because `InPoleForm` fails there: PIECE 2 is neither vacuous nor refutable at the VOA in
  question;
* `not_trivial_satisfies_piece2` — the exact analogue of the deleted `LQ43.trivial_satisfies`
  is **refutable**.  This is the formal contrast between the tautologous hypothesis and PIECE 2;
* `no_uniform_derivation_piece2`, `no_uniform_derivation_sl2Basis_tripletW2` — a uniform
  derivation of either split hypothesis from graded rigidity would refute graded rigidity of a
  free boson, resp. of the triplet algebra `W(2)`;
* `heis_weightOne_bracket_zero`, `heis_X0_smul_one` — the two free-boson facts that drive §4:
  `𝒱₁` is abelian, and the level is nonzero.

## Status

No `sorry`, no `admit`, no `native_decide`, no new axioms, and no `VOA.pbw`: every
declaration reports `[propext, Classical.choice, Quot.sound]`.

## References
* A. R. Linshaw and F. Qi, *Deformation rigidity of some simple affine VOAs*,
  arXiv:2601.12017v2, §3, §5 (equation (3) is the normalisation discussed above).
* V. Kovalchuk and F. Qi, *First-order deformations of freely generated vertex algebras*,
  arXiv:2408.16309, §6.2 — the `H²(𝔤,𝔤) = 0` normalisation.
-/

open VOA VOA.VertexOperatorAlgebra

namespace VOA.AffineSl2RigidityCollapse

variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1  The two refuted readings, named

Neither is used anywhere else in the repository, and neither should be.  They are stated here
only so that the refutations below have something to be refutations *of*. -/

/-- ⚠⚠ **REFUTED — do not use.**  The naive reading of Linshaw–Qi §5: every graded first-order
deformation of `W` is regular.  `not_gradedImpliesRegular_L43` proves this is false at
`W = L₋₄⁄₃(𝔰𝔩₂)`.  The faithful statement is the SPLIT of §4:
`VertexOperatorAlgebra.WeightOneH2Vanishes` (the normalisation) plus
`LQ43.NormalisedPoleVanishes` (the computation, for a deformation already in pole form). -/
def GradedImpliesRegular (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ D : Deform.FirstOrderDeformation W, D.IsGraded → D.Regular

/-- ⚠⚠ **REFUTED — do not use.**  The weakening of `GradedImpliesRegular` to the `x^{-2}`
coefficient alone — "the paper's pole constant `c` vanishes for every graded deformation".  This
is the reading one reaches for after noticing that the `x^{-1}` clause is the problem.  It fails
too: `not_gradedImpliesPoleZero_L43`.  The reason is that `c` is simply not gauge-invariant before
the [KQ] §6.2 normalisation. -/
def GradedImpliesPoleZero (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ D : Deform.FirstOrderDeformation W, D.IsGraded →
    ∀ a ∈ W.grading 1, ∀ b ∈ W.grading 1, D.poleVec a b = 0

/-! ## §2  The general collapse, at `n = 0` and at `n = 1`

Both run through the repository's own `NonzeroDeform.scalingDeformation = δ(L₀)`.  Nothing about
`L₋₄⁄₃(𝔰𝔩₂)` enters yet: these hold for every VOA. -/

/-- ⚠ **The `n = 0` collapse.**  If every graded first-order deformation of `W` is regular, then
the weight-one Lie bracket of `W` is identically zero.

Proof: apply the hypothesis to `δ(L₀)`, whose `n`-th product is `(n+1)·u₍ₙ₎v`; at `n = 0` the
factor is `1`. -/
theorem weightOne_bracket_eq_zero_of_gradedImpliesRegular (W : VertexOperatorAlgebra 𝒱)
    (h : GradedImpliesRegular W) (a : 𝒱) (ha : a ∈ W.grading 1) (b : 𝒱) (hb : b ∈ W.grading 1) :
    W.smul a 0 b = 0 := by
  have hreg := h (NonzeroDeform.scalingDeformation W)
    (NonzeroDeform.isGraded_scalingDeformation W) a ha b hb 0 le_rfl
  rw [NonzeroDeform.smul₁_scalingDeformation_homog W ha hb 0] at hreg
  simpa using hreg

/-- ⚠ **The `n = 1` collapse.**  If the pole coefficient vanishes for every graded first-order
deformation of `W`, then `a₍₁₎b = 0` for all weight-one `a, b` — for an affine VOA, "the level is
zero".

Proof: the same deformation `δ(L₀)`, now at `n = 1`, where the factor is `2`. -/
theorem weightOne_pole_eq_zero_of_gradedImpliesPoleZero (W : VertexOperatorAlgebra 𝒱)
    (h : GradedImpliesPoleZero W) (a : 𝒱) (ha : a ∈ W.grading 1) (b : 𝒱)
    (hb : b ∈ W.grading 1) : W.smul a 1 b = 0 := by
  have hpole := h (NonzeroDeform.scalingDeformation W)
    (NonzeroDeform.isGraded_scalingDeformation W) a ha b hb
  rw [Deform.FirstOrderDeformation.poleVec,
    NonzeroDeform.smul₁_scalingDeformation_homog W ha hb 1] at hpole
  have h2 : ((1 : ℤ) : ℂ) + 1 = 2 := by norm_num
  rw [h2] at hpole
  rcases smul_eq_zero.mp hpole with h' | h'
  · exact absurd h' (by norm_num)
  · exact h'


/-! ## §3  `L₋₄⁄₃(𝔰𝔩₂)`: the weight-one bracket and the level are both nonzero

Everything here is about the *simple quotient*, so the work is to show that `e` survives it.  Li's
radical theorem does that in one step from `(f|e) = -k = 4/3 ≠ 0`. -/

open VOA.AffineVOA VOA.AffineLie VOA.AffineVOA.Inst
open VOA.LiRadical VOA.Sl2Sing

local notation "kk" => (-4 / 3 : ℂ)

/-- `(f|e) = -k` for the canonical invariant form on `V^{-4/3}(𝔰𝔩₂)`: adjointness of `f₍₋₁₎`
against `f₍₁₎` turns the form into minus the level, via `F1E1` and `(𝟙|𝟙)=1`. -/
theorem form_f_e :
    (canonicalInvariantForm LQ43.vacuum_ne_zero LQ43.quasiPrimary).form
      (currentState kk colF) (currentState kk colE) = -kk := by
  have hu : currentState kk colF ∈ voaSl2Adm.grading 1 :=
    currentState_mem_grading kk admLevel_noncritical colF
  have h1 : voaSl2Adm.L 1 (currentState kk colF) = 0 := LQ43.quasiPrimary _ hu
  have key := LQ43.weightOne_adj (𝒱 := WakModule kk)
    (canonicalInvariantForm_isFullyInvariant LQ43.vacuum_ne_zero LQ43.quasiPrimary) hu h1
    (-1) voaSl2Adm.vacuum (currentState kk colE)
  rw [show (- -1 : ℤ) = 1 from by norm_num] at key
  rw [show voaSl2Adm.smul (currentState kk colF) (-1) voaSl2Adm.vacuum = currentState kk colF from
        by rw [LQ43.smul_currentState_adm, voaSl2Adm_vacuum, currentState_def],
      show voaSl2Adm.smul (currentState kk colF) 1 (currentState kk colE)
          = kk • voaSl2Adm.vacuum from
        by rw [LQ43.smul_currentState_adm, currentState_def, voaSl2Adm_vacuum, F1E1]] at key
  rw [key, map_smul,
    show (canonicalInvariantForm LQ43.vacuum_ne_zero LQ43.quasiPrimary).form
        voaSl2Adm.vacuum voaSl2Adm.vacuum = 1 from
      canonicalInvariantForm_normalized LQ43.vacuum_ne_zero LQ43.quasiPrimary]
  simp

/-- **`e` survives in `L₋₄⁄₃(𝔰𝔩₂)`.**  By Li's theorem the maximal graded ideal is the radical
of the canonical form, and `(f|e) = 4/3 ≠ 0` puts `e` outside it. -/
theorem currentE_not_mem : currentState kk colE ∉ QuotVOA.maxGradedIdeal voaSl2Adm := by
  rw [← rightRadical_eq_maxGradedIdeal
    (canonicalInvariantForm_isFullyInvariant LQ43.vacuum_ne_zero LQ43.quasiPrimary)
    (canonicalInvariantForm_normalized LQ43.vacuum_ne_zero LQ43.quasiPrimary)]
  intro h
  have hz := (SingVec.mem_rightRadical.mp h) (currentState kk colF)
  rw [form_f_e] at hz
  norm_num at hz

/-- `h₍₀₎e = 2e` in `L₋₄⁄₃(𝔰𝔩₂)`, with both sides nonzero. -/
theorem mkQ_H0E : LQ43.L43.smul ((QuotVOA.maxGradedIdeal voaSl2Adm).mkQ (currentState kk colH)) 0
      ((QuotVOA.maxGradedIdeal voaSl2Adm).mkQ (currentState kk colE))
    = (2 : ℂ) • (QuotVOA.maxGradedIdeal voaSl2Adm).mkQ (currentState kk colE) := by
  have hI := QuotVOA.maxGradedIdeal_isIdeal voaSl2Adm
  have hgr := QuotVOA.maxGradedIdeal_isGradedIdeal voaSl2Adm
  rw [show LQ43.L43.smul ((QuotVOA.maxGradedIdeal voaSl2Adm).mkQ (currentState kk colH)) 0
          ((QuotVOA.maxGradedIdeal voaSl2Adm).mkQ (currentState kk colE))
        = (QuotVOA.maxGradedIdeal voaSl2Adm).mkQ
            (voaSl2Adm.smul (currentState kk colH) 0 (currentState kk colE)) from
      QuotVOA.quotientVOA_mkQ_smul hI hgr _ _ _,
    LQ43.smul_currentState_adm, currentState_def, H0E1, map_smul, ← currentState_def]

/-- **`GradedImpliesRegular L43` is FALSE.**  Hence the earlier form of
`LQ43.L43_isRigidGraded`, which took it as a hypothesis, was **vacuous**. -/
theorem not_gradedImpliesRegular_L43 : ¬ GradedImpliesRegular LQ43.L43 := by
  intro h
  have hI := QuotVOA.maxGradedIdeal_isIdeal voaSl2Adm
  have hgr := QuotVOA.maxGradedIdeal_isGradedIdeal voaSl2Adm
  set I := QuotVOA.maxGradedIdeal voaSl2Adm with hIdef
  have hh : I.mkQ (currentState kk colH) ∈ LQ43.L43.grading 1 :=
    QuotVOA.quotientVOA_mkQ_grading hI hgr (currentState_mem_grading kk admLevel_noncritical colH)
  have he : I.mkQ (currentState kk colE) ∈ LQ43.L43.grading 1 :=
    QuotVOA.quotientVOA_mkQ_grading hI hgr (currentState_mem_grading kk admLevel_noncritical colE)
  have hzero := weightOne_bracket_eq_zero_of_gradedImpliesRegular LQ43.L43 h _ hh _ he
  rw [mkQ_H0E] at hzero
  refine currentE_not_mem ?_
  have h2 : I.mkQ (currentState kk colE) = 0 := by
    rcases smul_eq_zero.mp hzero with h' | h'
    · exact absurd h' (by norm_num)
    · exact h'
  rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2

/-- `f₍₁₎e = k𝟙` in `L₋₄⁄₃(𝔰𝔩₂)`. -/
theorem mkQ_F1E : LQ43.L43.smul ((QuotVOA.maxGradedIdeal voaSl2Adm).mkQ (currentState kk colF)) 1
      ((QuotVOA.maxGradedIdeal voaSl2Adm).mkQ (currentState kk colE))
    = kk • LQ43.L43.vacuum := by
  have hI := QuotVOA.maxGradedIdeal_isIdeal voaSl2Adm
  have hgr := QuotVOA.maxGradedIdeal_isGradedIdeal voaSl2Adm
  rw [show LQ43.L43.smul ((QuotVOA.maxGradedIdeal voaSl2Adm).mkQ (currentState kk colF)) 1
          ((QuotVOA.maxGradedIdeal voaSl2Adm).mkQ (currentState kk colE))
        = (QuotVOA.maxGradedIdeal voaSl2Adm).mkQ
            (voaSl2Adm.smul (currentState kk colF) 1 (currentState kk colE)) from
      QuotVOA.quotientVOA_mkQ_smul hI hgr _ _ _,
    LQ43.smul_currentState_adm, currentState_def, F1E1, map_smul]
  rfl

/-- **The weakening `GradedImpliesPoleZero L43` is FALSE too.**  So one cannot rescue the
refuted statement by asking only for the paper's constant `c` to vanish: `δ(L₀)` moves `c` by
`2k`, and `k = -4/3 ≠ 0`.  This is precisely the failure of gauge-invariance of `c` *before* the
[KQ] §6.2 normalisation. -/
theorem not_gradedImpliesPoleZero_L43 : ¬ GradedImpliesPoleZero LQ43.L43 := by
  intro h
  have hI := QuotVOA.maxGradedIdeal_isIdeal voaSl2Adm
  have hgr := QuotVOA.maxGradedIdeal_isGradedIdeal voaSl2Adm
  set I := QuotVOA.maxGradedIdeal voaSl2Adm with hIdef
  have hf : I.mkQ (currentState kk colF) ∈ LQ43.L43.grading 1 :=
    QuotVOA.quotientVOA_mkQ_grading hI hgr (currentState_mem_grading kk admLevel_noncritical colF)
  have he : I.mkQ (currentState kk colE) ∈ LQ43.L43.grading 1 :=
    QuotVOA.quotientVOA_mkQ_grading hI hgr (currentState_mem_grading kk admLevel_noncritical colE)
  have hzero := weightOne_pole_eq_zero_of_gradedImpliesPoleZero LQ43.L43 h _ hf _ he
  rw [mkQ_F1E] at hzero
  rcases smul_eq_zero.mp hzero with h' | h'
  · exact absurd h' (by norm_num)
  · exact LQ43.L43_vacuum_ne_zero h'

/-! ## §4  Why the SPLIT is not bookkeeping — the free-boson certificates

A first repair of the refuted statements of §1–§3 is

`GradedRegularUpToCoboundary W := ∀ D graded, ∃ E graded regular, IsCoboundary W (D.Y1 - E.Y1)`,

which removes the vacuity but introduces a **worse** defect: it is *uniformly derivable from its
own conclusion*.  Given `IsRigidGraded W`, take `E = 0`; then `D.Y1 - 0` is a coboundary and `0`
is graded and regular.  That derivation uses **nothing** about `W`, so a main theorem fed by it is a
tautology.  That predicate, and the lemmas `LQ43.trivial_satisfies`,
`LQ43.gradedRegularUpToCoboundary_of_isRigidGraded`,
`LQ43.gradedRegularUpToCoboundary_iff_isRigidGraded` and
`LQ43.gradedRegularUpToCoboundary_of_grading_one_eq_bot` that supported it, are not part of the library.

The current hypotheses are the two independent halves Linshaw–Qi actually keep separate:

* **PIECE 1**, `VertexOperatorAlgebra.WeightOneH2Vanishes` — the [KQ] §6.2 normalisation, a
  statement about the Lie algebra `𝒱₁` alone.  It is not a hypothesis at all: it is *discharged*
  from `LQ43.Sl2BasisOnWeightOne` by Whitehead's second lemma
  (`VertexOperatorAlgebra.weightOneH2Vanishes_of_sl2Basis`).
* **PIECE 2**, `LQ43.NormalisedPoleVanishes` — the §5 computation, for a deformation *already in
  pole form*.  This is where the level `-4/3` and the singular vector enter, and only here.

### The criterion, and why it is the right one

At a **fixed** `W`, "not implied by `IsRigidGraded W`" is unattainable for any true hypothesis:
two true propositions imply each other.  The criterion with content is **uniform derivability** —
is there a proof of `∀ W, IsRigidGraded W → H W` using nothing about `W`?  Since rigidity's whole
force is to collapse every graded `D` into a coboundary `δφ`, a uniform derivation of
`H = ∀ D graded, P D` exists precisely when `P` restricted to `D = δφ` — the **coboundary
content** of `H` — is provable with no input about `W`.

* For the deleted hypothesis the coboundary content was provable for **every** `W` in two lines;
  that was literally the deleted theorem `trivial_satisfies`.  Nothing survived.
* For PIECE 2 the coboundary content is: *every derivation of `𝒱₁` is skew for the level form*
  `⟨a,b⟩𝟙 = a₍₁₎b`.  (If `D = δφ` with `φ` grade-preserving and `φ𝟙 = 0`, write `ψ := φ|𝒱₁`;
  `InPoleForm D` says `d₁₂ψ = 0`, i.e. `ψ ∈ Der(𝒱₁)`, and since `a₍₁₎b ∈ 𝒱₀ = ℂ𝟙` with `φ𝟙 = 0`
  the conclusion reads `⟨ψa,b⟩ + ⟨a,ψb⟩ = 0`.)  At `L43` that is true, through
  `Der(𝔰𝔩₂) = ad(𝔰𝔩₂)` plus invariance of the form — genuine `W`-specific input.  At the **rank-1
  free boson** it is false: `𝒱₁ = ℂα` is abelian, so every `ψ` is a derivation, while
  `⟨α,α⟩ = α₍₁₎α = k𝟙 ≠ 0`.

The three theorems below make that formal.  `not_trivial_satisfies_piece2` is the exact analogue
of the deleted `trivial_satisfies` and is **refutable**; that is a formal contrast, not a
rhetorical one.

⚠ **What is NOT achieved, stated plainly.**  A fully unconditional separation would exhibit a `W`
with `IsRigidGraded W` **proved** and a piece refuted.  This repository proves `IsRigidGraded` for
no VOA at all, so that is out of reach; `no_uniform_derivation_piece2` is the strongest available
statement, and it is sharp: a uniform derivation would produce a non-trivial *graded* first-order
deformation of a free boson, which the repository has never produced for any VOA
(`Examples/NonzeroDeformation.lean` records that its only non-trivial deformation,
`l1Deformation`, is **ungraded**).

⚠⚠ **The residual, stated so that nobody re-discovers it as a defect.**  *At `L43` specifically*,
and **given** `LQ43.Sl2BasisOnWeightOne L43`, PIECE 2 remains mathematically **equivalent** to the
conclusion: `IsRigidGraded L43` turns every graded `D` in pole form into `δφ`, `InPoleForm` makes
`ψ := φ|𝒱₁` a derivation, `Der(𝔰𝔩₂) = ad(𝔰𝔩₂)` (Whitehead's **first** lemma) makes it `ad x`, and
invariance of the level form then gives `poleVec = 0`.  So
`IsRigidGraded L43 ↔ RegularImpliesTrivialGraded L43 ∧ NormalisedPoleVanishes L43` holds under
`hb`, and it is *reachable* in Lean — Mathlib has Whitehead I as
`LieDerivation.IsKilling.exists_eq_ad`, needing only `LieAlgebra.IsKilling ℂ ↥(𝒱₁)` (a 3×3 Killing
Gram determinant).  This is **not** the defect that was repaired, and it is not repairable:

* the deleted `GradedRegularUpToCoboundary` was derivable from its conclusion **uniformly, in one
  line, using nothing about `W`** — the derivation was bookkeeping;
* PIECE 2 is derivable from its conclusion only **at `L43`**, only **given `hb`**, and only
  **through Whitehead's first lemma plus invariance of the level form**;
* and *no* faithful split of "Theorem 5.1 = Theorem 3.1 + the §5 computation" can avoid this,
  because §5's *conclusion* is exactly "the normalised pole vanishes".

The way to buy content beyond the split is therefore **not** a different hypothesis but the
bridge: assume §5's *input* (the singular vector and equations (10)–(14), which
`Examples/AffineSl2Rigidity43.lean` §A already proves force `c = 0` unconditionally) instead of
its output.  That is the work item recorded in the docstring of `LQ43.NormalisedPoleVanishes`. -/

/-! ### The weight-one space of the rank-1 free boson is `ℂ·X₀`, and it is abelian -/

/-- A weight-`1` exponent vector is `single 0 1`: `weightFn i = i + 1`, so a variable of weight
`1` must be `X₀` and must occur to the first power. -/
theorem weightDegSet_one_eq {d : ℕ →₀ ℕ} (hd : Finsupp.weight weightFn d = 1) :
    d = Finsupp.single 0 1 := by
  have hsupp : ∀ i : ℕ, i ≠ 0 → d i = 0 := by
    intro i hi
    by_contra hne
    have := weightDegSet_support_lt (w := 1) hd hne
    omega
  have hd0 : d = Finsupp.single 0 (d 0) := by
    refine Finsupp.ext fun i => ?_
    rcases eq_or_ne i 0 with rfl | hi
    · simp
    · rw [hsupp i hi, Finsupp.single_apply, if_neg (Ne.symm hi)]
  have hw : Finsupp.weight weightFn (Finsupp.single (0 : ℕ) (d 0)) = d 0 := by
    simp [Finsupp.weight_single, weightFn_apply]
  have hone : d 0 = 1 := by rw [hd0] at hd; rwa [hw] at hd
  rw [hd0, hone]

/-- The only weight-`1` monomial of the Fock space is `X₀`. -/
theorem weightMonSet_one_subset : weightMonSet 1 ⊆ {(MvPolynomial.X 0 : Fock)} := by
  rintro v ⟨d, hd, rfl⟩
  rw [Set.mem_singleton_iff, weightDegSet_one_eq hd]
  rfl

/-- `𝒱₁` of the rank-1 Heisenberg VOA is contained in `ℂ·X₀`. -/
theorem heis_gradingOne_le_span (k : ℂ) (hk : k ≠ 0) :
    (heisenbergVOA k hk).grading 1 ≤ Submodule.span ℂ {(MvPolynomial.X 0 : Fock)} := by
  intro v hv
  have h : v ∈ gradingZ (1 : ℤ) := hv
  rw [gradingZ_of_nonneg (by norm_num : (0 : ℤ) ≤ 1)] at h
  have hv1 : v ∈ gradingW 1 := by simpa using h
  exact Submodule.span_mono weightMonSet_one_subset (gradingW_le_span 1 hv1)

/-- `X₀` has conformal weight `1`. -/
theorem heis_X0_mem_gradingOne (k : ℂ) (hk : k ≠ 0) :
    (MvPolynomial.X 0 : Fock) ∈ (heisenbergVOA k hk).grading 1 := by
  have h : (MvPolynomial.X 0 : Fock) ∈ gradingW 1 := by
    have hX := MvPolynomial.isWeightedHomogeneous_X ℂ weightFn (0 : ℕ)
    rw [weightFn_apply] at hX
    simpa using hX
  simpa using mem_gradingZ_of_gradingW h

/-- `α₍₀₎ = 0` on the free boson: the zero mode of the current annihilates everything. -/
theorem heis_X0_smul_zero (k : ℂ) (hk : k ≠ 0) (v : Fock) :
    (heisenbergVOA k hk).smul (MvPolynomial.X 0 : Fock) 0 v = 0 := by
  rw [heis_smul_X0 k hk 0 v, osc_zero, LinearMap.zero_apply]

/-- **The weight-one Lie algebra of a free boson is abelian.**  This is what makes
`InPoleForm` automatic there, and it is the whole reason the free boson refutes PIECE 2. -/
theorem heis_weightOne_bracket_zero (k : ℂ) (hk : k ≠ 0) {a : Fock}
    (ha : a ∈ (heisenbergVOA k hk).grading 1) (v : Fock) :
    (heisenbergVOA k hk).smul a 0 v = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (heis_gradingOne_le_span k hk ha)
  rw [PreVertexAlgebra.smul_smul_left, heis_X0_smul_zero, smul_zero]

/-- **The level is nonzero**: `α₍₁₎α = k𝟙`.  This is the pole that PIECE 2 would have to kill
and cannot. -/
theorem heis_X0_smul_one (k : ℂ) (hk : k ≠ 0) :
    (heisenbergVOA k hk).smul (MvPolynomial.X 0 : Fock) 1 (MvPolynomial.X 0 : Fock)
      = k • (heisenbergVOA k hk).vacuum := by
  rw [heis_smul_X0 k hk 1, osc_apply_pos k (by norm_num : (0 : ℤ) < 1)]
  show ((1 : ℤ) : ℂ) • k • MvPolynomial.pderiv ((1 : ℤ) - 1).toNat (MvPolynomial.X 0 : Fock)
    = k • (1 : Fock)
  norm_num [MvPolynomial.pderiv_X_self]

/-! ### The three certificates -/

/-- `δ(L₀)` is automatically **in pole form** on a free boson, because `𝒱₁` is abelian.  This is
the coboundary content of PIECE 2 being tested at its sharpest point. -/
theorem scalingDeformation_inPoleForm (k : ℂ) (hk : k ≠ 0) :
    (NonzeroDeform.scalingDeformation (heisenbergVOA k hk)).InPoleForm := by
  intro a ha b hb
  rw [NonzeroDeform.smul₁_scalingDeformation_homog _ ha hb 0,
    heis_weightOne_bracket_zero k hk ha b, smul_zero]

/-- …but its pole is `2k𝟙 ≠ 0`. -/
theorem scalingDeformation_poleVec_ne_zero (k : ℂ) (hk : k ≠ 0) :
    (NonzeroDeform.scalingDeformation (heisenbergVOA k hk)).poleVec
      (MvPolynomial.X 0 : Fock) (MvPolynomial.X 0 : Fock) ≠ 0 := by
  have hX0 := heis_X0_mem_gradingOne k hk
  rw [Deform.FirstOrderDeformation.poleVec,
    NonzeroDeform.smul₁_scalingDeformation_homog _ hX0 hX0 1, heis_X0_smul_one k hk, smul_smul,
    show (((1 : ℤ) : ℂ) + 1) = 2 from by norm_num]
  intro hzero
  rcases smul_eq_zero.mp hzero with h' | h'
  · rcases mul_eq_zero.mp h' with h2 | h2
    · exact absurd h2 (by norm_num)
    · exact hk h2
  · exact (one_ne_zero : (heisenbergVOA k hk).vacuum ≠ 0) h'

/-- **PIECE 2 is FALSE at the rank-1 free boson.**  `δ(L₀)` is graded and — because `𝒱₁` is
abelian — automatically **in pole form**, yet its pole is `2k𝟙 ≠ 0`.

So `NormalisedPoleVanishes` is a genuine constraint on `W`, not bookkeeping: it fails at a
concrete VOA of this repository, for a reason (`Der(𝒱₁)` not skew for the level form) that is
exactly the `W`-specific Lie theory Linshaw–Qi use at `L43`. -/
theorem not_normalisedPoleVanishes_heisenberg (k : ℂ) (hk : k ≠ 0) :
    ¬ LQ43.NormalisedPoleVanishes (heisenbergVOA k hk) := fun h =>
  scalingDeformation_poleVec_ne_zero k hk
    (h _ (NonzeroDeform.isGraded_scalingDeformation _) (scalingDeformation_inPoleForm k hk)
      _ (heis_X0_mem_gradingOne k hk) _ (heis_X0_mem_gradingOne k hk))

/-- **The counterexample that killed the FIRST hypothesis is BLOCKED against PIECE 2 at
`L43`** — the other half of the certificate, and the one that shows PIECE 2 is not *refutable*.

`δ(L₀)` is what refutes `GradedImpliesRegular L43` and `GradedImpliesPoleZero L43` (§3), and it
is also what refutes PIECE 2 at the free boson (`not_normalisedPoleVanishes_heisenberg`).  At
`L43` it cannot: `InPoleForm` demands `a¹₍₀₎b = 0`, which for `δ(L₀)` is `(0+1)·a₍₀₎b = a₍₀₎b`,
and the weight-one bracket of `L43` is **nonzero** (`mkQ_H0E`: `h₍₀₎e = 2e`, with `e ≠ 0` by
`currentE_not_mem`).

So the two refutations of §3 are turned off by the normalisation hypothesis at exactly the VOA
the main theorem is about, while the *same* deformation still refutes PIECE 2 where `𝒱₁` is abelian.
That is the difference between "vacuous" and "a genuine constraint on `W`", proved rather than
asserted. -/
theorem scalingDeformation_not_inPoleForm_L43 :
    ¬ (NonzeroDeform.scalingDeformation LQ43.L43).InPoleForm := by
  intro h
  have hI := QuotVOA.maxGradedIdeal_isIdeal voaSl2Adm
  have hgr := QuotVOA.maxGradedIdeal_isGradedIdeal voaSl2Adm
  set I := QuotVOA.maxGradedIdeal voaSl2Adm with hIdef
  have hh : I.mkQ (currentState kk colH) ∈ LQ43.L43.grading 1 :=
    QuotVOA.quotientVOA_mkQ_grading hI hgr (currentState_mem_grading kk admLevel_noncritical colH)
  have he : I.mkQ (currentState kk colE) ∈ LQ43.L43.grading 1 :=
    QuotVOA.quotientVOA_mkQ_grading hI hgr (currentState_mem_grading kk admLevel_noncritical colE)
  have hz := h _ hh _ he
  rw [NonzeroDeform.smul₁_scalingDeformation_homog _ hh he 0, mkQ_H0E] at hz
  refine currentE_not_mem ?_
  have h2 : I.mkQ (currentState kk colE) = 0 := by
    rcases smul_eq_zero.mp hz with h' | h'
    · exact absurd h' (by norm_num)
    · rcases smul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' (by norm_num)
      · exact h''
  rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2

/-- **The exact analogue of the statement `trivial_satisfies` is refutable.**

The statement `trivial_satisfies` — *every trivial deformation satisfies the conclusion of the
hypothesis `GradedRegularUpToCoboundary`* — holds for every `W`, in two lines.  That is precisely why that
hypothesis is uniformly derivable from graded rigidity — rigidity turns every graded `D` into a
trivial one, and its conclusion then holds for free.  The corresponding statement for PIECE 2 — *every trivial graded
deformation in pole form has vanishing pole* — is **false**, refuted by `δ(L₀)` on a free boson.

This is the formal contrast between `GradedRegularUpToCoboundary` and PIECE 2, and it is what makes
`no_uniform_derivation_piece2` below more than a restatement. -/
theorem not_trivial_satisfies_piece2 :
    ¬ (∀ (𝒲 : Type) [AddCommGroup 𝒲] [Module ℂ 𝒲] (V : VertexOperatorAlgebra 𝒲)
        (D : Deform.FirstOrderDeformation V), D.IsTrivial → D.IsGraded → D.InPoleForm →
        ∀ a ∈ V.grading 1, ∀ b ∈ V.grading 1, D.poleVec a b = 0) := fun H =>
  scalingDeformation_poleVec_ne_zero 1 one_ne_zero
    (H Fock (heisenbergVOA 1 one_ne_zero) _
      (NonzeroDeform.isTrivial_scalingDeformation _)
      (NonzeroDeform.isGraded_scalingDeformation _)
      (scalingDeformation_inPoleForm 1 one_ne_zero)
      _ (heis_X0_mem_gradingOne 1 one_ne_zero) _ (heis_X0_mem_gradingOne 1 one_ne_zero))

/-- **No uniform derivation of PIECE 2 from graded rigidity.**  A proof of
`∀ W, IsRigidGraded W → NormalisedPoleVanishes W` using nothing about `W` would refute graded
rigidity of every free boson — i.e. would produce a non-trivial **graded** first-order
deformation of a free boson, which this repository has never produced for any VOA.

This is the replacement for the deleted `LQ43.gradedRegularUpToCoboundary_iff_isRigidGraded`, and
it points the opposite way: that theorem *proved* the derivation; this one shows the derivation
cannot be had for free. -/
theorem no_uniform_derivation_piece2 (k : ℂ) (hk : k ≠ 0)
    (H : ∀ (𝒲 : Type) [AddCommGroup 𝒲] [Module ℂ 𝒲] (V : VertexOperatorAlgebra 𝒲),
      Deform.IsRigidGraded V → LQ43.NormalisedPoleVanishes V) :
    ¬ Deform.IsRigidGraded (heisenbergVOA k hk) :=
  fun hrig => not_normalisedPoleVanishes_heisenberg k hk (H Fock (heisenbergVOA k hk) hrig)

/-- **PIECE 1 is not a hypothesis, and the `𝔰𝔩₂`-basis input that replaces it is not uniformly
derivable either.**  `LQ43.no_uniform_derivation_sl2Basis`, instantiated at the triplet algebra
`W(2)`, whose weight-one space is `⊥` (`SympFerm.tripletW2_grading_one`): a uniform derivation
would refute graded rigidity of `W(2)`. -/
theorem no_uniform_derivation_sl2Basis_tripletW2
    (H : ∀ (𝒲 : Type) [AddCommGroup 𝒲] [Module ℂ 𝒲] (V : VertexOperatorAlgebra 𝒲),
      Deform.IsRigidGraded V → LQ43.Sl2BasisOnWeightOne V) :
    ¬ Deform.IsRigidGraded SympFerm.tripletW2 :=
  LQ43.no_uniform_derivation_sl2Basis SympFerm.tripletW2 SympFerm.tripletW2_grading_one H

/-- **A main theorem over `GradedImpliesRegular` is empty.**  Any theorem of the form
`GradedImpliesRegular L43 → …` proves nothing whatever: its hypothesis is unsatisfiable.  Kept as
a single, unmissable statement of what went wrong. -/
theorem oldHeadline_hypothesis_unsatisfiable (h5 : GradedImpliesRegular LQ43.L43) : False :=
  not_gradedImpliesRegular_L43 h5

/-- The same for the weakening. -/
theorem oldHeadline_weakened_hypothesis_unsatisfiable (h5 : GradedImpliesPoleZero LQ43.L43) :
    False :=
  not_gradedImpliesPoleZero_L43 h5

end VOA.AffineSl2RigidityCollapse
