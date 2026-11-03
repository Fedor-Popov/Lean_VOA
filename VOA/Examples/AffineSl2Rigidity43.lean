/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.AffineSl2VOAInstance
import VOA.Examples.WakimotoFree
import VOA.Core.DeformationGraded
import VOA.Core.InvariantFormRadical
import VOA.Core.WeightOneCohomology
import VOA.Examples.NonzeroDeformation

/-!
# Deformation rigidity of `L₋₄⁄₃(𝔰𝔩₂)`: Linshaw–Qi, arXiv:2601.12017v2

Target: **Linshaw–Qi, Theorem 5.1** — the simple affine VOA `L₋₄⁄₃(𝔰𝔩₂)` admits only trivial
first-order deformations.  Their argument has two halves:

* **Theorem 3.1 (the reduction).**  If `Y₁(a,x)b` is *regular* (no negative powers of `x`) for
  all weight-one `a, b`, then `Y₁` is a trivial (coboundary) deformation.
* **Section 5 (the computation).**  At `k = -4/3` the weight-3 singular vector `s` is killed in
  `L₋₄⁄₃(𝔰𝔩₂)`; applying `f^def(1)` and `h^def(1)` to `s` and expanding produces five linear
  equations (10)–(14) in sixteen unknowns whose only consequence for the pole constant `c` is
  `c = 0` — i.e. regularity.

This file delivers the parts that can be **proved outright**, and states the rest as *named,
documented hypotheses*.  Nothing is assumed silently.

## What is proved here, unconditionally

**§A — the linear-algebra core of Section 5.3** (`PrintedSystem.c_eq_zero`,
`CorrectedSystem.c_eq_zero`).  Equations (10)–(14) are transcribed verbatim from the paper and
the Gaussian elimination is carried out in Lean.  Both the intermediate displays (15) and (16)
are reproduced *exactly as printed*, so the file audits the paper's own elimination and not
merely its conclusion.

⚠ **An arithmetic erratum in the paper, found and recorded here.**  Equation (10) is printed
with constant term `+12c`.  The correct value is `+72c`: the paper's own §5.1 display reads
`+ 72c · e(-1)f(-1)1`, and all fifteen `aᵢ/bᵢ/cᵢ` coefficients of (10) are right — only the
`c`-coefficient is wrong.  The printed elimination is internally consistent with the erroneous
`12`, producing the suspiciously clean `10c = 0`.  Both versions are formalised
(`PrintedSystem`, `CorrectedSystem`); the corrected elimination gives `210c = 0`, and **the
conclusion `c = 0` is unaffected**.  See `CorrectedSystem.eq15` for the corrected display.

**§A′ — what the 5×16 system really is** (`PrintedSystem.reduced`, `CorrectedSystem.reduced`).
The fifteen unknowns enter *only* through the five combinations `Pᵢ = 42aᵢ - 9bᵢ - 36cᵢ`, so the
system is five equations in six unknowns, not sixteen; and its solution space is exactly
`c = 0` together with `(P₁,…,P₅) ∈ ℂ·(8, -12, -6, 9, 36)`.  Those five numbers are precisely the
coordinates of the singular vector `s` itself in the paper's own basis
`{e₋₃1, e₋₂h₋₁1, e₋₁h₋₂1, e₋₁h₋₁²1, e₋₁²f₋₁1}` (`sl2Singular_eq_lqBasis`), so the kernel of the
paper's system is exactly the line `ℂ·s`.  This is an internal consistency check that the
paper does not make and that a transcription error would almost certainly break.

**§A″ — the one-line certificate** (`CorrectedSystem.c_eq_zero_certificate`,
`PrintedSystem.ninety_c_eq_zero`, `pSystem_c_eq_zero`, `CorrectedSystem.pForm`).  The paper's
five-step Gaussian elimination through displays (15) and (16) is not needed: the covector
`λ = (30, -14, 18, 23, 9)` spans the left null space of the 5×15 matrix of `aᵢ/bᵢ/cᵢ`
coefficients, so `λ · (10,…,14)` is a *single* scalar equation in `c`.  It reads `1890 c = 0` on
the corrected system and `90 c = 0` on the printed one; `λ` itself is the same for both, since
the erratum touches only the constant column.  Combined with the `P`-reduction this presents §5.3
in the six unknowns it really has (`pSystem_c_eq_zero`), which is the form a future bridge from
`FirstOrderDeformation` should target — it needs the three deformed vectors only through the
single combination `P = 42A - 9B - 36C`.

**§B — the singular-vector identification** (`lqVector_eq_ansatz`, `lqVector_eq_sl2Singular`).
The vector written in Linshaw–Qi §5,
`s = -48 h₋₁e₋₂1 + 36 e₋₁²f₋₁1 - 6 h₋₂e₋₁1 + 9 h₋₁²e₋₁1 + 80 e₋₃1`,
is proved **equal in `WakModule (-4/3)`** to the repository's independently derived
`Sl2Sing.sl2Singular = ansatz (-4/3) 20 (-12) (-6) 36 9`.  The reordering identities
`h₋₁e₋₂1 = M₂ + 2M₁` and `h₋₁²e₋₁1 = M₅ + 4M₂ + 4M₁` are proved from the repository's own
affine commutators.

⚠ **A documentation correction the repository needs.**  `Examples/AffineSl2Singular.lean` §D
("DISCREPANCY WITH THE REPORTED LITERATURE FORM") is **wrong** and should be deleted.  It
reasons only about `h₋₁e₋₂1 = e₋₂h₋₁1 + 2e₋₃1` and overlooks that Linshaw–Qi's `9 h₋₁²e₋₁1`
*also* contributes to the `e₋₂h₋₁1` monomial: `h₋₁²e₋₁1 = M₅ + 4M₂ + 4M₁`.  With that term
included, `M₂ : -48 + 4·9 = -12` and `M₁ : 80 - 2·48 + 4·9 = 20`.  There is no discrepancy;
§D's claim that "the derived ratio is `-12/36 = -1/3` against the reported `-48/36 = -4/3`" is a
miscount.  `lqVector_eq_ansatz` below is the Lean refutation.

**§C — `L₋₄⁄₃(𝔰𝔩₂)` exists as a proper simple quotient**
(`sl2Singular_mem_maxGradedIdeal`, `maxGradedIdeal_ne_bot`, `L43`, `L43_isSimple`,
`L43_vacuum_ne_zero`, `mkQ_sl2Singular_eq_zero`).  This closes a gap the repository had recorded
as out of reach.  `Examples/AffineSl2Singular.lean` §E3 says of properness of the ideal
generated by `s`: "**Out of reach** without (2)", i.e. without a PBW basis; and the Wakimoto
route fails structurally, since Wakimoto modules are irreducible and so a free-field functional
cannot detect properness.  Li's theorem, already in the repository as
`LiRadical.rightRadical_eq_maxGradedIdeal`, gives it directly and in one peel of the mode:

* `weightOne_adj` — for `u ∈ 𝒱₁` with `L₁u = 0`, full invariance collapses to
  `(u₍ₙ₎a|b) = -(a|u₍₋ₙ₎b)`.  Three lines.
* `L1_grading_one` — `L₁𝒱₁ = 0` for `V^k(𝔰𝔩₂)`, from `gradingZA_le_hspan` at weight `1`
  (`wordDegA_eq_one`: a degree-1 word is a single current) and `Vir.current_primary`.  This
  discharges the standing hypothesis `hqp` of `canonicalInvariantForm`, flagged as step 2 of the
  recipe in `Examples/AffineSimpleQuotient.lean` §4 and not done there.
* `sl2Singular_mem_rightRadical` — every weight-3 vector is a combination of word states
  `J^a₍₋ₘ₎y′` with `m ≥ 1`; adjointness turns `(J^a₍₋ₘ₎y′|s)` into `-(y′|J^a₍ₘ₎s) = 0` by
  `Sl2Sing.sl2Singular_pos`, and other weights are orthogonal for free.

This deliberately **bypasses** `SingVec.IsStronglySingularOfWeight`, whose `annihilated` field is
the "second real work item" that `Examples/AffineSimpleQuotient.lean` §4 flags as needing strong
generation.  It is not needed.  Consequence: the conditional Theorem 5.1 below is about an
honest nonzero simple VOA that is genuinely a *proper* quotient of `V^{-4/3}(𝔰𝔩₂)`, so it is not
vacuous.

**§D — `regular_iff_zero_one`.**  For a graded deformation, "regular" (`a^def₍ₙ₎b = 0` for all
`n ≥ 0` on `𝒱₁`) is equivalent to the two conditions `a^def₍₀₎b = 0` and `a^def₍₁₎b = 0`: VOA4
positivity kills `n ≥ 2` automatically.  So the paper's reduction of regularity to finitely many
structure constants is legitimate as far as the mode count goes.

**§E — PIECE 1 of Section 5, the [KQ] §6.2 normalisation, is proved** (in
`Core.WeightOneCohomology`, consumed here through `weightOneH2Vanishes_of_sl2Basis'`).  Its three
ingredients are `Sl2Whitehead.whitehead2_of_sl2Basis` (Whitehead's second lemma `H²(𝔰𝔩₂,𝔰𝔩₂) = 0`,
a finite computation — Mathlib has no Lie-algebra cohomology beyond the low-degree cochain complex
and no Whitehead lemma at all), `Deform.weightOneCochain_mem_twoCocycle` (the `ℓ = m = n = 0`
Jacobi identity *is* the Chevalley–Eilenberg cocycle condition), and
`VertexOperatorAlgebra.coboundary_weightOne_eq_d₁₂` (the repository's VOA coboundary and Mathlib's
`d₁₂` agree on the nose, no sign-translation layer).  Under `Sl2BasisOnWeightOne W` this is a
theorem, so the main theorem does not *assume* the normalisation — which is exactly what avoids
the tautology described under the dead ends below.

## What is NOT proved here — the named hypotheses, and why

**Theorem 3.1** is retained here as `RegularImpliesTrivialGraded`. Its concrete L43
specialization is proved downstream in `AffineSl2RegularReconstruction` as
`L43_regularImpliesTrivialGraded`, using explicit cyclic evaluation, iteration and simplicity.
The following discussion explains the gap that construction resolves at L43.

1. *Provenance.*  The paper carries an authors' statement: "We used ChatGPT 5.6-Pro to detect
   the gaps and mistakes in the previous version.  The proof of Theorem 3.1 in the current
   version is contributed by ChatGPT 5.6-Pro."  The load-bearing reduction is therefore
   AI-authored, in a revision that exists because v1 contained errors.
2. *Independent reconstruction.*  The proof was reconstructed line by line and judged
   **sound**, with one qualification: it invokes
   [L, Theorem 4.11] (Bong H. Lian, *On the classification of simple vertex operator algebras*,
   Comm. Math. Phys. **163** (1994), 307–357, DOI 10.1007/BF02102011) to conclude that the
   subalgebra `W ⊆ Vᵗ` generated by `𝟙` and `V₍₁₎` is a quotient of an affine VOA, and then
   says "in particular `W₍₀₎ = ℂ𝟙`".  Lian's category consists of `ℤ₊`-graded pre-VOAs whose
   degree-0 component is *one-dimensional*, and his subject is *simple* VOAs, whereas `W` is
   only known to be some quotient of `V^k(𝔤)`.  If `W₍₀₎ = ℂ𝟙` is a hypothesis of Thm 4.11
   rather than a conclusion, the citation is circular exactly where `W₍₀₎ = ℂ𝟙` is used to
   derive the contradiction that kills the ideal.  Lian's paper is not on arXiv and was not
   consulted, so the point is not settled from the source.
   **The gap is repairable without Lian**: regularity gives `aᵗ₍₀₎b = ⁅a,b⁆`, `aᵗ₍₁₎b = k⟨a,b⟩𝟙`,
   `aᵗ₍ₙ₎b = 0` for `n ≥ 2`, and `𝟙ᵗ₍ⱼ₎ = δ_{j,-1}`, so the modes `aᵗ₍ₙ₎` satisfy the level-`k`
   affine relations on `W`; with `aᵗ₍ₙ₎𝟙 = 0` for `n ≥ 0` this makes `W` a quotient of the
   generalized Verma module `V^k(𝔤)`, whence `W = span{aᵗ₍₋ₙ₁₎⋯aᵗ₍₋ₙᵣ₎𝟙}` with all `nᵢ ≥ 1` and
   `W₍₀₎ = ℂ𝟙` directly.

The downstream L43 construction uses universal affine evaluation, current-word spanning,
independent energy eigenspaces and the iterate identity to prove the needed closed cyclic
image has only the ordinary vacuum at weight zero. It constructs the trivializing coordinate
change through `Deform.Reconstruction.isTrivial_of_closed_lift`. The arbitrary-VOA assembly
below still takes `RegularImpliesTrivialGraded` explicitly; its L43 specialization does not
need that unproved input.

**Section 5 is SPLIT into two logically independent hypotheses**, because Linshaw–Qi keep them
apart and bundling them makes the hypothesis tautological (see the dead ends below).

* **PIECE 1 — the normalisation** (their equation (3), performed silently, citing [KQ] §6.2).
  For a graded deformation `D`, the map `(a,b) ↦ a¹₍₀₎b` is a 2-cochain on `𝔤 = 𝒱₁` valued in
  `𝒱_{1+1-0-1} = 𝒱₁ = 𝔤`, and the `ℓ = m = n = 0` Jacobi identity makes it a Chevalley–Eilenberg
  2-cocycle.  Whitehead's second lemma `H²(𝔤,𝔤) = 0` then produces `ψ ∈ End(𝔤)` with
  `a¹₍₀₎b = ⁅ψa,b⁆ + ⁅a,ψb⁆ - ψ⁅a,b⁆`; subtracting the induced coboundary kills the `x^{-1}`
  coefficient.  **Only then** is the single constant `c` of equation (3) defined, and only then
  is it gauge-invariant: a residual gauge preserving `x^{-1} = 0` lies in `Der(𝔤) = ad(𝔤)`, and
  invariance of the bilinear form gives `Δc = 0`.
  **This piece is about `𝔤` alone** — nothing to do with the level, the singular vector, or
  `L₋₄⁄₃`.  It is **proved** here, not assumed: `Core.WeightOneCohomology` carries
  `Sl2Whitehead.whitehead2_of_sl2Basis` (Whitehead for `𝔰𝔩₂`, as a finite computation — Mathlib
  has no Lie-algebra cohomology beyond the low-degree cochain complex and no Whitehead lemma),
  `Deform.weightOneCochain_mem_twoCocycle` (the bridge from the deformed Jacobi identity), and
  `VertexOperatorAlgebra.weightOneH2Vanishes_of_sl2Basis`.  What remains assumed at `L43` is only
  the Lie-theoretic input `Sl2BasisOnWeightOne L43` — that `(L43)₁` is `𝔰𝔩₂`.
* **PIECE 2 — the §5 computation** (`NormalisedPoleVanishes`).  For a deformation *already in
  pole form* (`Deform.FirstOrderDeformation.InPoleForm`: `a¹₍₀₎b = 0` on `𝒱₁`), applying
  `f^def(1)` and `h^def(1)` to the weight-3 singular vector `s` and using `s = 0` in `L₋₄⁄₃`
  forces `c = 0`.  **This is the only place the level and the singular vector enter.**
  It is **NOT** proved here; see its docstring for the three remaining steps and for why the
  hardest of them (linear *independence* of the weight-3 monomials, `pbw`-free through Wakimoto)
  is a separate module.

⚠⚠ **Two dead ends, recorded so that neither can recur.**

1. *Vacuity.*  The §5 hypothesis first read `GradedImpliesRegular` — "every graded first-order
   deformation of `W` is regular".  **That is false for `L43`, so a main theorem stated over it is vacuous.**  The
   counterexample was already in the repository: `NonzeroDeform.scalingDeformation = δ(L₀)`
   satisfies `u¹₍ₙ₎v = (n+1)·u₍ₙ₎v` on homogeneous vectors
   (`NonzeroDeform.smul₁_scalingDeformation_homog`) and is graded
   (`NonzeroDeform.isGraded_scalingDeformation`).  At `n = 0` the factor is `1`, so regularity
   would force `a₍₀₎b = 0` for all weight-one `a, b`, which fails at `h₍₀₎e = 2e`; at `n = 1` the
   factor is `2`, so even "the pole coefficient vanishes for every graded deformation" fails, at
   `f₍₁₎e = k𝟙 = -(4/3)𝟙`.  Coboundaries are graded cocycles
   (`Deform.coboundaries_le_gradedCochains`) and are generically non-regular, so *no* statement of
   the form "every graded cocycle is regular" can hold.  The refutations are kept as theorems in
   `Examples/AffineSl2RigidityCollapse.lean` (`not_gradedImpliesRegular_L43`,
   `not_gradedImpliesPoleZero_L43`).
2. *Tautology.*  The repair `GradedRegularUpToCoboundary W := ∀ D graded, ∃ E graded regular,
   IsCoboundary W (D.Y1 - E.Y1)` removed the vacuity but was **uniformly derivable from its own
   conclusion**: given `IsRigidGraded W`, take `E = 0`.  That derivation uses nothing about `W`,
   and the resulting equivalence is a one-line proof.  A main theorem stated over it is bookkeeping.
   `GradedRegularUpToCoboundary`, `trivial_satisfies`,
   `gradedRegularUpToCoboundary_of_isRigidGraded`, `gradedRegularUpToCoboundary_iff_isRigidGraded`,
   `gradedRegularUpToCoboundary_of_grading_one_eq_bot` and `isRigidGraded_of_hypotheses` are
   not part of the library.

Neither defect was one of *encoding*: `Deform.FirstOrderDeformation.Regular` is a faithful
rendering of "no negative powers of `x`" (`regular_iff`), `Deform.IsGraded` is a faithful
rendering of order-`t` VA1, and — `smul₁` being bilinear — quantifying over all of `W.grading 1`
is equivalent to quantifying over the paper's generators `a(-1)𝟙, b(-1)𝟙`.  The first defect was
one of **generality**, the second of **content**.


⚠ **A second, independent over-generality, recorded but not repaired.**
`RegularImpliesTrivialGraded` (below) quantifies over an *arbitrary* VOA `W`, whereas Linshaw–Qi's
Theorem 3.1 assumes `V` is a **simple affine** VOA, strongly generated by `V₁`.  For any `W` with
`W.grading 1 = ⊥`, `Regular` holds vacuously, so the predicate asserts that every graded
deformation of such a `W` is trivial — morally false for the Virasoro VOA `V(c,0)`, whose
`∂/∂c` direction is not a gauge direction (`Examples/VirasoroCDeformation.lean` proves the
obstruction half, `not_isTrivial_of_isCDeformation`; it stops short of a refutation only because
`IsCDeformation c` is never inhabited there).  It is not refutable in this repository today, and
it is only ever instantiated at `L43`, where it should be true — but a faithful statement of
Theorem 3.1 would carry `W.IsSimple` and a "generated by `W.grading 1`" clause.

**`IsRigid` would be the wrong target.**  `Deform.IsRigid` quantifies over *all* first-order
deformations, graded or not, while `Deform.IsCoboundary` demands a grade-preserving `φ`.  The
repository already proves `NonzeroDeform.not_isRigid_virasoroVOA` by exhibiting
`l1Deformation = deltaCochain W (W.L 1)`, a legitimate ungraded deformation of *every* VOA that
`isGraded_of_isTrivial` then makes non-trivial.  The same construction applies here, so
`IsRigid (L₋₄⁄₃(𝔰𝔩₂))` is very likely **false** in this formalism.  Linshaw–Qi mean *graded*
deformations, so the target of the main theorem is `Deform.IsRigidGraded` (`isRigidGraded_of_split`).

## Axiom hygiene

No `sorry`, no `admit`, no `native_decide`, no new axioms — and, checked rather than assumed,
**no `VOA.pbw`**.  Every declaration listed above reports exactly

`[propext, Classical.choice, Quot.sound]`

under `#print axioms`.  The two places where `VOA.pbw` could have
crept in are avoided deliberately: `vacuum_ne_zero` routes through `Wak.vacuumA_ne_zero_free` rather
than `AffineVOA.vacuumA_ne_zero` (which is where `pbw` enters `AffineSl2VOAInstance`), and
`lqVector_ne_zero` / `maxGradedIdeal_ne_bot` route through `Wak.sl2Singular_ne_zero`, the
`pbw`-free Wakimoto nonvanishing proof.

The same holds of the companion certificate `Examples/AffineSl2RigidityCollapse.lean`, which
records — as theorems — that the stronger hypothesis `GradedImpliesRegular` is false.

## References
* A. R. Linshaw and F. Qi, *Deformation rigidity of some simple affine VOAs*,
  arXiv:2601.12017v2 (20 Aug 2026), §3, §5.
* D. Adamović, *A construction of admissible A₁⁽¹⁾-modules of level -4/3*,
  J. Pure Appl. Alg. **196** (2005) 119–134 — the singular vector.
* V. Kovalchuk and F. Qi, *First-order deformations of freely generated vertex algebras*,
  arXiv:2408.16309 — §4.1, §6.2, cited by Linshaw–Qi throughout §4–§5.
* B. H. Lian, *On the classification of simple vertex operator algebras*,
  Comm. Math. Phys. **163** (1994) 307–357 — cited for Theorem 4.11; see the caveat above.
-/

open scoped BigOperators
open Module (End)
open VOA VOA.AffineVOA VOA.AffineLie
open VOA.VertexOperatorAlgebra VOA.AffineVOA.Inst VOA.LiRadical

namespace VOA.LQ43

universe u

/-! ## §A  The linear-algebra core of Linshaw–Qi §5.3

Sixteen unknowns.  The fifteen structure constants `a₁…a₅, b₁…b₅, c₁…c₅` are the coordinates of
the three unknown weight-3 vectors

* `h^def(-1)e(-2)1  = a₁e₋₃1 + a₂e₋₂h₋₁1 + a₃e₋₁h₋₂1 + a₄e₋₁h₋₁²1 + a₅e₋₁²f₋₁1`,
* `h^def(-1)h(-1)e(-1)1 = b₁… `,
* `e^def(-1)e(-1)f(-1)1 = c₁… `,

and `c` is the single pole constant of `Y₁` on the weight-one space (the paper's equation (3)).
The five equations below are the components of `f^def(1)s = 0` and `h^def(1)s = 0`.

⚠ **Basis caution for anyone re-deriving these.**  The paper silently uses two different bases:
(10)–(12) are components in `{e₋₁f₋₁1, h₋₂1, h₋₁h₋₁1}`, but (13)–(14) are components in
`{h₋₁e₋₁1, e₋₂1}`, **not** `{e₋₁h₋₁1, e₋₂1}`.  Once matched by `h₋₁e₋₁1 = 2e₋₂1 + e₋₁h₋₁1`, all
of (11)–(14) agree to the last integer.  Nothing in the paper announces the switch.

The paper prints each equation as `0 = ⋯`; the fields below are the same equations written
`⋯ = 0`, which is what `linear_combination` consumes.
-/

/-- **Equations (10)–(14) of Linshaw–Qi §5.3, transcribed verbatim as printed.**

The constant term of `eq10` is `+12 * c`, exactly as printed in the paper.  It is arithmetically
wrong — see `CorrectedSystem` — but the conclusion `c = 0` survives either way, and formalising
the printed system is what lets `eq15`/`eq16` below reproduce the paper's own displays. -/
structure PrintedSystem (a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ c : ℂ) : Prop where
  /-- Equation (10), as printed. -/
  eq10 : 84 * a₃ + 168 * a₄ - 28 * a₅ - 18 * b₃ - 36 * b₄ + 6 * b₅
      - 72 * c₃ - 144 * c₄ + 24 * c₅ + 12 * c = 0
  /-- Equation (11). -/
  eq11 : -42 * a₂ - 56 * a₄ + 9 * b₂ + 12 * b₄ + 36 * c₂ + 48 * c₄ + 9 * c = 0
  /-- Equation (12). -/
  eq12 : -42 * a₁ - 56 * a₃ + 9 * b₁ + 12 * b₃ + 36 * c₁ + 48 * c₃ - 6 * c = 0
  /-- Equation (13). -/
  eq13 : 84 * a₂ - 560 * a₄ + 168 * a₅ - 18 * b₂ + 120 * b₄ - 36 * b₅
      - 72 * c₂ + 480 * c₄ - 144 * c₅ + 36 * c = 0
  /-- Equation (14). -/
  eq14 : 84 * a₁ - 280 * a₂ - 168 * a₃ + 784 * a₄ - 336 * a₅ - 18 * b₁ + 60 * b₂ + 36 * b₃
      - 168 * b₄ + 72 * b₅ - 72 * c₁ + 240 * c₂ + 144 * c₃ - 672 * c₄ + 288 * c₅ - 96 * c = 0

namespace PrintedSystem

variable {a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ c : ℂ}
variable (h : PrintedSystem a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ c)

include h

/-- **The paper's display (15), reproduced exactly.**  The stated operation
`(14) + 2(12) - (70·4/42)(11) + (280/84)(10)` eliminates `a₁, a₂, a₃` and yields
`(4/3)(1288a₄ - 322a₅ - 276b₄ + 69b₅ - 96c - 1104c₄ + 276c₅) = 0`.

Every printed coefficient, including the `-96c` that carries the erratum of (10), matches. -/
theorem eq15 : (4 / 3 : ℂ) * (1288 * a₄ - 322 * a₅ - 276 * b₄ + 69 * b₅ - 96 * c
    - 1104 * c₄ + 276 * c₅) = 0 := by
  linear_combination h.eq14 + 2 * h.eq12 - (70 * 4 / 42 : ℂ) * h.eq11 + (280 / 84 : ℂ) * h.eq10

/-- **The paper's display (16), reproduced exactly.**  The operation `(13) + 2(11)` eliminates
`a₂` and yields `-6(112a₄ - 28a₅ - 24b₄ + 6b₅ - 9c - 96c₄ + 24c₅) = 0`. -/
theorem eq16 : (-6 : ℂ) * (112 * a₄ - 28 * a₅ - 24 * b₄ + 6 * b₅ - 9 * c
    - 96 * c₄ + 24 * c₅) = 0 := by
  linear_combination h.eq13 + 2 * h.eq11

/-- **The paper's final elimination, reproduced exactly**: `(15) + (1288·4)/(112·6·3)·(16)`
gives `10c = 0`. -/
theorem ten_c_eq_zero : (10 : ℂ) * c = 0 := by
  linear_combination h.eq15 + (1288 * 4 / (112 * 6 * 3) : ℂ) * h.eq16

/-- **The conclusion of Linshaw–Qi §5.3 from the printed system: `c = 0`.** -/
theorem c_eq_zero : c = 0 := by
  have h10 := h.ten_c_eq_zero
  linear_combination h10 / 10

/-- **What the 5×16 system actually is.**

The fifteen structure constants enter only through the five combinations
`Pᵢ = 42aᵢ - 9bᵢ - 36cᵢ`, and the solution space is exactly `c = 0` together with
`(P₁,…,P₅) ∈ ℂ·(8, -12, -6, 9, 36)`.  In particular the system has rank 5, its kernel is
one-dimensional, and — by `sl2Singular_eq_lqBasis` — that kernel is precisely the line spanned
by the singular vector `s` in the paper's own basis.  The Gaussian elimination of §5.3 is a
16-column computation that is really a 6-column one. -/
theorem reduced : c = 0 ∧ ∃ lam : ℂ,
    42 * a₁ - 9 * b₁ - 36 * c₁ = 8 * lam ∧
    42 * a₂ - 9 * b₂ - 36 * c₂ = -12 * lam ∧
    42 * a₃ - 9 * b₃ - 36 * c₃ = -6 * lam ∧
    42 * a₄ - 9 * b₄ - 36 * c₄ = 9 * lam ∧
    42 * a₅ - 9 * b₅ - 36 * c₅ = 36 * lam := by
  have hc := h.c_eq_zero
  refine ⟨hc, (42 * a₅ - 9 * b₅ - 36 * c₅) / 36, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (3 : ℂ) * h.eq10 - (92 / 45 : ℂ) * h.eq11 + (6 / 5 : ℂ) * h.eq12
      + (119 / 45 : ℂ) * h.eq13 + (11 / 10 : ℂ) * h.eq14
  · linear_combination (3 / 2 : ℂ) * h.eq10 - (23 / 15 : ℂ) * h.eq11 + (9 / 10 : ℂ) * h.eq12
      + (37 / 30 : ℂ) * h.eq13 + (9 / 20 : ℂ) * h.eq14
  · linear_combination (-15 / 4 : ℂ) * h.eq10 + (67 / 30 : ℂ) * h.eq11 - (51 / 20 : ℂ) * h.eq12
      - (47 / 15 : ℂ) * h.eq13 - (51 / 40 : ℂ) * h.eq14
  · linear_combination (9 / 8 : ℂ) * h.eq10 - (13 / 20 : ℂ) * h.eq11 + (27 / 40 : ℂ) * h.eq12
      + (4 / 5 : ℂ) * h.eq13 + (27 / 80 : ℂ) * h.eq14
  · ring

/-- **The one-line certificate.**  The Gaussian elimination of §5.3 is unnecessary: the
covector `λ = (30, -14, 18, 23, 9)` annihilates all fifteen `aᵢ/bᵢ/cᵢ` columns of (10)–(14)
simultaneously, so `λ · (10,…,14)` is a single scalar equation in `c` alone.  For the *printed*
system its value is `90 c = 0`.

`λ` is the (one-dimensional) left null space of the 5×15 coefficient matrix, and it does not
depend on which version of (10) is used — only the resulting multiple of `c` does. -/
theorem ninety_c_eq_zero : (90 : ℂ) * c = 0 := by
  linear_combination 30 * h.eq10 - 14 * h.eq11 + 18 * h.eq12 + 23 * h.eq13 + 9 * h.eq14

end PrintedSystem

/-- **Equations (10)–(14) with the erratum in (10) repaired.**

Only `eq10` differs from `PrintedSystem`: its constant term is `+72 * c`, not `+12 * c`.  The
correct value is forced by the paper's own §5.1 display, which reads `+ 72c · e(-1)f(-1)1`; the
transcription slip happened between §5.1 and equation (10).  All fifteen `aᵢ/bᵢ/cᵢ`
coefficients are unchanged, because they are all correct as printed. -/
structure CorrectedSystem (a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ c : ℂ) : Prop where
  /-- Equation (10), with the constant term corrected from `+12c` to `+72c`. -/
  eq10 : 84 * a₃ + 168 * a₄ - 28 * a₅ - 18 * b₃ - 36 * b₄ + 6 * b₅
      - 72 * c₃ - 144 * c₄ + 24 * c₅ + 72 * c = 0
  /-- Equation (11). -/
  eq11 : -42 * a₂ - 56 * a₄ + 9 * b₂ + 12 * b₄ + 36 * c₂ + 48 * c₄ + 9 * c = 0
  /-- Equation (12). -/
  eq12 : -42 * a₁ - 56 * a₃ + 9 * b₁ + 12 * b₃ + 36 * c₁ + 48 * c₃ - 6 * c = 0
  /-- Equation (13). -/
  eq13 : 84 * a₂ - 560 * a₄ + 168 * a₅ - 18 * b₂ + 120 * b₄ - 36 * b₅
      - 72 * c₂ + 480 * c₄ - 144 * c₅ + 36 * c = 0
  /-- Equation (14). -/
  eq14 : 84 * a₁ - 280 * a₂ - 168 * a₃ + 784 * a₄ - 336 * a₅ - 18 * b₁ + 60 * b₂ + 36 * b₃
      - 168 * b₄ + 72 * b₅ - 72 * c₁ + 240 * c₂ + 144 * c₃ - 672 * c₄ + 288 * c₅ - 96 * c = 0

namespace CorrectedSystem

variable {a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ c : ℂ}
variable (h : CorrectedSystem a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ c)

include h

/-- **Display (15) with the erratum repaired.**  The same elimination
`(14) + 2(12) - (70·4/42)(11) + (280/84)(10)` gives constant term `+72c` in place of the
printed `(4/3)·(-96c) = -128c`; every other coefficient is unchanged. -/
theorem eq15 : (4 / 3 : ℂ) * (1288 * a₄ - 322 * a₅ - 276 * b₄ + 69 * b₅
    - 1104 * c₄ + 276 * c₅) + 72 * c = 0 := by
  linear_combination h.eq14 + 2 * h.eq12 - (70 * 4 / 42 : ℂ) * h.eq11 + (280 / 84 : ℂ) * h.eq10

/-- Display (16) is unaffected by the erratum: `(13) + 2(11)` does not involve (10). -/
theorem eq16 : (-6 : ℂ) * (112 * a₄ - 28 * a₅ - 24 * b₄ + 6 * b₅ - 9 * c
    - 96 * c₄ + 24 * c₅) = 0 := by
  linear_combination h.eq13 + 2 * h.eq11

/-- **The final elimination with the erratum repaired**: `(15) + (23/9)(16)` gives `210c = 0`,
where the printed version gives the cleaner-looking `10c = 0`.  The two systems in fact span the
same row space (their difference is `60c`), so this is a cosmetic change only. -/
theorem twoTen_c_eq_zero : (210 : ℂ) * c = 0 := by
  linear_combination h.eq15 + (1288 * 4 / (112 * 6 * 3) : ℂ) * h.eq16

/-- **`c = 0` from the corrected system** — the conclusion is unaffected by the erratum. -/
theorem c_eq_zero : c = 0 := by
  have h210 := h.twoTen_c_eq_zero
  linear_combination h210 / 210

/-- The reduced description of the corrected system: identical to `PrintedSystem.reduced`.
The two systems have the same solution set. -/
theorem reduced : c = 0 ∧ ∃ lam : ℂ,
    42 * a₁ - 9 * b₁ - 36 * c₁ = 8 * lam ∧
    42 * a₂ - 9 * b₂ - 36 * c₂ = -12 * lam ∧
    42 * a₃ - 9 * b₃ - 36 * c₃ = -6 * lam ∧
    42 * a₄ - 9 * b₄ - 36 * c₄ = 9 * lam ∧
    42 * a₅ - 9 * b₅ - 36 * c₅ = 36 * lam := by
  have hc := h.c_eq_zero
  refine ⟨hc, (42 * a₅ - 9 * b₅ - 36 * c₅) / 36, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (1 / 7 : ℂ) * h.eq10 - (32 / 45 : ℂ) * h.eq11 - (18 / 35 : ℂ) * h.eq12
      + (143 / 315 : ℂ) * h.eq13 + (17 / 70 : ℂ) * h.eq14
  · linear_combination (1 / 14 : ℂ) * h.eq10 - (13 / 15 : ℂ) * h.eq11 + (3 / 70 : ℂ) * h.eq12
      + (29 / 210 : ℂ) * h.eq13 + (3 / 140 : ℂ) * h.eq14
  · linear_combination (-5 / 28 : ℂ) * h.eq10 + (17 / 30 : ℂ) * h.eq11 - (57 / 140 : ℂ) * h.eq12
      - (83 / 210 : ℂ) * h.eq13 - (57 / 280 : ℂ) * h.eq14
  · linear_combination (3 / 56 : ℂ) * h.eq10 - (3 / 20 : ℂ) * h.eq11 + (9 / 280 : ℂ) * h.eq12
      - (3 / 140 : ℂ) * h.eq13 + (9 / 560 : ℂ) * h.eq14
  · ring

/-- **The one-line certificate, corrected system.**  The same covector
`λ = (30, -14, 18, 23, 9)` — the left null space of the 5×15 matrix of `aᵢ/bᵢ/cᵢ` coefficients,
which the erratum does not touch — turns (10)–(14) into `1890 c = 0` in a single
`linear_combination`.  This replaces the paper's five-step elimination through displays (15) and
(16) entirely; those are kept above only because reproducing them is what audits the paper.

Check of the certificate: `λ · (72, 9, -6, 36, -96) = 2160 - 126 - 108 + 828 - 864 = 1890`, and
against the printed constants `(12, 9, -6, 36, -96)` it gives `90`
(`PrintedSystem.ninety_c_eq_zero`). -/
theorem c_eq_zero_certificate : (1890 : ℂ) * c = 0 := by
  linear_combination 30 * h.eq10 - 14 * h.eq11 + 18 * h.eq12 + 23 * h.eq13 + 9 * h.eq14

/-- `c = 0` again, this time by the one-line certificate rather than by the paper's elimination.
Recorded so that the conclusion has two independent proofs in the file. -/
theorem c_eq_zero' : c = 0 := by
  have hcert := h.c_eq_zero_certificate
  linear_combination hcert / 1890

end CorrectedSystem

/-- The two systems agree except in the constant term of (10); the corrected one implies the
printed one exactly when `c = 0`, which both force.  Recorded so that neither version has
special standing. -/
theorem printed_iff_corrected {a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ c : ℂ} :
    PrintedSystem a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ c
      ↔ CorrectedSystem a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ c := by
  constructor
  · intro h
    have hc := h.c_eq_zero
    exact ⟨by linear_combination h.eq10 + 60 * hc, h.eq11, h.eq12, h.eq13, h.eq14⟩
  · intro h
    have hc := h.c_eq_zero
    exact ⟨by linear_combination h.eq10 - 60 * hc, h.eq11, h.eq12, h.eq13, h.eq14⟩

/-! ## §A″  Section 5.3 in six unknowns — the form a formalisation should actually target

The fifteen structure constants occur in (10)–(14) *only* through the five combinations

`Pᵢ = 42 aᵢ - 9 bᵢ - 36 cᵢ`,

so the paper's "five equations in sixteen unknowns" is five equations in **six**.  Written in
those coordinates the corrected system is

* (10) `2P₃ + 4P₄ - (2/3)P₅ + 72c = 0`
* (11) `-P₂ - (4/3)P₄ + 9c = 0`
* (12) `-P₁ - (4/3)P₃ - 6c = 0`
* (13) `2P₂ - (40/3)P₄ + 4P₅ + 36c = 0`
* (14) `2P₁ - (20/3)P₂ - 4P₃ + (56/3)P₄ - 8P₅ - 96c = 0`

and the left null covector `λ = (30, -14, 18, 23, 9)` annihilates the `P`-block, leaving
`1890 c = 0`.  When the §5 bridge is eventually built, this — not the 5×16 array — is the shape
to aim the deformation-theoretic input at: it needs only the three vectors
`A = h^def(-1)e(-2)1`, `B = h^def(-1)h(-1)e(-1)1`, `C = e^def(-1)e(-1)f(-1)1` through the single
combination `P = 42A - 9B - 36C`.
-/

/-- **§5.3, stated in the six unknowns it really has.**  Each hypothesis is the corresponding
equation of `CorrectedSystem` rewritten in the coordinates `Pᵢ = 42aᵢ - 9bᵢ - 36cᵢ`; the proof is
the single covector `λ = (30, -14, 18, 23, 9)`. -/
theorem pSystem_c_eq_zero {P₁ P₂ P₃ P₄ P₅ c : ℂ}
    (e10 : 2 * P₃ + 4 * P₄ - (2 / 3) * P₅ + 72 * c = 0)
    (e11 : -P₂ - (4 / 3) * P₄ + 9 * c = 0)
    (e12 : -P₁ - (4 / 3) * P₃ - 6 * c = 0)
    (e13 : 2 * P₂ - (40 / 3) * P₄ + 4 * P₅ + 36 * c = 0)
    (e14 : 2 * P₁ - (20 / 3) * P₂ - 4 * P₃ + (56 / 3) * P₄ - 8 * P₅ - 96 * c = 0) :
    c = 0 := by
  have hcert : (1890 : ℂ) * c = 0 := by
    linear_combination 30 * e10 - 14 * e11 + 18 * e12 + 23 * e13 + 9 * e14
  linear_combination hcert / 1890

/-- The corrected 5×16 system really *is* the 5×6 system above: each equation (10)–(14) is the
displayed `P`-equation, with `Pᵢ := 42aᵢ - 9bᵢ - 36cᵢ`.  Together with `pSystem_c_eq_zero` this
gives a third, coordinate-free proof of `c = 0`. -/
theorem CorrectedSystem.pForm {a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ c : ℂ}
    (h : CorrectedSystem a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₃ b₄ b₅ c₁ c₂ c₃ c₄ c₅ c) :
    ∀ P₁ P₂ P₃ P₄ P₅ : ℂ,
      P₁ = 42 * a₁ - 9 * b₁ - 36 * c₁ → P₂ = 42 * a₂ - 9 * b₂ - 36 * c₂ →
      P₃ = 42 * a₃ - 9 * b₃ - 36 * c₃ → P₄ = 42 * a₄ - 9 * b₄ - 36 * c₄ →
      P₅ = 42 * a₅ - 9 * b₅ - 36 * c₅ →
      (2 * P₃ + 4 * P₄ - (2 / 3) * P₅ + 72 * c = 0) ∧
      (-P₂ - (4 / 3) * P₄ + 9 * c = 0) ∧
      (-P₁ - (4 / 3) * P₃ - 6 * c = 0) ∧
      (2 * P₂ - (40 / 3) * P₄ + 4 * P₅ + 36 * c = 0) ∧
      (2 * P₁ - (20 / 3) * P₂ - 4 * P₃ + (56 / 3) * P₄ - 8 * P₅ - 96 * c = 0) := by
  rintro P₁ P₂ P₃ P₄ P₅ rfl rfl rfl rfl rfl
  exact ⟨by linear_combination h.eq10, by linear_combination h.eq11, by linear_combination h.eq12,
    by linear_combination h.eq13, by linear_combination h.eq14⟩

/-! ## §B  The Linshaw–Qi singular vector equals the repository's `sl2Singular`

Linshaw–Qi §5 writes the weight-3 singular vector of `V^{-4/3}(𝔰𝔩₂)` as

`s = -48 h₋₁e₋₂1 + 36 e₋₁²f₋₁1 - 6 h₋₂e₋₁1 + 9 h₋₁²e₋₁1 + 80 e₋₃1`,

which is *not* normally ordered: `h₋₁e₋₂1` and `h₋₁²e₋₁1` both have the Cartan generator on the
left.  The repository derives its own vector from scratch (`Sl2Sing.exists_nonzero_solution_iff`
forces the level `k = -4/3`) in the normally-ordered basis
`M₁ = e₋₃1, M₂ = e₋₂h₋₁1, M₃ = h₋₂e₋₁1, M₄ = e₋₁²f₋₁1, M₅ = e₋₁h₋₁²1`.  The two agree.
-/

/-- `h₋₁e₋₂|0⟩`, the first non-normally-ordered monomial of Linshaw–Qi §5. -/
noncomputable def N1 (k : ℂ) : WakModule k := J k colH (-1) (J k colE (-2) (vacuumA k))

/-- `h₋₁h₋₁e₋₁|0⟩`, the second non-normally-ordered monomial of Linshaw–Qi §5. -/
noncomputable def N2 (k : ℂ) : WakModule k :=
  J k colH (-1) (J k colH (-1) (J k colE (-1) (vacuumA k)))

/-- `e₋₁h₋₂|0⟩` — the third basis vector of the paper's §5.3 parameterisation.  Note it is
`e₋₁h₋₂1`, **not** the repository's `M₃ = h₋₂e₋₁1`. -/
noncomputable def N3 (k : ℂ) : WakModule k := J k colE (-1) (J k colH (-2) (vacuumA k))

/-- Expand the first ordered current word: apply the e mode of index −2 to the vacuum, then the h
mode of index −1. The order matters because current operators do not commute. -/
theorem N1_def (k : ℂ) : N1 k = J k colH (-1) (J k colE (-2) (vacuumA k)) := rfl
/-- Expand the second ordered word: apply e at index −1, then h at index −1 twice. Its total weight
is three. -/
theorem N2_def (k : ℂ) :
    N2 k = J k colH (-1) (J k colH (-1) (J k colE (-1) (vacuumA k))) := rfl
/-- Expand the third ordered word: apply h at index −2 before e at index −1. Reversing these
operators would add a commutator term. -/
theorem N3_def (k : ℂ) : N3 k = J k colE (-1) (J k colH (-2) (vacuumA k)) := rfl

/-- **Reordering, first identity**: `h₋₁e₋₂|0⟩ = e₋₂h₋₁|0⟩ + 2 e₋₃|0⟩`, i.e. `N₁ = M₂ + 2M₁`.
This is `⁅h₋₁, e₋₂⁆ = 2e₋₃` applied to the vacuum. -/
theorem N1_eq (k : ℂ) : N1 k = Sl2Sing.M2 k + (2 : ℂ) • Sl2Sing.M1 k := by
  rw [N1_def, Sl2Sing.HEs k (-1) (-2) (-3) (by norm_num), Sl2Sing.M2_def, Sl2Sing.M1_def]

/-- **Reordering, second identity**: `h₋₁h₋₁e₋₁|0⟩ = e₋₁h₋₁h₋₁|0⟩ + 4 e₋₂h₋₁|0⟩ + 4 e₋₃|0⟩`,
i.e. `N₂ = M₅ + 4M₂ + 4M₁`.  Apply `⁅h₋₁, e₋₁⁆ = 2e₋₂` twice and then `⁅h₋₁, e₋₂⁆ = 2e₋₃`.

**This is the identity that `Examples/AffineSl2Singular.lean` §D overlooks.** -/
theorem N2_eq (k : ℂ) :
    N2 k = Sl2Sing.M5 k + (4 : ℂ) • Sl2Sing.M2 k + (4 : ℂ) • Sl2Sing.M1 k := by
  have hin : J k colH (-1) (J k colE (-1) (vacuumA k))
      = J k colE (-1) (J k colH (-1) (vacuumA k)) + (2 : ℂ) • J k colE (-2) (vacuumA k) :=
    Sl2Sing.Hm1Em1 k
  have hmid : J k colH (-1) (J k colE (-1) (J k colH (-1) (vacuumA k)))
      = J k colE (-1) (J k colH (-1) (J k colH (-1) (vacuumA k)))
        + (2 : ℂ) • J k colE (-2) (J k colH (-1) (vacuumA k)) :=
    Sl2Sing.HEs k (-1) (-1) (-2) (by norm_num) _
  rw [N2_def, hin, map_add, map_smul, hmid, ← N1_def, N1_eq k,
    Sl2Sing.M5_def, Sl2Sing.M2_def, Sl2Sing.M1_def]
  module

/-- **Reordering, third identity**: `e₋₁h₋₂|0⟩ = h₋₂e₋₁|0⟩ - 2 e₋₃|0⟩`, i.e. `N₃ = M₃ - 2M₁`.
Needed to place the paper's §5.3 parameterisation basis against the repository's. -/
theorem N3_eq (k : ℂ) : N3 k = Sl2Sing.M3 k - (2 : ℂ) • Sl2Sing.M1 k := by
  rw [N3_def, Sl2Sing.EHs k (-1) (-2) (-3) (by norm_num), Sl2Sing.M3_def, Sl2Sing.M1_def]

/-- **The Linshaw–Qi vector**, written exactly as in the paper:
`-48 h₋₁e₋₂1 + 36 e₋₁²f₋₁1 - 6 h₋₂e₋₁1 + 9 h₋₁²e₋₁1 + 80 e₋₃1`. -/
noncomputable def lqVector (k : ℂ) : WakModule k :=
  (-48 : ℂ) • N1 k + (36 : ℂ) • Sl2Sing.M4 k + (-6 : ℂ) • Sl2Sing.M3 k
    + (9 : ℂ) • N2 k + (80 : ℂ) • Sl2Sing.M1 k

/-- Expose the five terms and coefficients of the proposed singular vector before reordering. Later
comparison with the repository normal order uses current commutators; this equality itself only
unfolds the definition. -/
theorem lqVector_def (k : ℂ) :
    lqVector k = (-48 : ℂ) • N1 k + (36 : ℂ) • Sl2Sing.M4 k + (-6 : ℂ) • Sl2Sing.M3 k
      + (9 : ℂ) • N2 k + (80 : ℂ) • Sl2Sing.M1 k := rfl

/-- **The identification.**  At every level `k`, the Linshaw–Qi vector normally-orders to
`20 M₁ - 12 M₂ - 6 M₃ + 36 M₄ + 9 M₅`, i.e. to the repository's `Sl2Sing.ansatz k 20 (-12) (-6)
36 9`.

Coefficient bookkeeping: `M₁ : 80 - 2·48 + 4·9 = 20` and `M₂ : -48 + 4·9 = -12`.  The `+4·9`
contributions come from `N₂ = M₅ + 4M₂ + 4M₁` and are exactly what
`Examples/AffineSl2Singular.lean` §D forgets. -/
theorem lqVector_eq_ansatz (k : ℂ) :
    lqVector k = Sl2Sing.ansatz k 20 (-12) (-6) 36 9 := by
  rw [lqVector_def, N1_eq, N2_eq, Sl2Sing.ansatz_def]
  module

/-- **At `k = -4/3` the Linshaw–Qi vector is literally `Sl2Sing.sl2Singular`.**

So the repository's independently derived singular vector and the one quoted from Adamović in
Linshaw–Qi §5 are the same element of `WakModule (-4/3)`, and the port of §5 is not built on a
mismatched vector. -/
theorem lqVector_eq_sl2Singular : lqVector (-4 / 3 : ℂ) = Sl2Sing.sl2Singular := by
  rw [lqVector_eq_ansatz, Sl2Sing.sl2Singular_def]

/-- The Linshaw–Qi vector is nonzero — inherited from `Wak.sl2Singular_ne_zero`, which the
repository proves unconditionally and `pbw`-free via the Wakimoto free-field realisation.
Without this the identification would be compatible with everything being `0`. -/
theorem lqVector_ne_zero : lqVector (-4 / 3 : ℂ) ≠ 0 := by
  rw [lqVector_eq_sl2Singular]; exact Wak.sl2Singular_ne_zero

/-- The Linshaw–Qi vector is annihilated by every positive mode of every current — the
singularity property that Linshaw–Qi §5 uses when it sets `f^def(1)s` and `h^def(1)s` to zero. -/
theorem lqVector_pos (a : Fin 3) {m : ℤ} (hm : 1 ≤ m) :
    J (-4 / 3 : ℂ) a m (lqVector (-4 / 3 : ℂ)) = 0 := by
  rw [lqVector_eq_sl2Singular]; exact Sl2Sing.sl2Singular_pos a hm

/-- **The kernel of the paper's own 5×16 system is the line through `s`.**

`PrintedSystem.reduced` says the solution space is `c = 0` together with
`(P₁,…,P₅) ∈ ℂ·(8, -12, -6, 9, 36)`.  Those five integers are exactly the coordinates of the
singular vector in the paper's *own* parameterisation basis
`{e₋₃1, e₋₂h₋₁1, e₋₁h₋₂1, e₋₁h₋₁²1, e₋₁²f₋₁1} = {M₁, M₂, N₃, M₅, M₄}`:

`s = 8 M₁ - 12 M₂ - 6 N₃ + 9 M₅ + 36 M₄`.

(The difference from `20 M₁ - 12 M₂ - 6 M₃ + 36 M₄ + 9 M₅` is only `N₃ = M₃ - 2M₁`.)  So the
one-dimensional kernel that §5.3's Gaussian elimination silently produces is not an accident:
it is the singular vector itself, and any transcription error in (10)–(14) would generically
destroy it. -/
theorem sl2Singular_eq_lqBasis :
    Sl2Sing.sl2Singular
      = (8 : ℂ) • Sl2Sing.M1 (-4 / 3 : ℂ) + (-12 : ℂ) • Sl2Sing.M2 (-4 / 3 : ℂ)
        + (-6 : ℂ) • N3 (-4 / 3 : ℂ) + (9 : ℂ) • Sl2Sing.M5 (-4 / 3 : ℂ)
        + (36 : ℂ) • Sl2Sing.M4 (-4 / 3 : ℂ) := by
  rw [N3_eq, Sl2Sing.sl2Singular_def, Sl2Sing.ansatz_def]
  module

/-! ## §C  `L₋₄⁄₃(𝔰𝔩₂)` exists as a proper simple quotient — a repository gap closed

`Examples/AffineSl2Singular.lean` §E3 records "the ideal / `L₋₄⁄₃(𝔰𝔩₂) ≠ V^{-4/3}(𝔰𝔩₂)`: **out of
reach** without PBW independence", and the free-field route to it fails structurally (Wakimoto
modules are irreducible, so the free-field functional cannot detect properness).  That
assessment is too pessimistic: Li's theorem, already in the repository as
`LiRadical.rightRadical_eq_maxGradedIdeal`, gives it in one peel of the mode, with no PBW basis
and no strong-singularity hypothesis.

The argument in three steps.

1. **Weight-one adjointness** (`weightOne_adj`).  For `u ∈ 𝒱₁` with `L₁u = 0`, the
   fully-invariant identity collapses to its single `j = 0` term:
   `(u₍ₙ₎a | b) = -(a | u₍₋ₙ₎b)`.  Three lines, and the most load-bearing lemma below.
2. **`L₁𝒱₁ = 0`** (`L1_grading_one`).  `gradingZA_le_hspan k 1` says every weight-one vector is a
   combination of word states of degree 1, and a word of degree 1 is a single current
   (`wordDegA_eq_one`); `Vir.current_primary` kills those.  This discharges the standing
   hypothesis `hqp` of `canonicalInvariantForm` for the affine `𝔰𝔩₂` VOA — flagged as step 2 of
   the recipe in `Examples/AffineSimpleQuotient.lean` §4 and not done there.
3. **One peel.**  Every weight-3 vector is a combination of word states `J^a₍₋ₘ₎y′` with `m ≥ 1`;
   adjointness turns `(J^a₍₋ₘ₎y′ | s)` into `-(y′ | J^a₍ₘ₎s) = 0` by `Sl2Sing.sl2Singular_pos`.
   Weights other than 3 are orthogonal to `s` for free.  So `s` is in the right radical, hence
   in `maxGradedIdeal` by Li.

This deliberately **bypasses** `SingVec.IsStronglySingularOfWeight`, whose `annihilated` field
(quantified over *all* homogeneous `u`) is the "second real work item" that
`Examples/AffineSimpleQuotient.lean` §4 flags; it is not needed.
-/

/-- **Weight-one adjointness.**  For `u` of conformal weight `1` with `L₁u = 0`, full invariance
`(u₍ₙ₎a|b) = (-1)^{wt} ∑_{j ≤ wt} (1/j!)((L₁ʲu)₍₂wt-n-2-j₎a|b)` has only its `j = 0` term, and
reads `(u₍ₙ₎a|b) = -(a|u₍₋ₙ₎b)`.

This is the whole of §C's mechanism, and it is exactly the identity Linshaw–Qi's Theorem 3.1
would need in order to replace the citation to [L, Thm 4.11]. -/
theorem weightOne_adj {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    {W : VertexOperatorAlgebra 𝒱} {B : InvariantForm W}
    (hB : B.IsFullyInvariant) {u : 𝒱} (hu : u ∈ W.grading 1) (hu1 : W.L 1 u = 0)
    (n : ℤ) (a b : 𝒱) :
    B.form (W.smul u n a) b = - B.form a (W.smul u (-n) b) := by
  have h := hB 1 u hu n a b
  rw [show ((1 : ℤ)).toNat + 1 = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one] at h
  simp only [pow_zero, pow_one, Module.End.one_apply, hu1,
    PreVertexAlgebra.smul_zero_left, map_zero, smul_zero, add_zero, Nat.factorial_zero,
    Nat.cast_one, inv_one, one_smul] at h
  rw [h, show (2 * (1 : ℤ) - n - 2 - (0 : ℕ)) = -n from by push_cast; ring]
  simp [zpow_one]

/-! ### Word degrees -/

/-- Creation words have non-negative degree. -/
theorem wordDegA_nonneg : ∀ l : List (Fin 3 × ℕ), 0 ≤ wordDegA l
  | [] => le_of_eq rfl
  | (ai :: rest) => by
      rw [wordDegA_cons]
      have := wordDegA_nonneg rest
      have h2 : (0 : ℤ) ≤ (ai.2 : ℤ) := Int.natCast_nonneg _
      omega

/-- The only creation word of degree `0` is the empty one. -/
theorem wordDegA_eq_nil_of_zero : ∀ {l : List (Fin 3 × ℕ)}, wordDegA l = 0 → l = []
  | [], _ => rfl
  | (ai :: rest), h => by
      rw [wordDegA_cons] at h
      have := wordDegA_nonneg rest
      have h2 : (0 : ℤ) ≤ (ai.2 : ℤ) := Int.natCast_nonneg _
      omega

/-- The creation words of degree `1` are exactly the single currents `J^a₍₋₁₎|0⟩`. -/
theorem wordDegA_eq_one : ∀ {l : List (Fin 3 × ℕ)}, wordDegA l = 1 → ∃ a : Fin 3, l = [(a, 0)]
  | [], h => by rw [wordDegA_nil] at h; exact absurd h (by norm_num)
  | (ai :: rest), h => by
      rw [wordDegA_cons] at h
      have hr := wordDegA_nonneg rest
      have h2 : (0 : ℤ) ≤ (ai.2 : ℤ) := Int.natCast_nonneg _
      have hn : (ai.2 : ℤ) = 0 := by omega
      have hrest : wordDegA rest = 0 := by omega
      refine ⟨ai.1, ?_⟩
      rw [wordDegA_eq_nil_of_zero hrest]
      have hz : ai.2 = 0 := by exact_mod_cast hn
      rw [← hz]

/-! ### `L₁` kills the weight-one subspace -/

/-- `ω₍₂₎` kills the degree-1 word span: a degree-1 word is a single current, and currents are
weight-1 primaries (`Vir.current_primary`). -/
theorem omega2_hspan_one (k : ℂ) (hk : k + 2 ≠ 0) {v : WakModule k} (hv : v ∈ HSpan k 1) :
    mode (YA k hk (omegaA k)) 2 v = 0 := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hl, rfl⟩ := hz
      obtain ⟨a, rfl⟩ := wordDegA_eq_one hl
      rw [wordStateA_cons, wordStateA_nil]
      exact_mod_cast Vir.current_primary k hk a
  | zero => rw [map_zero]
  | add x y _ _ ihx ihy => rw [map_add, ihx, ihy, add_zero]
  | smul c x _ ihx => rw [map_smul, ihx, smul_zero]

/-- **`L₁𝒱₁ = 0` for the affine `𝔰𝔩₂` VOA at any non-critical level.**  This is the standing
hypothesis `hqp` of `canonicalInvariantForm`, and it is what makes the canonical invariant form
available for `V^k(𝔰𝔩₂)` at all. -/
theorem L1_grading_one (k : ℂ) (hk : k + 2 ≠ 0) (v : WakModule k)
    (hv : v ∈ (affineSl2VOA_closed k hk).grading 1) :
    (affineSl2VOA_closed k hk).L 1 v = 0 := by
  have hL : (affineSl2VOA_closed k hk).L 1 = mode (YA k hk (omegaA k)) 2 := by
    rw [VertexOperatorAlgebra.L_def, closed_Y, closed_conformalVector]
    norm_num
  rw [closed_grading] at hv
  rw [hL]
  exact omega2_hspan_one k hk (gradingZA_le_hspan k 1 hv)

/-! ### The canonical invariant form of `V^{-4/3}(𝔰𝔩₂)` -/

/-- The vacuum of `V^{-4/3}(𝔰𝔩₂)` is nonzero.  Routed through `Wak.vacuumA_ne_zero_free`, the
`pbw`-free Wakimoto re-proof, rather than through `AffineVOA.vacuumA_ne_zero`, which uses
the theorem `VOA.pbw`. -/
theorem vacuum_ne_zero : voaSl2Adm.vacuum ≠ 0 := by
  rw [voaSl2Adm_vacuum]; exact Wak.vacuumA_ne_zero_free (-4 / 3 : ℂ) (by norm_num)

/-- `L₁` kills the weight-one subspace of `V^{-4/3}(𝔰𝔩₂)`. -/
theorem quasiPrimary : ∀ v, v ∈ voaSl2Adm.grading 1 → voaSl2Adm.L 1 v = 0 :=
  fun v hv => L1_grading_one (-4 / 3 : ℂ) admLevel_noncritical v hv

/-- The canonical invariant form of `V^{-4/3}(𝔰𝔩₂)` — unconditionally fully invariant and
normalised, by `Core.InvariantFormFHL2`, using `vacuum_ne_zero` and `quasiPrimary`. -/
noncomputable def formAdm : InvariantForm voaSl2Adm := canonicalInvariantForm vacuum_ne_zero
  quasiPrimary

/-- The VOA mode of a current state is the affine current mode, at `k = -4/3`. -/
theorem smul_currentState_adm (a : Fin 3) (n : ℤ) (v : WakModule (-4 / 3 : ℂ)) :
    voaSl2Adm.smul (currentState (-4 / 3 : ℂ) a) n v = J (-4 / 3 : ℂ) a n v :=
  smul_currentState_eq_J (-4 / 3 : ℂ) admLevel_noncritical a n v

/-- The explicit affine singular vector has weight three. Each monomial in its defining combination
has the same total creation energy, so the whole combination belongs to that homogeneous space. -/
theorem sl2Singular_mem_grading3 : Sl2Sing.sl2Singular ∈ voaSl2Adm.grading 3 := by
  change Sl2Sing.sl2Singular ∈ gradingZA (-4 / 3 : ℂ) 3
  exact Sl2Sing.ansatz_mem _ _ _ _ _ _

/-- **The one peel.**  A creation word of degree `3` is nonempty, so it is `J^a₍₋ₘ₎y′` with
`m ≥ 1`; adjointness moves the mode across the form, and `Sl2Sing.sl2Singular_pos` kills it. -/
theorem form_wordState_sl2Singular : ∀ l : List (Fin 3 × ℕ), wordDegA l = 3 →
    formAdm.form (wordStateA (-4 / 3 : ℂ) l) Sl2Sing.sl2Singular = 0
  | [], h => by rw [wordDegA_nil] at h; exact absurd h (by norm_num)
  | (ai :: rest), _ => by
      change (canonicalInvariantForm vacuum_ne_zero quasiPrimary).form _ _ = 0
      rw [wordStateA_cons,
        show J (-4 / 3 : ℂ) ai.1 (-(ai.2 : ℤ) - 1) (wordStateA (-4 / 3 : ℂ) rest)
          = voaSl2Adm.smul (currentState (-4 / 3 : ℂ) ai.1) (-(ai.2 : ℤ) - 1)
              (wordStateA (-4 / 3 : ℂ) rest) from (smul_currentState_adm ai.1 _ _).symm,
        weightOne_adj (canonicalInvariantForm_isFullyInvariant vacuum_ne_zero quasiPrimary)
          (currentState_mem_grading (-4 / 3 : ℂ) admLevel_noncritical ai.1)
          (quasiPrimary _ (currentState_mem_grading (-4 / 3 : ℂ) admLevel_noncritical ai.1)),
        show -(-(ai.2 : ℤ) - 1) = (ai.2 : ℤ) + 1 from by ring,
        smul_currentState_adm,
        Sl2Sing.sl2Singular_pos ai.1 (by omega), map_zero, neg_zero]

/-- The singular vector pairs to zero with every linear combination of weight-three current words.
Orthogonality for individual words has already been proved by moving a creation mode across the
invariant form and using positive-mode annihilation; bilinearity extends it to their span. -/
theorem form_hspan3_sl2Singular {v : WakModule (-4 / 3 : ℂ)} (hv : v ∈ HSpan (-4 / 3 : ℂ) 3) :
    formAdm.form v Sl2Sing.sl2Singular = 0 := by
  induction hv using Submodule.span_induction with
  | mem z hz => obtain ⟨l, hl, rfl⟩ := hz; exact form_wordState_sl2Singular l hl
  | zero => rw [map_zero, LinearMap.zero_apply]
  | add x y _ _ ihx ihy => rw [map_add, LinearMap.add_apply, ihx, ihy, add_zero]
  | smul c x _ ihx => rw [map_smul, LinearMap.smul_apply, ihx, smul_zero]

/-- The singular vector is orthogonal to *everything*: to weight-3 vectors by the peel above,
to every other weight for free by `InvariantForm.orthogonal_of_ne`. -/
theorem sl2Singular_mem_rightRadical :
    Sl2Sing.sl2Singular ∈ SingVec.rightRadical formAdm := by
  rw [SingVec.mem_rightRadical]
  intro x
  have hxtop : x ∈ ⨆ i : ℤ, voaSl2Adm.grading i := by
    rw [voaSl2Adm.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction voaSl2Adm.grading
    (motive := fun x => formAdm.form x Sl2Sing.sl2Singular = 0) hxtop ?_ ?_ ?_
  · intro q y hy
    by_cases hq : q = 3
    · subst hq
      exact form_hspan3_sl2Singular (gradingZA_le_hspan (-4 / 3 : ℂ) 3 hy)
    · exact InvariantForm.orthogonal_of_ne formAdm hq hy sl2Singular_mem_grading3
  · change (formAdm.form 0) Sl2Sing.sl2Singular = 0
    rw [map_zero, LinearMap.zero_apply]
  · intro y y' hy hy'
    change (formAdm.form (y + y')) Sl2Sing.sl2Singular = 0
    rw [map_add, LinearMap.add_apply, hy, hy', add_zero]

/-- **The singular vector lies in the maximal proper graded ideal of `V^{-4/3}(𝔰𝔩₂)`.**
Li's theorem (`LiRadical.rightRadical_eq_maxGradedIdeal`) converts the orthogonality above into
ideal membership.  This is the repository gap that `Examples/AffineSl2Singular.lean` §E3 called
"out of reach". -/
theorem sl2Singular_mem_maxGradedIdeal :
    Sl2Sing.sl2Singular ∈ QuotVOA.maxGradedIdeal voaSl2Adm := by
  rw [← rightRadical_eq_maxGradedIdeal
    (canonicalInvariantForm_isFullyInvariant vacuum_ne_zero quasiPrimary)
    (canonicalInvariantForm_normalized vacuum_ne_zero quasiPrimary)]
  exact sl2Singular_mem_rightRadical

/-- **The maximal graded ideal is nonzero**, because the singular vector is nonzero
(`Wak.sl2Singular_ne_zero`, unconditional and `pbw`-free).  So the simple quotient is a
**proper** quotient: `L₋₄⁄₃(𝔰𝔩₂) ≠ V^{-4/3}(𝔰𝔩₂)`.  This is exactly the hypothesis under which
Linshaw–Qi conjecture rigidity, and the hypothesis their Theorem 3.1 needs (via simplicity). -/
theorem maxGradedIdeal_ne_bot : QuotVOA.maxGradedIdeal voaSl2Adm ≠ ⊥ := by
  intro h
  refine Wak.sl2Singular_ne_zero ?_
  have := sl2Singular_mem_maxGradedIdeal
  rw [h, Submodule.mem_bot] at this
  exact this

/-- **`L₋₄⁄₃(𝔰𝔩₂)`**, the simple quotient of `V^{-4/3}(𝔰𝔩₂)` by its maximal proper graded
ideal.  Definitionally the same object as `AffineSl2QuasiLisse.simpleSl2QL` (the two differ only
in which proof of `-4/3 + 2 ≠ 0` is supplied, and proof irrelevance is definitional); it is
re-introduced here so that this file does not have to import the quasi-lisse development. -/
noncomputable def L43 :
    VertexOperatorAlgebra (WakModule (-4 / 3 : ℂ) ⧸ QuotVOA.maxGradedIdeal voaSl2Adm) :=
  QuotVOA.maxQuotientVOA voaSl2Adm

/-- `L₋₄⁄₃(𝔰𝔩₂)` is a **simple** VOA (`QuotVOA.isSimple_maxQuotientVOA'`). -/
theorem L43_isSimple : L43.IsSimple :=
  QuotVOA.isSimple_maxQuotientVOA' voaSl2Adm vacuum_ne_zero

/-- `L₋₄⁄₃(𝔰𝔩₂)` is **nonzero** — its vacuum survives.  This is the non-vacuity witness for
every rigidity statement below: a rigidity theorem about the zero VOA would be trivially true. -/
theorem L43_vacuum_ne_zero : L43.vacuum ≠ 0 := by
  intro h
  refine QuotVOA.vacuum_not_mem_maxGradedIdeal voaSl2Adm vacuum_ne_zero ?_
  rwa [show L43.vacuum = (QuotVOA.maxGradedIdeal voaSl2Adm).mkQ voaSl2Adm.vacuum from rfl,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h

/-- **The singular vector dies in `L₋₄⁄₃(𝔰𝔩₂)`** — the second hypothesis Linshaw–Qi §5 uses
(the first being simplicity).  Both are theorems rather than assumptions. -/
theorem mkQ_sl2Singular_eq_zero :
    (QuotVOA.maxGradedIdeal voaSl2Adm).mkQ Sl2Sing.sl2Singular = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact sl2Singular_mem_maxGradedIdeal

/-- The Linshaw–Qi vector itself dies in `L₋₄⁄₃(𝔰𝔩₂)`, via §B's identification. -/
theorem mkQ_lqVector_eq_zero :
    (QuotVOA.maxGradedIdeal voaSl2Adm).mkQ (lqVector (-4 / 3 : ℂ)) = 0 := by
  rw [lqVector_eq_sl2Singular]; exact mkQ_sl2Singular_eq_zero

/-! ## §D  Theorem 3.1 and the SPLIT of Section 5

Three predicates on an arbitrary VOA, so that the conditional assembly in §E carries them
explicitly and a later module can discharge any of them without restating anything:

* `RegularImpliesTrivialGraded` — their Theorem 3.1. Proved for L43 downstream in
  `AffineSl2RegularReconstruction`; retained here as an arbitrary-VOA input.
* `Sl2BasisOnWeightOne` — the Lie-theoretic input, from which **PIECE 1** (the [KQ] §6.2
  normalisation, `VertexOperatorAlgebra.WeightOneH2Vanishes`) is *proved* by Whitehead's second
  lemma in `Core.WeightOneCohomology`. Proved at L43 downstream in
  `AffineSl2RigidityBasis` (see also the docstring of
  `Sl2BasisOnWeightOne` for the route).
* `NormalisedPoleVanishes` — **PIECE 2**, the §5 computation for a deformation already in pole
  form.  Not proved; this is the only genuinely unfinished mathematics.

The split is what removes the tautology of the previous revision, and §4 of
`Examples/AffineSl2RigidityCollapse.lean` proves that it does.
-/

/-- **Linshaw–Qi, Theorem 3.1** (the reduction), as a named hypothesis on `W`:

> if `Y₁(a,x)b` contains no negative powers of `x` for all weight-one `a, b`, then `Y₁` is a
> trivial (coboundary) deformation.

⚠ **Scope.**  The predicate is stated for an arbitrary `W`, but it is **not** proved in general.
It is proved only at affine `𝔰𝔩₂` simple quotients: `LQ43.L43_regularImpliesTrivialGraded`
(`Examples/AffineSl2RegularReconstruction.lean`) and
`AffineSl2GeneralRigidity.simple_regularImpliesTrivialGraded`
(`Examples/AffineSl2GeneralRegularReconstruction.lean`, under its own level hypotheses), both by
the closed-lift reconstruction, not via Linshaw–Qi.  As a general statement it remains a citation.
History, for the general Linshaw–Qi argument: the proof was reconstructed independently and judged sound, *except* that it invokes
[L, Thm 4.11] (Lian, Comm. Math. Phys. **163** (1994) 307–357) for "`W` is a quotient of an
affine VOA, in particular `W₍₀₎ = ℂ𝟙`".  Lian's category has one-dimensional degree-0 component
as a standing hypothesis and his subject is simple VOAs, neither of which is known for the `W`
at hand, so the citation may be circular exactly where `W₍₀₎ = ℂ𝟙` is used.  The source could
not be obtained to settle this.  The step is repairable without Lian by the universal property
of `V^k(𝔤)`, which is the route a formalisation should take.

⚠ The proof of Theorem 3.1 in arXiv:2601.12017**v2** is, by the authors' own statement,
contributed by ChatGPT 5.6-Pro, in a revision that exists because v1 contained errors.

Note the `IsGraded` hypothesis: it is not in the paper (which works in the graded category
throughout) but is needed here, because `Deform.FirstOrderDeformation` does not carry gradedness
as a field while `Deform.IsCoboundary` demands a grade-preserving `φ`. -/
def RegularImpliesTrivialGraded {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ D : Deform.FirstOrderDeformation W, D.IsGraded → D.Regular → D.IsTrivial

/-! ### PIECE 2 — the §5 computation, for a deformation already in pole form

`Deform.FirstOrderDeformation.InPoleForm` (defined in `Core.WeightOneCohomology`) is the first
clause of the paper's equation (3): the `x^{-1}` coefficient of `Y₁(a,x)b` vanishes for
weight-one `a, b`.  It is what PIECE 1 produces, and the condition under which the paper's
constant `c` is defined and gauge-invariant at all. -/

/-- **Linshaw–Qi §5 — PIECE 2**, as a named hypothesis on `W`: for a graded deformation **already
in pole form**, the pole itself vanishes, i.e. `c = 0`.

This is the **only** place in the whole argument where the level `-4/3` and the weight-3
singular vector enter.  Everything about the weight-one Lie algebra alone has been separated off
into `VertexOperatorAlgebra.WeightOneH2Vanishes` (PIECE 1), which — unlike this — is a *theorem*
whenever `𝒱₁` carries an `𝔰𝔩₂`-triple basis.

⚠ **Status: not proved in this module.**  §A above proves the *conclusion* of §5.3 — that
equations (10)–(14) force `c = 0` — outright and unconditionally, and §A″ presents it in the six
unknowns it really has.  What is missing is the bridge from `Deform.FirstOrderDeformation` to
those six scalars:

**Steps 1 and 2 below are proved in
`Core/DeformationCurrentModes`, `Core/DeformationPoleForm`, and
`Examples/AffineSl2DeformationPole`. `L43_normalized_master_relation` supplies the
actual single scalar for every normalized graded deformation. Step 3 is not carried out in this
module; the predicate at `L43` is proved downstream as
`AffineSl2RigidityComplete.L43_normalisedPoleVanishes`.**

1. the deformed commutator ("master") relation
   `⁅a^def_m, b_n⁆ + ⁅a_m, b^def_n⁆ = ⁅a,b⁆^def_{m+n} + m·c·⟨a,b⟩δ_{m+n,0}`, the `ℓ = 0`,
   general-`(m,n)` case of `Deform.FirstOrderDeformation.jacobi`.  This is the *same* finsum
   collapse that `Deform.jacobi_zero_modes` already performs for `ℓ = m = n = 0`, so it is
   reachable and low-risk;
2. the single constant `c`: with `InPoleForm` in hand, `(a,b) ↦ D.poleVec a b ∈ 𝒱₀ = ℂ𝟙`
   (`poleVec_mem_grading_zero`) is a bilinear form, the master relation makes it invariant, and
   an invariant form on `𝔰𝔩₂` is a multiple of the Killing form;
3. the identification of `h^def(-1)e(-2)1`, `h^def(-1)h(-1)e(-1)1`, `e^def(-1)e(-1)f(-1)1` with
   §A's coordinates — by §A″ only through `P = 42A - 9B - 36C`.  Reading the five scalar
   equations off `f^def(1)s = 0` and `h^def(1)s = 0` needs linear **independence** of the
   weight-2 and weight-3 monomials, the "weight-3 spanning" gap flagged at
   `Examples/AffineSl2Singular.lean` §E1, which must be closed `pbw`-free through the Wakimoto
   realisation.  That is a separate module, not a corollary.

⚠⚠ **Remark: two stronger hypotheses fail.**

* The hypothesis `GradedImpliesRegular` — "every graded first-order
  deformation of `W` is regular".  That is **false** for `L43`, so a theorem assuming it is vacuous.  The
  refutation is kept as a theorem in `Examples/AffineSl2RigidityCollapse.lean`
  (`not_gradedImpliesRegular_L43`, `not_gradedImpliesPoleZero_L43`): `δ(L₀)` is graded and
  trivial and has `u¹₍ₙ₎v = (n+1)u₍ₙ₎v`, so at `n = 0` regularity would force `h₍₀₎e = 0` and at
  `n = 1` pole-vanishing would force `f₍₁₎e = 0`.
* The hypothesis `GradedRegularUpToCoboundary W` — "every graded deformation is regular
  after subtracting a coboundary" — avoids the vacuity but has a worse defect: it is
  **uniformly equivalent to the conclusion**, since `IsRigidGraded W → GradedRegularUpToCoboundary W`
  holds for every `W` in one line, with witness `E = 0`.  A theorem assuming it is a tautology.  That
  predicate and the theorems supporting it are not part of the library.

The present form has no such escape: it is a `∀`-statement with a normalisation hypothesis, not
an `∃`-statement about representatives, so `E = 0` has no analogue.  Its **coboundary content**
— what it says about `D = δφ`, which is all that rigidity can ever supply — is exactly *every
derivation of `𝒱₁` is skew for the level form `⟨a,b⟩𝟙 = a₍₁₎b`*, which is true at `L43` for a
`W`-specific Lie-theoretic reason (`Der(𝔰𝔩₂) = ad(𝔰𝔩₂)` plus invariance of the form) and **false**
at the rank-1 free boson.  That refutation is a theorem:
`AffineSl2RigidityCollapse.not_normalisedPoleVanishes_heisenberg`. -/
def NormalisedPoleVanishes {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ D : Deform.FirstOrderDeformation W, D.IsGraded → D.InPoleForm →
    ∀ a ∈ W.grading 1, ∀ b ∈ W.grading 1, D.poleVec a b = 0

/-! ### The `𝔰𝔩₂`-triple hypothesis, and why the split is not bookkeeping

**A logical point that has to be stated, because it changes what "non-tautological" can mean.**
At a *fixed* `W`, "not implied by `Deform.IsRigidGraded W`" is unattainable for any true
hypothesis: two true propositions imply each other.  The criterion with content — and it is
exactly the one the deleted `GradedRegularUpToCoboundary` failed — is **uniform derivability**:
is there a proof of `∀ W, IsRigidGraded W → H W` that uses nothing about `W`?  For the deleted
predicate there was, and it was one line.

For the split hypotheses there is not, and the file carries formal certificates of that:

* `AffineSl2RigidityCollapse.not_normalisedPoleVanishes_heisenberg` refutes PIECE 2 at the
  rank-1 free boson, where `𝒱₁ = ℂα` is abelian (so `InPoleForm` is automatic at `n = 0`) while
  `α₍₁₎α = k𝟙 ≠ 0`.  Hence
  `AffineSl2RigidityCollapse.no_uniform_derivation_piece2`: a uniform derivation of PIECE 2 from
  graded rigidity would refute graded rigidity of a free boson — i.e. would produce a non-trivial
  graded first-order deformation of a free boson, which this repository has never produced for
  any VOA.
* `AffineSl2RigidityCollapse.not_trivial_satisfies_piece2` is the exact analogue of the deleted
  `trivial_satisfies`, and it is **refutable**: the coboundary content of PIECE 2 is not provable
  for every `W`.  This is a formal contrast with the deleted hypothesis, not a rhetorical one.
* PIECE 1 has no coboundary content at all — it does not quantify over deformations — and it is
  not a hypothesis here in the first place: `Sl2BasisOnWeightOne` discharges it outright, through
  `VertexOperatorAlgebra.weightOneH2Vanishes_of_sl2Basis`.  A discharged step cannot be a
  tautology-generator.  `no_uniform_derivation_sl2Basis` below records the corresponding uniform
  statement for the basis hypothesis itself.

**The two pieces are not a repartition of one thing.**  The rank-1 free boson separates them:
`WeightOneH2Vanishes` holds there vacuously (`Λ²` of a one-dimensional space is `0`) while
`NormalisedPoleVanishes` fails, so PIECE 1 does not imply PIECE 2.  In the other direction the
separation is structural: PIECE 1 never sees any mode but `₍₀₎`, so it cannot see the level; PIECE
2 never sees `H²` of the `₍₀₎`-bracket.  That is exactly the division Linshaw–Qi make and the
deleted single hypothesis had merged.

⚠⚠ **The residual, stated openly so that it is not re-found as a defect.**  *At `L43`*, and
*given* `Sl2BasisOnWeightOne L43`, PIECE 2 is still mathematically **equivalent** to the
conclusion: rigidity turns a graded `D` in pole form into `δφ`, `InPoleForm` makes `ψ := φ|𝒱₁` a
derivation, Whitehead's **first** lemma `Der(𝔰𝔩₂) = ad(𝔰𝔩₂)` makes it `ad x`, and invariance of the
level form kills the pole.  So `IsRigidGraded L43 ↔ (h31 ∧ h2)` under `hb`; and unlike the deleted
predicate that equivalence is *reachable* rather than one line — Mathlib supplies Whitehead I as
`LieDerivation.IsKilling.exists_eq_ad`, needing `LieAlgebra.IsKilling ℂ ↥𝒱₁`.

That is **not** the repaired defect, and it is not repairable by choosing a different hypothesis:
§5's *conclusion* is "the normalised pole vanishes", so any faithful split of Theorem 5.1 into
Theorem 3.1 + §5 has it.  The distinction that matters, and that the split delivers, is between a
derivation that is **bookkeeping** (`E = 0`: uniform, one line, nothing about `W`) and one that
consumes **the `𝔰𝔩₂` structure of `𝒱₁` and a second Whitehead lemma**.  Content beyond the split
is bought only by the *bridge* — assuming §5's **input** (equations (10)–(14), which §A above
already proves force `c = 0` unconditionally) in place of its output.  See the three numbered
steps in the docstring of `NormalisedPoleVanishes`. -/

/-- The Lie-theoretic input at `W`: the weight-one space carries an `𝔰𝔩₂`-triple basis
`(e, h, f) = (b 0, b 1, b 2)`.

This is a statement about `𝒱₁` **alone**.  From it, both `CentrelessWeightOne` and PIECE 1
(`WeightOneH2Vanishes`) follow as theorems — the latter by Whitehead's second lemma, proved in
`Core.WeightOneCohomology` as a finite computation.

For `L43` this is proved in the companion module `AffineSl2RigidityBasis` as
`L43_sl2BasisOnWeightOne`, by positive-mode coefficient extraction and current spanning.
The original alternative route described below uses invariant forms: it needs `dim (L43)₁ = 3` with `e, h, f`
independent *in the quotient*.  The route is nondegeneracy of the canonical form on `𝒱₁` (Gram
determinant `-2k³ ≠ 0` at `k = -4/3`, every entry computed by the same three-line route as
`AffineSl2RigidityCollapse.form_f_e`) plus Li's radical theorem.  See the file docstring. -/
def Sl2BasisOnWeightOne {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∃ b : Module.Basis (Fin 3) ℂ ↥(W.grading 1), IsSl2Triple (b 1) (b 0) (b 2)

/-- PIECE 1 is a **theorem** under `Sl2BasisOnWeightOne`. -/
theorem weightOneH2Vanishes_of_sl2Basis' {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) (hb : Sl2BasisOnWeightOne W) : W.WeightOneH2Vanishes := by
  obtain ⟨b, ht⟩ := hb
  exact VertexOperatorAlgebra.weightOneH2Vanishes_of_sl2Basis W b ht

/-- Centrelessness of `𝒱₁` is a **theorem** under `Sl2BasisOnWeightOne`. -/
theorem centrelessWeightOne_of_sl2Basis' {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) (hb : Sl2BasisOnWeightOne W) : W.CentrelessWeightOne := by
  obtain ⟨b, ht⟩ := hb
  exact VertexOperatorAlgebra.centrelessWeightOne_of_sl2Basis W b ht

/-- **A uniform derivation of the `𝔰𝔩₂`-basis hypothesis from graded rigidity is impossible**,
on pain of refuting graded rigidity of every VOA with no weight-one states — the triplet algebra
`W(2)` (`SympFerm.tripletW2_grading_one`) among them.  A `Basis (Fin 3) ℂ ↥⊥` cannot exist,
because `b 0 ≠ 0` in any basis while every element of `⊥` is `0`. -/
theorem no_uniform_derivation_sl2Basis {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) (h1 : W.grading 1 = ⊥)
    (H : ∀ (𝒲 : Type u) [AddCommGroup 𝒲] [Module ℂ 𝒲] (V : VertexOperatorAlgebra 𝒲),
      Deform.IsRigidGraded V → Sl2BasisOnWeightOne V) : ¬ Deform.IsRigidGraded W := by
  intro hrig
  obtain ⟨b, ht⟩ := H 𝒱 W hrig
  refine ht.h_ne_zero (Subtype.ext ?_)
  rw [ZeroMemClass.coe_zero]
  exact (Submodule.eq_bot_iff _).mp h1 _ (b 1).2

/-! ### One piece of §5's reduction that *is* provable here

The paper's "regular" means `a^def₍ₙ₎b = 0` for **all** `n ≥ 0`, but only `n = 0` and `n = 1` can
ever be nonzero on the weight-one space: grading sends `a^def₍ₙ₎b` into `𝒱_{1-n}`, which is `⊥`
for `n ≥ 2` by VOA4 positivity.  So the whole of regularity really is carried by the two
constants the paper writes down, and §A's `c` is the only one of them that survives
skew-symmetry.  This is proved, not assumed. -/
/-- For a graded deformation, regularity on two currents requires checking only the zero and first
positive modes. Higher modes would land in negative weights, which are absent. These two slots
encode the corrected Lie bracket and corrected central pairing. -/
theorem regular_iff_zero_one {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    {W : VertexOperatorAlgebra 𝒱} (D : Deform.FirstOrderDeformation W) (hD : D.IsGraded) :
    D.Regular ↔ ∀ a ∈ W.grading 1, ∀ b ∈ W.grading 1,
      D.smul₁ a 0 b = 0 ∧ D.smul₁ a 1 b = 0 := by
  constructor
  · intro h a ha b hb
    exact ⟨h a ha b hb 0 le_rfl, h a ha b hb 1 (by norm_num)⟩
  · intro h a ha b hb n hn
    rcases lt_or_ge n 2 with h2 | h2
    · interval_cases n
      · exact (h a ha b hb).1
      · exact (h a ha b hb).2
    · have hmem := hD 1 1 a ha b hb n
      rw [show (1 : ℤ) + 1 - n - 1 = 1 - n from by ring,
        W.positivity (1 - n) (by omega), Submodule.mem_bot] at hmem
      exact hmem

/-! ## §E  The assembly — Theorem 5.1 in conditional form

⚠ **The target is `Deform.IsRigidGraded`, not `Deform.IsRigid`.**  `Deform.IsRigid` quantifies
over *all* first-order deformations while `Deform.IsCoboundary` insists on a grade-preserving
`φ`; `NonzeroDeform.l1Deformation = deltaCochain W (W.L 1)` is a legitimate deformation of every
VOA which is not graded when `L₁` acts nontrivially, and `isGraded_of_isTrivial` then makes it
non-trivial.  The repository already proves the Virasoro instance
(`NonzeroDeform.not_isRigid_virasoroVOA`) and flags the asymmetry in `NonzeroDeformation` §7.
So `Deform.IsRigid L43` is very probably **false**, and claiming it would be an overclaim.
Linshaw–Qi's Theorem 5.1 is about grading- and vacuum-preserving deformations, which is
`IsRigidGraded`.
-/

/-- **The assembly, for an arbitrary VOA.**  Theorem 3.1, PIECE 1 and PIECE 2 give graded
rigidity.  This replaces the deleted `isRigidGraded_of_hypotheses`, which took a *single* §5
hypothesis that bundled the normalisation together with the computation and was for that reason
uniformly equivalent to its own conclusion.

The shape of the argument, which is where the split earns its keep:

1. `Deform.weightOneCochain_mem_twoCocycle` turns the graded `D` into a Chevalley–Eilenberg
   2-cocycle `ω(a,b) = a¹₍₀₎b` on `𝒱₁`;
2. PIECE 1 (`h1`) produces `ψ` with `d₁₂ψ = ω`;
3. `VertexOperatorAlgebra.extendWeightOne` lifts `ψ` to a grade-preserving `φ : 𝒱 →ₗ 𝒱` killing
   the vacuum, and `coboundary_weightOne_eq_d₁₂` says the VOA coboundary `δφ` restricts on `𝒱₁`
   at mode `0` to exactly `d₁₂ψ`;
4. `E := D - δφ` is therefore a graded deformation **in pole form** — Linshaw–Qi's equation (3);
5. PIECE 2 (`h2`) kills its pole, `regular_iff_zero_one` upgrades that to `E.Regular`, Theorem 3.1
   (`h31`) makes `E.Y1` a coboundary, and `D.Y1 = E.Y1 + δφ` is one by `Deform.IsCoboundary.add`.
-/
theorem isRigidGraded_of_split {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) (hZ : W.CentrelessWeightOne)
    (h31 : RegularImpliesTrivialGraded W) (h1 : W.WeightOneH2Vanishes)
    (h2 : NormalisedPoleVanishes W) : Deform.IsRigidGraded W := by
  classical
  haveI : DirectSum.Decomposition W.grading := W.isInternal.chooseDecomposition W.grading
  intro D hD
  obtain ⟨ψ, hψ⟩ := h1 (Deform.weightOneCochain D hD hZ)
    (Deform.weightOneCochain_mem_twoCocycle D hD hZ)
  set φ : 𝒱 →ₗ[ℂ] 𝒱 := VertexOperatorAlgebra.extendWeightOne W ψ with hφdef
  have hφ0 : φ W.vacuum = 0 := VertexOperatorAlgebra.extendWeightOne_vacuum ψ
  have hφg : Deform.GradePreserving W φ :=
    VertexOperatorAlgebra.gradePreserving_extendWeightOne ψ
  have hcobφ : Deform.IsCoboundary W (NonzeroDeform.deltaCochain W φ) :=
    NonzeroDeform.isCoboundary_deltaCochain W hφ0 hφg
  have hmem : D.Y1 - NonzeroDeform.deltaCochain W φ ∈ Deform.cocycles W :=
    Submodule.sub_mem _ (Deform.Y1_mem_cocycles D)
      (NonzeroDeform.deltaCochain_mem_cocycles W hφ0)
  set E : Deform.FirstOrderDeformation W :=
    Deform.ofCocycle (D.Y1 - NonzeroDeform.deltaCochain W φ) hmem with hEdef
  have hEY : E.Y1 = D.Y1 - NonzeroDeform.deltaCochain W φ := rfl
  have hEsmul : ∀ (u : 𝒱) (n : ℤ) (v : 𝒱), E.smul₁ u n v
      = D.smul₁ u n v - (W.smul (φ u) n v - φ (W.smul u n v) + W.smul u n (φ v)) :=
    fun _ _ _ => rfl
  have hEg : E.IsGraded := by
    rw [Deform.isGraded_iff_Y1_mem_gradedCochains, hEY]
    exact Submodule.sub_mem _ ((Deform.isGraded_iff_Y1_mem_gradedCochains D).mp hD)
      (Deform.coboundaries_le_gradedCochains W hcobφ)
  have hEpole : E.InPoleForm := by
    intro a ha b hb
    have key := VertexOperatorAlgebra.coboundary_weightOne_eq_d₁₂ (W := W) ψ ⟨a, ha⟩ ⟨b, hb⟩
    rw [hψ, Deform.weightOneCochain_coe] at key
    rw [hEsmul a 0 b, key, sub_self]
  have hEr : E.Regular :=
    (regular_iff_zero_one E hEg).mpr fun a ha b hb =>
      ⟨hEpole a ha b hb, h2 E hEg hEpole a ha b hb⟩
  have hEcob : Deform.IsCoboundary W E.Y1 := h31 E hEg hEr
  change Deform.IsCoboundary W D.Y1
  rw [show D.Y1 = E.Y1 + NonzeroDeform.deltaCochain W φ from by rw [hEY]; abel]
  exact Deform.IsCoboundary.add hEcob hcobφ

/-- **The assembly with PIECE 1 discharged.**  Given an `𝔰𝔩₂`-triple basis of `𝒱₁`, both the
normalisation (PIECE 1) and the centrelessness the bridge needs are theorems, so only Theorem 3.1
and PIECE 2 remain as hypotheses. -/
theorem isRigidGraded_of_sl2Basis {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) (hb : Sl2BasisOnWeightOne W)
    (h31 : RegularImpliesTrivialGraded W) (h2 : NormalisedPoleVanishes W) :
    Deform.IsRigidGraded W :=
  isRigidGraded_of_split W (centrelessWeightOne_of_sl2Basis' W hb) h31
    (weightOneH2Vanishes_of_sl2Basis' W hb) h2

/-- **Linshaw–Qi Theorem 5.1, conditional form.**  `L₋₄⁄₃(𝔰𝔩₂)` admits only trivial graded
first-order deformations, *given* their Theorem 3.1, the `𝔰𝔩₂` structure of the weight-one space,
and their Section 5 computation for a deformation already in pole form.

What is unconditional here, and what is not:

* **Unconditional** — that `L43` exists, is simple (`L43_isSimple`), is nonzero
  (`L43_vacuum_ne_zero`), is a *proper* quotient of `V^{-4/3}(𝔰𝔩₂)` (`maxGradedIdeal_ne_bot`),
  and kills the singular vector (`mkQ_sl2Singular_eq_zero`).  So the statement is not vacuous.
* **Unconditional** — the linear algebra of §5.3 (`PrintedSystem.c_eq_zero`,
  `CorrectedSystem.c_eq_zero`, `pSystem_c_eq_zero`), and the identification of the singular
  vector (`lqVector_eq_sl2Singular`).
* **Unconditional** — PIECE 1, the [KQ] §6.2 normalisation, *given* `hb`: it is
  `VertexOperatorAlgebra.weightOneH2Vanishes_of_sl2Basis`, Whitehead's second lemma proved as a
  finite computation in `Core.WeightOneCohomology`.  This is the step that the previous two
  revisions of this file had bundled into the §5 hypothesis, and unbundling it is what removes
  the tautology.
* **Assumed** — `hb` (`Sl2BasisOnWeightOne L43`: the weight-one space of `L43` is `𝔰𝔩₂`, true
  and reachable, see the docstring), `h31` (their Theorem 3.1; see the caveat on the Lian
  citation and on the AI provenance) and `h2` (PIECE 2, the §5 computation).

⚠⚠ **Remark: two tempting hypotheses fail.**  Taking
`GradedImpliesRegular L43`, which is **refutable**, would make the theorem vacuous.  Taking
`GradedRegularUpToCoboundary L43`, which is **uniformly equivalent to the conclusion**, would
make it a tautology.  Neither predicate is part of the library; the
refutations of the first are kept as theorems in `Examples/AffineSl2RigidityCollapse.lean`, and
the certificates that the present hypotheses are *not* uniformly derivable from the conclusion
are `not_normalisedPoleVanishes_heisenberg`, `not_trivial_satisfies_piece2`,
`no_uniform_derivation_piece2` and `no_uniform_derivation_sl2Basis`. -/
theorem L43_isRigidGraded (hb : Sl2BasisOnWeightOne L43) (h31 : RegularImpliesTrivialGraded L43)
    (h2 : NormalisedPoleVanishes L43) : Deform.IsRigidGraded L43 :=
  isRigidGraded_of_sl2Basis L43 hb h31 h2

end VOA.LQ43
