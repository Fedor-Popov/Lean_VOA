/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroSimpleGram
import VOA.Examples.VirasoroCDeformation

/-!
# Rigidity of a simple quotient from a **graded-dimension jump**

The target is a *structural* rigidity theorem for `L(c,0)` — one that does not analyse singular
vectors case by case.  This file records **exactly** how much of that argument goes through, and
names the rest.

## The argument, and where it is honest

1. **The gauge orbit at `(ω,ω)` is exactly a line.**  §1.  `L(c,0)₂ = ℂ·[ω]` (transported from
   `V(c,0)₂ = ℂ·ω`), so `Examples/VirasoroCDeformation.cmode_conformal_of_isCoboundary` applies to
   the *simple quotient*, and the converse (`exists_isCoboundary_on_gauge_line'`, proved here for
   an arbitrary VOA) shows every point of the line is attained.  For `c ≠ 0` this gives a sharp
   iff (`attained_by_coboundary_iff`): the pair `(α·ω, β·𝟙)` is a coboundary value **iff**
   `2β = αc`.  So on the two slots the gauge is one-dimensional inside a two-dimensional space:
   **exactly one modulus**, at that level of the data.

   ⚠ "the deformation data at the `(ω,ω)` level is two-dimensional" is an **undercount** as a
   statement about the whole deformation.  `Deform.FirstOrderDeformation` has four fields —
   `truncation`, `vacuum_Y1`, `creation`, `jacobi` — and **no** translation/`T`-covariance and
   **no** skew-symmetry field.  So `ω¹₍₀₎ω ∈ 𝒱₃` is unconstrained by anything proved here, and
   `ω¹₍ₙ₎ω ∈ 𝒱_{3-n}` is a further nonzero slot for every `n ≤ -1`.  Reducing all of those to the
   two slots is the *generation/reconstruction* step, and it is hypothesis (D) below.

2. **The jump.**  §2.  `Core/GradedFormMatrix.finrank_maxQuotient_grading` (D1) plus a level-`n`
   determinant computation gives `dim L(c₀,0)ₙ < dim L(c,0)ₙ` whenever the determinant vanishes at
   `c₀` and not at `c`.  Unconditional, and instantiated at Ising `c = 1/2` and `M(2,7)`
   `c = -68/7`, level `6`.

3. **Rigidity.**  §3.  This is the step that needs a hypothesis, and it is named
   `RealisedByNondegenerate`.  A `FirstOrderDeformation` is an infinitesimal object: it deforms
   `Y` and leaves the graded vector space alone, so *by itself* it cannot see a dimension jump.
   What turns the jump into an obstruction is the assertion that a nontrivial graded deformation
   of `L(c₀,0)` is realised by the family `c ↦ L(c,0)` — i.e. that the modulus integrates — and
   that graded dimensions are then preserved.  That is hypothesis (E), and the theorem
   `isRigidGraded_of_finrank_lt` is one line given it.

## ⚠ What is deliberately **not** claimed

* **`∂_c` is not constructed.**  `VirCDef.IsCDeformation` is a *predicate* with no inhabitant
  anywhere in this repository (its own file says so).  Nothing here asserts one exists.
* **"the degenerate locus is discrete" is false** as a statement about the union over all levels:
  `1 - 6(p-q)²/(pq) → 1` as `p,q → ∞` with `p - q` fixed, so the minimal-model charges accumulate
  at `c = 1`.  The true and sufficient statement is the **per-level** one — for fixed `n`,
  `det canGram_n` is a nonzero polynomial, hence has finitely many roots — and that is what §2
  uses.  The same correction applies verbatim to admissible affine `𝔰𝔩₂` levels `-2 + p/q`,
  which are *dense* in `[-2, ∞)`, not discrete.
* **No statement "every graded cocycle is regular".**  It would be false:
  `NonzeroDeform.scalingDeformation = δL₀` is a graded coboundary sitting on the gauge line at
  `μ = 2`, with `ω¹₍₃₎ω = 2c·𝟙 ≠ 0` (`VirCDef.scaling_on_gauge_line`).  Every statement below is
  therefore *modulo coboundaries*.
* **`Deform.GradedToGlobalRigidity` is untouched.**  §3 is phrased against `IsRigidGraded`
  directly, not tridegree by tridegree, so it does not inherit that gap.

## Contents

* §1  `virasoroSimple_grading_two`, `gauge_line_simple`, `exists_isCoboundary_on_gauge_line'`,
  `attained_by_coboundary_iff`, `not_isTrivial_simple`.
* §2  `finrank_maxQuotient_lt_of_det_jump` (general, two VOAs), `no_gradedEquiv_of_finrank_ne`.
* §3  ⚠ `DeterminedByConformalVector` (hypothesis D), ⚠ `RealisedByNondegenerate`
  (hypothesis E), `isRigidGraded_of_finrank_lt`, and the instances
  `isRigidGraded_virasoroSimple_ising`, `isRigidGraded_virasoroSimple_m27`.
-/

set_option linter.style.longLine false

namespace VOA.VirRigidStruct

open VOA VOA.VirModule VOA.VirSimple VOA.LeeYang
open VOA.VirGram56 VOA.VirSimpleGram
open VOA.VertexOperatorAlgebra
open Deform
open Module (Basis finrank)

universe u

/-! ## §1  The gauge orbit at `(ω,ω)`, on the **simple** quotient

`Examples/VirasoroCDeformation` proves the gauge line for the *universal* `V(c,0)`, and its own
`## ⚠ Not claimed` section disclaims the simple-quotient version.  It transports with no new
mathematics, because the two general lemmas there are stated for an arbitrary VOA whose weight-2
space is the line on `ω`, and `L(c,0)₂` still is that line. -/

section Gauge

variable (c : ℂ)

/-- `L(c,0)₂ = ℂ·[ω]`: the weight-2 space of the **simple** quotient is still the line on the
conformal vector, at every central charge. -/
theorem virasoroSimple_grading_two :
    (virasoroSimple c).grading 2 = ℂ ∙ (virasoroSimple c).conformalVector := by
  rw [virasoroSimple_grading, VirCDef.gradingVir_two_eq_span_conformal c, Submodule.map_span,
    Set.image_singleton]
  rfl

/-- **The gauge line, on `L(c,0)`.**  Every coboundary has `(ω¹₍₁₎ω, ω¹₍₃₎ω) = (2μ·ω, μc·𝟙)`
for a single scalar `μ`. -/
theorem gauge_line_simple {f : Cochain (VirUniv c ⧸ maxIdealVir c)}
    (hf : IsCoboundary (virasoroSimple c) f) :
    ∃ μ : ℂ,
      cmode f (virasoroSimple c).conformalVector 1 (virasoroSimple c).conformalVector
          = (2 * μ) • (virasoroSimple c).conformalVector ∧
      cmode f (virasoroSimple c).conformalVector 3 (virasoroSimple c).conformalVector
          = (μ * c) • (virasoroSimple c).vacuum :=
  VirCDef.cmode_conformal_of_isCoboundary (virasoroSimple c) (virasoroSimple_grading_two c) hf

end Gauge

/-- **The converse, for an arbitrary VOA.**  Every point of the line `ℂ·(2ω, c·𝟙)` really is
attained by a coboundary, namely `(μ/2)·δL₀`.  `VirCDef.exists_isCoboundary_on_gauge_line`
proves this for `V(c,0)`; the proof uses only ingredients stated for a general `W`
(`NonzeroDeform.scalingDeformation`, `isTrivial_scalingDeformation`,
`smul₁_scalingDeformation_homog`), so it generalises verbatim. -/
theorem exists_isCoboundary_on_gauge_line' {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) (μ : ℂ) :
    ∃ f : Cochain 𝒱, IsCoboundary W f ∧
      cmode f W.conformalVector 1 W.conformalVector = (2 * μ) • W.conformalVector ∧
      cmode f W.conformalVector 3 W.conformalVector
        = (μ * W.centralCharge) • W.vacuum := by
  refine ⟨(μ / 2) • (NonzeroDeform.scalingDeformation W).Y1,
    IsCoboundary.smul _ (NonzeroDeform.isTrivial_scalingDeformation W), ?_, ?_⟩
  · rw [cmode_smul_cochain, cmode_Y1,
      NonzeroDeform.smul₁_scalingDeformation_homog W W.conformal_mem W.conformal_mem 1,
      VirCDef.conformal_smul_one, smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  · rw [cmode_smul_cochain, cmode_Y1,
      NonzeroDeform.smul₁_scalingDeformation_homog W W.conformal_mem W.conformal_mem 3,
      VirCDef.conformal_smul_three, smul_smul, smul_smul]
    congr 1
    push_cast
    ring

section GaugeSharp

variable (c : ℂ)

/-- **Exactly one modulus at the `(ω,ω)` level.**  For `c ≠ 0` a pair of scalars `(α, β)` is
the coboundary value of `(ω¹₍₁₎ω, ω¹₍₃₎ω)` on `L(c,0)` **iff** `2β = αc`.

So inside the two-dimensional space of pairs the gauge orbit is exactly a line — no smaller (the
converse direction) and no larger (`gauge_line_simple`) — and the quotient is **one**-dimensional.
That single surviving direction is what `∂/∂c` would be; nothing here asserts that it is
realised by an actual deformation. -/
theorem attained_by_coboundary_iff (hc : c ≠ 0) (α β : ℂ) :
    (∃ f : Cochain (VirUniv c ⧸ maxIdealVir c), IsCoboundary (virasoroSimple c) f ∧
        cmode f (virasoroSimple c).conformalVector 1 (virasoroSimple c).conformalVector
          = α • (virasoroSimple c).conformalVector ∧
        cmode f (virasoroSimple c).conformalVector 3 (virasoroSimple c).conformalVector
          = β • (virasoroSimple c).vacuum)
      ↔ 2 * β = α * c := by
  constructor
  · rintro ⟨f, hf, h1, h3⟩
    obtain ⟨μ, hμ1, hμ3⟩ := gauge_line_simple c hf
    have hα : α = 2 * μ := by
      have h := hμ1.symm.trans h1
      have hsub : (2 * μ - α) • (virasoroSimple c).conformalVector = 0 := by
        rw [sub_smul, h, sub_self]
      rcases smul_eq_zero.mp hsub with hz | hz
      · linear_combination (-1 : ℂ) * hz
      · exact absurd hz (virasoroSimple_conformalVector_ne_zero c hc)
    have hβ : β = μ * c := by
      have h := hμ3.symm.trans h3
      have hsub : (μ * c - β) • (virasoroSimple c).vacuum = 0 := by
        rw [sub_smul, h, sub_self]
      rcases smul_eq_zero.mp hsub with hz | hz
      · linear_combination (-1 : ℂ) * hz
      · exact absurd hz (virasoroSimple_vacuum_ne_zero c)
    rw [hα, hβ]
    ring
  · intro hlin
    obtain ⟨f, hf, h1, h3⟩ := exists_isCoboundary_on_gauge_line' (virasoroSimple c) (α / 2)
    refine ⟨f, hf, ?_, ?_⟩
    · rw [h1]; congr 1; ring
    · rw [h3]
      congr 1
      have hcc : (virasoroSimple c).centralCharge = c := virasoroSimple_centralCharge c
      rw [hcc]
      linear_combination (-1/2 : ℂ) * hlin

/-- **The separating criterion, on the simple quotient**, for `c ≠ 0`.  A deformation that
leaves `ω₍₁₎ω` alone but moves the central term `ω₍₃₎ω` is not trivial. -/
theorem not_isTrivial_simple (hc : c ≠ 0) (D : FirstOrderDeformation (virasoroSimple c))
    (h1 : D.smul₁ (virasoroSimple c).conformalVector 1 (virasoroSimple c).conformalVector = 0)
    (h3 : D.smul₁ (virasoroSimple c).conformalVector 3 (virasoroSimple c).conformalVector ≠ 0) :
    ¬ D.IsTrivial :=
  VirCDef.not_isCoboundary_of_conformal_witness (virasoroSimple c)
    (virasoroSimple_grading_two c) (virasoroSimple_conformalVector_ne_zero c hc) h1 h3

end GaugeSharp

/-! ## §2  The jump, in general form

Two VOAs, one degenerate at level `n` and one not, with the same level-`n` dimension: the simple
quotients have **different** graded dimensions.  Unconditional. -/

section Jump

variable {V₀ : Type u} [AddCommGroup V₀] [Module ℂ V₀] {W₀ : VertexOperatorAlgebra V₀}
variable {V₁ : Type u} [AddCommGroup V₁] [Module ℂ V₁] {W₁ : VertexOperatorAlgebra V₁}
variable {ι₀ : Type*} [Fintype ι₀] [DecidableEq ι₀]
variable {ι₁ : Type*} [Fintype ι₁] [DecidableEq ι₁]

/-- **The dimension jump.**  If the level-`n` canonical Gram determinant vanishes for `W₀`
and does not vanish for `W₁`, and the two universal level-`n` spaces have the same dimension, then

  `dim L(W₀)ₙ < dim L(W₁)ₙ`.

This is D1 (`finrank_maxQuotient_grading`) together with the two halves of the rank dichotomy.  It
is the whole unconditional content of "rigidity is inherited from the degenerate locus": the
family of *simple* quotients is not a family of graded vector spaces of constant dimension. -/
theorem finrank_maxQuotient_lt_of_det_jump
    (hne₀ : W₀.vacuum ≠ 0) (hqp₀ : ∀ v, v ∈ W₀.grading 1 → W₀.L 1 v = 0)
    (hne₁ : W₁.vacuum ≠ 0) (hqp₁ : ∀ v, v ∈ W₁.grading 1 → W₁.L 1 v = 0)
    (n : ℤ) (e₀ : Basis ι₀ ℂ (W₀.grading n)) (e₁ : Basis ι₁ ℂ (W₁.grading n))
    (hdim : finrank ℂ (W₀.grading n) = finrank ℂ (W₁.grading n))
    (h0 : (GramMat.canGram hne₀ hqp₀ n e₀).det = 0)
    (h1 : (GramMat.canGram hne₁ hqp₁ n e₁).det ≠ 0) :
    finrank ℂ ((QuotVOA.maxQuotientVOA W₀).grading n)
      < finrank ℂ ((QuotVOA.maxQuotientVOA W₁).grading n) := by
  have hlt := GramMat.finrank_maxQuotient_grading_lt_of_det_eq_zero hne₀ hqp₀ n e₀ h0
  have heq := GramMat.finrank_maxQuotient_grading_eq_of_det_ne_zero hne₁ hqp₁ n e₁ h1
  omega

end Jump

/-- **A dimension jump obstructs every graded linear equivalence.**  If two VOAs have different
level-`n` graded dimensions then there is no `ℂ`-linear equivalence of their carriers matching the
level-`n` graded pieces — a fortiori no isomorphism of vertex operator algebras.  So a jump is not
merely a numerical curiosity: it separates the objects. -/
theorem no_gradedEquiv_of_finrank_ne {U₀ : Type u} [AddCommGroup U₀] [Module ℂ U₀]
    {U₁ : Type u} [AddCommGroup U₁] [Module ℂ U₁]
    (p₀ : Submodule ℂ U₀) (p₁ : Submodule ℂ U₁)
    (h : finrank ℂ p₀ ≠ finrank ℂ p₁) :
    ¬ ∃ e : U₀ ≃ₗ[ℂ] U₁, ∀ x : U₀, x ∈ p₀ ↔ e x ∈ p₁ := by
  rintro ⟨e, he⟩
  refine h ?_
  have hmap : Submodule.map (e : U₀ →ₗ[ℂ] U₁) p₀ = p₁ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact (he x).mp hx
    · intro hy
      refine ⟨e.symm y, (he (e.symm y)).mpr ?_, by simp⟩
      simpa using hy
  have := LinearEquiv.finrank_eq (e.submoduleMap p₀)
  rw [hmap] at this
  exact this

/-! ## §3  ⚠ The two named hypotheses, and the structural theorem

Neither of the two predicates below is proved anywhere in this repository, and neither is
asserted.  They are stated so that every use of them is visible in a **signature**. -/

section Structural

variable {𝒰 : Type u} [AddCommGroup 𝒰] [Module ℂ 𝒰]

/-- ⚠ **HYPOTHESIS (D): `ω` generates, and a graded deformation is determined by its values on the
generator.**  Concretely: a graded first-order deformation that is *trivial on the two slots the
gauge line sees* is trivial outright.

This is the step that turns "one modulus at the `(ω,ω)` level" (§1) into "one modulus".  It is
**not** proved.  There is no strong-generation notion for the Virasoro VOA anywhere in this
repository (`StronglyGenerated` occurs only in the Triplet, affine-`𝔰𝔩₂` and Zhu–Verma files), and
`Deform.FirstOrderDeformation` carries no `T`-covariance and no skew-symmetry, so even
`ω¹₍₀₎ω ∈ 𝒱₃` is unconstrained.  Discharging it needs a reconstruction theorem for deformations. -/
def DeterminedByConformalVector (U : VertexOperatorAlgebra 𝒰) : Prop :=
  ∀ D : FirstOrderDeformation U, D.IsGraded →
    D.smul₁ U.conformalVector 1 U.conformalVector = 0 →
    D.smul₁ U.conformalVector 3 U.conformalVector = 0 →
    D.IsTrivial

/-- ⚠ **HYPOTHESIS (E): a nontrivial graded deformation is realised by the family, and the family
does not move graded dimensions.**

`d` is the *generic* level-`n` dimension.  The predicate says: if `U` admits a nontrivial graded
first-order deformation at all, then `U` already sits at the generic level-`n` dimension.

This is the only place where "the modulus integrates" enters, and it is exactly the step that a
first-order deformation cannot supply on its own: a `FirstOrderDeformation` deforms `Y` on a
**fixed** graded vector space, so it never sees a dimension jump by itself.  Stating (E) is the
honest way to say "the surviving modulus `∂/∂c` is realised by the family `c ↦ L(c,0)`, along
which graded dimensions are constant". -/
def RealisedByNondegenerate (U : VertexOperatorAlgebra 𝒰) (n : ℤ) (d : ℕ) : Prop :=
  (∃ D : FirstOrderDeformation U, D.IsGraded ∧ ¬ D.IsTrivial) → finrank ℂ (U.grading n) = d

/-- ⚠ **A TAUTOLOGY, not a rigidity theorem.**  Given the jump `hlt`, the hypothesis
`hE : RealisedByNondegenerate U n d` is logically *equivalent* to the conclusion `IsRigidGraded U`
(`VirRigidTangent.realisedByNondegenerate_iff_isRigidGraded`, `Examples/VirasoroRigidityTangent.lean`),
so this theorem and its instances read "if `U` is graded rigid then it is graded rigid".  The genuine
rigidity theorems are `VirModule.minimal_graded_rigidity` and its special cases.

Original description: a simple VOA whose level-`n` graded dimension is *strictly below* the
generic value `d` is graded-rigid, given hypothesis (E).

Read it as intended: `dim Uₙ < d` is the **dimension jump**, supplied unconditionally by D1 plus a
level-`n` Kac determinant (`finrank_maxQuotient_lt_of_det_jump`); `RealisedByNondegenerate` is the
assertion that a modulus, if there were one, would move `U` along the family and therefore keep
the graded dimension at the generic value.  The two are contradictory, so there is no modulus.

Uniform in everything: no Virasoro, no `𝔰𝔩₂`, no discreteness — only a *finite* level-`n`
degenerate locus is ever needed, and here not even that, just one nondegenerate comparison
point folded into `d`. -/
theorem isRigidGraded_of_finrank_lt (U : VertexOperatorAlgebra 𝒰) (n : ℤ) (d : ℕ)
    (hE : RealisedByNondegenerate U n d) (hlt : finrank ℂ (U.grading n) < d) :
    IsRigidGraded U := by
  intro D hD
  by_contra hT
  exact absurd (hE ⟨D, hD, hT⟩) (Nat.ne_of_lt hlt)

end Structural

/-! ## §4  The instances: Ising and `M(2,7)`, at level 6

Both are degenerate at level `6` and at no lower level (`VirGram56.det_canGram5_ising_ne_zero`,
`det_canGram5_m27_ne_zero`, and levels `2,3,4` have determinants `c/2`, `2c`, `c²(5c+22)/2`).
So these are genuinely new instances, not restatements of the Lee–Yang level-4 story. -/

/-- **Ising.**  Given hypothesis (E) at level 6 with generic dimension `4`, the simple
Virasoro VOA `L(1/2, 0)` is graded-rigid.  The jump input is unconditional:
`dim L(1/2,0)₆ < 4 = dim L(1,0)₆`. -/
theorem isRigidGraded_virasoroSimple_ising
    (hE : RealisedByNondegenerate (virasoroSimple isingC) 6 4) :
    IsRigidGraded (virasoroSimple isingC) :=
  isRigidGraded_of_finrank_lt (virasoroSimple isingC) 6 4 hE
    (finrank_virasoroSimple_six_lt_of_degenerate isingC (Or.inr (Or.inl rfl)))

/-- **`M(2,7)`.**  The same at `c = -68/7`. -/
theorem isRigidGraded_virasoroSimple_m27
    (hE : RealisedByNondegenerate (virasoroSimple m27C) 6 4) :
    IsRigidGraded (virasoroSimple m27C) :=
  isRigidGraded_of_finrank_lt (virasoroSimple m27C) 6 4 hE
    (finrank_virasoroSimple_six_lt_of_degenerate m27C (Or.inr (Or.inr (Or.inr rfl))))

/-- **Lee–Yang, at level 4.**  `dim L(-22/5,0)₄ = 1 < 2`. -/
theorem isRigidGraded_virasoroSimple_leeYang
    (hE : RealisedByNondegenerate (virasoroSimple leeYangC) 4 2) :
    IsRigidGraded (virasoroSimple leeYangC) :=
  isRigidGraded_of_finrank_lt (virasoroSimple leeYangC) 4 2 hE
    (by rw [finrank_virasoroSimple_leeYang_four]; norm_num)

/-- The jump feeding the Ising instance, spelled out against a comparison charge.  Nothing
here is hypothetical. -/
theorem finrank_ising_six_lt_generic :
    finrank ℂ ((virasoroSimple isingC).grading 6)
      < finrank ℂ ((virasoroSimple 1).grading 6) :=
  finrank_virasoroSimple_six_ising_lt

/-- …and the consequence that separates the two objects outright: no graded linear equivalence
carries `L(1/2,0)₆` onto `L(1,0)₆`. -/
theorem no_gradedEquiv_ising_one :
    ¬ ∃ e : (VirUniv isingC ⧸ maxIdealVir isingC) ≃ₗ[ℂ] (VirUniv 1 ⧸ maxIdealVir 1),
        ∀ x, x ∈ (virasoroSimple isingC).grading 6 ↔ e x ∈ (virasoroSimple 1).grading 6 :=
  no_gradedEquiv_of_finrank_ne _ _ (Nat.ne_of_lt finrank_ising_six_lt_generic)

end VOA.VirRigidStruct
