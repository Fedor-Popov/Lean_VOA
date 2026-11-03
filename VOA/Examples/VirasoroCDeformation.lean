/-
Copyright (c) 2026 Leonardo Rastelli, Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroDeformationLow
import VOA.Examples.NonzeroDeformation

/-!
# The `∂/∂c` direction of `V(c,0)` is not a gauge direction

## ⚠ Scope, stated before anything else

The cochain `∂_c Y` is **not constructed in this file**; it is constructed downstream, as
`VOA.VirPoly.cDeformation c : Deform.FirstOrderDeformation (virasoroVOA c)`
(`Examples/VirasoroCDefJacobi.lean`, via the polynomial-in-`c` family of
`Examples/VirasoroPoly*.lean`).  `Examples/VirasoroCDefFinal.lean` proves that it inhabits the
predicate `IsCDeformation` of §4 (`VOA.VirPoly.isCDeformation_cDeformation`) and hence, with
`not_isRigidGraded_of_isCDeformation` below, that `V(c,0)` is **not** `IsRigidGraded`, at every
`c ∈ ℂ` (`VOA.VirPoly.not_isRigidGraded_virasoroVOA`).  The theorems of *this* file remain
conditional on a deformation with the stated normalisation; they are the half of the argument
that does not depend on the construction.

What *is* proved here, unconditionally and at **every** central charge `c`, is that half:
**no field redefinition can move the central term of `V(c,0)` without also moving the
weight-`2` product.**  That is exactly the obstruction the `∂_c` direction exploits, and it
is the half that `Examples/VirasoroDeformationLow` records as an *orientation remark* (written
before `∂_c Y` was constructed).  Here it becomes a theorem — and one about
`Deform.IsTrivial` directly, not about a per-tridegree quotient, so it is immune to the
`Deform.GradedToGlobalRigidity` gap.

## The gauge line

A field redefinition is a grade-preserving `φ` with `φ𝟙 = 0` (`Deform.IsCoboundary`).  On
`V(c,0)` the weight-`2` space is the line `ℂ·ω` (`VirDefLow.gradingVir_two`) and the weight-`0`
space is `ℂ·𝟙` (VOA4), so such a `φ` is *one scalar* on everything the pair `(ω₍₁₎ω, ω₍₃₎ω)`
can see: `φω = μω`, and `φ` annihilates `𝒱₀`.  The two structure constants are

* `ω₍₁₎ω = L₀ω = 2ω` — carries **no** `c` (`conformal_smul_one`);
* `ω₍₃₎ω = L₂L₋₂𝟙 = (c/2)𝟙` — the central term, the *only* place `c` enters
  (`conformal_smul_three`).

Hence for every coboundary `δφ`

`δφ(ω,1,ω) = 2μ·ω`  and  `δφ(ω,3,ω) = μc·𝟙`  (`cmode_conformal_of_isCoboundary`),

and every point of that line is attained (`exists_isCoboundary_on_gauge_line`, by `(μ/2)·δL₀`).
The image of the field redefinitions in these two slots is therefore **exactly** the line
`ℂ·(2ω, c·𝟙)`.  A deformation with `ω¹₍₁₎ω = 0` and `ω¹₍₃₎ω ≠ 0` sits off it, and is not trivial
(`not_isTrivial_of_omega_witness`).

Why this is the right invariant, in one sentence: rescaling `ω` moves `c` quadratically, but the
Virasoro bracket `[Lₘ,Lₙ] = (m−n)L_{m+n} + …` is *linear* in `L` in its first term, so rescaling
is not an automorphism — unlike the Heisenberg family in the level, where rescaling the generator
*is* available and the level-derivative *is* a coboundary.

## Main results

* `conformal_smul_one`, `conformal_smul_three` — the two structure constants `ω₍₁₎ω = 2ω` and
  `ω₍₃₎ω = (c/2)𝟙`, for an **arbitrary** VOA, from VOA1–VOA2 and VA3.
* `deltaCochain_id`, `jacobiAx_Y` — `Y = δ(id)`, so `Y` itself satisfies the order-`t` Jacobi
  identity and fails to be a deformation only through `vacuum_Y1`.
* `cmode_conformal_of_isCoboundary` — the gauge line, for any VOA with `𝒱₂ = ℂ·ω`.
* `not_isCoboundary_of_conformal_witness` — the separating criterion, same generality.
* `not_isTrivial_of_omega_witness` — for `V(c,0)`, every `c`: a deformation fixing `ω₍₁₎ω`
  and moving `ω₍₃₎ω` is **not** trivial.
* `not_isRigidGraded_of_omega_witness`, `not_isRigid_of_omega_witness` — such a witness,
  if graded, refutes `Deform.IsRigidGraded (virasoroVOA c)` (and `Deform.IsRigid`).
* `IsCDeformation` — the `∂/∂c` normalisation (`ω¹₍₁₎ω = 0`, `ω¹₍₃₎ω = ½𝟙`, graded), with
  `not_isTrivial_of_isCDeformation` and `not_isRigidGraded_of_isCDeformation`.
* `exists_isCoboundary_on_gauge_line` — the converse: the gauge line is exactly a line.
* `smul₁_scaling_omega_one`, `smul₁_scaling_omega_three`, `scaling_on_gauge_line` — the
  non-vacuity cross-check: `δL₀` sits on the gauge line at `μ = 2`, computed independently from
  `NonzeroDeform.smul₁_scalingDeformation_homog` (`u¹₍ₙ₎v = (n+1)u₍ₙ₎v`), which never mentions
  `φω = μω`.

## ⚠ What is missing here, precisely (since supplied downstream)

`IsCDeformation c` is a predicate and this file does **not** inhabit it.  (It is inhabited
downstream by `VOA.VirPoly.cDeformation c`, `Examples/VirasoroCDefFinal.lean`, along route 2
below; the rest of this section records the obstruction as it stood when this file was written.)
The obstruction is not
the *definition* of `∂_c` — the underlying graded space of `V(c,0)` is `c`-independent in the
sense that matters (`Examples/VirasoroPartitionBasis`: the sorted creation words are independent
at every `c`, with a `c`-free index set) — but the *vertex-algebra structure carrying the
derivative*.  Two routes, both real projects:

1. **Square-zero extension.**  `E(c) := U(𝔙𝔦𝔯) ⧸ J₂(c)` with `J₂(c)` generated by `{Lₙ : n ≥ -1}`
   and `(ιC − c)²`.  Left multiplication makes `E(c)` a `𝔙𝔦𝔯`-module with *no* new work — the
   `c`-dependence sits entirely in the ideal — and `ε := ιC − c` is a central square-zero
   operator, so `E(c)` is a `ℂ[ε]/ε²`-module and the word fields, their locality and the
   reconstruction all go through with the scalar `(c/12)·1` of `VirasoroField.YomegaVir_unit`
   replaced by the *operator* `(1/12)·ιC`.  Extracting `Y₁` from `E(c)` then needs
   `E(c) ≅ V(c,0) ⊕ ε·V(c,0)`, i.e. `ann_E(ε) = εE` — a PBW-flavoured freeness statement.  That
   is the genuinely hard input, and `Examples/VirasoroTopSymbol`'s Fock realisation does not
   obviously extend to central charge `c + ε`.
2. **Differentiating the family.**  Transport along the partition basis and differentiate the
   structure constants in `c`.  Needs the family, its polynomiality in `c`, and honest
   differentiation — strictly more machinery than route 1.

Two facts worth recording for whoever attempts this.  The first **is** proved here (§1b): `Y`
regarded as a cochain is `δ(id)`, hence satisfies `Deform.JacobiAx` (`jacobiAx_Y`) — the
first-order identity is the polarisation of the quadratic one — and fails only the vacuum
axiom.  The second is ⚠ **checked by hand only, not a theorem**: a cochain supported at the
single tridegree `(2,2,0)` is *not* a cocycle (the `ℓ = 0`, `m = 3`, `n = 1`, `u = v = x = ω`
instance gives `2λ𝟙` on the left and `6λ𝟙` on the right), so the `c = 0` detector
`VirDefLow.deformationSpaceAt_two_two_zero_ne_zero_of_witness` cannot be triggered by a cochain
concentrated where it looks.  Any construction must populate other tridegrees too — for `∂_c`,
`(3,2,0)` among them, where the value is `∂_c[(L₋₃𝟙)₍₄₎ω] = ∂_c(−2c·𝟙) = −2·𝟙`.

## ⚠ Not claimed

That the deformation dies in the **simple** quotient `L(c,0)` at minimal-model central charges —
which is where the real rigidity target (and the Linshaw–Qi statement, which is about *simple*
affine VOAs, never universal ones) lives.  That is a separate theorem about
`Examples/VirasoroSimple.virasoroSimple`, and nothing here bears on it.

## Status
No `sorry`, no `admit`, no `native_decide`, no `unsafe`, no new axioms;
`#print axioms` = `[propext, Classical.choice, Quot.sound]` on every declaration (in particular
`VOA.pbw` is **not** used).  Imported by the umbrella `VOA/Examples.lean`.

## Dependencies
`Examples.VirasoroDeformationLow` (`gradingVir_two`, `omegaVir_ne_zero_all`, and the `(2,2,·)`
coboundary computation this file completes), `Examples.NonzeroDeformation`
(`scalingDeformation`, `smul₁_scalingDeformation_homog`, `isTrivial_scalingDeformation`), and
through them `Core.DeformationGraded` and `Examples.VirasoroInstance`.
-/

set_option linter.style.longLine false

namespace VOA

namespace VirCDef

open Module (End)
open Deform
open VOA.VirModule

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1  The two structure constants at `ω`, for an arbitrary VOA -/

/-- `Lₙ|0⟩ = 0` for `n ≥ -1`: the creation axiom VA3 read through `Lₙ = ω₍ₙ₊₁₎`. -/
theorem L_vacuum_of_neg_one_le (W : VertexOperatorAlgebra 𝒱) {n : ℤ} (hn : -1 ≤ n) :
    W.L n W.vacuum = 0 := by
  have h : W.L n W.vacuum = W.smul W.conformalVector (n + 1) W.vacuum := rfl
  rw [h]
  exact W.toPreVertexAlgebra.smul_vacuum_nonneg W.conformalVector (by omega)

/-- `L₋₂|0⟩ = ω`: the creation axiom VA3 at `n = -1`. -/
theorem L_negTwo_vacuum (W : VertexOperatorAlgebra 𝒱) :
    W.L (-2) W.vacuum = W.conformalVector := by
  have h : W.L (-2) W.vacuum = W.smul W.conformalVector (-1) W.vacuum := by
    rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def]
    norm_num
  rw [h, PreVertexAlgebra.smul_vacuum_neg_one]

/-- **The `c`-free structure constant.** `ω₍₁₎ω = L₀ω = 2ω`: the conformal weight of `ω` is
`2`, and this carries **no** central charge.  It is the fact that pins the scale of `ω` and hence
makes the `∂_c` direction non-gaugeable. -/
theorem conformal_smul_one (W : VertexOperatorAlgebra 𝒱) :
    W.smul W.conformalVector 1 W.conformalVector = (2 : ℂ) • W.conformalVector := by
  have h : W.smul W.conformalVector 1 W.conformalVector = W.L 0 W.conformalVector := rfl
  rw [h, W.L_zero_grading _ W.conformal_mem]
  norm_num

/-- **The structure constant that carries `c`.** `ω₍₃₎ω = L₂L₋₂|0⟩ = (c/2)|0⟩`, from VOA1 at
`(m,n) = (2,-2)`: the central term is `(2³−2)/12·c = c/2`, and `L₂|0⟩ = L₀|0⟩ = 0`. -/
theorem conformal_smul_three (W : VertexOperatorAlgebra 𝒱) :
    W.smul W.conformalVector 3 W.conformalVector = (W.centralCharge / 2) • W.vacuum := by
  have key := congrArg (fun T : End ℂ 𝒱 => T W.vacuum) (W.L_virasoro 2 (-2))
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply] at key
  rw [L_vacuum_of_neg_one_le W (by norm_num : (-1 : ℤ) ≤ 2), map_zero, sub_zero,
    L_negTwo_vacuum, show ((2 : ℤ) + -2) = 0 from by norm_num,
    L_vacuum_of_neg_one_le W (by norm_num : (-1 : ℤ) ≤ 0), smul_zero, zero_add, if_pos rfl,
    show ((2 : ℤ) : ℂ) ^ 3 - ((2 : ℤ) : ℂ) = 6 from by norm_num] at key
  have hL : W.L 2 W.conformalVector = W.smul W.conformalVector 3 W.conformalVector := rfl
  rw [← hL, key, LinearMap.smul_apply, Module.End.one_apply]
  congr 1
  ring

/-! ## §1b  `Y` is the coboundary of the identity

A structural remark that orients the whole file, and that costs two lines given
`NonzeroDeform.jacobiAx_deltaCochain` (which needs *no* hypothesis on `φ`): the undeformed `Y`,
regarded as a cochain, is `δ(id)`.  Hence `Y` **satisfies the order-`t` Jacobi identity** — the
first-order identity is the polarisation of the quadratic one, so substituting `Y₁ = Y` just
doubles both sides.  What stops `Y` from being a first-order deformation is only that `id` does
not kill the vacuum: `Y(𝟙,z) = 1 ≠ 0` violates `Deform.FirstOrderDeformation.vacuum_Y1`.

The moral for the rest of the file: the "gauge group" acting on cochains is *all*
grade-preserving `φ`, and `Deform.IsCoboundary` cuts it down by exactly one condition, `φ𝟙 = 0`.
That single condition is what makes the gauge line of §2 a line rather than a plane. -/

/-- **`δ(id) = Y`.**  The coboundary cochain of the identity map is the undeformed state–field
correspondence itself. -/
theorem deltaCochain_id (W : VertexOperatorAlgebra 𝒱) :
    NonzeroDeform.deltaCochain W LinearMap.id = (W.Y : Cochain 𝒱) := by
  refine cochain_ext fun u n v => ?_
  rw [NonzeroDeform.cmode_deltaCochain]
  simp only [LinearMap.id_coe, id_eq, cmode_def, ← PreVertexAlgebra.smul_def]
  abel

/-- **`Y` satisfies the order-`t` Jacobi identity.**  Immediate from `δ(id) = Y` and the fact
that `NonzeroDeform.jacobiAx_deltaCochain` needs no hypothesis on `φ`.  `Y` is nevertheless not a
first-order deformation: it fails `vacuum_Y1`, since `Y(𝟙,z) = 1`. -/
theorem jacobiAx_Y (W : VertexOperatorAlgebra 𝒱) : JacobiAx W (W.Y : Cochain 𝒱) := by
  rw [← deltaCochain_id]
  exact NonzeroDeform.jacobiAx_deltaCochain W LinearMap.id

/-! ## §2  The gauge line at `ω`

A field redefinition `φ` is grade-preserving and kills `𝟙`.  If moreover `𝒱₂ = ℂ·ω` — true for
`V(c,0)`, `gradingVir_two` — then `φ` is *one scalar* on the two graded pieces that the pair
`(ω₍₁₎ω, ω₍₃₎ω)` sees: `φω = μω`, and `φ` kills `𝒱₀ = ℂ·𝟙` outright.  Both components of `δφ`
are then forced, and they move **together** along a single line parametrised by `μ`:

`δφ(ω,1,ω) = 2μ·ω`,  `δφ(ω,3,ω) = μc·𝟙`.

That is the whole content: coboundaries cannot change the weight-`2` product and the central
term independently. -/

/-- **The gauge line.**  For a coboundary `f = δφ` on a VOA whose weight-`2` space is the
line `ℂ·ω`, the two products `ω¹₍₁₎ω` and `ω¹₍₃₎ω` are determined by a **single** scalar `μ`
(namely `φω = μω`):

`ω¹₍₁₎ω = 2μ·ω`  and  `ω¹₍₃₎ω = μc·𝟙`.

The two entries `(2μ, μc)` are *proportional*: no field redefinition can switch on the central
term while leaving the weight-`2` product alone.  This is the separating invariant. -/
theorem cmode_conformal_of_isCoboundary (W : VertexOperatorAlgebra 𝒱)
    (hV2 : W.grading 2 = ℂ ∙ W.conformalVector) {f : Cochain 𝒱} (hf : IsCoboundary W f) :
    ∃ μ : ℂ,
      cmode f W.conformalVector 1 W.conformalVector = (2 * μ) • W.conformalVector ∧
      cmode f W.conformalVector 3 W.conformalVector = (μ * W.centralCharge) • W.vacuum := by
  obtain ⟨φ, hφ0, hφg, hφ⟩ := hf
  -- `φ` acts on `𝒱₂ = ℂ·ω` by a scalar.
  have hωspan : φ W.conformalVector ∈ ℂ ∙ W.conformalVector := by
    rw [← hV2]; exact hφg 2 _ W.conformal_mem
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hωspan
  -- `φ` kills `𝒱₀ = ℂ·𝟙`, because `φ𝟙 = 0`.
  have hφgrade0 : ∀ x ∈ W.grading 0, φ x = 0 := by
    intro x hx
    rw [W.vacuum_grade] at hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, hφ0, smul_zero]
  refine ⟨μ, ?_, ?_⟩
  · -- mode `1`: the weight-`2` product `ω₍₁₎ω = 2ω`.
    rw [cmode_def, hφ, ← hμ, conformal_smul_one, PreVertexAlgebra.smul_smul_left,
      PreVertexAlgebra.smul_smul_right, conformal_smul_one, map_smul, ← hμ]
    module
  · -- mode `3`: the central term `ω₍₃₎ω = (c/2)·𝟙`, and `φ` kills it.
    have hker : φ (W.smul W.conformalVector 3 W.conformalVector) = 0 := by
      refine hφgrade0 _ ?_
      have h := W.toPreVertexAlgebra.smul_mem_grading W.conformal_mem W.conformal_mem (3 : ℤ)
      have he : (2 : ℤ) + 2 - 3 - 1 = 0 := by norm_num
      rwa [he] at h
    rw [cmode_def, hφ, hker, sub_zero, ← hμ, PreVertexAlgebra.smul_smul_left,
      PreVertexAlgebra.smul_smul_right, conformal_smul_three]
    module

/-- **The separating criterion, general form.**  A cochain that leaves the weight-`2`
product `ω₍₁₎ω` undeformed but *does* deform the central term `ω₍₃₎ω` is **not** a coboundary.

Proof in one line: the gauge line forces `2μ·ω = 0`, hence `μ = 0` since `ω ≠ 0`, hence the
`ω¹₍₃₎ω` entry is `0·c·𝟙 = 0`. -/
theorem not_isCoboundary_of_conformal_witness (W : VertexOperatorAlgebra 𝒱)
    (hV2 : W.grading 2 = ℂ ∙ W.conformalVector) (hω : W.conformalVector ≠ 0) {f : Cochain 𝒱}
    (h1 : cmode f W.conformalVector 1 W.conformalVector = 0)
    (h3 : cmode f W.conformalVector 3 W.conformalVector ≠ 0) : ¬ IsCoboundary W f := by
  intro hf
  obtain ⟨μ, hμ1, hμ3⟩ := cmode_conformal_of_isCoboundary W hV2 hf
  rw [h1] at hμ1
  have hμ0 : μ = 0 := by
    rcases smul_eq_zero.mp hμ1.symm with h | h
    · rcases mul_eq_zero.mp h with h2 | h2
      · exact absurd h2 (by norm_num)
      · exact h2
    · exact absurd h hω
  exact h3 (by rw [hμ3, hμ0, zero_mul, zero_smul])

/-! ## §3  Specialisation to `V(c,0)`, at **every** central charge -/

section Virasoro

variable (c : ℂ)

/-- `𝒱₂ = ℂ·ω` for `V(c,0)`, in the `VertexOperatorAlgebra` spelling (`VirDefLow.gradingVir_two`
with `(virasoroVOA c).conformalVector = ω` unfolded). -/
theorem gradingVir_two_eq_span_conformal :
    (virasoroVOA c).grading 2 = ℂ ∙ (virasoroVOA c).conformalVector :=
  VirDefLow.gradingVir_two c

/-- `ω₍₁₎ω = 2ω` on `V(c,0)`, spelled with `omegaVir`. -/
theorem smulVir_omega_one :
    (virasoroVOA c).smul (omegaVir c) 1 (omegaVir c) = (2 : ℂ) • omegaVir c :=
  conformal_smul_one (virasoroVOA c)

/-- `ω₍₃₎ω = (c/2)|0⟩` on `V(c,0)`, spelled with `omegaVir`.  Agrees with
`VirDefLow.Lop_two_omega` through `VirDefLow.smulVir_omega`. -/
theorem smulVir_omega_three :
    (virasoroVOA c).smul (omegaVir c) 3 (omegaVir c) = (c / 2) • vacVec c :=
  conformal_smul_three (virasoroVOA c)

/-- **The gauge line for `V(c,0)`.**  Every *trivial* first-order deformation `D` of `V(c,0)`
satisfies, for one and the same scalar `μ`,

`ω¹₍₁₎ω = 2μ·ω`  and  `ω¹₍₃₎ω = μc·|0⟩`.

Unconditional in `c`, and unconditional in `D` beyond triviality. -/
theorem smul₁_omega_of_isTrivial (D : FirstOrderDeformation (virasoroVOA c))
    (hD : D.IsTrivial) :
    ∃ μ : ℂ,
      D.smul₁ (omegaVir c) 1 (omegaVir c) = (2 * μ) • omegaVir c ∧
      D.smul₁ (omegaVir c) 3 (omegaVir c) = (μ * c) • vacVec c :=
  cmode_conformal_of_isCoboundary (virasoroVOA c) (gradingVir_two_eq_span_conformal c) hD

/-- **The separating theorem for `V(c,0)`.**  A first-order deformation that leaves the
weight-`2` product `ω₍₁₎ω = 2ω` alone but *does* deform the central term `ω₍₃₎ω = (c/2)|0⟩` is
**not** trivial — at every central charge, including `c = 0`.

This is the mathematical heart: it says the `∂/∂c` direction is not a field redefinition.  The
`ω₍₁₎ω` slot is what makes the argument work: rescaling `ω ↦ (1+tμ)ω` *does* move the central
term (by `μc`), but it moves the weight-`2` product too (by `2μ`), and `∂_c` moves only the
first.  Equivalently: `[Lₘ,Lₙ] = (m−n)L_{m+n} + …` is **not** invariant under rescaling `L`, which
is exactly why the Virasoro family in `c` is not a family of isomorphic vertex algebras — unlike,
say, the Heisenberg family in the level, where rescaling the generator *is* available. -/
theorem not_isTrivial_of_omega_witness (D : FirstOrderDeformation (virasoroVOA c))
    (h1 : D.smul₁ (omegaVir c) 1 (omegaVir c) = 0)
    (h3 : D.smul₁ (omegaVir c) 3 (omegaVir c) ≠ 0) : ¬ D.IsTrivial :=
  not_isCoboundary_of_conformal_witness (virasoroVOA c) (gradingVir_two_eq_span_conformal c)
    (VirDefLow.omegaVir_ne_zero_all c) h1 h3

/-- **…and such a deformation, if graded, refutes `IsRigidGraded`.**  `IsRigidGraded` is the
notion in which grade-preservation is a hypothesis on **both** sides (unlike `Deform.IsRigid`,
which `NonzeroDeform.not_isRigid_virasoroVOA` already refutes with the *ungraded* `δL₁`), so this
is the meaningful rigidity statement.  Its hypotheses are met for every `c` by
`VOA.VirPoly.cDeformation c` (`Examples/VirasoroCDefFinal.lean`), which gives
`VOA.VirPoly.not_isRigidGraded_virasoroVOA`. -/
theorem not_isRigidGraded_of_omega_witness (D : FirstOrderDeformation (virasoroVOA c))
    (hgr : D.IsGraded)
    (h1 : D.smul₁ (omegaVir c) 1 (omegaVir c) = 0)
    (h3 : D.smul₁ (omegaVir c) 3 (omegaVir c) ≠ 0) : ¬ IsRigidGraded (virasoroVOA c) :=
  fun hR => not_isTrivial_of_omega_witness c D h1 h3 (hR D hgr)

/-- The same witness also refutes the (stronger) ungraded `Deform.IsRigid`. -/
theorem not_isRigid_of_omega_witness (D : FirstOrderDeformation (virasoroVOA c))
    (h1 : D.smul₁ (omegaVir c) 1 (omegaVir c) = 0)
    (h3 : D.smul₁ (omegaVir c) 3 (omegaVir c) ≠ 0) : ¬ IsRigid (virasoroVOA c) :=
  fun hR => not_isTrivial_of_omega_witness c D h1 h3 (hR D)

/-! ## §4  The `∂/∂c` normalisation, and what it would buy -/

/-- **The `∂/∂c` deformation, characterised by its value on the generators.**  `V(c,0)` is
generated by `ω`, and `c` enters the structure constants **only** through the central term of
`Lop_bracket`, linearly.  Differentiating `Y(ω,z)ω` in `c` therefore gives exactly

`ω¹₍₃₎ω = ½|0⟩`,   `ω¹₍ₙ₎ω = 0` for `n ≠ 3`

(only `n = 3` sees `(c/2)|0⟩`; `ω₍₁₎ω = 2ω`, `ω₍₀₎ω = L₋₃|0⟩` and `ω₍₋₁₎ω = L₋₂ω` carry no `c`).
`IsCDeformation c D` records the two of those values that the separating theorem needs, together
with gradedness (`c` does not move the grading, so `∂_c Y` is graded).

⚠ This is a **predicate**, not a construction: nothing in this file asserts that it is
inhabited.  It is inhabited downstream, at every `c`, by `VOA.VirPoly.cDeformation c`
(`VOA.VirPoly.isCDeformation_cDeformation`, `Examples/VirasoroCDefFinal.lean`). -/
def IsCDeformation (D : FirstOrderDeformation (virasoroVOA c)) : Prop :=
  D.IsGraded ∧
    D.smul₁ (omegaVir c) 1 (omegaVir c) = 0 ∧
    D.smul₁ (omegaVir c) 3 (omegaVir c) = (2⁻¹ : ℂ) • vacVec c

/-- The `∂/∂c` value at mode `3` is nonzero: `½|0⟩ ≠ 0` because `|0⟩ ≠ 0` (`vacVec_ne_zero`,
`pbw`-free). -/
theorem half_vacVec_ne_zero : (2⁻¹ : ℂ) • vacVec c ≠ 0 := by
  intro h
  rcases smul_eq_zero.mp h with h1 | h1
  · exact absurd h1 (by norm_num)
  · exact vacVec_ne_zero c h1

/-- **`∂_c Y` is not trivial.**  Any deformation with the `∂/∂c` normalisation is a
non-trivial first-order deformation of `V(c,0)`, at every central charge. -/
theorem not_isTrivial_of_isCDeformation {D : FirstOrderDeformation (virasoroVOA c)}
    (hD : IsCDeformation c D) : ¬ D.IsTrivial :=
  not_isTrivial_of_omega_witness c D hD.2.1 (by rw [hD.2.2]; exact half_vacVec_ne_zero c)

/-- **The main theorem, conditional on the construction.**  If the `∂/∂c` deformation exists as
a `Deform.FirstOrderDeformation` then `V(c,0)` is **not** `IsRigidGraded`, at every `c`.  The
construction is `VOA.VirPoly.cDeformation`; the unconditional form is
`VOA.VirPoly.not_isRigidGraded_virasoroVOA` (`Examples/VirasoroCDefFinal.lean`). -/
theorem not_isRigidGraded_of_isCDeformation {D : FirstOrderDeformation (virasoroVOA c)}
    (hD : IsCDeformation c D) : ¬ IsRigidGraded (virasoroVOA c) :=
  fun hR => not_isTrivial_of_isCDeformation c hD (hR D hD.1)

/-- The existential form: an inhabitant of `IsCDeformation` refutes `IsRigidGraded`. -/
theorem not_isRigidGraded_of_exists_isCDeformation
    (h : ∃ D : FirstOrderDeformation (virasoroVOA c), IsCDeformation c D) :
    ¬ IsRigidGraded (virasoroVOA c) := by
  obtain ⟨D, hD⟩ := h
  exact not_isRigidGraded_of_isCDeformation c hD

/-! ## §5  Non-vacuity: the gauge line is *occupied*

The gauge line of §2 would be worthless information if no deformation ever sat on it with
`μ ≠ 0`.  The repository's `NonzeroDeform.scalingDeformation` (`δL₀`) sits on it at `μ = 2`, and
computing its two entries from `smul₁_scalingDeformation_homog` — an **independent** route, via
`u¹₍ₙ₎v = (n+1)u₍ₙ₎v`, that never mentions `φω = μω` — reproduces `(2μ, μc) = (4, 2c)` exactly.
That is a genuine cross-check of §2, not a restatement of it. -/

/-- `δL₀` at mode `1`: `ω¹₍₁₎ω = 2·ω₍₁₎ω = 4ω`. -/
theorem smul₁_scaling_omega_one :
    (NonzeroDeform.scalingDeformation (virasoroVOA c)).smul₁ (omegaVir c) 1 (omegaVir c)
      = (4 : ℂ) • omegaVir c := by
  rw [NonzeroDeform.smul₁_scalingDeformation_homog (virasoroVOA c)
      (omegaVir_mem_gradingVir_two c) (omegaVir_mem_gradingVir_two c) 1,
    smulVir_omega_one]
  push_cast
  module

/-- `δL₀` at mode `3`: `ω¹₍₃₎ω = 4·ω₍₃₎ω = 2c·|0⟩`. -/
theorem smul₁_scaling_omega_three :
    (NonzeroDeform.scalingDeformation (virasoroVOA c)).smul₁ (omegaVir c) 3 (omegaVir c)
      = (2 * c) • vacVec c := by
  rw [NonzeroDeform.smul₁_scalingDeformation_homog (virasoroVOA c)
      (omegaVir_mem_gradingVir_two c) (omegaVir_mem_gradingVir_two c) 3,
    smulVir_omega_three]
  push_cast
  module

/-- **The cross-check.**  `δL₀` realises the gauge line of §2 at `μ = 2`: its two entries are
`(2μ)·ω = 4ω` and `(μc)·|0⟩ = 2c·|0⟩`, computed here by the independent closed form
`u¹₍ₙ₎v = (n+1)u₍ₙ₎v`.  So §2 is not vacuous, and `μ` genuinely ranges over nonzero values. -/
theorem scaling_on_gauge_line :
    (NonzeroDeform.scalingDeformation (virasoroVOA c)).smul₁ (omegaVir c) 1 (omegaVir c)
        = (2 * (2 : ℂ)) • omegaVir c ∧
      (NonzeroDeform.scalingDeformation (virasoroVOA c)).smul₁ (omegaVir c) 3 (omegaVir c)
        = ((2 : ℂ) * c) • vacVec c := by
  refine ⟨?_, smul₁_scaling_omega_three c⟩
  rw [smul₁_scaling_omega_one]
  norm_num

/-- **The gauge line is exactly a line — the sharp converse of §2.**  For *every* scalar `μ`
there is an honest coboundary realising the pair `(2μ·ω, μc·|0⟩)`, namely `(μ/2)·δL₀`.  Together
with `cmode_conformal_of_isCoboundary` this pins the image of the field redefinitions in the two
slots `(ω¹₍₁₎ω, ω¹₍₃₎ω)` down to **exactly** the line `ℂ·(2ω, c·|0⟩)` — no smaller, no larger.
So `not_isTrivial_of_omega_witness` is sharp: `(0, nonzero)` is off that line, and every point on
it is attained. -/
theorem exists_isCoboundary_on_gauge_line (μ : ℂ) :
    ∃ f : Cochain (VirUniv c), IsCoboundary (virasoroVOA c) f ∧
      cmode f (omegaVir c) 1 (omegaVir c) = (2 * μ) • omegaVir c ∧
      cmode f (omegaVir c) 3 (omegaVir c) = (μ * c) • vacVec c := by
  refine ⟨(μ / 2) • (NonzeroDeform.scalingDeformation (virasoroVOA c)).Y1,
    IsCoboundary.smul _ (NonzeroDeform.isTrivial_scalingDeformation (virasoroVOA c)), ?_, ?_⟩
  · rw [cmode_smul_cochain, cmode_Y1, smul₁_scaling_omega_one, smul_smul]
    congr 1
    ring
  · rw [cmode_smul_cochain, cmode_Y1, smul₁_scaling_omega_three, smul_smul]
    congr 1
    ring

/-- **`δL₀` is not the `∂/∂c` deformation** — it fails the `ω¹₍₁₎ω = 0` normalisation, since
`4ω ≠ 0`.  (It could not be: `δL₀` is trivial, `NonzeroDeform.isTrivial_scalingDeformation`.) -/
theorem not_isCDeformation_scalingDeformation :
    ¬ IsCDeformation c (NonzeroDeform.scalingDeformation (virasoroVOA c)) := by
  rintro ⟨-, h1, -⟩
  rw [smul₁_scaling_omega_one] at h1
  rcases smul_eq_zero.mp h1 with h | h
  · exact absurd h (by norm_num)
  · exact VirDefLow.omegaVir_ne_zero_all c h

end Virasoro

end VirCDef

end VOA
