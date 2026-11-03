/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Core.LieAlgebraV1
import VOA.Core.DeformationGraded
import Mathlib.Algebra.Lie.Cochain
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.DirectSum.Decomposition

/-!
# `H²(𝒱₁, 𝒱₁)` and the normalisation of a graded first-order deformation

This file supplies **Piece 1** of the split of Linshaw–Qi's Theorem 5.1 (see
`Examples/AffineSl2Rigidity43.lean`): the *normalisation* step that their equation (3) performs
silently, citing [KQ] §6.2.  It is a statement about the weight-one Lie algebra `𝒱₁` **and
nothing else** — no level, no singular vector, no mode other than `₍₀₎`, no reference to `𝒱`
outside `𝒱₁`.

## The mathematical content

For a **graded** first-order deformation `D` of a VOA `W`, VA1 puts `D.smul₁ a 0 b` in
`𝒱_{1+1-0-1} = 𝒱₁` when `a, b ∈ 𝒱₁`.  So

`ω(a,b) := a¹₍₀₎b`

is a bilinear map `𝒱₁ × 𝒱₁ → 𝒱₁`, i.e. a 2-cochain of the Lie algebra `(𝒱₁, ⁅a,b⁆ = a₍₀₎b)`
(`Core.LieAlgebraV1`) with **adjoint** coefficients.  The `ℓ = m = n = 0` case of the deformed
Jacobi identity `Deform.FirstOrderDeformation.jacobi` says exactly two things about `ω`:

* `ω(a,a)` is **central** in `𝒱₁`, hence `0` when `𝒱₁` is centreless — so `ω` is alternating;
* `ω` is a **Chevalley–Eilenberg 2-cocycle**, `d₂₃ ω = 0`.

`WeightOneH2Vanishes W` then says every such cocycle is a coboundary `d₁₂ ψ`.  Subtracting the
induced VOA coboundary `δφ` (with `φ` the extension of `ψ` by zero off `𝒱₁`) kills the `x^{-1}`
coefficient of `Y₁` on the weight-one space — which is the first clause of Linshaw–Qi's
equation (3), and the condition under which their constant `c` is defined and gauge-invariant.

## Signs: Mathlib's convention already matches the repository's

Mathlib's `LieModule.Cohomology.d₁₂` (Carnahan, `Mathlib/Algebra/Lie/Cochain.lean`) is

`d₁₂ ψ x y = ⁅x, ψ y⁆ - ⁅y, ψ x⁆ - ψ ⁅x,y⁆`,

and the repository's coboundary `Deform.IsCoboundary` reads, at mode `0` on `𝒱₁`,

`(φa)₍₀₎b - φ(a₍₀₎b) + a₍₀₎(φb) = ⁅ψa,b⁆ - ψ⁅a,b⁆ + ⁅a,ψb⁆ = d₁₂ψ a b`

using `⁅ψa,b⁆ = -⁅b,ψa⁆` (antisymmetry, `bracketV1_antisymm`).  The two agree **on the nose**,
so no sign-translation layer is needed; this is `coboundary_weightOne_eq_d₁₂` below.

## Main declarations

### §1 — Whitehead's second lemma for `𝔰𝔩₂`, as a finite computation

* `Sl2Whitehead.whitehead2_of_sl2Basis` — `H²(𝔤,𝔤) = 0` for any `ℂ`-Lie algebra `𝔤` with a
  basis `(e,h,f)` forming an `𝔰𝔩₂`-triple.  Mathlib has **no** Lie-algebra cohomology beyond the
  low-degree cochain complex and **no** Whitehead lemma (`grep -ri whitehead Mathlib/` returns
  only topology), so this is built here.  The proof is the explicit primitive
  `ψe = (B₂ - A₁/2)e + (A₃/4)f`, `ψh = C₂e - (A₁/2)h + A₂f`, `ψf = (C₁/4)e`
  in the coordinates `ω(e,h) = A₁e+A₂h+A₃f`, `ω(e,f) = B₁e+B₂h+B₃f`, `ω(h,f) = C₁e+C₂h+C₃f`;
  the cocycle condition contributes exactly the three scalar relations
  `C₂ + B₁ = 0`, `C₃ = A₁`, `B₃ + A₂ = 0` (`Sl2Whitehead.cocycle_rel`).
* `Sl2Whitehead.centreless_of_sl2Basis` — an `𝔰𝔩₂`-triple basis makes `𝔤` centreless.

### §2 — the bridge from a graded deformation to a Lie 2-cocycle

* `weightOneBilin`, `weightOneCochain` — `ω(a,b) = a¹₍₀₎b` as a Lie 2-cochain.
* `weightOneCochain_mem_twoCocycle` — the `ℓ = m = n = 0` Jacobi identity **is** `d₂₃ ω = 0`.
* `WeightOneH2Vanishes` — Piece 1, as a predicate on `W` mentioning only `𝒱₁` and `₍₀₎`.
* `weightOneH2Vanishes_of_sl2Basis` — Piece 1 is a **theorem**, not a hypothesis, for any `W`
  whose weight-one Lie algebra carries an `𝔰𝔩₂`-triple basis.

### §3 — extending `ψ : 𝒱₁ → 𝒱₁` to a grade-preserving `φ : 𝒱 → 𝒱`

* `gradedProj`, `extendWeightOne`, `gradePreserving_extendWeightOne`,
  `extendWeightOne_vacuum`, `extendWeightOne_of_mem_one`.

## Status

No `sorry`, no `admit`, no `native_decide`, no new axioms, no `VOA.pbw`.

## References
* V. Kovalchuk and F. Qi, *First-order deformations of freely generated vertex algebras*,
  arXiv:2408.16309, §6.2 — the `H²(𝔤,𝔤) = 0` normalisation this file formalises.
* A. R. Linshaw and F. Qi, *Deformation rigidity of some simple affine VOAs*,
  arXiv:2601.12017v2, equation (3).
* S. Carnahan, `Mathlib/Algebra/Lie/Cochain.lean` — `twoCochain`, `d₁₂`, `d₂₃`, `twoCocycle`.
* Gannon §5.2.1 — the Lie algebra `𝒱₁`.
-/

open LieModule.Cohomology Module

namespace VOA

/-! ## §1  Whitehead's second lemma for `𝔰𝔩₂`

Everything in this section is pure Lie algebra: no VOA appears.  The target is

`H²(𝔤,𝔤) = 0` for `𝔤` a `ℂ`-Lie algebra with an `𝔰𝔩₂`-triple basis,

phrased — since Mathlib's `Cochain.lean` has no coboundary submodule and no cohomology — as
"every 2-cocycle is `d₁₂` of a 1-cochain". -/

namespace Sl2Whitehead

variable {g : Type*} [LieRing g] [LieAlgebra ℂ g]

/-- Reading the three coefficients off a vanishing combination of a `Fin 3` basis. -/
theorem coeff_zero_of_comb (b : Basis (Fin 3) ℂ g) {x y z : ℂ}
    (h : x • b 0 + y • b 1 + z • b 2 = 0) : x = 0 ∧ y = 0 ∧ z = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg (fun v => b.repr v 0) h
  · simpa using congrArg (fun v => b.repr v 1) h
  · simpa using congrArg (fun v => b.repr v 2) h

/-- Expansion of a vector in a `Fin 3` basis. -/
theorem basis_expand (b : Basis (Fin 3) ℂ g) (v : g) :
    v = b.repr v 0 • b 0 + b.repr v 1 • b 1 + b.repr v 2 • b 2 := by
  conv_lhs => rw [← b.sum_repr v]
  rw [Fin.sum_univ_three]

section Brackets

variable (b : Basis (Fin 3) ℂ g) (ht : IsSl2Triple (b 1) (b 0) (b 2))
include ht

/-- `⁅h,e⁆ = 2e`. -/
theorem br_he : ⁅(b 1 : g), b 0⁆ = (2 : ℂ) • b 0 := ht.lie_h_e_smul ℂ

/-- `⁅h,f⁆ = -2f`. -/
theorem br_hf : ⁅(b 1 : g), b 2⁆ = -((2 : ℂ) • b 2) := ht.lie_lie_smul_f (R := ℂ)

/-- `⁅e,f⁆ = h`. -/
theorem br_ef : ⁅(b 0 : g), b 2⁆ = b 1 := ht.lie_e_f

/-- `⁅e,h⁆ = -2e`. -/
theorem br_eh : ⁅(b 0 : g), b 1⁆ = -((2 : ℂ) • b 0) := by rw [← lie_skew, br_he b ht]

/-- `⁅f,h⁆ = 2f`. -/
theorem br_fh : ⁅(b 2 : g), b 1⁆ = (2 : ℂ) • b 2 := by rw [← lie_skew, br_hf b ht, neg_neg]

/-- `⁅f,e⁆ = -h`. -/
theorem br_fe : ⁅(b 2 : g), b 0⁆ = - b 1 := by rw [← lie_skew, br_ef b ht]

/-- **An `𝔰𝔩₂`-triple basis makes `𝔤` centreless.**  Needed for the alternating property of
the weight-one 2-cochain in §2, and it is the only route to that property that does not require
porting `Core.SkewSymmetry` to the deformed setting. -/
theorem centreless_of_sl2Basis (z : g) (hz : ∀ x : g, ⁅z, x⁆ = 0) : z = 0 := by
  have hzc := basis_expand b z
  set z₁ := b.repr z 0
  set z₂ := b.repr z 1
  set z₃ := b.repr z 2
  -- `⁅z,f⁆ = 0` gives `z₁ = 0` and `z₂ = 0`
  have hf : (0 : ℂ) • b 0 + z₁ • b 1 + (-(2 * z₂)) • b 2 = 0 := by
    rw [← hz (b 2)]
    conv_rhs => rw [hzc]
    simp only [add_lie, smul_lie, lie_self, br_ef b ht, br_hf b ht]
    module
  obtain ⟨-, h1, h2⟩ := coeff_zero_of_comb b hf
  -- `⁅z,e⁆ = 0` gives `z₃ = 0`
  have he : (2 * z₂) • b 0 + (-z₃) • b 1 + (0 : ℂ) • b 2 = 0 := by
    rw [← hz (b 0)]
    conv_rhs => rw [hzc]
    simp only [add_lie, smul_lie, lie_self, br_he b ht, br_fe b ht]
    module
  obtain ⟨-, h3, -⟩ := coeff_zero_of_comb b he
  rw [hzc, show z₁ = 0 from h1, show z₂ = 0 from by linear_combination -h2 / 2,
    show z₃ = 0 from by linear_combination -h3]
  module

/-- `d₁₂ψ(e,h) = -2q₂ e + (q₃+2p₂) h + 4p₃ f`. -/
theorem d12_eh {ψ : g →ₗ[ℂ] g} {p₁ p₂ p₃ q₁ q₂ q₃ : ℂ}
    (hp : ψ (b 0) = p₁ • b 0 + p₂ • b 1 + p₃ • b 2)
    (hq : ψ (b 1) = q₁ • b 0 + q₂ • b 1 + q₃ • b 2) :
    d₁₂ ℂ g g ψ (b 0) (b 1)
      = (-2 * q₂) • b 0 + (q₃ + 2 * p₂) • b 1 + (4 * p₃) • b 2 := by
  rw [d₁₂_apply_apply, br_eh b ht, map_neg, map_smul, hp, hq]
  simp only [lie_add, lie_smul, lie_self, br_eh b ht, br_ef b ht, br_he b ht, br_hf b ht]
  module

/-- `d₁₂ψ(e,f) = -(2r₂+q₁) e + (p₁+r₃-q₂) h - (2p₂+q₃) f`. -/
theorem d12_ef {ψ : g →ₗ[ℂ] g} {p₁ p₂ p₃ q₁ q₂ q₃ r₁ r₂ r₃ : ℂ}
    (hp : ψ (b 0) = p₁ • b 0 + p₂ • b 1 + p₃ • b 2)
    (hq : ψ (b 1) = q₁ • b 0 + q₂ • b 1 + q₃ • b 2)
    (hr : ψ (b 2) = r₁ • b 0 + r₂ • b 1 + r₃ • b 2) :
    d₁₂ ℂ g g ψ (b 0) (b 2)
      = (-(2 * r₂) - q₁) • b 0 + (p₁ + r₃ - q₂) • b 1 + (-(2 * p₂) - q₃) • b 2 := by
  rw [d₁₂_apply_apply, br_ef b ht, hp, hq, hr]
  simp only [lie_add, lie_smul, lie_self, br_eh b ht, br_ef b ht, br_fh b ht, br_fe b ht]
  module

/-- `d₁₂ψ(h,f) = 4r₁ e + (q₁+2r₂) h - 2q₂ f`. -/
theorem d12_hf {ψ : g →ₗ[ℂ] g} {q₁ q₂ q₃ r₁ r₂ r₃ : ℂ}
    (hq : ψ (b 1) = q₁ • b 0 + q₂ • b 1 + q₃ • b 2)
    (hr : ψ (b 2) = r₁ • b 0 + r₂ • b 1 + r₃ • b 2) :
    d₁₂ ℂ g g ψ (b 1) (b 2)
      = (4 * r₁) • b 0 + (q₁ + 2 * r₂) • b 1 + (-2 * q₂) • b 2 := by
  rw [d₁₂_apply_apply, br_hf b ht, map_neg, map_smul, hq, hr]
  simp only [lie_add, lie_smul, lie_self, br_he b ht, br_hf b ht, br_fh b ht, br_fe b ht]
  module

/-- **What the cocycle condition says, in coordinates.**  Evaluating `d₂₃ ω e h f = 0`: the
three `ω(⁅·,·⁆,·)` terms **cancel identically** (`⁅e,h⁆ = -2e` and `⁅h,f⁆ = -2f` contribute
`+2ω(e,f)` and `-2ω(e,f)`, while `⁅e,f⁆ = h` contributes `ω(h,h) = 0`), leaving
`⁅e,ω(h,f)⁆ - ⁅h,ω(e,f)⁆ + ⁅f,ω(e,h)⁆ = 0`, i.e. exactly three scalar relations. -/
theorem cocycle_rel {ω : twoCochain ℂ g g} (hω : ω ∈ twoCocycle ℂ g g)
    {A₁ A₂ A₃ B₁ B₂ B₃ C₁ C₂ C₃ : ℂ}
    (hA : ω (b 0) (b 1) = A₁ • b 0 + A₂ • b 1 + A₃ • b 2)
    (hB : ω (b 0) (b 2) = B₁ • b 0 + B₂ • b 1 + B₃ • b 2)
    (hC : ω (b 1) (b 2) = C₁ • b 0 + C₂ • b 1 + C₃ • b 2) :
    C₂ + B₁ = 0 ∧ C₃ = A₁ ∧ B₃ + A₂ = 0 := by
  have hd : d₂₃ ℂ g g ω = 0 := (mem_twoCocycle_iff ℂ g g ω).mp hω
  have h3 : d₂₃ ℂ g g ω (b 0) (b 1) (b 2) = 0 := by rw [hd]; simp
  have key : (-2 * C₂ - 2 * B₁) • b 0 + (C₃ - A₁) • b 1 + (2 * B₃ + 2 * A₂) • b 2 = 0 := by
    rw [← h3, d₂₃_apply, br_eh b ht, br_ef b ht, br_hf b ht]
    simp only [map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply, twoCochain_alt,
      ← twoCochain_skew ω (b 0) (b 2), hA, hB, hC]
    simp only [lie_add, lie_smul, lie_self, br_eh b ht, br_ef b ht, br_he b ht, br_hf b ht,
      br_fh b ht, br_fe b ht]
    module
  obtain ⟨k1, k2, k3⟩ := coeff_zero_of_comb b key
  exact ⟨by linear_combination -k1 / 2, by linear_combination k2, by linear_combination k3 / 2⟩

end Brackets

/-- Two 2-cochains agreeing on the three ordered pairs from a `Fin 3` basis are equal. -/
theorem twoCochain_ext3 (b : Basis (Fin 3) ℂ g) {ω ω' : twoCochain ℂ g g}
    (h01 : ω (b 0) (b 1) = ω' (b 0) (b 1))
    (h02 : ω (b 0) (b 2) = ω' (b 0) (b 2))
    (h12 : ω (b 1) (b 2) = ω' (b 1) (b 2)) : ω = ω' := by
  have r01 : ω (b 1) (b 0) = ω' (b 1) (b 0) := by
    rw [← twoCochain_skew ω (b 0) (b 1), ← twoCochain_skew ω' (b 0) (b 1), h01]
  have r02 : ω (b 2) (b 0) = ω' (b 2) (b 0) := by
    rw [← twoCochain_skew ω (b 0) (b 2), ← twoCochain_skew ω' (b 0) (b 2), h02]
  have r12 : ω (b 2) (b 1) = ω' (b 2) (b 1) := by
    rw [← twoCochain_skew ω (b 1) (b 2), ← twoCochain_skew ω' (b 1) (b 2), h12]
  refine Subtype.ext (b.ext fun i => b.ext fun j => ?_)
  rw [twoCochain_val_apply, twoCochain_val_apply]
  have hfin : ∀ m : Fin 3, m = 0 ∨ m = 1 ∨ m = 2 := by decide
  rcases hfin i with rfl | rfl | rfl <;> rcases hfin j with rfl | rfl | rfl <;>
    first
      | simp only [twoCochain_alt]
      | exact h01 | exact h02 | exact h12
      | exact r01 | exact r02 | exact r12

/-- **Whitehead's second lemma for `𝔰𝔩₂`, with adjoint coefficients:** every
Chevalley–Eilenberg 2-cocycle on a `ℂ`-Lie algebra with an `𝔰𝔩₂`-triple basis is a coboundary,
i.e. `H²(𝔤,𝔤) = 0`.

Mathlib has no Lie-algebra cohomology beyond `Mathlib/Algebra/Lie/Cochain.lean` (whose own TODO
records that "coboundaries, cohomology" are absent) and no Whitehead lemma at all, so the
statement is phrased as `∃ ψ, d₁₂ ψ = ω` and the proof is the explicit primitive.

In coordinates `ω(e,h) = A₁e + A₂h + A₃f`, `ω(e,f) = B₁e + B₂h + B₃f`,
`ω(h,f) = C₁e + C₂h + C₃f`, the primitive is

`ψe = (B₂ - A₁/2)e + (A₃/4)f`,  `ψh = C₂e - (A₁/2)h + A₂f`,  `ψf = (C₁/4)e`.

The general formulas behind it — with `ψe = p₁e+p₂h+p₃f`, `ψh = q₁e+q₂h+q₃f`,
`ψf = r₁e+r₂h+r₃f` —

`d₁₂ψ(e,h) = -2q₂ e + (q₃+2p₂) h + 4p₃ f`,
`d₁₂ψ(e,f) = -(2r₂+q₁) e + (p₁+r₃-q₂) h - (2p₂+q₃) f`,
`d₁₂ψ(h,f) = 4r₁ e + (q₁+2r₂) h - 2q₂ f`

(`d12_eh`, `d12_ef`, `d12_hf`) also show the solution is unique up to three free parameters,
matching `dim Der(𝔰𝔩₂) = dim ad(𝔰𝔩₂) = 3`.  That residual gauge freedom is exactly the
`ψ ∈ Der(𝔤) = ad(𝔤)` that makes Linshaw–Qi's constant `c` gauge-invariant once the `x^{-1}`
coefficient has been normalised away. -/
theorem whitehead2_of_sl2Basis (b : Basis (Fin 3) ℂ g) (ht : IsSl2Triple (b 1) (b 0) (b 2))
    (ω : twoCochain ℂ g g) (hω : ω ∈ twoCocycle ℂ g g) :
    ∃ ψ : oneCochain ℂ g g, d₁₂ ℂ g g ψ = ω := by
  classical
  set A₁ := b.repr (ω (b 0) (b 1)) 0 with hA1
  set A₂ := b.repr (ω (b 0) (b 1)) 1 with hA2
  set A₃ := b.repr (ω (b 0) (b 1)) 2 with hA3
  set B₁ := b.repr (ω (b 0) (b 2)) 0 with hB1
  set B₂ := b.repr (ω (b 0) (b 2)) 1 with hB2
  set B₃ := b.repr (ω (b 0) (b 2)) 2 with hB3
  set C₁ := b.repr (ω (b 1) (b 2)) 0 with hC1
  set C₂ := b.repr (ω (b 1) (b 2)) 1 with hC2
  set C₃ := b.repr (ω (b 1) (b 2)) 2 with hC3
  have hA : ω (b 0) (b 1) = A₁ • b 0 + A₂ • b 1 + A₃ • b 2 := basis_expand b _
  have hB : ω (b 0) (b 2) = B₁ • b 0 + B₂ • b 1 + B₃ • b 2 := basis_expand b _
  have hC : ω (b 1) (b 2) = C₁ • b 0 + C₂ • b 1 + C₃ • b 2 := basis_expand b _
  obtain ⟨r1, r2, r3⟩ := cocycle_rel b ht hω hA hB hC
  have hB' : ω (b 0) (b 2) = (-C₂) • b 0 + B₂ • b 1 + (-A₂) • b 2 := by
    rw [hB, show B₁ = -C₂ from by linear_combination r1,
      show B₃ = -A₂ from by linear_combination r3]
  have hC' : ω (b 1) (b 2) = C₁ • b 0 + C₂ • b 1 + A₁ • b 2 := by
    rw [hC, show C₃ = A₁ from r2]
  refine ⟨b.constr ℂ ![(B₂ - A₁ / 2) • b 0 + (0 : ℂ) • b 1 + (A₃ / 4) • b 2,
                       C₂ • b 0 + (-(A₁ / 2)) • b 1 + A₂ • b 2,
                       (C₁ / 4) • b 0 + (0 : ℂ) • b 1 + (0 : ℂ) • b 2], ?_⟩
  set ψ : oneCochain ℂ g g :=
    b.constr ℂ ![(B₂ - A₁ / 2) • b 0 + (0 : ℂ) • b 1 + (A₃ / 4) • b 2,
                 C₂ • b 0 + (-(A₁ / 2)) • b 1 + A₂ • b 2,
                 (C₁ / 4) • b 0 + (0 : ℂ) • b 1 + (0 : ℂ) • b 2] with hψ
  have hp : ψ (b 0) = (B₂ - A₁ / 2) • b 0 + (0 : ℂ) • b 1 + (A₃ / 4) • b 2 :=
    b.constr_basis ℂ _ 0
  have hq : ψ (b 1) = C₂ • b 0 + (-(A₁ / 2)) • b 1 + A₂ • b 2 := b.constr_basis ℂ _ 1
  have hr : ψ (b 2) = (C₁ / 4) • b 0 + (0 : ℂ) • b 1 + (0 : ℂ) • b 2 := b.constr_basis ℂ _ 2
  refine twoCochain_ext3 b ?_ ?_ ?_
  · rw [d12_eh b ht hp hq, hA]; module
  · rw [d12_ef b ht hp hq hr, hB']; module
  · rw [d12_hf b ht hq hr, hC']; module

end Sl2Whitehead

/-! ## §2  The weight-one 2-cochain of a graded deformation -/

namespace VertexOperatorAlgebra

open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The `𝒱₁` Lie bracket, pushed to `𝒱`.  Restates `bracketV1_coe` for the `⁅·,·⁆` notation of
the `LieRing` instance, so that `simp` can push coercions through it. -/
@[simp] theorem coe_bracket_gradingOne (W : VertexOperatorAlgebra 𝒱) (u v : ↥(W.grading 1)) :
    ((⁅u, v⁆ : ↥(W.grading 1)) : 𝒱) = W.smul (u : 𝒱) 0 (v : 𝒱) := rfl

/-- **The weight-one Lie algebra is centreless.**  A property of `W` alone; for a VOA whose `𝒱₁`
is `𝔰𝔩₂` it is a theorem (`Sl2Whitehead.centreless_of_sl2Basis`). -/
def CentrelessWeightOne (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ z : ↥(W.grading 1), (∀ x : ↥(W.grading 1), ⁅z, x⁆ = 0) → z = 0

/-- Centrelessness follows from an `𝔰𝔩₂`-triple basis of `𝒱₁`. -/
theorem centrelessWeightOne_of_sl2Basis (W : VertexOperatorAlgebra 𝒱)
    (b : Basis (Fin 3) ℂ ↥(W.grading 1)) (ht : IsSl2Triple (b 1) (b 0) (b 2)) :
    CentrelessWeightOne W :=
  fun z hz => Sl2Whitehead.centreless_of_sl2Basis b ht z hz

/-- **PIECE 1 — the normalisation, Linshaw–Qi eq. (3) / [KQ] §6.2.**

`H²(𝒱₁, 𝒱₁) = 0`: every Chevalley–Eilenberg 2-cocycle on the weight-one Lie algebra
`(𝒱₁, ⁅a,b⁆ = a₍₀₎b)` with adjoint coefficients is a coboundary `d₁₂ ψ`.

**What this statement does NOT contain, and that is the whole point.**  No
`FirstOrderDeformation`, no `Y₁`, no mode other than `₍₀₎`, no level, no singular vector, nothing
about `𝒱` outside `𝒱₁`.  It is a predicate on the Lie algebra `𝒱₁`, wearing `W` only as the way
that Lie algebra is presented — so it is invariant under replacing `W` by any other VOA with the
same weight-one Lie algebra, whereas `Deform.IsRigidGraded` is not.  In particular there is no
map from an abstract Chevalley–Eilenberg 2-cocycle to a graded VOA deformation, so graded
rigidity of `W` constrains no `ω` here.

Mathlib carries no coboundary submodule (`Mathlib/Algebra/Lie/Cochain.lean`'s own TODO records
that "coboundaries, cohomology" are absent), hence the `∃ ψ, d₁₂ ψ = ω` phrasing. -/
def WeightOneH2Vanishes (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ ω : twoCochain ℂ ↥(W.grading 1) ↥(W.grading 1),
    ω ∈ twoCocycle ℂ ↥(W.grading 1) ↥(W.grading 1) →
      ∃ ψ : oneCochain ℂ ↥(W.grading 1) ↥(W.grading 1),
        d₁₂ ℂ ↥(W.grading 1) ↥(W.grading 1) ψ = ω

/-- **Piece 1 is a theorem, not a hypothesis**, for every VOA whose weight-one Lie algebra
carries an `𝔰𝔩₂`-triple basis — by Whitehead's second lemma, proved here as the finite
computation `Sl2Whitehead.whitehead2_of_sl2Basis`.

A hypothesis that is *discharged* from purely Lie-theoretic data about `𝒱₁` cannot be a
tautology-generator: the remaining input is `Sl2BasisOnWeightOne`, a statement about the
weight-one space alone. -/
theorem weightOneH2Vanishes_of_sl2Basis (W : VertexOperatorAlgebra 𝒱)
    (b : Basis (Fin 3) ℂ ↥(W.grading 1)) (ht : IsSl2Triple (b 1) (b 0) (b 2)) :
    WeightOneH2Vanishes W :=
  fun ω hω => Sl2Whitehead.whitehead2_of_sl2Basis b ht ω hω

/-! ### Extending `ψ : 𝒱₁ → 𝒱₁` by zero to a grade-preserving `φ : 𝒱 → 𝒱` -/

section Extend

variable (W : VertexOperatorAlgebra 𝒱) [DirectSum.Decomposition W.grading]

/-- The projection of `𝒱` onto its weight-`k` summand, as a linear map into the submodule. -/
noncomputable def gradedProj (k : ℤ) : 𝒱 →ₗ[ℂ] ↥(W.grading k) :=
  (DirectSum.component ℂ ℤ (fun j => (W.grading j : Submodule ℂ 𝒱)) k).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap

/-- To project a state to weight k, first write it in the internal direct sum of weight spaces and
select the kth component. The equality identifies the abstract linear projection with that
concrete operation. -/
theorem gradedProj_apply (k : ℤ) (x : 𝒱) :
    gradedProj W k x = (DirectSum.decompose W.grading x) k := rfl

/-- On its own graded piece the projection is the identity. -/
theorem gradedProj_of_mem {k : ℤ} {x : 𝒱} (hx : x ∈ W.grading k) :
    (gradedProj W k x : 𝒱) = x := by
  rw [gradedProj_apply]
  have hdec : DirectSum.decompose W.grading x
      = DirectSum.of (fun j => (W.grading j : Submodule ℂ 𝒱)) k ⟨x, hx⟩ :=
    DirectSum.decompose_coe (ℳ := fun j => (W.grading j : Submodule ℂ 𝒱)) (⟨x, hx⟩ : W.grading k)
  rw [hdec]
  simp

/-- On a different graded piece the projection vanishes. -/
theorem gradedProj_of_mem_ne {k j : ℤ} (hjk : j ≠ k) {x : 𝒱} (hx : x ∈ W.grading j) :
    gradedProj W k x = 0 := by
  apply Subtype.ext
  rw [gradedProj_apply]
  have hdec : DirectSum.decompose W.grading x
      = DirectSum.of (fun i => (W.grading i : Submodule ℂ 𝒱)) j ⟨x, hx⟩ :=
    DirectSum.decompose_coe (ℳ := fun i => (W.grading i : Submodule ℂ 𝒱)) (⟨x, hx⟩ : W.grading j)
  rw [hdec]
  simp only [DirectSum.of_eq_of_ne (β := fun i => (W.grading i : Submodule ℂ 𝒱))
    j k (⟨x, hx⟩ : W.grading j) hjk.symm, ZeroMemClass.coe_zero]

/-- The extension of `ψ : 𝒱₁ →ₗ 𝒱₁` by zero off the weight-one space. -/
noncomputable def extendWeightOne (ψ : ↥(W.grading 1) →ₗ[ℂ] ↥(W.grading 1)) : 𝒱 →ₗ[ℂ] 𝒱 :=
  (W.grading 1).subtype ∘ₗ ψ ∘ₗ gradedProj W 1

variable {W}

/-- Extending a linear map from weight one to the whole VOA leaves its action on weight-one states
unchanged. This is what lets a Lie-algebra coordinate change normalize the VOA currents. -/
theorem extendWeightOne_of_mem_one (ψ : ↥(W.grading 1) →ₗ[ℂ] ↥(W.grading 1))
    (a : ↥(W.grading 1)) : extendWeightOne W ψ (a : 𝒱) = (ψ a : 𝒱) := by
  change ((ψ (gradedProj W 1 (a : 𝒱)) : ↥(W.grading 1)) : 𝒱) = _
  rw [show gradedProj W 1 (a : 𝒱) = a from Subtype.ext (gradedProj_of_mem W a.2)]

/-- The extended weight-one coordinate change is zero on every other homogeneous weight. It
therefore changes the currents while leaving all other grades pointwise fixed at the level of
the chosen linear map. -/
theorem extendWeightOne_of_mem_ne (ψ : ↥(W.grading 1) →ₗ[ℂ] ↥(W.grading 1)) {k : ℤ} (hk : k ≠ 1)
    {a : 𝒱} (ha : a ∈ W.grading k) : extendWeightOne W ψ a = 0 := by
  change ((ψ (gradedProj W 1 a) : ↥(W.grading 1)) : 𝒱) = 0
  rw [gradedProj_of_mem_ne W hk ha, map_zero]
  rfl

/-- The extension preserves the grading. -/
theorem gradePreserving_extendWeightOne (ψ : ↥(W.grading 1) →ₗ[ℂ] ↥(W.grading 1)) :
    Deform.GradePreserving W (extendWeightOne W ψ) := by
  intro k u hu
  by_cases hk : k = 1
  · subst hk
    rw [show u = ((⟨u, hu⟩ : ↥(W.grading 1)) : 𝒱) from rfl,
      extendWeightOne_of_mem_one ψ ⟨u, hu⟩]
    exact (ψ ⟨u, hu⟩).2
  · rw [extendWeightOne_of_mem_ne ψ hk hu]
    exact (W.grading k).zero_mem

/-- The extension kills the vacuum (`𝟙 ∈ 𝒱₀` and `0 ≠ 1`). -/
theorem extendWeightOne_vacuum (ψ : ↥(W.grading 1) →ₗ[ℂ] ↥(W.grading 1)) :
    extendWeightOne W ψ W.vacuum = 0 :=
  extendWeightOne_of_mem_ne ψ (by norm_num) W.vacuum_mem

/-- **The signs match on the nose.**  On the weight-one space, the repository's VOA coboundary
`δφ` at mode `0` — `(φa)₍₀₎b - φ(a₍₀₎b) + a₍₀₎(φb)` — is literally Mathlib's Chevalley–Eilenberg
`d₁₂ψ a b = ⁅a,ψb⁆ - ⁅b,ψa⁆ - ψ⁅a,b⁆`, with `φ = extendWeightOne W ψ`.  The only input is
antisymmetry of the `𝒱₁` bracket (`smul_zero_add_swap_eq_zero`). -/
theorem coboundary_weightOne_eq_d₁₂ (ψ : ↥(W.grading 1) →ₗ[ℂ] ↥(W.grading 1))
    (a b : ↥(W.grading 1)) :
    W.smul (extendWeightOne W ψ (a : 𝒱)) 0 (b : 𝒱)
        - extendWeightOne W ψ (W.smul (a : 𝒱) 0 (b : 𝒱))
        + W.smul (a : 𝒱) 0 (extendWeightOne W ψ (b : 𝒱))
      = ((d₁₂ ℂ ↥(W.grading 1) ↥(W.grading 1) ψ a b : ↥(W.grading 1)) : 𝒱) := by
  have hbr : W.smul (a : 𝒱) 0 (b : 𝒱) = ((⁅a, b⁆ : ↥(W.grading 1)) : 𝒱) := rfl
  have hswap : W.smul ((ψ a : ↥(W.grading 1)) : 𝒱) 0 (b : 𝒱)
      = - W.smul (b : 𝒱) 0 ((ψ a : ↥(W.grading 1)) : 𝒱) := by
    have h := W.smul_zero_add_swap_eq_zero (ψ a).2 b.2
    linear_combination (norm := abel) h
  rw [extendWeightOne_of_mem_one ψ a, extendWeightOne_of_mem_one ψ b, hbr,
    extendWeightOne_of_mem_one ψ ⁅a, b⁆, hswap, d₁₂_apply_apply]
  simp only [Submodule.coe_sub, coe_bracket_gradingOne]
  abel

end Extend

end VertexOperatorAlgebra

namespace Deform

open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **The `ℓ = m = n = 0` case of the deformed Jacobi identity.**  Both `finsum`s collapse to
their `i = 0` term (`cbz 0 i = δ_{i,0}`), leaving

`ω(u,⁅v,x⁆) + ⁅u,ω(v,x)⁆ - ω(v,⁅u,x⁆) - ⁅v,ω(u,x)⁆ = ⁅ω(u,v),x⁆ + ω(⁅u,v⁆,x)`

with `ω(a,b) = a¹₍₀₎b` and `⁅a,b⁆ = a₍₀₎b`.  This single identity carries **both** halves of the
bridge: skewness of `ω` (set `u = v`) and the Chevalley–Eilenberg cocycle condition. -/
theorem jacobi_zero_modes {W : VertexOperatorAlgebra 𝒱} (D : FirstOrderDeformation W)
    (u v x : 𝒱) :
    D.smul₁ u 0 (W.smul v 0 x) + W.smul u 0 (D.smul₁ v 0 x)
        - (D.smul₁ v 0 (W.smul u 0 x) + W.smul v 0 (D.smul₁ u 0 x))
      = W.smul (D.smul₁ u 0 v) 0 x + D.smul₁ (W.smul u 0 v) 0 x := by
  have h := D.jacobi u v x 0 0 0
  rw [finsum_eq_single _ (0 : ℤ)
        (fun i hi => by rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul]),
      finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_smul])] at h
  simp only [cbz_zero_left, mul_one, one_smul, negOnePow, Even.zero, if_pos, add_zero,
    sub_zero] at h
  simpa using h

variable {W : VertexOperatorAlgebra 𝒱}

/-- A deformation is **in pole form** — the first clause of Linshaw–Qi's equation (3) — when the
`x^{-1}` coefficient of `Y₁(a,x)b` vanishes for weight-one `a, b`.

This is exactly the normalisation that Piece 1 (`VertexOperatorAlgebra.WeightOneH2Vanishes`)
produces, and the condition under which the paper's constant `c` is defined and gauge-invariant
at all.  Without it `c` is not an invariant: the coboundary `δ(L₀)` shifts it by `2k`
(`AffineSl2RigidityCollapse.not_gradedImpliesPoleZero_L43`). -/
def FirstOrderDeformation.InPoleForm (D : FirstOrderDeformation W) : Prop :=
  ∀ a ∈ W.grading 1, ∀ b ∈ W.grading 1, D.smul₁ a 0 b = 0

/-- The weight-one `0`-mode of a graded deformation, as a bilinear map `𝒱₁ × 𝒱₁ → 𝒱₁`.
Well defined by VA1 at order `t`: `1 + 1 - 0 - 1 = 1`. -/
noncomputable def weightOneBilin (D : FirstOrderDeformation W) (hD : D.IsGraded) :
    ↥(W.grading 1) →ₗ[ℂ] ↥(W.grading 1) →ₗ[ℂ] ↥(W.grading 1) where
  toFun a :=
    { toFun := fun b => ⟨D.smul₁ (a : 𝒱) 0 (b : 𝒱), by
        have h := hD 1 1 (a : 𝒱) a.2 (b : 𝒱) b.2 0
        rwa [show (1 : ℤ) + 1 - 0 - 1 = 1 from by ring] at h⟩
      map_add' := fun b₁ b₂ => by apply Subtype.ext; simp
      map_smul' := fun c b => by apply Subtype.ext; simp }
  map_add' := fun a₁ a₂ => by ext b; simp
  map_smul' := fun c a => by ext b; simp

/-- Forgetting the proof that the output has weight one recovers the original corrected zero-mode
product. The bilinear map on the current space carries the actual deformation data, not an
independent operation. -/
@[simp] theorem weightOneBilin_coe (D : FirstOrderDeformation W) (hD : D.IsGraded)
    (a b : ↥(W.grading 1)) :
    ((weightOneBilin D hD a b : ↥(W.grading 1)) : 𝒱) = D.smul₁ (a : 𝒱) 0 (b : 𝒱) := rfl

/-- `ω(a,a)` is **central** in `𝒱₁`: the `u = v = a` case of `jacobi_zero_modes` kills the whole
left-hand side and the `ω(⁅a,a⁆,·)` term, leaving `⁅ω(a,a),x⁆ = 0`.

⚠ Skewness of the weight-one `0`-mode is therefore **not free**: it is obtained from this
identity *plus* centrelessness of `𝒱₁`.  Proving first-order skew-symmetry in general instead
would be a port of `Core.SkewSymmetry` to the deformed setting, which is much harder. -/
theorem weightOneBilin_self_central (D : FirstOrderDeformation W) (hD : D.IsGraded)
    (a x : ↥(W.grading 1)) : ⁅weightOneBilin D hD a a, x⁆ = 0 := by
  have haa : W.smul (a : 𝒱) 0 (a : 𝒱) = 0 := by
    have h := W.smul_zero_add_swap_eq_zero a.2 a.2
    rw [← two_smul ℂ] at h
    rcases smul_eq_zero.mp h with h' | h'
    · exact absurd h' (by norm_num)
    · exact h'
  have h := jacobi_zero_modes D (a : 𝒱) (a : 𝒱) (x : 𝒱)
  rw [haa, D.smul₁_zero_left, add_zero, sub_self] at h
  apply Subtype.ext
  change W.smul (D.smul₁ (a : 𝒱) 0 (a : 𝒱)) 0 (x : 𝒱) = (0 : 𝒱)
  exact h.symm

/-- The weight-one `0`-mode of a graded deformation, as a **Lie 2-cochain** on `𝒱₁` with
adjoint coefficients. -/
noncomputable def weightOneCochain (D : FirstOrderDeformation W) (hD : D.IsGraded)
    (hZ : W.CentrelessWeightOne) : twoCochain ℂ ↥(W.grading 1) ↥(W.grading 1) :=
  ⟨weightOneBilin D hD, fun a => hZ _ (weightOneBilin_self_central D hD a)⟩

/-- The alternating Lie-algebra cochain has the same underlying value as the corrected zero-mode
product. The additional construction certifies alternation under the stated hypotheses without
changing that value. -/
@[simp] theorem weightOneCochain_coe (D : FirstOrderDeformation W) (hD : D.IsGraded)
    (hZ : W.CentrelessWeightOne) (a b : ↥(W.grading 1)) :
    ((weightOneCochain D hD hZ a b : ↥(W.grading 1)) : 𝒱) = D.smul₁ (a : 𝒱) 0 (b : 𝒱) := rfl

/-- **THE BRIDGE.**  The `ℓ = m = n = 0` case of the deformed Jacobi identity says exactly
that the weight-one `0`-mode of a graded deformation is a Chevalley–Eilenberg 2-cocycle.

Term by term: the three `ω(⁅·,·⁆,·)` terms of `d₂₃` reassemble, using skewness of `ω`, as
`-ω(⁅u,v⁆,x) - ω(v,⁅u,x⁆) + ω(u,⁅v,x⁆)`, and `⁅x,ω(u,v)⁆ = -⁅ω(u,v),x⁆` by antisymmetry of the
`𝒱₁` bracket. -/
theorem weightOneCochain_mem_twoCocycle (D : FirstOrderDeformation W) (hD : D.IsGraded)
    (hZ : W.CentrelessWeightOne) :
    weightOneCochain D hD hZ ∈ twoCocycle ℂ ↥(W.grading 1) ↥(W.grading 1) := by
  rw [mem_twoCocycle_iff]
  refine LinearMap.ext fun u => LinearMap.ext fun v => LinearMap.ext fun x => ?_
  rw [d₂₃_apply]
  simp only [LinearMap.zero_apply]
  rw [show weightOneCochain D hD hZ ⁅u, x⁆ v = - weightOneCochain D hD hZ v ⁅u, x⁆ from
        by rw [← twoCochain_skew],
      show weightOneCochain D hD hZ ⁅v, x⁆ u = - weightOneCochain D hD hZ u ⁅v, x⁆ from
        by rw [← twoCochain_skew],
      show ⁅x, weightOneCochain D hD hZ u v⁆ = - ⁅weightOneCochain D hD hZ u v, x⁆ from
        by rw [← lie_skew]]
  apply Subtype.ext
  simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_neg, ZeroMemClass.coe_zero,
    VertexOperatorAlgebra.coe_bracket_gradingOne, weightOneCochain_coe]
  refine Eq.trans ?_ (sub_eq_zero.mpr (jacobi_zero_modes D (u : 𝒱) (v : 𝒱) (x : 𝒱)))
  abel

end Deform

end VOA
