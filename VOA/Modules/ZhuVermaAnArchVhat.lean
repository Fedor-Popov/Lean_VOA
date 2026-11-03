/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.Submodule
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.LSum
import VOA.Core.VertexOperatorAlgebra
import VOA.Core.BorcherdsIdentity

/-!
# The loop / Frenkel–Zhu Lie algebra `V̂`

DLM3 (Dong–Li–Mason, *Twisted representations of VOAs*, q-alg/9612010) §4 / H. Li
(hep-th/9406211) §2: the loop Lie algebra attached to a VOA is

`g(𝒱) = (𝒱 ⊗ ℂ[t,t⁻¹]) / Im (L₋₁⊗1 + 1⊗ d/dt)`,

with the Borcherds bracket coming from the singular OPE

`[a(m), b(k)] = Σ_{i≥0} C(m,i) · (a₍ᵢ₎ b)(m+k-i)`        (a *finite* sum, `a₍ᵢ₎b = 0` for `i ≫ 0`).

Here `a(m) := a ⊗ tᵐ` and `C(m,i) = gBinom m i` is the generalized binomial coefficient
(`Foundations.FormalCalculus`).  The defining commutator formula 5.1.7c of the VOA
(`Core.BorcherdsIdentity.jacobi_commutator` / `Core.Reconstruction.mode_commutator`) is *exactly*
this bracket at the operator level — it is what makes the construction well posed.

This file builds the **foundational layer T0–T3** of the design map, proving everything that is
genuinely closeable from the existing infrastructure:

* **T0** the carrier `VLoop 𝒱 = ℤ →₀ 𝒱`, the derivative submodule `loopDerivSubmodule`, the
  quotient `VHat`, the generator `gen a m = a(m)`, the derivative relation `gen_Lneg1`, and the
  weight grading `VHat.deg`;
* **T1** the Borcherds loop bracket `vloopBracket : VLoop →ₗ VLoop →ₗ VLoop` (ℂ-bilinear, finite
  by VOA regularity), with the generator value `vloopBracket_gen` and additivity/`smul` lemmas;
* antisymmetry-of-the-leading-term and the precise reductions for the remaining obligations
  (descent to the quotient and the full Jacobi identity), which are stated as the named cruxes.

The construction *imitates* `Foundations.AffineLie` (`loopBracket`/`loopDeriv`/`ofProd`/`bracketP`
→ `LieRing`/`LieAlgebra`), but the bracket coefficients are the Borcherds binomials (a sum over
`i`), not affine structure constants, and there is **no central extension** — DLM3's `V̂` is
centreless, the conformal data already living inside `𝒱`.

## Status
Foundational layer for Construction A of Zhu's Theorem 5.3.4.  Green, `sorry`/axiom-free.  The full
`LieRing (VHat W)` instance is **not** claimed here: it needs (a) `vloopBracket_mem_derivSubmodule`
(`Im D` is a bracket ideal) and (b) the Borcherds–Jacobi identity for the descended bracket — both
recorded as precise targets in the docstrings below, neither stubbed.

## References
DLM3 §4; H. Li, hep-th/9406211 §2; Gannon §5.3.2, Thm 5.3.4; cf. `Foundations.AffineLie`.
-/

namespace VOA

open VertexOperatorAlgebra PreVertexAlgebra
open scoped BigOperators
open Finsupp

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## T0. The current space `VLoop = ℤ →₀ 𝒱` and the generator `a(m)` -/

/-- The "current" space `𝒱 ⊗ ℂ[t,t⁻¹]` before the quotient: finitely-supported functions
`ℤ → 𝒱`, with `a(m) = a ⊗ tᵐ` modelled as `Finsupp.single m a` (DLM3 §4). -/
abbrev VLoop (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] : Type u := ℤ →₀ 𝒱

namespace VHat

/-! ## T1. The Borcherds loop bracket on `VLoop`

We build the bracket as `Finsupp.lsum` over the *left* degree `m` (the binomial coefficient
`gBinom m i` depends on `m`), and, inside, a finite sum over the OPE index `i : ℕ`.  Each fixed
`(m, i)` contributes the *degree-homogeneous* piece

`brLevel m i : 𝒱 →ₗ VLoop →ₗ VLoop`,  `a, single k b ↦ gBinom m i • single (m+k-i) (a₍ᵢ₎b)`,

modelled exactly on `AffineLie.loopBracketLeft` (a `mapDomain` shift composed with a `mapRange`).
The full left-bracket is `bracketLeft m a := Σᶠ i, brLevel m i a`, a finsum that is finite for
each fixed input by VOA regularity (`smul_eventually_zero`). -/

/-- `b ↦ a₍ᵢ₎b` as a `ℂ`-linear map (the `i`-th product by `a`), for the bracket's `mapRange`. -/
noncomputable def smulMap (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (i : ℕ) : 𝒱 →ₗ[ℂ] 𝒱 where
  toFun b := W.smul a i b
  map_add' b b' := by simp
  map_smul' c b := by simp

@[simp] theorem smulMap_apply (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (i : ℕ) (b : 𝒱) :
    smulMap W a i b = W.smul a i b := rfl

theorem smulMap_add (W : VertexOperatorAlgebra 𝒱) (a a' : 𝒱) (i : ℕ) :
    smulMap W (a + a') i = smulMap W a i + smulMap W a' i := by
  refine LinearMap.ext fun b => ?_; simp [smul_add_left]

theorem smulMap_smul (W : VertexOperatorAlgebra 𝒱) (c : ℂ) (a : 𝒱) (i : ℕ) :
    smulMap W (c • a) i = c • smulMap W a i := by
  refine LinearMap.ext fun b => ?_; simp [smul_smul_left]

/-- The degree-homogeneous level-`i` piece of the bracket, keyed by the left degree `m`:
on `single k b` it gives `gBinom m i • single (m+k-i) (a₍ᵢ₎b)`.  Modelled on
`AffineLie.loopBracketLeft`. -/
noncomputable def brLevel (W : VertexOperatorAlgebra 𝒱) (m : ℤ) (i : ℕ) :
    𝒱 →ₗ[ℂ] VLoop 𝒱 →ₗ[ℂ] VLoop 𝒱 where
  toFun a :=
    (gBinom m i) • ((Finsupp.lmapDomain 𝒱 ℂ (· + (m - i))).comp
      (Finsupp.mapRange.linearMap (smulMap W a i)))
  map_add' a a' := by
    rw [smulMap_add]
    have : (Finsupp.mapRange.linearMap (smulMap W a i + smulMap W a' i) :
        VLoop 𝒱 →ₗ[ℂ] VLoop 𝒱)
        = Finsupp.mapRange.linearMap (smulMap W a i) + Finsupp.mapRange.linearMap (smulMap W a' i) := by
      refine LinearMap.ext fun g => ?_
      refine Finsupp.ext fun k => ?_
      simp [Finsupp.mapRange_apply]
    rw [this, LinearMap.comp_add, smul_add]
  map_smul' c a := by
    rw [smulMap_smul]
    have : (Finsupp.mapRange.linearMap (c • smulMap W a i) : VLoop 𝒱 →ₗ[ℂ] VLoop 𝒱)
        = c • Finsupp.mapRange.linearMap (smulMap W a i) := by
      refine LinearMap.ext fun g => ?_
      refine Finsupp.ext fun k => ?_
      simp [Finsupp.mapRange_apply]
    rw [this, LinearMap.comp_smul, RingHom.id_apply, smul_comm]

@[simp] theorem brLevel_single (W : VertexOperatorAlgebra 𝒱) (m : ℤ) (i : ℕ) (a : 𝒱)
    (k : ℤ) (b : 𝒱) :
    brLevel W m i a (single k b) = (gBinom m i) • single (m + k - i) (W.smul a i b) := by
  simp only [brLevel, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, LinearMap.comp_apply,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, smulMap_apply,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  congr 2
  ring

/-! ### Finiteness of the OPE sum and the bracket value

By VOA regularity (`smul_eventually_zero`), for fixed `a` and `b` the products `a₍ᵢ₎b` vanish for
`i` large, so the OPE sum `Σ_i brLevel m i a g` is finite for each input. -/

/-- For a single generator `single k b` only finitely many levels `i` contribute: `a₍ᵢ₎b = 0`
for `i ≥ N(a,b)`. -/
theorem brLevel_single_eventually_zero (W : VertexOperatorAlgebra 𝒱) (m : ℤ) (a : 𝒱) (k : ℤ)
    (b : 𝒱) : ∃ N : ℕ, ∀ i : ℕ, N ≤ i → brLevel W m i a (single k b) = 0 := by
  obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a b
  refine ⟨Nz.toNat, fun i hi => ?_⟩
  rw [brLevel_single, hNz i (by exact_mod_cast le_trans (Int.self_le_toNat Nz) (by exact_mod_cast hi)),
    Finsupp.single_zero, smul_zero]

/-- The level-indexed family `i ↦ brLevel W m i a g` has finite support, for every `g`
(VOA regularity, applied on the finite support of `g`). -/
theorem brLevel_support_finite (W : VertexOperatorAlgebra 𝒱) (m : ℤ) (a : 𝒱) (g : VLoop 𝒱) :
    (Function.support fun i : ℕ => brLevel W m i a g).Finite := by
  -- choose a uniform bound over the finite support of `g`
  classical
  induction g using Finsupp.induction_linear with
  | zero =>
    refine Set.Finite.subset (Set.finite_empty) ?_
    intro i hi
    rw [Function.mem_support] at hi
    exact absurd (map_zero (brLevel W m i a)) hi
  | add g₁ g₂ h₁ h₂ =>
    refine (h₁.union h₂).subset ?_
    intro i hi
    rw [Function.mem_support] at hi
    by_contra hcon
    rw [Set.mem_union, not_or, Function.mem_support, not_not, Function.mem_support, not_not] at hcon
    exact hi (by rw [map_add, hcon.1, hcon.2, add_zero])
  | single k b =>
    obtain ⟨N, hN⟩ := brLevel_single_eventually_zero W m a k b
    refine Set.Finite.subset (Set.finite_Iio N) ?_
    intro i hi
    rw [Function.mem_support] at hi
    rw [Set.mem_Iio]
    by_contra hcon
    rw [not_lt] at hcon
    exact hi (hN i hcon)

/-- The **left bracket value** `[a(m), g] = Σᶠ i, gBinom m i • (a₍ᵢ₎ ·)(m+·-i) g`, a finsum over the
OPE index `i` that is finite by `brLevel_support_finite`. -/
noncomputable def bracketLeftFun (W : VertexOperatorAlgebra 𝒱) (m : ℤ) (a : 𝒱) (g : VLoop 𝒱) :
    VLoop 𝒱 := ∑ᶠ i : ℕ, brLevel W m i a g

theorem bracketLeftFun_add_right (W : VertexOperatorAlgebra 𝒱) (m : ℤ) (a : 𝒱) (g g' : VLoop 𝒱) :
    bracketLeftFun W m a (g + g') = bracketLeftFun W m a g + bracketLeftFun W m a g' := by
  unfold bracketLeftFun
  rw [← finsum_add_distrib (brLevel_support_finite W m a g) (brLevel_support_finite W m a g')]
  exact finsum_congr fun i => by rw [map_add]

theorem bracketLeftFun_smul_right (W : VertexOperatorAlgebra 𝒱) (m : ℤ) (a : 𝒱) (c : ℂ)
    (g : VLoop 𝒱) : bracketLeftFun W m a (c • g) = c • bracketLeftFun W m a g := by
  unfold bracketLeftFun
  rw [finsum_congr fun i => by rw [map_smul], smul_finsum]

theorem bracketLeftFun_add_left (W : VertexOperatorAlgebra 𝒱) (m : ℤ) (a a' : 𝒱) (g : VLoop 𝒱) :
    bracketLeftFun W m (a + a') g = bracketLeftFun W m a g + bracketLeftFun W m a' g := by
  unfold bracketLeftFun
  rw [← finsum_add_distrib (brLevel_support_finite W m a g) (brLevel_support_finite W m a' g)]
  exact finsum_congr fun i => by rw [map_add, LinearMap.add_apply]

theorem bracketLeftFun_smul_left (W : VertexOperatorAlgebra 𝒱) (m : ℤ) (c : ℂ) (a : 𝒱)
    (g : VLoop 𝒱) : bracketLeftFun W m (c • a) g = c • bracketLeftFun W m a g := by
  unfold bracketLeftFun
  rw [finsum_congr fun i => by rw [map_smul, LinearMap.smul_apply], smul_finsum]

theorem bracketLeftFun_zero_left (W : VertexOperatorAlgebra 𝒱) (m : ℤ) (g : VLoop 𝒱) :
    bracketLeftFun W m 0 g = 0 := by
  unfold bracketLeftFun
  rw [finsum_congr fun i => by rw [map_zero, LinearMap.zero_apply], finsum_zero]

theorem bracketLeftFun_zero_right (W : VertexOperatorAlgebra 𝒱) (m : ℤ) (a : 𝒱) :
    bracketLeftFun W m a 0 = 0 := by
  unfold bracketLeftFun
  rw [finsum_congr fun i => by rw [map_zero], finsum_zero]

/-- `[a(m), ·]` packaged as a `ℂ`-linear map `VLoop →ₗ VLoop` (linear in the right argument). -/
noncomputable def bracketLeft (W : VertexOperatorAlgebra 𝒱) (m : ℤ) : 𝒱 →ₗ[ℂ] VLoop 𝒱 →ₗ[ℂ] VLoop 𝒱
    where
  toFun a :=
    { toFun := fun g => bracketLeftFun W m a g
      map_add' := bracketLeftFun_add_right W m a
      map_smul' := fun c g => by simp only [bracketLeftFun_smul_right, RingHom.id_apply] }
  map_add' a a' := by
    refine LinearMap.ext fun g => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    exact bracketLeftFun_add_left W m a a' g
  map_smul' c a := by
    refine LinearMap.ext fun g => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply]
    exact bracketLeftFun_smul_left W m c a g

@[simp] theorem bracketLeft_apply (W : VertexOperatorAlgebra 𝒱) (m : ℤ) (a : 𝒱) (g : VLoop 𝒱) :
    bracketLeft W m a g = ∑ᶠ i : ℕ, brLevel W m i a g := rfl

/-- The **Borcherds loop bracket** `[f, g] = Σ_{m} [a(m), g]` (extending `bracketLeft` over the
left degree via `Finsupp.lsum`): ℂ-bilinear, `VLoop →ₗ VLoop →ₗ VLoop`. -/
noncomputable def vloopBracket (W : VertexOperatorAlgebra 𝒱) :
    VLoop 𝒱 →ₗ[ℂ] VLoop 𝒱 →ₗ[ℂ] VLoop 𝒱 :=
  Finsupp.lsum ℂ (bracketLeft W)

/-- The generator-level OPE family `i ↦ gBinom m i • (a₍ᵢ₎b)(m+k-i)` has finite support
(VOA regularity). -/
theorem brLevel_support_finite' (W : VertexOperatorAlgebra 𝒱) (m k : ℤ) (a b : 𝒱) :
    (Function.support fun i : ℕ => (gBinom m i) • single (m + k - i) (W.smul a i b)).Finite := by
  obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a b
  refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Iio]
  by_contra hcon
  rw [not_lt] at hcon
  refine hi ?_
  rw [hNz i (le_trans (Int.self_le_toNat Nz) (by exact_mod_cast hcon)), Finsupp.single_zero,
    smul_zero]

/-- The bracket on generators: `[a(m), b(k)] = Σᶠ i, gBinom m i • (a₍ᵢ₎b)(m+k-i)` — the Borcherds
commutator formula 5.1.7c at the loop level. -/
theorem vloopBracket_single (W : VertexOperatorAlgebra 𝒱) (m k : ℤ) (a b : 𝒱) :
    vloopBracket W (single m a) (single k b)
      = ∑ᶠ i : ℕ, (gBinom m i) • single (m + k - i) (W.smul a i b) := by
  rw [vloopBracket, Finsupp.lsum_single, bracketLeft_apply]
  exact finsum_congr fun i => by rw [brLevel_single]

/-! ## T0. The derivative submodule `Im D`, the quotient `V̂`, and the generator `gen` -/

/-- The image of the derivative operator `D = L₋₁⊗1 + 1⊗ d/dt` whose quotient defines `V̂`
(DLM3 §4): the span of `(L₋₁ a)(m) + m·a(m-1) = single m (L₋₁ a) + m • single (m-1) a`. -/
noncomputable def loopDerivSubmodule (W : VertexOperatorAlgebra 𝒱) : Submodule ℂ (VLoop 𝒱) :=
  Submodule.span ℂ {x | ∃ (a : 𝒱) (m : ℤ),
    x = single m (W.L (-1) a) + (m : ℂ) • single (m - 1) a}

/-- The generators of `loopDerivSubmodule` lie in it (the derivative relation
`(L₋₁ a)(m) = -m·a(m-1)`). -/
theorem derivGen_mem (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (m : ℤ) :
    single m (W.L (-1) a) + (m : ℂ) • single (m - 1) a ∈ loopDerivSubmodule W :=
  Submodule.subset_span ⟨a, m, rfl⟩

/-- The **loop Lie algebra** `V̂ = (𝒱 ⊗ ℂ[t,t⁻¹]) / Im D` (Frenkel–Zhu / DLM3 §4, Li §2). -/
abbrev VHatCarrier (W : VertexOperatorAlgebra 𝒱) : Type u := VLoop 𝒱 ⧸ loopDerivSubmodule W

/-- The quotient map `VLoop ↠ V̂`. -/
noncomputable def mk (W : VertexOperatorAlgebra 𝒱) : VLoop 𝒱 →ₗ[ℂ] VHatCarrier W :=
  (loopDerivSubmodule W).mkQ

/-- The generator `a(m) = a ⊗ tᵐ ∈ V̂` (DLM3 §4). -/
noncomputable def gen (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (m : ℤ) : VHatCarrier W :=
  mk W (single m a)

@[simp] theorem gen_add_left (W : VertexOperatorAlgebra 𝒱) (a a' : 𝒱) (m : ℤ) :
    gen W (a + a') m = gen W a m + gen W a' m := by
  simp only [gen, mk, single_add, map_add]

@[simp] theorem gen_smul_left (W : VertexOperatorAlgebra 𝒱) (c : ℂ) (a : 𝒱) (m : ℤ) :
    gen W (c • a) m = c • gen W a m := by
  simp only [gen, mk, ← Finsupp.smul_single, map_smul]

@[simp] theorem gen_zero_left (W : VertexOperatorAlgebra 𝒱) (m : ℤ) :
    gen W (0 : 𝒱) m = 0 := by
  simp only [gen, mk, single_zero, map_zero]

/-- **The derivative relation** `(L₋₁ a)(m) = -m · a(m-1)` in `V̂` (DLM3 §4 / Li §2): the defining
relation of the quotient — `L₋₁⊗1 + 1⊗d/dt` is killed. -/
theorem gen_Lneg1 (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (m : ℤ) :
    gen W (W.L (-1) a) m = -(m : ℂ) • gen W a (m - 1) := by
  have h : mk W (single m (W.L (-1) a) + (m : ℂ) • single (m - 1) a) = 0 := by
    rw [mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact derivGen_mem W a m
  rw [map_add, map_smul] at h
  have he : mk W (single m (W.L (-1) a)) = -((m : ℂ) • mk W (single (m - 1) a)) := by
    rw [eq_neg_iff_add_eq_zero]; exact h
  simp only [gen]
  rw [he, neg_smul]

/-! ## T0. The weight grading of `V̂`

`a(m)` has degree `wt a − m − 1` on a homogeneous `a ∈ 𝒱_{wt a}` (DLM3 / `OrdVModule.weight`).
We define `VHat.deg d` as the span of the generators `gen a m` with `a` homogeneous of weight
`w` and `w − m − 1 = d`.  (`ℓ₀ := −deg`.) -/

/-- The weight-`d` graded piece of `V̂`: the span of `gen a m` over homogeneous `a ∈ 𝒱_w`
with `w − m − 1 = d` (DLM3 grading; `deg (a(m)) = wt a − m − 1`). -/
noncomputable def deg (W : VertexOperatorAlgebra 𝒱) (d : ℤ) : Submodule ℂ (VHatCarrier W) :=
  Submodule.span ℂ {x | ∃ (w m : ℤ) (a : 𝒱), a ∈ W.grading w ∧ w - m - 1 = d ∧ x = gen W a m}

/-- Generators land in their graded piece: `gen a m ∈ deg (w − m − 1)` for `a ∈ 𝒱_w`. -/
theorem gen_mem_deg (W : VertexOperatorAlgebra 𝒱) {w : ℤ} {a : 𝒱} (ha : a ∈ W.grading w) (m : ℤ) :
    gen W a m ∈ deg W (w - m - 1) :=
  Submodule.subset_span ⟨w, m, a, ha, rfl, rfl⟩

/-- The quotient map is surjective: every element of `V̂` is `mk W` of a loop element. -/
theorem mk_surjective (W : VertexOperatorAlgebra 𝒱) : Function.Surjective (mk W) :=
  (loopDerivSubmodule W).mkQ_surjective

/-- The **generators span `V̂`**: `V̂ = span ℂ {a(m)}` (DLM3 §4).  Immediate from surjectivity of
`mk` and the fact that `VLoop = ℤ →₀ 𝒱` is spanned by its `single`s. -/
theorem gen_span_top (W : VertexOperatorAlgebra 𝒱) :
    Submodule.span ℂ (Set.range (fun p : 𝒱 × ℤ => gen W p.1 p.2)) = ⊤ := by
  rw [eq_top_iff]
  rintro xbar -
  obtain ⟨x, rfl⟩ := mk_surjective W xbar
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add f g hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | single m a =>
    exact Submodule.subset_span ⟨(a, m), rfl⟩

/-! ## T2/T3. The descended bracket on `V̂`, antisymmetry and Jacobi — precise targets

The remaining content of step 1 is to descend `vloopBracket` to the quotient `V̂` and equip `V̂`
with its `LieRing`/`LieAlgebra` instances.  Both reduce to two named obligations, stated here as
precise `Prop`s.  Neither is stubbed: when discharged, the descended bracket and the Lie structure
follow mechanically (via `Submodule.liftQ₂` + the `AffineLie` pattern), exactly as the design map
(`PHASE4_MU_PLAN §1.2/§1.3`) prescribes. -/

/-- **Target T2 — the descent obligation.** The derivative subspace `Im D` is a two-sided ideal for
the loop bracket: bracketing a derivative-relation element against anything (on either side) stays
in `Im D`.  This is the statement that lets `vloopBracket` descend to `V̂` (DLM3 §4 / Li Lemma 2.1),
and rests on the Borcherds fact that `L₋₁` is a derivation of every mode
(`Core.Identities`/`Core.Translation`):
`L₋₁(a₍ᵢ₎b) = (L₋₁a)₍ᵢ₎b + a₍ᵢ₎(L₋₁b)` together with `(L₋₁a)₍ᵢ₎ = -i·a₍ᵢ₋₁₎`. -/
def BracketDescends (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ x ∈ loopDerivSubmodule W, ∀ y : VLoop 𝒱,
    vloopBracket W x y ∈ loopDerivSubmodule W ∧ vloopBracket W y x ∈ loopDerivSubmodule W

/-- The right-argument descent of `[x, ·]`: given `hD`, `vloopBracket W x` descends to a map
`V̂ → V̂`.  (Auxiliary for `vhatBracket`.) -/
noncomputable def vhatBracketRight (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (x : VLoop 𝒱) : VHatCarrier W →ₗ[ℂ] VHatCarrier W :=
  Submodule.liftQ (loopDerivSubmodule W) ((loopDerivSubmodule W).mkQ.comp (vloopBracket W x))
    (fun y hy => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact (hD y hy x).2)

@[simp] theorem vhatBracketRight_mk (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (x y : VLoop 𝒱) :
    vhatBracketRight W hD x (mk W y) = mk W (vloopBracket W x y) := by
  simp only [vhatBracketRight, mk, Submodule.liftQ_apply, LinearMap.comp_apply,
    Submodule.mkQ_apply]

/-- `x ↦ vhatBracketRight W hD x` is `ℂ`-linear in `x`. -/
noncomputable def vhatBracketLeft (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W) :
    VLoop 𝒱 →ₗ[ℂ] VHatCarrier W →ₗ[ℂ] VHatCarrier W where
  toFun := vhatBracketRight W hD
  map_add' x x' := by
    refine LinearMap.ext fun ybar => ?_
    obtain ⟨y, rfl⟩ := (loopDerivSubmodule W).mkQ_surjective ybar
    show vhatBracketRight W hD (x + x') (mk W y)
      = vhatBracketRight W hD x (mk W y) + vhatBracketRight W hD x' (mk W y)
    rw [vhatBracketRight_mk, vhatBracketRight_mk, vhatBracketRight_mk, map_add,
      LinearMap.add_apply, map_add]
  map_smul' c x := by
    refine LinearMap.ext fun ybar => ?_
    obtain ⟨y, rfl⟩ := (loopDerivSubmodule W).mkQ_surjective ybar
    show vhatBracketRight W hD (c • x) (mk W y) = c • vhatBracketRight W hD x (mk W y)
    rw [vhatBracketRight_mk, vhatBracketRight_mk, map_smul, LinearMap.smul_apply, map_smul]

@[simp] theorem vhatBracketLeft_mk (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (x : VLoop 𝒱) : vhatBracketLeft W hD x = vhatBracketRight W hD x := rfl

/-- **The descended bracket on `V̂`**, given the descent obligation `BracketDescends`.  Built from
`vloopBracket` by `Submodule.liftQ` in both arguments (the standard quotient-of-a-bilinear-map
construction).  This is *not* an axiom: it is a `def` parameterized by the honest hypothesis `hD`,
mirroring how `ZhuInducedPointwise` carries `BottomIsoLifts`.  When `BracketDescends` is proved,
`vhatBracket` becomes unconditional. -/
noncomputable def vhatBracket (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W) :
    VHatCarrier W →ₗ[ℂ] VHatCarrier W →ₗ[ℂ] VHatCarrier W :=
  Submodule.liftQ (loopDerivSubmodule W) (vhatBracketLeft W hD)
    (fun x hx => by
      refine LinearMap.ext fun ybar => ?_
      obtain ⟨y, rfl⟩ := (loopDerivSubmodule W).mkQ_surjective ybar
      show vhatBracketRight W hD x (mk W y) = (0 : VHatCarrier W)
      rw [vhatBracketRight_mk, mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact (hD x hx y).1)

@[simp] theorem vhatBracket_mk (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (x y : VLoop 𝒱) :
    vhatBracket W hD (mk W x) (mk W y) = mk W (vloopBracket W x y) := by
  change vhatBracketLeft W hD x (mk W y) = mk W (vloopBracket W x y)
  rw [vhatBracketLeft_mk, vhatBracketRight_mk]

/-- The descended bracket on generators (given descent): the Borcherds commutator formula in `V̂`,
`⁅a(m), b(k)⁆ = Σᶠ i, gBinom m i • (a₍ᵢ₎b)(m+k-i)` — design target `vhat_bracket_gen`. -/
theorem vhatBracket_gen (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (a b : 𝒱) (m k : ℤ) :
    vhatBracket W hD (gen W a m) (gen W b k)
      = ∑ᶠ i : ℕ, (gBinom m i) • gen W (W.smul a i b) (m + k - i) := by
  rw [gen, gen, vhatBracket_mk, vloopBracket_single]
  rw [show mk W = (loopDerivSubmodule W).mkQ from rfl,
    map_finsum (loopDerivSubmodule W).mkQ (brLevel_support_finite' W m k a b)]
  refine finsum_congr fun i => ?_
  rw [map_smul]
  rfl

/-- **Target T3 — antisymmetry in `V̂`.** `⁅x, y⁆ = -⁅y, x⁆` on the quotient `V̂` (given descent).
This is *false* on the loop space `VLoop` and becomes true only after quotienting by `Im D`: it is
the VOA skew-symmetry `Y(a,z)b = e^{zL₋₁}Y(b,-z)a` (Gannon 5.1.8, `Core.SkewSymmetry.skew`) packaged
at the level of modes.  Concretely, the leading `i = 0` term already shows the structure
`a₍₀₎b = -(b₍₀₎a) + (L₋₁-exact)`; the higher terms collect into `Im D` by the same skew-mode formula
(`Core.SkewSymmetry.skew_mode`). -/
def VHatAntisymm (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W) : Prop :=
  ∀ x y : VHatCarrier W, vhatBracket W hD x y = - vhatBracket W hD y x

/-- **Target T3 — Jacobi/Leibniz in `V̂`.** The Borcherds–Jacobi identity for the descended
bracket, the `leibniz_lie` form needed for `LieRing (VHat W)`.  This is the deep crux: it is the
full Borcherds identity 5.1.7 (the repo proves its `ℓ = 0` slice
`mode_commutator`/`jacobi_commutator` and its `m = 0` slice `mode_iterate`; the general identity
assembled into the loop bracket Jacobi is the remaining content), the loop-level analogue of
`AffineLie.loop_leibniz` but with binomial
Borcherds coefficients instead of structure constants. -/
def VHatLeibniz (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W) : Prop :=
  ∀ x y z : VHatCarrier W, vhatBracket W hD x (vhatBracket W hD y z)
    = vhatBracket W hD (vhatBracket W hD x y) z + vhatBracket W hD y (vhatBracket W hD x z)

/-- **The `LieRing` structure on `V̂`** (DLM3 §4), assembled from the three honest obligations
`BracketDescends` (T2), `VHatAntisymm` and `VHatLeibniz` (T3), exactly mirroring how
`AffineLie`'s `LieRing` instance is assembled from `bracketP_self`/`bracketP_leibniz`.  No axiom:
when the three `Prop`s are discharged this yields the unconditional Lie algebra `V̂`. -/
@[reducible]
noncomputable def lieRingOfData (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (hS : VHatAntisymm W hD) (hJ : VHatLeibniz W hD) : LieRing (VHatCarrier W) where
  bracket x y := vhatBracket W hD x y
  add_lie x y z := by simp only [map_add, LinearMap.add_apply]
  lie_add x y z := by simp only [map_add]
  lie_self x := by
    have := hS x x
    rw [eq_neg_iff_add_eq_zero, ← two_smul ℂ] at this
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero
  leibniz_lie x y z := hJ x y z

/-- The **`LieAlgebra ℂ` structure on `V̂`**, completing `lieRingOfData` (the bracket is already
`ℂ`-bilinear by construction). -/
noncomputable def lieAlgebraOfData (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (hS : VHatAntisymm W hD) (hJ : VHatLeibniz W hD) :
    letI := lieRingOfData W hD hS hJ
    LieAlgebra ℂ (VHatCarrier W) :=
  letI := lieRingOfData W hD hS hJ
  { lie_smul := fun r x y => by
      show vhatBracket W hD x (r • y) = r • vhatBracket W hD x y
      rw [map_smul] }

end VHat

end VOA
