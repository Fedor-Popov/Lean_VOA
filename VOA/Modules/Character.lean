/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.WeakModule
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Characters and graded dimensions  (Gannon §5.3.1, §5.3.3)

The numerical invariants of modules that Moonshine is "primarily interested in" — and
which will turn out to be modular (`Modularity.ZhuTheorem`). Convergence is treated in
`Modularity` *by design*: here the characters are honest **formal `q`-series**, modeled as
functions `ℂ → ℂ` of the complex exponent (the coefficient of `q^e`, with the `q^{-c/24}`
Casimir shift built in).

* **Graded dimension** (eq. 5.3.2): `χ_M(τ) = q^{-c/24} ∑_α (dim M_α) qᵃ`; the coefficient
  of `q^e` is `dim M_{e + c/24}`. (`gradedDim`.)
* **Zero-mode** `o(v) = ∑_k (v_k)₍ₖ₋₁₎` (Gannon §5.2.1): the conformal-weight-graded zero
  mode, bundled as a genuine `ℂ`-linear map `oMod N : 𝒱 →ₗ[ℂ] End M` (so linearity in `v`
  is automatic). Built from `LieAlgebraV1.zeroMode`'s mode shift via the (finite) grade
  decomposition of `v`.
* **One-point function** (eq. 5.3.13): `χ_M(τ,v) = tr_M o(v) q^{L₀-c/24}`; the coefficient
  of `q^e` is the graded trace `tr_{M_α} o(v)` (`α = e + c/24`), realized as the trace of
  the `α`-diagonal block `weightBlock` of `o(v)`. (`onePoint`.) It is **linear in `v`**
  (`onePoint_add`, `onePoint_smul`) and `χ_M(τ,𝟙) = χ_M(τ)` (`onePoint_vacuum`, since
  `o(𝟙) = id`).
* **Jacobi character** (Def 5.3.7, eq. 5.3.14): `χ^J_M(τ,v,w) = e^{2πiw} tr_M e^{2πi o(v)}
  q^{L₀-c/24}` (`v ∈ 𝒱₁`). The operator exponential `e^{2πi o(v)}` and its modular
  transformation are analytic; they are treated in `Modularity.JacobiCharacter`, built
  on the `onePoint`/`gradedDim` scaffolding here.

## Dependencies
* `VOA.Modules.WeakModule`; `Mathlib.LinearAlgebra.Trace`,
  `Mathlib.Algebra.DirectSum.Decomposition`.

## Status
`sorry`-free, with no project axioms. `gradedDim`, the bundled zero mode
`oMod`, the graded-trace `onePoint`, its `ℂ`-linearity in `v`, and `χ_M(τ,𝟙) = χ_M(τ)` are
all built and axiom-clean (`#print axioms onePoint_vacuum` =
`[propext, Classical.choice, Quot.sound]`). The Jacobi character's analytic content
(`e^{2πi o(v)}`, modular transformation) is in `Modularity.JacobiCharacter`.

## References
* Gannon §5.3.1, §5.3.3, eqs. (5.1.10b), (5.3.2), (5.3.13)–(5.3.14); Zhu [574].
-/

namespace VOA

open Module (End)
open scoped BigOperators
open Classical

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- A **formal `q`-series**: the coefficient function `e ↦ [q^e]`, indexed by the complex
exponent `e` (Gannon §5.3.1; convergence to a function on `ℍ` is treated in `Modularity`). -/
abbrev FormalQSeries : Type := ℂ → ℂ

/-! ## Component projection of an internal direct sum -/

/-- The component projection `M ↠ A i` of an internal direct-sum decomposition. -/
noncomputable def internalProjTo {ι : Type*} {M : Type*} [AddCommGroup M] [Module ℂ M]
    {A : ι → Submodule ℂ M} (h : DirectSum.IsInternal A) (i : ι) : M →ₗ[ℂ] A i :=
  letI := DirectSum.IsInternal.chooseDecomposition A h
  (DirectSum.component ℂ ι (fun j => A j) i).comp (DirectSum.decomposeLinearEquiv A).toLinearMap

/-- The projection restricted to its own summand is the identity: `proj_i (x) = x` for
`x ∈ A i`. -/
theorem internalProjTo_coe {ι : Type*} {M : Type*} [AddCommGroup M] [Module ℂ M]
    {A : ι → Submodule ℂ M} (h : DirectSum.IsInternal A) (i : ι) (x : A i) :
    internalProjTo h i (x : M) = x := by
  letI := DirectSum.IsInternal.chooseDecomposition A h
  apply Subtype.ext
  show ((internalProjTo h i (x : M)) : M) = (x : M)
  unfold internalProjTo
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, DirectSum.decomposeLinearEquiv_apply,
    ← DirectSum.apply_eq_component]
  exact DirectSum.decompose_of_mem_same A x.2

variable {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M] [Module ℂ M]

/-! ## The conformal-weight-graded zero mode `o(v)` (Gannon §5.2.1) -/

/-- Reading off the `m`-th mode `f ↦ f₍ₘ₎` of a field, as a `ℂ`-linear map. -/
noncomputable def modeLinear (m : ℤ) : (End ℂ M)⟦z^±⟧ →ₗ[ℂ] End ℂ M where
  toFun f := mode f m
  map_add' f g := mode_add f g m
  map_smul' c f := mode_smul c f m

/-- The weight-`k` slice of the zero mode: `vₖ ↦ (vₖ)₍ₖ₋₁₎` as a map `𝒱ₖ → End M`. -/
noncomputable def oModFamily (N : OrdVModule W M) (k : ℤ) : (W.grading k) →ₗ[ℂ] End ℂ M :=
  (modeLinear (k - 1)).comp (N.YM.comp (W.grading k).subtype)

/-- The **module zero mode** `o(v) = ∑_k (v_k)₍ₖ₋₁₎` (Gannon §5.2.1), bundled as a
`ℂ`-linear map `𝒱 →ₗ[ℂ] End M` via the (finite) `𝒱`-grade decomposition of `v`. On a
homogeneous `v ∈ 𝒱ₖ` it is the conformal zero mode `v₍ₖ₋₁₎` = `LieAlgebraV1.zeroMode`. -/
noncomputable def oMod (N : OrdVModule W M) : 𝒱 →ₗ[ℂ] End ℂ M :=
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  (DFinsupp.lsum ℂ (oModFamily N)).comp (DirectSum.decomposeLinearEquiv W.grading).toLinearMap

/-- `o(𝟙) = id_M`: the vacuum's only homogeneous slice is the grade-`0` mode `𝟙₍₋₁₎ = id`. -/
theorem oMod_vacuum (N : OrdVModule W M) : oMod N W.vacuum = LinearMap.id := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hcollapse : oMod N W.vacuum = oModFamily N 0 ⟨W.vacuum, W.vacuum_mem⟩ := by
    change (DFinsupp.lsum ℂ (oModFamily N)) (DirectSum.decompose W.grading W.vacuum) = _
    rw [DirectSum.decompose_of_mem W.grading W.vacuum_mem]
    exact DFinsupp.lsum_single ℂ (oModFamily N) 0 ⟨W.vacuum, W.vacuum_mem⟩
  rw [hcollapse]
  change mode (N.YM (W.vacuum : 𝒱)) (0 - 1) = LinearMap.id
  rw [N.vacuum_YM, show (0 : ℤ) - 1 = -1 from rfl, mode_one, if_pos rfl, Module.End.one_eq_id]

/-! ## The `α`-diagonal block of an operator -/

/-- The `α`-diagonal block of `T : End M`, as an endomorphism of the weight space `M_α`. -/
noncomputable def weightBlock (N : OrdVModule W M) (T : End ℂ M) (α : ℂ) : End ℂ (N.weight α) :=
  (internalProjTo N.isInternal α).comp (T.comp (N.weight α).subtype)

@[simp] theorem weightBlock_add (N : OrdVModule W M) (S T : End ℂ M) (α : ℂ) :
    weightBlock N (S + T) α = weightBlock N S α + weightBlock N T α := by
  simp only [weightBlock, LinearMap.add_comp, LinearMap.comp_add]

@[simp] theorem weightBlock_smul (N : OrdVModule W M) (c : ℂ) (T : End ℂ M) (α : ℂ) :
    weightBlock N (c • T) α = c • weightBlock N T α := by
  simp only [weightBlock, LinearMap.smul_comp, LinearMap.comp_smul]

/-- The block of the identity is the identity of `M_α`. -/
theorem weightBlock_id (N : OrdVModule W M) (α : ℂ) :
    weightBlock N LinearMap.id α = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  exact internalProjTo_coe N.isInternal α x

/-! ## Graded dimension and one-point function -/

/-- The **graded dimension** `χ_M(τ) = q^{-c/24} ∑_α (dim M_α) q^α` as a formal `q`-series:
the coefficient of `q^e` is `dim M_{e+c/24}` (Gannon 5.3.2). -/
noncomputable def gradedDim (N : OrdVModule W M) : FormalQSeries :=
  fun e => (Module.finrank ℂ (N.weight (e + W.centralCharge / 24)) : ℂ)

/-- The **one-point function** `χ_M(τ, v) = tr_M o(v) q^{L₀-c/24}` as a formal `q`-series:
the coefficient of `q^e` is the graded trace `tr_{M_α} o(v)`, `α = e + c/24` (Gannon
5.3.13). -/
noncomputable def onePoint (N : OrdVModule W M) (v : 𝒱) : FormalQSeries :=
  fun e =>
    haveI := N.finrank (e + W.centralCharge / 24)
    LinearMap.trace ℂ _ (weightBlock N (oMod N v) (e + W.centralCharge / 24))

/-- The one-point function is **additive in `v`** (Gannon §5.3.3). -/
theorem onePoint_add (N : OrdVModule W M) (v w : 𝒱) :
    onePoint N (v + w) = onePoint N v + onePoint N w := by
  funext e
  haveI := N.finrank (e + W.centralCharge / 24)
  simp only [onePoint, Pi.add_apply, map_add, weightBlock_add]

/-- The one-point function is **homogeneous in `v`** (Gannon §5.3.3); together with
`onePoint_add` this is its `ℂ`-linearity. -/
theorem onePoint_smul (N : OrdVModule W M) (c : ℂ) (v : 𝒱) :
    onePoint N (c • v) = c • onePoint N v := by
  funext e
  haveI := N.finrank (e + W.centralCharge / 24)
  simp only [onePoint, Pi.smul_apply, map_smul, weightBlock_smul, map_smul, smul_eq_mul]

/-- **`χ_M(τ, 𝟙) = χ_M(τ)`** (Gannon 5.3.13): the one-point function at the vacuum is the
graded dimension, since `o(𝟙) = id` and `tr_{M_α} id = dim M_α`. -/
theorem onePoint_vacuum (N : OrdVModule W M) : onePoint N W.vacuum = gradedDim N := by
  funext e
  haveI := N.finrank (e + W.centralCharge / 24)
  rw [onePoint, oMod_vacuum, weightBlock_id, LinearMap.trace_id, gradedDim]

end VOA
