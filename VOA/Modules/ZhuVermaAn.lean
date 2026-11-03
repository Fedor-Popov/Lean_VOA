/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuAlgebra

/-!
# The higher Zhu tower `A_n(𝒱)` (Dong–Li–Mason) — foundation for the generalized-Verma module `M(U)`

Theorem 5.3.4's lifting direction `U ↦ M(U)` is the generalized-Verma / induced module of
Frenkel–Zhu, built on the **`A_n(𝒱)` tower** of higher Zhu algebras.  Attribution: the tower
`A_n(𝒱)` is Dong–Li–Mason's (1998); Frenkel–Zhu (1992) introduced the `A(𝒱)`-bimodules `A(M)`.
**Caveat.** `On W n` is spanned by the circle products `a ∘ₙ b` only; it omits DLM's further
generators `(L₋₁ + L₀) a` for `n ≥ 1`, so `On ⊆ O_n^{DLM}` and `An W n` surjects onto DLM's
`A_n(𝒱)` but may be larger.  This file
lays the genuine foundation: the `n`-th circle product `a ∘ₙ b`, the subspace `O_n(𝒱)`, and the
graded quotient `A_n(𝒱) = 𝒱 / O_n(𝒱)`, generalizing the `n = 0` Zhu data (`zhuFamily`/`O`/`A` in
`Modules.ZhuAlgebra`).

For homogeneous `a ∈ 𝒱ₖ`,
`a ∘ₙ b = Res_z ( Y(a,z) b · (1+z)^{k+n} / z^{2n+2} ) = ∑ᵢ C(k+n, i) · a₍ᵢ₋₂ₙ₋₂₎ b`,
extended bilinearly over the grade decomposition of `a` (exactly the `zhuMul` pattern, with the
single change `mode i-1 ↦ mode i-2n-2`, i.e. the Zhu *product* `/z` replaced by the FZ `/z^{2n+2}`).

* **`circFamily`/`circ`** — the `n`-th circle product `a ∘ₙ b`, `ℂ`-bilinear.
* **`On`** — `O_n(𝒱) := span{ a ∘ₙ b }`, a `ℂ`-subspace; **`An`** — `A_n(𝒱) := 𝒱 / O_n(𝒱)`.
* **`circ_add_left`/`circ_smul_left`/`circ_add_right`/`circ_smul_right`** — bilinearity.
* **`mkAn`** — the projection `𝒱 → A_n(𝒱)`; **`circ_mem_On`** — `a ∘ₙ b ∈ O_n(𝒱)`.

## Status
Axiom-clean for the tower foundation. The bimodule structure on `A_n(𝒱)`, the tower maps, and
the induced module `M(U) = ⊕ₙ A_n(𝒱) ⊗_{A(𝒱)} U` with its field `Y_{M(U)}` and module Jacobi
5.3.1b build on this (the next stages of the construction).

## References
* Gannon §5.3.2, Thm 5.3.4; Frenkel–Zhu (generalized Verma modules); Dong–Li–Mason.
-/

namespace VOA

open Module (End)
open scoped BigOperators
open Classical

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The `n`-th circle product `a ∘ₙ b` (Frenkel–Zhu / Dong–Li–Mason) -/

/-- The weight-`k` slice of `· ∘ₙ b`: on `aₖ ∈ 𝒱ₖ`,
`∑_{i=0}^{k+n} C(k+n, i) (aₖ)₍ᵢ₋₂ₙ₋₂₎ b` — the FZ `n`-th circle product
`Res_z Y(a,z) b (1+z)^{k+n}/z^{2n+2}`. A `ℂ`-linear map `𝒱ₖ → 𝒱` (the `n = 0` case is the Zhu
`O`-generator `zhuFamily`, with mode `i-1 ↦ i-2`). -/
noncomputable def circFamily (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (b : 𝒱) (k : ℤ) :
    (W.grading k) →ₗ[ℂ] 𝒱 where
  toFun ak := ∑ i ∈ Finset.range ((k + n).toNat + 1),
    cbz (k + (n : ℤ)) i • W.smul (ak : 𝒱) ((i : ℤ) - 2 * (n : ℤ) - 2) b
  map_add' a b := by
    simp only [Submodule.coe_add, PreVertexAlgebra.smul_add_left, smul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [SetLike.val_smul, PreVertexAlgebra.smul_smul_left, smul_comm c, RingHom.id_apply,
      Finset.smul_sum]

/-- The **`n`-th circle product** `a ∘ₙ b = Res_z(Y(a,z) b (1+z)^{wt a + n}/z^{2n+2})`, extended
bilinearly over the grade decomposition of `a` (Frenkel–Zhu). For `n = 0` this is the `O`-generator
`a ∘ b` whose span is Zhu's `O(𝒱)`. -/
noncomputable def circ (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a b : 𝒱) : 𝒱 :=
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  (DFinsupp.lsum ℂ (circFamily W n b)) (DirectSum.decompose W.grading a)

/-! ## Bilinearity of `∘ₙ` (the structural prerequisite for the `A_n`-bimodule) -/

/-- `circFamily W n b` is additive in `b`. -/
theorem circFamily_add (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (b₁ b₂ : 𝒱) :
    circFamily W n (b₁ + b₂) = circFamily W n b₁ + circFamily W n b₂ := by
  funext k
  refine LinearMap.ext fun ak => ?_
  simp only [Pi.add_apply, LinearMap.add_apply, circFamily, LinearMap.coe_mk, AddHom.coe_mk,
    PreVertexAlgebra.smul_add_right, smul_add, Finset.sum_add_distrib]

/-- `circFamily W n b` is homogeneous in `b`. -/
theorem circFamily_smul (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (c : ℂ) (b : 𝒱) :
    circFamily W n (c • b) = c • circFamily W n b := by
  funext k
  refine LinearMap.ext fun ak => ?_
  simp only [Pi.smul_apply, LinearMap.smul_apply, circFamily, LinearMap.coe_mk, AddHom.coe_mk,
    PreVertexAlgebra.smul_smul_right, Finset.smul_sum, smul_comm c]

/-- **`(a₁ + a₂) ∘ₙ b = a₁ ∘ₙ b + a₂ ∘ₙ b`** — `∘ₙ` is additive in the left factor. -/
theorem circ_add_left (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a₁ a₂ b : 𝒱) :
    circ W n (a₁ + a₂) b = circ W n a₁ b + circ W n a₂ b := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  exact map_add ((DFinsupp.lsum ℂ (circFamily W n b)).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap) a₁ a₂

/-- **`(c • a) ∘ₙ b = c • (a ∘ₙ b)`** — `∘ₙ` is homogeneous in the left factor. -/
theorem circ_smul_left (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (c : ℂ) (a b : 𝒱) :
    circ W n (c • a) b = c • circ W n a b := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  exact map_smul ((DFinsupp.lsum ℂ (circFamily W n b)).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap) c a

/-- **`a ∘ₙ (b₁ + b₂) = a ∘ₙ b₁ + a ∘ₙ b₂`** — `∘ₙ` is additive in the right factor. -/
theorem circ_add_right (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a b₁ b₂ : 𝒱) :
    circ W n a (b₁ + b₂) = circ W n a b₁ + circ W n a b₂ := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  show (DFinsupp.lsum ℂ (circFamily W n (b₁ + b₂))) (DirectSum.decompose W.grading a) = _
  rw [circFamily_add, map_add, LinearMap.add_apply]
  rfl

/-- **`a ∘ₙ (c • b) = c • (a ∘ₙ b)`** — `∘ₙ` is homogeneous in the right factor. -/
theorem circ_smul_right (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (c : ℂ) (a b : 𝒱) :
    circ W n a (c • b) = c • circ W n a b := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  show (DFinsupp.lsum ℂ (circFamily W n (c • b))) (DirectSum.decompose W.grading a) = _
  rw [circFamily_smul, map_smul, LinearMap.smul_apply]
  rfl

/-- On a homogeneous `a ∈ 𝒱ₖ`, the circle product collapses to the single weight-`k` slice
`∑_{i=0}^{k+n} C(k+n,i) a₍ᵢ₋₂ₙ₋₂₎ b` (the explicit FZ residue). -/
theorem circ_homogeneous (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {k : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading k) (b : 𝒱) :
    circ W n a b
      = ∑ i ∈ Finset.range ((k + (n : ℤ)).toNat + 1),
          cbz (k + (n : ℤ)) i • W.smul a ((i : ℤ) - 2 * (n : ℤ) - 2) b := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hcollapse : circ W n a b = circFamily W n b k ⟨a, ha⟩ := by
    change (DFinsupp.lsum ℂ (circFamily W n b)) (DirectSum.decompose W.grading a) = _
    rw [DirectSum.decompose_of_mem W.grading ha]
    exact DFinsupp.lsum_single ℂ (circFamily W n b) k ⟨a, ha⟩
  rw [hcollapse]; rfl

/-! ## `O_n(𝒱)` and the graded quotient `A_n(𝒱)` -/

/-- **`O_n(𝒱) := span{ a ∘ₙ b }`** (circle products only; for `n ≥ 1` this omits Dong–Li–Mason's
generators `(L₋₁ + L₀) a`, so it may be smaller than DLM's `O_n(𝒱)`). For `n = 0` this is Zhu's `O(𝒱)` (the circle-
product characterization). A `ℂ`-subspace by construction. -/
def On (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ {x | ∃ a b : 𝒱, x = circ W n a b}

/-- **The `n`-th higher Zhu space** `A_n(𝒱) := 𝒱 / O_n(𝒱)`, as a `ℂ`-module (a quotient of
which is Dong–Li–Mason's `A_n(𝒱)`; see `On`). The bottom `A₀(𝒱)`
is Zhu's algebra `A(𝒱)`; the tower `A_n` carries the bimodule data assembling `M(U)`. -/
abbrev An (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Type u := 𝒱 ⧸ On W n

/-- The canonical projection `𝒱 → A_n(𝒱)`, `u ↦ [u]ₙ`. -/
def mkAn (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : 𝒱 →ₗ[ℂ] An W n := (On W n).mkQ

/-- Every circle product lands in `O_n(𝒱)`. -/
theorem circ_mem_On (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a b : 𝒱) :
    circ W n a b ∈ On W n :=
  Submodule.subset_span ⟨a, b, rfl⟩

/-- `[a ∘ₙ b]ₙ = 0` in `A_n(𝒱)`: the circle products are the defining relations. -/
@[simp] theorem mkAn_circ (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a b : 𝒱) :
    mkAn W n (circ W n a b) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (circ_mem_On W n a b)

end VOA
