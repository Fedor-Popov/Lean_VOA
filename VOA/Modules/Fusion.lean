/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.Character

/-!
# Fusion products and the fusion ring  (Gannon §5.3.1, §5.3.3)

"The notion of tensor product — called fusion — for VOA modules is unexpectedly subtle."
Fusion is the tensor structure on `Φ(𝒱)` making the modules of a nice VOA into a braided
monoidal category, and the `χ_M` into a representation of the modular group (`Modularity`).

## The accessible core

* **Intertwining operator** `𝒴 : M × N → P` of type `(P; M, N)` (Def 6.1.9): mode data
  `𝒴(u,z)x = ∑_{s∈ℂ} 𝒴_s(u)x z^{-s-1}` (complex powers), lower-truncated, with the defining
  **intertwining commutator** relating the `𝒱`-actions on `M, N, P`. Built here as
  `Intertwiner`, and as the kernel `IntertwinerSpace` of the linear *intertwining defect*.
  ⚠ `IntertwinerSpace` imposes only the commutator condition — no truncation, `L₋₁`-derivative
  or grading constraint — so it is not the literature's space of intertwining operators.
* **Fusion coefficient** `fusionCoeff := finrank (IntertwinerSpace …)`.  ⚠ This is **identically
  `0`** (each shift class of `IntertwinerSpace` is either zero or infinite-dimensional, and
  `finrank` of an infinite-dimensional space is `0`): certificate
  `Notes/Textbook/certificates/L12_FusionCoeffZero.lean`.  It is
  **not** Gannon's `𝒩ᴾ_{MN}` (5.3.3).  It has no consumers.
* **Quantum dimension** `𝒟(M) = lim_{τ→0} χ_M(τ)/χ_𝒱(τ)` (5.3.12), with multiplicativity
  `𝒟(M ⊠ N) = 𝒟(M) 𝒟(N)`.

## Status

The `Intertwiner` structure (Def 6.1.9), the intertwining-defect linear map, the space
`IntertwinerSpace` (its kernel) and `fusionCoeff` are defined `sorry`-free; see the warnings
above — `fusionCoeff` is the constant `0`.

**Not formalized:** the braided tensor product `M ⊠ N`, the fusion ring, quantum dimensions and
Verlinde's formula.  None of them is defined in the library, and with the present `fusionCoeff`
(identically `0`) none could be connected to it; the intertwiner axioms would first have to be
imposed.  (See the `### The ⊠ / Verlinde formula` section.)

## Dependencies
* `VOA.Modules.Character`. Verlinde links to `Modularity.ZhuTheorem`.

## References
* Gannon §5.3.1, §5.3.3, §6.1.1, eqs. (5.3.3), (5.3.12); Huang–Lepowsky (tensor category
  theory); Frenkel–Huang–Lepowsky [199]; Verlinde.
-/

namespace VOA

open Module (End)
open scoped BigOperators
open Classical

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱}
variable {M N P : Type u} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  [AddCommGroup P] [Module ℂ P]

/-! ## Intertwining operators (Def 6.1.9) -/

/-- The **mode data** of an intertwining operator `𝒴(·,z) : M → Hom(N,P){z}`: the family of
`s`-modes `u ⊗ x ↦ 𝒴_s(u)x`, `s ∈ ℂ` (complex powers). -/
abbrev IntertwinerModes (M N P : Type u) [AddCommGroup M] [Module ℂ M] [AddCommGroup N]
    [Module ℂ N] [AddCommGroup P] [Module ℂ P] : Type u := ℂ → (M →ₗ[ℂ] N →ₗ[ℂ] P)

/-- The per-`j` summand of the intertwining commutator `∑ⱼ C(p,j) 𝒴_{s+p-j}(a₍ⱼ₎u) x`. -/
noncomputable def intertwinerSummand (A : OrdVModule W M) (Y : IntertwinerModes M N P)
    (a : 𝒱) (p : ℤ) (s : ℂ) (u : M) (x : N) (j : ℕ) : P :=
  cbz p j • Y (s + p - j) (A.toWeakModule.act a (j : ℤ) u) x

/-- The intertwining-commutator sum has finite support (lower truncation of the module
action `a₍ⱼ₎u`). -/
theorem intertwinerSummand_support_finite (A : OrdVModule W M) (Y : IntertwinerModes M N P)
    (a : 𝒱) (p : ℤ) (s : ℂ) (u : M) (x : N) :
    (Function.support (intertwinerSummand A Y a p s u x)).Finite := by
  obtain ⟨L, hL⟩ := A.truncation a u
  refine Set.Finite.subset (Set.finite_Iio L.toNat) (fun j hj => ?_)
  simp only [Function.mem_support, intertwinerSummand] at hj
  by_contra hge
  simp only [Set.mem_Iio, not_lt] at hge
  have : A.toWeakModule.act a (j : ℤ) u = 0 := hL (j : ℤ) (by omega)
  rw [this, map_zero, LinearMap.zero_apply, smul_zero] at hj
  exact hj rfl

/-- The **intertwining defect** of mode data `Y`, a `ℂ`-linear functional of `Y` whose
vanishing is the defining intertwining commutator of an operator of type `(P; M, N)`
(Gannon Def. 6.1.9):
`a₍ₚ₎ᴾ 𝒴_s(u)x − 𝒴_s(u)(a₍ₚ₎ᴺx) − ∑ⱼ C(p,j) 𝒴_{s+p-j}(a₍ⱼ₎ᴹu)x`. -/
noncomputable def intertwiningDefect (A : OrdVModule W M) (B : OrdVModule W N) (C : OrdVModule W P) :
    IntertwinerModes M N P →ₗ[ℂ] (𝒱 → ℤ → ℂ → M → N → P) where
  toFun Y := fun a p s u x =>
    C.toWeakModule.act a p (Y s u x) - Y s u (B.toWeakModule.act a p x)
      - ∑ᶠ j : ℕ, intertwinerSummand A Y a p s u x j
  map_add' Y₁ Y₂ := by
    funext a p s u x
    have h₁ := intertwinerSummand_support_finite A Y₁ a p s u x
    have h₂ := intertwinerSummand_support_finite A Y₂ a p s u x
    have hsplit : ∑ᶠ j : ℕ, intertwinerSummand A (Y₁ + Y₂) a p s u x j
        = (∑ᶠ j, intertwinerSummand A Y₁ a p s u x j)
          + ∑ᶠ j, intertwinerSummand A Y₂ a p s u x j := by
      rw [← finsum_add_distrib h₁ h₂]
      refine finsum_congr (fun j => ?_)
      simp only [intertwinerSummand, Pi.add_apply, LinearMap.add_apply, smul_add]
    simp only [Pi.add_apply, LinearMap.add_apply, WeakModule.act_add_right, hsplit]
    abel
  map_smul' c Y := by
    funext a p s u x
    have hsmul : ∑ᶠ j : ℕ, intertwinerSummand A (c • Y) a p s u x j
        = c • ∑ᶠ j, intertwinerSummand A Y a p s u x j := by
      rw [smul_finsum' c (intertwinerSummand_support_finite A Y a p s u x)]
      refine finsum_congr (fun j => ?_)
      simp only [intertwinerSummand, Pi.smul_apply, LinearMap.smul_apply, smul_comm c]
    simp only [Pi.smul_apply, LinearMap.smul_apply, WeakModule.act_smul_right, hsmul,
      RingHom.id_apply, smul_sub]

/-- The kernel of the intertwining defect: mode data satisfying the intertwining commutator of
Gannon Def. 6.1.9.  A `ℂ`-subspace of the mode data.  ⚠ It imposes **no** truncation,
`L₋₁`-derivative or grading condition, so it is larger than the space of intertwining operators of
type `(P; M, N)`; the bundled `Intertwiner` adds truncation. -/
noncomputable def IntertwinerSpace (A : OrdVModule W M) (B : OrdVModule W N) (C : OrdVModule W P) :
    Submodule ℂ (IntertwinerModes M N P) :=
  LinearMap.ker (intertwiningDefect A B C)

/-- A **bundled intertwining operator** of type `(P; M, N)` (Gannon Def. 6.1.9): mode data
that is lower-truncated and satisfies the intertwining commutator. -/
structure Intertwiner (A : OrdVModule W M) (B : OrdVModule W N) (C : OrdVModule W P) where
  /-- The mode data `𝒴_s(u)x`. -/
  modes : IntertwinerModes M N P
  /-- Lower truncation: `𝒴_s(u)x = 0` for `Re s ≫ 0`. -/
  truncation : ∀ (u : M) (x : N), ∃ s₀ : ℝ, ∀ s : ℂ, s₀ ≤ s.re → modes s u x = 0
  /-- The defining intertwining commutator (membership in `IntertwinerSpace`). -/
  isIntertwiner : modes ∈ IntertwinerSpace A B C

/-! ## Fusion coefficients (5.3.3) -/

/-- Intended as the fusion coefficient `𝒩ᴾ_{MN}` (Gannon 5.3.3), but defined as `finrank` of
`IntertwinerSpace`, which lacks truncation and grading.  ⚠ It is **identically `0`**
(certificate `Notes/Textbook/certificates/L12_FusionCoeffZero.lean`, `fusionCoeff_eq_zero`); it has
no consumers. -/
noncomputable def fusionCoeff (A : OrdVModule W M) (B : OrdVModule W N) (C : OrdVModule W P) : ℕ :=
  Module.finrank ℂ (IntertwinerSpace A B C)

/-!
### The `⊠` / Verlinde formula — not formalized

The following are **not** in the library; they are listed as targets only.

* **Fusion product** `M ⊠ N ≅ ⊕_{P∈Φ(𝒱)} 𝒩ᴾ_{MN} P` (eq. 5.3.3) — the braided tensor
  product (Huang–Lepowsky); the adjoint module `𝒱` is its unit (`𝒱 ⊠ M = M`).
* **Fusion ring** — the based `ℤ₊`-ring on `Φ(𝒱)` with structure constants `𝒩ᴾ_{MN}`.
* **Quantum dimension** `𝒟(M) = lim_{τ→0} χ_M(τ)/χ_𝒱(τ)` (eq. 5.3.12), multiplicative
  `𝒟(M⊠N) = 𝒟(M)𝒟(N)`.
* **Verlinde's formula** `𝒩ᴾ_{MN} = ∑_{Q} S_{MQ} S_{NQ} \overline{S_{PQ}} / S_{𝒱Q}`
  (eq. 6.1.1b).

The present `fusionCoeff` cannot serve as `𝒩ᴾ_{MN}` in any of these: it is identically `0`
(`fusionCoeff_eq_zero`).
-/

end VOA
