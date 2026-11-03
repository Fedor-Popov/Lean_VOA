/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.ModuleC2Main

/-!
# The associativity target (statement only)

This file states, as named **TRUE** propositions, the associativity theorem for intertwining
operators must provide: associativity of intertwining operators among the irreducible modules
of a strongly rational VOA (Huang 1995, *A theory of tensor products for module categories for a
vertex operator algebra IV*, JPAA 100; Huang 2005, CCM 7, Thm 3.5).  It proves only that both sides
of the statement are honest absolutely convergent sums (not `tsum` junk values), unconditionally.

## The two sides

For irreducible `P₁, …, P₄`, an irreducible intermediate `Q` and FHL intertwiners, homogeneous
`wᵢ ∈ Pᵢ(αᵢ)` and `f` supported at `h₄`, `L₀`-conservation puts all coefficients on the line
`n₁ + n₂ = σ := α₁+α₂+α₃−h₄−2`, and irreducibility of `Q` puts the inner modes on ONE coset with
the canonical base `ν₀ = α₂+α₃−1−h_Q` (`isBase_canonical`).  So

* `prodValue … σ ν₀ z₁ z₂ = Σ_k prodCoeff(σ−ν₀+k, ν₀−k) z₁^{−(σ−ν₀+k)−1} z₂^{−(ν₀−k)−1}`
  is `⟨f, 𝒴₁(w₁,z₁)𝒴₂(w₂,z₂)w₃⟩`, and
* `iterValue … σ ν₀ z₀ z₂ = Σ_k iterCoeff(ν₀−k, σ−ν₀+k) z₂^{−(σ−ν₀+k)−1} z₀^{−(ν₀−k)−1}`
  is `⟨f, 𝒴₃(𝒴₄(w₁,z₀)w₂,z₂)w₃⟩`.

Both converge absolutely on their domains for every strongly rational `V`
(`summable_prodValue`, `summable_iterValue`, from Huang's ODEs, `ModuleC2.huangODEInput_holds`).

## The targets

* `AssociativityInput W`: every product equals a finite sum of iterates (irreducible intermediate
  modules) for **real** `z₁ > z₂ > z₁ − z₂ > 0`;
* `AssociativityConverse W`: every iterate equals a finite sum of products, same region.

Both are TRUE for strongly rational `W` (Huang, loc. cit.).  The region is Huang's own
(`z₁ > z₂ > z₁ − z₂ > 0`, real logarithms).  ⚠ Do not "generalise" to complex `z` with principal
powers: then `log z₁ = log z₂ + log(1 + z₀/z₂)` fails in general and the statement with the same
coefficients is not true as stated.

## Status
No `sorry`, no new axioms.  The two `Prop`s are open in this file.
-/

namespace VOA.Huang.AssocTarget

open VOA VOA.Huang.MatrixCoeff VOA.Huang.Convergence VOA.Huang.FusionTop PowerSeries

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- The single-coset value of the product `⟨f, 𝒴₁(w₁,z₁)𝒴₂(w₂,z₂)w₃⟩` (line `n₁+n₂ = σ`,
inner modes `ν₀ − k`, principal powers). -/
noncomputable def prodValue (Y₁ : IntertwiningModes M₁ M₅ M₄) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ z₁ z₂ : ℂ) : ℂ :=
  ∑' k : ℕ, prodCoeff Y₁ Y₂ f w₁ w₂ w₃ (σ - ν₀ + k) (ν₀ - k)
    * z₁ ^ (-(σ - ν₀ + k) - 1) * z₂ ^ (-(ν₀ - k) - 1)

/-- The single-coset value of the iterate `⟨f, 𝒴₃(𝒴₄(w₁,z₀)w₂,z₂)w₃⟩` (line `n₀+n₂ = σ`,
inner modes `ν₀ − k`, principal powers). -/
noncomputable def iterValue (Y₃ : IntertwiningModes M₅ M₃ M₄) (Y₄ : IntertwiningModes M₁ M₂ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ z₀ z₂ : ℂ) : ℂ :=
  ∑' k : ℕ, iterCoeff Y₃ Y₄ f w₁ w₂ w₃ (ν₀ - k) (σ - ν₀ + k)
    * z₂ ^ (-(σ - ν₀ + k) - 1) * z₀ ^ (-(ν₀ - k) - 1)

/-- **The canonical base.**  If the target `Q` of `𝒴` has lowest weight `h`, then for homogeneous
`w ∈ N₁(α)`, `w' ∈ N₂(β)` the coset `α+β−1−h + ℤ` carries all nonzero modes and `α+β−1−h` is a
base: `𝒴(w)₍α+β−1−h+j+1₎w'` has weight `h − j − 1 < h`. -/
theorem isBase_canonical {N₁ N₂ : Type u} [AddCommGroup N₁] [Module ℂ N₁] [AddCommGroup N₂]
    [Module ℂ N₂] {B₁ : OrdVModule W N₁} {B₂ : OrdVModule W N₂} (Q : LWModule W)
    {Y : IntertwiningModes N₁ N₂ Q.carrier} (hY : IsIntertwiningOperator B₁ B₂ Q.isMod Y)
    {α β : ℂ} {w : N₁} {w' : N₂} (hw : w ∈ B₁.weight α) (hw' : w' ∈ B₂.weight β) :
    IsBase Y w w' (α + β - 1 - Q.h) := by
  intro j
  have hmem := mem_weight hY hw hw' (α + β - 1 - Q.h + ((j : ℂ) + 1))
  have e : α + β - (α + β - 1 - Q.h + ((j : ℂ) + 1)) - 1 = Q.h + (-(j : ℂ) - 1) := by ring
  rw [e] at hmem
  by_contra hne
  have hbot : Q.isMod.weight (Q.h + (-(j : ℂ) - 1)) ≠ ⊥ := by
    intro hb
    rw [hb, Submodule.mem_bot] at hmem
    exact hne hmem
  obtain ⟨n, hn⟩ := Q.isLow _ hbot
  have h2 : ((n + j + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination -hn
  have h3 : n + j + 1 = 0 := by exact_mod_cast h2
  omega

section Summable

/-- **The product side is an honest convergent sum** for every strongly rational `V`
(irreducible modules, `0 < ‖z₂‖ < ‖z₁‖`), unconditionally. -/
theorem summable_prodValue (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
    (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) :
    Summable fun k : ℕ =>
      prodCoeff Y₁ Y₂ f w₁ w₂ w₃ ((α₁ + α₂ + α₃ - h₄ - 2) - (α₂ + α₃ - 1 - Q.h) + k)
          ((α₂ + α₃ - 1 - Q.h) - k)
        * z₁ ^ (-((α₁ + α₂ + α₃ - h₄ - 2) - (α₂ + α₃ - 1 - Q.h) + k) - 1)
        * z₂ ^ (-((α₂ + α₃ - 1 - Q.h) - k) - 1) :=
  (VOA.Huang.HuangODEContra.summable_prodTerm_of_moduleC2Input
    VOA.Huang.BuhlSpanning.moduleC2Input_holds hV i₁ i₂ i₃ i₄ Q.isMod hY₁ hY₂ h₁ h₂ h₃ hf
    (isBase_canonical Q hY₂ h₂ h₃) hz₂ hz).of_norm

/-- **The iterate side is an honest convergent sum** for every strongly rational `V`
(irreducible modules, `0 < ‖z₀‖ < ‖z₂‖`), unconditionally. -/
theorem summable_iterValue (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    {Y₃ : IntertwiningModes Q.carrier P₃.carrier P₄.carrier}
    {Y₄ : IntertwiningModes P₁.carrier P₂.carrier Q.carrier}
    (hY₃ : IsIntertwiningOperator Q.isMod P₃.isMod P₄.isMod Y₃)
    (hY₄ : IsIntertwiningOperator P₁.isMod P₂.isMod Q.isMod Y₄)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
    {z₀ z₂ : ℂ} (hz₀ : z₀ ≠ 0) (hz : ‖z₀‖ < ‖z₂‖) :
    Summable fun k : ℕ =>
      iterCoeff Y₃ Y₄ f w₁ w₂ w₃ ((α₁ + α₂ - 1 - Q.h) - k)
          ((α₁ + α₂ + α₃ - h₄ - 2) - (α₁ + α₂ - 1 - Q.h) + k)
        * z₂ ^ (-((α₁ + α₂ + α₃ - h₄ - 2) - (α₁ + α₂ - 1 - Q.h) + k) - 1)
        * z₀ ^ (-((α₁ + α₂ - 1 - Q.h) - k) - 1) :=
  (VOA.Huang.HuangODEContra.summable_iterTerm_of_moduleC2Input
    VOA.Huang.BuhlSpanning.moduleC2Input_holds hV i₁ i₂ i₃ i₄ Q.isMod hY₃ hY₄ h₁ h₂ h₃ hf
    (isBase_canonical Q hY₄ h₁ h₂) hz₀ hz).of_norm

end Summable

/-! ## The V4 targets (named, TRUE, open) -/

/-- **Associativity of intertwining operators** (V4 target; TRUE for strongly rational `W`:
Huang 1995 JPAA 100 + Huang 2005 CCM 7 Thm 3.5).  Every product of intertwiners among irreducible
modules, with irreducible intermediate module `Q`, equals on the real region
`z₁ > z₂ > z₁ − z₂ > 0` a finite sum of iterates with irreducible intermediate modules `Qⱼ`, the
same finite family serving all `w₁, w₂, w₃, f`. -/
def AssociativityInput (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ Q : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW →
    P₃.IsIrreducibleLW → P₄.IsIrreducibleLW → Q.IsIrreducibleLW →
  ∀ (Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier)
    (Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier),
    IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁ →
    IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂ →
  ∃ (r : ℕ) (Qs : Fin r → LWModule W) (_ : ∀ j, (Qs j).IsIrreducibleLW)
    (Y₃ : ∀ j, IntertwiningModes (Qs j).carrier P₃.carrier P₄.carrier)
    (Y₄ : ∀ j, IntertwiningModes P₁.carrier P₂.carrier (Qs j).carrier),
    (∀ j, IsIntertwiningOperator (Qs j).isMod P₃.isMod P₄.isMod (Y₃ j)) ∧
    (∀ j, IsIntertwiningOperator P₁.isMod P₂.isMod (Qs j).isMod (Y₄ j)) ∧
    ∀ (α₁ α₂ α₃ h₄ : ℂ) (w₁ : P₁.carrier) (w₂ : P₂.carrier) (w₃ : P₃.carrier)
      (f : P₄.carrier →ₗ[ℂ] ℂ),
      w₁ ∈ P₁.isMod.weight α₁ → w₂ ∈ P₂.isMod.weight α₂ → w₃ ∈ P₃.isMod.weight α₃ →
      SupportedAt P₄.isMod f h₄ →
    ∀ z₁ z₂ : ℝ, 0 < z₁ - z₂ → z₁ - z₂ < z₂ →
      prodValue Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h) z₁ z₂
        = ∑ j, iterValue (Y₃ j) (Y₄ j) f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2)
            (α₁ + α₂ - 1 - (Qs j).h) ((z₁ - z₂ : ℝ) : ℂ) z₂

/-- **The converse** (V4 target; TRUE for strongly rational `W`, same sources): every iterate is a
finite sum of products on `z₁ > z₂ > z₁ − z₂ > 0`. -/
def AssociativityConverse (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ Q : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW →
    P₃.IsIrreducibleLW → P₄.IsIrreducibleLW → Q.IsIrreducibleLW →
  ∀ (Y₃ : IntertwiningModes Q.carrier P₃.carrier P₄.carrier)
    (Y₄ : IntertwiningModes P₁.carrier P₂.carrier Q.carrier),
    IsIntertwiningOperator Q.isMod P₃.isMod P₄.isMod Y₃ →
    IsIntertwiningOperator P₁.isMod P₂.isMod Q.isMod Y₄ →
  ∃ (r : ℕ) (Qs : Fin r → LWModule W) (_ : ∀ j, (Qs j).IsIrreducibleLW)
    (Y₁ : ∀ j, IntertwiningModes P₁.carrier (Qs j).carrier P₄.carrier)
    (Y₂ : ∀ j, IntertwiningModes P₂.carrier P₃.carrier (Qs j).carrier),
    (∀ j, IsIntertwiningOperator P₁.isMod (Qs j).isMod P₄.isMod (Y₁ j)) ∧
    (∀ j, IsIntertwiningOperator P₂.isMod P₃.isMod (Qs j).isMod (Y₂ j)) ∧
    ∀ (α₁ α₂ α₃ h₄ : ℂ) (w₁ : P₁.carrier) (w₂ : P₂.carrier) (w₃ : P₃.carrier)
      (f : P₄.carrier →ₗ[ℂ] ℂ),
      w₁ ∈ P₁.isMod.weight α₁ → w₂ ∈ P₂.isMod.weight α₂ → w₃ ∈ P₃.isMod.weight α₃ →
      SupportedAt P₄.isMod f h₄ →
    ∀ z₁ z₂ : ℝ, 0 < z₁ - z₂ → z₁ - z₂ < z₂ →
      iterValue Y₃ Y₄ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₁ + α₂ - 1 - Q.h)
          ((z₁ - z₂ : ℝ) : ℂ) z₂
        = ∑ j, prodValue (Y₁ j) (Y₂ j) f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2)
            (α₂ + α₃ - 1 - (Qs j).h) z₁ z₂

/-- The V4 input for one VOA: both directions. -/
def AssociativityBoth (W : VertexOperatorAlgebra 𝒱) : Prop :=
  AssociativityInput W ∧ AssociativityConverse W

end VOA.Huang.AssocTarget
