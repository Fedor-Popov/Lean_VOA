/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib

/-!
# Statement of the D₄ finite identity (paper d4, eq. (P))

This file only *states* `D4FiniteIdentity`; the proof is in `VOA/DeligneAudit/D4Finite*.lean`.

Ring: `LP7 = ℤ[q^{±1}, s^{±1}, x^{±1}, z₁^{±1}, …, z₄^{±1}]`, as `AddMonoidAlgebra ℤ (Fin 7 → ℤ)`, with
coordinates `0 = q`, `1 = s`, `2 = x`, `3..6 = z₁..z₄`, and `t = s²`.

* `P₀ = ∏_{ε = ±1} ∏_{a ∈ {z_j^{±1}}} (1 - s x^ε a)`;
* `P_θ = ∏_{ε = ±1} [∏_{j=1,2} (1 - s x^ε/z_j)(1 - q s x^ε/z_j) ∏_{j=3,4} ∏_{σ=±1} (1 - s x^ε z_j^σ)]`;
* `N = P₀ - q⁻² z₁² z₂² P_θ`, and `G₀ = N / (1 - q⁻¹ z₁ z₂)` (exact);
* `F = π_{s_θ} G₀`, with `π_{s_θ}` the composite of the isobaric Demazure operators `π_i` along the
  reduced word `2,1,3,2,4,2,3,1,2` (palindromic), acting on the `z`-exponents with the simple roots
  `α₁ = e₁-e₂, α₂ = e₂-e₃, α₃ = e₃-e₄, α₄ = e₃+e₄` (string formula, `demazurePi`);
* `D₊ = (1-tx²)(1-qtx²)`, `D₋ = (1-tx⁻²)(1-qtx⁻²)`, `P(x) = ∏_a (1 - sxa)`, `P(x⁻¹) = ∏_a (1 - sx⁻¹a)`.

**(P)**:  `(1-x²) t q F = (1-x²)(1-t)(1-qt) D₊ D₋ - (1-qt)[P(x) D₋ - x² P(x⁻¹) D₊]`.

Division-free form: `D4FiniteIdentity` asserts the existence of `G₀` with `(1 - q⁻¹z₁z₂) G₀ = N` and (P) for
`F = π_{s_θ} G₀`.  (`1 - q⁻¹z₁z₂` is a non-zero-divisor, so `G₀` is unique.)

Checked symbolically outside Lean (zero residual; independently re-checked).  A kernel experiment: building `P₀` (9825 terms) with integer-encoded keys and
sorted merges takes about 5 s under `decide +kernel`; the full chain overflowed the stack with non-tail-recursive
merges on 2·10⁴-term lists (use accumulator-style merges).
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4F

noncomputable section

/-- `ℤ[q^{±1}, s^{±1}, x^{±1}, z₁^{±1}, …, z₄^{±1}]`. -/
abbrev LP7 := AddMonoidAlgebra ℤ (Fin 7 → ℤ)

/-- The monomial with exponent vector `v`. -/
def mono (v : Fin 7 → ℤ) : LP7 := AddMonoidAlgebra.single v 1

/-- Exponent vector from a list `[q, s, x, z₁, z₂, z₃, z₄]`. -/
def ev (l : List ℤ) : Fin 7 → ℤ := fun i => l.getD i 0

/-- `1 - m` for the monomial with exponent list `l`. -/
def oneSub (l : List ℤ) : LP7 := 1 - mono (ev l)

/-- The simple roots of `D₄` in the `e`-basis (`z`-coordinates). -/
def d4Root : Fin 4 → (Fin 4 → ℤ)
  | 0 => ![1, -1, 0, 0]
  | 1 => ![0, 1, -1, 0]
  | 2 => ![0, 0, 1, -1]
  | 3 => ![0, 0, 1, 1]

/-- Embed a `z`-vector into the seven coordinates. -/
def zEmbed (r : Fin 4 → ℤ) : Fin 7 → ℤ := fun i =>
  if h : 3 ≤ i.val then r ⟨i.val - 3, by omega⟩ else 0

/-- `⟨μ, α_i^∨⟩` for the `z`-part of `v`. -/
def zPair (v : Fin 7 → ℤ) (r : Fin 4 → ℤ) : ℤ := ∑ j : Fin 4, v ⟨j.val + 3, by omega⟩ * r j

/-- The isobaric Demazure operator on one monomial (string formula):
`π_i z^μ = z^μ + z^{μ-α} + ⋯ + z^{μ-nα}` for `n = ⟨μ,α^∨⟩ ≥ 0`, `0` for `n = -1`, and
`-(z^{μ+α} + ⋯ + z^{μ+(-n-1)α})` for `n ≤ -2`. -/
def demazureString (i : Fin 4) (v : Fin 7 → ℤ) : LP7 :=
  let r := zEmbed (d4Root i)
  let n := zPair v (d4Root i)
  if 0 ≤ n then ∑ j ∈ Finset.range (n.toNat + 1), mono (v - (j : ℤ) • r)
  else -∑ j ∈ Finset.range ((-n).toNat - 1), mono (v + ((j : ℤ) + 1) • r)

/-- `π_i`, extended `ℤ`-linearly. -/
def demazurePi (i : Fin 4) : LP7 →ₗ[ℤ] LP7 :=
  Finsupp.linearCombination ℤ (demazureString i)

/-- The reduced word `2,1,3,2,4,2,3,1,2` for `s_θ`, 0-based. -/
def wordTheta : List (Fin 4) := [1, 0, 2, 1, 3, 1, 2, 0, 1]

/-- `π_{s_θ}`: apply `π_i` for `i` in `wordTheta`, first letter first. -/
def demazureTheta (f : LP7) : LP7 := wordTheta.foldl (fun g i => demazurePi i g) f

/-- The factors `s x^ε a` of `P₀`. -/
def factorsP0 : List (List ℤ) :=
  [1, -1].flatMap fun eps => [[0, 1, eps, 1, 0, 0, 0], [0, 1, eps, -1, 0, 0, 0],
    [0, 1, eps, 0, 1, 0, 0], [0, 1, eps, 0, -1, 0, 0], [0, 1, eps, 0, 0, 1, 0],
    [0, 1, eps, 0, 0, -1, 0], [0, 1, eps, 0, 0, 0, 1], [0, 1, eps, 0, 0, 0, -1]]

/-- The factors of `P_θ`: for `j = 1,2` both `σ` slots carry `z_j⁻¹`, at `q⁰` and `q¹`. -/
def factorsPtheta : List (List ℤ) :=
  [1, -1].flatMap fun eps => [[0, 1, eps, -1, 0, 0, 0], [1, 1, eps, -1, 0, 0, 0],
    [0, 1, eps, 0, -1, 0, 0], [1, 1, eps, 0, -1, 0, 0], [0, 1, eps, 0, 0, 1, 0],
    [0, 1, eps, 0, 0, -1, 0], [0, 1, eps, 0, 0, 0, 1], [0, 1, eps, 0, 0, 0, -1]]

def prodOneSub (fs : List (List ℤ)) : LP7 := (fs.map oneSub).prod

def P0 : LP7 := prodOneSub factorsP0
def Ptheta : LP7 := prodOneSub factorsPtheta
/-- `N = P₀ - q⁻² z₁² z₂² P_θ`. -/
def Nnum : LP7 := P0 - mono (ev [-2, 0, 0, 2, 2, 0, 0]) * Ptheta

/-- `P(x) = ∏_a (1 - sxa)` and `P(x⁻¹)`. -/
def Pplus : LP7 := prodOneSub (factorsP0.filter fun l => l.getD 2 0 = 1)
def Pminus : LP7 := prodOneSub (factorsP0.filter fun l => l.getD 2 0 = -1)
/-- `D₊ = (1-tx²)(1-qtx²)`, `D₋ = (1-tx⁻²)(1-qtx⁻²)`. -/
def Dplus : LP7 := oneSub [0, 2, 2, 0, 0, 0, 0] * oneSub [1, 2, 2, 0, 0, 0, 0]
def Dminus : LP7 := oneSub [0, 2, -2, 0, 0, 0, 0] * oneSub [1, 2, -2, 0, 0, 0, 0]

/-- **The D₄ finite identity (P)**, division-free. -/
structure D4FiniteIdentity : Prop where
  holds : ∃ G₀ : LP7, oneSub [-1, 0, 0, 1, 1, 0, 0] * G₀ = Nnum ∧
    oneSub [0, 0, 2, 0, 0, 0, 0] * mono (ev [1, 2, 0, 0, 0, 0, 0]) * demazureTheta G₀ =
      oneSub [0, 0, 2, 0, 0, 0, 0] * oneSub [0, 2, 0, 0, 0, 0, 0] * oneSub [1, 2, 0, 0, 0, 0, 0] *
          Dplus * Dminus -
        oneSub [1, 2, 0, 0, 0, 0, 0] *
          (Pplus * Dminus - mono (ev [0, 0, 2, 0, 0, 0, 0]) * Pminus * Dplus)

end

end VOA.DeligneAudit.DeligneCharacter.D4F
