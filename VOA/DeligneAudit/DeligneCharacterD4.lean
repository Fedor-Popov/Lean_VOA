/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacter
import VOA.DeligneAudit.DeligneCharacterDemazure

/-!
# The D₄ (`so₈`, `k = -2`) character data

* `d4DemazureHilb m N = [q^N] Hilb_q D(1,mθ)` for `D₄`, by the affine Demazure character formula
  (`levelOneDemazureHilb`; inputs: Demazure character formula and Ravinder `D(1,mθ)` =
  `V_{(s_θ s_0)^m}(Λ₀)`).
* `d4TargetCoeff N = [q^{N+1}] (∑_{n ≥ 1} n σ₃(n) qⁿ) / ∏_{r ≥ 1}(1-q^r)^{10}`, the coefficients of
  `q^{-7/12} E₄′/(240 η^{10})` (`E₄ = 1 + 240 ∑ σ₃(n) qⁿ`).
* `D4StarIdentity` (paper d4 + residue proof + Jacobi triple product; audited SOUND) and
  `D4TargetLowerBound W` (Arakawa class S, arXiv:1811.01577 Thm A.2 + 10.11; or Arakawa–Kawasetsu
  MLDE uniqueness) are the named inputs.  No D₄ VOA is referenced here: `W` is any VOA, to be
  instantiated with the `L_{-2}(D₄)`.

Kernel checks are for tiny `N` only (`decide` cost grows fast).
-/

namespace VOA.DeligneAudit.DeligneCharacter

open VertexOperatorAlgebra

/-- `D₄` Cartan matrix, `α₂` the central node (0-based index 1). -/
def cartanD4 : List (List ℤ) := [[2, -1, 0, 0], [-1, 2, -1, -1], [0, -1, 2, 0], [0, -1, 0, 2]]

/-- Highest root `θ = α₁ + 2α₂ + α₃ + α₄`. -/
def thetaD4 : List ℤ := [1, 2, 1, 1]

/-- A reduced word for `s_θ` (`2,1,3,2,4,2,3,1,2`, 0-based). -/
def wordD4 : List ℕ := [1, 0, 2, 1, 3, 1, 2, 0, 1]

/-- `[q^N] Hilb_q D(1,mθ)` for `D₄`. -/
def d4DemazureHilb (m N : ℕ) : ℕ := levelOneDemazureHilb cartanD4 thetaD4 wordD4 m N

/-- `σ₃(n)`. -/
def sigma3 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d ^ 3

/-- `[q^N] ∏_{r=1}^{R} (1-q^r)^{-10}`. -/
def colorPart10 : ℕ → ℕ → ℕ
  | 0, N => if N = 0 then 1 else 0
  | R + 1, N => ∑ j ∈ Finset.range (N / (R + 1) + 1),
      Nat.choose (j + 9) 9 * colorPart10 R (N - j * (R + 1))

/-- **The D₄ target**: `[q^N] q^{-7/12} E₄′/(240 η^{10})`. -/
def d4TargetCoeff (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 2), n * sigma3 n * colorPart10 (N + 1) (N + 1 - n)

/-- The D₄ star identity `D_N = [q^N] q^{-7/12}E₄′/(240η¹⁰)`. -/
abbrev D4StarIdentity : Prop := StarIdentityFor d4DemazureHilb d4TargetCoeff

/-- The D₄ representation-theoretic input, for a VOA `W` (intended: `L_{-2}(D₄)`). -/
abbrev D4TargetLowerBound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) : Prop :=
  TargetLowerBound W d4TargetCoeff

/-! ## Finite checks -/

/-- `Hilb D(1,θ) = 28 + q`. -/
theorem d4DemazureHilb_one : (List.range 3).map (d4DemazureHilb 1) = [28, 1, 0] := by
  decide +kernel

/-- The first target coefficients: `1, 28, 329, 2632`. -/
theorem d4TargetCoeff_small : (List.range 4).map d4TargetCoeff = [1, 28, 329, 2632] := by
  decide +kernel

/-- The D₄ star identity in conformal weights `0, 1`. -/
theorem d4_star_small : (List.range 2).map (demazureSumCoeff d4DemazureHilb) =
    (List.range 2).map d4TargetCoeff := by
  decide +kernel

end VOA.DeligneAudit.DeligneCharacter

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.d4DemazureHilb_one
#print axioms VOA.DeligneAudit.DeligneCharacter.d4TargetCoeff_small
#print axioms VOA.DeligneAudit.DeligneCharacter.d4_star_small
end AxiomAudit
