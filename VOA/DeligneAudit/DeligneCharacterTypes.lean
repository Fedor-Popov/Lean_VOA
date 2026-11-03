/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacter

/-!
# Rational targets and the Arakawa–Kawasetsu recurrence

For the types `G₂, F₄, E₆, E₇, E₈` the unflavoured vacuum character of `L_k(g)`, `k = -1 - h∨/6`,
is the unique solution with `c₀ = 1` of the Arakawa–Kawasetsu MLDE recurrence

  `N(6N + h) c_N = ∑_{r=1}^{N} [10(h²-1)σ₃(r) - (24(N-r) + 2(h+1))σ₁(r)] c_{N-r}`,   `h = h∨`

(AK arXiv:1610.05865, Lemma 7.1 with Lemma 5.5 / Thm 5.7: a theorem for the simple quotient in all
eight Deligne types).  `mldeCoeff h N` computes it over `ℚ`.

Generic `ℚ`-valued forms of the character-side inputs:
* `StarIdentityQ hilb target`: `D_N = target_N` (the combinatorial identity);
* `TargetLowerBoundQ W target`: `target_N ≤ dim W_N` (the representation-theoretic input);
* `demazureBoundFor_of_Q`: together they give `DemazureBoundFor W hilb`.
-/

namespace VOA.DeligneAudit.DeligneCharacter

open VertexOperatorAlgebra

/-- `σ_k(n)`. -/
def sigmaK (k n : ℕ) : ℕ := ∑ d ∈ n.divisors, d ^ k

/-- The list `[c₀, …, c_N]` of the Arakawa–Kawasetsu recurrence with `h = h∨`. -/
def mldeList (h : ℕ) : ℕ → List ℚ
  | 0 => [1]
  | n + 1 =>
      let l := mldeList h n
      let N := n + 1
      l ++ [(∑ r ∈ Finset.range N,
          ((10 * ((h : ℚ) ^ 2 - 1) * sigmaK 3 (r + 1) -
            (24 * ((N : ℚ) - (r + 1)) + 2 * ((h : ℚ) + 1)) * sigmaK 1 (r + 1)) *
              l.getD (N - (r + 1)) 0)) / ((N : ℚ) * (6 * N + h))]

/-- `c_N`, the `q^N` coefficient of the AK solution. -/
def mldeCoeff (h N : ℕ) : ℚ := (mldeList h N).getD N 0

/-- The combinatorial identity `D_N = target_N` with a rational target. -/
structure StarIdentityQ (hilb : ℕ → ℕ → ℕ) (target : ℕ → ℚ) : Prop where
  eq : ∀ N, (demazureSumCoeff hilb N : ℚ) = target N

/-- The representation-theoretic input `target_N ≤ dim W_N`. -/
structure TargetLowerBoundQ {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (target : ℕ → ℚ) : Prop where
  le : ∀ N : ℕ, target N ≤ (Module.finrank ℂ (W.grading N) : ℚ)

theorem demazureBoundFor_of_Q {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W : VertexOperatorAlgebra V} {hilb : ℕ → ℕ → ℕ} {target : ℕ → ℚ}
    (hstar : StarIdentityQ hilb target) (hlow : TargetLowerBoundQ W target) :
    DemazureBoundFor W hilb :=
  ⟨fun N => by
    have h := (hstar.eq N).trans_le (hlow.le N)
    exact_mod_cast h⟩

/-- The recurrence reproduces the known first coefficients `1, dim g, c₂` (e.g. `G₂`: `1, 14, 92`). -/
theorem mldeCoeff_G2_small : (List.range 3).map (mldeCoeff 4) = [1, 14, 92] := by decide +kernel

end VOA.DeligneAudit.DeligneCharacter

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.demazureBoundFor_of_Q
#print axioms VOA.DeligneAudit.DeligneCharacter.mldeCoeff_G2_small
end AxiomAudit
