/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterExceptionalData
import VOA.DeligneAudit.DeligneCharacterExceptionalAssembly
import VOA.DeligneAudit.DeligneCharacterExceptionalCoeffG2M1N0
import VOA.DeligneAudit.DeligneCharacterExceptionalCoeffG2M1N1
import VOA.DeligneAudit.DeligneCharacterExceptionalCoeffG2M1N2
import VOA.DeligneAudit.DeligneCharacterExceptionalCoeffF4M1N0
import VOA.DeligneAudit.DeligneCharacterExceptionalCoeffF4M1N1
import VOA.DeligneAudit.DeligneCharacterExceptionalCoeffF4M1N2
import VOA.DeligneAudit.DeligneCharacterExceptionalCoeffE6M1N0
import VOA.DeligneAudit.DeligneCharacterExceptionalCoeffE6M1N1
import VOA.DeligneAudit.DeligneCharacterExceptionalCoeffE6M1N2
import VOA.DeligneAudit.DeligneCharacterExceptionalStarG2N0
import VOA.DeligneAudit.DeligneCharacterExceptionalStarG2N1
import VOA.DeligneAudit.DeligneCharacterExceptionalStarG2N2
import VOA.DeligneAudit.DeligneCharacterExceptionalStarF4N0
import VOA.DeligneAudit.DeligneCharacterExceptionalStarF4N1

/-!
# Character data for `G₂, F₄, E₆, E₇, E₈`

Per type: Cartan matrix (Bourbaki labelling, row `i` = pairings with `α_i^∨`, i.e. `A_{ij} = ⟨α_j,
α_i^∨⟩`),
highest root `θ` in simple-root coordinates, a reduced word for `s_θ` (computed by right descents
from
the reflection `s_θ`, length `2 ht(θ∨) - 1`), the Demazure Hilbert series `levelOneDemazureHilb`,
and the
AK target `mldeCoeff h∨`.

**Non-simply-laced types.** The generic algorithm is correct for `G₂` and `F₄` without change:
* finite `D_i` uses `⟨μ, α_i^∨⟩ = ∑_j A_{ij} μ_j`, valid for any Cartan matrix in this convention;
* `D₀` uses `1 - ∑_i ⟨θ, α_i^∨⟩ μ_i`, which equals `1 - ⟨μ, θ∨⟩` because `θ` is long and
  orthogonal to
  every short simple root (in `G₂`, `F₄` the affine node attaches to a long simple root);
* the extremal vector of `(s_θ s₀)^m Λ₀` has energy `-m²` (θ long), so the regrading by `m²` is
  unchanged.

Checked outside Lean (Python, same algorithm): `Hilb D(1,θ) = dim g + q` for all five types, and the
Demazure
sums agree with the AK recurrence through `q⁴` (`G₂`), `q³` (`F₄`), `q²` (`E₆, E₇, E₈`).

Named inputs per type (all `ℚ`-valued, see `DeligneCharacterTypes`):
* `XStarIdentity := StarIdentityQ xDemazureHilb (mldeCoeff h∨)`: the paper's identity
  `∑ q^n Hilb D(1,nθ)/(q)_n = ch L_k(g)`, in its unflavoured form against the MLDE solution.
  Literature (audit "Type inputs"): `G₂` Macdonald/Cherednik constant terms with `t_long → 0`;
  `F₄` van Diejen–Emsiz (two operators); `E₆–E₈` van Diejen–Emsiz; U7 in all cases.
* `XTargetLowerBound W := TargetLowerBoundQ W (mldeCoeff h∨)`: `ch L_k(g) ≥ c_N`.
  Literature: AK MLDE for the simple quotient, with the right side identified by the KW admissible
  formula (`G₂`: twisted `D₄^{(3)}` numerator; `F₄`: twisted `E₆^{(2)}`) or by
  Bezrukavnikov–Kac–Krylov Prop. 2.13 (`E₆–E₈`, branch node, `w_i ∘ (-bΛ₀) = -Λ_i`).
  **Now proved in Lean for every type** (for the cert-basis VOA of each file):
  `G2Lie.g2_targetLowerBound`, `F4Lie.f4_targetLowerBound`, `DeligneCarrier.E6.e6_targetLowerBound`,
  `E7Lie.e7_targetLowerBound`, `E8Lie.targetLowerBoundQ8` (all in `VOA.DeligneAudit`, via
  `targetLowerBound_of_carrierData`).  The route (`finrank_eq_mldeCoeff_of_isAKSolution`) in fact
  gives equality.
-/

namespace VOA.DeligneAudit.DeligneCharacter

open VertexOperatorAlgebra

theorem g2DemazureHilb_one : (List.range 3).map (g2DemazureHilb 1) = [14, 1, 0] := by
  exact exceptional_map_three (g2DemazureHilb 1) 14 1 0
    exceptional_g2_m1_n0 exceptional_g2_m1_n1 exceptional_g2_m1_n2

theorem f4DemazureHilb_one : (List.range 3).map (f4DemazureHilb 1) = [52, 1, 0] := by
  exact exceptional_map_three (f4DemazureHilb 1) 52 1 0
    exceptional_f4_m1_n0 exceptional_f4_m1_n1 exceptional_f4_m1_n2

theorem e6DemazureHilb_one : (List.range 3).map (e6DemazureHilb 1) = [78, 1, 0] := by
  exact exceptional_map_three (e6DemazureHilb 1) 78 1 0
    exceptional_e6_m1_n0 exceptional_e6_m1_n1 exceptional_e6_m1_n2

theorem g2_star_upto_two : ∀ N ∈ List.range 3,
    (demazureSumCoeff g2DemazureHilb N : ℚ) = mldeCoeff 4 N := by
  exact exceptional_check_three
    (fun N => (demazureSumCoeff g2DemazureHilb N : ℚ) = mldeCoeff 4 N)
    exceptional_g2_star_n0 exceptional_g2_star_n1 exceptional_g2_star_n2

theorem f4_star_upto_one : ∀ N ∈ List.range 2,
    (demazureSumCoeff f4DemazureHilb N : ℚ) = mldeCoeff 9 N := by
  exact exceptional_check_two
    (fun N => (demazureSumCoeff f4DemazureHilb N : ℚ) = mldeCoeff 9 N)
    exceptional_f4_star_n0 exceptional_f4_star_n1

end VOA.DeligneAudit.DeligneCharacter

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.g2DemazureHilb_one
#print axioms VOA.DeligneAudit.DeligneCharacter.f4DemazureHilb_one
#print axioms VOA.DeligneAudit.DeligneCharacter.e6DemazureHilb_one
#print axioms VOA.DeligneAudit.DeligneCharacter.g2_star_upto_two
#print axioms VOA.DeligneAudit.DeligneCharacter.f4_star_upto_one
end AxiomAudit
