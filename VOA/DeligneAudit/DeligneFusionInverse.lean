/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2Final

/-!
# U6 by the choice of `F`: the fusion characters as the inverse of the mixed recursion

`A2.classicallyFree_of_fusion F hU5 hU6` leaves `F` free.  The mixed recursion of U6,
`Dem n = ∑_{d ≤ n} q^{dn} [n,d]_q F_{n-d}` (`DeligneGaussian.mixed_eq`), is unitriangular in `F`, so it
has a unique solution `fusionF` (`fusionF n = Dem n - ∑_{d=1}^{n} q^{dn}[n,d]_q fusionF (n-d)`).
For this `F`, U6 holds by construction (`mixedFusionRecursion_fusionF`), and the A₂ case rests
on U5 alone (`classicallyFree_of_fusionBound`).

By uniqueness `fusionF m` is Ravinder's fusion character `f_m` (graded character of the fusion product
`V(θ)^{*m} = W_loc(mθ)/⟨(f_α ⊗ t^m) w⟩`), so U5 for `fusionF` is Ravinder Prop. 1 + Prop. 5
(Feigin) read through Ravinder Cor. 1.  Exact computation (outside Lean):
`fusionF 0 = 1`, `fusionF 1 = 8`, `fusionF 2 = 27 + 28q + 9q²`,
`fusionF 3 = 64 + 97q + 152q² + 111q³ + 71q⁴ + 16q⁵ + q⁶`; `fusionF m (1) = 8^m` and
`[q⁰] fusionF m = (m+1)³ = dim V(mθ)` for `m ≤ 5`.
-/

namespace VOA.DeligneAudit.A2

open PowerSeries VOA.DeligneGaussian VOA.DeligneHigherRankConditionalCapstone

noncomputable section

/-- **The fusion characters**: the unique solution of the mixed recursion with `M_{n,0} = Dem n`. -/
def fusionF : ℕ → PowerSeries ℚ
  | n => demazureHilbSeries n -
      ∑ d : Fin n, X ^ ((d.1 + 1) * n) * qbinom (X : PowerSeries ℚ) n (d.1 + 1) * fusionF (n - (d.1 + 1))
decreasing_by omega

theorem fusionF_eq (n : ℕ) : fusionF n = demazureHilbSeries n -
    ∑ d ∈ Finset.range n, X ^ ((d + 1) * n) * qbinom (X : PowerSeries ℚ) n (d + 1) *
      fusionF (n - (d + 1)) := by
  rw [fusionF, Fin.sum_univ_eq_sum_range (fun d => X ^ ((d + 1) * n) *
    qbinom (X : PowerSeries ℚ) n (d + 1) * fusionF (n - (d + 1))) n]

/-- **U6 holds for `fusionF`** (by construction). -/
theorem mixedFusionRecursion_fusionF : MixedFusionRecursion fusionF demazureHilbSeries := by
  refine ⟨fun n => ?_⟩
  rw [mixed_eq, Finset.sum_range_succ']
  simp only [zero_mul, pow_zero, qbinom_zero_right, mul_one, one_mul, add_zero, Nat.sub_zero]
  rw [fusionF_eq n]
  ring

/-- **A₂ Deligne classical freeness, conditional only on U5** (for the explicit `fusionF`). -/
theorem classicallyFree_of_fusionBound (hU5 : SectorWeyl.FusionModuleBound fusionF) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_fusion fusionF hU5 mixedFusionRecursion_fusionF

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.mixedFusionRecursion_fusionF
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_fusionBound
end AxiomAudit
