import VOA.DeligneAudit.D4CharKernelEuler
import VOA.DeligneAudit.D4CharMixedFour

/-!
Specialize the proved mixed-Cauchy identity into the actual D4 Laurent series ring.
Both alphabets are (s*x,s/x). The following is the actual ring substitution of the
Euler kernel, not a newly defined series on which a Cauchy formula is assumed.
-/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open DeligneCharacter PowerSeries

noncomputable section

/-- The actual MC_(2,2,4) Euler product after homogeneous diagonal substitution. -/
def rsMixedKernel : D4K.S :=
  gtBiCollapseHom 1 1
    (gtFourCollapse (fun i => (rsXAlphabet i : D4K.R)) (fun i => (rsXAlphabet i : D4K.R))
      (gtMixedRankKernel rsNome rsPochhammerUnits rsZAlphabet 4))

/-- The substitution of the proved MC identity, as equality of complete series. -/
theorem rsMixedKernel_eq_series :
    rsMixedKernel = gtBiCollapseHom 1 1
      (gtMixedFourSeries rsNome rsPochhammerUnits rsXAlphabet rsXAlphabet rsZAlphabet) := by
  rw [rsMixedKernel, ← gtMixed_four]

/-- Every coefficient of the substituted kernel is its full finite GT expansion. -/
theorem rsMixedKernel_coeff (d : ℕ) :
    coeff d rsMixedKernel = ∑ t ∈ Finset.antidiagonal d,
      ∑ p ∈ gtPartitionsTwo t.2, ∑ z ∈ gtPartitionsTwo t.1,
        gtQ rsNome rsPochhammerUnits rsXAlphabet 2 ![(p.1 : ℤ), (p.2 : ℤ)] *
          gtQ rsNome rsPochhammerUnits rsXAlphabet 2 ![(z.1 : ℤ), (z.2 : ℤ)] *
            gtEval rsNome rsZAlphabet 4 (gtMixedFourRow p.1 p.2 z.1 z.2) := by
  rw [rsMixedKernel_eq_series]
  change coeff d (gtBiCollapse 1 1
    (gtMixedFourSeries rsNome rsPochhammerUnits rsXAlphabet rsXAlphabet rsZAlphabet)) = _
  simp only [gtBiCollapse, coeff_mk, one_pow, one_mul]
  apply Finset.sum_congr rfl
  intro t _
  simp [gtBiCoeff, gtMixedFourSeries]

/-- Orthogonality applied to each finite coefficient of the actual substituted kernel. -/
theorem rsMixedKernel_moment_coeff (d : ℕ) :
    rsMoment (coeff d rsMixedKernel) = ∑ t ∈ Finset.antidiagonal d,
      ∑ p ∈ gtPartitionsTwo t.2, ∑ z ∈ gtPartitionsTwo t.1,
        if p.1 - p.2 = z.1 - z.2 then
          ((D4K.qpoch (p.1 - p.2))⁻¹ * (D4K.qpoch p.2)⁻¹ * (D4K.qpoch z.2)⁻¹) •
            gtEval rsNome rsZAlphabet 4 (gtMixedFourRow p.1 p.2 z.1 z.2)
        else 0 := by
  rw [rsMixedKernel_coeff, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z hz
  exact rsMoment_mixed_term p.1 p.2 z.1 z.2
    ((mem_gtPartitionsTwo _ _).mp hp).2 ((mem_gtPartitionsTwo _ _).mp hz).2

/-- The substituted theta integral has no odd s-degree. -/
theorem rsMixedKernel_moment_odd (n : ℕ) :
    rsMoment (coeff (2 * n + 1) rsMixedKernel) = 0 := by
  rw [rsMixedKernel_moment_coeff]
  apply Finset.sum_eq_zero
  intro t ht
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro z hz
  have ht := Finset.mem_antidiagonal.mp ht
  have hp := (mem_gtPartitionsTwo _ _).mp hp
  have hz := (mem_gtPartitionsTwo _ _).mp hz
  rw [if_neg (by omega : p.1 - p.2 ≠ z.1 - z.2)]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.rsMixedKernel_eq_series
#print axioms VOA.DeligneAudit.D4Char.rsMixedKernel_coeff
#print axioms VOA.DeligneAudit.D4Char.rsMixedKernel_moment_coeff
#print axioms VOA.DeligneAudit.D4Char.rsMixedKernel_moment_odd
