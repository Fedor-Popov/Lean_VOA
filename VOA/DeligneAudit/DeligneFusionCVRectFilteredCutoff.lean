import VOA.DeligneAudit.DeligneFusionCVRectFilteredRegion
import VOA.DeligneAudit.DeligneFusionCVRectFilteredLeading
import VOA.DeligneAudit.DeligneFusionCVRectFilteredStar

/-!
# Empty-current cases and clipped-region source bounds

An empty source current kills its entire graded family. Nonzero powers of
that color therefore yield actual relations modulo shorter words. The other
cases have the exact reverse/excess-to-clipped arithmetic, with no positivity
restriction on the number of retained modes.
-/

namespace VOA.DeligneAudit.A2.CVRectFiltered

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.A2.CVFamily
open VOA.DeligneAudit.A2.CVRectCommutative
open VOA.DeligneAudit.A2.CVRectStarIdeal
open VOA.DeligneAudit.A2.CVRectStarCount

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule bracketTable V) (w : V)

theorem grFs_zero_of_source (a : Fin 3) (ha : ∀ k, R.op (negRoot a) k w = 0) :
    Garland.Fs (grOp R w a) = 0 := by
  apply PowerSeries.ext
  intro k
  simpa only [Garland.Fs, PowerSeries.coeff_mk, map_zero] using
    grOp_zero_of_source_zero R w a k (ha k)

theorem orderedCoeff_mem_of_first_zero (p q r s : ℕ) (hp : 0 < p)
    (hX : ∀ k, R.op 3 k w = 0) :
    orderedCoeff R w p q r s ∈ Pbelow R w (p + q + r) := by
  apply (orderedCoeff_mem_iff_zero R w p q r s).mpr
  simp only [gradedOrderedCoeff, grFs_zero_of_source R w 0 hX,
    zero_pow hp.ne', zero_mul, map_zero, LinearMap.zero_apply]

theorem orderedCoeff_mem_of_theta_zero (p q r s : ℕ) (hq : 0 < q)
    (hY : ∀ k, R.op 5 k w = 0) :
    orderedCoeff R w p q r s ∈ Pbelow R w (p + q + r) := by
  apply (orderedCoeff_mem_iff_zero R w p q r s).mpr
  simp only [gradedOrderedCoeff, grFs_zero_of_source R w 1 hY,
    zero_pow hq.ne', mul_zero, zero_mul, map_zero, LinearMap.zero_apply]

theorem orderedCoeff_mem_of_second_zero (p q r s : ℕ) (hr : 0 < r)
    (hZ : ∀ k, R.op 4 k w = 0) :
    orderedCoeff R w p q r s ∈ Pbelow R w (p + q + r) := by
  apply (orderedCoeff_mem_iff_zero R w p q r s).mpr
  simp only [gradedOrderedCoeff, grFs_zero_of_source R w 2 hZ,
    zero_pow hr.ne', mul_zero, map_zero, LinearMap.zero_apply]

/-- Exact clipped source relations imply all canonical reversed STAR
generator relations, including empty colors. -/
theorem star_relations_of_clipped (left right center : List ℕ)
    (hx : ∀ t, left.length ≤ t → R.op 3 t w = 0)
    (hy : ∀ t, left.length + right.length + center.length ≤ t → R.op 5 t w = 0)
    (hz : ∀ t, right.length ≤ t → R.op 4 t w = 0)
    (hrel : ∀ p q r s,
      clippedSum left (p + q) + clippedSum right (q + r) + clippedSum center q <
        s + (p + q + r) → orderedCoeff R w p q r s ∈ Pbelow R w (p + q + r))
    (p q r j : ℕ) (hj : j < starOrder left right center p q r)
    (hD : j ≤ reverseDegree left.length (left.length + right.length + center.length)
      right.length p q r) :
    orderedCoeff R w p q r
      (reverseDegree left.length (left.length + right.length + center.length) right.length p q r - j)
        ∈ Pbelow R w (p + q + r) := by
  by_cases hX : left.length = 0 ∧ 0 < p
  · exact orderedCoeff_mem_of_first_zero R w _ _ _ _ hX.2 (fun t => hx t (by omega))
  by_cases hY : left.length + right.length + center.length = 0 ∧ 0 < q
  · exact orderedCoeff_mem_of_theta_zero R w _ _ _ _ hY.2 (fun t => hy t (by omega))
  by_cases hZ : right.length = 0 ∧ 0 < r
  · exact orderedCoeff_mem_of_second_zero R w _ _ _ _ hZ.2 (fun t => hz t (by omega))
  exact hrel p q r _ (star_reverse_region left right center p q r j
    (by omega) (by omega) (by omega) hj hD)

/-- Count-transfer interface using the optimized clipped source region.
Its relation premise is the explicit actual current family being proved;
no leading-ideal or original dimension premise occurs. -/
theorem source_star_bound_of_clipped {ε ν ϱ : Weight} {j : ℕ}
    (h : CV3Rel R w ε ν ϱ j) (hspan : currentCyclic R w = ⊤)
    (left right center : List ℕ)
    (hx : ∀ t, left.length ≤ t → R.op 3 t w = 0)
    (hy : ∀ t, left.length + right.length + center.length ≤ t → R.op 5 t w = 0)
    (hz : ∀ t, right.length ≤ t → R.op 4 t w = 0)
    (hrel : ∀ p q r s,
      clippedSum left (p + q) + clippedSum right (q + r) + clippedSum center q <
        s + (p + q + r) → orderedCoeff R w p q r s ∈ Pbelow R w (p + q + r)) :
    FiniteDimensional ℂ V ∧ Module.finrank ℂ V ≤ starWeight left right center :=
  source_star_bound R w h hspan left right center hx hy hz
    (star_relations_of_clipped R w left right center hx hy hz hrel)

end

end VOA.DeligneAudit.A2.CVRectFiltered

#print axioms VOA.DeligneAudit.A2.CVRectFiltered.orderedCoeff_mem_of_first_zero
#print axioms VOA.DeligneAudit.A2.CVRectFiltered.star_relations_of_clipped
#print axioms VOA.DeligneAudit.A2.CVRectFiltered.source_star_bound_of_clipped
