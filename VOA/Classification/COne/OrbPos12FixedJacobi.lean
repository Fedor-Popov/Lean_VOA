import VOA.Classification.COne.OrbPos11Fields

/-! The actual fractional-mode Jacobi identity with first insertion in U.
This is a proper special case: the second insertion is arbitrary in A, and
the other mode index can be fractional. It does not imply full twisted Jacobi. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbPos12
open VOA CategoryTheory VOA.Huang.TensorCat VOA.Huang.FusionUnit
open OrbPos9 OrbPos11

variable (G : Subgroup (Aut (V2m 1 le_rfl)))
  (hSR : StronglyRational (orbifoldVOA G)) (X : Ordinary (orbifoldVOA G))
  (a : tensorObj (fusionChoice_pbw hSR) (ambient G) X ⟶ X)

/-- Reindexing the actual intertwiner on a positive-denominator grid. -/
theorem actionModes_grid_add {N : ℕ} (hN : 0 < N)
    (v : (ambient G).carrier) (m k : ℤ) :
    actionModes G hSR X a N v (m + N * k) =
      (actionIntertwiner G hSR X a).val ((m : ℂ) / N + k) v := by
  change (actionIntertwiner G hSR X a).val (((m + N * k : ℤ) : ℂ) / N) v = _
  congr 1
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp

set_option maxHeartbeats 1000000 in
-- Fractional reindexing unfolds the concrete lattice scalar structures.
/-- Jacobi for a fixed-point first insertion, proved from the intertwiner's
U-Jacobi identity and the already proved restriction of the action to U. -/
theorem actionModes_jacobi_fixed (E : CanonicalExtensionAlgebra G hSR)
    (ha : ActionLaws G hSR E X a) {N : ℕ} (hN : 0 < N)
    (u : (orbifold G).carrier) (v : (ambient G).carrier) (x : X.carrier) (ℓ k m : ℤ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
      (actionModes G hSR X a N u.1 (N * (ℓ + k - i))
        (actionModes G hSR X a N v (m + N * i) x) -
       negOnePow ℓ • actionModes G hSR X a N v (m + N * (ℓ - i))
        (actionModes G hSR X a N u.1 (N * (k + i)) x))) =
      ∑ᶠ i : ℕ, cbinom (k : ℂ) i •
        actionModes G hSR X a N ((V2m 1 le_rfl).smul u.1 (ℓ + i) v)
          (m + N * (k - i)) x := by
  have hj := (actionIntertwiner G hSR X a).property.jacobi u v x ℓ k ((m : ℂ) / N)
  conv at hj =>
    rhs
    rw [VOA.TwistedReduction.finsum_int_eq_finsum_nat _ (fun i hi => by
      rw [cbz_apply_neg k hi, zero_smul])]
  calc
    _ = (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (mode (X.isMod.YM u) (ℓ + k - i)
          ((actionIntertwiner G hSR X a).val ((m : ℂ) / N + i) v x) -
          negOnePow ℓ • (actionIntertwiner G hSR X a).val (ℓ + (m : ℂ) / N - i) v
            (mode (X.isMod.YM u) (k + i) x))) := by
      apply finsum_congr
      intro i
      rw [actionModes_fixed G hSR E X a ha hN,
        actionModes_fixed G hSR E X a ha hN,
        actionModes_grid_add G hSR X a hN, actionModes_grid_add G hSR X a hN]
      congr 3
      push_cast
      ring
    _ = _ := hj.trans (by
      apply finsum_congr
      intro i
      rw [VOA.TwistedReduction.cbz_natCast, actionModes_grid_add G hSR X a hN]
      change cbinom (k : ℂ) i • (actionIntertwiner G hSR X a).val
          ((k : ℂ) + (m : ℂ) / N - (i : ℤ))
          ((V2m 1 le_rfl).smul u.1 (ℓ + i) v) x = _
      congr 2
      push_cast
      ring)

end VOA.Classification.COne.OrbPos12
