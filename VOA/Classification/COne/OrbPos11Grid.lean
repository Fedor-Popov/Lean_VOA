import VOA.Classification.COne.OrbPos11Support

/-! # No coefficients are lost by restricting to the fractional grid -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbPos11
open VOA VOA.Huang.FusionUnit VOA.Huang.TensorCat
open VOA.Huang.TensorCat.BraidRibbon CategoryTheory OrbPos9 OrbPos10

variable (G : Subgroup (Aut (V2m 1 le_rfl)))
  (hSR : StronglyRational (orbifoldVOA G))
  (X : Ordinary (orbifoldVOA G))
  (a : tensorObj (fusionChoice_pbw hSR) (ambient G) X ⟶ X)

/-- Iterate covariance before using the finite order of the automorphism. -/
theorem action_coefficient_covariance_pow (g : G)
    (hm : ActionMonodromyThrough G hSR X a g) (z : ℂ) (n : ℕ)
    (v : (ambient G).carrier) (x : X.carrier) :
    (Phase.upper.c z * Phase.upper.c z) ^ n •
      (actionIntertwiner G hSR X a).val z ((g.1 ^ n) v) x =
        (actionIntertwiner G hSR X a).val z v x := by
  have hc (w : (ambient G).carrier) : (Phase.upper.c z * Phase.upper.c z) •
      (actionIntertwiner G hSR X a).val z (g.1 w) x =
        (actionIntertwiner G hSR X a).val z w x :=
    (actionMonodromyThrough_iff_coefficients G hSR X a g).mp hm z w x
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' g.1, Aut.mul_apply, pow_succ, mul_smul, hc, ih]

/-- Every nonzero coefficient lies on the fractional grid of any positive
period. This is stronger than support on eigenvectors: it covers every state. -/
theorem action_coefficient_grid (g : G)
    (hm : ActionMonodromyThrough G hSR X a g) {N : ℕ} (hN : 0 < N)
    (hg : g.1 ^ N = 1) (z : ℂ) (v : (ambient G).carrier) (x : X.carrier)
    (hne : (actionIntertwiner G hSR X a).val z v x ≠ 0) :
    ∃ k : ℤ, z = (k : ℂ) / N := by
  have h := action_coefficient_covariance_pow G hSR X a g hm z N v x
  rw [hg, Aut.one_apply] at h
  have hp : (Phase.upper.c z * Phase.upper.c z) ^ N = 1 := by
    apply sub_eq_zero.mp
    apply (smul_eq_zero.mp (show
      ((Phase.upper.c z * Phase.upper.c z) ^ N - 1) •
        (actionIntertwiner G hSR X a).val z v x = 0 by
          rw [sub_smul, h, one_smul, sub_self])).resolve_right hne
  rw [monodromy_phase, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff] at hp
  obtain ⟨m, hm⟩ := hp
  have ht : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : -(N : ℂ) * (z + 1) = m := by
    apply mul_left_cancel₀ ht
    linear_combination hm
  refine ⟨-m - N, ?_⟩
  apply (eq_div_iff hn).mpr
  push_cast
  linear_combination -he

/-- Stability under the fractional modes is stability under *all* coefficients
of the universal action field. Thus using the grid does not lose submodules. -/
theorem actionModes_stable_iff (g : G)
    (hm : ActionMonodromyThrough G hSR X a g) {N : ℕ} (hN : 0 < N)
    (hg : g.1 ^ N = 1) (P : Submodule ℂ X.carrier) :
    (∀ v k x, x ∈ P → actionModes G hSR X a N v k x ∈ P) ↔
      (∀ z v x, x ∈ P → (actionIntertwiner G hSR X a).val z v x ∈ P) := by
  constructor
  · intro h z v x hx
    by_cases he : (actionIntertwiner G hSR X a).val z v x = 0
    · rw [he]; exact P.zero_mem
    · obtain ⟨k, rfl⟩ := action_coefficient_grid G hSR X a g hm hN hg z v x he
      exact h v k x hx
  · intro h v k x hx
    exact h _ v x hx

end VOA.Classification.COne.OrbPos11
