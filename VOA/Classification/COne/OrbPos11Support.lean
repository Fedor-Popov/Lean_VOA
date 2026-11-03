import VOA.Classification.COne.OrbPos10Monodromy
import VOA.Classification.COne.OrbPos8Lowest

/-! # Fractional support of categorical monodromy

These are the actual coefficients obtained by postcomposing the universal
intertwiner with the given action. No twisted Jacobi identity is assumed in
the support theorem. The sign agrees with `TwistedModule.support`.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbPos11
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct VOA.Huang.TensorCat
open VOA.Huang.TensorCat.BraidRibbon VOA.Huang.BraidingSkew
open CategoryTheory OrbPos9 OrbPos10

variable (G : Subgroup (Aut (V2m 1 le_rfl)))
  (hSR : StronglyRational (orbifoldVOA G))
  (X : Ordinary (orbifoldVOA G))
  (a : tensorObj (fusionChoice_pbw hSR) (ambient G) X ⟶ X)

/-- The candidate field, with all complex-index coefficients retained. -/
def actionIntertwiner : IntertwiningOperator (ambient G).isMod X.isMod X.isMod :=
  postcompose ((fusionChoice_pbw hSR) (ambient G) X).intertwiner X.isMod a

/-- Fractional modes of that same field, with denominator `N`. -/
def actionModes (N : ℕ) : (ambient G).carrier →ₗ[ℂ] (ℤ → Module.End ℂ X.carrier) where
  toFun v k := (actionIntertwiner G hSR X a).val ((k : ℂ) / N) v
  map_add' v w := by funext k; exact map_add _ v w
  map_smul' c v := by funext k; exact map_smul _ c v

/-- The concrete phase in the coefficient monodromy equation. -/
theorem monodromy_phase (z : ℂ) :
    Phase.upper.c z * Phase.upper.c z =
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (z + 1)) :=
  omegaPhase_sq z

set_option maxHeartbeats 1000000 in
-- Unfolding the lattice carrier to identify its scalar action is expensive.
/-- An eigenvector coefficient can survive only when its scalar monodromy is one. -/
theorem action_coefficient_phase (g : G)
    (hm : ActionMonodromyThrough G hSR X a g) (z c : ℂ)
    (v : (ambient G).carrier) (hv : g.1 v = c • v) (x : X.carrier)
    (hne : (actionIntertwiner G hSR X a).val z v x ≠ 0) :
    (Phase.upper.c z * Phase.upper.c z) * c = 1 := by
  have h := (actionMonodromyThrough_iff_coefficients G hSR X a g).mp hm z v x
  rw [hv] at h
  erw [map_smul, LinearMap.smul_apply, map_smul] at h
  change (Phase.upper.c z * Phase.upper.c z) •
    (c • (actionIntertwiner G hSR X a).val z v x) =
      (actionIntertwiner G hSR X a).val z v x at h
  have hz : ((Phase.upper.c z * Phase.upper.c z) * c - 1) •
      (actionIntertwiner G hSR X a).val z v x = 0 := by
    rw [sub_smul, mul_smul, h, one_smul, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hne)

/-- The scalar compatibility is exactly the required residue class. -/
theorem fractional_phase_iff {N : ℕ} (hN : 0 < N) (k : ℤ) (j : ℕ) :
    (Phase.upper.c ((k : ℂ) / N) * Phase.upper.c ((k : ℂ) / N)) *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * j) / N) = 1 ↔
        (k + j) % (N : ℤ) = 0 := by
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [monodromy_phase, ← Complex.exp_add]
  have he : -(2 * (Real.pi : ℂ) * Complex.I) * ((k : ℂ) / N + 1) +
      -(2 * (Real.pi : ℂ) * Complex.I * j) / N =
      2 * (Real.pi : ℂ) * Complex.I * ((-(k + j + N) : ℤ) : ℂ) / N := by
    push_cast
    field_simp
    ring
  rw [he]
  change OrbPos5.phase N (-(k + j + N)) = 1 ↔ _
  rw [show (1 : ℂ) = OrbPos5.phase N 0 by simp [OrbPos5.phase],
    OrbPos5.phase_eq_iff hN]
  simp only [sub_zero, ← Int.dvd_iff_emod_eq_zero]
  constructor
  · intro h
    have h' := dvd_neg.mp h
    exact (dvd_add_left (dvd_refl (N : ℤ))).mp h'
  · intro h
    exact dvd_neg.mpr (dvd_add h (dvd_refl (N : ℤ)))

/-- Categorical twistedness proves the exact support axiom for the candidate
fractional fields, on every state and every test vector. -/
theorem actionModes_support (g : G) (hm : ActionMonodromyThrough G hSR X a g)
    {N : ℕ} (hN : 0 < N) (j : ℕ) (v : (ambient G).carrier)
    (hv : v ∈ g.1.twistedEigenspace N j) (k : ℤ)
    (hk : (k + j) % (N : ℤ) ≠ 0) : actionModes G hSR X a N v k = 0 := by
  ext x
  change (actionIntertwiner G hSR X a).val ((k : ℂ) / N) v x = 0
  by_contra hne
  apply hk
  apply (fractional_phase_iff hN k j).mp
  apply action_coefficient_phase G hSR X a g hm _ _ v _ x hne
  exact Module.End.mem_eigenspace_iff.mp hv

end VOA.Classification.COne.OrbPos11
