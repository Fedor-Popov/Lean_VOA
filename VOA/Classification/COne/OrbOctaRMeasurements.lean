import VOA.Classification.COne.OrbOctaRNumbers

/-! Coefficient extraction from two linear functionals.

The state-level spanning theorem supplies existence. Thus a finite numerical
certificate only has to identify two measurements; it need not expand a large
Virasoro descendant expression. The functionals must annihilate the stated
intrinsic error space. Numerical tables alone do not supply that hypothesis.
-/

set_option Elab.async false

noncomputable section
namespace VOA.Classification.COne.OrbOctaR
open VOA VertexOperatorAlgebra OrbOcta OrbC2b OrbC2c

section General
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Two independent measurements uniquely determine a known two-term remainder. -/
theorem remainder_of_measurements (S : Submodule ℂ V) (u v y : V) (a b : ℂ)
    (f g : V →ₗ[ℂ] ℂ) (hf : S ≤ f.ker) (hg : S ≤ g.ker)
    (hdet : f u * g v - g u * f v ≠ 0)
    (hex : ∃ c d : ℂ, y - (c • u + d • v) ∈ S)
    (hyf : f y = a * f u + b * f v) (hyg : g y = a * g u + b * g v) :
    y - (a • u + b • v) ∈ S := by
  obtain ⟨c, d, hcd⟩ := hex
  have hf0 : f (y - (c • u + d • v)) = 0 := hf hcd
  have hg0 : g (y - (c • u + d • v)) = 0 := hg hcd
  simp only [map_sub, map_add, map_smul, smul_eq_mul] at hf0 hg0
  have he1 : f u • (c - a) + f v • (d - b) = 0 := by
    simp only [smul_eq_mul]
    linear_combination hyf - hf0
  have he2 : g u • (c - a) + g v • (d - b) = 0 := by
    simp only [smul_eq_mul]
    linear_combination hyg - hg0
  obtain ⟨hc, hd⟩ := exceptional_two_relations_vanish hdet he1 he2
  rw [sub_eq_zero] at hc hd
  simpa only [hc, hd] using hcd

end General

/-- A certificate at either requested weight can use measurements instead of descendants. -/
theorem mode_remainder_of_measurements (r : ℕ) (hr : 8 ≤ r) (hmax : r < 18)
    (a b : ℂ) (f g : (orbifold octa).carrier →ₗ[ℂ] ℂ)
    (hf : virError W W.vacuum ⊔ virError W X ≤ f.ker)
    (hg : virError W W.vacuum ⊔ virError W X ≤ g.ker)
    (hdet : f (((W.L (-2)) ^ r) W.vacuum) * g (((W.L (-2)) ^ (r - 8)) X) -
      g (((W.L (-2)) ^ r) W.vacuum) * f (((W.L (-2)) ^ (r - 8)) X) ≠ 0)
    (hyf : f (W.smul X (31 - 2 * r) X) =
      a * f (((W.L (-2)) ^ r) W.vacuum) + b * f (((W.L (-2)) ^ (r - 8)) X))
    (hyg : g (W.smul X (31 - 2 * r) X) =
      a * g (((W.L (-2)) ^ r) W.vacuum) + b * g (((W.L (-2)) ^ (r - 8)) X)) :
    W.smul X (31 - 2 * r) X -
      (a • ((W.L (-2)) ^ r) W.vacuum + b • ((W.L (-2)) ^ (r - 8)) X) ∈
        virError W W.vacuum ⊔ virError W X :=
  remainder_of_measurements _ _ _ _ a b f g hf hg hdet
    (mode_remainder_exists r hr hmax) hyf hyg

end VOA.Classification.COne.OrbOctaR
