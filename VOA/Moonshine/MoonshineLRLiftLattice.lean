import VOA.Moonshine.LatticeMorph
import VOA.Moonshine.LatticeInvolution

/-!
# Lattice isometries act on `V_Λ` and on `V_Λ⁺` (lifting `Co₀`)

For a surjective isometry `ι` of the Leech lattice, `Φ_ι = latMorph leech leech ι` is a
bijective VOA endomorphism of `V_Λ` commuting with `θ`:
* `latMorphAut ι hι hsurj : Aut leechVOA`, with `latMorphAut_apply`;
* `leechPlusAutOfTheta g hg`: an automorphism of `V_Λ` commuting with `θ` restricts to `V_Λ⁺`;
* **`leechPlusLatMorphAut ι hι hsurj : Aut leechVOAPlus`**, acting by `Φ_ι` on `V_Λ⁺`.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine LatGen

variable (ι : leech.carrier →ₗ[ℤ] leech.carrier)
  (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β) (hsurj : Function.Surjective ι)

include hι hsurj in
theorem latMorph_surjective_of_surjective : Function.Surjective (latMorph leech leech ι) := by
  intro x
  have hx : x ∈ LinearMap.range (latMorph leech leech ι) :=
    (mem_range_latMorph_iff leech leech ι leech_posDef leech_posDef hι rfl x).mpr
      fun γ hγ => absurd (hsurj γ) (by simpa [Set.mem_range] using hγ)
  exact hx

/-- `Φ_ι` as an automorphism of `V_Λ`. -/
def latMorphAut : Aut leechVOA where
  toLinearEquiv := LinearEquiv.ofBijective (latMorph leech leech ι)
    ⟨latMorph_injective leech leech ι leech_posDef leech_posDef hι rfl,
      latMorph_surjective_of_surjective ι hι hsurj⟩
  map_smul' u n v :=
    (latMorph_isVOAHom leech leech ι leech_posDef leech_posDef hι leech_even leech_even).map_smul
      u n v
  map_vacuum := latMorph_vacuum leech leech ι
  map_omega := latMorph_omega leech leech ι leech_posDef leech_posDef hι rfl

@[simp] theorem latMorphAut_apply (v : LatModuleGen leech) :
    latMorphAut ι hι hsurj v = latMorph leech leech ι v := rfl

/-- An automorphism of `V_Λ` commuting with `θ` restricts to `V_Λ⁺`. -/
def leechPlusAutOfTheta (g : Aut leechVOA) (hg : ∀ x, g (thetaLat leech x) = thetaLat leech (g x)) :
    Aut leechVOAPlus where
  toLinearEquiv :=
    { toFun := fun x => ⟨g x, (mem_leechVOAPlus_iff _).mpr (by
        rw [← hg, ((mem_leechVOAPlus_iff _).mp x.2)])⟩
      invFun := fun x => ⟨g.toLinearEquiv.symm x, (mem_leechVOAPlus_iff _).mpr (by
        apply g.toLinearEquiv.injective
        rw [LinearEquiv.apply_symm_apply, Aut.coe_toLinearEquiv, hg, ← Aut.coe_toLinearEquiv,
          LinearEquiv.apply_symm_apply, ((mem_leechVOAPlus_iff _).mp x.2)])⟩
      left_inv := fun x => Subtype.ext (g.toLinearEquiv.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (g.toLinearEquiv.apply_symm_apply x)
      map_add' := fun x y => Subtype.ext (map_add g.toLinearEquiv x.val y.val)
      map_smul' := fun c x => Subtype.ext (map_smul g.toLinearEquiv c x.val) }
  map_smul' := fun x n y => Subtype.ext (g.map_smul' x n y)
  map_vacuum := Subtype.ext g.map_vacuum
  map_omega := Subtype.ext g.map_omega

@[simp] theorem leechPlusAutOfTheta_apply (g : Aut leechVOA)
    (hg : ∀ x, g (thetaLat leech x) = thetaLat leech (g x))
    (x : (orbifold (Subgroup.zpowers leechTheta)).carrier) :
    ((leechPlusAutOfTheta g hg x : (orbifold (Subgroup.zpowers leechTheta)).carrier) :
      LatModuleGen leech) = g x := rfl

/-- **`Co₀` on `V_Λ⁺`:** `Φ_ι` as an automorphism of `V_Λ⁺`. -/
def leechPlusLatMorphAut : Aut leechVOAPlus :=
  leechPlusAutOfTheta (latMorphAut ι hι hsurj) fun x => latMorph_thetaLat leech leech ι x

end VOA.Moonshine.ConwayNorton.M8
