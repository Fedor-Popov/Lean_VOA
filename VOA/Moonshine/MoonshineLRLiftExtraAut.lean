import VOA.Moonshine.MoonshineLRLiftExtra
import VOA.Moonshine.MoonshineLRLiftNatural

/-!
# The extraspecial elements as automorphisms of `V♮` (lifting `2^{1+24}`)

For `μ ∈ Λ`, the pair (`extraLeechPlusAut μ` on `V_Λ⁺`, the normalised `e_μ`-action
`extraPlusIsometryEquiv μ` on `T⁺`) is compatible (`extraPlusIsometry_mode`) and preserves `TPForm`
(`extraPlusIsometry_form`), so naturality (`vnatAutOfPair`) gives **`extraVnatAut μ : AutVnat`**.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA.Moonshine VOA.Moonshine.AutMonster

/-- **The extraspecial element `μ` as an automorphism of `V♮`.** -/
def extraVnatAut (μ : leech.carrier) : AutVnat :=
  vnatAutOfPair (extraLeechPlusAut μ) (extraPlusIsometryEquiv μ)
    (fun u n t => extraPlusIsometry_mode μ u n t) (fun x y => extraPlusIsometry_form μ x y)

theorem extraVnatAut_apply (μ : leech.carrier) (u : SkewVP) (t : TP) :
    extraVnatAut μ ((u, t) : Vnat) = (extraLeechPlusAut μ u, extraPlusIsometry μ t) := by
  rw [extraVnatAut, vnatAutOfPair_apply]
  rfl

end VOA.Moonshine.ConwayNorton.M8
