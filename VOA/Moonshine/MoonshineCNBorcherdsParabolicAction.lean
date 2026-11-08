import VOA.Moonshine.MoonshineCNBorcherdsGeneratorWeights
import VOA.Moonshine.MoonshineCNLieProjection

/-! The Levi quotient of the opposite parabolic and its action on U. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton.BorcherdsData

open Module
variable {g : Type*} [LieRing g] [LieAlgebra ℂ g] (D : BorcherdsData g)

def parabolicLeviSpace : Submodule ℂ D.parabolicPart :=
  D.leviPart.toSubmodule.comap D.parabolicPart.toSubmodule.subtype

def parabolicNegativeSpace : Submodule ℂ D.parabolicPart :=
  D.negativePart.toSubmodule.comap D.parabolicPart.toSubmodule.subtype

theorem parabolic_levi_negative_isCompl :
    IsCompl D.parabolicLeviSpace D.parabolicNegativeSpace := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hl hn
    apply Subtype.ext
    exact Submodule.disjoint_def.mp D.levi_negative_disjoint x hl hn
  · apply codisjoint_iff.mpr
    apply top_unique
    intro x _
    have hx : (x : g) ∈ D.leviPart.toSubmodule ⊔ D.negativePart.toSubmodule := by
      rw [← D.parabolic_eq_levi_sup_negative]
      exact x.property
    obtain ⟨l, hl, n, hn, hsum⟩ := Submodule.mem_sup.mp hx
    exact Submodule.mem_sup.mpr
      ⟨⟨l, D.leviPart_le_parabolic hl⟩, hl,
        ⟨n, D.negativePart_le_parabolic hn⟩, hn, Subtype.ext hsum⟩

/-- Linear Levi projection along the negative ideal. -/
def parabolicLeviProjectionLinear : D.parabolicPart →ₗ[ℂ] D.leviPart :=
  leviProjectionOfComplement D.parabolicPart D.leviPart D.parabolicNegativeSpace
    D.parabolic_levi_negative_isCompl

theorem parabolicLeviProjection_residual (x : D.parabolicPart) :
    (x : g) - (D.parabolicLeviProjectionLinear x : g) ∈ D.negativePart := by
  obtain ⟨r, hr, heq⟩ := leviProjectionOfComplement_residual D.parabolicPart D.leviPart
    D.parabolicNegativeSpace D.parabolic_levi_negative_isCompl x
  change (r : g) ∈ D.negativePart at hr
  exact heq ▸ hr

theorem parabolicLeviProjection_left (x : D.leviPart) :
    D.parabolicLeviProjectionLinear ⟨x, D.leviPart_le_parabolic x.property⟩ = x :=
  leviProjectionOfComplement_left D.parabolicPart D.leviPart D.parabolicNegativeSpace
    D.parabolic_levi_negative_isCompl D.leviPart_le_parabolic x

theorem parabolicLeviProjection_right (x : D.parabolicPart) (hx : (x : g) ∈ D.negativePart) :
    D.parabolicLeviProjectionLinear x = 0 :=
  leviProjectionOfComplement_right D.parabolicPart D.leviPart D.parabolicNegativeSpace
    D.parabolic_levi_negative_isCompl x hx

/-- Projection is a Lie homomorphism because the negative cone is an ideal. -/
def parabolicLeviProjection : D.parabolicPart →ₗ⁅ℂ⁆ D.leviPart where
  __ := D.parabolicLeviProjectionLinear
  map_lie' {x y} := by
    let lx : D.parabolicPart :=
      ⟨D.parabolicLeviProjectionLinear x, D.leviPart_le_parabolic
        (D.parabolicLeviProjectionLinear x).property⟩
    let ly : D.parabolicPart :=
      ⟨D.parabolicLeviProjectionLinear y, D.leviPart_le_parabolic
        (D.parabolicLeviProjectionLinear y).property⟩
    have hn : ((⁅x, y⁆ - ⁅lx, ly⁆ : D.parabolicPart) : g) ∈ D.negativePart := by
      have h₁ := D.parabolic_normalizes_negative x.property (D.parabolicLeviProjection_residual y)
      have h₂ := D.parabolic_normalizes_negative ly.property (D.parabolicLeviProjection_residual x)
      have h₂' : ⁅(x : g) - (lx : g), (ly : g)⁆ ∈ D.negativePart := by
        rw [← lie_skew]
        exact D.negativePart.neg_mem h₂
      have h := D.negativePart.add_mem h₁ h₂'
      change ⁅(x : g), (y : g) - (ly : g)⁆ + ⁅(x : g) - (lx : g), (ly : g)⁆ ∈ _ at h
      simp only [lie_sub, sub_lie] at h
      change ⁅(x : g), (y : g)⁆ - ⁅(lx : g), (ly : g)⁆ ∈ _
      convert h using 1
      abel
    have h := D.parabolicLeviProjection_right (⁅x, y⁆ - ⁅lx, ly⁆) hn
    rw [map_sub] at h
    have hleft : D.parabolicLeviProjectionLinear ⁅lx, ly⁆ =
        ⁅D.parabolicLeviProjectionLinear x, D.parabolicLeviProjectionLinear y⁆ :=
      by
        convert D.parabolicLeviProjection_left
          ⁅D.parabolicLeviProjectionLinear x, D.parabolicLeviProjectionLinear y⁆ using 1
    rw [hleft] at h
    exact sub_eq_zero.mp h

/-- The parabolic acts on U through its Levi quotient; the negative ideal acts by zero. -/
def genSpaceParabolicRep (e f : g)
    (he : e ∈ D.weightSpace borcherdsRealRoot)
    (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1) :
    D.parabolicPart →ₗ⁅ℂ⁆ End ℂ (D.genSpace e) :=
  (LieModule.toEnd ℂ D.leviPart (D.genSpaceLeviSubmodule e f he hf hef)).comp
    D.parabolicLeviProjection

theorem genSpaceParabolicRep_levi (e f : g)
    (he : e ∈ D.weightSpace borcherdsRealRoot)
    (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1)
    (x : D.leviPart) (u : D.genSpace e) :
    (D.genSpaceParabolicRep e f he hf hef ⟨x, D.leviPart_le_parabolic x.property⟩ u : g) =
      ⁅(x : g), (u : g)⁆ := by
  change (LieModule.toEnd ℂ D.leviPart (D.genSpaceLeviSubmodule e f he hf hef)
    (D.parabolicLeviProjectionLinear ⟨x, D.leviPart_le_parabolic x.property⟩) u : g) = _
  rw [D.parabolicLeviProjection_left]
  rfl

theorem genSpaceParabolicRep_negative (e f : g)
    (he : e ∈ D.weightSpace borcherdsRealRoot)
    (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1)
    (x : D.parabolicPart) (hx : (x : g) ∈ D.negativePart) :
    D.genSpaceParabolicRep e f he hf hef x = 0 := by
  change LieModule.toEnd ℂ D.leviPart (D.genSpaceLeviSubmodule e f he hf hef)
    (D.parabolicLeviProjectionLinear x) = 0
  rw [D.parabolicLeviProjection_right x hx, map_zero]

end VOA.Moonshine.ConwayNorton.BorcherdsData
