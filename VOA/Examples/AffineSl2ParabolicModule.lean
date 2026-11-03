import VOA.Examples.AffineSl2Verma

/-! # The actual finite-horizontal affine highest module

This is the affine Verma left-ideal quotient with the additional relation
F₀^(d+1)v=0 at horizontal highest weight d. No basis or character is assumed.
-/
namespace VOA.AffineVOA.HighestModule
noncomputable section
open UniversalEnvelopingAlgebra
open Module (End)

/-- The finite horizontal relation, as an actual enveloping element. -/
def parabolicRelation (d : ℕ) : U := (ι ℂ (modeElement 1 0))^(d+1)

/-- The actual parabolic highest-weight left ideal. -/
def parabolicIdeal (k : ℂ) (d : ℕ) : Submodule U U :=
  highestIdeal k (d:ℂ) ⊔ Submodule.span U {parabolicRelation d}

/-- The genuine parabolic induced module with finite horizontal spin d/2. -/
abbrev Parabolic (k : ℂ) (d : ℕ) := U ⧸ parabolicIdeal k d

/-- The class of the enveloping unit in the actual parabolic quotient. -/
def parabolicHighest (k : ℂ) (d : ℕ) : Parabolic k d := Submodule.Quotient.mk 1

/-- Affine action on the parabolic module induced by actual left multiplication. -/
def parabolicRho (k : ℂ) (d : ℕ) : AffSl2 →ₗ⁅ℂ⁆ End ℂ (Parabolic k d) :=
  (Algebra.lsmul ℂ ℂ (Parabolic k d)).toLieHom.comp (ι ℂ)

/-- Actual parabolic current modes. -/
def parabolicMode (k : ℂ) (d : ℕ) (a : Fin 3) (n : ℤ) : End ℂ (Parabolic k d) :=
  parabolicRho k d (modeElement a n)

@[simp] theorem parabolicRho_mk (k : ℂ) (d : ℕ) (x : AffSl2) (u : U) :
    parabolicRho k d x (Submodule.Quotient.mk u)=
      Submodule.Quotient.mk (ι ℂ x*u) := rfl

/-- The highest-weight defining ideal is contained in the parabolic ideal. -/
theorem highestIdeal_le_parabolicIdeal (k : ℂ) (d : ℕ) :
    highestIdeal k (d:ℂ) ≤ parabolicIdeal k d := le_sup_left

/-- The literal extra relation vanishes in the actual parabolic quotient. -/
theorem parabolicRelation_vanishes (k : ℂ) (d : ℕ) :
    (Submodule.Quotient.mk (parabolicRelation d) : Parabolic k d)=0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact (show Submodule.span U {parabolicRelation d} ≤ parabolicIdeal k d from
    le_sup_right) (Submodule.subset_span (Set.mem_singleton _))

end
end VOA.AffineVOA.HighestModule
