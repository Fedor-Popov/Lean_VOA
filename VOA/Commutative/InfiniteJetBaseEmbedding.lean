import VOA.Commutative.InfiniteJetArc

/-! # The zero-jet embedding and reflection of injectivity by arcs -/
namespace VOA.InfiniteJet
noncomputable section
variable {R σ : Type*} [CommRing R]

/-- The original presented algebra embeds as the order-zero functions on its arc algebra. -/
def baseToJet (I : Ideal (MvPolynomial σ R)) :
    (MvPolynomial σ R ⧸ I) →ₐ[R] PresentedJet I where
  toRingHom := PowerSeries.constantCoeff.comp (universalArc I).toRingHom
  commutes' r := by simp [PowerSeries.algebraMap_apply]

/-- The constant arc of the original presented algebra. -/
def constantArc (I : Ideal (MvPolynomial σ R)) :
    (MvPolynomial σ R ⧸ I) →ₐ[R] PowerSeries (MvPolynomial σ R ⧸ I) where
  toRingHom := PowerSeries.C
  commutes' r := by simp [PowerSeries.algebraMap_apply]

/-- Evaluation of all positive jet coordinates at zero. -/
def jetToBase (I : Ideal (MvPolynomial σ R)) :
    PresentedJet I →ₐ[R] (MvPolynomial σ R ⧸ I) := ofArc I (constantArc I)

@[simp] theorem baseToJet_mk_X (I : Ideal (MvPolynomial σ R)) (i : σ) :
    baseToJet I (Ideal.Quotient.mkₐ R I (MvPolynomial.X i)) =
      presentedJetMk I (MvPolynomial.X (i,0)) := by
  simpa [baseToJet] using coeff_universalArc_X I i 0

@[simp] theorem jetToBase_X_zero (I : Ideal (MvPolynomial σ R)) (i : σ) :
    jetToBase I (presentedJetMk I (MvPolynomial.X (i,0))) =
      Ideal.Quotient.mkₐ R I (MvPolynomial.X i) := by
  simp [jetToBase,ofArc_mk_X,constantArc]

/-- The zero-jet projection retracts the actual base-to-arc map. -/
theorem jetToBase_comp_baseToJet (I : Ideal (MvPolynomial σ R)) :
    (jetToBase I).comp (baseToJet I) = AlgHom.id R (MvPolynomial σ R ⧸ I) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change jetToBase I (baseToJet I (Ideal.Quotient.mkₐ R I (MvPolynomial.X i))) =
    Ideal.Quotient.mkₐ R I (MvPolynomial.X i)
  rw [baseToJet_mk_X,jetToBase_X_zero]

/-- Base elements cannot acquire extra relations on passing to the arc algebra. -/
theorem baseToJet_injective (I : Ideal (MvPolynomial σ R)) : Function.Injective (baseToJet I) := by
  have h : Function.LeftInverse (jetToBase I) (baseToJet I) :=
    DFunLike.congr_fun (jetToBase_comp_baseToJet I)
  exact h.injective

/-- Naturality of the zero-jet embedding under arbitrary maps of base presentations. -/
theorem baseToJet_natural {τ : Type*} (I : Ideal (MvPolynomial σ R))
    (J : Ideal (MvPolynomial τ R))
    (f : (MvPolynomial σ R ⧸ I) →ₐ[R] (MvPolynomial τ R ⧸ J)) (a : MvPolynomial σ R ⧸ I) :
    arcMap I J f (baseToJet I a) = baseToJet J (f a) := by
  have h := congrArg (PowerSeries.coeff 0) (DFunLike.congr_fun (arcMap_universal I J f) a)
  simpa [baseToJet,PowerSeries.mapAlgHom_apply] using h

/-- Injectivity of an induced arc map implies injectivity of the original algebra map. -/
theorem baseMap_injective_of_arcMap_injective {τ : Type*} (I : Ideal (MvPolynomial σ R))
    (J : Ideal (MvPolynomial τ R))
    (f : (MvPolynomial σ R ⧸ I) →ₐ[R] (MvPolynomial τ R ⧸ J))
    (hf : Function.Injective (arcMap I J f)) : Function.Injective f := by
  intro a b hab
  apply baseToJet_injective I
  apply hf
  rw [baseToJet_natural,baseToJet_natural,hab]

/-- The genuine arc functor of any algebra identified with the presented base algebra. -/
def arcEquivOfBaseAlgebraEquiv {A B : Type*} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (I : Ideal (MvPolynomial σ R))
    (e : (MvPolynomial σ R ⧸ I) ≃ₐ[R] B) :
    (PresentedJet I →ₐ[R] A) ≃ (B →ₐ[R] PowerSeries A) where
  toFun f := (toArc I f).comp e.symm.toAlgHom
  invFun u := ofArc I (u.comp e.toAlgHom)
  left_inv f := by simp [AlgHom.comp_assoc]
  right_inv u := by simp [AlgHom.comp_assoc]

/-- **Naturality in the coefficient algebra.** For `g : A → C`, the arc attached to `g ∘ f` is
the coefficientwise image under `g` of the arc attached to `f`. Together with bijectivity, this
says `PresentedJet I` represents the functor `A ↦ Hom(B, A⟦t⟧)`. -/
theorem arcEquivOfBaseAlgebraEquiv_natural {A B C : Type*} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] (I : Ideal (MvPolynomial σ R))
    (e : (MvPolynomial σ R ⧸ I) ≃ₐ[R] B) (f : PresentedJet I →ₐ[R] A) (g : A →ₐ[R] C) :
    arcEquivOfBaseAlgebraEquiv I e (g.comp f) =
      (PowerSeries.mapAlgHom g).comp (arcEquivOfBaseAlgebraEquiv I e f) := by
  change (toArc I (g.comp f)).comp e.symm.toAlgHom =
    (PowerSeries.mapAlgHom g).comp ((toArc I f).comp e.symm.toAlgHom)
  rw [toArc_natural, AlgHom.comp_assoc]

/-- The inverse direction of `arcEquivOfBaseAlgebraEquiv_natural`. -/
theorem arcEquivOfBaseAlgebraEquiv_symm_natural {A B C : Type*} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] (I : Ideal (MvPolynomial σ R))
    (e : (MvPolynomial σ R ⧸ I) ≃ₐ[R] B) (u : B →ₐ[R] PowerSeries A) (g : A →ₐ[R] C) :
    (arcEquivOfBaseAlgebraEquiv I e).symm ((PowerSeries.mapAlgHom g).comp u) =
      g.comp ((arcEquivOfBaseAlgebraEquiv I e).symm u) := by
  apply (arcEquivOfBaseAlgebraEquiv (A := C) I e).injective
  rw [Equiv.apply_symm_apply, arcEquivOfBaseAlgebraEquiv_natural, Equiv.apply_symm_apply]

end
end VOA.InfiniteJet
