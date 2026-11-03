import VOA.DeligneAudit.DeligneFusionCVRectAdjointFamily
import VOA.DeligneAudit.DeligneFusionCVRectStarEliminateVariables
import VOA.DeligneAudit.DeligneFusionCVRectStarFactor
import VOA.DeligneAudit.DeligneFusionCVRectEliminate

/-!
# Actual elimination of a phantom x-coordinate and the three-dimensional branch

For any order function, an added summand p forces the last x-variable to
vanish. Its actual quotient is covered by the smaller polynomial family.
The special adjoint primitive branch uses this map; its numerical factor
is assembled separately.
-/

namespace VOA.DeligneAudit.A2.CVRectAdjointBase

open CVRectStarBase CVRectStarIdeal CVRectStarFactor CVRectAdjointFamily
open CVRectAdjointOrder

noncomputable section

def sectionX (L N R : ℕ) : StarRing L N R →ₐ[ℂ] StarRing (L + 1) N R :=
  MvPolynomial.rename (Sum.map Fin.castSucc id)

def projectX (L N R : ℕ) : StarRing (L + 1) N R →ₐ[ℂ] StarRing L N R :=
  MvPolynomial.aeval fun x => match x with
    | Sum.inl i => Fin.lastCases 0 (fun j => MvPolynomial.X (Sum.inl j)) i
    | Sum.inr a => MvPolynomial.X (Sum.inr a)

@[simp] theorem sectionX_X (L N R : ℕ) (i : Fin L) :
    sectionX L N R (MvPolynomial.X (Sum.inl i)) = MvPolynomial.X (Sum.inl i.castSucc) := by
  simp [sectionX]

@[simp] theorem sectionX_other (L N R : ℕ) (a : Fin N ⊕ Fin R) :
    sectionX L N R (MvPolynomial.X (Sum.inr a)) = MvPolynomial.X (Sum.inr a) := by
  simp [sectionX]

@[simp] theorem projectX_X (L N R : ℕ) (i : Fin L) :
    projectX L N R (MvPolynomial.X (Sum.inl i.castSucc)) = MvPolynomial.X (Sum.inl i) := by
  simp [projectX]

@[simp] theorem projectX_other (L N R : ℕ) (a : Fin N ⊕ Fin R) :
    projectX L N R (MvPolynomial.X (Sum.inr a)) = MvPolynomial.X (Sum.inr a) := by
  simp [projectX]

@[simp] theorem projectX_last (L N R : ℕ) :
    projectX L N R (MvPolynomial.X (Sum.inl (Fin.last L))) = 0 := by simp [projectX]

theorem projectX_sectionX (L N R : ℕ) :
    (projectX L N R).comp (sectionX L N R) = AlgHom.id ℂ (StarRing L N R) := by
  ext x
  cases x <;> simp

theorem projectX_surjective (L N R : ℕ) : Function.Surjective (projectX L N R) := by
  intro p
  exact ⟨sectionX L N R p, DFunLike.congr_fun (projectX_sectionX L N R) p⟩

theorem projectX_starX (L N R : ℕ) :
    PowerSeries.map (projectX L N R).toRingHom (starX (L + 1) N R) =
      PowerSeries.X * starX L N R := by
  unfold starX
  simp only [map_sum, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X]
  rw [Fin.sum_univ_castSucc]
  simp only [show ∀ p, (projectX L N R).toRingHom p = projectX L N R p from fun _ => rfl,
    projectX_last, map_zero, zero_mul, add_zero, projectX_X,
    Fin.val_castSucc, Nat.add_sub_cancel]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show L - i.val = (L - 1 - i.val) + 1 by omega, pow_succ]
  ring

theorem projectX_starY (L N R : ℕ) :
    PowerSeries.map (projectX L N R).toRingHom (starY (L + 1) N R) = starY L N R := by
  simp [starY]

theorem projectX_starZ (L N R : ℕ) :
    PowerSeries.map (projectX L N R).toRingHom (starZ (L + 1) N R) = starZ L N R := by
  simp [starZ]

theorem coefficientIdeal_phantom {A : Type*} [CommRing A]
    (X Y Z : PowerSeries A) (μ : ℕ → ℕ → ℕ → ℕ) :
    coefficientIdeal3 (PowerSeries.X * X) Y Z (fun p q r => p + μ p q r) =
      coefficientIdeal3 X Y Z μ := by
  have hμ : (fun p q r => p + μ p q r) =
      fun p q r => μ p q r + 1 * p + 0 * q + 0 * r := by funext p q r; omega
  rw [hμ]
  simpa only [pow_one, pow_zero, one_mul] using coefficientIdeal3_factor X Y Z μ 1 0 0

theorem projectX_ideal (L N R : ℕ) (μ : ℕ → ℕ → ℕ → ℕ) :
    Ideal.map (projectX L N R).toRingHom
        (ideal (L + 1) N R (fun p q r => p + μ p q r)) = ideal L N R μ := by
  unfold ideal
  rw [coefficientIdeal3_map, projectX_starX, projectX_starY, projectX_starZ,
    coefficientIdeal_phantom]

theorem last_x_mem (L N R : ℕ) (μ : ℕ → ℕ → ℕ → ℕ) :
    MvPolynomial.X (Sum.inl (Fin.last L)) ∈
      ideal (L + 1) N R (fun p q r => p + μ p q r) := by
  have h : PowerSeries.coeff 0
      (starX (L + 1) N R ^ 1 * starY (L + 1) N R ^ 0 * starZ (L + 1) N R ^ 0) ∈
      ideal (L + 1) N R (fun p q r => p + μ p q r) :=
    Ideal.subset_span ⟨1, 0, 0, 0, by dsimp; omega, rfl⟩
  simpa only [pow_one, pow_zero, mul_one, CVRectStarEliminate.coeff_zero_starX] using h

theorem sectionX_project_quotient (L N R : ℕ) (J : Ideal (StarRing (L + 1) N R))
    (hx : MvPolynomial.X (Sum.inl (Fin.last L)) ∈ J) :
    ((Ideal.Quotient.mkₐ ℂ J).comp (sectionX L N R)).comp (projectX L N R) =
      Ideal.Quotient.mkₐ ℂ J := by
  ext x
  cases x with
  | inl i =>
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa only [AlgHom.comp_apply, projectX_last, map_zero, Ideal.Quotient.mkₐ_eq_mk] using
          (Ideal.Quotient.eq_zero_iff_mem.mpr hx).symm
      · simp
  | inr a => simp

/-- Actual smaller-to-phantom quotient map for an arbitrary order function. -/
def phantomModelMap (L N R : ℕ) (μ : ℕ → ℕ → ℕ → ℕ) :
    Model L N R μ →ₐ[ℂ] Model (L + 1) N R (fun p q r => p + μ p q r) :=
  CVRectEliminate.quotientSectionMap (sectionX L N R) (projectX L N R) _ _
    (projectX_surjective L N R) (projectX_ideal L N R μ)
    (sectionX_project_quotient L N R _ (last_x_mem L N R μ))

theorem phantomModelMap_surjective (L N R : ℕ) (μ : ℕ → ℕ → ℕ → ℕ) :
    Function.Surjective (phantomModelMap L N R μ) :=
  CVRectEliminate.quotientSectionMap_surjective _ _ _ _ _ _ _

/-- The actual phantom-variable quotient has no greater finite rank. -/
theorem phantom_model_bound (L N R : ℕ) (μ : ℕ → ℕ → ℕ → ℕ)
    [FiniteDimensional ℂ (Model L N R μ)] :
    FiniteDimensional ℂ (Model (L + 1) N R (fun p q r => p + μ p q r)) ∧
      Module.finrank ℂ (Model (L + 1) N R (fun p q r => p + μ p q r)) ≤
        Module.finrank ℂ (Model L N R μ) := by
  have hs := phantomModelMap_surjective L N R μ
  let f := (phantomModelMap L N R μ).toLinearMap
  have hf : Function.Surjective f := hs
  exact ⟨Module.Finite.of_surjective f hf,
    LinearMap.finrank_le_finrank_of_surjective (f := f) hf⟩

end

end VOA.DeligneAudit.A2.CVRectAdjointBase

#print axioms VOA.DeligneAudit.A2.CVRectAdjointBase.phantomModelMap_surjective
#print axioms VOA.DeligneAudit.A2.CVRectAdjointBase.phantom_model_bound
