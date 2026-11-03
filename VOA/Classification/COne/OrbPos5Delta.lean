import VOA.Classification.COne.OrbPos4Charges

/-!
# Finite Li substitution on the actual lattice oscillator space

The sign is that of `OrbPos4`: the momentum is `k+j/2-a/(2n)`.
This file constructs the oscillator part on every polynomial, not just on
the conformal vector. The charge-dependent fractional power is inserted in
`OrbPos5Fields`. No twisted-module identity is assumed here.
-/

namespace VOA.Classification.COne.OrbPos5
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet VOA.HeisenbergN
open OrbPos2 OrbPos3 OrbPos4 LatMod

noncomputable abbrev Osc := FockN (rank (latP 1))

/-- Orthonormal coordinate of the root of squared norm two. -/
noncomputable def rootCoord : ℂ := chargeCoord (latP 1) (1 : ℤ) (a0 1)

theorem rootCoord_sq : rootCoord ^ 2 = 2 := by
  have h := sum_chargeCoord (latP 1) (latP_posDef 1 le_rfl) (1 : ℤ) (1 : ℤ)
  rw [sum_rankOne, latP_form] at h
  simpa [rootCoord, pow_two] using h

/-- Li's finite oscillator substitution, with `w=z⁻¹`.
The orthonormal oscillator `X_(i,b)` changes by
`-t <α,b> (-1)^i w^(i+1)`. In rank one `b` is unique. -/
noncomputable def delta (t : ℂ) : Osc →ₐ[ℂ] Polynomial Osc :=
  MvPolynomial.aeval fun ib : ℕ × Fin (rank (latP 1)) =>
    Polynomial.C (MvPolynomial.X ib) +
      Polynomial.C (MvPolynomial.C (-t * rootCoord * (-1) ^ ib.1)) *
        Polynomial.X ^ (ib.1 + 1)

@[simp] theorem delta_X (t : ℂ) (ib : ℕ × Fin (rank (latP 1))) :
    delta t (MvPolynomial.X ib) = Polynomial.C (MvPolynomial.X ib) +
      Polynomial.C (MvPolynomial.C (-t * rootCoord * (-1) ^ ib.1)) *
        Polynomial.X ^ (ib.1 + 1) := by
  simp [delta]

/-- Polynomial coefficients of the substitution as a finitely supported linear map. -/
noncomputable def deltaCoeffs (t : ℂ) : Osc →ₗ[ℂ] (ℕ →₀ Osc) :=
  ((Polynomial.toFinsuppIsoLinear Osc).restrictScalars ℂ).toLinearMap.comp
    (delta t).toLinearMap

@[simp] theorem deltaCoeffs_one (t : ℂ) :
    deltaCoeffs t 1 = Finsupp.single 0 1 := by
  change (delta t 1).toFinsupp = _
  rw [map_one]
  rfl

theorem delta_zero (p : Osc) : delta 0 p = Polynomial.C p := by
  have h : delta 0 = Polynomial.CAlgHom (R := ℂ) (A := Osc) := by
    apply MvPolynomial.algHom_ext
    intro ib
    simp
  exact congrArg (fun f : Osc →ₐ[ℂ] Polynomial Osc => f p) h

theorem deltaCoeffs_zero (p : Osc) : deltaCoeffs 0 p = Finsupp.single 0 p := by
  change (delta 0 p).toFinsupp = _
  rw [delta_zero]
  rfl

/-- The polynomial-valued substitution extends over coefficients while fixing `w`. -/
noncomputable def deltaExtend (t : ℂ) : Polynomial Osc →ₐ[ℂ] Polynomial Osc :=
  Polynomial.eval₂AlgHom (delta t) Polynomial.X (fun _ => Commute.all _ _)

@[simp] theorem deltaExtend_C (t : ℂ) (p : Osc) :
    deltaExtend t (Polynomial.C p) = delta t p := by
  simp [deltaExtend]

@[simp] theorem deltaExtend_X (t : ℂ) : deltaExtend t Polynomial.X = Polynomial.X := by
  simp [deltaExtend]

/-- Group law on the entire oscillator polynomial algebra. -/
theorem delta_comp (s t : ℂ) : (deltaExtend s).comp (delta t) = delta (s + t) := by
  apply MvPolynomial.algHom_ext
  intro ib
  simp only [AlgHom.comp_apply, delta_X, map_add, map_mul, map_pow,
    deltaExtend_C, deltaExtend_X]
  simp only [delta, MvPolynomial.aeval_C]
  simp only [Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq,
    neg_add, map_add]
  ring

/-- The substitution has an explicit inverse on every oscillator state. -/
theorem delta_inverse (t : ℂ) (p : Osc) :
    deltaExtend (-t) (delta t p) = Polynomial.C p := by
  have h := congrArg (fun f : Osc →ₐ[ℂ] Polynomial Osc => f p) (delta_comp (-t) t)
  simpa only [AlgHom.comp_apply, neg_add_cancel, delta_zero] using h

theorem omega_osc :
    ωN (rank (latP 1)) 1 = (1/2 : ℂ) •
      (MvPolynomial.X (0, a0 1) : Osc)^2 := by
  haveI : Subsingleton (Fin (rank (latP 1))) := by rw [rank_latP]; infer_instance
  letI : Unique (Fin (rank (latP 1))) := ⟨⟨a0 1⟩, fun _ => Subsingleton.elim _ _⟩
  rw [ωN, Fintype.sum_unique, ωNa, oscN_neg_one_sq_vacuumN]
  norm_num
  rfl

/-- All coefficients of Δ on the actual rank-one Sugawara state. -/
theorem delta_omega (t : ℂ) :
    delta t (ωN (rank (latP 1)) 1) =
      Polynomial.monomial 0 (ωN (rank (latP 1)) 1) +
      Polynomial.monomial 1 ((-t * rootCoord) • (MvPolynomial.X (0, a0 1) : Osc)) +
      Polynomial.monomial 2 (t^2 • (1 : Osc)) := by
  rw [omega_osc, map_smul, map_pow, delta_X]
  simp only [pow_zero, mul_one, zero_add, pow_one, ← Polynomial.C_mul_X_pow_eq_monomial,
    map_pow, Algebra.smul_def, Polynomial.algebraMap_apply,
    MvPolynomial.algebraMap_eq, map_mul, map_neg]
  have hc : (Polynomial.C (MvPolynomial.C rootCoord) : Polynomial Osc)^2 = 2 := by
    rw [← map_pow, ← map_pow, rootCoord_sq]
    simp only [map_ofNat]
  have hh : (Polynomial.C (MvPolynomial.C (1/2 : ℂ)) : Polynomial Osc) * 2 = 1 := by
    calc
      _ = Polynomial.C (MvPolynomial.C ((1/2 : ℂ)*2)) := by
        simp only [map_mul, map_ofNat]
      _ = 1 := by norm_num
  linear_combination
    Polynomial.C (MvPolynomial.C (1/2 : ℂ)) *
      (Polynomial.C (MvPolynomial.C t))^2 * Polynomial.X^2 * hc -
    ((Polynomial.C (MvPolynomial.X (0, a0 1))) * Polynomial.C (MvPolynomial.C t) *
      Polynomial.C (MvPolynomial.C rootCoord) * Polynomial.X -
      (Polynomial.C (MvPolynomial.C t))^2 * Polynomial.X^2) * hh

theorem deltaCoeffs_omega (t : ℂ) :
    deltaCoeffs t (ωN (rank (latP 1)) 1) =
      Finsupp.single 0 (ωN (rank (latP 1)) 1) +
      Finsupp.single 1 ((-t * rootCoord) • (MvPolynomial.X (0, a0 1) : Osc)) +
      Finsupp.single 2 (t^2 • (1 : Osc)) := by
  change (delta t _).toFinsupp = _
  rw [delta_omega, Polynomial.toFinsupp_add, Polynomial.toFinsupp_add]
  rfl

end VOA.Classification.COne.OrbPos5
