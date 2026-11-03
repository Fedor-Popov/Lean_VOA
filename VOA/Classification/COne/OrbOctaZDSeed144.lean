import VOA.Classification.COne.OrbOctaZDGrade144

/-! The binary invariant relation closes the weight-144 Zhu seed. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZD
open VOA OrbSpan OrbPrim OrbRat6 OrbOcta OrbC2b OrbOctaZC OrbOctaR MvPolynomial

noncomputable local instance : Fintype octa :=
  @Fintype.ofFinite _ (Finite.of_equiv (Equiv.Perm (Fin 4)) octa_group.some.symm.toEquiv)

theorem psi_I3sq : psi (I3 * I3) =
    (-4 : ℂ) • (X 0 ^ 10 * X 1 ^ 2) + (8 : ℂ) • (X 0 ^ 6 * X 1 ^ 6) +
      (-4 : ℂ) • (X 0 ^ 2 * X 1 ^ 10) := by
  rw [map_mul, psi_I3]
  have he : MvPolynomial.C Complex.I * MvPolynomial.C (-2 * eps1) *
      (MvPolynomial.C Complex.I * MvPolynomial.C (-2 * eps1) : P2) = -4 := by
    calc
      _ = (MvPolynomial.C Complex.I : P2) ^ 2 *
          MvPolynomial.C (-2 * eps1) ^ 2 := by ring
      _ = -4 := by rw [C_I_pow_two, C_eps_pow_two]; ring
  simp only [smul_eq_C_mul, map_neg, map_ofNat]
  linear_combination (X 0 ^ 5 * X 1 - X 0 * X 1 ^ 5) ^ 2 * he

/-- The relation is exact after the binary map, so no extra descendant is introduced. -/
theorem psi_I6sq : psi (I6 * I6) =
    (1 / 2 : ℂ) • psi (I4 * (I4 * I4)) -
      (27 : ℂ) • psi ((I3 * I3) * (I3 * I3)) := by
  have h : (2 : ℂ) • psi (I6 * I6) = psi (I4 * (I4 * I4)) -
      (54 : ℂ) • psi ((I3 * I3) * (I3 * I3)) := by
    rw [map_mul, map_mul, map_mul, map_mul, psi_I3sq, psi_I4, psi_I6]
    simp only [smul_eq_C_mul, map_neg, map_ofNat]
    ring
  have he := congrArg (fun P : P2 => (1 / 2 : ℂ) • P) h
  simpa only [smul_smul, smul_sub, show (1 / 2 : ℂ) * 2 = 1 by norm_num,
    show (1 / 2 : ℂ) * 54 = 27 by norm_num, one_smul] using he

theorem Tav_I6sq : Tav (I6 * I6) =
    (1 / 2 : ℂ) • Tav (I4 * (I4 * I4)) -
      (27 : ℂ) • Tav ((I3 * I3) * (I3 * I3)) := by
  have h := congrArg (fun P => OrbC2.average octa (Tb P)) psi_I6sq
  simpa only [map_sub, map_smul] using h

/-- Q24 annihilates the weight-144 seed. -/
theorem q24_seed_four :
    Polynomial.aeval (OrbZhu.omegaL W) OrbOctaZ.positivePolynomial (mk W (octaSeeds 4)) = 0 := by
  change q24L (mk W (Tav (I6 * I6))) = 0
  rw [Tav_I6sq, map_sub, map_smul, map_smul, map_sub, map_smul, map_smul,
    q24_I4cube, q24_I3four, smul_zero, smul_zero, sub_self]

end VOA.Classification.COne.OrbOctaZD
