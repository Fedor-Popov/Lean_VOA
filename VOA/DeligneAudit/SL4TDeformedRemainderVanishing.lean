import VOA.DeligneAudit.SL4TDeformedRemainderLeading
import Mathlib.RingTheory.Polynomial.Basic

/-! Vanishing of remainder minors from a common polynomial divisor. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- A large common divisor forces every selected coefficient minor to vanish. -/
theorem coefficientMinor_eq_zero_of_common_divisor (r j : ℕ)
    (p : Fin j → Polynomial ℂ) (rows : Fin j → ℕ) (s : Polynomial ℂ)
    (hs : s.Monic) (hp : ∀ b, (p b).degree < (r : WithBot ℕ))
    (hdiv : ∀ b, s ∣ p b) (hr : r - s.natDegree < j) :
    Matrix.det (fun a b => (p b).coeff (rows a)) = 0 := by
  classical
  let d := r - s.natDegree
  have he (b : Fin j) : s * (p b /ₘ s) = p b := by
    have hz := (Polynomial.modByMonic_eq_zero_iff_dvd hs).mpr (hdiv b)
    simpa only [hz, zero_add] using Polynomial.modByMonic_add_div (p b) s
  have hd (b : Fin j) : (p b /ₘ s).degree < (d : WithBot ℕ) := by
    by_cases hz : p b /ₘ s = 0
    · simp [hz]
    · have hpz : p b ≠ 0 := by
        rw [← he b]
        exact mul_ne_zero hs.ne_zero hz
      have hnat : s.natDegree + (p b /ₘ s).natDegree = (p b).natDegree := by
        rw [← Polynomial.natDegree_mul hs.ne_zero hz, he b]
      have hb := hp b
      rw [Polynomial.degree_eq_natDegree hpz] at hb
      rw [Polynomial.degree_eq_natDegree hz]
      have hh : (p b).natDegree < r := by exact_mod_cast hb
      exact_mod_cast (show (p b /ₘ s).natDegree < d by dsimp [d]; omega)
  let v : Fin j → Polynomial.degreeLT ℂ d := fun b =>
    ⟨p b /ₘ s, Polynomial.mem_degreeLT.mpr (hd b)⟩
  let L : Polynomial.degreeLT ℂ d →ₗ[ℂ] (Fin j → ℂ) :=
    { toFun := fun u a => (s * u.val).coeff (rows a)
      map_add' := by intro u v; ext a; simp [mul_add]
      map_smul' := by intro c u; ext a; simp }
  apply Matrix.det_eq_zero_of_not_linearIndependent_cols
  intro hi
  have hv : LinearIndependent ℂ v := LinearIndependent.of_comp L (by
    convert hi using 1
    funext b a
    exact congrArg (fun z : Polynomial ℂ => z.coeff (rows a)) (he b))
  let e := Polynomial.degreeLTEquiv ℂ d
  letI : FiniteDimensional ℂ (Polynomial.degreeLT ℂ d) :=
    Module.Finite.of_injective e.toLinearMap e.injective
  have hcard := hv.fintype_card_le_finrank
  rw [e.finrank_eq] at hcard
  simp only [Module.finrank_pi, Fintype.card_fin] at hcard
  omega

/-- Remainders retain every common divisor of the modulus and the input polynomial. -/
theorem scalarRemainderMinor_eq_zero (P q s : Polynomial ℂ) (j : ℕ)
    (hP : P.Monic) (hs : s.Monic) (hPs : s ∣ P) (hqs : s ∣ q)
    (rows cols : Fin j → ℕ) (hj : P.natDegree - s.natDegree < j) :
    Matrix.det (fun a b => ((q * Polynomial.X ^ cols b) %ₘ P).coeff (rows a)) = 0 := by
  apply coefficientMinor_eq_zero_of_common_divisor P.natDegree j _ rows s hs
  · intro b
    simpa only [Polynomial.degree_eq_natDegree hP.ne_zero] using
      Polynomial.degree_modByMonic_lt (q * Polynomial.X ^ cols b) hP
  · intro b
    rw [Polynomial.modByMonic_eq_sub_mul_div]
    exact dvd_sub (dvd_mul_of_dvd_left hqs _) (dvd_mul_of_dvd_left hPs _)
  · exact hj

/-- A bounded scalar polynomial expands its remainder as a sum of power remainders. -/
theorem scalarRemainder_coeff (xs : List ℂ) (N c l : ℕ) (q : Polynomial ℂ)
    (hq : q.natDegree ≤ N) :
    ((q * Polynomial.X ^ c) %ₘ alphabetCharacteristic xs).coeff l =
      ∑ a : Fin (N + 1), q.coeff a.val *
        alphabetPowerRemainder xs (a.val + c) l := by
  have he := Polynomial.as_sum_range_C_mul_X_pow' q (by omega : q.natDegree < N + 1)
  conv_lhs => rw [he]
  simp only [Finset.sum_mul, mul_assoc, ← pow_add]
  change ((Polynomial.modByMonicHom (alphabetCharacteristic xs))
    (∑ a ∈ Finset.range (N + 1), Polynomial.C (q.coeff a) *
      Polynomial.X ^ (a + c))).coeff l = _
  rw [map_sum]
  simp only [Polynomial.finsetSum_coeff, ← Polynomial.smul_eq_C_mul, map_smul,
    Polynomial.coeff_smul, smul_eq_mul, Polynomial.modByMonicHom,
    LinearMap.coe_mk, AddHom.coe_mk, alphabetPowerRemainder]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

/-- Evaluation of a deformed polynomial minor is the corresponding scalar remainder minor. -/
theorem deformedRemainderMinor_evaluate {σ : Type*}
    (xs : List (MvPolynomial σ ℂ)) (N j : ℕ) (q : Polynomial ℂ)
    (hq : q.natDegree ≤ N) (rows cols : Fin j → ℕ) (z : σ → ℂ) :
    MvPolynomial.aeval z (deformedRemainderMinor xs N j q rows cols) =
      Matrix.det (fun a b => ((q * Polynomial.X ^ cols b) %ₘ
        alphabetCharacteristic (xs.map (MvPolynomial.aeval z))).coeff (rows a)) := by
  change (MvPolynomial.aeval z).toRingHom
    (deformedRemainderMinor xs N j q rows cols) = _
  rw [deformedRemainderMinor, RingHom.map_det]
  congr 1
  ext a b
  change MvPolynomial.aeval z (∑ l : Fin (N + 1),
    MvPolynomial.C (q.coeff l.val) *
      alphabetPowerRemainder xs (l.val + cols b) (rows a)) = _
  simp only [map_sum, map_mul, MvPolynomial.aeval_C]
  simp_rw [show ∀ m l, MvPolynomial.aeval z (alphabetPowerRemainder xs m l) =
      alphabetPowerRemainder (xs.map (MvPolynomial.aeval z)) m l from
    fun m l => alphabetPowerRemainder_map (MvPolynomial.aeval z).toRingHom xs m l]
  exact (scalarRemainder_coeff _ N _ _ q hq).symm

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.coefficientMinor_eq_zero_of_common_divisor
#print axioms VOA.DeligneAudit.SL4T.scalarRemainderMinor_eq_zero
#print axioms VOA.DeligneAudit.SL4T.scalarRemainder_coeff
#print axioms VOA.DeligneAudit.SL4T.deformedRemainderMinor_evaluate
