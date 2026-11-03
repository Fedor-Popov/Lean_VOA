import VOA.Huang.GenusTwoPointElliptic
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-!
# Lattice Laurent coefficients in the q-coordinate

The regular part of the actual lattice Weierstrass function has even Taylor
coefficients given by the Eisenstein q-functions constructed earlier in the library.
This identifies the lattice side of the desired Fourier comparison. It does
not yet identify `wpTwoQ` with the lattice function away from its poles.
-/
namespace VOA.Huang.GenusTwoPoint.QEquation
open VOA Complex
open scoped BigOperators

/-- The period lattice is Z tau + Z, in the order used by `eisSummand`. -/
noncomputable def torusPeriods (τ : UpperHalfPlane) : PeriodPair where
  ω₁ := τ
  ω₂ := 1
  indep := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.one_im, Complex.one_re, Complex.zero_im, mul_zero] at hi
    have ha : a = 0 := (mul_eq_zero.mp hi).resolve_right (ne_of_gt τ.im_pos)
    subst a
    simpa using h

/-- Reindexing the lattice sum by its integer basis. Reindexing total sums
does not itself assert convergence at the small exponents. -/
theorem torus_sumInvPow (τ : UpperHalfPlane) (r : ℕ) :
    (torusPeriods τ).sumInvPow 0 r =
      ∑' v : Fin 2 → ℤ, EisensteinSeries.eisSummand (r : ℤ) v τ := by
  let L := torusPeriods τ
  let e : L.lattice ≃ (Fin 2 → ℤ) :=
    L.latticeEquivProd.toEquiv.trans (LinearEquiv.finTwoArrow ℤ ℤ).toEquiv.symm
  rw [PeriodPair.sumInvPow, ← e.symm.tsum_eq]
  apply tsum_congr
  intro v
  have he : ((e.symm v : L.lattice) : ℂ) = (v 0 : ℂ) * τ + v 1 := by
    change ((L.latticeEquivProd.symm (v 0, v 1) : L.lattice) : ℂ) = _
    rw [L.latticeEquiv_symm_apply]
    simp [L, torusPeriods]
  simp only [he, sub_zero, EisensteinSeries.eisSummand, zpow_neg, zpow_natCast]

/-- Every even lattice coefficient of weight at least four is the actual
Eisenstein q-series with Huang's normalization. -/
theorem torus_sumInvPow_even (τ : UpperHalfPlane) {j : ℕ} (hj : 2 ≤ j) :
    (torusPeriods τ).sumInvPow 0 (2 * j) = huangEisensteinQ j (qParam τ) := by
  rw [torus_sumInvPow, huangEisensteinQ_eq_lattice hj]

/-- Odd lattice sums vanish by the lattice involution, with no convergence
assumption needed for this identity of total sums. -/
theorem sumInvPow_odd (L : PeriodPair) (j : ℕ) : L.sumInvPow 0 (2 * j + 1) = 0 := by
  have hneg : L.sumInvPow 0 (2 * j + 1) = -L.sumInvPow 0 (2 * j + 1) := by
    unfold PeriodPair.sumInvPow
    conv_lhs => rw [← (Equiv.neg L.lattice).tsum_eq]
    rw [← tsum_neg]
    apply tsum_congr
    intro l
    simp [pow_succ, pow_mul]
  linear_combination (1 / 2 : ℂ) * hneg

/-- The lattice-defined regular part has precisely the expected positive even
Laurent coefficients, identified with analytic functions of q. -/
theorem torus_weierstrass_even_derivative (τ : UpperHalfPlane) {j : ℕ} (hj : 1 ≤ j) :
    iteratedDeriv (2 * j) ((torusPeriods τ).weierstrassPExcept 0) 0 =
      ((2 * j + 1).factorial : ℂ) * huangEisensteinQ (j + 1) (qParam τ) := by
  rw [PeriodPair.iteratedDeriv_weierstrassPExcept_self, if_neg (by omega)]
  rw [show 2 * j + 2 = 2 * (j + 1) by omega, torus_sumInvPow_even τ (by omega)]

theorem torus_weierstrass_odd_derivative (τ : UpperHalfPlane) (j : ℕ) :
    iteratedDeriv (2 * j + 1) ((torusPeriods τ).weierstrassPExcept 0) 0 = 0 := by
  rw [PeriodPair.iteratedDeriv_weierstrassPExcept_self, if_neg (by omega)]
  rw [show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by omega, sumInvPow_odd, mul_zero]

/-- Coefficients of the regular part of wp₂ at the insertion diagonal. -/
noncomputable def ellipticLaurentCoeff (τ : UpperHalfPlane) (n : ℕ) : ℂ :=
  if n = 0 then 0 else if Even n then
    (n + 1) * huangEisensteinQ (n / 2 + 1) (qParam τ) else 0

theorem ellipticLaurentCoeff_eq (τ : UpperHalfPlane) (n : ℕ) :
    ellipticLaurentCoeff τ n =
      if n = 0 then (torusPeriods τ).weierstrassPExcept 0 0 else
        (n + 1) * (torusPeriods τ).sumInvPow 0 (n + 2) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [ellipticLaurentCoeff, PeriodPair.weierstrassPExcept]
  · rw [ellipticLaurentCoeff, if_neg hn, if_neg hn]
    rcases Nat.even_or_odd n with he | ho
    · rw [if_pos he]
      obtain ⟨j, hj⟩ := he
      have hnj : n = 2 * j := by omega
      rw [hnj] at hn ⊢
      rw [show 2 * j + 2 = 2 * (j + 1) by omega,
        torus_sumInvPow_even τ (by omega)]
      congr 2
      omega
    · have hne : ¬ Even n := by
        rintro ⟨k, hk⟩
        obtain ⟨j, hj⟩ := ho
        omega
      rw [if_neg hne]
      obtain ⟨j, hj⟩ := ho
      rw [show n + 2 = 2 * (j + 1) + 1 by omega, sumInvPow_odd, mul_zero]

/-- A convergent lattice Laurent expansion, whose coefficients are already
identified with the cusp-analytic Eisenstein q-functions. -/
theorem torus_weierstrass_hasFPowerSeriesAt (τ : UpperHalfPlane) :
    HasFPowerSeriesAt ((torusPeriods τ).weierstrassPExcept 0)
      (FormalMultilinearSeries.ofScalars ℂ (ellipticLaurentCoeff τ)) 0 := by
  have hc := funext (ellipticLaurentCoeff_eq τ)
  rw [hc]
  exact (torusPeriods τ).hasFPowerSeriesAt_weierstrassPExcept 0

/-- The proposed removable extension of the Fourier formula at the insertion
diagonal. The extension's analyticity still has to be established. -/
noncomputable def fourierRegularPart (τ : UpperHalfPlane) (z : ℂ) : ℂ :=
  if z = 0 then 0 else
    wpTwoQ (Complex.exp (2 * (Real.pi : ℂ) * I * z)) (qParam τ) - 1 / z ^ 2

/-- The remaining local Fourier calculation, with every normalization fixed.
This is a target predicate, not a hypothesis silently discharged by analyticity. -/
def FourierLaurentExpansion (τ : UpperHalfPlane) : Prop :=
  HasFPowerSeriesAt (fourierRegularPart τ)
    (FormalMultilinearSeries.ofScalars ℂ (ellipticLaurentCoeff τ)) 0

/-- The local Fourier calculation implies equality with the actual lattice
function on a punctured neighborhood. No global total-function equality is inferred. -/
theorem fourier_eq_lattice_germ (τ : UpperHalfPlane) (h : FourierLaurentExpansion τ) :
    ∀ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ,
      wpTwoQ (Complex.exp (2 * (Real.pi : ℂ) * I * z)) (qParam τ) =
        (torusPeriods τ).weierstrassP z := by
  have he : ∀ᶠ z in nhds (0 : ℂ),
      fourierRegularPart τ z = (torusPeriods τ).weierstrassPExcept 0 z := by
    filter_upwards [h.eventually_hasSum_sub,
      (torus_weierstrass_hasFPowerSeriesAt τ).eventually_hasSum_sub] with z hz hL
    exact hz.unique hL
  filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hz0
  have hn : z ≠ 0 := by simpa using hz0
  rw [fourierRegularPart, if_neg hn] at hz
  have hL := (torusPeriods τ).weierstrassPExcept_add 0 z
  simp only [Submodule.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, div_zero] at hL
  linear_combination hz + hL

end VOA.Huang.GenusTwoPoint.QEquation
