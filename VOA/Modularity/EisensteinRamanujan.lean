/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.BlockRelSpanE
import VOA.Modularity.QExpansionBridge
import VOA.Modularity.SerreDerivative

/-!
# Weighted Eisenstein coefficients and the Ramanujan boundary

An MLDE coefficient is not merely a power series: it is a modular form of a specified weight.
This file packages that distinction for the repository's analytic coefficient algebra
`E46 = ℂ[E₄,E₆]`.

`E46Weight k f` records that the element `f : E46` is represented by a genuine level-one modular
form of weight `k`.  It is closed under the coefficient algebra operations.  The predicate
`E46SerreClosed` states the one analytic primitive needed to run the usual Ramanujan induction:
the Serre derivative of a homogeneous element is again represented in `E46`, with weight raised
by two.  Mathlib's modular-form derivative file currently defines the operator but does not prove
this preservation theorem, so the predicate is deliberately exposed rather than postulated.  It is
proved downstream, in `Modularity/EisensteinSerreClosure.lean`: `VOA.e46SerreClosed`, together with
`VOA.e46HasWeightedPolynomialReps` and `VOA.e46SerreMonomialClosed`.

Nothing here identifies an Euler equation over formal power series with an MLDE.
-/

namespace VOA

open ModularForm UpperHalfPlane
open scoped MatrixGroups

/-- Extend an `E46` coefficient from the upper half-plane to the ambient complex plane using
Mathlib's canonical retraction.  Statements about it below are restricted back to `imGT 0`. -/
noncomputable def e46C (f : E46) (z : ℂ) : ℂ :=
  (f : UpperHalfPlane → ℂ) (UpperHalfPlane.ofComplex z)

@[simp] theorem e46C_of_mem (f : E46) {z : ℂ} (hz : z ∈ imGT 0) :
    e46C f z = (f : UpperHalfPlane → ℂ) ⟨z, hz⟩ := by
  rw [e46C, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

@[simp] theorem e46C_zero : e46C 0 = 0 := rfl

@[simp] theorem e46C_one : e46C 1 = 1 := rfl

@[simp] theorem e46C_add (f g : E46) : e46C (f + g) = e46C f + e46C g := rfl

@[simp] theorem e46C_sub (f g : E46) : e46C (f - g) = e46C f - e46C g := rfl

@[simp] theorem e46C_mul (f g : E46) : e46C (f * g) = e46C f * e46C g := rfl

@[simp] theorem e46C_smul (c : ℂ) (f : E46) : e46C (c • f) = c • e46C f := rfl

@[simp] theorem e46C_finset_sum {ι : Type*} (t : Finset ι) (f : ι → E46) :
    e46C (∑ i ∈ t, f i) = ∑ i ∈ t, e46C (f i) := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | @insert i t hi ih => simp [Finset.sum_insert hi, ih]

/-- A homogeneous element of `E46` of modular weight `k`.

The existential representative retains holomorphy at the cusp and not merely the slash-law, so
this is strong enough to describe genuine MLDE coefficients. -/
def E46Weight (k : ℤ) (f : E46) : Prop :=
  ∃ F : ModularForm 𝒮ℒ k, (f : UpperHalfPlane → ℂ) = F

namespace E46Weight

theorem zero (k : ℤ) : E46Weight k 0 := by
  exact ⟨0, rfl⟩

theorem one : E46Weight 0 1 := by
  exact ⟨1, rfl⟩

theorem add {k : ℤ} {f g : E46} (hf : E46Weight k f) (hg : E46Weight k g) :
    E46Weight k (f + g) := by
  obtain ⟨F, hF⟩ := hf
  obtain ⟨G, hG⟩ := hg
  refine ⟨F + G, ?_⟩
  change (f : UpperHalfPlane → ℂ) + g = F + G
  rw [hF, hG]

theorem neg {k : ℤ} {f : E46} (hf : E46Weight k f) : E46Weight k (-f) := by
  obtain ⟨F, hF⟩ := hf
  refine ⟨-F, ?_⟩
  change -(f : UpperHalfPlane → ℂ) = -(F : UpperHalfPlane → ℂ)
  rw [hF]

theorem sub {k : ℤ} {f g : E46} (hf : E46Weight k f) (hg : E46Weight k g) :
    E46Weight k (f - g) := by
  exact hf.add hg.neg

theorem smul {k : ℤ} {f : E46} (c : ℂ) (hf : E46Weight k f) : E46Weight k (c • f) := by
  obtain ⟨F, hF⟩ := hf
  refine ⟨c • F, ?_⟩
  change c • (f : UpperHalfPlane → ℂ) = c • (F : UpperHalfPlane → ℂ)
  rw [hF]

theorem mul {k l : ℤ} {f g : E46} (hf : E46Weight k f) (hg : E46Weight l g) :
    E46Weight (k + l) (f * g) := by
  obtain ⟨F, hF⟩ := hf
  obtain ⟨G, hG⟩ := hg
  refine ⟨F.mul G, ?_⟩
  change (f : UpperHalfPlane → ℂ) * g = F * G
  rw [hF, hG]

/-- A weighted `E46` coefficient is holomorphic at every point of the upper half-plane, when
read through the ambient complex-plane extension `e46C`. -/
theorem differentiableAt_e46C {k : ℤ} {f : E46} (hf : E46Weight k f)
    {z : ℂ} (hz : z ∈ imGT 0) : DifferentiableAt ℂ (e46C f) z := by
  obtain ⟨F, hF⟩ := hf
  have hfun : e46C f = (F : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex := by
    funext w
    rw [e46C, hF]
    rfl
  rw [hfun]
  exact UpperHalfPlane.mdifferentiableAt_iff.mp (F.holo' ⟨z, hz⟩)

theorem sum {ι : Type*} {k : ℤ} (t : Finset ι) (f : ι → E46)
    (hf : ∀ i ∈ t, E46Weight k (f i)) : E46Weight k (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using zero k
  | @insert i t hi ih =>
      rw [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i t)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

end E46Weight

/-- The Serre derivative obeys the graded Leibniz rule at points where both factors are
differentiable. -/
theorem serreDerivC_mul (k l : ℤ) (f g : ℂ → ℂ) {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z) :
    serreDerivC (k + l) (f * g) z =
      serreDerivC k f z * g z + f z * serreDerivC l g z := by
  rw [serreDerivC, serreDerivC, serreDerivC,
    show f * g = fun w => f w * g w from rfl, deriv_fun_mul hf hg]
  push_cast
  ring

/-- The Serre derivative is additive at points where both summands are differentiable. -/
theorem serreDerivC_add (k : ℤ) (f g : ℂ → ℂ) {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z) :
    serreDerivC k (f + g) z = serreDerivC k f z + serreDerivC k g z := by
  rw [serreDerivC, serreDerivC, serreDerivC,
    show f + g = fun w => f w + g w from rfl, deriv_fun_add hf hg]
  push_cast
  ring

/-- The Serre derivative respects a local equality of germs. -/
theorem serreDerivC_congr_of_eventuallyEq (k : ℤ) {f g : ℂ → ℂ} {z : ℂ}
    (hfg : f =ᶠ[nhds z] g) : serreDerivC k f z = serreDerivC k g z := by
  rw [serreDerivC, serreDerivC, Filter.EventuallyEq.deriv_eq hfg, hfg.self_of_nhds]

/-- The Serre derivative commutes with a finite sum of differentiable germs. -/
theorem serreDerivC_finset_sum {ι : Type*} (k : ℤ) (t : Finset ι)
    (f : ι → ℂ → ℂ) {z : ℂ} (hf : ∀ i ∈ t, DifferentiableAt ℂ (f i) z) :
    serreDerivC k (∑ i ∈ t, f i) z = ∑ i ∈ t, serreDerivC k (f i) z := by
  classical
  rw [serreDerivC,
    show (∑ i ∈ t, f i) = fun w => ∑ i ∈ t, f i w by funext w; simp,
    deriv_fun_sum hf]
  simp only [serreDerivC]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib]

/-- Mathlib's weight-two Eisenstein series, extended through `ofComplex`, is analytic at every
point of the upper half-plane. -/
theorem analyticAt_G2C {z : ℂ} (hz : z ∈ imGT 0) : AnalyticAt ℂ G2C z := by
  let q : ℂ := ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2
  have hq : q ≠ 0 := pow_ne_zero 2 (inv_ne_zero two_pi_I_ne_zero)
  have heq : G2C =ᶠ[nhds z] fun w => q⁻¹ * zhuGC 1 w := by
    filter_upwards [(isOpen_imGT 0).mem_nhds hz] with w hw
    rw [zhuGC_one hw]
    change G2C w = q⁻¹ * (q * G2C w)
    rw [← mul_assoc, inv_mul_cancel₀ hq, one_mul]
  have ha : AnalyticAt ℂ (fun w => q⁻¹ * zhuGC 1 w) z :=
    analyticAt_const.mul (analyticAt_zhuGC 1 hz)
  rw [← analyticWithinAt_univ] at ha ⊢
  exact ha.congr_of_eventuallyEq (by simpa using heq) heq.self_of_nhds

/-- The Serre derivative of a germ analytic on the upper half-plane is again analytic there. -/
theorem analyticAt_serreDerivC (k : ℤ) {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hz : z ∈ imGT 0) :
    AnalyticAt ℂ (serreDerivC k f) z := by
  change AnalyticAt ℂ (fun w =>
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv f w
      + (k : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * (G2C w * f w)) z
  exact (analyticAt_const.mul hf.deriv).add
    (analyticAt_const.mul ((analyticAt_G2C hz).mul hf))

/-- Zhu's analytic Eisenstein coefficient `G_{2j}`, for `j ≥ 2`, has its exact modular weight
`2j`. -/
theorem zhuGE_weight (j : ℕ) (hj : 2 ≤ j) : E46Weight (2 * (j : ℤ)) (zhuGE j hj) := by
  let E : ModularForm 𝒮ℒ (2 * (j : ℤ)) :=
    ModularForm.mcast (by push_cast; rfl)
      ((zhuG j 0) • ModularForm.E (show 3 ≤ 2 * j by omega))
  refine ⟨E, ?_⟩
  change (fun z : UpperHalfPlane => zhuGC j (z : ℂ)) = (E : UpperHalfPlane → ℂ)
  rw [zhuGC_fun_eq_smul_E hj]
  rw [show (E : UpperHalfPlane → ℂ) =
      (((zhuG j 0) • ModularForm.E (show 3 ≤ 2 * j by omega)) : UpperHalfPlane → ℂ) by
    simp only [E, ModularForm.coe_mcast]
    exact ModularForm.IsGLPos.coe_smul _ _]

/-- `E46` is a finite-type `ℂ`-algebra, directly from its two generators. -/
theorem finiteType_E46 : Algebra.FiniteType ℂ E46 := by
  rw [E46]
  exact Algebra.FiniteType.adjoin_of_finite (Set.toFinite _)

/-- The analytic modular coefficient ring is Noetherian. -/
theorem isNoetherianRing_E46 : IsNoetherianRing E46 :=
  haveI := finiteType_E46
  Algebra.FiniteType.isNoetherianRing ℂ E46

/-- The two distinguished generators of `E46`, retained as elements of the coefficient
algebra rather than merely as upper-half-plane functions. -/
noncomputable def e46E4 : E46 := ⟨⇑ModularForm.E₄, E4_mem_E46⟩

noncomputable def e46E6 : E46 := ⟨⇑ModularForm.E₆, E6_mem_E46⟩

theorem e46E4_weight : E46Weight 4 e46E4 := by
  exact ⟨ModularForm.E₄, rfl⟩

theorem e46E6_weight : E46Weight 6 e46E6 := by
  exact ⟨ModularForm.E₆, rfl⟩

theorem e46E4_pow_weight (a : ℕ) : E46Weight (4 * (a : ℤ)) (e46E4 ^ a) := by
  induction a with
  | zero => simpa using E46Weight.one
  | succ a ha =>
      rw [pow_succ]
      convert ha.mul e46E4_weight using 1

theorem e46E6_pow_weight (b : ℕ) : E46Weight (6 * (b : ℤ)) (e46E6 ^ b) := by
  induction b with
  | zero => simpa using E46Weight.one
  | succ b hb =>
      rw [pow_succ]
      convert hb.mul e46E6_weight using 1

/-- The `E₄^a E₆^b` monomial, with its weight visible in the type-level interface below. -/
noncomputable def e46Monomial (a b : ℕ) : E46 := e46E4 ^ a * e46E6 ^ b

theorem e46Monomial_weight (a b : ℕ) :
    E46Weight (4 * (a : ℤ) + 6 * (b : ℤ)) (e46Monomial a b) := by
  unfold e46Monomial
  convert (e46E4_pow_weight a).mul (e46E6_pow_weight b) using 1

/-- A finite homogeneous polynomial representative in the concrete generators of `E46`.

This is deliberately stronger than `E46Weight`: the latter supplies a modular-form
representative but not a weight-homogeneous polynomial representative. -/
def E46WeightedPolynomialRep (k : ℤ) (f : E46) : Prop :=
  ∃ (t : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ),
    f = ∑ ab ∈ t, c ab • e46Monomial ab.1 ab.2 ∧
      ∀ ab ∈ t, 4 * (ab.1 : ℤ) + 6 * (ab.2 : ℤ) = k

/-- The algebraic normal-form statement used to reduce Serre closure to the two Eisenstein
generators.  It is not proved in this file; it is proved downstream as
`VOA.e46HasWeightedPolynomialReps` (`Modularity/EisensteinSerreClosure.lean`), from the vendored
basis theorem `ModularForm.span_eisBasisFun` (`LatticesAndCodes/ModularForms/LevelOne`), following
`Notes/Textbook/certificates/L14_Checks.lean` (`L14Cert.e46HasWeightedPolynomialReps`). -/
def E46HasWeightedPolynomialReps : Prop :=
  ∀ (k : ℤ) (f : E46), E46Weight k f → E46WeightedPolynomialRep k f

/-- Serre closure on the homogeneous `E₄^a E₆^b` monomials.

The analytic Ramanujan identities for `E₄` and `E₆`, together with the graded Leibniz rule,
are precisely what prove this predicate.  It is proved downstream as `VOA.e46SerreMonomialClosed`
(`Modularity/EisensteinSerreClosure.lean`). -/
def E46SerreMonomialClosed : Prop :=
  ∀ (a b : ℕ), ∃ g : E46,
    E46Weight (4 * (a : ℤ) + 6 * (b : ℤ) + 2) g ∧
      ∀ z ∈ imGT 0,
        e46C g z = serreDerivC (4 * (a : ℤ) + 6 * (b : ℤ))
          (e46C (e46Monomial a b)) z

/-- Constant scalar multiplication commutes with the Serre derivative at differentiable
germs. -/
theorem serreDerivC_smul (k : ℤ) (c : ℂ) (f : ℂ → ℂ) {z : ℂ}
    (hf : DifferentiableAt ℂ f z) :
    serreDerivC k (c • f) z = c • serreDerivC k f z := by
  rw [serreDerivC, serreDerivC,
    show c • f = fun w => c * f w from rfl, deriv_const_mul c hf]
  push_cast
  ring

/-- The exact Ramanujan/Serre closure property required by the universal MLDE conversion.

The equality is required only on the upper half-plane because `e46C` is an arbitrary extension
outside it.  This is a named property, not an axiom.  It is not proved in this file, and theorems
in this file and in `Modularity/AKMLDE.lean` take it explicitly
(`e46SerreClosed_of_weightedPolynomialReps` reduces it to `E46HasWeightedPolynomialReps` and
`E46SerreMonomialClosed`).  It **is** proved downstream: `VOA.e46SerreClosed : E46SerreClosed`
(`Modularity/EisensteinSerreClosure.lean`, via the Serre derivative `serreForm` of a level-one
modular form), which discharges the hypothesis in the primed MLDE theorems there. -/
def E46SerreClosed : Prop :=
  ∀ (k : ℤ) (f : E46), E46Weight k f →
    ∃ g : E46, E46Weight (k + 2) g ∧
      ∀ z ∈ imGT 0, e46C g z = serreDerivC k (e46C f) z

/-- Homogeneous polynomial representatives and monomial Serre closure supply the full
coefficient-algebra closure property.  This reduction uses no spin-statistics or formal-series
claim: it is only the finite algebraic aggregation of the analytic monomial identities. -/
theorem e46SerreClosed_of_weightedPolynomialReps
    (hreps : E46HasWeightedPolynomialReps) (hmono : E46SerreMonomialClosed) :
    E46SerreClosed := by
  intro k f hf
  obtain ⟨t, c, hrepr, hweight⟩ := hreps k f hf
  classical
  choose d hdweight hdapply using hmono
  refine ⟨∑ ab ∈ t, c ab • d ab.1 ab.2, ?_, ?_⟩
  · apply E46Weight.sum
    intro ab hab
    apply E46Weight.smul
    have h := hdweight ab.1 ab.2
    rw [← hweight ab hab]
    convert h using 1
  · intro z hz
    have hdiff : ∀ ab ∈ t,
        DifferentiableAt ℂ (c ab • e46C (e46Monomial ab.1 ab.2)) z := by
      intro ab hab
      change DifferentiableAt ℂ (fun w => c ab * e46C (e46Monomial ab.1 ab.2) w) z
      exact ((e46Monomial_weight ab.1 ab.2).differentiableAt_e46C hz).const_mul (c ab)
    calc
      e46C (∑ ab ∈ t, c ab • d ab.1 ab.2) z
          = ∑ ab ∈ t, c ab • e46C (d ab.1 ab.2) z := by
              rw [e46C_finset_sum]
              simp only [Finset.sum_apply]
              apply Finset.sum_congr rfl
              intro ab hab
              simp only [e46C_smul, Pi.smul_apply]
      _ = ∑ ab ∈ t, c ab • serreDerivC
          (4 * (ab.1 : ℤ) + 6 * (ab.2 : ℤ))
          (e46C (e46Monomial ab.1 ab.2)) z := by
              apply Finset.sum_congr rfl
              intro ab hab
              rw [hdapply ab.1 ab.2 z hz]
      _ = ∑ ab ∈ t, serreDerivC k
          (c ab • e46C (e46Monomial ab.1 ab.2)) z := by
              apply Finset.sum_congr rfl
              intro ab hab
              rw [hweight ab hab]
              exact (serreDerivC_smul k (c ab)
                (e46C (e46Monomial ab.1 ab.2))
                ((e46Monomial_weight ab.1 ab.2).differentiableAt_e46C hz)).symm
      _ = serreDerivC k (∑ ab ∈ t,
          c ab • e46C (e46Monomial ab.1 ab.2)) z :=
            (serreDerivC_finset_sum k t _ hdiff).symm
      _ = serreDerivC k (e46C f) z := by
            rw [hrepr, e46C_finset_sum]
            simp only [e46C_smul]

/-- A chosen `E46` representative of the Serre derivative supplied by `E46SerreClosed`. -/
noncomputable def E46SerreClosed.derivCoeff (hclose : E46SerreClosed)
    (k : ℤ) (f : E46) (hf : E46Weight k f) : E46 :=
  (hclose k f hf).choose

theorem E46SerreClosed.derivCoeff_weight (hclose : E46SerreClosed)
    (k : ℤ) (f : E46) (hf : E46Weight k f) :
    E46Weight (k + 2) (hclose.derivCoeff k f hf) :=
  (hclose k f hf).choose_spec.1

theorem E46SerreClosed.derivCoeff_apply (hclose : E46SerreClosed)
    (k : ℤ) (f : E46) (hf : E46Weight k f) {z : ℂ} (hz : z ∈ imGT 0) :
    e46C (hclose.derivCoeff k f hf) z = serreDerivC k (e46C f) z :=
  (hclose k f hf).choose_spec.2 z hz

/-- Operational graded Leibniz rule: the derivative of a weighted `E46` coefficient times a
weight-`l` germ is expressed using the chosen coefficient supplied by `E46SerreClosed`. -/
theorem E46SerreClosed.serreDerivC_e46C_mul (hclose : E46SerreClosed)
    {k : ℤ} {f : E46} (hf : E46Weight k f) (l : ℤ) (g : ℂ → ℂ)
    {z : ℂ} (hz : z ∈ imGT 0) (hg : DifferentiableAt ℂ g z) :
    serreDerivC (k + l) (e46C f * g) z =
      e46C (hclose.derivCoeff k f hf) z * g z
        + e46C f z * serreDerivC l g z := by
  rw [serreDerivC_mul k l (e46C f) g (hf.differentiableAt_e46C hz) hg,
    hclose.derivCoeff_apply k f hf hz]

end VOA
