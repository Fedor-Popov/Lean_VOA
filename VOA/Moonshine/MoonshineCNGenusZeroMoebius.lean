/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGenusZeroOverlap
import VOA.Moonshine.MoonshineCNGenusZeroExtension
import VOA.Moonshine.MoonshineCNGenusZeroClassification

/-!
# Genus zero on the abstract interface: local symmetries are real Möbius maps

Blueprint: `Notes/moonshine/MOON_M8_LEAN.md`; this file assembles the whole route. Let `F` be a
replicable family of period `N > 0` satisfying the prime Hecke identity, `f = qSeriesFun (F.c k)`,
and `α` holomorphic on a disc `D(z₀, η)` with closure in `ℍ`, `Im α ≥ m > 0`, `f ∘ α = f` and
`α′(z₀) ≠ 0`. Then on `D(z₀, η/2)` the map `α` is a real Möbius transformation
`z ↦ (p z + q)/(r z + s)`, `p s − q r = 1`, whose matrix lies in `symmetryGroup f`
(`isMoebiusSymmetryOn_of_localSymmetry`).

Route: real affine `α` extends by the identity theorem; otherwise the overlap construction
gives an intertwining sequence, hence a real linear ODE and an explicit family; the explicit
function maps `ℍ` into `ℍ` and intertwines `f` globally (boundary-real exclusion and global
extension, `forall_im_pos_and_eq_of_local`), and the classification of the families leaves only
`z ↦ z + n`, `z ↦ a (z − c) + M₀` (`a > 0`) and `z ↦ M₀ + K/(z − c)` (`K < 0`).
-/

namespace VOA.Moonshine.ConwayNorton

open UpperHalfPlane Filter Topology Set
open scoped Real

/-! ### Real Möbius maps in the symmetry group -/

lemma coe_glOfDetOne_smul {p q r s : ℝ} (h : p * s - q * r = 1) (τ : ℍ) :
    ((glOfDetOne p q r s h • τ : ℍ) : ℂ) = (p * τ + q) / (r * τ + s) := by
  rw [coe_smul_of_det_pos (by rw [glOfDetOne_det]; exact one_pos)]
  simp [num, denom]

/-- A real Möbius map of determinant one intertwining `f` on `ℍ` lies in `symmetryGroup f`. -/
lemma glOfDetOne_mem_symmetryGroup_of {c : ℕ → ℂ} {p q r s : ℝ} (h : p * s - q * r = 1)
    (hrel : ∀ τ : ℍ, qSeriesExt c ((p * τ + q) / (r * τ + s)) = qSeriesExt c τ) :
    glOfDetOne p q r s h ∈ symmetryGroup (qSeriesFun c) := by
  refine ⟨Units.val_eq_one.mp (glOfDetOne_det _ _ _ _ _), fun τ => ?_⟩
  rw [← qSeriesExt_coe, coe_glOfDetOne_smul, hrel, qSeriesExt_coe]

/-- `α` agrees on `S` with a real Möbius map of determinant one lying in `symmetryGroup f`. -/
def IsMoebiusSymmetryOn (f : ℍ → ℂ) (α : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∃ (p q r s : ℝ) (h : p * s - q * r = 1), glOfDetOne p q r s h ∈ symmetryGroup f ∧
    ∀ z ∈ S, α z = (p * z + q) / (r * z + s)

/-- A real affine global symmetry `z ↦ a z + b` (`a > 0`). -/
lemma isMoebiusSymmetryOn_of_affine {c : ℕ → ℂ} {α : ℂ → ℂ} {S : Set ℂ} {a b : ℝ} (ha : 0 < a)
    (hS : ∀ z ∈ S, α z = a * z + b)
    (hglob : ∀ z : ℂ, 0 < z.im → qSeriesExt c ((a : ℂ) * z + b) = qSeriesExt c z) :
    IsMoebiusSymmetryOn (qSeriesFun c) α S := by
  set t := Real.sqrt a with ht
  have ht0 : 0 < t := Real.sqrt_pos.mpr ha
  have htt : t * t = a := Real.mul_self_sqrt ha.le
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
  have hdet : t * t⁻¹ - b / t * 0 = 1 := by
    rw [mul_zero, sub_zero, mul_inv_cancel₀ ht0.ne']
  have hform : ∀ z : ℂ, ((t : ℂ) * z + ((b / t : ℝ) : ℂ)) / (((0 : ℝ) : ℂ) * z + ((t⁻¹ : ℝ) : ℂ)) =
      (a : ℂ) * z + b := by
    intro z
    have hac : (a : ℂ) = (t : ℂ) * t := by rw [← Complex.ofReal_mul, htt]
    rw [hac]
    push_cast
    field_simp
    ring
  refine ⟨t, b / t, 0, t⁻¹, hdet, glOfDetOne_mem_symmetryGroup_of hdet fun τ => ?_,
    fun z hz => ?_⟩
  · rw [hform]
    exact hglob τ τ.im_pos
  · rw [hform, hS z hz]

/-- A real global symmetry `z ↦ M₀ + K/(z − c₀)` with `K < 0`. -/
lemma isMoebiusSymmetryOn_of_inv {c : ℕ → ℂ} {α : ℂ → ℂ} {S : Set ℂ} {K c₀ M₀ : ℝ} (hK : K < 0)
    (hSU : ∀ z ∈ S, 0 < z.im) (hS : ∀ z ∈ S, α z = K * (z - c₀)⁻¹ + M₀)
    (hglob : ∀ z : ℂ, 0 < z.im → qSeriesExt c ((K : ℂ) * (z - c₀)⁻¹ + M₀) = qSeriesExt c z) :
    IsMoebiusSymmetryOn (qSeriesFun c) α S := by
  set t := Real.sqrt (-K) with ht
  have ht0 : 0 < t := Real.sqrt_pos.mpr (by linarith)
  have htt : t * t = -K := Real.mul_self_sqrt (by linarith)
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
  have hdet : M₀ / t * (-c₀ / t) - (K - M₀ * c₀) / t * (1 / t) = 1 := by
    field_simp
    nlinarith
  have hform : ∀ z : ℂ, 0 < z.im →
      (((M₀ / t : ℝ) : ℂ) * z + (((K - M₀ * c₀) / t : ℝ) : ℂ)) /
        (((1 / t : ℝ) : ℂ) * z + ((-c₀ / t : ℝ) : ℂ)) = (K : ℂ) * (z - c₀)⁻¹ + M₀ := by
    intro z hz
    have hzc : z - (c₀ : ℂ) ≠ 0 := sub_ofReal_ne_zero hz c₀
    have hnum : ((M₀ / t : ℝ) : ℂ) * z + (((K - M₀ * c₀) / t : ℝ) : ℂ) =
        ((M₀ : ℂ) * z + K - M₀ * c₀) / t := by
      push_cast
      ring
    have hden : ((1 / t : ℝ) : ℂ) * z + ((-c₀ / t : ℝ) : ℂ) = (z - c₀) / t := by
      push_cast
      ring
    rw [hnum, hden]
    field_simp
    ring
  refine ⟨M₀ / t, (K - M₀ * c₀) / t, 1 / t, -c₀ / t, hdet,
    glOfDetOne_mem_symmetryGroup_of hdet fun τ => ?_, fun z hz => ?_⟩
  · rw [hform τ τ.im_pos]
    exact hglob τ τ.im_pos
  · rw [hform z (hSU z hz), hS z hz]

/-! ### Derivatives of the explicit families -/

lemma deriv_eq_of_eqOn_nhds {α β : ℂ → ℂ} {S : Set ℂ} (hSo : IsOpen S) {z₀ : ℂ} (hz₀ : z₀ ∈ S)
    (h : ∀ z ∈ S, α z = β z) : _root_.deriv α z₀ = _root_.deriv β z₀ :=
  Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (hSo.mem_nhds hz₀) h)

/-! ### Local symmetries are real Möbius maps -/

/-- **Local symmetries are real Möbius maps**. -/
theorem isMoebiusSymmetryOn_of_localSymmetry {N : ℕ} (hN : 0 < N) (F : ReplicableFamily N)
    (k : ℕ) (hB1 : PrimeHeckeIdentity F k) {z₀ : ℂ} {η : ℝ} (hη : 0 < η) (hηz : η < z₀.im)
    {α : ℂ → ℂ} (hα : DifferentiableOn ℂ α (Metric.ball z₀ η)) {m : ℝ} (hm : 0 < m)
    (hαm : ∀ z ∈ Metric.ball z₀ η, m ≤ (α z).im)
    (hαf : ∀ z ∈ Metric.ball z₀ η, qSeriesExt (F.c k) (α z) = qSeriesExt (F.c k) z)
    (hd : _root_.deriv α z₀ ≠ 0) :
    IsMoebiusSymmetryOn (qSeriesFun (F.c k)) α (Metric.ball z₀ (η / 2)) := by
  have hc := F.isJDominated k
  set S := Metric.ball z₀ (η / 2) with hSdef
  have hSB : S ⊆ Metric.ball z₀ η := Metric.ball_subset_ball (by linarith)
  have hSo : IsOpen S := Metric.isOpen_ball
  have hSc : IsPreconnected S := (convex_ball _ _).isPreconnected
  have hz₀S : z₀ ∈ S := Metric.mem_ball_self (half_pos hη)
  have hSU : ∀ z ∈ S, 0 < z.im := fun z hz => im_pos_of_mem_ball (by linarith) hz
  have hz₀U : 0 < z₀.im := hη.trans hηz
  have hUc : IsPreconnected upperHalfPlaneSet := (convex_halfSpace_im_gt 0).isPreconnected
  have hgA : AnalyticOnNhd ℂ (qSeriesExt (F.c k)) upperHalfPlaneSet :=
    (differentiableOn_qSeriesExt hc).analyticOnNhd isOpen_upperHalfPlaneSet
  by_cases haff : ∃ a b : ℝ, 0 < a ∧ ∀ z ∈ Metric.ball z₀ η, α z = affC a b z
  · -- a real affine local symmetry extends by the identity theorem
    obtain ⟨a, b, ha, hab⟩ := haff
    have hglob : ∀ z : ℂ, 0 < z.im →
        qSeriesExt (F.c k) ((a : ℂ) * z + b) = qSeriesExt (F.c k) z := by
      have hA1 : AnalyticOnNhd ℂ (qSeriesExt (F.c k) ∘ affC a b) upperHalfPlaneSet :=
        ((differentiableOn_qSeriesExt hc).comp (differentiable_affC a b).differentiableOn
          fun z hz => affC_im_pos ha b hz).analyticOnNhd isOpen_upperHalfPlaneSet
      have hev : (qSeriesExt (F.c k) ∘ affC a b) =ᶠ[𝓝 z₀] qSeriesExt (F.c k) :=
        Filter.eventually_of_mem (Metric.ball_mem_nhds z₀ hη) fun z hz => by
          simp only [Function.comp_apply]
          rw [← hab z hz]
          exact hαf z hz
      intro z hz
      exact hA1.eqOn_of_preconnected_of_eventuallyEq hgA hUc hz₀U hev hz
    exact isMoebiusSymmetryOn_of_affine ha (fun z hz => hab z (hSB hz)) hglob
  · -- intertwining sequence, real ODE, explicit family
    obtain ⟨a, b, a', b', -, hane, -, ha, hb, hint⟩ :=
      exists_intertwining_of_not_realAffine hN F k hB1 hη hηz hα hm hαm hαf haff
    have hnc : ∃ z₁ ∈ S, α z₁ ≠ α z₀ := by
      by_contra hcon
      apply hd
      have hconst : ∀ z ∈ S, α z = (fun _ : ℂ => α z₀) z := fun z hz =>
        not_not.mp fun hne => hcon ⟨z, hz, hne⟩
      rw [deriv_eq_of_eqOn_nhds hSo hz₀S hconst, deriv_const]
    obtain ⟨z₁, hz₁S, hz₁⟩ := hnc
    obtain ⟨l, mm, l', m', hlm, hode⟩ := exists_real_linear_ode hSo (hα.mono hSB) ha hb
      (fun n => Or.inl (hane n)) (fun n z hz => (hint n z hz).2) hz₁S hz₀S hz₁
    -- global extension of an explicit germ
    have hext : ∀ β : ℂ → ℂ, DifferentiableOn ℂ β upperHalfPlaneSet →
        (∀ z : ℂ, 0 < z.im → _root_.deriv β z ≠ 0) → (∀ z ∈ S, α z = β z) →
        ∀ z : ℂ, 0 < z.im → 0 < (β z).im ∧ qSeriesExt (F.c k) (β z) = qSeriesExt (F.c k) z := by
      intro β hβ hβ' hαβ
      refine forall_im_pos_and_eq_of_local hN F k hB1 hβ hβ' hz₀U
        (by rw [← hαβ z₀ hz₀S]; exact hm.trans_le (hαm z₀ (hSB hz₀S))) ?_
      filter_upwards [hSo.mem_nhds hz₀S] with z hz
      rw [← hαβ z hz]
      exact hαf z (hSB hz)
    -- a germ equal to `α` near `z₀` has nonzero derivative at `z₀`
    have hnd : ∀ β : ℂ → ℂ, (∀ z ∈ S, α z = β z) → _root_.deriv β z₀ ≠ 0 := fun β hαβ => by
      rw [← deriv_eq_of_eqOn_nhds hSo hz₀S hαβ]
      exact hd
    rcases eqOn_explicit_of_real_linear_ode hSo hSc hSU (hα.mono hSB) hlm hode with
      ⟨c₀, A, M₀, K, hA, hP⟩ | ⟨c₀, B, K, hL⟩ | ⟨A, M₀, K, hA, hE⟩ | ⟨B, K, hAf⟩
    · -- power family
      have hK : K ≠ 0 := by
        rintro rfl
        apply hnd (fun _ => (M₀ : ℂ)) (fun z hz => by rw [hP z hz]; ring)
        exact deriv_const _ _
      have hder : ∀ z : ℂ, 0 < z.im → HasDerivAt (fun z => K * (z - c₀) ^ (A : ℂ) + M₀)
          (K * ((A : ℂ) * (z - c₀) ^ ((A : ℂ) - 1) * 1)) z := fun z hz =>
        ((((hasDerivAt_id' z).sub_const (c₀ : ℂ)).cpow_const
          (sub_ofReal_mem_slitPlane hz c₀)).const_mul K).add_const (M₀ : ℂ)
      have hglob := hext _ (fun z hz => (hder z hz).differentiableAt.differentiableWithinAt)
        (fun z hz => by
          rw [(hder z hz).deriv, mul_one]
          refine mul_ne_zero hK (mul_ne_zero (Complex.ofReal_ne_zero.mpr hA) ?_)
          rw [Ne, Complex.cpow_eq_zero_iff]
          exact fun h => sub_ofReal_ne_zero hz c₀ h.1) hP
      rcases power_family_cases hc hA hK hglob with ⟨hA1, a₀, ha₀, hKa⟩ | ⟨hA1, a₀, ha₀, hKa⟩
      · refine isMoebiusSymmetryOn_of_affine (b := M₀ - a₀ * c₀) ha₀ (fun z hz => ?_)
          (fun z hz => ?_)
        · rw [hP z hz, hA1, hKa, Complex.ofReal_one, Complex.cpow_one]
          push_cast
          ring
        · have h := (hglob z hz).2
          rw [hA1, hKa, Complex.ofReal_one, Complex.cpow_one] at h
          rw [← h]
          push_cast
          ring_nf
      · refine isMoebiusSymmetryOn_of_inv (K := a₀) (c₀ := c₀) (M₀ := M₀) ha₀ hSU
          (fun z hz => ?_) (fun z hz => ?_)
        · rw [hP z hz, hA1, hKa, Complex.ofReal_neg, Complex.ofReal_one, Complex.cpow_neg_one]
        · have h := (hglob z hz).2
          rw [hA1, hKa, Complex.ofReal_neg, Complex.ofReal_one, Complex.cpow_neg_one] at h
          exact h
    · -- logarithmic family: impossible
      have hB : B ≠ 0 := by
        rintro rfl
        apply hnd (fun _ => K) (fun z hz => by rw [hL z hz]; simp)
        exact deriv_const _ _
      have hder : ∀ z : ℂ, 0 < z.im → HasDerivAt (fun z => (B : ℂ) * Complex.log (z - c₀) + K)
          ((B : ℂ) * (1 / (z - c₀))) z := fun z hz =>
        ((((hasDerivAt_id' z).sub_const (c₀ : ℂ)).clog
          (sub_ofReal_mem_slitPlane hz c₀)).const_mul (B : ℂ)).add_const K
      have hglob := hext _ (fun z hz => (hder z hz).differentiableAt.differentiableWithinAt)
        (fun z hz => by
          rw [(hder z hz).deriv]
          exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hB)
            (one_div_ne_zero (sub_ofReal_ne_zero hz c₀))) hL
      exact (false_of_log_family hc hglob).elim
    · -- exponential family: impossible
      have hK : K ≠ 0 := by
        rintro rfl
        apply hnd (fun _ => (M₀ : ℂ)) (fun z hz => by rw [hE z hz]; ring)
        exact deriv_const _ _
      have hder : ∀ z : ℂ, HasDerivAt (fun z => K * Complex.exp (A * z) + M₀)
          (K * (Complex.exp (A * z) * A)) z := fun z =>
        ((((hasDerivAt_id' z).const_mul (A : ℂ)).cexp).const_mul K).add_const (M₀ : ℂ)
          |>.congr_deriv (by ring)
      have hglob := hext _ (fun z _ => (hder z).differentiableAt.differentiableWithinAt)
        (fun z _ => by
          rw [(hder z).deriv]
          exact mul_ne_zero hK (mul_ne_zero (Complex.exp_ne_zero _)
            (Complex.ofReal_ne_zero.mpr hA))) hE
      exact (false_of_exp_family hA hK fun z hz => (hglob z hz).1).elim
    · -- affine family: an integer translation
      have hB : B ≠ 0 := by
        rintro rfl
        apply hnd (fun _ => K) (fun z hz => by rw [hAf z hz]; simp)
        exact deriv_const _ _
      have hder : ∀ z : ℂ, HasDerivAt (fun z => (B : ℂ) * z + K) (B : ℂ) z := fun z => by
        simpa using ((hasDerivAt_id' z).const_mul (B : ℂ)).add_const K
      have hglob := hext _ (fun z _ => (hder z).differentiableAt.differentiableWithinAt)
        (fun z _ => by
          rw [(hder z).deriv]
          exact Complex.ofReal_ne_zero.mpr hB) hAf
      obtain ⟨hB1', n, hKn⟩ := exists_int_of_affine_family hc hglob
      refine isMoebiusSymmetryOn_of_affine (a := 1) (b := n) one_pos (fun z hz => ?_)
        (fun z hz => ?_)
      · rw [hAf z hz, hB1', hKn]
        push_cast
        ring
      · have h := (hglob z hz).2
        rw [hB1', hKn] at h
        push_cast at h ⊢
        exact h

end VOA.Moonshine.ConwayNorton
