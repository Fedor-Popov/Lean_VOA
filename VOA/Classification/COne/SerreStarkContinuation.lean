/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkRemoval
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Serre–Stark S5-5b: analytic continuation of the resolvent factor

The resolvent factor `F_g(s) = a_{R(s) g}(t)`, `R(s) = ∏_p (1 − p^{−2s} U_p)^{−1}`, is holomorphic
on the set `Good` where all factors are invertible (`differentiableAt_Fs`); the complement of
`Good` is closed and countable (`isClosed_not_good`, `countable_not_good`). The proof transports
the commutative operator algebra into matrices (`ιm`, an injective algebra map that commutes with
`Ring.inverse`) and uses the differentiability of `Ring.inverse` in a complete normed ring.
-/

open Complex Polynomial Filter Topology
open scoped UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

namespace ClassSetup

variable (S : ClassSetup)

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- A basis of the class-form space. -/
def bV : Module.Basis (Fin (Module.finrank ℂ S.V)) ℂ S.V := Module.finBasis ℂ S.V

/-- Matrices of size `dim V`. -/
abbrev Mat : Type := Matrix (Fin (Module.finrank ℂ S.V)) (Fin (Module.finrank ℂ S.V)) ℂ

/-- Operators as matrices. -/
def Φm : Module.End ℂ S.V ≃ₐ[ℂ] S.Mat := LinearMap.toMatrixAlgEquiv S.bV

/-- The operator algebra inside the matrices. -/
def ιm : S.opAlg →ₐ[ℂ] S.Mat := S.Φm.toAlgHom.comp S.opAlg.val

theorem ιm_injective : Function.Injective S.ιm := by
  intro a b h
  apply Subtype.ext
  exact S.Φm.injective h

theorem isUnit_of_isUnit_ιm {a : S.opAlg} (h : IsUnit (S.ιm a)) : IsUnit a := by
  apply S.isUnit_of_isUnit_coe
  have : (a : Module.End ℂ S.V) = S.Φm.symm (S.ιm a) := by
    simp [ιm]
  rw [this]
  exact h.map S.Φm.symm

theorem ιm_inverse (a : S.opAlg) : S.ιm (Ring.inverse a) = Ring.inverse (S.ιm a) := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [Ring.inverse_unit, show S.ιm (u : S.opAlg) = ((Units.map S.ιm.toMonoidHom u : S.Matˣ) :
      S.Mat) from rfl, Ring.inverse_unit, Units.coe_map_inv]
    rfl
  · rw [Ring.inverse_non_unit a ha, map_zero, Ring.inverse_non_unit]
    exact fun h => ha (S.isUnit_of_isUnit_ιm h)

/-- The functional `A ↦ a_{A g}(t)` on matrices. -/
def Lm (g : S.V) : S.Mat →ₗ[ℂ] ℂ :=
  S.coeffL S.t ∘ₗ LinearMap.applyₗ g ∘ₗ S.Φm.symm.toLinearMap

/-- `U(p²)` as a matrix. -/
def Mp (p : S.ι) : S.Mat := S.ιm (S.Ua p)

/-- The resolvent product as a matrix. -/
def resM (s : ℂ) : S.Mat :=
  ((Finset.univ : Finset S.ι).toList.map fun p =>
    Ring.inverse (1 - ((p.1 : ℂ) ^ (-(2 * s))) • S.Mp p)).prod

theorem Fs_eq_resM (s : ℂ) (g : S.V) : S.Fs s g = S.Lm g (S.resM s) := by
  have h1 : ((S.Rinv s : S.opAlg) : Module.End ℂ S.V) = S.Φm.symm (S.ιm (S.Rinv s)) := by
    simp [ιm]
  have h2 : S.ιm (S.Rinv s) = S.resM s := by
    rw [Rinv, ← Finset.prod_map_toList, map_list_prod, List.map_map, resM]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply]
    rw [ιm_inverse, map_sub, map_one, map_smul]
    rfl
  rw [Fs, h1, h2]
  rfl

theorem differentiableAt_list_prod {ι' : Type*} (L : List ι') (F : ι' → ℂ → S.Mat) {s : ℂ}
    (hF : ∀ i ∈ L, DifferentiableAt ℂ (F i) s) :
    DifferentiableAt ℂ (fun s => (L.map fun i => F i s).prod) s := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hF a List.mem_cons_self).mul (ih fun i hi => hF i (List.mem_cons_of_mem a hi))

theorem isUnit_Mp_of_good {s : ℂ} (hs : S.Good s) (p : S.ι) :
    IsUnit (1 - ((p.1 : ℂ) ^ (-(2 * s))) • S.Mp p) := by
  have := (hs p).map S.ιm
  rwa [map_sub, map_one, map_smul] at this

theorem good_of_isUnit_Mp {s : ℂ} (h : ∀ p : S.ι, IsUnit (1 - ((p.1 : ℂ) ^ (-(2 * s))) • S.Mp p)) :
    S.Good s := by
  intro p
  apply S.isUnit_of_isUnit_ιm
  rw [map_sub, map_one, map_smul]
  exact h p

theorem differentiableAt_resM {s : ℂ} (hs : S.Good s) : DifferentiableAt ℂ S.resM s := by
  refine S.differentiableAt_list_prod _ _ fun p _ => ?_
  have hp0 : (p.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (S.prime p).ne_zero
  have hin : DifferentiableAt ℂ (fun s : ℂ => 1 - ((p.1 : ℂ) ^ (-(2 * s))) • S.Mp p) s := by
    refine (differentiableAt_const _).sub (DifferentiableAt.smul_const ?_ _)
    exact ((differentiableAt_id.const_mul 2).neg).const_cpow (Or.inl hp0)
  exact (differentiableAt_inverse (S.isUnit_Mp_of_good hs p)).comp s hin

/-- `F_g` is holomorphic on `Good`. -/
theorem differentiableAt_Fs (g : S.V) {s : ℂ} (hs : S.Good s) :
    DifferentiableAt ℂ (fun s => S.Fs s g) s := by
  have e : (fun s => S.Fs s g) = fun s => S.Lm g (S.resM s) := funext fun s => S.Fs_eq_resM s g
  rw [e]
  exact (LinearMap.toContinuousLinearMap (S.Lm g)).differentiableAt.comp s
    (S.differentiableAt_resM hs)

/-! ## The bad set is closed and countable -/

theorem isOpen_good : IsOpen {s | S.Good s} := by
  have : {s | S.Good s} = ⋂ p : S.ι,
      (fun s : ℂ => 1 - ((p.1 : ℂ) ^ (-(2 * s))) • S.Mp p) ⁻¹' {A | IsUnit A} := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    exact ⟨fun h p => S.isUnit_Mp_of_good h p, S.good_of_isUnit_Mp⟩
  rw [this]
  refine isOpen_iInter_of_finite fun p => ?_
  refine Units.isOpen.preimage ?_
  have hp0 : (p.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (S.prime p).ne_zero
  refine continuous_const.sub (Continuous.smul ?_ continuous_const)
  exact continuous_id.const_mul 2 |>.neg |>.const_cpow (Or.inl hp0)

theorem eval_charpolyRev_eq_det (M : S.Mat) (x : ℂ) :
    (Matrix.charpolyRev M).eval x = (1 - x • M).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  rcases eq_or_ne i j with hij | hij <;> simp [hij] <;> ring

theorem countable_cpow_eq (p : ℕ) (hp : 1 < p) (x : ℂ) :
    {s : ℂ | (p : ℂ) ^ (-(2 * s)) = x}.Countable := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hlog : Complex.log p ≠ 0 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _)]
    exact Complex.ofReal_ne_zero.2 (Real.log_pos (by exact_mod_cast hp)).ne'
  by_cases hx : x = 0
  · convert Set.countable_empty
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, hx]
    exact (cpow_ne_zero_iff.2 (Or.inl hp0))
  · refine (Set.countable_range fun k : ℤ =>
      -(Complex.log x + k * (2 * Real.pi * I)) / (2 * Complex.log p)).mono ?_
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    rw [cpow_def_of_ne_zero hp0, ← Complex.exp_log hx, Complex.exp_eq_exp_iff_exists_int] at hs
    obtain ⟨k, hk⟩ := hs
    refine ⟨k, ?_⟩
    simp only
    rw [div_eq_iff (mul_ne_zero two_ne_zero hlog)]
    linear_combination hk

theorem countable_not_good : {s | ¬ S.Good s}.Countable := by
  have hsub : {s | ¬ S.Good s} ⊆ ⋃ p : S.ι, ⋃ x ∈ (Matrix.charpolyRev (S.Mp p)).roots.toFinset,
      {s : ℂ | (p.1 : ℂ) ^ (-(2 * s)) = x} := by
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    have : ∃ p : S.ι, ¬ IsUnit (1 - ((p.1 : ℂ) ^ (-(2 * s))) • S.Mp p) := by
      by_contra hcon; push Not at hcon; exact hs (S.good_of_isUnit_Mp hcon)
    obtain ⟨p, hp⟩ := this
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨p, _, ?_, rfl⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots]
    · rw [Polynomial.IsRoot, eval_charpolyRev_eq_det]
      by_contra hdet
      exact hp ((Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hdet))
    · intro h0
      have := congrArg (Polynomial.eval 0) h0
      rw [Matrix.eval_charpolyRev, Polynomial.eval_zero] at this
      exact one_ne_zero this
  refine Set.Countable.mono hsub ?_
  refine Set.countable_iUnion fun p => ?_
  refine Set.Countable.biUnion (Finset.countable_toSet _) fun x _ => ?_
  exact countable_cpow_eq p.1 (S.prime p).one_lt x

/-! ## The identity `Λ_f(s)/Γ(s) = (2π/√N)^{-s} F_g(s) t^{-s} L(2s, ψ^{(N)})` -/

instance : NeZero S.r := ⟨fun h => by
  have := S.hrN; rw [h] at this; exact S.hN.ne' (Nat.eq_zero_of_zero_dvd this)⟩

/-- `ψ^{(N)}` as a Dirichlet character mod `N`. -/
def χN : DirichletCharacter ℂ S.N := DirichletCharacter.changeLevel S.hrN S.ψ

theorem chiN_eq (v : ℕ) : S.chiN v = S.χN (v : ZMod S.N) := by
  unfold chiN χN
  by_cases hv : v.Coprime S.N
  · rw [if_pos hv]
    have hu : IsUnit (v : ZMod S.N) := (ZMod.isUnit_iff_coprime v S.N).2 hv
    obtain ⟨u, hu'⟩ := hu
    rw [← hu', DirichletCharacter.changeLevel_eq_cast_of_dvd, hu', ZMod.cast_natCast S.hrN]
  · rw [if_neg hv, MulChar.map_nonunit]
    rwa [ZMod.isUnit_iff_coprime]

theorem LSeries_chiN {w : ℂ} (hw : 1 < w.re) :
    LSeries S.chiN w = DirichletCharacter.LFunction S.χN w := by
  rw [DirichletCharacter.LFunction_eq_LSeries _ hw]
  congr 1
  funext v
  exact S.chiN_eq v

variable {f : ℂ → ℂ} (hf : IsClassForm S.N S.r S.ψ S.t f)

/-- The class form as an element of `V`. -/
def gf : S.V := ⟨restrictUpper f, f, hf, rfl⟩

/-- `Λ_f(s)/Γ(s)`. -/
def G1 (s : ℂ) : ℂ := (fePair S.N f S.hN S.h24 hf.1).Λ s * (Gamma s)⁻¹

/-- `(2π/√N)^{-s} F_g(s) t^{-s} L(2s, ψ^{(N)})`. -/
def G2 (s : ℂ) : ℂ := ((feScale S.N : ℝ) : ℂ) ^ (-s) * S.Fs s (S.gf hf) * (S.t : ℂ) ^ (-s) *
  DirichletCharacter.LFunction S.χN (2 * s)

/-- The domain `Ω` of the identity theorem. -/
def Ω : Set ℂ := {s | S.Good s ∧ s ≠ 0 ∧ s ≠ 1 / 2}

theorem isOpen_Ω : IsOpen S.Ω := by
  have : S.Ω = {s | S.Good s} ∩ ({0}ᶜ ∩ {1 / 2}ᶜ) := by
    ext s; simp [Ω]
  rw [this]
  exact S.isOpen_good.inter (isOpen_compl_singleton.inter isOpen_compl_singleton)

theorem isPreconnected_Ω : IsPreconnected S.Ω := by
  have hc : S.Ωᶜ.Countable := by
    have : S.Ωᶜ ⊆ {s | ¬ S.Good s} ∪ ({0} ∪ {1 / 2}) := by
      intro s hs
      simp only [Ω, Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, not_not] at hs
      rcases hs with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    exact (S.countable_not_good.union ((Set.countable_singleton _).union
      (Set.countable_singleton _))).mono this
  have := (Set.Countable.isPathConnected_compl_of_one_lt_rank (by simp) hc).isConnected
  rw [compl_compl] at this
  exact this.isPreconnected

theorem differentiableAt_G1 {s : ℂ} (h0 : s ≠ 0) (h12 : s ≠ 1 / 2) :
    DifferentiableAt ℂ (S.G1 hf) s :=
  (fePair_differentiableAt S.hN S.h24 hf.1 h0 h12).mul (Complex.differentiable_one_div_Gamma s)

theorem differentiableAt_G2 {s : ℂ} (hs : S.Good s) (h12 : s ≠ 1 / 2) :
    DifferentiableAt ℂ (S.G2 hf) s := by
  have hc0 : ((feScale S.N : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (feScale_pos S.hN).ne'
  have ht0 : (S.t : ℂ) ≠ 0 := Nat.cast_ne_zero.2 S.ht.ne_zero
  refine (((differentiableAt_id.neg.const_cpow (Or.inl hc0)).mul
    (S.differentiableAt_Fs (S.gf hf) hs)).mul
    (differentiableAt_id.neg.const_cpow (Or.inl ht0))).mul ?_
  have h2 : 2 * s ≠ 1 := fun h => h12 (by linear_combination h / 2)
  exact (DirichletCharacter.differentiableAt_LFunction _ _ (Or.inl h2)).comp s
    (differentiableAt_id.const_mul 2)

theorem G1_eq_G2_of_re {s : ℂ} (hs : 3 / 2 < s.re) : S.G1 hf s = S.G2 hf s := by
  have hΓ : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hLS : LSeries (thetaTypeCoeff f) s = S.LS s (S.gf hf) := rfl
  rw [G1, fePair_Λ_eq S.hN S.h24 hf.1 hs, hLS, S.LS_eq_Fs _ hs,
    S.LSeries_chiN (by rw [mul_re]; simp; linarith), G2]
  field_simp

/-- **Analytic continuation.** On `Ω` (all resolvent factors invertible, `s ≠ 0, 1/2`),
`Λ_f(s)/Γ(s) = (2π/√N)^{-s} F_g(s) t^{-s} L(2s, ψ^{(N)})`. -/
theorem G1_eq_G2 {s : ℂ} (hs : s ∈ S.Ω) : S.G1 hf s = S.G2 hf s := by
  have h2 : (2 : ℂ) ∈ S.Ω := ⟨S.good_of_re (by norm_num), two_ne_zero, by norm_num⟩
  have hD1 : DifferentiableOn ℂ (S.G1 hf) S.Ω := fun s hs =>
    (S.differentiableAt_G1 hf hs.2.1 hs.2.2).differentiableWithinAt
  have hD2 : DifferentiableOn ℂ (S.G2 hf) S.Ω := fun s hs =>
    (S.differentiableAt_G2 hf hs.1 hs.2.2).differentiableWithinAt
  have hA1 : AnalyticOnNhd ℂ (S.G1 hf) S.Ω := hD1.analyticOnNhd S.isOpen_Ω
  have hA2 : AnalyticOnNhd ℂ (S.G2 hf) S.Ω := hD2.analyticOnNhd S.isOpen_Ω
  refine hA1.eqOn_of_preconnected_of_eventuallyEq hA2 S.isPreconnected_Ω h2 ?_ hs
  have hopen : IsOpen {s : ℂ | 3 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds (show (3 / 2 : ℝ) < (2 : ℂ).re by norm_num)] with s hs
  exact S.G1_eq_G2_of_re hf hs

end ClassSetup

end SSHecke

end VOA.Classification.COne
