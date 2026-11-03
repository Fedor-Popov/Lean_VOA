/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesStrictWords

/-!
# The conformal grading of the model is a direct sum

The model pieces `modelDeg R t r d` (span of the length-`r` model word symbols of conformal
weight `d`) are independent in `d`, provided the coefficient ring carries a **scaling
automorphism** `θ : R → R` with `θ (t n) = 2^{n+1} t n` (the jet `T_n` has jet weight `n + 1`).
For `R_n = ℂ[T_j]/(jets of Tⁿ)` this is `T_j ↦ 2^{j+1} T_j`, which preserves the homogeneous
jet ideal.

* `sJ` — the scaling `u_j, v_j ↦ 2^j u_j, 2^j v_j` of `ℂ[u_j, v_j]`; `sJ_weighted`: on jet
  weight `e` it is multiplication by `2^e`;
* `Θ R θ` — the combined scaling of `R[u_j, v_j]`; `Θ_mword`: a model word symbol is an
  eigenvector with eigenvalue `2^{jet weight}`;
* `modelDeg_iSupIndep` — **independence of the conformal pieces of the model**, for each `r`.

Everything is proved outright.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial VOA.SymbolModel VOA.AdamovicSymbol
open VOA.AffineVOA.CorrectedR (Generator)

noncomputable section

/-! ### Scaling the jet ring -/

/-- The scaling `X (b, j) ↦ 2^j X (b, j)` of `ℂ[u_j, v_j]`. -/
def sJ : JetPoly →ₐ[ℂ] JetPoly := aeval fun x => (2 : ℂ) ^ x.2 • X x

theorem sJ_monomial (s : Fin 2 × ℕ →₀ ℕ) (c : ℂ) :
    sJ (monomial s c) = (2 : ℂ) ^ (s.sum fun x k => x.2 * k) • monomial s c := by
  rw [sJ, aeval_monomial, monomial_eq, Finsupp.prod, Finsupp.prod, Finsupp.sum]
  simp_rw [smul_pow, MvPolynomial.smul_eq_C_mul]
  rw [Finset.prod_mul_distrib, ← map_prod, ← Finset.prod_pow_eq_pow_sum]
  simp_rw [pow_mul]
  rw [algebraMap_eq]
  ring

/-- The scaling on jet weight `e` is multiplication by `2^e`. -/
theorem sJ_weighted {P : JetPoly} {e : ℕ}
    (hP : P ∈ weightedHomogeneousSubmodule ℂ jetWt (e : ℤ)) : sJ P = (2 : ℂ) ^ e • P := by
  rw [mem_weightedHomogeneousSubmodule] at hP
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [sJ_monomial]
  congr 2
  have hw := hP (mem_support_iff.mp hs)
  rw [Finsupp.weight_apply] at hw
  have : ((s.sum fun x k => x.2 * k : ℕ) : ℤ) = (e : ℤ) := by
    rw [← hw, Finsupp.sum, Finsupp.sum]
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [jetWt, mul_comm]
  exact_mod_cast this

/-- The jet weight of a letter, as a natural number. -/
def ljw : Generator × ℕ → ℕ
  | (.current _, n) => n
  | (.sugawara, n) => n + 1

/-- The jet weight of a word. -/
def wjw (w : List (Generator × ℕ)) : ℕ := (w.map ljw).sum

theorem wordWt_eq_wjw (w : List (Generator × ℕ)) : wordWt w = (wjw w : ℤ) + w.length := by
  induction w with
  | nil => simp [wordWt, wjw]
  | cons l w ih =>
    obtain ⟨g, n⟩ := l
    cases g <;> simp only [wordWt, wjw, List.map_cons, List.sum_cons, letterWt, ljw,
      List.length_cons] at ih ⊢ <;> push_cast [Nat.cast_list_sum] at ih ⊢ <;> linarith

theorem sJ_letterSym (l : Generator × ℕ) : sJ (letterSym l) = (2 : ℂ) ^ ljw l • letterSym l := by
  apply sJ_weighted
  have h := letterSym_mem_weighted l
  obtain ⟨g, n⟩ := l
  cases g <;> simpa [letterJetWt, ljw] using h

/-! ### Scaling the model ring -/

variable (R : Type) [CommRing R] [Algebra ℂ R] (θ : R →ₐ[ℂ] R)

/-- The combined scaling of `R[u_j, v_j]`: `θ` on coefficients, `2^j` on `u_j, v_j`. -/
def Θ : MPoly R →ₐ[ℂ] MPoly R :=
  ((aeval fun x : Fin 2 × ℕ => MvPolynomial.C (algebraMap ℂ R ((2 : ℂ) ^ x.2)) * X x :
      MPoly R →ₐ[R] MPoly R).restrictScalars ℂ).comp (MvPolynomial.mapAlgHom θ)

theorem Θ_ι (P : JetPoly) : Θ R θ (ι R P) = ι R (sJ P) := by
  have h : (Θ R θ).comp (ι R) = (ι R).comp sJ := by
    apply MvPolynomial.algHom_ext
    intro x
    simp only [Θ, ι, sJ, AlgHom.comp_apply, MvPolynomial.mapAlgHom_apply, map_X,
      AlgHom.restrictScalars_apply, aeval_X, map_smul]
    rw [Algebra.smul_def, MvPolynomial.algebraMap_apply]
  exact AlgHom.congr_fun h P

theorem Θ_C (a : R) : Θ R θ (MvPolynomial.C a) = MvPolynomial.C (θ a) := by
  simp [Θ]

variable (t : ℕ → R)

theorem Θ_mletter (ht : ∀ n, θ (t n) = (2 : ℂ) ^ (n + 1) • t n) (l : Generator × ℕ) :
    Θ R θ (mletter R t l) = (2 : ℂ) ^ ljw l • mletter R t l := by
  obtain ⟨g, n⟩ := l
  cases g with
  | current a =>
    change Θ R θ (ι R (letterSym _)) = _ • ι R (letterSym _)
    rw [Θ_ι, sJ_letterSym, map_smul]
  | sugawara =>
    change Θ R θ (ι R (letterSym _) + MvPolynomial.C (t n)) =
      _ • (ι R (letterSym _) + MvPolynomial.C (t n))
    rw [map_add, Θ_ι, sJ_letterSym, map_smul, Θ_C, ht, smul_add]
    congr 1
    rw [Algebra.smul_def, map_mul, Algebra.smul_def, MvPolynomial.algebraMap_apply]
    rfl

/-- A model word symbol is a scaling eigenvector, eigenvalue `2^{jet weight}`. -/
theorem Θ_mword (ht : ∀ n, θ (t n) = (2 : ℂ) ^ (n + 1) • t n) (w : List (Generator × ℕ)) :
    Θ R θ (mword R t w) = (2 : ℂ) ^ wjw w • mword R t w := by
  induction w with
  | nil => simp [wjw]
  | cons l w ih =>
    rw [mword_cons, map_mul, Θ_mletter R θ t ht, ih, smul_mul_smul_comm, ← pow_add]
    simp [wjw]

theorem two_zpow_injective : Function.Injective fun d : ℤ => (2 : ℂ) ^ d := by
  intro a b h
  simp only at h
  have h' : (((2 : ℝ) ^ a : ℝ) : ℂ) = (((2 : ℝ) ^ b : ℝ) : ℂ) := by push_cast; exact h
  exact zpow_right_injective₀ (by norm_num) (by norm_num) (Complex.ofReal_injective h')

/-- **The conformal pieces of the model are independent.** -/
theorem modelDeg_iSupIndep (ht : ∀ n, θ (t n) = (2 : ℂ) ^ (n + 1) • t n) (r : ℕ) :
    iSupIndep (modelDeg R t r) := by
  have h := (Module.End.eigenspaces_iSupIndep
    ((Θ R θ).toLinearMap)).comp (f := fun d : ℤ => (2 : ℂ) ^ (d - r))
    (fun a b hab => by simpa using two_zpow_injective hab)
  refine h.mono fun d => ?_
  rw [modelDeg, Submodule.span_le]
  rintro _ ⟨w, hw, hd, rfl⟩
  rw [SetLike.mem_coe, Function.comp_apply, Module.End.mem_eigenspace_iff,
    AlgHom.toLinearMap_apply, Θ_mword R θ t ht]
  congr 1
  rw [← hd, wordWt_eq_wjw, hw, add_sub_cancel_right, zpow_natCast]

end

end VOA.TwoSeries.StrictModel
