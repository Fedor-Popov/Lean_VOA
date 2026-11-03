/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.FrobeniusIndep
import VOA.Huang.FrobeniusUnique
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The Frobenius fundamental system at a regular singular point

For a Fuchsian equation `θ^s F + Σ_{i<s} cᵢ(y) θ^i F = 0` (`θ = y d/dy`) whose coefficients `cᵢ`
converge on the unit disc, **every** holomorphic solution on **any** connected open piece of the
punctured disc (taken on the universal cover `y = e^t`, `Re t < 0`, where `θ = d/dt`) is a finite
linear combination of the log-Frobenius solutions `y^ρ Σ_n yⁿ pₙ(log y)`, `ρ` running over the
roots of the indicial polynomial with multiplicity (`exists_eq_sum_logFun`,
`fundamental_system`).

This is the "matching expansions on an overlap" step of Huang's extension argument
(Huang 2005, CCM 7, (3.3)): a function known on a small region (e.g. a correlation function defined
by a convergent product expansion) which solves an equation regular at another singular point
**is** a log-Frobenius expansion at that point on the whole region.  No branch of `log y`, no
analytic continuation in the punctured disc, and no Wronskian is used:

* the `s` solutions `basisSol` are produced by `exists_logFuchsianEq` with leading term `ℓᵏ`,
  `k < mult(ρ)` (`dOp_indPoly_X_pow_eq_zero`: these are the kernel of `P₀(D)`);
* they are linearly independent as functions on `Re t < 0` (`basis_indep`): group the exponents by
  their class mod `ℤ`, apply the monodromy independence `eq_zero_of_sum_logFun_eq_zero`, then a
  triangular argument on the leading terms;
* the jet map `a ↦ (Σ aⱼ Fⱼ)^{(i)}(t₀)` is injective on `ℂ^s` (uniqueness, `eqOn_zero_of_ode`,
  plus the identity theorem to pass from `U` to the half-plane), hence surjective; so `F` and some
  `Σ aⱼ Fⱼ` share their jet at `t₀`, hence agree on `U`.

## Status
No `sorry`, no new axioms.  General (VOA-free).
-/

namespace VOA.Huang.FrobeniusLog

open Polynomial Filter Topology
open scoped BigOperators

/-! ## Index shifts -/

/-- Shift a log-series by `N` places: `(shiftIdx N p)ₙ = p_{n−N}` (`0` for `n < N`). -/
noncomputable def shiftIdx (N : ℕ) (p : ℕ → ℂ[X]) : ℕ → ℂ[X] :=
  fun n => if N ≤ n then p (n - N) else 0

theorem LogGood.shiftIdx {p : ℕ → ℂ[X]} (hp : LogGood p) (N : ℕ) :
    LogGood (FrobeniusLog.shiftIdx N p) where
  deg := by
    obtain ⟨K, hK⟩ := hp.deg
    refine ⟨K, fun n => ?_⟩
    unfold FrobeniusLog.shiftIdx
    split_ifs
    · exact hK _
    · simp
  coeff := fun k => Subexponential.of_shift N
    (Subexponential.of_le (fun n => le_of_eq (by simp [FrobeniusLog.shiftIdx])) (hp.coeff k))

/-- `logFun (λ + N) p = logFun λ (shiftIdx N p)`. -/
theorem logFun_add_nat (lam : ℂ) (N : ℕ) (p : ℕ → ℂ[X]) (t : ℂ) :
    logFun (lam + N) p t = logFun lam (shiftIdx N p) t := by
  rw [logFun, logFun]
  have hinj : Function.Injective (fun m : ℕ => m + N) := fun a b h => by simpa using h
  set f : ℕ → ℂ := fun n => Complex.exp ((lam + n) * t) * (shiftIdx N p n).eval t with hf
  have hsupp : Function.support f ⊆ Set.range (fun m : ℕ => m + N) := by
    intro n hn
    by_contra hnr
    apply hn
    have hlt : n < N := by
      by_contra hge
      exact hnr ⟨n - N, by simp only; omega⟩
    simp [hf, shiftIdx, Nat.not_le.mpr hlt]
  rw [← hinj.tsum_eq hsupp]
  refine tsum_congr fun m => ?_
  simp only [hf, shiftIdx, if_pos (Nat.le_add_left N m), Nat.add_sub_cancel]
  congr 2
  push_cast
  ring

/-! ## The indicial polynomial and the kernel of `P₀(D)` -/

/-- The indicial polynomial `I(X) = X^s + Σ_{i<s} cᵢ(0) X^i`. -/
noncomputable def indicial (s : ℕ) (c : ℕ → PowerSeries ℂ) : ℂ[X] := indPoly 0 s c 0

theorem indPoly_zero_eq_comp (lam : ℂ) (s : ℕ) (c : ℕ → PowerSeries ℂ) :
    indPoly lam s c 0 = (indicial s c).comp (X + Polynomial.C lam) := by
  simp [indicial, indPoly, add_comp, mul_comp, pow_comp]

theorem natDegree_indPoly (lam : ℂ) (s : ℕ) (c : ℕ → PowerSeries ℂ) (n : ℕ) :
    (indPoly lam s c n).natDegree = s := by
  have hdeg : ((X + Polynomial.C (lam + n)) ^ s : ℂ[X]).degree = (s : WithBot ℕ) := by
    rw [degree_pow, degree_X_add_C, nsmul_one]
  have hlt : (∑ i ∈ Finset.range s, Polynomial.C (PowerSeries.coeff 0 (c i))
      * (X + Polynomial.C (lam + n)) ^ i).degree < (s : WithBot ℕ) := by
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe s)).mpr fun i hi => ?_
    have hi' : i < s := Finset.mem_range.mp hi
    refine lt_of_le_of_lt (degree_mul_le _ _) ?_
    refine lt_of_le_of_lt (add_le_add degree_C_le (degree_pow_le _ _)) ?_
    rw [degree_X_add_C, zero_add, nsmul_one]
    exact Nat.cast_lt.mpr hi'
  have h : (indPoly lam s c n).degree = (s : WithBot ℕ) := by
    rw [indPoly, degree_add_eq_left_of_degree_lt (hlt.trans_eq hdeg.symm), hdeg]
  exact natDegree_eq_of_degree_eq_some h

theorem indicial_ne_zero (s : ℕ) (c : ℕ → PowerSeries ℂ) : indicial s c ≠ 0 :=
  indPoly_ne_zero 0 s c 0

/-- `ℓᵏ ∈ ker P₀(D)` for `k` below the multiplicity of `ρ` as an indicial root. -/
theorem dOp_indPoly_X_pow_eq_zero {s : ℕ} {c : ℕ → PowerSeries ℂ} {ρ : ℂ} {k : ℕ}
    (hk : k < (indicial s c).rootMultiplicity ρ) :
    dOp (indPoly ρ s c 0) (X ^ k) = 0 := by
  have hm : (indicial s c).rootMultiplicity ρ = (indPoly ρ s c 0).rootMultiplicity 0 := by
    rw [indPoly_zero_eq_comp]; exact rootMultiplicity_eq_rootMultiplicity
  obtain ⟨U, hU⟩ := pow_rootMultiplicity_dvd (indPoly ρ s c 0) 0
  rw [map_zero, sub_zero, ← hm] at hU
  rw [hU, dOp_mul, Module.End.mul_apply, dOp_X_pow_apply]
  refine iterate_derivative_eq_zero ?_
  exact lt_of_le_of_lt (le_trans (natDegree_dOp_le _ _) (by rw [natDegree_X_pow])) hk

/-! ## Exponent classes mod `ℤ` -/

/-- The indicial roots in the monodromy class `μ`. -/
noncomputable def classSet (s : ℕ) (c : ℕ → PowerSeries ℂ) (μ : ℂ) : Finset ℂ :=
  (indicial s c).roots.toFinset.filter fun x => monoEig x = μ

/-- A representative of the class `μ` of minimal real part. -/
noncomputable def repOf (s : ℕ) (c : ℕ → PowerSeries ℂ) (μ : ℂ) : ℂ :=
  if h : (classSet s c μ).Nonempty then
    Classical.choose (Finset.exists_min_image (classSet s c μ) Complex.re h)
  else 0

theorem repOf_spec {s : ℕ} {c : ℕ → PowerSeries ℂ} {μ : ℂ} (h : (classSet s c μ).Nonempty) :
    repOf s c μ ∈ classSet s c μ ∧ ∀ x ∈ classSet s c μ, (repOf s c μ).re ≤ x.re := by
  rw [repOf, dif_pos h]
  exact Classical.choose_spec (Finset.exists_min_image (classSet s c μ) Complex.re h)

theorem mem_classSet_self {s : ℕ} {c : ℕ → PowerSeries ℂ} {ρ : ℂ}
    (hρ : ρ ∈ (indicial s c).roots.toFinset) : ρ ∈ classSet s c (monoEig ρ) := by
  simp [classSet, hρ]

theorem monoEig_repOf {s : ℕ} {c : ℕ → PowerSeries ℂ} {ρ : ℂ}
    (hρ : ρ ∈ (indicial s c).roots.toFinset) : monoEig (repOf s c (monoEig ρ)) = monoEig ρ := by
  have := (repOf_spec ⟨ρ, mem_classSet_self hρ⟩).1
  simp only [classSet, Finset.mem_filter] at this
  exact this.2

theorem twoPiI_ne_zero : twoPiI ≠ 0 := by
  simp [twoPiI, Real.pi_ne_zero, Complex.I_ne_zero]

/-- Two exponents with the same monodromy eigenvalue differ by an integer. -/
theorem exists_int_of_monoEig_eq {x y : ℂ} (h : monoEig x = monoEig y) :
    ∃ n : ℤ, x - y = n := by
  have h1 : Complex.exp ((x - y) * twoPiI) = 1 := by
    rw [sub_mul, Complex.exp_sub, ← monoEig, ← monoEig, h, div_self (monoEig_ne_zero y)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  refine ⟨n, ?_⟩
  have : (x - y) * twoPiI = n * twoPiI := by rw [hn, twoPiI]
  exact mul_right_cancel₀ twoPiI_ne_zero this

/-- The shift of `ρ` above its class representative. -/
noncomputable def nShift (s : ℕ) (c : ℕ → PowerSeries ℂ) (ρ : ℂ) : ℕ :=
  ⌊(ρ - repOf s c (monoEig ρ)).re⌋₊

theorem repOf_add_nShift {s : ℕ} {c : ℕ → PowerSeries ℂ} {ρ : ℂ}
    (hρ : ρ ∈ (indicial s c).roots.toFinset) :
    repOf s c (monoEig ρ) + (nShift s c ρ : ℂ) = ρ := by
  obtain ⟨n, hn⟩ := exists_int_of_monoEig_eq (monoEig_repOf hρ).symm
  have hle := (repOf_spec ⟨ρ, mem_classSet_self hρ⟩).2 ρ (mem_classSet_self hρ)
  have hre : (ρ - repOf s c (monoEig ρ)).re = n := by rw [hn]; simp
  have hn0 : (0 : ℤ) ≤ n := by
    have : (0 : ℝ) ≤ n := by rw [← hre, Complex.sub_re]; linarith
    exact_mod_cast this
  have hnat : nShift s c ρ = n.toNat := by
    have : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn0
    rw [nShift, hre, ← this, Nat.floor_natCast]
  rw [hnat]
  have : ((n.toNat : ℕ) : ℂ) = (n : ℂ) := by
    rw [show ((n.toNat : ℕ) : ℂ) = ((n.toNat : ℤ) : ℂ) by push_cast; rfl,
      Int.toNat_of_nonneg hn0]
  rw [this, ← hn]; ring

theorem repOf_eq_of_monoEig_eq {s : ℕ} {c : ℕ → PowerSeries ℂ} {ρ ρ' : ℂ}
    (h : monoEig ρ = monoEig ρ') : repOf s c (monoEig ρ) = repOf s c (monoEig ρ') := by
  rw [h]

/-! ## The basis of formal solutions -/

/-- Index set of the Frobenius basis: an indicial root `ρ` and `k < mult(ρ)`. -/
abbrev Idx (s : ℕ) (c : ℕ → PowerSeries ℂ) : Type :=
  Σ ρ : (indicial s c).roots.toFinset, Fin ((indicial s c).rootMultiplicity (ρ : ℂ))

theorem card_Idx (s : ℕ) (c : ℕ → PowerSeries ℂ) : Fintype.card (Idx s c) = s := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Finset.sum_coe_sort (indicial s c).roots.toFinset
    (fun ρ => (indicial s c).rootMultiplicity ρ)]
  rw [Finset.sum_congr rfl fun ρ _ => (count_roots (indicial s c)).symm,
    Multiset.toFinset_sum_count_eq, IsAlgClosed.card_roots_eq_natDegree]
  exact natDegree_indPoly 0 s c 0

/-- The exponent of a basis element. -/
def Idx.exp {s : ℕ} {c : ℕ → PowerSeries ℂ} (j : Idx s c) : ℂ := j.1.1

theorem Idx.exp_mem {s : ℕ} {c : ℕ → PowerSeries ℂ} (j : Idx s c) :
    j.exp ∈ (indicial s c).roots.toFinset := j.1.2

theorem exists_basisSol {s : ℕ} {c : ℕ → PowerSeries ℂ} (j : Idx s c) :
    ∃ p : ℕ → ℂ[X], LogFuchsianEq j.exp s c p ∧ (∀ m < 0, p m = 0) ∧ p 0 = X ^ (j.2 : ℕ) :=
  exists_logFuchsianEq j.exp s c 0 _ (dOp_indPoly_X_pow_eq_zero j.2.isLt)

/-- The basis log-series: exponent `ρ`, leading term `ℓᵏ`. -/
noncomputable def basisSol {s : ℕ} {c : ℕ → PowerSeries ℂ} (j : Idx s c) : ℕ → ℂ[X] :=
  Classical.choose (exists_basisSol j)

theorem basisSol_eq {s : ℕ} {c : ℕ → PowerSeries ℂ} (j : Idx s c) :
    LogFuchsianEq j.exp s c (basisSol j) :=
  (Classical.choose_spec (exists_basisSol j)).1

theorem basisSol_zero {s : ℕ} {c : ℕ → PowerSeries ℂ} (j : Idx s c) :
    basisSol j 0 = X ^ (j.2 : ℕ) :=
  (Classical.choose_spec (exists_basisSol j)).2.2

theorem logGood_basisSol {s : ℕ} (hs : 1 ≤ s) {c : ℕ → PowerSeries ℂ}
    (hc : ∀ i < s, c i ∈ SubexpPS) (j : Idx s c) : LogGood (basisSol j) :=
  logGood_of_logFuchsianEq hs hc (basisSol_eq j)

theorem isRoot_exp {s : ℕ} {c : ℕ → PowerSeries ℂ} (j : Idx s c) :
    (indicial s c).IsRoot j.exp :=
  (mem_roots (indicial_ne_zero s c)).mp (Multiset.mem_toFinset.mp j.exp_mem)

/-! ## Independence of the basis -/

/-- **The basis functions are linearly independent on the half-plane.** -/
theorem basis_indep {s : ℕ} (hs : 1 ≤ s) {c : ℕ → PowerSeries ℂ} (hc : ∀ i < s, c i ∈ SubexpPS)
    (a : Idx s c → ℂ)
    (h : ∀ t ∈ halfPlane, ∑ j, a j * logFun j.exp (basisSol j) t = 0) : ∀ j, a j = 0 := by
  classical
  set R := (indicial s c).roots.toFinset with hR
  set M : Finset ℂ := R.image monoEig with hM
  set Q : ℂ → ℕ → ℂ[X] := fun μ =>
    ∑ j ∈ (Finset.univ : Finset (Idx s c)).filter (fun j => monoEig j.exp = μ),
      a j • shiftIdx (nShift s c j.exp) (basisSol j) with hQ
  have hgood : ∀ μ ∈ M, LogGood (Q μ) := fun μ _ =>
    LogGood.sum _ fun j _ => ((logGood_basisSol hs hc j).shiftIdx _).smul _
  have hfib : ∀ μ, ∀ t ∈ halfPlane, logFun (repOf s c μ) (Q μ) t
      = ∑ j ∈ (Finset.univ : Finset (Idx s c)).filter (fun j => monoEig j.exp = μ),
          a j * logFun j.exp (basisSol j) t := by
    intro μ t ht
    rw [hQ, logFun_sum _ (fun j _ => ((logGood_basisSol hs hc j).shiftIdx _).smul _) _ ht]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [logFun_smul, ← logFun_add_nat]
    have hjμ : monoEig j.exp = μ := (Finset.mem_filter.mp hj).2
    congr 1
    rw [← hjμ, repOf_add_nShift j.exp_mem]
  have hsum : ∀ t ∈ halfPlane, ∑ μ ∈ M, logFun (repOf s c μ) (Q μ) t = 0 := by
    intro t ht
    rw [Finset.sum_congr rfl fun μ _ => hfib μ t ht]
    rw [Finset.sum_fiberwise_of_maps_to (g := fun j : Idx s c => monoEig j.exp)
      (fun j _ => Finset.mem_image_of_mem _ j.exp_mem)]
    exact h t ht
  have hdist : ∀ μ ∈ M, ∀ μ' ∈ M, μ ≠ μ' →
      monoEig (repOf s c μ) ≠ monoEig (repOf s c μ') := by
    intro μ hμ μ' hμ' hne
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hμ
    obtain ⟨ρ', hρ', rfl⟩ := Finset.mem_image.mp hμ'
    rw [monoEig_repOf hρ, monoEig_repOf hρ']
    exact hne
  have hQ0 := eq_zero_of_sum_logFun_eq_zero M (repOf s c) hdist Q hgood hsum
  -- triangular argument on the leading terms
  have key : ∀ N, ∀ j : Idx s c, nShift s c j.exp = N → a j = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro j₀ hj₀
    set μ := monoEig j₀.exp with hμ
    have hQN := congrArg (fun q => Polynomial.coeff q (j₀.2 : ℕ))
      (hQ0 μ (Finset.mem_image_of_mem _ j₀.exp_mem) N)
    simp only [hQ, Finset.sum_apply, Pi.smul_apply, finsetSum_coeff, coeff_smul, smul_eq_mul,
      coeff_zero] at hQN
    have hmem : j₀ ∈ (Finset.univ : Finset (Idx s c)).filter (fun j => monoEig j.exp = μ) := by
      simp [hμ]
    rw [Finset.sum_eq_single_of_mem j₀ hmem] at hQN
    · rw [shiftIdx, if_pos (le_of_eq hj₀), hj₀, Nat.sub_self, basisSol_zero, coeff_X_pow,
        if_pos rfl, mul_one] at hQN
      exact hQN
    · intro j hj hne
      have hjμ : monoEig j.exp = μ := (Finset.mem_filter.mp hj).2
      rcases lt_trichotomy (nShift s c j.exp) N with hlt | heq | hgt
      · rw [ih _ hlt j rfl, zero_mul]
      · rw [shiftIdx, if_pos (le_of_eq heq), heq, Nat.sub_self, basisSol_zero, coeff_X_pow]
        have hexp : j.exp = j₀.exp := by
          rw [← repOf_add_nShift j.exp_mem, ← repOf_add_nShift j₀.exp_mem, hjμ, ← hμ, heq, hj₀]
        have hk : (j₀.2 : ℕ) ≠ (j.2 : ℕ) := by
          intro hk
          apply hne
          obtain ⟨⟨ρ, hρ⟩, k⟩ := j
          obtain ⟨⟨ρ₀, hρ₀⟩, k₀⟩ := j₀
          simp only [Idx.exp] at hexp
          subst hexp
          have : k = k₀ := Fin.ext hk.symm
          subst this
          rfl
        rw [if_neg hk, mul_zero]
      · rw [shiftIdx, if_neg (by omega), coeff_zero, mul_zero]
  intro j
  exact key _ j rfl

/-! ## The fundamental system -/

/-- The basis functions on the half-plane. -/
noncomputable def basisFun {s : ℕ} {c : ℕ → PowerSeries ℂ} (j : Idx s c) : ℂ → ℂ :=
  logFun j.exp (basisSol j)

/-- **Every solution on a connected open piece of the half-plane is a combination of the
Frobenius basis.** -/
theorem exists_eq_sum_logFun {s : ℕ} (hs : 1 ≤ s) {c : ℕ → PowerSeries ℂ}
    (hc : ∀ i < s, c i ∈ SubexpPS) {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUH : U ⊆ halfPlane) {t₀ : ℂ} (ht₀ : t₀ ∈ U) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F U)
    (hode : ∀ t ∈ U, iteratedDeriv s F t
      + ∑ i ∈ Finset.range s, psEval (c i) (Complex.exp t) * iteratedDeriv i F t = 0) :
    ∃ a : Idx s c → ℂ, ∀ t ∈ U, F t = ∑ j, a j * basisFun j t := by
  classical
  set A : ℕ → ℂ → ℂ := fun i t => psEval (c i) (Complex.exp t) with hA
  have hAd : ∀ i < s, DifferentiableOn ℂ (A i) U := fun i hi =>
    (differentiableOn_psEval_exp (hc i hi)).mono hUH
  have hFj : ∀ j : Idx s c, DifferentiableOn ℂ (basisFun j) halfPlane := fun j =>
    differentiableOn_logFun (logGood_basisSol hs hc j) _
  have hodej : ∀ j : Idx s c, ∀ t ∈ halfPlane, iteratedDeriv s (basisFun j) t
      + ∑ i ∈ Finset.range s, A i t * iteratedDeriv i (basisFun j) t = 0 := fun j t ht =>
    logFun_ode hc (logGood_basisSol hs hc j) (basisSol_eq j) ht
  -- combinations of basis functions solve the equation
  set G : (Idx s c → ℂ) → ℂ → ℂ := fun a t => ∑ j, a j * basisFun j t with hG
  have hGd : ∀ a, DifferentiableOn ℂ (G a) halfPlane := fun a => by
    have : DifferentiableOn ℂ (fun t => ∑ j ∈ Finset.univ, a j * basisFun j t) halfPlane :=
      DifferentiableOn.fun_sum fun j _ => (hFj j).const_mul (a j)
    simpa [hG] using this
  have hGder : ∀ a i, ∀ t ∈ halfPlane,
      iteratedDeriv i (G a) t = ∑ j, a j * iteratedDeriv i (basisFun j) t := fun a i t ht =>
    iteratedDeriv_sum_on isOpen_halfPlane Finset.univ a (fun j _ => hFj j) i ht
  have hGode : ∀ a, ∀ t ∈ halfPlane, iteratedDeriv s (G a) t
      + ∑ i ∈ Finset.range s, A i t * iteratedDeriv i (G a) t = 0 := by
    intro a t ht
    simp only [hGder a _ t ht, Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := hodej j t ht
    have e : ∑ x ∈ Finset.range s, A x t * (a j * iteratedDeriv x (basisFun j) t)
        = a j * ∑ x ∈ Finset.range s, A x t * iteratedDeriv x (basisFun j) t := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    linear_combination a j * this
  -- the jet map
  set Mx : Matrix (Fin s) (Idx s c) ℂ := fun i j => iteratedDeriv i (basisFun j) t₀ with hMx
  have hjet : ∀ a (i : Fin s), iteratedDeriv i (G a) t₀ = (Mx.mulVecLin a) i := by
    intro a i
    rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hGder a i t₀ (hUH ht₀)]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hinj : Function.Injective Mx.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have hzeroU : Set.EqOn (G a) 0 U :=
      eqOn_zero_of_ode hUo hUc hAd ((hGd a).mono hUH) (fun t ht => hGode a t (hUH ht)) ht₀
        (fun i hi => by rw [hjet a ⟨i, hi⟩, ha]; rfl)
    have hloc : G a =ᶠ[𝓝 t₀] 0 :=
      Filter.eventually_of_mem (hUo.mem_nhds ht₀) fun t ht => hzeroU ht
    have hzeroH : Set.EqOn (G a) 0 halfPlane :=
      ((hGd a).analyticOnNhd isOpen_halfPlane).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_halfPlane (hUH ht₀) hloc
    funext j
    exact basis_indep hs hc a (fun t ht => by simpa [hG, basisFun] using hzeroH ht) j
  have hsurj : Function.Surjective Mx.mulVecLin := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, card_Idx,
      Fintype.card_fin]
  obtain ⟨a, ha⟩ := hsurj fun i => iteratedDeriv i F t₀
  refine ⟨a, fun t ht => ?_⟩
  have := eqOn_of_ode hUo hUc hAd hF ((hGd a).mono hUH) hode (fun t ht => hGode a t (hUH ht)) ht₀
    (fun i hi => by rw [hjet a ⟨i, hi⟩, ha])
  exact this ht

/-- **The Frobenius fundamental system** (packaged): every holomorphic solution on a
connected open piece `U` of `Re t < 0` of `F⁽ˢ⁾ + Σ_{i<s} cᵢ(e^t) F⁽ⁱ⁾ = 0` (`cᵢ` convergent on the
unit disc) is `Σ_j aⱼ y^{λⱼ} Σ_n yⁿ p_{j,n}(log y)` (`y = e^t`), with exactly `s` terms, each
`λⱼ` an indicial root and each `pⱼ` a formal log-solution. -/
theorem fundamental_system {s : ℕ} (hs : 1 ≤ s) {c : ℕ → PowerSeries ℂ}
    (hc : ∀ i < s, c i ∈ SubexpPS) {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUH : U ⊆ halfPlane) (hUne : U.Nonempty) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F U)
    (hode : ∀ t ∈ U, iteratedDeriv s F t
      + ∑ i ∈ Finset.range s, psEval (c i) (Complex.exp t) * iteratedDeriv i F t = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (lam : ι → ℂ) (p : ι → ℕ → ℂ[X]) (a : ι → ℂ),
      Fintype.card ι = s ∧ (∀ j, LogFuchsianEq (lam j) s c (p j)) ∧
      (∀ j, (indicial s c).IsRoot (lam j)) ∧
      ∀ t ∈ U, F t = ∑ j, a j * logFun (lam j) (p j) t := by
  obtain ⟨t₀, ht₀⟩ := hUne
  obtain ⟨a, ha⟩ := exists_eq_sum_logFun hs hc hUo hUc hUH ht₀ hF hode
  exact ⟨Idx s c, inferInstance, fun j => j.exp, basisSol, a, card_Idx s c, basisSol_eq,
    isRoot_exp, ha⟩

end VOA.Huang.FrobeniusLog
