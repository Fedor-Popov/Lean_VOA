/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.BetaGammaInstance
import VOA.Examples.BetaGammaC2LowerBound
import VOA.Examples.BetaGammaPolynomialReduction
import VOA.Modularity.GammaThetaStatement
import VOA.Modularity.SuperPoissonTrace

/-!
# The beta--gamma `C₂` and Poisson quotients

This file is the strict half-integral, purely even benchmark for the super quasi-lisse axis.
It treats `bgSVOA`, not symplectic fermions.  The two axes remain independent: the conformal
weights are half-integral while every state is even.

The first exact reduction is recorded here: the two level-one creation variables are literal
`C₂` generators, and the polynomial translation commutator carries that conclusion to every
positive level.  The Poisson quotient additionally kills the two remaining level-zero polynomial
directions by their zero modes.  The independent polynomial antiderivative and the weight/charge
coefficient detector prove respectively super Etingof finiteness and failure of super
`C₂`-cofiniteness.
-/

namespace VOA.BGInst

open VOA
open MvPolynomial
open VOA.BetaGamma
open VOA.BG
open VOA.GammaThetaStmt

-- The ambient namespace also contains unrelated Fock/creation names.  Fix the beta--gamma
-- polynomial carrier explicitly in this focused file.
local notation "Fock" => VOA.BetaGamma.Fock
local notation "X" => MvPolynomial.X
local notation "mulX" => VOA.BetaGamma.mulX
local notation "der" => VOA.BetaGamma.der

/-- The two weight-`1/2` creation states. -/
noncomputable def betaState : Fock := X (Sum.inl 0)
noncomputable def gammaState : Fock := X (Sum.inr 0)

/-- The beta state has the beta field. -/
theorem YBG_betaState : YBG betaState = betaZ := by
  simpa only [betaState, bgSVA_Y] using bgSVA_Y_beta

/-- The gamma state has the gamma field. -/
theorem YBG_gammaState : YBG gammaState = gammaZ := by
  simpa only [gammaState, bgSVA_Y] using bgSVA_Y_gamma

/-- The `(-2)`-product by the beta creation state is multiplication by the first higher beta
oscillator. -/
theorem betaState_smul_neg_two (v : Fock) :
    bgSVOA.smul betaState (-2) v = mulX (Sum.inl 1) v := by
  change mode (YBG betaState) (-2) v = mulX (Sum.inl 1) v
  rw [mode_apply, YBG_betaState, betaZ_of_nonneg (by norm_num)]
  norm_num

/-- The `(-2)`-product by the gamma creation state is multiplication by the first higher gamma
oscillator. -/
theorem gammaState_smul_neg_two (v : Fock) :
    bgSVOA.smul gammaState (-2) v = mulX (Sum.inr 1) v := by
  change mode (YBG gammaState) (-2) v = mulX (Sum.inr 1) v
  rw [mode_apply, YBG_gammaState, gammaZ_of_nonneg (by norm_num)]
  norm_num

/-- The beta zero mode is differentiation in the level-zero gamma variable. -/
theorem betaState_smul_zero (v : Fock) :
    bgSVOA.smul betaState 0 v = der (Sum.inr 0) v := by
  change mode (YBG betaState) 0 v = der (Sum.inr 0) v
  rw [mode_apply, YBG_betaState, betaZ_of_neg (by norm_num)]
  norm_num

/-- The gamma zero mode is minus differentiation in the level-zero beta variable. -/
theorem gammaState_smul_zero (v : Fock) :
    bgSVOA.smul gammaState 0 v = -der (Sum.inl 0) v := by
  change mode (YBG gammaState) 0 v = -der (Sum.inl 0) v
  rw [mode_apply, YBG_gammaState, gammaZ_of_neg (by norm_num)]
  norm_num

/-- Every multiple of the level-one beta oscillator is a super `C₂` relation. -/
theorem mulX_beta_one_mem_superO₂ (v : Fock) : mulX (Sum.inl 1) v ∈ superO₂ bgSVOA := by
  rw [← betaState_smul_neg_two]
  exact Submodule.subset_span ⟨betaState, v, rfl⟩

/-- Every multiple of the level-one gamma oscillator is a super `C₂` relation. -/
theorem mulX_gamma_one_mem_superO₂ (v : Fock) : mulX (Sum.inr 1) v ∈ superO₂ bgSVOA := by
  rw [← gammaState_smul_neg_two]
  exact Submodule.subset_span ⟨gammaState, v, rfl⟩

/-- Translation is a super `C₂` relation in this concrete system. -/
theorem T_mem_superO₂ (v : Fock) : T v ∈ superO₂ bgSVOA := by
  have h := Lneg1_mem_superO₂ bgSVOA v
  change mode (YBG bgOmega) 0 v ∈ superO₂ bgSVOA at h
  rw [show (0 : ℤ) = -1 + 1 by ring, mode_YBG_bgOmega_eq_Lbg, Lbg_neg_one_eq_T] at h
  exact h

/-- All positive beta oscillators, not merely level one, are super `C₂` relations.
The induction is the exact translation identity for the polynomial Fock representation. -/
theorem mulX_beta_succ_mem_superO₂ (k : ℕ) (v : Fock) :
    mulX (Sum.inl (k + 1)) v ∈ superO₂ bgSVOA := by
  induction k generalizing v with
  | zero => simpa using mulX_beta_one_mem_superO₂ v
  | succ n ih =>
      have hnonzero : ((n : ℂ) + 2) ≠ 0 := by
        have hcast : ((n : ℂ) + 2) = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
        rw [hcast]
        exact_mod_cast Nat.succ_ne_zero (n + 1)
      have hcomm := DFunLike.congr_fun (T_mulX (Sum.inl (n + 1))) v
      have hcomm' : ((n : ℂ) + 2) • mulX (Sum.inl (n + 2)) v =
          T (mulX (Sum.inl (n + 1)) v) - mulX (Sum.inl (n + 1)) (T v) := by
        convert hcomm.symm using 1 <;>
          simp [Module.End.mul_apply, lvl_inl, up_inl] <;> push_cast <;> ring
      have hmem : ((n : ℂ) + 2) • mulX (Sum.inl (n + 2)) v ∈ superO₂ bgSVOA := by
        rw [hcomm']
        exact (superO₂ bgSVOA).sub_mem (T_mem_superO₂ _) (ih (T v))
      have hinv := (superO₂ bgSVOA).smul_mem (((n : ℂ) + 2)⁻¹) hmem
      rwa [inv_smul_smul₀ hnonzero] at hinv

/-- All positive gamma oscillators, not merely level one, are super `C₂` relations. -/
theorem mulX_gamma_succ_mem_superO₂ (k : ℕ) (v : Fock) :
    mulX (Sum.inr (k + 1)) v ∈ superO₂ bgSVOA := by
  induction k generalizing v with
  | zero => simpa using mulX_gamma_one_mem_superO₂ v
  | succ n ih =>
      have hnonzero : ((n : ℂ) + 2) ≠ 0 := by
        have hcast : ((n : ℂ) + 2) = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
        rw [hcast]
        exact_mod_cast Nat.succ_ne_zero (n + 1)
      have hcomm := DFunLike.congr_fun (T_mulX (Sum.inr (n + 1))) v
      have hcomm' : ((n : ℂ) + 2) • mulX (Sum.inr (n + 2)) v =
          T (mulX (Sum.inr (n + 1)) v) - mulX (Sum.inr (n + 1)) (T v) := by
        convert hcomm.symm using 1 <;>
          simp [Module.End.mul_apply, lvl_inr, up_inr] <;> push_cast <;> ring
      have hmem : ((n : ℂ) + 2) • mulX (Sum.inr (n + 2)) v ∈ superO₂ bgSVOA := by
        rw [hcomm']
        exact (superO₂ bgSVOA).sub_mem (T_mem_superO₂ _) (ih (T v))
      have hinv := (superO₂ bgSVOA).smul_mem (((n : ℂ) + 2)⁻¹) hmem
      rwa [inv_smul_smul₀ hnonzero] at hinv

/-- Positive beta level is precisely the range already killed by the `C₂` induction. -/
theorem mulX_beta_pos_mem_superO₂ {k : ℕ} (hk : 1 ≤ k) (v : Fock) :
    mulX (Sum.inl k) v ∈ superO₂ bgSVOA := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  exact mulX_beta_succ_mem_superO₂ n v

/-- Positive gamma level is precisely the range already killed by the `C₂` induction. -/
theorem mulX_gamma_pos_mem_superO₂ {k : ℕ} (hk : 1 ≤ k) (v : Fock) :
    mulX (Sum.inr k) v ∈ superO₂ bgSVOA := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  exact mulX_gamma_succ_mem_superO₂ n v

/-- Differentiation in the level-zero gamma variable is a Poisson-trace relation. -/
theorem der_gamma_zero_mem_superPoissonRelSpan (v : Fock) :
    der (Sum.inr 0) v ∈ superPoissonRelSpan bgSVOA := by
  rw [← betaState_smul_zero]
  exact superZeroMode_mem_superPoissonRelSpan bgSVOA betaState v

/-- Differentiation in the level-zero beta variable is a Poisson-trace relation.
The sign is deliberately discharged by the submodule's additive closure. -/
theorem der_beta_zero_mem_superPoissonRelSpan (v : Fock) :
    der (Sum.inl 0) v ∈ superPoissonRelSpan bgSVOA := by
  have h := superZeroMode_mem_superPoissonRelSpan bgSVOA gammaState v
  change bgSVOA.smul gammaState 0 v ∈ superPoissonRelSpan bgSVOA at h
  rw [gammaState_smul_zero] at h
  simpa using (superPoissonRelSpan bgSVOA).neg_mem h

/-- The beta--gamma Poisson relation span is all of the Fock space.  This uses the zero mode of
the beta state and algebraic integration in the level-zero gamma variable; it is independent of
super `C₂`-cofiniteness. -/
theorem superPoissonRelSpan_eq_top : superPoissonRelSpan bgSVOA = ⊤ :=
  BetaGamma.submodule_eq_top_of_der_mem (superPoissonRelSpan bgSVOA) (Sum.inr 0)
    der_gamma_zero_mem_superPoissonRelSpan

/-- The half-integrally graded, purely even beta--gamma super VOA is super Etingof-finite.
This is not obtained from `C₂`-cofiniteness: the proof makes its Poisson quotient zero directly. -/
theorem bgSVOA_superEtingofFinite : SuperEtingofFinite bgSVOA := by
  rw [SuperEtingofFinite_iff, superPoissonRelSpan_eq_top]
  infer_instance

/-- The rank-one beta--gamma/symplectic-boson system is the strict half-integral, purely even
quasi-lisse benchmark: it is super Etingof-finite but not super `C₂`-cofinite.  The two halves
are independent proofs: the first uses zero-mode integration, the second the surviving beta-zero
coefficient tower. -/
theorem bgSVOA_strict_halfIntegral_quasiLisse :
    ¬ SuperC2Cofinite bgSVOA ∧ SuperEtingofFinite bgSVOA :=
  ⟨BGNonC2.not_SuperC2Cofinite_bgSVOA, bgSVOA_superEtingofFinite⟩

/-! ## An optional stronger `C₂` projection interface -/

/-- Projecting after embedding the two level-zero variables is the identity. -/
theorem zeroProject_zeroEmbed (q : BetaGamma.ZeroFock) :
    BetaGamma.zeroProject (BetaGamma.zeroEmbed q) = q := by
  have h : BetaGamma.zeroProject.comp BetaGamma.zeroEmbed = AlgHom.id ℂ BetaGamma.ZeroFock := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp
  exact DFunLike.congr_fun h q

/-- The pure beta-zero powers are linearly independent in the two-variable polynomial algebra.
This is deliberately a polynomial fact, before any vertex-algebra quotient is taken. -/
theorem zeroFock_betaTower_linearIndependent :
    LinearIndependent ℂ (fun n : ℕ => (MvPolynomial.X (0 : Fin 2) : BetaGamma.ZeroFock) ^ n) := by
  classical
  rw [linearIndependent_iff]
  intro ell hell
  set q : BetaGamma.ZeroFock :=
    ell.sum (fun n c => c • (MvPolynomial.X (0 : Fin 2) : BetaGamma.ZeroFock) ^ n) with hq
  have hqzero : q = 0 := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at hell
    rw [hq]
    simpa only [Finsupp.sum] using hell
  ext m
  have hcm : MvPolynomial.coeff (Finsupp.single (0 : Fin 2) m) q = ell m := by
    rw [hq, Finsupp.sum]
    rw [show MvPolynomial.coeff (Finsupp.single (0 : Fin 2) m)
          (∑ n ∈ ell.support, ell n • (MvPolynomial.X (0 : Fin 2) : BetaGamma.ZeroFock) ^ n)
          = (MvPolynomial.lcoeff (R := ℂ) (σ := Fin 2) (Finsupp.single (0 : Fin 2) m))
              (∑ n ∈ ell.support, ell n • (MvPolynomial.X (0 : Fin 2) : BetaGamma.ZeroFock) ^ n) from by
          rw [MvPolynomial.lcoeff_apply], map_sum]
    have hterm : ∀ n ∈ ell.support,
        (MvPolynomial.lcoeff (R := ℂ) (σ := Fin 2) (Finsupp.single (0 : Fin 2) m))
            (ell n • (MvPolynomial.X (0 : Fin 2) : BetaGamma.ZeroFock) ^ n)
          = if m = n then ell n else 0 := by
      intro n _
      rw [map_smul, MvPolynomial.lcoeff_apply, MvPolynomial.X_pow_eq_monomial,
        MvPolynomial.coeff_monomial, smul_eq_mul]
      by_cases h : m = n
      · rw [if_pos h, if_pos (by rw [h]), mul_one]
      · rw [if_neg h, if_neg (by
          intro he
          exact h (by
            have he0 := congrArg (fun t : Fin 2 →₀ ℕ => t 0) he
            simpa using he0.symm)), mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq ell.support m (fun n => ell n)]
    by_cases hm : m ∈ ell.support
    · rw [if_pos hm]
    · rw [if_neg hm, Finsupp.notMem_support_iff.mp hm]
  rw [← hcm, hqzero]
  simp

/-- A stronger projection statement than the strict non-lisse benchmark needs: every super `C₂`
generator vanishes after discarding all positive-level oscillators.  The unconditional theorem
`BGNonC2.not_SuperC2Cofinite_bgSVOA` above uses the individual beta-power coefficient detectors
instead, so it does not assume this condition. -/
def C2ProjectionCondition : Prop :=
  superO₂ bgSVOA ≤ LinearMap.ker BetaGamma.zeroProject.toLinearMap

/-- Under `C2ProjectionCondition`, the level-zero polynomial projection descends to the super
`C₂` quotient. -/
noncomputable def c2ZeroProject (hproj : C2ProjectionCondition) :
    (Fock ⧸ superO₂ bgSVOA) →ₗ[ℂ] BetaGamma.ZeroFock :=
  (superO₂ bgSVOA).liftQ BetaGamma.zeroProject.toLinearMap hproj

@[simp] theorem c2ZeroProject_mk (hproj : C2ProjectionCondition) (x : Fock) :
    c2ZeroProject hproj ((superO₂ bgSVOA).mkQ x) = BetaGamma.zeroProject x := rfl

/-- The descended zero-level projection is onto, with the displayed zero-level embedding as a
section. -/
theorem c2ZeroProject_surjective (hproj : C2ProjectionCondition) :
    Function.Surjective (c2ZeroProject hproj) := by
  intro q
  refine ⟨(superO₂ bgSVOA).mkQ (BetaGamma.zeroEmbed q), ?_⟩
  rw [c2ZeroProject_mk, zeroProject_zeroEmbed]

/-- If the exact projection condition holds, super `C₂`-cofiniteness would force the infinite
two-variable polynomial algebra to be finite-dimensional, which is impossible. -/
theorem not_superC2Cofinite_of_C2ProjectionCondition (hproj : C2ProjectionCondition) :
    ¬ SuperC2Cofinite bgSVOA := by
  intro hfin
  haveI : FiniteDimensional ℂ (Fock ⧸ superO₂ bgSVOA) := hfin
  haveI : FiniteDimensional ℂ BetaGamma.ZeroFock :=
    Module.Finite.of_surjective (c2ZeroProject hproj) (c2ZeroProject_surjective hproj)
  haveI : Finite ℕ := zeroFock_betaTower_linearIndependent.finite
  exact not_finite ℕ

end VOA.BGInst
