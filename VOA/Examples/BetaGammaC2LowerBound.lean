/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.BetaGammaInstance
import VOA.Examples.BetaGammaC2SpanReduction
import VOA.Modularity.GammaThetaStatement

/-!
# The beta--gamma C2 quotient is infinite-dimensional

The level-zero beta powers survive the super C2 quotient.  Their monomial coefficients are
detectors.  Conformal weight forces a same-weight C2 generator to start two units below the
target doubled weight, while beta-minus-gamma charge is bounded by doubled word weight.
-/

namespace VOA.BGNonC2

open MvPolynomial
open VOA
open VOA.BetaGamma
open VOA.BG
open VOA.BGGrad
open VOA.BGInst
open VOA.GammaThetaStmt
open VOA.Reconstruction

noncomputable section

def chargeWt : ℕ ⊕ ℕ → ℂ
  | Sum.inl _ => 1
  | Sum.inr _ => -1

@[simp] theorem chargeWt_inl (k : ℕ) : chargeWt (Sum.inl k) = 1 := rfl
@[simp] theorem chargeWt_inr (k : ℕ) : chargeWt (Sum.inr k) = -1 := rfl

noncomputable def chargeGrading (c : ℂ) : Submodule ℂ Fock :=
  MvPolynomial.weightedHomogeneousSubmodule ℂ chargeWt c

theorem mem_chargeGrading {c : ℂ} {p : Fock} :
    p ∈ chargeGrading c ↔ p.IsWeightedHomogeneous chargeWt c :=
  MvPolynomial.mem_weightedHomogeneousSubmodule ℂ chargeWt c p

theorem mulX_mem_chargeGrading (i : ℕ ⊕ ℕ) {c : ℂ} {p : Fock}
    (hp : p ∈ chargeGrading c) :
    mulX i p ∈ chargeGrading (chargeWt i + c) := by
  rw [mulX_apply, mem_chargeGrading]
  exact (MvPolynomial.isWeightedHomogeneous_X ℂ chargeWt i).mul (mem_chargeGrading.mp hp)

theorem der_mem_chargeGrading (i : ℕ ⊕ ℕ) {c : ℂ} {p : Fock}
    (hp : p ∈ chargeGrading c) :
    der i p ∈ chargeGrading (c - chargeWt i) := by
  rw [der_apply, mem_chargeGrading]
  exact (mem_chargeGrading.mp hp).pderiv (by ring)

theorem beta_mem_chargeGrading {c : ℂ} {p : Fock} (hp : p ∈ chargeGrading c) (n : ℤ) :
    beta n p ∈ chargeGrading (c + 1) := by
  rw [beta]
  by_cases hn : 0 ≤ n
  · rw [if_pos hn]
    simpa only [chargeWt_inr, sub_neg_eq_add] using
      (der_mem_chargeGrading (Sum.inr n.toNat) hp)
  · rw [if_neg hn]
    simpa only [chargeWt_inl, add_comm] using
      (mulX_mem_chargeGrading (Sum.inl (-n - 1).toNat) hp)

theorem gamma_mem_chargeGrading {c : ℂ} {p : Fock} (hp : p ∈ chargeGrading c) (n : ℤ) :
    gamma n p ∈ chargeGrading (c - 1) := by
  rw [gamma]
  by_cases hn : 0 ≤ n
  · rw [if_pos hn, LinearMap.neg_apply]
    exact Submodule.neg_mem _ (by
      simpa only [chargeWt_inl] using
        (der_mem_chargeGrading (Sum.inl n.toNat) hp))
  · rw [if_neg hn]
    simpa only [chargeWt_inr, sub_eq_add_neg, add_comm] using
      (mulX_mem_chargeGrading (Sum.inr (-n - 1).toNat) hp)

def ChargeFieldBG (f : FormalDist (Module.End ℂ Fock)) (D : ℂ) : Prop :=
  ∀ (j : ℤ) (c : ℂ) (x : Fock), x ∈ chargeGrading c → f j x ∈ chargeGrading (D + c)

theorem betaZ_ChargeField : ChargeFieldBG betaZ 1 := by
  intro j c x hx
  rw [betaZ_eq]
  simpa only [add_comm] using beta_mem_chargeGrading hx (-j - 1)

theorem gammaZ_ChargeField : ChargeFieldBG gammaZ (-1) := by
  intro j c x hx
  rw [gammaZ_eq]
  simpa only [sub_eq_add_neg, add_comm] using gamma_mem_chargeGrading hx (-j - 1)

def letterCharge : ℕ ⊕ ℕ → ℤ
  | Sum.inl _ => 1
  | Sum.inr _ => -1

@[simp] theorem letterCharge_inl (k : ℕ) : letterCharge (Sum.inl k) = 1 := rfl
@[simp] theorem letterCharge_inr (k : ℕ) : letterCharge (Sum.inr k) = -1 := rfl

theorem chargeWt_eq_letterCharge (i : ℕ ⊕ ℕ) :
    chargeWt i = (letterCharge i : ℂ) := by
  cases i <;> simp [chargeWt, letterCharge]

theorem bgBase_ChargeField (i : ℕ ⊕ ℕ) :
    ChargeFieldBG (bgBase i) (letterCharge i : ℂ) := by
  cases i with
  | inl k => simpa using betaZ_ChargeField
  | inr k => simpa using gammaZ_ChargeField

theorem bgGenField_ChargeField (i : ℕ ⊕ ℕ) :
    ChargeFieldBG (bgGenField i) (letterCharge i : ℂ) := by
  intro j c x hx
  change (((((lvl i).factorial : ℂ)⁻¹ •
    ((VOA.deriv^[lvl i] (bgBase i)) j))) x) ∈ _
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    ← Int.cast_smul_eq_zsmul ℂ (∏ m ∈ Finset.range (lvl i), (j + 1 + (m : ℤ))),
    LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (bgBase_ChargeField i _ _ _ hx)

theorem idFieldBG_ChargeField : ChargeFieldBG idField 0 := by
  intro j c x hx
  rw [idField_apply]
  by_cases hj : j = 0
  · subst hj
    simpa using hx
  · rw [if_neg hj, LinearMap.zero_apply]
    exact Submodule.zero_mem _

theorem ChargeFieldBG.nprod (ε : ℂ) {a b : FormalDist (Module.End ℂ Fock)}
    (ha : IsField a) (hb : IsField b) {Da Db : ℂ}
    (hca : ChargeFieldBG a Da) (hcb : ChargeFieldBG b Db) :
    ChargeFieldBG (nprodε ε ha hb) (Da + Db) := by
  intro s c x hx
  rw [nprodε_apply]
  refine finsum_mem_submodule _ _ (normalOrderedε_diag_support_finite ε ha hb s x)
    (fun m => ?_)
  rw [normalOrderedε_apply]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0]
    change a m (b (s - m) x) ∈ _
    have hb' := hcb (s - m) c x hx
    have ha' := hca m (Db + c) _ hb'
    simpa [add_assoc] using ha'
  · rw [if_neg h0, LinearMap.smul_apply]
    refine Submodule.smul_mem _ _ ?_
    change b (s - m) (a m x) ∈ _
    have ha' := hca m c x hx
    have hb' := hcb (s - m) (Da + c) _ ha'
    simpa [add_assoc, add_comm, add_left_comm] using hb'

def wordCharge : BGWord → ℤ
  | [] => 0
  | i :: rest => letterCharge i + wordCharge rest

@[simp] theorem wordCharge_nil : wordCharge ([] : BGWord) = 0 := rfl
@[simp] theorem wordCharge_cons (i : ℕ ⊕ ℕ) (rest : BGWord) :
    wordCharge (i :: rest) = letterCharge i + wordCharge rest := rfl

theorem YwordBG_ChargeField (l : BGWord) :
    ChargeFieldBG (YwordBG l) (wordCharge l : ℂ) := by
  induction l with
  | nil =>
      rw [YwordBG_nil, wordCharge_nil, Int.cast_zero]
      exact idFieldBG_ChargeField
  | cons i rest ih =>
      rw [YwordBG_cons, wordCharge_cons, Int.cast_add]
      exact ChargeFieldBG.nprod 1 (bgGenField_isField i) (YwordBG_isField rest)
        (bgGenField_ChargeField i) ih

theorem stWordBG_mem_chargeGrading (l : BGWord) :
    stWordBG l ∈ chargeGrading (wordCharge l : ℂ) := by
  induction l with
  | nil =>
      rw [stWordBG_nil, wordCharge_nil, Int.cast_zero, mem_chargeGrading]
      exact MvPolynomial.isWeightedHomogeneous_one ℂ chargeWt
  | cons i rest ih =>
      rw [stWordBG_cons, wordCharge_cons, Int.cast_add]
      simpa only [chargeWt_eq_letterCharge] using mulX_mem_chargeGrading i ih

def wordWeight2 : BGWord → ℕ
  | [] => 0
  | i :: rest => bgWt2 i + wordWeight2 rest

@[simp] theorem wordWeight2_nil : wordWeight2 ([] : BGWord) = 0 := rfl
@[simp] theorem wordWeight2_cons (i : ℕ ⊕ ℕ) (rest : BGWord) :
    wordWeight2 (i :: rest) = bgWt2 i + wordWeight2 rest := rfl

theorem wordWeight2_cast (l : BGWord) :
    (wordWeight2 l : ℂ) = 2 * bgWeight l := by
  induction l with
  | nil => simp [bgWeight_nil]
  | cons i rest ih =>
      rw [wordWeight2_cons, bgWeight_cons, Nat.cast_add, ih, bgWt2_cast]
      ring

theorem wordCharge_le_wordWeight2 (l : BGWord) :
    wordCharge l ≤ (wordWeight2 l : ℤ) := by
  induction l with
  | nil => simp
  | cons i rest ih =>
      rw [wordCharge_cons, wordWeight2_cons, Nat.cast_add]
      have hi : letterCharge i ≤ (bgWt2 i : ℤ) := by
        cases i with
        | inl k =>
            simp [letterCharge, bgWt2, bgLevel]
        | inr k =>
            have hk : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg _
            simp [letterCharge, bgWt2, bgLevel]
            omega
      omega

def betaZeroExp (n : ℕ) : (ℕ ⊕ ℕ) →₀ ℕ := Finsupp.single (Sum.inl 0) n

noncomputable def betaZeroPow (n : ℕ) : Fock := (X (Sum.inl 0) : Fock) ^ n

theorem betaZeroPow_eq_monomial (n : ℕ) :
    betaZeroPow n = monomial (betaZeroExp n) 1 := by
  rw [betaZeroPow, MvPolynomial.X_pow_eq_monomial, betaZeroExp]

theorem betaZeroExp_weight (n : ℕ) :
    Finsupp.weight bgWt (betaZeroExp n) = (n : ℂ) / 2 := by
  simp [betaZeroExp, Finsupp.weight_single, bgWt_inl]
  ring

theorem betaZeroExp_charge (n : ℕ) :
    Finsupp.weight chargeWt (betaZeroExp n) = (n : ℂ) := by
  simp [betaZeroExp, Finsupp.weight_single]

noncomputable def betaZeroCoeff (n : ℕ) : Fock →ₗ[ℂ] ℂ :=
  MvPolynomial.lcoeff ℂ (betaZeroExp n)

theorem betaZeroCoeff_eq_coeff (n : ℕ) (p : Fock) :
    betaZeroCoeff n p = coeff (betaZeroExp n) p := rfl

theorem betaZeroCoeff_zero_of_weight_ne (n : ℕ) {w : ℂ} {p : Fock}
    (hp : p ∈ gradingBG w) (hne : w ≠ (n : ℂ) / 2) :
    betaZeroCoeff n p = 0 := by
  rw [betaZeroCoeff_eq_coeff]
  by_contra hc
  have hw := (mem_gradingBG.mp hp) hc
  exact hne (hw.symm.trans (betaZeroExp_weight n))

theorem betaZeroCoeff_zero_of_charge_ne (n : ℕ) {c : ℂ} {p : Fock}
    (hp : p ∈ chargeGrading c) (hne : c ≠ (n : ℂ)) :
    betaZeroCoeff n p = 0 := by
  rw [betaZeroCoeff_eq_coeff]
  by_contra hc
  have hw := (mem_chargeGrading.mp hp) hc
  exact hne (hw.symm.trans (betaZeroExp_charge n))

theorem betaZeroCoeff_word_smul_neg_two (n : ℕ) (l₁ l₂ : BGWord) :
    betaZeroCoeff n
      (bgSVOA.smul (stWordBG l₁) (-2) (stWordBG l₂)) = 0 := by
  have hwt :
      bgSVOA.smul (stWordBG l₁) (-2) (stWordBG l₂) ∈
        gradingBG (bgWeight l₁ + bgWeight l₂ + 1) := by
    change mode (YBG (stWordBG l₁)) (-2) (stWordBG l₂) ∈ _
    rw [mode_apply, YBG_word]
    have h := YwordBG_WtField l₁ 1 (bgWeight l₂) (stWordBG l₂)
      (stWordBG_mem_gradingBG l₂)
    simpa only [Int.cast_one] using h
  by_cases heq : bgWeight l₁ + bgWeight l₂ + 1 = (n : ℂ) / 2
  · have hcharge :
        bgSVOA.smul (stWordBG l₁) (-2) (stWordBG l₂) ∈
          chargeGrading ((wordCharge l₁ + wordCharge l₂ : ℤ) : ℂ) := by
      change mode (YBG (stWordBG l₁)) (-2) (stWordBG l₂) ∈ _
      rw [mode_apply, YBG_word, Int.cast_add]
      exact YwordBG_ChargeField l₁ 1 (wordCharge l₂ : ℂ) (stWordBG l₂)
        (stWordBG_mem_chargeGrading l₂)
    have hweightNat : wordWeight2 l₁ + wordWeight2 l₂ + 2 = n := by
      have hc : ((wordWeight2 l₁ + wordWeight2 l₂ + 2 : ℕ) : ℂ) = (n : ℂ) := by
        push_cast
        rw [wordWeight2_cast, wordWeight2_cast]
        linear_combination 2 * heq
      exact_mod_cast hc
    have hlt : wordCharge l₁ + wordCharge l₂ < (n : ℤ) := by
      have h₁ := wordCharge_le_wordWeight2 l₁
      have h₂ := wordCharge_le_wordWeight2 l₂
      omega
    exact betaZeroCoeff_zero_of_charge_ne n hcharge
      (by exact_mod_cast (ne_of_lt hlt))
  · exact betaZeroCoeff_zero_of_weight_ne n hwt heq

/-- Every beta-power coefficient detector annihilates the full super C2 relation space. -/
theorem superO₂_le_ker_betaZeroCoeff (n : ℕ) :
    superO₂ bgSVOA ≤ LinearMap.ker (betaZeroCoeff n) :=
  BGInst.superO₂_le_ker_of_linearMap_word_pairs (betaZeroCoeff n)
    (betaZeroCoeff_word_smul_neg_two n)

theorem betaZeroCoeff_superO₂_zero (n : ℕ) {p : Fock} (hp : p ∈ superO₂ bgSVOA) :
    betaZeroCoeff n p = 0 :=
  LinearMap.mem_ker.mp (superO₂_le_ker_betaZeroCoeff n hp)

theorem betaZeroExp_injective : Function.Injective betaZeroExp := by
  intro m n h
  have h0 := congrArg (fun d : (ℕ ⊕ ℕ) →₀ ℕ => d (Sum.inl 0)) h
  simpa [betaZeroExp] using h0

@[simp] theorem betaZeroCoeff_betaZeroPow_self (n : ℕ) :
    betaZeroCoeff n (betaZeroPow n) = 1 := by
  rw [betaZeroCoeff_eq_coeff, betaZeroPow_eq_monomial, MvPolynomial.coeff_monomial,
    if_pos rfl]

theorem betaZeroCoeff_betaZeroPow_of_ne {m n : ℕ} (hmn : m ≠ n) :
    betaZeroCoeff n (betaZeroPow m) = 0 := by
  rw [betaZeroCoeff_eq_coeff, betaZeroPow_eq_monomial, MvPolynomial.coeff_monomial,
    if_neg (fun h => hmn (betaZeroExp_injective h))]

/-- The class of the n-th level-zero beta power in the super C2 quotient. -/
noncomputable def betaZeroClass (n : ℕ) : Fock ⧸ superO₂ bgSVOA :=
  (superO₂ bgSVOA).mkQ (betaZeroPow n)

theorem betaZeroPow_not_mem_superO₂ (n : ℕ) :
    betaZeroPow n ∉ superO₂ bgSVOA := by
  intro h
  have hz := betaZeroCoeff_superO₂_zero n h
  rw [betaZeroCoeff_betaZeroPow_self] at hz
  exact one_ne_zero hz

/-- The pure beta tower is linearly independent in the super C2 quotient. -/
theorem betaZeroClass_linearIndependent :
    LinearIndependent ℂ betaZeroClass := by
  rw [linearIndependent_iff']
  intro s c hc j hj
  have hmem : (∑ k ∈ s, c k • betaZeroPow k) ∈ superO₂ bgSVOA := by
    have hq : (superO₂ bgSVOA).mkQ (∑ k ∈ s, c k • betaZeroPow k) = 0 := by
      rw [map_sum]
      simpa only [map_smul, betaZeroClass] using hc
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq
  have hz := betaZeroCoeff_superO₂_zero j hmem
  have hcoeff : betaZeroCoeff j (∑ k ∈ s, c k • betaZeroPow k) = c j := by
    rw [map_sum]
    rw [Finset.sum_eq_single j (fun k _ hkj => ?_) (fun hjs => absurd hj hjs)]
    · rw [map_smul, betaZeroCoeff_betaZeroPow_self, smul_eq_mul, mul_one]
    · rw [map_smul, betaZeroCoeff_betaZeroPow_of_ne hkj, smul_zero]
  rw [hcoeff] at hz
  exact hz

/-- The beta--gamma super VOA is unconditionally not C2-cofinite. -/
theorem not_SuperC2Cofinite_bgSVOA : ¬ SuperC2Cofinite bgSVOA := by
  intro hfin
  rw [SuperC2Cofinite] at hfin
  haveI : Module.Finite ℂ (Fock ⧸ superO₂ bgSVOA) := hfin
  haveI : Finite ℕ := betaZeroClass_linearIndependent.finite
  exact not_finite ℕ

end

end VOA.BGNonC2

#print axioms VOA.BGNonC2.betaZeroCoeff_word_smul_neg_two
#print axioms VOA.BGNonC2.superO₂_le_ker_betaZeroCoeff
#print axioms VOA.BGNonC2.betaZeroClass_linearIndependent
#print axioms VOA.BGNonC2.not_SuperC2Cofinite_bgSVOA
