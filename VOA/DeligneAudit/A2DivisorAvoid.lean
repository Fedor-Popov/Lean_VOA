/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2SectorGeneric

/-!
# A uniform witness off the divisor `Δ = 0`

For a pair `a ≠ b` of roots let `E_{ab} = ∏_{i ≠ j, {i,j} ≠ {a,b}} (z_i - z_j)`, and let
`w = Σ_{a ≠ b} E_{ab}`, a symmetric polynomial (`wS : B_m`).  On the divisor `z_a = z_b` only the two
terms `E_{ab} = E_{ba}` survive, and they do not vanish there.

**`wS_not_mem`**: `w` lies in no height-one prime of `B_m` containing the discriminant.  Proof: such a
prime is `(π)` for a prime element `π` of the UFD `B_m`; in `P_m = ℂ[z]`, `π` is a nonconstant
divisor of `Δ = ∏(z_i - z_j)`, hence divisible by a prime factor `f` of some `z_i - z_j`; then
`f` and `z_i - z_j` differ by a unit, so the substitution `z_i ↦ z_j` kills `π`, hence `w`, but it
sends `w` to `2 ∏_{{k,l} ≠ {i,j}} (z_k - z_l)|_{z_i = z_j} ≠ 0`.
-/

namespace VOA.DeligneAudit.A2

open MvPolynomial VOA.DeligneAudit.SectorFiber VOA.HeightOneGlobalization

noncomputable section

variable {m : ℕ}

/-- `E_{ab} = ∏_{i ≠ j, (i,j) ∉ {(a,b),(b,a)}} (z_i - z_j)`. -/
def pairE (a b : Fin (m + 0)) : MvPolynomial (Fin (m + 0)) ℂ :=
  ∏ i, ∏ j, if i = j ∨ (i = a ∧ j = b) ∨ (i = b ∧ j = a) then 1 else (X i - X j)

/-- `w = Σ_{a ≠ b} E_{ab}`. -/
def wSum (m : ℕ) : MvPolynomial (Fin (m + 0)) ℂ :=
  ∑ a, ∑ b, if a = b then 0 else pairE (m := m) a b

theorem rename_pairE (e : Equiv.Perm (Fin (m + 0))) (a b : Fin (m + 0)) :
    rename e (pairE a b) = pairE (e a) (e b) := by
  simp only [pairE, map_prod]
  conv_rhs => rw [← Equiv.prod_comp e]
  refine Finset.prod_congr rfl fun i _ => ?_
  conv_rhs => rw [← Equiv.prod_comp e]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [EmbeddingLike.apply_eq_iff_eq]
  split_ifs <;> simp

theorem wSum_isSymmetric (m : ℕ) : (wSum m).IsSymmetric := by
  intro e
  simp only [wSum, map_sum]
  conv_rhs => rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_rhs => rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [EmbeddingLike.apply_eq_iff_eq]
  split_ifs
  · simp
  · exact rename_pairE e a b

/-- `w` as an element of `B_m`. -/
def wS (m : ℕ) : SymAlg (K := ℂ) m := ⟨wSum m, wSum_isSymmetric m⟩

/-! ### The substitution `z_i ↦ z_j` -/

/-- Substitute `z_i := z_j`. -/
def collapse (i j : Fin (m + 0)) : MvPolynomial (Fin (m + 0)) ℂ →ₐ[ℂ] MvPolynomial (Fin (m + 0)) ℂ :=
  aeval fun k => if k = i then X j else X k

theorem collapse_X_sub (i j : Fin (m + 0)) : collapse i j (X i - X j) = 0 := by
  simp [collapse]

theorem collapse_X_sub_ne (i j k l : Fin (m + 0)) (_hij : i ≠ j) (hkl : k ≠ l)
    (h : ¬ ((k = i ∧ l = j) ∨ (k = j ∧ l = i))) : collapse i j (X k - X l) ≠ 0 := by
  simp only [collapse, map_sub, aeval_X]
  intro h0
  rw [sub_eq_zero] at h0
  split_ifs at h0 with hk hl hl
  · exact hkl (hk.trans hl.symm)
  · exact h (Or.inl ⟨hk, (X_injective h0).symm⟩)
  · exact h (Or.inr ⟨X_injective h0, hl⟩)
  · exact hkl (X_injective h0)

theorem collapse_pairE_self (i j : Fin (m + 0)) (hij : i ≠ j) :
    collapse i j (pairE i j) ≠ 0 := by
  simp only [pairE, map_prod]
  rw [Finset.prod_ne_zero_iff]
  intro k _
  rw [Finset.prod_ne_zero_iff]
  intro l _
  split_ifs with h
  · simp
  · push Not at h
    exact collapse_X_sub_ne i j k l hij h.1 (by
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact h.2.1 rfl rfl
      · exact h.2.2 rfl rfl)

theorem pairE_swap (a b : Fin (m + 0)) : pairE a b = pairE b a := by
  simp only [pairE]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  congr 1
  apply propext
  tauto

theorem collapse_pairE_other (i j a b : Fin (m + 0)) (hij : i ≠ j)
    (h : ¬ ((a = i ∧ b = j) ∨ (a = j ∧ b = i))) : collapse i j (pairE a b) = 0 := by
  simp only [pairE, map_prod]
  rw [Finset.prod_eq_zero_iff]
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rw [Finset.prod_eq_zero_iff]
  refine ⟨j, Finset.mem_univ _, ?_⟩
  rw [if_neg]
  · exact collapse_X_sub i j
  · rintro (h1 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hij h1
    · exact h (Or.inl ⟨rfl, rfl⟩)
    · exact h (Or.inr ⟨rfl, rfl⟩)

theorem collapse_wSum (i j : Fin (m + 0)) (hij : i ≠ j) : collapse i j (wSum m) ≠ 0 := by
  have hsum : collapse i j (wSum m) = collapse i j (pairE i j) + collapse i j (pairE i j) := by
    simp only [wSum, map_sum]
    rw [← Finset.sum_product' (f := fun a b => collapse i j (if a = b then 0 else pairE a b))]
    rw [Finset.sum_eq_add (i, j) (j, i) (by simp [hij])]
    · simp only [if_neg hij, if_neg (Ne.symm hij), pairE_swap j i]
    · rintro ⟨a, b⟩ _ ⟨h1, h2⟩
      dsimp only
      split_ifs
      · simp
      · apply collapse_pairE_other i j a b hij
        rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact h1 rfl
        · exact h2 rfl
    · simp
    · simp
  rw [hsum, ← two_mul]
  exact mul_ne_zero two_ne_zero (collapse_pairE_self i j hij)

/-! ### Prime avoidance -/

theorem divisor_of_dvd_linear (i j : Fin (m + 0)) {f : MvPolynomial (Fin (m + 0)) ℂ}
    (hf : ¬ IsUnit f) (hdvd : f ∣ X i - X j) (hij : i ≠ j) : collapse i j f = 0 := by
  obtain ⟨g, hg⟩ := hdvd
  have hXne : (X i - X j : MvPolynomial (Fin (m + 0)) ℂ) ≠ 0 := by
    rw [sub_ne_zero]; exact fun h => hij (X_injective h)
  have hf0 : f ≠ 0 := by rintro rfl; rw [zero_mul] at hg; exact hXne hg
  have hg0 : g ≠ 0 := by rintro rfl; rw [mul_zero] at hg; exact hXne hg
  have hdeg := totalDegree_mul_of_isDomain hf0 hg0
  rw [← hg] at hdeg
  have hX1 : (X i - X j : MvPolynomial (Fin (m + 0)) ℂ).totalDegree = 1 := by
    apply le_antisymm
    · refine (totalDegree_sub _ _).trans ?_
      simp
    · by_contra hlt
      push Not at hlt
      have h0 : (X i - X j : MvPolynomial (Fin (m + 0)) ℂ).totalDegree = 0 := by omega
      rw [totalDegree_eq_zero_iff_eq_C] at h0
      have := congrArg (MvPolynomial.coeff (Finsupp.single i 1)) h0
      rw [coeff_sub, coeff_X, coeff_X', coeff_C] at this
      simp [Finsupp.single_eq_single_iff, Ne.symm hij] at this
  have hfdeg : f.totalDegree ≠ 0 := by
    intro h0
    apply hf
    rw [totalDegree_eq_zero_iff_eq_C] at h0
    rw [h0]
    have hc : f.coeff 0 ≠ 0 := by
      intro hc; rw [hc, map_zero] at h0; exact hf0 h0
    exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
  have hgdeg : g.totalDegree = 0 := by omega
  rw [totalDegree_eq_zero_iff_eq_C] at hgdeg
  have hgc : g.coeff 0 ≠ 0 := by
    intro hc; rw [hc, map_zero] at hgdeg; exact hg0 hgdeg
  have h := congrArg (collapse i j) hg
  rw [collapse_X_sub, map_mul, hgdeg] at h
  have hcC : collapse i j (MvPolynomial.C (g.coeff 0)) ≠ 0 := by
    simp [collapse, hgc]
  exact (mul_eq_zero.mp h.symm).resolve_right hcC

/-- **Prime avoidance**: `w` lies in no height-one prime of `B_m` containing the discriminant. -/
theorem wS_not_mem (p : HeightOnePrime (SymAlg (K := ℂ) m)) (hΔ : discS m ∈ p.asIdeal) :
    wS m ∉ p.asIdeal := by
  intro hw
  have hpbot : p.asIdeal ≠ ⊥ := by
    intro h
    have := p.height_eq_one
    rw [h, Ideal.height_bot] at this
    exact zero_ne_one this
  obtain ⟨π, hπp, hπ⟩ := p.isPrime.exists_mem_prime_of_ne_bot hpbot
  have hspan : p.asIdeal = Ideal.span {π} := by
    have hle : Ideal.span {π} ≤ p.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hπp
    haveI : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
    by_contra hne
    have hlt : Ideal.span {π} < p.asIdeal := lt_of_le_of_ne hle (Ne.symm hne)
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [p.height_eq_one] at h1
    have h0 : (Ideal.span {π}).height = 0 := by
      by_contra hne0
      have h3 : (1 : ℕ∞) ≤ (Ideal.span {π}).height := ENat.one_le_iff_ne_zero.mpr hne0
      have h4 := (add_le_add_left h3 1).trans h1
      norm_num at h4
    rw [Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot,
      Set.mem_singleton_iff, Ideal.span_singleton_eq_bot] at h0
    exact hπ.ne_zero h0
  rw [hspan, Ideal.mem_span_singleton] at hw hΔ
  obtain ⟨u, hu⟩ := hw
  obtain ⟨v, hv⟩ := hΔ
  have hw' : wSum m = (π : MvPolynomial (Fin (m + 0)) ℂ) * u := congrArg Subtype.val hu
  have hΔ' : (discS m : MvPolynomial (Fin (m + 0)) ℂ) = (π : MvPolynomial (Fin (m + 0)) ℂ) * v :=
    congrArg Subtype.val hv
  have hne0 : (π : MvPolynomial (Fin (m + 0)) ℂ) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hnu : ¬ IsUnit (π : MvPolynomial (Fin (m + 0)) ℂ) := by
    intro hu'
    obtain ⟨r, hr, hrπ⟩ := isUnit_iff_eq_C_of_isReduced.mp hu'
    apply hπ.not_unit
    have hr0 : r ≠ 0 := hr.ne_zero
    refine IsUnit.of_mul_eq_one (b := ⟨MvPolynomial.C r⁻¹, fun e => by simp⟩) ?_
    apply Subtype.ext
    change (π : MvPolynomial (Fin (m + 0)) ℂ) * MvPolynomial.C r⁻¹ = 1
    rw [hrπ, ← map_mul, mul_inv_cancel₀ hr0, map_one]
  obtain ⟨f, hf, hfπ⟩ := WfDvdMonoid.exists_irreducible_factor hnu hne0
  have hfp : Prime f := hf.prime
  have hfΔ : f ∣ (discS m : MvPolynomial (Fin (m + 0)) ℂ) := hfπ.trans ⟨v, hΔ'⟩
  change f ∣ ∏ i : Fin (m + 0), ∏ j : Fin (m + 0), if i = j then 1 else (X i - X j) at hfΔ
  obtain ⟨i, _, hi⟩ := (hfp.dvd_finsetProd_iff _).mp hfΔ
  obtain ⟨j, _, hj⟩ := (hfp.dvd_finsetProd_iff _).mp hi
  by_cases hij : i = j
  · rw [if_pos hij] at hj
    exact hfp.not_unit (isUnit_of_dvd_one hj)
  rw [if_neg hij] at hj
  have hcf := divisor_of_dvd_linear i j hfp.not_unit hj hij
  have hcπ : collapse i j (π : MvPolynomial (Fin (m + 0)) ℂ) = 0 := by
    obtain ⟨g, hg⟩ := hfπ
    rw [hg, map_mul, hcf, zero_mul]
  apply collapse_wSum i j hij
  rw [hw', map_mul, hcπ, zero_mul]

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.wS_not_mem
end AxiomAudit
