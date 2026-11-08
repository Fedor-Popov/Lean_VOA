import VOA.Moonshine.MoonshineCNComplexFrame

/-!
# Finite exponential coefficients in a complex lattice frame

The Newton recursions for the creation and annihilation exponentials work over
complex bilinear coordinates. Proofs adapt `LatticeGenChargeFields` to remove
the real positive frame, preserving the polynomial Fock carrier and all levels.
No analytic convergence or completed tensor product is used.
-/

set_option maxHeartbeats 800000

namespace VOA.Moonshine.ConwayNorton

open scoped BigOperators
open IntegralLattice HeisenbergN MvPolynomial
open Module (End)

variable {L : IntegralLattice} (F : ComplexLatticeFrame L)

noncomputable def creationVariable (α : L.carrier) (m : ℕ) : HeisenbergN.FockN (rank L) :=
  ∑ a : Fin (rank L), F.coordinate α a • (MvPolynomial.X ((m, a)) : HeisenbergN.FockN (rank L))


noncomputable def creationCoefficient (α : L.carrier) : ℕ → HeisenbergN.FockN (rank L)
  | 0 => 1
  | (N+1) => ((N+1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N+1), creationVariable F α m * creationCoefficient α (N - m)

theorem creationCoefficient_zero (α : L.carrier) : creationCoefficient F α 0 = 1 := by simp only [creationCoefficient]

theorem creationCoefficient_succ (α : L.carrier) (N : ℕ) :
    creationCoefficient F α (N+1)
      = ((N+1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N+1), creationVariable F α m * creationCoefficient F α (N - m) := by
  simp only [creationCoefficient]


theorem creationCoefficient_recursion_sum (α : L.carrier) (d : ℕ) :
    (∑ m ∈ Finset.range d, creationVariable F α m * creationCoefficient F α ((d-1) - m)) = (d : ℂ) • creationCoefficient F α d := by
  match d with
  | 0 => simp [creationCoefficient_zero]
  | (D+1) =>
    rw [creationCoefficient_succ]
    simp only [Nat.add_sub_cancel]
    rw [smul_smul]
    push_cast
    rw [mul_inv_cancel₀ (Nat.cast_add_one_ne_zero D), one_smul]


theorem creationVariable_derivative (α : L.carrier) (i : ℕ) (b : Fin (rank L)) (m : ℕ) :
    (pderiv ((i, b))) (creationVariable F α m)
      = if m = i then MvPolynomial.C (F.coordinate α b) else 0 := by
  rw [creationVariable, map_sum, Finset.sum_eq_single b]
  · rw [MvPolynomial.smul_eq_C_mul, pderiv_C_mul, pderiv_X, Pi.single_apply]
    by_cases h : m = i
    · subst h; rw [if_pos rfl, if_pos rfl, mul_one]
    · rw [if_neg (show ((m, b) : ℕ × Fin (rank L)) ≠ (i, b) from
        fun hc => h (congrArg Prod.fst hc)), mul_zero, if_neg h]
  · intro a _ ha
    rw [MvPolynomial.smul_eq_C_mul, pderiv_C_mul, pderiv_X, Pi.single_apply,
      if_neg (show ((m, a) : ℕ × Fin (rank L)) ≠ (i, b) from
        fun hc => ha (congrArg Prod.snd hc)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ b) h


theorem creationCoefficient_derivative (α : L.carrier) (i : ℕ) (b : Fin (rank L)) (N : ℕ) :
    (pderiv ((i, b))) (creationCoefficient F α N)
      = if i + 1 ≤ N then F.coordinate α b • (((i+1 : ℂ))⁻¹ • creationCoefficient F α (N - (i+1))) else 0 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => simp [creationCoefficient_zero]
    | (M+1) =>
      rw [creationCoefficient_succ, MvPolynomial.smul_eq_C_mul, pderiv_C_mul, map_sum]
      have hterm : ∀ m ∈ Finset.range (M+1),
          (pderiv ((i, b))) (creationVariable F α m * creationCoefficient F α (M - m))
            = (if m = i then MvPolynomial.C (F.coordinate α b) * creationCoefficient F α (M - m) else 0)
              + creationVariable F α m * (if i + 1 ≤ M - m then
                  F.coordinate α b • (((i+1:ℂ))⁻¹ • creationCoefficient F α ((M-m) - (i+1))) else 0) := by
        intro m hm
        rw [pderiv_mul, ih (M - m) (by simp at hm; omega), creationVariable_derivative]
        congr 1
        by_cases h : m = i
        · subst h; rw [if_pos rfl, if_pos rfl]
        · rw [if_neg h, if_neg h, zero_mul]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      have hS1 : (∑ m ∈ Finset.range (M+1),
              if m = i then MvPolynomial.C (F.coordinate α b) * creationCoefficient F α (M - m) else 0)
          = if i ≤ M then MvPolynomial.C (F.coordinate α b) * creationCoefficient F α (M - i) else 0 := by
        rw [Finset.sum_ite_eq' (Finset.range (M+1)) i
          (fun m => MvPolynomial.C (F.coordinate α b) * creationCoefficient F α (M - m))]
        simp only [Finset.mem_range]
        by_cases h : i ≤ M
        · rw [if_pos (by omega), if_pos h]
        · rw [if_neg (by omega), if_neg h]
      by_cases hiM : i ≤ M
      · have hS2 : (∑ m ∈ Finset.range (M+1),
              creationVariable F α m * (if i+1 ≤ M-m then
                F.coordinate α b • (((i+1:ℂ))⁻¹ • creationCoefficient F α ((M-m)-(i+1))) else 0))
            = F.coordinate α b • (((i+1:ℂ))⁻¹ • (((M - i : ℕ) : ℂ) • creationCoefficient F α (M - i))) := by
          have hpt : ∀ m ∈ Finset.range (M+1),
              creationVariable F α m * (if i+1 ≤ M-m then
                  F.coordinate α b • (((i+1:ℂ))⁻¹ • creationCoefficient F α ((M-m)-(i+1))) else 0)
                = F.coordinate α b • (((i+1:ℂ))⁻¹ •
                    (if i+1 ≤ M-m then creationVariable F α m * creationCoefficient F α ((M-i-1)-m) else 0)) := by
            intro m hm
            by_cases h : i+1 ≤ M-m
            · rw [if_pos h, if_pos h, mul_smul_comm, mul_smul_comm]
              congr 4; omega
            · rw [if_neg h, if_neg h, mul_zero, smul_zero, smul_zero]
          rw [Finset.sum_congr rfl hpt, ← Finset.smul_sum, ← Finset.smul_sum]
          have hstep1 : (∑ m ∈ Finset.range (M+1),
                if i+1 ≤ M-m then creationVariable F α m * creationCoefficient F α ((M-i-1)-m) else 0)
              = ∑ m ∈ Finset.range (M-i),
                if i+1 ≤ M-m then creationVariable F α m * creationCoefficient F α ((M-i-1)-m) else 0 := by
            refine (Finset.sum_subset
              (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) ?_).symm
            intro m _ hm'
            simp only [Finset.mem_range, not_lt] at hm'
            rw [if_neg (by omega)]
          have hstep2 : (∑ m ∈ Finset.range (M-i),
                if i+1 ≤ M-m then creationVariable F α m * creationCoefficient F α ((M-i-1)-m) else 0)
              = ∑ m ∈ Finset.range (M-i), creationVariable F α m * creationCoefficient F α ((M-i-1) - m) := by
            apply Finset.sum_congr rfl
            intro m hm; simp only [Finset.mem_range] at hm; rw [if_pos (by omega)]
          rw [hstep1, hstep2, creationCoefficient_recursion_sum F α (M - i)]
        rw [hS1, hS2, if_pos hiM, if_pos (show i+1 ≤ M+1 by omega),
          show M + 1 - (i+1) = M - i from by omega,
          ← MvPolynomial.smul_eq_C_mul (creationCoefficient F α (M - i)) (F.coordinate α b),
          ← MvPolynomial.smul_eq_C_mul _ (((M : ℂ) + 1)⁻¹)]
        simp only [smul_smul]
        rw [← add_smul, smul_smul]
        congr 1
        rw [Nat.cast_sub hiM]
        have hM1 : (M : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero M
        have hi1 : (i : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero i
        field_simp
        ring
      · rw [hS1, if_neg hiM]
        have hS2z : (∑ m ∈ Finset.range (M+1),
              creationVariable F α m * (if i+1 ≤ M-m then
                F.coordinate α b • (((i+1:ℂ))⁻¹ • creationCoefficient F α ((M-m)-(i+1))) else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro m hm
          simp only [Finset.mem_range] at hm
          rw [if_neg (by omega), mul_zero]
        rw [hS2z, add_zero, mul_zero, if_neg (show ¬ i + 1 ≤ M + 1 by omega)]




noncomputable def creationOperator (α : L.carrier) (N : ℕ) : End ℂ (HeisenbergN.FockN (rank L)) :=
  LinearMap.mulLeft ℂ (creationCoefficient F α N)

theorem creationOperator_vacuum (α : L.carrier) (N : ℕ) :
    creationOperator F α N (HeisenbergN.vacuumN (rank L)) = creationCoefficient F α N := by
  rw [creationOperator, LinearMap.mulLeft_apply, HeisenbergN.vacuumN, mul_one]




theorem directionOscillator_creation_contraction (α : L.carrier) (b : Fin (rank L)) (m N : ℕ) (hm : 1 ≤ m) :
    (HeisenbergN.oscN (rank L) 1 b (m : ℤ)).comp (creationOperator F α N)
      = (creationOperator F α N).comp (HeisenbergN.oscN (rank L) 1 b (m : ℤ))
        + (if m ≤ N then F.coordinate α b • creationOperator F α (N - m) else 0) := by
  refine LinearMap.ext fun q => ?_
  have hmpos : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have hidx : ((m : ℤ) - 1).toNat = m - 1 := by omega
  have hcast : ((m - 1 : ℕ) : ℂ) + 1 = (m : ℂ) := by rw [Nat.cast_sub hm]; push_cast; ring
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.1 hm
  simp only [LinearMap.comp_apply, LinearMap.add_apply, creationOperator, LinearMap.mulLeft_apply]
  rw [HeisenbergN.oscN_apply_pos (rank L) 1 b hmpos, HeisenbergN.oscN_apply_pos (rank L) 1 b hmpos,
    hidx, one_smul, one_smul, pderiv_mul, creationCoefficient_derivative F α (m - 1) b N, hcast]
  by_cases h : m ≤ N
  · rw [if_pos (by omega), if_pos h, LinearMap.smul_apply]
    simp only [LinearMap.mulLeft_apply, show N - (m - 1 + 1) = N - m from by omega,
      Int.cast_natCast, smul_mul_assoc, mul_smul_comm, smul_smul, smul_add]
    rw [show (m : ℂ) * (F.coordinate α b * (m : ℂ)⁻¹) = F.coordinate α b from by field_simp]
    abel
  · rw [if_neg (by omega), if_neg h, LinearMap.zero_apply, add_zero]
    simp only [zero_mul, zero_add, Int.cast_natCast, mul_smul_comm]




theorem frameOscillator_creation_contraction (α β : L.carrier) (m N : ℕ) (hm : 1 ≤ m) :
    (frameOscillator F β (m : ℤ)).comp (creationOperator F α N)
      = (creationOperator F α N).comp (frameOscillator F β (m : ℤ))
        + (if m ≤ N then ((L.form α β : ℤ) : ℂ) • creationOperator F α (N - m) else 0) := by
  rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, frameOscillator, Finset.sum_mul]
  have hb : ∀ b : Fin (rank L),
      (F.coordinate β b • HeisenbergN.oscN (rank L) 1 b (m : ℤ))
          * creationOperator F α N
        = F.coordinate β b •
            (creationOperator F α N * HeisenbergN.oscN (rank L) 1 b (m : ℤ))
          + F.coordinate β b •
            (if m ≤ N then F.coordinate α b • creationOperator F α (N - m) else 0) := by
    intro b
    rw [smul_mul_assoc, Module.End.mul_eq_comp, directionOscillator_creation_contraction F α b m N hm,
      ← Module.End.mul_eq_comp, smul_add]
  rw [Finset.sum_congr rfl (fun b _ => hb b), Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun b _ => (mul_smul_comm _ _ _).symm)
  · by_cases h : m ≤ N
    · simp only [if_pos h, smul_smul]
      rw [← Finset.sum_smul]
      congr 1
      rw [← F.pairing α β]
      exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)
    · simp only [if_neg h, smul_zero, Finset.sum_const_zero]




theorem frameOscillator_mem_grading (α : L.carrier) (n : ℤ) {d : ℤ}
    {p : HeisenbergN.FockN (rank L)} (hp : p ∈ HeisenbergN.gradingZN (rank L) d) :
    frameOscillator F α n p ∈ HeisenbergN.gradingZN (rank L) (d - n) := by
  rw [frameOscillator, LinearMap.coe_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ (fun b _ => ?_)
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  by_cases hd : 0 ≤ d
  · rw [HeisenbergN.gradingZN_of_nonneg hd] at hp
    have h := HeisenbergN.oscN_mem_gradingZN (rank L) 1 b n hp
    rwa [Int.toNat_of_nonneg hd] at h
  · rw [HeisenbergN.gradingZN_of_neg (by omega), Submodule.mem_bot] at hp
    rw [hp, map_zero]
    exact HeisenbergN.zero_mem_gradingZN (rank L) _




noncomputable def annihilationCoefficient (α : L.carrier) : ℕ → End ℂ (HeisenbergN.FockN (rank L))
  | 0 => LinearMap.id
  | (N+1) => ((N+1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N+1),
      (-(frameOscillator F α (m+1 : ℤ))).comp (annihilationCoefficient α (N - m))

theorem annihilationCoefficient_zero (α : L.carrier) : annihilationCoefficient F α 0 = LinearMap.id := by simp only [annihilationCoefficient]

theorem annihilationCoefficient_succ (α : L.carrier) (N : ℕ) :
    annihilationCoefficient F α (N+1) = ((N+1 : ℂ))⁻¹ • ∑ m ∈ Finset.range (N+1),
      (-(frameOscillator F α (m+1 : ℤ))).comp (annihilationCoefficient F α (N - m)) := by simp only [annihilationCoefficient]


theorem annihilationCoefficient_vacuum (α : L.carrier) (N : ℕ) :
    annihilationCoefficient F α N (HeisenbergN.vacuumN (rank L))
      = if N = 0 then HeisenbergN.vacuumN (rank L) else 0 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => simp [annihilationCoefficient_zero]
    | (M+1) =>
      rw [annihilationCoefficient_succ, LinearMap.smul_apply, LinearMap.sum_apply]
      have hz : ∀ m ∈ Finset.range (M+1),
          ((-(frameOscillator F α (m+1 : ℤ))).comp (annihilationCoefficient F α (M - m)))
            (HeisenbergN.vacuumN (rank L)) = 0 := by
        intro m hm
        rw [LinearMap.comp_apply, ih (M - m) (by simp at hm; omega)]
        split_ifs with h
        · rw [LinearMap.neg_apply, frameOscillator_vacuum F α (m+1 : ℤ) (by positivity), neg_zero]
        · rw [map_zero]
      rw [Finset.sum_eq_zero hz, smul_zero]; simp


theorem annihilationCoefficient_mem_gradingZN (α : L.carrier) (N : ℕ) {w : ℕ}
    {p : HeisenbergN.FockN (rank L)} (hp : p ∈ HeisenbergN.gradingWN (rank L) w) :
    annihilationCoefficient F α N p ∈ HeisenbergN.gradingZN (rank L) ((w : ℤ) - N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [annihilationCoefficient_zero, LinearMap.id_apply, Nat.cast_zero, sub_zero]
           exact HeisenbergN.mem_gradingZN_of_gradingWN hp
    | (M+1) =>
      rw [annihilationCoefficient_succ, LinearMap.smul_apply, LinearMap.sum_apply]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m hm => ?_)
      simp only [Finset.mem_range] at hm
      rw [LinearMap.comp_apply, LinearMap.neg_apply]
      refine Submodule.neg_mem _ ?_
      have hrec : annihilationCoefficient F α (M - m) p
          ∈ HeisenbergN.gradingZN (rank L) ((w : ℤ) - (M - m : ℕ)) := ih (M - m) (by omega)
      have h := frameOscillator_mem_grading F α ((m : ℤ) + 1) hrec
      have hgoal : (w : ℤ) - (M - m : ℕ) - ((m : ℤ) + 1) = (w : ℤ) - ((M + 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub (by omega : m ≤ M)]; push_cast; ring
      rwa [hgoal] at h


end VOA.Moonshine.ConwayNorton
