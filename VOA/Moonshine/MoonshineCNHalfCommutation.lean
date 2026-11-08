import VOA.Moonshine.MoonshineCNChargedFields

/-!
# Complex-frame lattice fields: HalfCommutation

Structural adaptation of `LatticeGenLocality`, `LatticeGenSameSign`.
The real positive frame is replaced by `ComplexLatticeFrame`; every contraction
uses its proved bilinear pairing. All coefficient rearrangements retain their
finite-support hypotheses. This module introduces no positivity assumption.
-/

set_option maxHeartbeats 1200000
set_option linter.style.longLine false

namespace VOA.Moonshine.ConwayNorton

open scoped BigOperators TensorProduct
open Module (End)
open IntegralLattice HeisenbergN LatGen


variable {L : IntegralLattice} (F : ComplexLatticeFrame L)

theorem creationField_comm (α β : L.carrier) (a b : ℤ) :
    (creationField F α a).comp (creationField F β b)
      = (creationField F β b).comp (creationField F α a) := by
  refine LinearMap.ext fun p => ?_
  simp only [LinearMap.comp_apply]
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · rw [creationField_apply, if_pos ha, creationField_apply, if_pos hb, creationOperator, creationOperator,
        LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply,
        LinearMap.mulLeft_apply, mul_left_comm]
    · rw [creationField_neg F β (show b < 0 by omega)]; simp
  · rw [creationField_neg F α (show a < 0 by omega)]; simp


theorem positive_frameOscillators_commute (α β : L.carrier) {m n : ℤ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) : Commute (frameOscillator F α m) (frameOscillator F β n) := by
  have h := frameOscillator_commutator F α β m n
  rw [if_neg (by omega : ¬ m + n = 0), zero_smul, sub_eq_zero] at h
  exact h


theorem annihilationCoefficient_commute_charge (α β : L.carrier) (N j : ℕ) :
    Commute (annihilationCoefficient F α N) (frameOscillator F β ((j : ℤ) + 1)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [annihilationCoefficient_zero]; exact Commute.one_left _
    | (M + 1) =>
      rw [annihilationCoefficient_succ]
      refine Commute.smul_left ?_ _
      refine Commute.sum_left _ _ _ (fun m hm => ?_)
      refine Commute.mul_left ?_ (ih (M - m) (by simp only [Finset.mem_range] at hm; omega))
      exact (positive_frameOscillators_commute F α β (by omega) (by omega)).neg_left


theorem annihilationCoefficient_commute (α β : L.carrier) (M N : ℕ) :
    Commute (annihilationCoefficient F α M) (annihilationCoefficient F β N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [annihilationCoefficient_zero]; exact Commute.one_right _
    | (K + 1) =>
      rw [annihilationCoefficient_succ]
      refine Commute.smul_right ?_ _
      refine Commute.sum_right _ _ _ (fun m hm => ?_)
      refine Commute.mul_right ?_ (ih (K - m) (by simp only [Finset.mem_range] at hm; omega))
      exact (annihilationCoefficient_commute_charge F α β M m).neg_right


theorem annihilationField_comm (α β : L.carrier) (a b : ℤ) :
    (annihilationField F α a).comp (annihilationField F β b)
      = (annihilationField F β b).comp (annihilationField F α a) := by
  by_cases ha : a ≤ 0
  · by_cases hb : b ≤ 0
    · rw [annihilationField_nonpos F α ha, annihilationField_nonpos F β hb]
      exact (annihilationCoefficient_commute F α β _ _).eq
    · refine LinearMap.ext fun p => ?_
      simp only [LinearMap.comp_apply, annihilationField_apply, if_neg hb, LinearMap.zero_apply,
        map_zero]
  · refine LinearMap.ext fun p => ?_
    simp only [LinearMap.comp_apply, annihilationField_apply, if_neg ha, LinearMap.zero_apply,
      map_zero]


noncomputable def normalOrderedFourField (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) : FockN (rank L) :=
  ∑ᶠ pq : ℤ × ℤ, creationField F α pq.1 (creationField F β pq.2
    (annihilationField F α (C - pq.1) (annihilationField F β (D - pq.2) x)))


theorem normalOrderedFourField_symm (α β : L.carrier) (C D : ℤ) (x : FockN (rank L)) :
    normalOrderedFourField F α β C D x = normalOrderedFourField F β α D C x := by
  rw [normalOrderedFourField, normalOrderedFourField, ← finsum_comp_equiv (Equiv.prodComm ℤ ℤ)
    (f := fun pq : ℤ × ℤ => creationField F β pq.1 (creationField F α pq.2
      (annihilationField F β (D - pq.1) (annihilationField F α (C - pq.2) x))))]
  refine finsum_congr fun pq => ?_
  obtain ⟨p, q⟩ := pq
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
  have hE : ∀ Y, creationField F α p (creationField F β q Y)
      = creationField F β q (creationField F α p Y) := fun Y => by
    have := DFunLike.congr_fun (creationField_comm F α β p q) Y
    simpa [LinearMap.comp_apply] using this
  have hP : ∀ x', annihilationField F α (C - p) (annihilationField F β (D - q) x')
      = annihilationField F β (D - q) (annihilationField F α (C - p) x') := fun x' => by
    have := DFunLike.congr_fun (annihilationField_comm F α β (C - p) (D - q)) x'
    simpa [LinearMap.comp_apply] using this
  rw [hE, hP]


noncomputable def annihilationCoefficientZ (α : L.carrier) (N : ℤ) : End ℂ (FockN (rank L)) :=
  if 0 ≤ N then annihilationCoefficient F α N.toNat else 0


theorem annihilationCoefficientZ_neg (α : L.carrier) {N : ℤ} (h : N < 0) : annihilationCoefficientZ F α N = 0 := by
  rw [annihilationCoefficientZ, if_neg (by omega)]


theorem annihilationCoefficientZ_nonneg (α : L.carrier) {N : ℤ} (h : 0 ≤ N) :
    annihilationCoefficientZ F α N = annihilationCoefficient F α N.toNat := by rw [annihilationCoefficientZ, if_pos h]


theorem annihilationCoefficientZ_zero (α : L.carrier) : annihilationCoefficientZ F α 0 = LinearMap.id := by
  rw [annihilationCoefficientZ_nonneg F α le_rfl]; simp [annihilationCoefficient_zero]


theorem annihilationField_eq_annihilationCoefficientZ (α : L.carrier) (a : ℤ) :
    annihilationField F α a = annihilationCoefficientZ F α (-a) := by
  rw [annihilationField_apply, annihilationCoefficientZ]
  by_cases h : a ≤ 0
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]


theorem annihilationCoefficientZ_recursion (α : L.carrier) (N : ℤ) (hN : 1 ≤ N) :
    annihilationCoefficientZ F α N = (N : ℂ)⁻¹ • ∑ m ∈ Finset.range N.toNat,
      (-(frameOscillator F α ((m : ℤ) + 1))).comp (annihilationCoefficientZ F α (N - 1 - m)) := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, N.toNat = K + 1 := ⟨N.toNat - 1, by omega⟩
  have hNK : N = (K : ℤ) + 1 := by omega
  rw [annihilationCoefficientZ_nonneg F α (by omega), hK, annihilationCoefficient_succ, hNK]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_range] at hm
  congr 2
  rw [annihilationCoefficientZ_nonneg F α (by omega)]
  congr 1
  omega


theorem annihilationCoefficientZ_sum_reassembly (α : L.carrier) (M : ℤ) (K : ℕ) (hK : M.toNat ≤ K) :
    ∑ m ∈ Finset.range K, (-(frameOscillator F α ((m : ℤ) + 1))).comp (annihilationCoefficientZ F α (M - 1 - m))
      = (M : ℂ) • annihilationCoefficientZ F α M := by
  by_cases hM : 1 ≤ M
  · have hsplit : ∑ m ∈ Finset.range K,
          (-(frameOscillator F α ((m : ℤ) + 1))).comp (annihilationCoefficientZ F α (M - 1 - m))
        = ∑ m ∈ Finset.range M.toNat,
          (-(frameOscillator F α ((m : ℤ) + 1))).comp (annihilationCoefficientZ F α (M - 1 - m)) := by
      refine (Finset.sum_subset (s₁ := Finset.range M.toNat) (s₂ := Finset.range K)
        (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) ?_).symm
      intro m _ hm
      simp only [Finset.mem_range, not_lt] at hm
      rw [annihilationCoefficientZ_neg F α (by omega), LinearMap.comp_zero]
    rw [hsplit, annihilationCoefficientZ_recursion F α M hM, smul_smul, mul_inv_cancel₀ (by
      simp only [ne_eq]; exact_mod_cast (by omega : (M : ℤ) ≠ 0)), one_smul]
  · have hsum0 : ∑ m ∈ Finset.range K,
        (-(frameOscillator F α ((m : ℤ) + 1))).comp (annihilationCoefficientZ F α (M - 1 - m)) = 0 := by
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [annihilationCoefficientZ_neg F α (by omega), LinearMap.comp_zero]
    rw [hsum0]
    rcases lt_or_eq_of_le (by omega : M ≤ 0) with hlt | heq
    · rw [annihilationCoefficientZ_neg F α hlt, smul_zero]
    · rw [heq]; simp


theorem frameOscillator_creationField_contraction (α β : L.carrier) (m : ℕ) (b : ℤ) :
    (frameOscillator F β ((m : ℤ) + 1)).comp (creationField F α b)
      = (creationField F α b).comp (frameOscillator F β ((m : ℤ) + 1))
        + ((L.form α β : ℤ) : ℂ) • creationField F α (b - ((m : ℤ) + 1)) := by
  have hmode : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
  by_cases hb : 0 ≤ b
  · rw [creationField_apply, if_pos hb, hmode,
      frameOscillator_creation_contraction F α β (m + 1) b.toNat (by omega)]
    congr 1
    by_cases hle : m + 1 ≤ b.toNat
    · rw [if_pos hle, creationField_apply, if_pos (by omega : (0 : ℤ) ≤ b - ((m + 1 : ℕ) : ℤ))]
      congr 2
      omega
    · rw [if_neg hle, creationField_apply,
        if_neg (by omega : ¬ (0 : ℤ) ≤ b - ((m + 1 : ℕ) : ℤ)), smul_zero]
  · rw [creationField_neg F α (by omega : b < 0), LinearMap.comp_zero, LinearMap.zero_comp,
      creationField_neg F α (by omega : b - ((m : ℤ) + 1) < 0), smul_zero, zero_add]


theorem frameOscillator_creationField_reorder (α β : L.carrier) (m : ℕ) (b : ℤ)
    (X : End ℂ (FockN (rank L))) :
    (-(frameOscillator F β ((m : ℤ) + 1))).comp ((creationField F α b).comp X)
      = (creationField F α b).comp ((-(frameOscillator F β ((m : ℤ) + 1))).comp X)
        - ((L.form α β : ℤ) : ℂ) • ((creationField F α (b - ((m : ℤ) + 1))).comp X) := by
  rw [← LinearMap.comp_assoc, LinearMap.neg_comp,
    frameOscillator_creationField_contraction F α β m b]
  simp only [LinearMap.neg_comp, LinearMap.add_comp, LinearMap.smul_comp, LinearMap.comp_assoc,
    LinearMap.comp_neg]
  abel


end VOA.Moonshine.ConwayNorton
