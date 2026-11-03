import VOA.DeligneAudit.DeligneFusionECalc

/-!
# Small rank-one current consequences for the m=2 contact source

These are direct vector identities. No rank-one fusion presentation,
finite-dimensionality, or polynomial initial-ideal assertion is assumed.
-/

namespace VOA.DeligneAudit.D4FusionContact.PolynomialRankOne

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {E H F : ℕ → Module.End ℂ V} {w : V}
variable (hEF : ∀ s k, E s * F k - F k * E s = H (s + k))
  (hHF : ∀ p k, H p * F k - F k * H p = (-2 : ℂ) • F (p + k))
  (hFF : ∀ i j, F i * F j = F j * F i)
  (hE : ∀ s, E s w = 0) (hH : ∀ p, 1 ≤ p → H p w = 0)

include hFF in
theorem F2_F0pow_zero (hF2 : F 2 w = 0) (n : ℕ) : F 2 ((F 0 ^ n) w) = 0 := by
  rw [← Module.End.mul_apply, (Commute.pow_right (hFF 2 0) n).eq,
    Module.End.mul_apply, hF2, map_zero]

include hFF in
theorem F2_F1_F0_zero (hF2 : F 2 w = 0) : F 2 (F 1 (F 0 w)) = 0 := by
  rw [← Module.End.mul_apply (F 2) (F 1), hFF 2 1, Module.End.mul_apply]
  have hz := F2_F0pow_zero hFF hF2 1
  simpa only [pow_one, hz, map_zero] using congrArg (F 1) hz

include hEF hHF hFF hE hH in
theorem first_derivative_of_nil (N : ℕ) (hN : 2 ≤ N) (hnil : (F 0 ^ N) w = 0) :
    F 1 ((F 0 ^ (N-2)) w) = 0 := by
  have hh := ECalc.E_F0pow hEF hHF hFF hE hH 1 (by omega) N
  rw [hnil, map_zero] at hh
  exact (smul_eq_zero.mp hh.symm).resolve_left (by
    apply neg_ne_zero.mpr
    exact_mod_cast Nat.mul_ne_zero (by omega : N ≠ 0) (by omega : N-1 ≠ 0))

include hHF hH in
theorem H1_F0 : H 1 (F 0 w) = (-2 : ℂ) • F 1 w := by
  have hh := congrArg (fun T : Module.End ℂ V => T w) (hHF 1 0)
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Nat.add_zero, hH 1 (by omega), map_zero, sub_zero] using hh

include hHF hFF hH in
theorem H1_F1_F0 (hF2 : F 2 w = 0) :
    H 1 (F 1 (F 0 w)) = (-2 : ℂ) • F 1 (F 1 w) := by
  have hh := congrArg (fun T : Module.End ℂ V => T (F 0 w)) (hHF 1 1)
  have hz : F 2 (F 0 w) = 0 := by simpa only [pow_one] using F2_F0pow_zero hFF hF2 1
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    H1_F0 hHF hH, map_smul, Nat.reduceAdd, hz, smul_zero] at hh
  exact sub_eq_zero.mp hh

include hHF hFF hH in
theorem square_one_of_pair (hF2 : F 2 w = 0) (hpair : F 1 (F 0 w) = 0) :
    F 1 (F 1 w) = 0 := by
  have hh := H1_F1_F0 hHF hFF hH hF2
  rw [hpair, map_zero] at hh
  exact (smul_eq_zero.mp hh.symm).resolve_left (by norm_num)

include hEF hHF hFF hE hH in
theorem second_derivative_of_five (hF2 : F 2 w = 0)
    (h31 : F 1 ((F 0 ^ 3) w) = 0) : F 1 (F 1 (F 0 w)) = 0 := by
  have hH2 : H 2 ((F 0 ^ 3) w) = 0 := by
    rw [ECalc.H_F0pow hHF hFF hH 2 (by omega) 3,
      F2_F0pow_zero hFF hF2, smul_zero]
  have hE3 : E 1 ((F 0 ^ 3) w) = (-6 : ℂ) • F 1 (F 0 w) := by
    simpa using ECalc.E_F0pow hEF hHF hFF hE hH 1 (by omega) 3
  have hh := congrArg (fun T : Module.End ℂ V => T ((F 0 ^ 3) w)) (hEF 1 1)
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Nat.reduceAdd] at hh
  rw [h31, map_zero, hH2, hE3, map_smul, zero_sub, neg_eq_zero] at hh
  exact (smul_eq_zero.mp hh).resolve_left (by norm_num)

include hHF hFF hH in
theorem cube_one_of_pair21 (hF2 : F 2 w = 0) (h21 : F 1 (F 1 (F 0 w)) = 0) :
    F 1 (F 1 (F 1 w)) = 0 := by
  have hh := congrArg (fun T : Module.End ℂ V => T (F 1 (F 0 w))) (hHF 1 1)
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Nat.reduceAdd, h21, map_zero, H1_F1_F0 hHF hFF hH hF2,
    F2_F1_F0_zero hFF hF2, smul_zero, map_smul, zero_sub, neg_eq_zero] at hh
  exact (smul_eq_zero.mp hh).resolve_left (by norm_num)

end
end VOA.DeligneAudit.D4FusionContact.PolynomialRankOne

#print axioms VOA.DeligneAudit.D4FusionContact.PolynomialRankOne.first_derivative_of_nil
#print axioms VOA.DeligneAudit.D4FusionContact.PolynomialRankOne.second_derivative_of_five
#print axioms VOA.DeligneAudit.D4FusionContact.PolynomialRankOne.cube_one_of_pair21
