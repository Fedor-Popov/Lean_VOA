import VOA.Classification.COne.PlusSplitZhuMixedCertificate

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusZhuNormalForms
open PlusUnitary PlusZhuMixed PlusC2
variable (m : ℕ) (hm : 1 ≤ m)
@[reducible] local instance mixedRing : Ring (VOA.A (V2mPlus m hm)) := instRingA _
@[reducible] local instance mixedAlgebra : Algebra ℂ (VOA.A (V2mPlus m hm)) := instAlgebraA _

/-- Denominator-cleared Dong--Nagatomo mixed relation in the actual quotient. -/
theorem W_E_relation (hm2 : 2 ≤ m) :
    (((4 * (m : ℂ) - 1) * (4 * m - 9)) : ℂ) •
      (generator m hm 1 * generator m hm 2) =
    (60 - 160 * (m : ℂ)) • (generator m hm 0 ^ 2 * generator m hm 2) +
    (72 * (m : ℂ)^2 - 80 * m + 3) • (generator m hm 0 * generator m hm 2) -
    (15/4 * (m : ℂ) * (m - 1)) • generator m hm 2 := by
  have hq : VOA.mk (V2mPlus m hm) (mixedState m hm) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (mixedState_mem_O m hm hm2)
  simp only [mixedState, map_add, map_smul, mk_zhuMul] at hq
  change scalarC (cα m) dC • (generator m hm 1 * VOA.mk (V2mPlus m hm) (y0 m hm)) +
    scalarC (cα m) aC • (generator m hm 0 * (generator m hm 0 * VOA.mk (V2mPlus m hm) (y0 m hm))) +
    scalarC (cα m) bC • (generator m hm 0 * VOA.mk (V2mPlus m hm) (y0 m hm)) +
    scalarC (cα m) cC • VOA.mk (V2mPlus m hm) (y0 m hm) = 0 at hq
  have he : generator m hm 2 = (2 : ℂ) • VOA.mk (V2mPlus m hm) (y0 m hm) := by
    change VOA.mk (V2mPlus m hm) (EP m hm) = _
    rw [EP_eq_y0, map_smul]
  have hc2 : cα m ^ 2 = 2 * (m : ℂ) := by
    simpa only [pow_two] using cα_sq m hm
  have hc4 : cα m ^ 4 = 4 * (m : ℂ)^2 := by
    calc cα m ^ 4 = (cα m ^ 2)^2 := by ring
         _ = 4 * (m : ℂ)^2 := by rw [hc2]; ring
  simp only [scalarC, dC, aC, bC, cC, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, pow_zero, mul_one, add_zero] at hq
  norm_num only [Rat.cast_ofNat, Rat.cast_neg, Rat.cast_div] at hq
  rw [hc4, hc2] at hq
  apply sub_eq_zero.mp
  rw [he]
  have h2 := congrArg (fun z : VOA.A (V2mPlus m hm) => (2 : ℂ) • z) hq
  simp only [smul_zero] at h2
  convert h2 using 1
  simp only [pow_two, mul_assoc, mul_smul_comm, smul_add, smul_smul]
  module

/-- The mixed relation's denominator never vanishes at an integer m ≥ 2. -/
theorem mixed_denominator_ne_zero (hm2 : 2 ≤ m) :
    (4 * (m : ℂ) - 1) * (4 * m - 9) ≠ 0 := by
  apply mul_ne_zero
  · intro h
    have hz : (4 * (m : ℤ) - 1) = 0 := by exact_mod_cast h
    omega
  · intro h
    have hz : (4 * (m : ℤ) - 9) = 0 := by exact_mod_cast h
    omega

/-- Explicit reduction of W E to E, omega E, and omega² E. -/
theorem W_mul_E (hm2 : 2 ≤ m) :
    generator m hm 1 * generator m hm 2 =
    ((4 * (m : ℂ) - 1) * (4 * m - 9))⁻¹ •
      ((60 - 160 * (m : ℂ)) • (generator m hm 0 ^ 2 * generator m hm 2) +
       (72 * (m : ℂ)^2 - 80 * m + 3) • (generator m hm 0 * generator m hm 2) -
       (15/4 * (m : ℂ) * (m - 1)) • generator m hm 2) := by
  rw [← W_E_relation m hm hm2, smul_smul,
    inv_mul_cancel₀ (mixed_denominator_ne_zero m hm2), one_smul]

/-- All W-times-E-column obligations in the original normal-form list. -/
theorem W_mul_E_monomial_mem (hm2 : 2 ≤ m) (i : Fin 3) :
    generator m hm 1 * monomial m hm (.inr (.inr i)) ∈
      Submodule.span ℂ (Set.range (monomial m hm)) := by
  change generator m hm 1 * (generator m hm 0 ^ i.val * generator m hm 2) ∈ _
  rw [← mul_assoc, ((omega_commute m hm (generator m hm 1)).pow_left i.val).eq.symm,
    mul_assoc, W_mul_E m hm hm2]
  simp only [mul_smul_comm, mul_add, mul_sub, ← mul_assoc, ← pow_add, ← pow_succ]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (omega_power_E_mem m hm hm2 _))
    (Submodule.smul_mem _ _ (omega_power_E_mem m hm hm2 _)))
    (Submodule.smul_mem _ _ (omega_power_E_mem m hm hm2 _)))

end VOA.Classification.COne.PlusZhuNormalForms
