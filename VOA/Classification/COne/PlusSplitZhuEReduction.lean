import VOA.Classification.COne.PlusSplitEqualBottom
import VOA.Classification.COne.PlusSplitTwistedOscillators

/-! # A genuine cubic Zhu relation and all omega times E reductions

The existing charged certificate lies in O(V), so its descent is an identity
of the actual Zhu quotient, including its possible radical. It reduces
omega^3 E and closes all three omega-times-E-column obligations in the fixed
normal-form list. The remaining W/E products and other boundary powers are open.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusZhuNormalForms
open PlusUnitary PlusC2
variable (m : ℕ) (hm : 1 ≤ m)
@[reducible] local instance zhuERing : Ring (VOA.A (V2mPlus m hm)) := instRingA _
@[reducible] local instance zhuEAlgebra : Algebra ℂ (VOA.A (V2mPlus m hm)) := instAlgebraA _

theorem mk_zhuMul (u v : VP m hm) :
    VOA.mk (V2mPlus m hm) (zhuMul (V2mPlus m hm) u v) =
      VOA.mk (V2mPlus m hm) u * VOA.mk (V2mPlus m hm) v :=
  (Amul_mk (zhuRingData_holds _) u v).symm

/-- The cubic annihilator of E, on the quotient itself. -/
theorem omega_E_nested_relation (hm2 : 2 ≤ m) :
    let w := generator m hm 0
    let e := generator m hm 2
    let a : ℂ := (m : ℂ)/4
    let b : ℂ := 1/16
    let c : ℂ := 9/16
    w * (w * (w*e - c • e) - b • (w*e - c • e)) -
      a • (w * (w*e - c • e) - b • (w*e - c • e)) = 0 := by
  have hy : y3 m hm ∈ O (V2mPlus m hm) := by
    have h := (O (V2mPlus m hm)).smul_mem
      ((cα m ^ 3 - 2*cα m)⁻¹) (eRel_mem_O m hm)
    rwa [smul_smul, inv_mul_cancel₀ (cα_poly_ne_zero m hm hm2), one_smul] at h
  have hq : VOA.mk (V2mPlus m hm) (y3 m hm) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hy
  have he : generator m hm 2 = (2 : ℂ) • VOA.mk (V2mPlus m hm) (y0 m hm) := by
    change VOA.mk (V2mPlus m hm) (EP m hm) = _
    rw [EP_eq_y0, map_smul]
  simp only [y3, y2, y1, map_sub, map_smul, mk_zhuMul] at hq
  dsimp only
  rw [he]
  simp only [mul_smul_comm, ← smul_sub, smul_comm _ (2 : ℂ)]
  change (2 : ℂ) • _ = 0
  simpa only [smul_zero] using congrArg (fun x : VOA.A (V2mPlus m hm) => (2 : ℂ) • x) hq

/-- Explicit normal form for the highest omega multiple of E. -/
theorem omega_cubed_E (hm2 : 2 ≤ m) :
    generator m hm 0 ^ 3 * generator m hm 2 =
      ((m : ℂ)/4 + 1/16 + 9/16) • (generator m hm 0 ^ 2 * generator m hm 2) -
      ((m : ℂ)/4*(1/16) + (m : ℂ)/4*(9/16) + (1/16)*(9/16)) •
        (generator m hm 0 * generator m hm 2) +
      ((m : ℂ)/4*(1/16)*(9/16)) • generator m hm 2 := by
  have h := omega_E_nested_relation m hm hm2
  dsimp only at h
  have he : generator m hm 0 ^ 3 * generator m hm 2 -
      (((m : ℂ)/4 + 1/16 + 9/16) • (generator m hm 0 ^ 2 * generator m hm 2) -
      ((m : ℂ)/4*(1/16) + (m : ℂ)/4*(9/16) + (1/16)*(9/16)) •
        (generator m hm 0 * generator m hm 2) +
      ((m : ℂ)/4*(1/16)*(9/16)) • generator m hm 2) = 0 := by
    convert h using 1
    simp only [pow_succ, pow_zero, one_mul, mul_assoc, mul_sub, mul_smul_comm,
      smul_sub, smul_smul]
    module
  exact sub_eq_zero.mp he

theorem omega_mul_E_monomial_mem (hm2 : 2 ≤ m) (i : Fin 3) :
    generator m hm 0 * monomial m hm (.inr (.inr i)) ∈
      Submodule.span ℂ (Set.range (monomial m hm)) := by
  have hmem (j : Fin 3) : monomial m hm (.inr (.inr j)) ∈
      Submodule.span ℂ (Set.range (monomial m hm)) :=
    Submodule.subset_span ⟨_, rfl⟩
  fin_cases i
  · simpa [monomial] using hmem 1
  · simpa [monomial, pow_succ, mul_assoc] using hmem 2
  · change generator m hm 0 * (generator m hm 0 ^ 2 * generator m hm 2) ∈ _
    rw [← mul_assoc, ← pow_succ', omega_cubed_E m hm hm2]
    refine Submodule.add_mem _ (Submodule.sub_mem _
      (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)) (Submodule.smul_mem _ _ ?_)
    · exact hmem 2
    · simpa [monomial] using hmem 1
    · simpa [monomial] using hmem 0

end VOA.Classification.COne.PlusZhuNormalForms
