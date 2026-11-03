import VOA.Classification.COne.PlusSplitZhuMixed
import VOA.Modules.ZhuVermaAnArchDLM3Zero

/-! Commutativity of the genuine rank-one plus Zhu algebra. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusZhuMixed
open PlusUnitary PlusC2 PlusC2Eval VOA.SparseRational VertexOperatorAlgebra

def bracketY : RawPoly ℕ := (List.range 4).flatMap fun i =>
  scaleR (Nat.choose 3 i : ℚ) (polyActWC WR (-(i : ℤ) - 1) Y0)
def bracketCertificate : List CEntry :=
[
  ([((-4 / 1 : ℚ), 1), ((2 / 1 : ℚ), 3)], [], [], 0),
  ([((20 / 1 : ℚ), 2)], [], [1], 0),
  ([((-80 / 1 : ℚ), 0), ((60 / 1 : ℚ), 2)], [], [2], 0),
  ([((-40 / 1 : ℚ), 1)], [], [1, 1], 0),
  ([((-160 / 1 : ℚ), 0), ((40 / 1 : ℚ), 2)], [], [3], 0),
  ([((-120 / 1 : ℚ), 1)], [], [2, 1], 0),
  ([((-80 / 1 : ℚ), 0)], [], [1, 1, 1], 0),
  ([((-80 / 1 : ℚ), 0)], [], [4], 0),
  ([((-80 / 1 : ℚ), 1)], [], [3, 1], 0),
  ([((-80 / 1 : ℚ), 0)], [], [2, 1, 1], 0),
  ([((20 / 1 : ℚ), 1)], [0, 0], [], 0),
  ([((-40 / 1 : ℚ), 1)], [0, 0], [], 1),
  ([((80 / 1 : ℚ), 0)], [0, 0], [1], 1),
  ([((40 / 1 : ℚ), 1)], [0, 0], [1, 1], 0),
  ([((40 / 1 : ℚ), 0)], [0, 0], [2], 0)
]

theorem bracketCertificate_even : ∀ t ∈ bracketCertificate, Even t.2.1.length := by decide
set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
-- Kernel evaluation of the finite rational certificate needs this local budget.
theorem bracketCertificate_check :
    normR (certC bracketCertificate) = normR (cmulR prefC bracketY) := by
  decide +kernel

variable (m : ℕ) (hm : 1 ≤ m)

def bracketState : VP m hm := ∑ i ∈ Finset.range 4,
  (Nat.choose 3 i : ℂ) • (V2mPlus m hm).smul (WP m hm) (i : ℤ) (y0 m hm)

theorem hasC_bracketState : HasC m hm (bracketState m hm) bracketY := by
  apply hasC_sum_range
  intro i
  have h := hasC_smul m hm (hasC_smul_left m hm (WP_coe m hm)
    (hasC_stP m hm Y0) (i : ℤ)) (Nat.choose 3 i : ℚ)
  simpa using h

theorem bracketState_mem_O (hm2 : 2 ≤ m) : bracketState m hm ∈ O (V2mPlus m hm) := by
  obtain ⟨y, hy, hyC⟩ := certC_mem m hm bracketCertificate bracketCertificate_even
  have he := hasC_of_normR_eq m hm hyC bracketCertificate_check
  have ht := hasC_cmulR_exact m hm (hasC_bracketState m hm) prefC
  have heq : (cα m ^ 3 - 2 * cα m) • bracketState m hm = y := by
    convert ht.trans he.symm using 1
    simp [scalarC, prefC, sub_eq_add_neg]
  have h := (O (V2mPlus m hm)).smul_mem ((cα m ^ 3 - 2 * cα m)⁻¹) (heq.symm ▸ hy)
  simpa only [smul_smul, inv_mul_cancel₀ (cα_poly_ne_zero m hm hm2), one_smul] using h

/-- Rewrite the finite commutator residue; no module/top evaluation is used. -/
theorem resFull_three (u v : VP m hm) :
    resFull (V2mPlus m hm) 3 0 u v =
      ∑ i ∈ Finset.range 4, (Nat.choose 3 i : ℂ) • (V2mPlus m hm).smul u (i : ℤ) v := by
  have hsub : (Function.support fun i : ℕ =>
      cbz 3 (i : ℤ) • (V2mPlus m hm).smul u (i : ℤ) v) ⊆ ↑(Finset.range 4) := by
    intro i hi
    rw [Function.mem_support] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hh
    exact hi (by rw [cbz_lt (by norm_num) (by omega), zero_smul])
  have hn := finsum_nat_to_int
    (fun i : ℕ => cbz 3 (i : ℤ) • (V2mPlus m hm).smul u (i : ℤ) v)
    (fun i : ℤ => cbz 3 i • (V2mPlus m hm).smul u i v)
    (fun i hi => by dsimp only; rw [cbz_apply_neg _ hi, zero_smul]) (fun _ => rfl)
  rw [resFull]
  simp only [add_zero]
  rw [← hn, finsum_eq_sum_of_support_subset _ hsub]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, cbz_natCast_eq_choose (by
    have := Finset.mem_range.mp hi; omega)]

end VOA.Classification.COne.PlusZhuMixed

namespace VOA.Classification.COne.PlusZhuNormalForms
open PlusUnitary PlusZhuMixed
variable (m : ℕ) (hm : 1 ≤ m)
@[reducible] local instance commRing : Ring (VOA.A (V2mPlus m hm)) := instRingA _
@[reducible] local instance commAlgebra : Algebra ℂ (VOA.A (V2mPlus m hm)) := instAlgebraA _

theorem W_commute_E (hm2 : 2 ≤ m) : Commute (generator m hm 1) (generator m hm 2) := by
  have hb : resFull (V2mPlus m hm) 3 0 (WP m hm) (EP m hm) ∈ O (V2mPlus m hm) := by
    rw [resFull_three, EP_eq_y0]
    simp only [PreVertexAlgebra.smul_smul_right, smul_comm _ (2 : ℂ), ← Finset.smul_sum]
    exact (O _).smul_mem 2 (bracketState_mem_O m hm hm2)
  have hc := zhu_comm_mod_O (V2mPlus m hm) (WP_mem_grading m hm) (EP_mem_grading m hm)
  have hd : zhuMul (V2mPlus m hm) (WP m hm) (EP m hm) -
      zhuMul (V2mPlus m hm) (EP m hm) (WP m hm) ∈ O (V2mPlus m hm) := by
    simpa using (O _).add_mem hc hb
  have hq := (Submodule.Quotient.mk_eq_zero _).mpr hd
  change VOA.mk (V2mPlus m hm) _ = 0 at hq
  rw [map_sub, mk_zhuMul, mk_zhuMul, sub_eq_zero] at hq
  exact hq

/-- All E-times-W-column obligations, including the shorter lists. -/
theorem E_mul_W_monomial_mem (hm2 : 2 ≤ m) (i : Fin (wCount m)) :
    generator m hm 2 * monomial m hm (.inr (.inl i)) ∈
      Submodule.span ℂ (Set.range (monomial m hm)) := by
  change generator m hm 2 * (generator m hm 0 ^ i.val * generator m hm 1) ∈ _
  rw [← mul_assoc, ((omega_commute m hm (generator m hm 2)).pow_left i.val).eq.symm,
    mul_assoc, (W_commute_E m hm hm2).eq.symm, ← mul_assoc,
    ((omega_commute m hm (generator m hm 1)).pow_left i.val).eq, mul_assoc]
  exact W_mul_E_monomial_mem m hm hm2 ⟨i.val, lt_of_lt_of_le i.isLt (wCount_le m)⟩

/-- Commutativity of the entire Zhu quotient, including any radical. -/
theorem zhu_mul_comm (hm2 : 2 ≤ m) (x y : VOA.A (V2mPlus m hm)) : x * y = y * x := by
  have hgen := V2mPlus_zhu_adjoin_generators m hm hm2
  change Algebra.adjoin ℂ (Set.range (generator m hm)) = ⊤ at hgen
  have hmem (z : VOA.A (V2mPlus m hm)) :
      z ∈ Algebra.adjoin ℂ (Set.range (generator m hm)) := by rw [hgen]; trivial
  have hgg (i j : Fin 3) : Commute (generator m hm i) (generator m hm j) := by
    fin_cases i <;> fin_cases j
    all_goals first
      | exact omega_commute m hm _
      | exact (omega_commute m hm _).symm
      | exact W_commute_E m hm hm2
      | exact (W_commute_E m hm hm2).symm
      | exact Commute.refl _
  have hg (i : Fin 3) (z : VOA.A (V2mPlus m hm)) : Commute (generator m hm i) z := by
    apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute (hmem z)
    rintro b ⟨j, rfl⟩
    exact hgg i j
  apply (Algebra.commute_of_mem_adjoin_of_forall_mem_commute (hmem y) ?_).eq
  rintro b ⟨i, rfl⟩
  exact (hg i x).symm

end VOA.Classification.COne.PlusZhuNormalForms
