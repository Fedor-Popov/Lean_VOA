import VOA.Classification.COne.OrbSglCwsDefs

/-!
# OrbSgl (5): soundness of the `termK` evaluation, and the finite commutator / skew formulas
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbSgl

open VOA VertexOperatorAlgebra VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational
  OrbC2g OrbC2h OrbC2c OrbC2e OrbC2f PlusC2 PlusC2Eval PlusUnitary

local notation "V8" => V2m 4 four_ge_one

/-! ## Generic finite formulas -/

section Generic

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V)

/-- Finite skew symmetry. -/
theorem skew_finite {u v : V} {p q n : ℤ} (hu : u ∈ W.grading p) (hv : v ∈ W.grading q)
    (B : ℕ) (hB : p + q ≤ n + B) :
    W.smul u n v = ∑ j ∈ Finset.range B,
      (((j.factorial : ℂ)⁻¹) * VOA.sgn (-n - 1 - j)) •
        (W.L (-1) ^ j) (W.smul v (n + j) u) := by
  have hY : ∀ j : ℕ, (W.Y v) (-n - 1 - j) u = W.smul v (n + j) u := by
    intro j
    rw [PreVertexAlgebra.smul_def, mode_apply]
    congr 1; ring
  rw [skew_mode, finsum_eq_finsetSum_of_support_subset _ (s := Finset.range B)]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [hY, T_eq_Lneg1, smul_smul]
  · intro j hj
    rw [Function.mem_support] at hj
    by_contra hc
    rw [Finset.coe_range, Set.mem_Iio, not_lt] at hc
    apply hj
    rw [hY, OrbC2f.smul_eq_zero_of_weights W hv hu (by omega), map_zero, smul_zero, smul_zero]

/-- Finite commutator. -/
theorem comm_finite {u a x : V} {p q : ℤ} (hu : u ∈ W.grading p) (ha : a ∈ W.grading q)
    (m n : ℤ) (B : ℕ) (hB : p + q ≤ B) :
    W.smul u m (W.smul a n x) = W.smul a n (W.smul u m x) +
      ∑ i ∈ Finset.range B, gBinom m i • W.smul (W.smul u i a) (m + n - i) x := by
  have h := congrArg (fun f : Module.End ℂ V => f x) (VHat.mode_commutator_finsum W u a m n)
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.range B)] at h
  · rw [LinearMap.sum_apply] at h
    simp only [LinearMap.smul_apply] at h
    have e : ∀ (b : V) (k : ℤ) (y : V), mode (W.Y b) k y = W.smul b k y := fun b k y => by
      rw [PreVertexAlgebra.smul_def]
    simp only [e] at h
    rw [← h]; abel
  · intro i hi
    rw [Function.mem_support] at hi
    by_contra hc
    rw [Finset.coe_range, Set.mem_Iio, not_lt] at hc
    apply hi
    rw [OrbC2f.smul_eq_zero_of_weights W hu ha (by omega), map_zero, mode_zero, smul_zero]

end Generic

/-! ## Soundness of the evaluators -/

theorem evaluate_iterFast (n : ℤ) (i : ℕ) (S : SectorVector) (x : VP 4 four_ge_one)
    (hS : evaluate S = (x : LatModuleGen (latP 4))) :
    evaluate (iterFast n i S) = (seedIterateTerm n i x : LatModuleGen (latP 4)) := by
  have hc : (-1 : ℂ)^i * gBinom (-2) i = (i : ℂ)+1 := by
    rw [gBinom_neg_two, ← mul_assoc, ← mul_pow]
    norm_num
    ring
  simp only [iterFast, evaluate_scaleVector, evaluate_append, evaluate_neutralS,
    evaluate_eS, hS, seedIterateTerm, Submodule.coe_smul,
    Submodule.coe_sub, V2mPlus_smul_coe, hc]
  norm_num only [Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Rat.cast_neg,
    neg_one_smul, zpow_neg, neg_neg, even_two, Even.neg_pow, one_pow, inv_one, one_smul]
  simp only [show (J 4 four_ge_one : LatModuleGen (latP 4)) = ls 4 JR from hasN_J _ _]
  module

theorem evaluate_uL (k : ℕ) (S : SectorVector) (x : VP 4 four_ge_one)
    (hx : x ∈ (V2mPlus 4 four_ge_one).grading 4)
    (hS : evaluate S = (x : LatModuleGen (latP 4))) :
    evaluate (uL k S) = (V8).smul (weightNine : LatModuleGen (latP 4)) k x := by
  rw [uL, evaluate_compact, evaluate_flatMap_range]
  simp only [evaluate_iterFast _ _ S x hS]
  rw [← V2mPlus_smul_coe, weightNine_smul_finite hx (k : ℤ) 9 (by norm_num) (by omega),
    Submodule.coe_sum]

theorem L_neg_one_eq (y : LatModuleGen (latP 4)) :
    (V8).L (-1) y = (V8).smul (ls 4 omR) 0 y := by
  rw [← omega_V2m 4 four_ge_one, VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def]
  norm_num

theorem evaluate_Tpow (S : SectorVector) : ∀ j : ℕ,
    evaluate (Tpow j S) = ((V8).L (-1) ^ j) (evaluate S)
  | 0 => rfl
  | j+1 => by
    rw [Tpow, evaluate_compact, evaluate_neutralBoundS, evaluate_Tpow S j, pow_succ',
      Module.End.mul_apply, L_neg_one_eq]

theorem sgnQ_cast (n : ℤ) : ((sgnQ n : ℚ) : ℂ) = VOA.sgn n := by
  unfold sgnQ VOA.sgn
  by_cases h : n % 2 = 0
  · rw [if_pos h, if_pos (Int.even_iff.mpr h)]; norm_num
  · rw [if_neg h, if_neg (fun he => h (Int.even_iff.mp he))]; norm_num

/-- The vector `a` (`J` or `E`) and its left action. -/
def aVec (isJ : Bool) : VP 4 four_ge_one := if isJ then J 4 four_ge_one else EP 4 four_ge_one

theorem aVec_mem (isJ : Bool) : aVec isJ ∈ (V2mPlus 4 four_ge_one).grading 4 := by
  cases isJ
  · exact EP_mem_grading 4 four_ge_one
  · exact J_mem_grading_four 4 four_ge_one

theorem aVec_mem' (isJ : Bool) :
    (aVec isJ : LatModuleGen (latP 4)) ∈ (V8).grading 4 := aVec_mem isJ

theorem evaluate_aLeft (isJ : Bool) (n : ℤ) (S : SectorVector) :
    evaluate (aLeft isJ n S) = (V8).smul (aVec isJ : LatModuleGen (latP 4)) n (evaluate S) := by
  cases isJ
  · simp [aLeft, evaluate_eS]; rfl
  · simp only [aLeft, if_true, evaluate_neutralS]
    change _ = (V8).smul (J 4 four_ge_one : LatModuleGen (latP 4)) n (evaluate S)
    rw [show (J 4 four_ge_one : LatModuleGen (latP 4)) = ls 4 JR from hasN_J _ _]

/-- The value of `termK`. -/
theorem evaluate_termK (isJ : Bool) (aV : SectorVector)
    (hS : evaluate aV = (aVec isJ : LatModuleGen (latP 4))) (k : ℕ) :
    evaluate (termK isJ aV k) = ((Nat.choose 15 k : ℕ) : ℂ) •
      (V8).smul ((V8).smul (weightNine : LatModuleGen (latP 4)) k (aVec isJ)) (6 - k)
        (aVec isJ : LatModuleGen (latP 4)) := by
  have hy := evaluate_uL k aV (aVec isJ) (aVec_mem isJ) hS
  have hnine : (weightNine : LatModuleGen (latP 4)) ∈ (V8).grading 9 := weightNine_mem_grading
  have hyg : (V8).smul (weightNine : LatModuleGen (latP 4)) k (aVec isJ) ∈ (V8).grading (12 - k) := by
    have := (V8).smul_mem_grading hnine (aVec_mem' isJ) (k : ℤ)
    rwa [show (9 : ℤ) + 4 - k - 1 = 12 - k by ring] at this
  rw [skew_finite (V8) hyg (aVec_mem' isJ) 10 (by omega), Finset.smul_sum]
  simp only [termK, evaluate_compact, evaluate_flatMap_range, evaluate_scaleVector,
    evaluate_Tpow, evaluate_aLeft, hy]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]
  congr 1
  push_cast
  rw [sgnQ_cast]
  ring_nf

end VOA.Classification.COne.OrbSgl
