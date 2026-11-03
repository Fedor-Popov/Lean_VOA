import VOA.Classification.COne.OrbSglCwsSound

/-!
# OrbSgl (5b): kernel-friendly two-stage evaluation of `C(15,k) (u₍ₖ₎a)₍₆₋ₖ₎a`

The iterate expansion of `u₍ₖ₎a` (`uL`) creates large intermediate states for small `k`; the
kernel cannot afford it.  Here both stages use skew symmetry, so every evaluator call is an
`a`-left action (`a ∈ {J, E}`) on a state of weight `≤ 12`, followed by `L(-1)` steps:

* stage 1: `u₍ₖ₎a = Σ_{i<13-k} (i!)⁻¹ sgn(-k-1-i) L(-1)ⁱ a₍ₖ₊ᵢ₎u`  (`uTerm`);
* stage 2: `(u₍ₖ₎a)₍₆₋ₖ₎a = Σ_{j<10} (j!)⁻¹ sgn(k-7-j) L(-1)ʲ a₍₆₋ₖ₊ⱼ₎(u₍ₖ₎a)`  (`vTerm`).

Each call is certified separately against precomputed data (`OrbSglSk*` files).
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbSgl

open VOA VertexOperatorAlgebra VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational
  OrbC2g OrbC2h OrbC2c OrbC2e OrbC2f PlusC2 PlusC2Eval PlusUnitary

local notation "V8" => V2m 4 four_ge_one

/-- Stage-1 term `L(-1)ⁱ a₍ₖ₊ᵢ₎ u`. -/
def uTerm (isJ : Bool) (k i : ℕ) : SectorVector := Tpow i (aLeft isJ ((k : ℤ) + i) nineData)

def uCoef (k i : ℕ) : ℚ := (1 : ℚ) / (Nat.factorial i) * sgnQ (-(k : ℤ) - 1 - i)

/-- Stage-1 assembly from data. -/
def uSum (k : ℕ) (P : ℕ → SectorVector) : SectorVector :=
  (List.range (13 - k)).flatMap fun i => scaleVector (uCoef k i) (P i)

/-- Stage-2 term `L(-1)ʲ a₍₆₋ₖ₊ⱼ₎ Y`. -/
def vTerm (isJ : Bool) (Y : SectorVector) (k j : ℕ) : SectorVector :=
  Tpow j (aLeft isJ (6 - (k : ℤ) + j) Y)

def vCoef (k j : ℕ) : ℚ :=
  (Nat.choose 15 k : ℚ) / (Nat.factorial j) * sgnQ (-(6 - (k : ℤ)) - 1 - j)

/-- Stage-2 assembly from data. -/
def vSum (k : ℕ) (Q : ℕ → SectorVector) : SectorVector :=
  (List.range 10).flatMap fun j => scaleVector (vCoef k j) (Q j)

theorem evaluate_uTerm (isJ : Bool) (k i : ℕ) :
    evaluate (uTerm isJ k i) = ((V8).L (-1) ^ i)
      ((V8).smul (aVec isJ : LatModuleGen (latP 4)) ((k : ℤ) + i) (weightNine : LatModuleGen (latP 4))) := by
  rw [uTerm, evaluate_Tpow, evaluate_aLeft, nine_value]

theorem evaluate_vTerm (isJ : Bool) (Y : SectorVector) (k j : ℕ) :
    evaluate (vTerm isJ Y k j) = ((V8).L (-1) ^ j)
      ((V8).smul (aVec isJ : LatModuleGen (latP 4)) (6 - (k : ℤ) + j) (evaluate Y)) := by
  rw [vTerm, evaluate_Tpow, evaluate_aLeft]

/-- Stage 1: certified data `P i` for the terms give `u₍ₖ₎a`. -/
theorem evaluate_uSum (isJ : Bool) (k : ℕ) (hk : k ≤ 12) (P : ℕ → SectorVector)
    (hP : ∀ i < 13 - k, evaluate (P i) = evaluate (uTerm isJ k i)) :
    evaluate (uSum k P) =
      (V8).smul (weightNine : LatModuleGen (latP 4)) k (aVec isJ : LatModuleGen (latP 4)) := by
  have hnine : (weightNine : LatModuleGen (latP 4)) ∈ (V8).grading 9 := weightNine_mem_grading
  rw [skew_finite (V8) hnine (aVec_mem' isJ) (13 - k) (by omega), uSum,
    evaluate_flatMap_range]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [evaluate_scaleVector, hP i (Finset.mem_range.mp hi), evaluate_uTerm, uCoef]
  congr 1
  push_cast
  rw [sgnQ_cast]
  ring_nf

/-- Stage 2: certified data `Q j` for the terms give `C(15,k) (u₍ₖ₎a)₍₆₋ₖ₎a`. -/
theorem evaluate_vSum (isJ : Bool) (k : ℕ) (hk : k ≤ 12) (Y : SectorVector)
    (hY : evaluate Y =
      (V8).smul (weightNine : LatModuleGen (latP 4)) k (aVec isJ : LatModuleGen (latP 4)))
    (Q : ℕ → SectorVector) (hQ : ∀ j < 10, evaluate (Q j) = evaluate (vTerm isJ Y k j)) :
    evaluate (vSum k Q) = ((Nat.choose 15 k : ℕ) : ℂ) •
      (V8).smul ((V8).smul (weightNine : LatModuleGen (latP 4)) k (aVec isJ)) (6 - k)
        (aVec isJ : LatModuleGen (latP 4)) := by
  have hnine : (weightNine : LatModuleGen (latP 4)) ∈ (V8).grading 9 := weightNine_mem_grading
  have hyg : (V8).smul (weightNine : LatModuleGen (latP 4)) k (aVec isJ) ∈ (V8).grading (12 - k) := by
    have := (V8).smul_mem_grading hnine (aVec_mem' isJ) (k : ℤ)
    rwa [show (9 : ℤ) + 4 - k - 1 = 12 - k by ring] at this
  rw [skew_finite (V8) hyg (aVec_mem' isJ) 10 (by omega), Finset.smul_sum, vSum,
    evaluate_flatMap_range]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [evaluate_scaleVector, hQ j (Finset.mem_range.mp hj), evaluate_vTerm, hY, smul_smul, vCoef]
  congr 1
  push_cast
  rw [sgnQ_cast]
  ring_nf

end VOA.Classification.COne.OrbSgl
