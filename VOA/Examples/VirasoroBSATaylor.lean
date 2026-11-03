/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroBSADiagonalResponse
import VOA.Core.QuasiPrimaryDecomp

/-!
# Finite translation coefficients and the first two Virasoro modes

Signed inverse-factorial powers of translation are the coefficients of a
formal exponential. Their commutation formulas with L₁ and L₂ are finite
identities, requiring no analytic exponential or convergence assumption.
-/
namespace VOA.VirModule

/-- The coefficient of z^k in formal translation by -z. This is an actual
linear endomorphism, so each finite coefficient can be used independently. -/
noncomputable def bsaTaylor (c : ℂ) (k : ℕ) : Module.End ℂ (VirUniv c) :=
  positiveLadderCoefficient k • (Lop c (-1))^k

/-- The zeroth translation coefficient is the identity. -/
@[simp] theorem bsaTaylor_zero (c : ℂ) (v : VirUniv c) : bsaTaylor c 0 v=v := by
  simp [bsaTaylor, positiveLadderCoefficient]

/-- Repeated translation raises conformal weight by its exponent. -/
theorem bsaTranslation_mem (c : ℂ) {j : ℤ} {v : VirUniv c}
    (hv : v ∈ gradingVir c j) (k : ℕ) :
    ((Lop c (-1))^k) v ∈ gradingVir c (j+(k:ℤ)) := by
  simpa only [virasoroVOA_L_eq_Lop] using Lneg1_pow_mem (virasoroVOA c) hv k

/-- On a homogeneous vector the L₁ commutator with an arbitrary translation
power consists of the translated L₁ image and one lower translation power. -/
theorem bsaL1_translation_power (c : ℂ) {j : ℤ} {v : VirUniv c}
    (hv : v ∈ gradingVir c j) (k : ℕ) :
    Lop c 1 (((Lop c (-1))^(k+1)) v) =
      ((Lop c (-1))^(k+1)) (Lop c 1 v) +
        (((k:ℂ)+1)*(2*(j:ℂ)+(k:ℂ))) • (((Lop c (-1))^k) v) := by
  have hcomm {q : ℤ} {w : VirUniv c} (hw : w ∈ gradingVir c q) :
      Lop c 1 (Lop c (-1) w) = Lop c (-1) (Lop c 1 w)+(2*(q:ℂ)) • w := by
    simpa only [virasoroVOA_L_eq_Lop] using L1_Lneg1_grading (virasoroVOA c) hw
  have hp (m : ℕ) (w : VirUniv c) : Lop c (-1) (((Lop c (-1))^m) w) =
      ((Lop c (-1))^(m+1)) w := by rw [pow_succ', Module.End.mul_apply]
  induction k with
  | zero => simpa using hcomm hv
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, hcomm (bsaTranslation_mem c hv (k+1)),
      ih, map_add, map_smul]
    simp only [Module.End.mul_apply, hp]
    push_cast
    module

/-- Commuting L₂ past one translation contributes three times L₁. There is
no central term because the mode indices do not add to zero. -/
theorem bsaL2_translation (c : ℂ) (v : VirUniv c) :
    Lop c 2 (Lop c (-1) v) = Lop c (-1) (Lop c 2 v)+(3:ℂ) • Lop c 1 v := by
  have hh := LeeYang.Lop_apply_comm c 2 (-1) v
  norm_num at hh
  exact hh

/-- For at least two translations the L₂ commutator stops after its L₀
term. Homogeneity evaluates L₀, leaving three explicit translated vectors. -/
theorem bsaL2_translation_power (c : ℂ) {j : ℤ} {v : VirUniv c}
    (hv : v ∈ gradingVir c j) (k : ℕ) :
    Lop c 2 (((Lop c (-1))^(k+2)) v) =
      ((Lop c (-1))^(k+2)) (Lop c 2 v) +
      (3*((k:ℂ)+2)) • (((Lop c (-1))^(k+1)) (Lop c 1 v)) +
      (((k:ℂ)+2)*((k:ℂ)+1)*(3*(j:ℂ)+(k:ℂ))) • (((Lop c (-1))^k) v) := by
  have hp (m : ℕ) (w : VirUniv c) : Lop c (-1) (((Lop c (-1))^m) w) =
      ((Lop c (-1))^(m+1)) w := by rw [pow_succ', Module.End.mul_apply]
  induction k with
  | zero =>
    have h1 := bsaL1_translation_power c hv 0
    have h2 := bsaL2_translation c v
    have h3 := bsaL2_translation c (Lop c (-1) v)
    simp only [pow_succ', pow_zero, Module.End.mul_apply, Module.End.one_apply,
      Nat.cast_zero, zero_add, mul_one, one_mul] at *
    rw [h2, h1, map_add, map_smul] at h3
    convert h3 using 1; module
  | succ k ih =>
    rw [show k+1+2=(k+2)+1 by omega, pow_succ', Module.End.mul_apply,
      bsaL2_translation, ih, bsaL1_translation_power c hv (k+1),
      map_add, map_add, map_smul, map_smul, smul_add]
    simp only [Module.End.mul_apply, hp]
    push_cast
    module

/-- Multiplying the next signed inverse factorial by its index removes
that index and changes the sign. -/
theorem bsaLadder_succ_mul (k : ℕ) :
    positiveLadderCoefficient (k+1)*((k:ℂ)+1) = -positiveLadderCoefficient k := by
  rw [positiveLadderCoefficient]
  field_simp

/-- The factorial-normalized L₁ translation formula has no denominators
left in its correction term. -/
theorem bsaTaylor_L1 (c : ℂ) {j : ℤ} {v : VirUniv c}
    (hv : v ∈ gradingVir c j) (k : ℕ) :
    Lop c 1 (bsaTaylor c (k+1) v) = bsaTaylor c (k+1) (Lop c 1 v) -
      (2*(j:ℂ)+(k:ℂ)) • bsaTaylor c k v := by
  simp only [bsaTaylor, LinearMap.smul_apply, map_smul, bsaL1_translation_power c hv k,
    smul_add, smul_smul]
  rw [← mul_assoc, bsaLadder_succ_mul]
  module

/-- The first normalized L₂ correction is minus three times L₁. -/
theorem bsaTaylor_L2_one (c : ℂ) (v : VirUniv c) :
    Lop c 2 (bsaTaylor c 1 v) = bsaTaylor c 1 (Lop c 2 v)-(3:ℂ) • Lop c 1 v := by
  simp [bsaTaylor, positiveLadderCoefficient, bsaL2_translation]
  module

/-- The normalized L₂ formula involves only the two preceding Taylor
coefficients. Its last scalar uses the original vector's conformal weight. -/
theorem bsaTaylor_L2 (c : ℂ) {j : ℤ} {v : VirUniv c}
    (hv : v ∈ gradingVir c j) (k : ℕ) :
    Lop c 2 (bsaTaylor c (k+2) v) = bsaTaylor c (k+2) (Lop c 2 v) -
      (3:ℂ) • bsaTaylor c (k+1) (Lop c 1 v) +
      (3*(j:ℂ)+(k:ℂ)) • bsaTaylor c k v := by
  have h1 := bsaLadder_succ_mul (k+1)
  have h2 := bsaLadder_succ_mul k
  push_cast at h1
  have h3 : positiveLadderCoefficient (k+2)*((k:ℂ)+2)*((k:ℂ)+1)=
      positiveLadderCoefficient k := by
    linear_combination ((k:ℂ)+1)*h1-h2
  simp only [bsaTaylor, LinearMap.smul_apply, map_smul,
    bsaL2_translation_power c hv k, smul_add, smul_smul]
  have he1 : positiveLadderCoefficient (k+2)*(3*((k:ℂ)+2))=
      -3*positiveLadderCoefficient (k+1) := by linear_combination 3*h1
  have he2 : positiveLadderCoefficient (k+2)*(((k:ℂ)+2)*((k:ℂ)+1)*(3*(j:ℂ)+(k:ℂ)))=
      (3*(j:ℂ)+(k:ℂ))*positiveLadderCoefficient k := by
    linear_combination (3*(j:ℂ)+(k:ℂ))*h3
  rw [he1, he2]
  module


/-- Finite convolution of Taylor translation coefficients with a sequence
of states. Its rth value is the rth coefficient of formal translation. -/
noncomputable def bsaTaylorSum (c : ℂ) (v : ℕ → VirUniv c) (r : ℕ) : VirUniv c :=
  ∑ j : Fin (r+1), bsaTaylor c (r-j.val) (v j)

/-- For the BSA sequence the Taylor convolution is precisely the
reflected state defined above, with the same signed factorial normalization. -/
theorem bsaTaylorSum_state (c : ℂ) (N r : ℕ) :
    bsaTaylorSum c (bsaState c N) r = bsaReflectedState c N r := rfl

/-- Separating the last coefficient of the convolution exposes its identity
Taylor term, leaving all earlier translation exponents positive. -/
theorem bsaTaylorSum_succ (c : ℂ) (v : ℕ → VirUniv c) (r : ℕ) :
    bsaTaylorSum c v (r+1) =
      (∑ j : Fin (r+1), bsaTaylor c (r-j.val+1) (v j)) + v (r+1) := by
  unfold bsaTaylorSum
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, Nat.sub_self, bsaTaylor_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [show r+1-j.val=r-j.val+1 by have := j.isLt; omega]

/-- Separating the last two coefficients leaves translation powers at
least two, as needed for the normalized L₂ commutator. -/
theorem bsaTaylorSum_two (c : ℂ) (v : ℕ → VirUniv c) (r : ℕ) :
    bsaTaylorSum c v (r+2) =
      (∑ j : Fin (r+1), bsaTaylor c (r-j.val+2) (v j)) +
      bsaTaylor c 1 (v (r+1)) + v (r+2) := by
  rw [show r+2=(r+1)+1 by omega, bsaTaylorSum_succ, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, Nat.sub_self, zero_add]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  rw [show r+1-j.val+1=r-j.val+2 by have := j.isLt; omega]

/-- The L₁ commutator of a translated homogeneous sequence reduces to two
finite convolutions. It only uses weights through the current level. -/
theorem bsaTaylorSum_L1 (c : ℂ) (v : ℕ → VirUniv c) (r : ℕ)
    (hv : ∀ j : Fin (r+1), v j ∈ gradingVir c (j:ℤ)) :
    Lop c 1 (bsaTaylorSum c v (r+1)) =
      bsaTaylorSum c (fun j => Lop c 1 (v j)) (r+1) -
        ∑ j : Fin (r+1), ((r:ℂ)+(j:ℂ)) • bsaTaylor c (r-j.val) (v j) := by
  rw [bsaTaylorSum_succ, bsaTaylorSum_succ]
  simp only [map_add, map_sum]
  have hs : (∑ j : Fin (r+1), Lop c 1 (bsaTaylor c (r-j.val+1) (v j))) =
      ∑ j : Fin (r+1), (bsaTaylor c (r-j.val+1) (Lop c 1 (v j)) -
        ((r:ℂ)+(j:ℂ)) • bsaTaylor c (r-j.val) (v j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [bsaTaylor_L1 c (hv j)]
    congr 2
    rw [Nat.cast_sub (by have := j.isLt; omega)]
    push_cast
    ring
  rw [hs, Finset.sum_sub_distrib]
  abel

/-- The L₂ commutator reduces to three finite convolutions. The last scalar
combines the conformal weight and the Taylor exponent. -/
theorem bsaTaylorSum_L2 (c : ℂ) (v : ℕ → VirUniv c) (r : ℕ)
    (hv : ∀ j : Fin (r+1), v j ∈ gradingVir c (j:ℤ)) :
    Lop c 2 (bsaTaylorSum c v (r+2)) =
      bsaTaylorSum c (fun j => Lop c 2 (v j)) (r+2) -
      (3:ℂ) • bsaTaylorSum c (fun j => Lop c 1 (v j)) (r+1) +
      ∑ j : Fin (r+1), ((r:ℂ)+2*(j:ℂ)) • bsaTaylor c (r-j.val) (v j) := by
  rw [bsaTaylorSum_two, bsaTaylorSum_two, bsaTaylorSum_succ]
  simp only [map_add, map_sum, bsaTaylor_L2_one]
  have hs : (∑ j : Fin (r+1), Lop c 2 (bsaTaylor c (r-j.val+2) (v j))) =
      ∑ j : Fin (r+1), (bsaTaylor c (r-j.val+2) (Lop c 2 (v j)) -
        (3:ℂ) • bsaTaylor c (r-j.val+1) (Lop c 1 (v j)) +
        ((r:ℂ)+2*(j:ℂ)) • bsaTaylor c (r-j.val) (v j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [bsaTaylor_L2 c (hv j)]
    congr 2
    rw [Nat.cast_sub (by have := j.isLt; omega)]
    push_cast
    ring
  rw [hs, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum]
  module

/-- After shifting past the vacuum term, the L₁ Ward image is a convolution
weighted by its earlier index. -/
theorem bsaTaylorSum_state_L1_input (c : ℂ) (N r : ℕ) (hr : r+1<N) :
    bsaTaylorSum c (fun j => Lop c 1 (bsaState c N j)) (r+1) =
      ∑ j : Fin (r+1), (j:ℂ) • bsaTaylor c (r-j.val) (bsaState c N j) := by
  unfold bsaTaylorSum
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, bsaState_zero,
    Lop_vacuum c (by norm_num : (-1:ℤ)≤1), map_zero, zero_add, Fin.val_succ]
  apply Finset.sum_congr rfl
  intro j hj
  rw [bsaState_L1 c N j (by have := j.isLt; omega), map_smul]
  congr 2
  congr 1
  omega

/-- Shifting past levels zero and one applies the established L₂ Ward
coefficient to every remaining intermediate state. -/
theorem bsaTaylorSum_state_L2_input (N r : ℕ) (hr : r+2<N) :
    bsaTaylorSum (bsaCharge N) (fun j => Lop (bsaCharge N) 2 (bsaState (bsaCharge N) N j)) (r+2) =
      ∑ j : Fin (r+1), ((j:ℂ)+2+bsaL2Offset N) •
        bsaTaylor (bsaCharge N) (r-j.val) (bsaState (bsaCharge N) N j) := by
  unfold bsaTaylorSum
  rw [show r+2+1=(r+1)+1+1 by omega, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, bsaState_zero, bsaState_one,
    Lop_vacuum (bsaCharge N) (by norm_num : (-1:ℤ)≤2), map_zero, zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show j.val+1+1=j.val+2 by omega, bsaState_L2 N j (by have := j.isLt; omega), map_smul]
  congr 2
  congr 1
  omega

/-- The reflected state has the sign-reversed L₁ Ward equation. This
holds at every charge, because the original L₁ equation does too. -/
theorem bsaReflectedState_L1 (c : ℂ) (N r : ℕ) (hr : r+1<N) :
    Lop c 1 (bsaReflectedState c N (r+1)) = -(r:ℂ) • bsaReflectedState c N r := by
  rw [← bsaTaylorSum_state, bsaTaylorSum_L1 c _ r (fun j => bsaState_mem_grading c N j),
    bsaTaylorSum_state_L1_input c N r hr, ← bsaTaylorSum_state, bsaTaylorSum, Finset.smul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  module

/-- At the singular charge the reflected state has the same L₂ Ward
equation as the original state. Thus the two states agree modulo the
canonical radical once their lower-level differences are known to do so. -/
theorem bsaReflectedState_L2 (N r : ℕ) (hr : r+2<N) :
    Lop (bsaCharge N) 2 (bsaReflectedState (bsaCharge N) N (r+2)) =
      ((r:ℂ)+2+bsaL2Offset N) • bsaReflectedState (bsaCharge N) N r := by
  rw [← bsaTaylorSum_state, bsaTaylorSum_L2 _ _ r (fun j => bsaState_mem_grading _ N j),
    bsaTaylorSum_state_L2_input N r hr, bsaTaylorSum_state_L1_input _ N r (by omega),
    ← bsaTaylorSum_state, bsaTaylorSum, Finset.smul_sum, Finset.smul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [smul_smul]
  module


/-- A state whose L₁ and L₂ images have zero right pairing also has zero
right pairing after any positive mode. The commutator induction works inside
the canonical radical, so the images need not be zero as vectors. -/
theorem canB_positive_right_zero_of_one_two (c : ℂ) (v : VirUniv c)
    (h1 : ∀ x, (VirGram4.canB c).form x (Lop c 1 v)=0)
    (h2 : ∀ x, (VirGram4.canB c).form x (Lop c 2 v)=0) :
    ∀ n : ℤ, 0<n → ∀ x, (VirGram4.canB c).form x (Lop c n v)=0 := by
  have hall : ∀ k : ℕ, ∀ x, (VirGram4.canB c).form x (Lop c ((k:ℤ)+2) v)=0 := by
    intro k
    induction k with
    | zero => simpa using h2
    | succ k ih =>
      intro x
      have hh := congrArg ((VirGram4.canB c).form x) (LeeYang.Lop_apply_comm c 1 ((k:ℤ)+2) v)
      have hz : ¬ (1:ℤ)+((k:ℤ)+2)=0 := by omega
      simp only [map_add, map_smul, smul_eq_mul, if_neg hz, zero_smul,
        add_zero] at hh
      rw [← VirGram4.canB_adj', ih, ← VirGram4.canB_adj', h1, zero_add] at hh
      have hn : (1:ℂ)-((k:ℤ)+2) ≠ 0 := by
        intro he
        have he' : (1:ℤ)-((k:ℤ)+2)=0 := by exact_mod_cast he
        omega
      push_cast at hh hn
      have he := (mul_eq_zero.mp hh.symm).resolve_left hn
      convert he using 1 <;> push_cast <;> congr 2 <;> ring
  intro n hn
  by_cases he : n=1
  · simpa [he] using h1
  · obtain ⟨k,hk⟩ := Int.eq_ofNat_of_zero_le (show 0≤n-2 by omega)
    have he : n=(k:ℤ)+2 := by omega
    simpa [he] using hall k

/-- Positive weight and radical-valued L₁/L₂ images force the whole state
into the right radical. Adjointness handles nonempty creation words;
weight orthogonality handles the vacuum. -/
theorem canB_right_zero_of_one_two_mod_radical (c : ℂ) {n : ℕ} (hn : 0<n)
    (v : VirUniv c) (hv : v ∈ gradingVir c (n:ℤ))
    (h1 : ∀ x, (VirGram4.canB c).form x (Lop c 1 v)=0)
    (h2 : ∀ x, (VirGram4.canB c).form x (Lop c 2 v)=0)
    (x : VirUniv c) : (VirGram4.canB c).form x v=0 := by
  have hw (w : List ℕ) : (VirGram4.canB c).form (negWordVir c w) v=0 := by
    cases w with
    | nil =>
        exact (VirGram4.canB c).orthogonal_of_ne (by exact_mod_cast Nat.ne_of_lt hn)
          (virasoroVOA c).vacuum_mem hv
    | cons i w =>
      rw [VirFormSym.negWord_cons_left]
      exact canB_positive_right_zero_of_one_two c v h1 h2 ((i:ℤ)+2) (by omega) _
  have htop : Submodule.span ℂ (Set.range (negWordVir c))=⊤ := negSpanVir_eq_top c
  have hx : x ∈ Submodule.span ℂ (Set.range (negWordVir c)) :=
    htop ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨w,rfl⟩ := hx; exact hw w
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul a x _ hx => simp [map_smul, hx]

/-- The difference between a reflected BSA coefficient and its signed
original. We will prove this difference is in the canonical radical;
no exact universal-state equality is required. -/
noncomputable def bsaReflectionDifference (c : ℂ) (N r : ℕ) : VirUniv c :=
  bsaReflectedState c N r - (-1:ℂ)^r • bsaState c N r

/-- Every term of the finite reflected state has the same conformal weight. -/
theorem bsaReflectedState_mem (c : ℂ) (N r : ℕ) :
    bsaReflectedState c N r ∈ gradingVir c (r:ℤ) := by
  unfold bsaReflectedState
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  have hh := bsaTranslation_mem c (bsaState_mem_grading c N j) (r-j.val)
  have he : (j:ℤ)+((r-j.val:ℕ):ℤ)=(r:ℤ) := by have := j.isLt; omega
  simpa only [he] using hh

/-- The reflection difference is homogeneous, so its vacuum pairing
vanishes at every positive level. -/
theorem bsaReflectionDifference_mem (c : ℂ) (N r : ℕ) :
    bsaReflectionDifference c N r ∈ gradingVir c (r:ℤ) :=
  Submodule.sub_mem _ (bsaReflectedState_mem c N r)
    (Submodule.smul_mem _ _ (bsaState_mem_grading c N r))

/-- The initial reflection difference is zero: translation begins with
the unchanged vacuum coefficient. -/
@[simp] theorem bsaReflectionDifference_zero (c : ℂ) (N : ℕ) :
    bsaReflectionDifference c N 0=0 := by
  simp [bsaReflectionDifference, bsaReflectedState, positiveLadderCoefficient]

/-- L₁ sends a reflection difference to the previous difference with its
sign-reversed Ward scalar. -/
theorem bsaReflectionDifference_L1 (c : ℂ) (N r : ℕ) (hr : r+1<N) :
    Lop c 1 (bsaReflectionDifference c N (r+1)) =
      -(r:ℂ) • bsaReflectionDifference c N r := by
  simp only [bsaReflectionDifference, map_sub, map_smul, bsaReflectedState_L1 c N r hr,
    bsaState_L1 c N r hr, pow_succ, smul_sub, smul_smul]
  module

/-- L₂ sends the reflection difference down two levels at the singular
charge. The even shift preserves its sign. -/
theorem bsaReflectionDifference_L2 (N r : ℕ) (hr : r+2<N) :
    Lop (bsaCharge N) 2 (bsaReflectionDifference (bsaCharge N) N (r+2)) =
      ((r:ℂ)+2+bsaL2Offset N) • bsaReflectionDifference (bsaCharge N) N r := by
  simp only [bsaReflectionDifference, map_sub, map_smul, bsaReflectedState_L2 N r hr,
    bsaState_L2 N r hr, pow_add, smul_sub, smul_smul]
  norm_num
  module

/-- The reflected and signed original BSA states agree in every canonical
pairing before the singular level. Induction only needs L₁ and L₂ and
works modulo the radical, avoiding an unnecessary exact state identity. -/
theorem bsaReflectionDifference_right_zero (N r : ℕ) (hr : r<N)
    (x : VirUniv (bsaCharge N)) :
    (VirGram4.canB (bsaCharge N)).form x (bsaReflectionDifference (bsaCharge N) N r)=0 := by
  induction r using Nat.strong_induction_on generalizing x with
  | h r ih =>
    obtain rfl | hr0 := Nat.eq_zero_or_pos r
    · simp
    apply canB_right_zero_of_one_two_mod_radical _ hr0 _ (bsaReflectionDifference_mem _ N r)
    · intro y
      have he : r=(r-1)+1 := by omega
      rw [he, bsaReflectionDifference_L1 _ N (r-1) (by omega), map_smul,
        ih (r-1) (by omega) (by omega), smul_zero]
    · intro y
      by_cases he : r=1
      · subst r
        have hh := Lop_maps_grading (bsaCharge N) 2 (bsaReflectionDifference_mem _ N 1)
        rw [gradingVir_neg _ _ (by norm_num)] at hh
        rw [show Lop (bsaCharge N) 2 (bsaReflectionDifference (bsaCharge N) N 1)=0 from hh, map_zero]
      · have he' : r=(r-2)+2 := by omega
        rw [he', bsaReflectionDifference_L2 N (r-2) (by omega), map_smul,
          ih (r-2) (by omega) (by omega), smul_zero]

/-- Symmetry transfers the proved radical identity to the first slot,
which is the slot appearing in the actual norm-response formula. -/
theorem bsaScalarNormResponse_eq_diagonal (N r : ℕ) (hr : r<N) :
    bsaScalarNormResponse (bsaCharge N) N r = (-1:ℂ)^r*bsaDiagonalResponse N r := by
  have hh := bsaReflectionDifference_right_zero N r hr
    (bsaL2SourceResponse (bsaCharge N) N r)
  rw [VirFormSym.canB_isSymmetric] at hh
  simp only [bsaReflectionDifference, map_sub, LinearMap.sub_apply,
    map_smul, LinearMap.smul_apply, smul_eq_mul] at hh
  rw [bsaScalarNormResponse_reflected, bsaDiagonalResponse]
  linear_combination hh

end VOA.VirModule
