import VOA.Moonshine.MoonshineCNNearAdjointClosure
import VOA.Moonshine.MoonshineCNNearConsequences
import VOA.Modules.ContragredientClose

/-! `L₁`-commutation with homogeneous near-VOA modes, the resulting expansion of
`L₁ᵗ (u₍ₛ₎ v)` into the two-sided `L₁` tower, and skew symmetry inside a mode.
Only the near-VOA axioms are used: no lower bound on weights and no
finite-dimensionality. The tower coefficients are the closed binomials `VOA.K`. -/

noncomputable section
namespace VOA.NearVOA

open Module (End)
open scoped BigOperators

variable {H : Type*} [AddCommGroup H] [Module ℂ H] (V : NearVOA H)

theorem smul_smul_scalar_left (c : ℂ) (u : H) (n : ℤ) (x : H) :
    V.smul (c • u) n x = c • V.smul u n x := by
  simp only [smul_def, map_smul, mode_smul, LinearMap.smul_apply]

/-- `L₁` against a homogeneous mode:
`L₁ (u₍ₛ₎ x) = (2p − s − 2) u₍ₛ₊₁₎ x + (L₁ u)₍ₛ₎ x + u₍ₛ₎ (L₁ x)`. -/
theorem virasoroOne_smul_of_mem_weight {p : ℤ} {u : H} (hu : u ∈ V.grading p)
    (s : ℤ) (x : H) :
    V.L 1 (V.smul u s x) = ((2 * p - s - 2 : ℤ) : ℂ) • V.smul u (s + 1) x
      + V.smul (V.L 1 u) s x + V.smul u s (V.L 1 x) := by
  classical
  have h := V.mode_commutator_apply V.conformalVector u x 2 s
  rw [finsum_eq_finsetSum_of_support_subset _ (s := ({0, 1, 2} : Finset ℤ)) (by
    intro i hi
    rw [Function.mem_support] at hi
    by_contra hc
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hc
    rcases lt_or_ge i 0 with hi0 | hi0
    · exact hi (by rw [cbz_apply_neg _ hi0, zero_smul])
    · have h2 : gBinom 2 i.toNat = 0 := by
        simpa using VertexOperatorAlgebra.gBinom_natCast_eq_zero (k := 2) (i := i.toNat)
          (by omega)
      exact hi (by rw [cbz_apply_nonneg _ hi0, h2, zero_smul]))] at h
  have e0 : V.smul V.conformalVector 0 u = V.L (-1) u := rfl
  have e1 : V.smul V.conformalVector 1 u = (p : ℂ) • u := V.L0_grading u hu
  have e2 : V.smul V.conformalVector 2 u = V.L 1 u := rfl
  have c1 : cbz 2 1 = 2 := by norm_num [cbz, gBinom]
  have c2 : cbz 2 2 = 1 := by
    rw [cbz_apply_nonneg _ (by norm_num)]
    change gBinom 2 2 = 1
    norm_num [gBinom, Finset.prod_range_succ]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    cbz_zero, c1, c2, e0, e1, e2, smul_T_apply, smul_smul_scalar_left] at h
  have hL : ∀ w : H, V.L 1 w = V.smul V.conformalVector 2 w := fun w => rfl
  rw [hL, hL x, sub_eq_iff_eq_add.mp h]
  rw [show (2 : ℤ) + s - 0 - 1 = s + 1 by ring, show (2 : ℤ) + s - 1 = s + 1 by ring,
    show (2 : ℤ) + s - 2 = s by ring, ← Int.cast_smul_eq_zsmul ℂ]
  push_cast
  module

/-- The inner derivation `M ↦ ⁅L₁, M⁆` on endomorphisms. -/
def virasoroOneBracket : End ℂ H →ₗ[ℂ] End ℂ H where
  toFun M := ⁅V.L 1, M⁆
  map_add' _ _ := lie_add _ _ _
  map_smul' _ _ := lie_smul _ _ _

theorem virasoroOneBracket_apply (M : End ℂ H) :
    V.virasoroOneBracket M = V.L 1 * M - M * V.L 1 := by
  rw [← LieRing.of_associative_ring_bracket]
  rfl

theorem virasoroOneBracket_mode_of_mem_weight {p : ℤ} {u : H} (hu : u ∈ V.grading p)
    (s : ℤ) :
    V.virasoroOneBracket (mode (V.Y u) s)
      = ((2 * p - s - 2 : ℤ) : ℂ) • mode (V.Y u) (s + 1) + mode (V.Y (V.L 1 u)) s := by
  ext x
  rw [virasoroOneBracket_apply, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply]
  simp only [← smul_def]
  rw [V.virasoroOne_smul_of_mem_weight hu s x]
  abel

/-- The iterated bracket of a homogeneous mode is a finite `L₁`-tower with coefficients `K`. -/
theorem virasoroOneBracket_pow_mode_of_mem_weight {p : ℤ} {u : H} (hu : u ∈ V.grading p)
    (s : ℤ) (b : ℕ) :
    (V.virasoroOneBracket ^ b) (mode (V.Y u) s)
      = ∑ a ∈ Finset.range (b + 1),
          K p s b a • mode (V.Y ((V.L 1 ^ a) u)) (s + ((b - a : ℕ) : ℤ)) := by
  induction b generalizing s with
  | zero =>
      rw [pow_zero, Module.End.one_apply, show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one,
        show K p s 0 0 = 1 from by rw [K]; simp, one_smul]
      simp
  | succ b ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_sum]
      have hstep : ∀ a ∈ Finset.range (b + 1),
          V.virasoroOneBracket (K p s b a • mode (V.Y ((V.L 1 ^ a) u)) (s + ((b - a : ℕ) : ℤ)))
            = (K p s b a * ((2 * p - (a : ℤ) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ))
                • mode (V.Y ((V.L 1 ^ a) u)) (s + ((b - a : ℕ) : ℤ) + 1)
              + K p s b a • mode (V.Y ((V.L 1 ^ (a + 1)) u)) (s + ((b - a : ℕ) : ℤ)) := by
        intro a ha
        rw [Finset.mem_range, Nat.lt_succ_iff] at ha
        have hmem : (V.L 1 ^ a) u ∈ V.grading (p - (a : ℤ)) := V.virasoroOne_pow_mem_weight hu a
        rw [map_smul, V.virasoroOneBracket_mode_of_mem_weight hmem (s + ((b - a : ℕ) : ℤ)),
          smul_add, smul_smul,
          show (V.L 1 ^ (a + 1)) u = V.L 1 ((V.L 1 ^ a) u) from by
            rw [pow_succ', Module.End.mul_apply]]
        congr 2
        rw [show ((2 * (p - (a : ℤ)) - (s + ((b - a : ℕ) : ℤ)) - 2 : ℤ) : ℂ)
            = ((2 * p - (a : ℤ) - s - (b : ℤ) - 2 : ℤ) : ℂ) from by
          congr 1; push_cast [Nat.cast_sub ha]; ring]
      rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
      set W : ℕ → End ℂ H :=
        fun a => mode (V.Y ((V.L 1 ^ a) u)) (s + ((b + 1 - a : ℕ) : ℤ)) with hW
      have hSum1 : ∑ a ∈ Finset.range (b + 1),
            (K p s b a * ((2 * p - (a : ℤ) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ))
              • mode (V.Y ((V.L 1 ^ a) u)) (s + ((b - a : ℕ) : ℤ) + 1)
          = ∑ a ∈ Finset.range (b + 1),
            (K p s b a * ((2 * p - (a : ℤ) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ)) • W a := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        rw [Finset.mem_range, Nat.lt_succ_iff] at ha
        rw [hW]; congr 2
        push_cast [Nat.cast_sub ha, Nat.cast_sub (by omega : a ≤ b + 1)]; ring
      have hSum2 : ∑ a ∈ Finset.range (b + 1),
            K p s b a • mode (V.Y ((V.L 1 ^ (a + 1)) u)) (s + ((b - a : ℕ) : ℤ))
          = ∑ a ∈ Finset.range (b + 1), K p s b a • W (a + 1) := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        rw [Finset.mem_range, Nat.lt_succ_iff] at ha
        rw [hW]; congr 2
        push_cast [Nat.cast_sub ha, Nat.cast_sub (by omega : a + 1 ≤ b + 1)]; ring
      rw [hSum1, hSum2]
      rw [show (∑ a ∈ Finset.range (b + 1 + 1),
            K p s (b + 1) a • mode (V.Y ((V.L 1 ^ a) u)) (s + ((b + 1 - a : ℕ) : ℤ)))
          = ∑ a ∈ Finset.range (b + 2), K p s (b + 1) a • W a from rfl]
      have hpad1 : ∑ a ∈ Finset.range (b + 1),
            (K p s b a * ((2 * p - (a : ℤ) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ)) • W a
          = ∑ a ∈ Finset.range (b + 2),
            (K p s b a * ((2 * p - (a : ℤ) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ)) • W a := by
        rw [show b + 2 = (b + 1) + 1 from rfl,
          Finset.sum_range_succ (fun a =>
            (K p s b a * ((2 * p - (a : ℤ) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ)) • W a) (b + 1),
          K_vanish p s b (b + 1) (by omega)]
        simp
      have hpad2 : ∑ a ∈ Finset.range (b + 1), K p s b a • W (a + 1)
          = ∑ a ∈ Finset.range (b + 2),
              (if a = 0 then (0 : ℂ) else K p s b (a - 1)) • W a := by
        rw [show b + 2 = (b + 1) + 1 from rfl,
          Finset.sum_range_succ' (fun a =>
            (if a = 0 then (0 : ℂ) else K p s b (a - 1)) • W a) (b + 1)]
        simp
      rw [hpad1, hpad2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [← add_smul]
      congr 1
      rcases Nat.eq_zero_or_pos a with rfl | hapos
      · simp only [if_true, add_zero]
        rw [show K p s (b + 1) 0
              = ((2 * p - (0 : ℤ) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ) * K p s b 0 from by
          rw [K]; push_cast; ring]
        push_cast; ring
      · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        rw [if_neg (Nat.succ_ne_zero _), show a' + 1 - 1 = a' from by omega,
          show K p s (b + 1) (a' + 1)
              = ((2 * p - ((a' : ℤ) + 1) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ) * K p s b (a' + 1)
                + K p s b a' from by rw [K]]
        push_cast; ring

/-- One-step Leibniz rule for `L₁`. -/
theorem virasoroOne_mul_eq (M : End ℂ H) :
    V.L 1 * M = M * V.L 1 + V.virasoroOneBracket M := by
  rw [virasoroOneBracket_apply]; abel

/-- The binomial operator identity `L₁ᵏ M = ∑ C(k,j) (ad L₁)ʲ(M) L₁^{k−j}`. -/
theorem virasoroOne_pow_mul_eq_sum (M : End ℂ H) (k : ℕ) :
    V.L 1 ^ k * M
      = ∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℂ) • ((V.virasoroOneBracket ^ j) M * V.L 1 ^ (k - j)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, ih, Finset.mul_sum]
    have hterm : ∀ j ∈ Finset.range (k + 1),
        V.L 1 * ((k.choose j : ℂ) • ((V.virasoroOneBracket ^ j) M * V.L 1 ^ (k - j)))
          = (k.choose j : ℂ) • ((V.virasoroOneBracket ^ j) M * V.L 1 ^ (k + 1 - j))
            + (k.choose j : ℂ) • ((V.virasoroOneBracket ^ (j + 1)) M * V.L 1 ^ (k - j)) := by
      intro j hj
      rw [Finset.mem_range, Nat.lt_succ_iff] at hj
      rw [mul_smul_comm, ← mul_assoc, V.virasoroOne_mul_eq ((V.virasoroOneBracket ^ j) M),
        add_mul, smul_add]
      congr 2
      · rw [mul_assoc, ← pow_succ', show k + 1 - j = (k - j) + 1 from by omega]
      · rw [pow_succ', Module.End.mul_apply]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    set T : ℕ → End ℂ H :=
      fun j => (V.virasoroOneBracket ^ j) M * V.L 1 ^ (k + 1 - j) with hT
    have hS_A : ∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℂ) • ((V.virasoroOneBracket ^ j) M * V.L 1 ^ (k + 1 - j))
        = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) • T j := rfl
    have hS_B : ∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℂ) • ((V.virasoroOneBracket ^ (j + 1)) M * V.L 1 ^ (k - j))
        = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) • T (j + 1) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_range, Nat.lt_succ_iff] at hj
      rw [hT]; simp only [show k + 1 - (j + 1) = k - j from by omega]
    rw [hS_A, hS_B, Finset.sum_range_succ' (fun j => (Nat.choose (k + 1) j : ℂ) • T j) (k + 1)]
    have hpascal : ∀ j ∈ Finset.range (k + 1),
        (Nat.choose (k + 1) (j + 1) : ℂ) • T (j + 1)
          = (k.choose j : ℂ) • T (j + 1) + (k.choose (j + 1) : ℂ) • T (j + 1) := by
      intro j _
      rw [← add_smul, ← Nat.cast_add, Nat.choose_succ_succ k j]
    rw [Finset.sum_congr rfl hpascal, Finset.sum_add_distrib,
      Finset.sum_range_succ' (fun j => (k.choose j : ℂ) • T j) k]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_smul]
    have hpad : ∑ x ∈ Finset.range k, (k.choose (x + 1) : ℂ) • T (x + 1)
        = ∑ x ∈ Finset.range (k + 1), (k.choose (x + 1) : ℂ) • T (x + 1) := by
      rw [Finset.sum_range_succ]
      simp only [Nat.choose_succ_self, Nat.cast_zero, zero_smul, add_zero]
    rw [hpad]
    abel

/-- `L₁ᵗ (u₍ₛ₎ v)` as an explicit combination of the two-sided `L₁` tower, for homogeneous `u`. -/
theorem virasoroOne_pow_smul_eq_sum {p : ℤ} {u : H} (hu : u ∈ V.grading p)
    (v : H) (s : ℤ) (t : ℕ) :
    (V.L 1 ^ t) (V.smul u s v)
      = ∑ b ∈ Finset.range (t + 1), ∑ a ∈ Finset.range (b + 1),
          ((t.choose b : ℂ) * K p s b a)
            • V.smul ((V.L 1 ^ a) u) (s + ((b - a : ℕ) : ℤ)) ((V.L 1 ^ (t - b)) v) := by
  have hmul := congrArg (fun S : End ℂ H => S v) (V.virasoroOne_pow_mul_eq_sum (mode (V.Y u) s) t)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply] at hmul
  rw [smul_def, hmul]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [V.virasoroOneBracket_pow_mode_of_mem_weight hu s b, LinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [LinearMap.smul_apply, smul_smul]
  rfl

/-- Evaluation of a fixed mode on a fixed vector, as a linear function of the state. -/
def smulLeftLinear (k : ℤ) (x : H) : H →ₗ[ℂ] H where
  toFun w := V.smul w k x
  map_add' a b := by simp only [smul_def, map_add, mode_add, LinearMap.add_apply]
  map_smul' c a := V.smul_smul_scalar_left c a k x

@[simp] theorem smulLeftLinear_apply (k : ℤ) (x w : H) :
    V.smulLeftLinear k x w = V.smul w k x := rfl

/-- Skew symmetry transported inside a mode, with the sign collapsed into a binomial. -/
theorem smul_smul_skew (u v : H) (s k : ℤ) (x : H) :
    V.smul (V.smul v s u) k x
      = ∑ᶠ j : ℕ, ((-(-1 : ℂ) ^ s) * gBinom k j) •
          V.smul (V.smul u (s + (j : ℤ)) v) (k - (j : ℤ)) x := by
  have hfin : (Function.support fun j : ℕ => ((j.factorial : ℂ)⁻¹) •
      (sgn (-s - 1 - (j : ℤ))) • ((V.L (-1) ^ j) (V.smul u (s + (j : ℤ)) v))).Finite := by
    obtain ⟨N, hN⟩ := V.regularity u v
    refine Set.Finite.subset (Set.finite_Iio (N - s).toNat) ?_
    intro j hj
    simp only [Function.mem_support, ne_eq] at hj
    simp only [Set.mem_Iio]
    by_contra hc
    rw [not_lt] at hc
    exact hj (by
      have hz := hN (s + (j : ℤ)) (by omega)
      change V.smul u (s + (j : ℤ)) v = 0 at hz
      rw [hz, map_zero, smul_zero, smul_zero])
  rw [V.smul_eq_skew u v s]
  change V.smulLeftLinear k x _ = _
  rw [map_finsum _ hfin]
  refine finsum_congr (fun j => ?_)
  rw [map_smul, map_smul, smulLeftLinear_apply, smul_Tpow, ← Int.cast_smul_eq_zsmul ℂ,
    smul_smul, smul_smul]
  congr 1
  have hprod : ((∏ i ∈ Finset.range j, (-(k - (i : ℤ))) : ℤ) : ℂ)
      = (-1 : ℂ) ^ j * ∏ l ∈ Finset.range j, ((k - (l : ℤ) : ℤ) : ℂ) := by
    induction j with
    | zero => simp
    | succ j ih =>
        rw [Finset.prod_range_succ, Finset.prod_range_succ, Int.cast_mul, ih]
        push_cast; ring
  have hsign : sgn (-s - 1 - (j : ℤ)) * ((-1 : ℂ) ^ j) = -(-1 : ℂ) ^ s := by
    change negOnePow (-s - 1 - (j : ℤ)) * ((-1 : ℂ) ^ j) = -(-1 : ℂ) ^ s
    rw [← negOnePow_natCast j, ← negOnePow_add,
      show (-s - 1 - (j : ℤ)) + (j : ℤ) = -s - 1 from by ring,
      VertexOperatorAlgebra.negOnePow_eq_zpow]
    have h2 : (-1 : ℂ) ^ (-2 * s) = 1 := by
      rw [show (-2 * s : ℤ) = 2 * (-s) from by ring]; exact negOne_zpow_even _
    have e : (-1 : ℂ) ^ (-s - 1) = (-1 : ℂ) ^ s * (-1 : ℂ) ^ (-2 * s - 1) := by
      rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]; congr 1; ring
    rw [e, show (-2 * s - 1 : ℤ) = (-2 * s) + (-1) from by ring,
      zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), h2]
    ring
  rw [hprod, ← gBinom_scalar k j, ← hsign]
  ring

end VOA.NearVOA
