/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Huang.ATransformComul

/-! # Actual L(1) comultiplication on arbitrary weak modules

This port of the finite Hadamard calculation uses only the genuine weak-module
Jacobi identity and translation covariance. It requires neither an ordinary
L(0) action nor a generalized grading, and supplies the A_r opposite Jacobi proof.
-/
namespace VOA.LogTensor.Ar
open VOA VOA.VertexOperatorAlgebra VOA.Huang.LiRegular VOA.Huang.ATransform
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
variable (N : WeakModule W M)

/-- L(1) of the actual weak action. -/
def L1w : Module.End ℂ M := mode (N.YM W.conformalVector) 2

/-- `[L(1), uₘ] = (2 wt u − m − 2) uₘ₊₁ + (L(1)u)ₘ` for homogeneous `u`. -/
theorem L1w_comm {wt : ℤ} {u : V} (hu : u ∈ W.grading wt) (m : ℤ) (x : M) :
    L1w N (mode (N.YM u) m x) - mode (N.YM u) m (L1w N x)
      = ((2 * wt - m - 2 : ℤ) : ℂ) • mode (N.YM u) (m + 1) x
        + mode (N.YM (W.L 1 u)) m x := by
  rw [L1w, module_commutator N]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc (0 : ℤ) 2) (fun i hi => by
    rw [Function.mem_support] at hi
    simp only [Finset.coe_Icc, Set.mem_Icc]
    refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
    · rw [cbz_apply_neg 2 h, zero_smul]
    · rw [cbz_lt (p := 2) (c := i) (by norm_num) h, zero_smul])]
  rw [show Finset.Icc (0 : ℤ) 2 = {0, 1, 2} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have e0 : W.smul W.conformalVector 0 u = W.L (-1) u := by
    rw [L_def]; rfl
  have e1 : W.smul W.conformalVector 1 u = (wt : ℂ) • u := by
    rw [← L_zero_grading W u hu, L_def]; rfl
  have e2 : W.smul W.conformalVector 2 u = W.L 1 u := by
    rw [L_def]; rfl
  rw [e0, e1, e2]
  have hT := act_T_covariance N u (2 + m - 0) x
  simp only [WeakModule.act_def] at hT
  rw [hT, map_smul, mode_smul, LinearMap.smul_apply]
  have c0 : cbz 2 0 = 1 := cbz_zero 2
  have c1 : cbz 2 1 = 2 := by
    have := cbz_natCast_eq_choose (a := 2) (k := 1) (by norm_num)
    norm_num at this; exact this
  have c2 : cbz 2 2 = 1 := by
    have := cbz_natCast_eq_choose (a := 2) (k := 2) (by norm_num)
    norm_num at this; exact this
  rw [c0, c1, c2, show 2 + m - 0 - 1 = m + 1 by ring, show 2 + m - 1 = m + 1 by ring,
    show 2 + m - 2 = m by ring]
  push_cast
  module


/-- The single step: `ad_{L(1)}(u₍ₛ₎) = (2p − s − 2) u₍ₛ₊₁₎ + (L(1)u)₍ₛ₎`. -/
theorem adE_L1w_mode {p : ℤ} {u : V} (hu : u ∈ W.grading p) (s : ℤ) :
    adE (L1w N) (mode (N.YM u) s)
      = ((2 * p - s - 2 : ℤ) : ℂ) • mode (N.YM u) (s + 1) + mode (N.YM (W.L 1 u)) s := by
  ext x
  simp only [adE, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply]
  exact L1w_comm N hu s x

/-- The iterate `ad_{L(1)}ᵇ(u₍ₛ₎) = Σ_{a ≤ b} K p s b a (L(1)ᵃu)₍ₛ₊₍b−a₎₎`
(library coefficient `K`). -/
theorem adE_L1w_pow_mode {p : ℤ} {u : V} (hu : u ∈ W.grading p) (s : ℤ) (b : ℕ) :
    (adE (L1w N))^[b] (mode (N.YM u) s)
      = ∑ a ∈ Finset.range (b + 1),
          K p s b a • mode (N.YM (((W.L 1) ^ a) u)) (s + ((b - a : ℕ) : ℤ)) := by
  induction b generalizing s with
  | zero =>
      rw [Function.iterate_zero, id_eq, show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one]
      rw [show K p s 0 0 = 1 from by rw [K]; simp, one_smul]
      simp
  | succ b ih =>
      rw [Function.iterate_succ', Function.comp_apply, ih]
      rw [show adE (L1w N) (∑ a ∈ Finset.range (b + 1),
            K p s b a • mode (N.YM (((W.L 1) ^ a) u)) (s + ((b - a : ℕ) : ℤ)))
          = adEₗ (L1w N) (∑ a ∈ Finset.range (b + 1),
            K p s b a • mode (N.YM (((W.L 1) ^ a) u)) (s + ((b - a : ℕ) : ℤ))) from rfl]
      rw [map_sum]
      have hstep : ∀ a ∈ Finset.range (b + 1),
          adEₗ (L1w N) (K p s b a • mode (N.YM (((W.L 1) ^ a) u)) (s + ((b - a : ℕ) : ℤ)))
            = (K p s b a * ((2 * p - (a : ℤ) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ))
                • mode (N.YM (((W.L 1) ^ a) u)) (s + ((b - a : ℕ) : ℤ) + 1)
              + K p s b a • mode (N.YM (((W.L 1) ^ (a + 1)) u)) (s + ((b - a : ℕ) : ℤ)) := by
        intro a ha
        rw [Finset.mem_range, Nat.lt_succ_iff] at ha
        have hmem : ((W.L 1) ^ a) u ∈ W.grading (p - (a : ℤ)) := L_one_pow_mem W hu a
        change adE (L1w N) _ = _
        rw [adE_smul, adE_L1w_mode N hmem (s + ((b - a : ℕ) : ℤ))]
        rw [smul_add, smul_smul]
        rw [show ((W.L 1) ^ (a + 1)) u = (W.L 1) (((W.L 1) ^ a) u) from by
          rw [pow_succ', Module.End.mul_apply]]
        congr 2
        rw [show ((2 * (p - (a : ℤ)) - (s + ((b - a : ℕ) : ℤ)) - 2 : ℤ) : ℂ)
            = ((2 * p - (a : ℤ) - s - (b : ℤ) - 2 : ℤ) : ℂ) from by
          congr 1; push_cast [Nat.cast_sub ha]; ring]
      rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
      set T : ℕ → Module.End ℂ M :=
        fun a => mode (N.YM (((W.L 1) ^ a) u)) (s + ((b + 1 - a : ℕ) : ℤ)) with hT
      have hSum1 : ∑ a ∈ Finset.range (b + 1),
            (K p s b a * ((2 * p - (a : ℤ) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ))
              • mode (N.YM (((W.L 1) ^ a) u)) (s + ((b - a : ℕ) : ℤ) + 1)
          = ∑ a ∈ Finset.range (b + 1),
            (K p s b a * ((2 * p - (a : ℤ) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ)) • T a := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        rw [Finset.mem_range, Nat.lt_succ_iff] at ha
        rw [hT]; congr 2
        push_cast [Nat.cast_sub ha, Nat.cast_sub (by omega : a ≤ b + 1)]; ring
      have hSum2 : ∑ a ∈ Finset.range (b + 1),
            K p s b a • mode (N.YM (((W.L 1) ^ (a + 1)) u)) (s + ((b - a : ℕ) : ℤ))
          = ∑ a ∈ Finset.range (b + 1), K p s b a • T (a + 1) := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        rw [Finset.mem_range, Nat.lt_succ_iff] at ha
        rw [hT]; congr 2
        push_cast [Nat.cast_sub ha, Nat.cast_sub (by omega : a + 1 ≤ b + 1)]; ring
      rw [hSum1, hSum2]
      rw [show (∑ a ∈ Finset.range (b + 1 + 1),
            K p s (b + 1) a • mode (N.YM (((W.L 1) ^ a) u)) (s + ((b + 1 - a : ℕ) : ℤ)))
          = ∑ a ∈ Finset.range (b + 2), K p s (b + 1) a • T a from rfl]
      have hpad1 : ∑ a ∈ Finset.range (b + 1),
            (K p s b a * ((2 * p - (a : ℤ) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ)) • T a
          = ∑ a ∈ Finset.range (b + 2),
            (K p s b a * ((2 * p - (a : ℤ) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ)) • T a := by
        rw [show b + 2 = (b + 1) + 1 from rfl,
          Finset.sum_range_succ (fun a =>
            (K p s b a * ((2 * p - (a : ℤ) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ)) • T a) (b + 1)]
        rw [K_vanish p s b (b + 1) (by omega)]; simp
      have hpad2 : ∑ a ∈ Finset.range (b + 1), K p s b a • T (a + 1)
          = ∑ a ∈ Finset.range (b + 2), (if a = 0 then (0 : ℂ) else K p s b (a - 1)) • T a := by
        rw [show b + 2 = (b + 1) + 1 from rfl]
        rw [Finset.sum_range_succ' (fun a => (if a = 0 then (0 : ℂ) else K p s b (a - 1)) • T a)
          (b + 1)]
        simp only [Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero _), if_pos]
        simp
      rw [hpad1, hpad2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a ha => ?_)
      rw [Finset.mem_range] at ha
      rw [← add_smul]
      congr 1
      rcases Nat.eq_zero_or_pos a with rfl | hapos
      · simp only [if_true, add_zero]
        rw [show K p s (b + 1) 0
              = ((2 * p - (0 : ℤ) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ) * K p s b 0 from by
          rw [K]; push_cast; ring]
        push_cast; ring
      · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        rw [if_neg (Nat.succ_ne_zero _)]
        rw [show a' + 1 - 1 = a' from by omega]
        rw [show K p s (b + 1) (a' + 1)
              = ((2 * p - ((a' : ℤ) + 1) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ) * K p s b (a' + 1)
                + K p s b a' from by rw [K]]
        push_cast; ring

/-- The comultiplication with the library coefficient:
`L(1)ᵗ(u₍ₛ₎w) = Σ_{k ≤ t} Σ_{a ≤ k} C(t,k) K p s k a (L(1)ᵃu)₍ₛ₊₍k−a₎₎ L(1)^{t−k} w`. -/
theorem L1w_pow_mode_K {p : ℤ} {u : V} (hu : u ∈ W.grading p) (s : ℤ) (w : M) (t : ℕ) :
    (L1w N ^ t) (mode (N.YM u) s w)
      = ∑ k ∈ Finset.range (t + 1), ∑ a ∈ Finset.range (k + 1),
          ((t.choose k : ℂ) * K p s k a)
            • mode (N.YM (((W.L 1) ^ a) u)) (s + ((k - a : ℕ) : ℤ)) ((L1w N ^ (t - k)) w) := by
  have h := congrArg (fun A : Module.End ℂ M => A w) (pow_mul_eq_sum (L1w N) (mode (N.YM u) s) t)
  simp only [Module.End.mul_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply] at h
  rw [h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [adE_L1w_pow_mode N hu s k]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
    smul_smul]

/-- The closed comultiplication coefficient. -/
noncomputable def comulCoeff (p s : ℤ) (a c b : ℕ) : ℂ :=
  ((a.factorial : ℂ)⁻¹ * (b.factorial : ℂ)⁻¹) * gBinom (2 * p - s - 2 - (a : ℤ)) c

/-- **The closed module comultiplication.**
`(t!)⁻¹ L(1)ᵗ(u₍ₛ₎w)`
`  = Σ_{k ≤ t} Σ_{a ≤ k} (a!)⁻¹((t−k)!)⁻¹ C(2p−s−2−a, k−a) (L(1)ᵃu)₍ₛ₊₍k−a₎₎ L(1)^{t−k} w`. -/
theorem comul_mode {p : ℤ} {u : V} (hu : u ∈ W.grading p) (s : ℤ) (w : M) (t : ℕ) :
    ((t.factorial : ℂ)⁻¹) • (L1w N ^ t) (mode (N.YM u) s w)
      = ∑ k ∈ Finset.range (t + 1), ∑ a ∈ Finset.range (k + 1),
          comulCoeff p s a (k - a) (t - k)
            • mode (N.YM (((W.L 1) ^ a) u)) (s + ((k - a : ℕ) : ℤ)) ((L1w N ^ (t - k)) w) := by
  rw [L1w_pow_mode_K N hu s w t, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk ha
  rw [smul_smul]
  congr 1
  have hK := K_closed p s k a ha
  have hfa : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have hfk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hft : (t.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
  have hftk : ((t - k).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (t - k)
  have hch : (t.choose k : ℂ) * (k.factorial : ℂ) * ((t - k).factorial : ℂ) = t.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hKv : K p s k a = (k.factorial : ℂ) * gBinom (2 * p - s - 2 - (a : ℤ)) (k - a)
      / (a.factorial : ℂ) := by
    rw [eq_div_iff hfa, mul_comm, hK]
  rw [comulCoeff, hKv]
  field_simp
  linear_combination (gBinom (2 * p - s - 2 - (a : ℤ)) (k - a)) * hch

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- **The summed comultiplication**: for any family of linear maps `G t`,
`Σᶠ_t (t!)⁻¹ G_t(L(1)ᵗ(u₍ₛ₎w))`
`  = Σ_{a,c,b} (a!)⁻¹(b!)⁻¹ C(2p−s−2−a, c) G_{a+c+b}((L(1)ᵃu)₍ₛ₊c₎ L(1)ᵇw)`,
the box bounds `P, C, J` being any bounds beyond which the summands vanish. -/
theorem comul_sum {p : ℤ} {u : V} (hu : u ∈ W.grading p) (s : ℤ) (w : M)
    (G : ℕ → M →ₗ[ℂ] E) (P C J : ℕ)
    (hP : ∀ a, P ≤ a → (W.L 1 ^ a) u = 0) (hJ : ∀ b, J ≤ b → (L1w N ^ b) w = 0)
    (hC : ∀ a b c : ℕ, C ≤ c →
      mode (N.YM ((W.L 1 ^ a) u)) (s + (c : ℤ)) ((L1w N ^ b) w) = 0) :
    ∑ᶠ t : ℕ, ((t.factorial : ℂ)⁻¹) • G t ((L1w N ^ t) (mode (N.YM u) s w))
      = ∑ a ∈ Finset.range P, ∑ c ∈ Finset.range C, ∑ b ∈ Finset.range J,
          comulCoeff p s a c b
            • G (a + c + b) (mode (N.YM ((W.L 1 ^ a) u)) (s + (c : ℤ)) ((L1w N ^ b) w)) := by
  set T : ℕ := P + C + J with hT
  set F : ℕ → ℕ → ℕ → E := fun a c b => comulCoeff p s a c b
      • G (a + c + b) (mode (N.YM ((W.L 1 ^ a) u)) (s + (c : ℤ)) ((L1w N ^ b) w)) with hF
  have hvec : ∀ a c b : ℕ, T ≤ a + c + b →
      mode (N.YM ((W.L 1 ^ a) u)) (s + (c : ℤ)) ((L1w N ^ b) w) = 0 := by
    intro a c b h
    rcases le_or_gt P a with ha | ha
    · rw [hP a ha, map_zero, mode_zero, LinearMap.zero_apply]
    rcases le_or_gt C c with hc | hc
    · exact hC a b c hc
    rw [hJ b (by omega), map_zero]
  have hF0 : ∀ a c b, T ≤ a + c + b → F a c b = 0 := by
    intro a c b h
    simp only [hF, hvec a c b h, map_zero, smul_zero]
  -- the per-`t` expansion
  have hexp : ∀ t : ℕ, ((t.factorial : ℂ)⁻¹) • G t ((L1w N ^ t) (mode (N.YM u) s w))
      = ∑ k ∈ Finset.range (t + 1), ∑ a ∈ Finset.range (k + 1), F a (k - a) (t - k) := by
    intro t
    rw [← map_smul, comul_mode N hu s w t, map_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [map_sum]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk ha
    rw [map_smul, hF]
    simp only
    rw [show a + (k - a) + (t - k) = t by omega]
  have hsupp : ∀ t : ℕ, T ≤ t →
      ((t.factorial : ℂ)⁻¹) • G t ((L1w N ^ t) (mode (N.YM u) s w)) = 0 := by
    intro t ht
    rw [hexp t]
    refine Finset.sum_eq_zero (fun k hk => Finset.sum_eq_zero (fun a ha => ?_))
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk ha
    exact hF0 a (k - a) (t - k) (by omega)
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range T) (fun t ht => by
    rw [Function.mem_support] at ht
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact ht (hsupp t (by omega)))]
  rw [Finset.sum_congr rfl (fun t _ => hexp t), simplex_eq_box F T hF0]
  -- shrink the box
  rw [Finset.sum_subset (Finset.range_subset_range.mpr (show P ≤ T by omega)) (fun a ha ha' => ?_)]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_subset (Finset.range_subset_range.mpr (show C ≤ T by omega))
      (fun c hc hc' => ?_)]
    · refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Finset.sum_subset (Finset.range_subset_range.mpr (show J ≤ T by omega))
        (fun b hb hb' => ?_)]
      rw [Finset.mem_range] at hb'
      simp only [hJ b (by omega), map_zero, smul_zero]
    · rw [Finset.mem_range] at hc'
      exact Finset.sum_eq_zero (fun b _ => by simp only [hC a b c (by omega), map_zero,
        smul_zero])
  · rw [Finset.mem_range] at ha'
    exact Finset.sum_eq_zero (fun c _ => Finset.sum_eq_zero (fun b _ => by
      simp only [hP a (by omega), map_zero, mode_zero, LinearMap.zero_apply, smul_zero]))


end VOA.LogTensor.Ar
