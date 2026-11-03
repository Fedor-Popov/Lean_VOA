/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.LiRegularShift
import VOA.Modules.ContragredientClose

/-!
# The `e^{L(1)}`-comultiplication on a module (A-transform, part 1)

For an ordinary module `N` (`L(1) = ω₍₂₎` acting on `M`), a homogeneous state `u ∈ V_p` and any
`w ∈ M`, the commutator `[L(1), u₍ₛ₎] = (2p − s − 2) u₍ₛ₊₁₎ + (L(1)u)₍ₛ₎` (`L1m_comm`) iterates to
the closed comultiplication

  `(t!)⁻¹ L(1)ᵗ (u₍ₛ₎ w)`
  `  = Σ_{a + c + b = t} (a!)⁻¹ (b!)⁻¹ C(2p − s − 2 − a, c) (L(1)ᵃu)₍ₛ₊c₎ (L(1)ᵇ w)`

(`comul_mode`), the mode form of FHL's conjugation formula
`e^{yL(1)} Y(u,x) e^{−yL(1)} = Y(e^{y(1−yx)L(1)}(1−yx)^{−2L(0)}u, x/(1−yx))` at `y = 1`.
The module statement is the module analogue of the library's `L1pow_smul_comul` (which is stated
on `V` itself); the coefficient is closed with the library's `K_closed`.

The summed form `comul_sum` (with an arbitrary family of linear maps `G t` applied to the `t`-th
term) is what the A-transform consumes.

No `sorry`, no axioms beyond Lean's.
-/

namespace VOA.Huang.ATransform

open VOA VOA.VertexOperatorAlgebra VOA.Huang.LiRegular
open scoped BigOperators

universe u

/-! ## A generic Hadamard expansion -/

section Hadamard

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- The inner derivation `ad_X M = X M − M X`. -/
def adE (X : Module.End ℂ E) (A : Module.End ℂ E) : Module.End ℂ E := X * A - A * X

theorem adE_add (X A B : Module.End ℂ E) : adE X (A + B) = adE X A + adE X B := by
  simp only [adE, mul_add, add_mul]; abel

theorem adE_smul (X : Module.End ℂ E) (c : ℂ) (A : Module.End ℂ E) :
    adE X (c • A) = c • adE X A := by
  simp only [adE, mul_smul_comm, smul_mul_assoc, smul_sub]

/-- `ad_X` as a linear map. -/
def adEₗ (X : Module.End ℂ E) : Module.End ℂ E →ₗ[ℂ] Module.End ℂ E where
  toFun := adE X
  map_add' := adE_add X
  map_smul' := adE_smul X

/-- **Hadamard expansion**: `Xᵏ A = Σ_{j ≤ k} C(k,j) (ad_Xʲ A) X^{k−j}`. -/
theorem pow_mul_eq_sum (X A : Module.End ℂ E) (k : ℕ) :
    X ^ k * A = ∑ j ∈ Finset.range (k + 1),
      (k.choose j : ℂ) • ((adE X)^[j] A * X ^ (k - j)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, ih, Finset.mul_sum]
    have hterm : ∀ j ∈ Finset.range (k + 1),
        X * ((k.choose j : ℂ) • ((adE X)^[j] A * X ^ (k - j)))
          = (k.choose j : ℂ) • ((adE X)^[j] A * X ^ (k + 1 - j))
            + (k.choose j : ℂ) • ((adE X)^[j + 1] A * X ^ (k - j)) := by
      intro j hj
      rw [Finset.mem_range, Nat.lt_succ_iff] at hj
      rw [mul_smul_comm, ← mul_assoc,
        show X * (adE X)^[j] A = (adE X)^[j] A * X + adE X ((adE X)^[j] A) by
          rw [adE]; abel,
        add_mul, smul_add]
      congr 2
      · rw [mul_assoc, ← pow_succ', show k + 1 - j = (k - j) + 1 from by omega]
      · rw [Function.iterate_succ_apply']
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    set T : ℕ → Module.End ℂ E := fun j => (adE X)^[j] A * X ^ (k + 1 - j) with hT
    have hS_B : ∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℂ) • ((adE X)^[j + 1] A * X ^ (k - j))
        = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) • T (j + 1) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_range, Nat.lt_succ_iff] at hj
      rw [hT]; simp only [show k + 1 - (j + 1) = k - j from by omega]
    change ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) • T j + _ = _
    rw [hS_B]
    rw [Finset.sum_range_succ' (fun j => (Nat.choose (k + 1) j : ℂ) • T j) (k + 1)]
    have hpascal : ∀ j ∈ Finset.range (k + 1),
        (Nat.choose (k + 1) (j + 1) : ℂ) • T (j + 1)
          = (k.choose j : ℂ) • T (j + 1) + (k.choose (j + 1) : ℂ) • T (j + 1) := by
      intro j _
      rw [← add_smul, ← Nat.cast_add, Nat.choose_succ_succ k j]
    rw [Finset.sum_congr rfl hpascal, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ' (fun j => (k.choose j : ℂ) • T j) k]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_smul]
    have hpad : ∑ x ∈ Finset.range k, (k.choose (x + 1) : ℂ) • T (x + 1)
        = ∑ x ∈ Finset.range (k + 1), (k.choose (x + 1) : ℂ) • T (x + 1) := by
      rw [Finset.sum_range_succ]
      simp only [Nat.choose_succ_self, Nat.cast_zero, zero_smul, add_zero]
    rw [hpad]
    abel

end Hadamard

/-! ## The module comultiplication -/

section Comul

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {M : Type u} [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M)

/-- The single step: `ad_{L(1)}(u₍ₛ₎) = (2p − s − 2) u₍ₛ₊₁₎ + (L(1)u)₍ₛ₎`. -/
theorem adE_L1m_mode {p : ℤ} {u : V} (hu : u ∈ W.grading p) (s : ℤ) :
    adE (L1m N) (mode (N.YM u) s)
      = ((2 * p - s - 2 : ℤ) : ℂ) • mode (N.YM u) (s + 1) + mode (N.YM (W.L 1 u)) s := by
  ext x
  simp only [adE, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply]
  exact L1m_comm N hu s x

/-- The iterate `ad_{L(1)}ᵇ(u₍ₛ₎) = Σ_{a ≤ b} K p s b a (L(1)ᵃu)₍ₛ₊₍b−a₎₎`
(library coefficient `K`). -/
theorem adE_L1m_pow_mode {p : ℤ} {u : V} (hu : u ∈ W.grading p) (s : ℤ) (b : ℕ) :
    (adE (L1m N))^[b] (mode (N.YM u) s)
      = ∑ a ∈ Finset.range (b + 1),
          K p s b a • mode (N.YM (((W.L 1) ^ a) u)) (s + ((b - a : ℕ) : ℤ)) := by
  induction b generalizing s with
  | zero =>
      rw [Function.iterate_zero, id_eq, show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one]
      rw [show K p s 0 0 = 1 from by rw [K]; simp, one_smul]
      simp
  | succ b ih =>
      rw [Function.iterate_succ', Function.comp_apply, ih]
      rw [show adE (L1m N) (∑ a ∈ Finset.range (b + 1),
            K p s b a • mode (N.YM (((W.L 1) ^ a) u)) (s + ((b - a : ℕ) : ℤ)))
          = adEₗ (L1m N) (∑ a ∈ Finset.range (b + 1),
            K p s b a • mode (N.YM (((W.L 1) ^ a) u)) (s + ((b - a : ℕ) : ℤ))) from rfl]
      rw [map_sum]
      have hstep : ∀ a ∈ Finset.range (b + 1),
          adEₗ (L1m N) (K p s b a • mode (N.YM (((W.L 1) ^ a) u)) (s + ((b - a : ℕ) : ℤ)))
            = (K p s b a * ((2 * p - (a : ℤ) - (s : ℤ) - (b : ℤ) - 2 : ℤ) : ℂ))
                • mode (N.YM (((W.L 1) ^ a) u)) (s + ((b - a : ℕ) : ℤ) + 1)
              + K p s b a • mode (N.YM (((W.L 1) ^ (a + 1)) u)) (s + ((b - a : ℕ) : ℤ)) := by
        intro a ha
        rw [Finset.mem_range, Nat.lt_succ_iff] at ha
        have hmem : ((W.L 1) ^ a) u ∈ W.grading (p - (a : ℤ)) := L_one_pow_mem W hu a
        change adE (L1m N) _ = _
        rw [adE_smul, adE_L1m_mode N hmem (s + ((b - a : ℕ) : ℤ))]
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
theorem L1m_pow_mode_K {p : ℤ} {u : V} (hu : u ∈ W.grading p) (s : ℤ) (w : M) (t : ℕ) :
    (L1m N ^ t) (mode (N.YM u) s w)
      = ∑ k ∈ Finset.range (t + 1), ∑ a ∈ Finset.range (k + 1),
          ((t.choose k : ℂ) * K p s k a)
            • mode (N.YM (((W.L 1) ^ a) u)) (s + ((k - a : ℕ) : ℤ)) ((L1m N ^ (t - k)) w) := by
  have h := congrArg (fun A : Module.End ℂ M => A w) (pow_mul_eq_sum (L1m N) (mode (N.YM u) s) t)
  simp only [Module.End.mul_apply, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply] at h
  rw [h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [adE_L1m_pow_mode N hu s k]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
    smul_smul]

/-- The closed comultiplication coefficient. -/
noncomputable def comulCoeff (p s : ℤ) (a c b : ℕ) : ℂ :=
  ((a.factorial : ℂ)⁻¹ * (b.factorial : ℂ)⁻¹) * gBinom (2 * p - s - 2 - (a : ℤ)) c

/-- **The closed module comultiplication.**
`(t!)⁻¹ L(1)ᵗ(u₍ₛ₎w)`
`  = Σ_{k ≤ t} Σ_{a ≤ k} (a!)⁻¹((t−k)!)⁻¹ C(2p−s−2−a, k−a) (L(1)ᵃu)₍ₛ₊₍k−a₎₎ L(1)^{t−k} w`. -/
theorem comul_mode {p : ℤ} {u : V} (hu : u ∈ W.grading p) (s : ℤ) (w : M) (t : ℕ) :
    ((t.factorial : ℂ)⁻¹) • (L1m N ^ t) (mode (N.YM u) s w)
      = ∑ k ∈ Finset.range (t + 1), ∑ a ∈ Finset.range (k + 1),
          comulCoeff p s a (k - a) (t - k)
            • mode (N.YM (((W.L 1) ^ a) u)) (s + ((k - a : ℕ) : ℤ)) ((L1m N ^ (t - k)) w) := by
  rw [L1m_pow_mode_K N hu s w t, Finset.smul_sum]
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

end Comul

/-! ## Regrouping simplex sums -/

section Regroup

variable {E : Type*} [AddCommGroup E]

/-- A sum over the simplex `a + c + b < T` in `(t, k, a)` coordinates is the box sum, when the
summand vanishes off the simplex. -/
theorem simplex_eq_box (F : ℕ → ℕ → ℕ → E) (T : ℕ)
    (hF : ∀ a c b, T ≤ a + c + b → F a c b = 0) :
    ∑ t ∈ Finset.range T, ∑ k ∈ Finset.range (t + 1), ∑ a ∈ Finset.range (k + 1),
        F a (k - a) (t - k)
      = ∑ a ∈ Finset.range T, ∑ c ∈ Finset.range T, ∑ b ∈ Finset.range T, F a c b := by
  rw [Finset.sum_range_diag_flip T (fun k b => ∑ a ∈ Finset.range (k + 1), F a (k - a) b)]
  have h1 : ∀ k ∈ Finset.range T,
      ∑ b ∈ Finset.range (T - k), ∑ a ∈ Finset.range (k + 1), F a (k - a) b
        = ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range T, F a (k - a) b := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Finset.mem_range] at ha
    refine Finset.sum_subset (Finset.range_subset_range.mpr (Nat.sub_le T k)) (fun b hb hb' => ?_)
    rw [Finset.mem_range] at hb hb'
    exact hF a (k - a) b (by omega)
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_range_diag_flip T (fun a c => ∑ b ∈ Finset.range T, F a c b)]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.mem_range] at ha
  refine Finset.sum_subset (Finset.range_subset_range.mpr (Nat.sub_le T a)) (fun c hc hc' => ?_)
  rw [Finset.mem_range] at hc hc'
  exact Finset.sum_eq_zero (fun b _ => hF a c b (by omega))

end Regroup

/-! ## The summed comultiplication -/

section ComulSum

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {M : Type u} [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M)
  {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- **The summed comultiplication**: for any family of linear maps `G t`,
`Σᶠ_t (t!)⁻¹ G_t(L(1)ᵗ(u₍ₛ₎w))`
`  = Σ_{a,c,b} (a!)⁻¹(b!)⁻¹ C(2p−s−2−a, c) G_{a+c+b}((L(1)ᵃu)₍ₛ₊c₎ L(1)ᵇw)`,
the box bounds `P, C, J` being any bounds beyond which the summands vanish. -/
theorem comul_sum {p : ℤ} {u : V} (hu : u ∈ W.grading p) (s : ℤ) (w : M)
    (G : ℕ → M →ₗ[ℂ] E) (P C J : ℕ)
    (hP : ∀ a, P ≤ a → (W.L 1 ^ a) u = 0) (hJ : ∀ b, J ≤ b → (L1m N ^ b) w = 0)
    (hC : ∀ a b c : ℕ, C ≤ c →
      mode (N.YM ((W.L 1 ^ a) u)) (s + (c : ℤ)) ((L1m N ^ b) w) = 0) :
    ∑ᶠ t : ℕ, ((t.factorial : ℂ)⁻¹) • G t ((L1m N ^ t) (mode (N.YM u) s w))
      = ∑ a ∈ Finset.range P, ∑ c ∈ Finset.range C, ∑ b ∈ Finset.range J,
          comulCoeff p s a c b
            • G (a + c + b) (mode (N.YM ((W.L 1 ^ a) u)) (s + (c : ℤ)) ((L1m N ^ b) w)) := by
  set T : ℕ := P + C + J with hT
  set F : ℕ → ℕ → ℕ → E := fun a c b => comulCoeff p s a c b
      • G (a + c + b) (mode (N.YM ((W.L 1 ^ a) u)) (s + (c : ℤ)) ((L1m N ^ b) w)) with hF
  have hvec : ∀ a c b : ℕ, T ≤ a + c + b →
      mode (N.YM ((W.L 1 ^ a) u)) (s + (c : ℤ)) ((L1m N ^ b) w) = 0 := by
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
  have hexp : ∀ t : ℕ, ((t.factorial : ℂ)⁻¹) • G t ((L1m N ^ t) (mode (N.YM u) s w))
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
      ((t.factorial : ℂ)⁻¹) • G t ((L1m N ^ t) (mode (N.YM u) s w)) = 0 := by
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

end ComulSum

end VOA.Huang.ATransform
