/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJ47
import VOA.Modules.ZhuVermaAnArchMUFullRho

/-!
# `MUFullBracket` — Dong–Jiang Lemma 4.7 on `M(U)`, assembled

`ZhuVermaAnArchDJ47` proves the commutator identity at the level of a single graded piece, in all
three regimes (interior and the two boundary regimes).  This file does the level bookkeeping and the
`vloopBracket` assembly, delivering

  **`mUFullBracket_holds (W) (U) : MUFullBracket W U`**,

the `hbracket` input of `VHat.assembleModeData`.  Together with the already-unconditional `hderiv`
(`muFullActGen_hderiv`) this makes `muFullRho W U` a genuine `V̂`-representation with **no carried
hypothesis**.

## The level bookkeeping

For homogeneous `a, b` of weights `K, M`, source level `n` and modes `m, k`, put

  `T₂ = K − m − 1 + n` (the `a`-target), `T₁ = M − k − 1 + n` (the `b`-target),
  `T  = K + M − m − k − 2 + n = T₁ + T₂ − n` (the common target).

Every term of `∑ᵢ C(m,i)·(a₍ᵢ₎b)_{m+k−i}` also lands in level `T`, since `wt(a₍ᵢ₎b) = K+M−i−1`
makes the `i`-dependence cancel.  So:

* `T < 0` — everything vanishes;
* `T ≥ 0`, `T₁, T₂ ≥ 0` — the interior regime;
* `T ≥ 0`, `T₁ < 0` — then `T₂ > T + n ≥ 0`, boundary regime A (`a_m b_k = 0`);
* `T ≥ 0`, `T₂ < 0` — then `T₁ > T + n ≥ 0`, boundary regime B (`b_k a_m = 0`).

(`T₁` and `T₂` cannot both be negative when `T ≥ 0`, since `T = T₁ + T₂ − n ≤ −2`.)
In every regime the OPE exponent is the mode index `m` itself.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang math/0601626 §4 (Lemma 4.7); `ZhuVermaAnArchDJ47` (the three regimes),
`ZhuVermaAnArchMUFullMode` (`muFullMode`, `oLevelIncl`, `muFull_end_ext`),
`ZhuVermaAnArchMUFullRho` (`MUFullBracket`, `muFullActGen`), `ZhuVermaAnArchVhat`
(`vloopBracket`, `brLevel`), `ZhuVermaAnArchVHatModeData` (`assembleAct`).
-/

namespace VOA

open VertexOperatorAlgebra
open VHat
open Finsupp
open scoped TensorProduct DirectSum BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The OPE weight bookkeeping. -/

theorem smul_mem_grading (W : VertexOperatorAlgebra 𝒱) {K M : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading K) (hb : b ∈ W.grading M) (i : ℤ) :
    W.smul a i b ∈ W.grading (K + M - i - 1) := by
  rw [PreVertexAlgebra.smul_def]
  exact W.grading_mode a ha b hb i

/-! ## The commutator on a single graded piece. -/

/-- **DJ Lemma 4.7 on the level-`n` piece of `M(U)`**:
`a_m b_k x − b_k a_m x = ∑ᵢ C(m,i)·(a₍ᵢ₎b)_{m+k−i} x` for `x ∈ M(U)(n)`. -/
theorem muFullMode_commutator_incl (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {K M : ℕ} {a b : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hb : b ∈ W.grading (M : ℤ)) (m k : ℤ) (n : ℕ)
    (x : MUPieceFull W U n) :
    muFullMode W U m a (muFullMode W U k b (MUFull.incl W U n x))
        - muFullMode W U k b (muFullMode W U m a (MUFull.incl W U n x))
      = ∑ᶠ i : ℕ, gBinom m i •
          muFullMode W U (m + k - (i : ℤ)) (W.smul a (i : ℤ) b) (MUFull.incl W U n x) := by
  have hab : ∀ i : ℕ, W.smul a (i : ℤ) b ∈ W.grading ((K : ℤ) + (M : ℤ) - (i : ℤ) - 1) :=
    fun i => smul_mem_grading W ha hb (i : ℤ)
  have hTi : ∀ i : ℕ, muTargetLevel ((K : ℤ) + (M : ℤ) - (i : ℤ) - 1) (m + k - (i : ℤ)) n
      = (K : ℤ) + (M : ℤ) - m - k - 2 + (n : ℤ) := by
    intro i; simp only [muTargetLevel]; ring
  -- evaluation of a single mode application, in the two regimes
  have hEa : ∀ (s t : ℕ) (y : MUPieceFull W U s), (K : ℤ) - m - 1 + (s : ℤ) = (t : ℤ) →
      muFullMode W U m a (MUFull.incl W U s y) = MUFull.incl W U t (oFullU W U t s a y) := by
    intro s t y h
    rw [muFullMode_apply_incl W U m ha s y,
      oLevelIncl_eq_of_target W U (show muTargetLevel (K : ℤ) m s = (t : ℤ) from h) a,
      LinearMap.comp_apply]
  have hZa : ∀ (s : ℕ) (y : MUPieceFull W U s), (K : ℤ) - m - 1 + (s : ℤ) < 0 →
      muFullMode W U m a (MUFull.incl W U s y) = 0 := by
    intro s y h
    rw [muFullMode_apply_incl W U m ha s y,
      oLevelIncl_of_neg W U (show muTargetLevel (K : ℤ) m s < 0 from h) a, LinearMap.zero_apply]
  have hEb : ∀ (s t : ℕ) (y : MUPieceFull W U s), (M : ℤ) - k - 1 + (s : ℤ) = (t : ℤ) →
      muFullMode W U k b (MUFull.incl W U s y) = MUFull.incl W U t (oFullU W U t s b y) := by
    intro s t y h
    rw [muFullMode_apply_incl W U k hb s y,
      oLevelIncl_eq_of_target W U (show muTargetLevel (M : ℤ) k s = (t : ℤ) from h) b,
      LinearMap.comp_apply]
  have hZb : ∀ (s : ℕ) (y : MUPieceFull W U s), (M : ℤ) - k - 1 + (s : ℤ) < 0 →
      muFullMode W U k b (MUFull.incl W U s y) = 0 := by
    intro s y h
    rw [muFullMode_apply_incl W U k hb s y,
      oLevelIncl_of_neg W U (show muTargetLevel (M : ℤ) k s < 0 from h) b, LinearMap.zero_apply]
  by_cases hT : 0 ≤ (K : ℤ) + (M : ℤ) - m - k - 2 + (n : ℤ)
  · obtain ⟨N, hN⟩ : ∃ N : ℕ, (K : ℤ) + (M : ℤ) - m - k - 2 + (n : ℤ) = (N : ℤ) :=
      ⟨_, (Int.toNat_of_nonneg hT).symm⟩
    have hfinop := commSum_op_support_finite W U N n m a b x
    have hRHS : (∑ᶠ i : ℕ, gBinom m i •
          muFullMode W U (m + k - (i : ℤ)) (W.smul a (i : ℤ) b) (MUFull.incl W U n x))
        = MUFull.incl W U N (∑ᶠ i : ℕ, gBinom m i • oFullU W U N n (W.smul a (i : ℤ) b) x) := by
      rw [map_finsum (MUFull.incl W U N) hfinop]
      refine finsum_congr fun i => ?_
      rw [muFullMode_apply_incl W U _ (hab i) n x,
        oLevelIncl_eq_of_target W U (by rw [hTi i, hN]) (W.smul a (i : ℤ) b),
        LinearMap.comp_apply, map_smul]
    rw [hRHS]
    by_cases h1 : 0 ≤ (M : ℤ) - k - 1 + (n : ℤ)
    · obtain ⟨n₁, hn₁⟩ : ∃ t : ℕ, (M : ℤ) - k - 1 + (n : ℤ) = (t : ℤ) :=
        ⟨_, (Int.toNat_of_nonneg h1).symm⟩
      by_cases h2 : 0 ≤ (K : ℤ) - m - 1 + (n : ℤ)
      · -- INTERIOR
        obtain ⟨n₂, hn₂⟩ : ∃ t : ℕ, (K : ℤ) - m - 1 + (n : ℤ) = (t : ℤ) :=
          ⟨_, (Int.toNat_of_nonneg h2).symm⟩
        rw [hEb n n₁ x hn₁, hEa n n₂ x hn₂,
          hEa n₁ N _ (by omega), hEb n₂ N _ (by omega), ← map_sub]
        congr 1
        exact oFullU_comm_interior_gen W U ha b (by omega) (by omega) x
      · -- BOUNDARY B : the `a`-target is negative, so `b_k a_m = 0`
        rw [hEb n n₁ x hn₁, hZa n x (by omega), map_zero, sub_zero,
          hEa n₁ N _ (by omega)]
        congr 1
        exact oFullU_comm_bdryB_gen W U ha b (by omega) (by omega) x
    · -- BOUNDARY A : the `b`-target is negative, so `a_m b_k = 0`
      obtain ⟨n₂, hn₂⟩ : ∃ t : ℕ, (K : ℤ) - m - 1 + (n : ℤ) = (t : ℤ) :=
        ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
      rw [hZb n x (by omega), map_zero, hEa n n₂ x hn₂,
        hEb n₂ N _ (by omega), zero_sub, ← map_neg]
      congr 1
      exact oFullU_comm_bdryA_gen W U ha hb (by omega) (by omega) x
  · -- the common target is negative: everything vanishes
    push_neg at hT
    have hRHS0 : (∑ᶠ i : ℕ, gBinom m i •
        muFullMode W U (m + k - (i : ℤ)) (W.smul a (i : ℤ) b) (MUFull.incl W U n x)) = 0 := by
      refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
      rw [muFullMode_apply_incl W U _ (hab i) n x,
        oLevelIncl_of_neg W U (by rw [hTi i]; omega) (W.smul a (i : ℤ) b),
        LinearMap.zero_apply, smul_zero]
    rw [hRHS0, sub_eq_zero]
    have hz1 : muFullMode W U m a (muFullMode W U k b (MUFull.incl W U n x)) = 0 := by
      by_cases h1 : 0 ≤ (M : ℤ) - k - 1 + (n : ℤ)
      · obtain ⟨n₁, hn₁⟩ : ∃ t : ℕ, (M : ℤ) - k - 1 + (n : ℤ) = (t : ℤ) :=
          ⟨_, (Int.toNat_of_nonneg h1).symm⟩
        rw [hEb n n₁ x hn₁, hZa n₁ _ (by omega)]
      · rw [hZb n x (by omega), map_zero]
    have hz2 : muFullMode W U k b (muFullMode W U m a (MUFull.incl W U n x)) = 0 := by
      by_cases h2 : 0 ≤ (K : ℤ) - m - 1 + (n : ℤ)
      · obtain ⟨n₂, hn₂⟩ : ∃ t : ℕ, (K : ℤ) - m - 1 + (n : ℤ) = (t : ℤ) :=
          ⟨_, (Int.toNat_of_nonneg h2).symm⟩
        rw [hEa n n₂ x hn₂, hZb n₂ _ (by omega)]
      · rw [hZa n x (by omega), map_zero]
    rw [hz1, hz2]

/-! ## The `vloopBracket` side, evaluated. -/

/-- The `V̂`-bracket generator, evaluated on `M(U)`: `assembleAct` of
`[a(m), b(k)] = ∑ᵢ C(m,i)·(a₍ᵢ₎b)(m+k−i)` is the operator OPE tail. -/
theorem assembleAct_bracket_apply (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (a b : 𝒱) (m k : ℤ)
    (y : MUFull W U) :
    assembleAct (muFullActGen W U) (vloopBracket W (single m a) (single k b)) y
      = ∑ᶠ i : ℕ, gBinom m i • muFullMode W U (m + k - (i : ℤ)) (W.smul a (i : ℤ) b) y := by
  have hvb : vloopBracket W (single m a) (single k b)
      = ∑ᶠ i : ℕ, brLevel W m i a (single k b) := by
    rw [vloopBracket, Finsupp.lsum_single, bracketLeft_apply]
  have hfin : (Function.support fun i : ℕ => brLevel W m i a (single k b)).Finite :=
    brLevel_support_finite W m a (single k b)
  let ev : Module.End ℂ (MUFull W U) →ₗ[ℂ] MUFull W U :=
    { toFun := fun f => f y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h := map_finsum (ev.comp (assembleAct (muFullActGen W U))) hfin
  rw [hvb]
  show ev (assembleAct (muFullActGen W U) (∑ᶠ i : ℕ, brLevel W m i a (single k b))) = _
  rw [show ev (assembleAct (muFullActGen W U) (∑ᶠ i : ℕ, brLevel W m i a (single k b)))
      = ∑ᶠ i : ℕ, ev (assembleAct (muFullActGen W U) (brLevel W m i a (single k b))) from h]
  refine finsum_congr fun i => ?_
  rw [brLevel_single, map_smul, map_smul]
  show gBinom m i • ev (assembleAct (muFullActGen W U) (single (m + k - (i : ℤ))
      (W.smul a (i : ℤ) b))) = _
  rw [assembleAct_single]
  rfl

/-! ## `MUFullBracket`, unconditional. -/

/-- **DJ Lemma 4.7 on `M(U)`, in the `assembleModeData` form — unconditional.**

`assembleAct (muFullActGen W U) ([a(m), b(k)]) = ⁅a_m, b_k⁆` on `M(U)`.  This is the `hbracket`
input of `VHat.assembleModeData`; together with the already-unconditional `hderiv`
(`muFullActGen_hderiv`) it makes `muFullRho W U` a genuine `V̂`-representation with no carried
hypothesis. -/
theorem mUFullBracket_holds (W : VertexOperatorAlgebra 𝒱) (U : AMod W) : MUFullBracket W U := by
  intro a b m k
  -- reduce `a` to homogeneous
  refine reduce_homogeneous W (P := fun a =>
    assembleAct (muFullActGen W U) (vloopBracket W (single m a) (single k b))
      = ⁅muFullActGen W U m a, muFullActGen W U k b⁆) ?_ ?_ ?_ a
  · intro Ka a ha
    -- reduce `b` to homogeneous
    refine reduce_homogeneous W (P := fun b =>
      assembleAct (muFullActGen W U) (vloopBracket W (single m a) (single k b))
        = ⁅muFullActGen W U m a, muFullActGen W U k b⁆) ?_ ?_ ?_ b
    · intro Mb b hb
      -- negative weights force the vector to be `0`
      rcases lt_or_ge Ka 0 with hKneg | hKpos
      · have ha0 : a = 0 := by
          have := W.positivity Ka hKneg
          rw [this, Submodule.mem_bot] at ha; exact ha
        subst ha0
        simp only [Finsupp.single_zero, map_zero, LinearMap.zero_apply, zero_lie]
      rcases lt_or_ge Mb 0 with hMneg | hMpos
      · have hb0 : b = 0 := by
          have := W.positivity Mb hMneg
          rw [this, Submodule.mem_bot] at hb; exact hb
        subst hb0
        simp only [Finsupp.single_zero, map_zero, LinearMap.zero_apply, lie_zero]
      obtain ⟨K, rfl⟩ := Int.eq_ofNat_of_zero_le hKpos
      obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le hMpos
      -- the core: agree on every graded piece
      refine muFull_end_ext W U (fun n x => ?_)
      rw [assembleAct_bracket_apply W U a b m k]
      show _ = (muFullActGen W U m a * muFullActGen W U k b
        - muFullActGen W U k b * muFullActGen W U m a) (MUFull.incl W U n x)
      rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
      exact (muFullMode_commutator_incl W U ha hb m k n x).symm
    · simp only [Finsupp.single_zero, map_zero, LinearMap.zero_apply, lie_zero]
    · intro x y hx hy
      simp only [Finsupp.single_add, map_add, LinearMap.add_apply, lie_add] at *
      rw [hx, hy]
  · simp only [Finsupp.single_zero, map_zero, LinearMap.zero_apply, zero_lie]
  · intro x y hx hy
    simp only [Finsupp.single_add, map_add, LinearMap.add_apply, add_lie] at *
    rw [hx, hy]

/-! ## `M(U)` as an unconditional `V̂`-representation. -/

/-- **DJ's `M(U)` `V̂`-representation, unconditional.** -/
noncomputable def muFullRhoU (W : VertexOperatorAlgebra 𝒱) (U : AMod W) :
    VHat.VHatRep W (MUFull W U) :=
  muFullRho W U (mUFullBracket_holds W U)

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.muFullMode_commutator_incl
  #print axioms VOA.assembleAct_bracket_apply
  #print axioms VOA.mUFullBracket_holds
  #print axioms VOA.muFullRhoU
-/
