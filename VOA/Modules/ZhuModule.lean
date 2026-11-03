/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuAlgebra
import VOA.Modules.ZeroModeMult

/-!
# Toward Theorem 5.3.4 — the Zhu residue recursion and the `A(𝒱)`-action on `M_h`

Two genuine, axiom-free advances toward Zhu's Theorem 5.3.4 (Gannon §5.3.2):

* **The higher-pole residue recursion `(★)`** (`Pres_mem_O`, Frenkel–Zhu Lemma 2.1.2): for
  homogeneous `a ∈ 𝒱_M` and all `n`, `∑_i C(M+n,i)·a₍ᵢ₋₂₋ₙ₎b ∈ O(𝒱)`. Proved by induction on `n`
  off the base residue `(L₋₁a+L₀a)*b = ∑_i C(M,i)·a₍ᵢ₋₂₎b` (`zhuMul_L_base`, `residue_base_mem_O`)
  and the integration-by-parts step `(n+2)·Pres(n+1) = Pres(L₋₁a)(M+1)(n) + (M+n+1)·Pres(n)`. This
  is the key technical input to Zhu's two-sided-ideal + associativity theorem (Thm 2.1.1/2.1.2).

* **Theorem 5.3.4, the easy direction** (`actA`): for a graded `𝒱`-module `N` with a lowest-weight
  space `M_h` (`IsLowestWeight N h`), the zero-mode representation `ρ_h : u ↦ o(u)|_{M_h}`
  descends through `A(𝒱) = 𝒱 ⧸ O(𝒱)` to a `ℂ`-linear action `actA : A(𝒱) →ₗ End ℂ M_h`,
  *well-defined* (`O_le_ker_rhoLW`, from 5.3.9b) and *unital + multiplicative on representable
  products* (`actA_one`, `actA_mk_mul`, from 5.3.9a). The 5.3.9a/b results are lifted from
  homogeneous to all `u, v` (`oMod_zhuMul_lowest_all`, via `iSup_induction` + `W.positivity`).

## Status
Axiom-clean for `(★)`, the easy-direction action, and the upgrade to a genuine `A(𝒱)`-module.
**`Pres_mem_O`**, **`actA`** (+ `actA_one`/`actA_mk_mul`/`O_le_ker_rhoLW`/`rhoLW_zhuMul`) are
`[propext, Classical.choice, Quot.sound]`.

**The `Ring (A 𝒱)` instance is available** (Zhu Thm 2.1.1/2.1.2 proved unconditionally in
`Modules.ZhuRingInstance`, off the associator-membership `(u*v)*w − u*(v*w) ∈ O` =
`ZhuAssociator.associator_core` and the right-ideal `ZhuRightIdeal.right_ideal_core`), so **`actA`
is a genuine `Module (A 𝒱) M_h`** (`ZhuRingInstance.moduleMh`) — Theorem 5.3.4's easy direction
complete, axiom-free.

**Not proved in this file:** the **5.3.4 bijection hard direction**: the
generalized-Verma lift `U ↦ M(U)`, `Φ(𝒱) ↔ Irr A(𝒱)` (the induced module is built in the
`ZhuVermaAn*` files).

## References
* Gannon §5.3.2, Thm 5.3.4, eqs. (5.3.8)–(5.3.10); Zhu [574]; Frenkel–Zhu Lemma 2.1.2.
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators
open Classical

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Homogeneous collapse of `zhuMul` -/

/-- On a homogeneous `u ∈ 𝒱ₖ`, `u * v = ∑_{m} C(k,m) u₍ₘ₋₁₎ v` (the single weight slice). -/
theorem zhuMul_homogeneous' (W : VertexOperatorAlgebra 𝒱) {k : ℤ} {u : 𝒱}
    (hu : u ∈ W.grading k) (v : 𝒱) :
    zhuMul W u v
      = ∑ m ∈ Finset.range (k.toNat + 1), cbz k m • W.smul u ((m : ℤ) - 1) v :=
  zhuMul_homogeneous W hu v

/-! ## Left/right Zhu multiplication as linear maps -/

/-- Right multiplication `v ↦ u * v` as a `ℂ`-linear map. -/
noncomputable def zhuR (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) : 𝒱 →ₗ[ℂ] 𝒱 where
  toFun v := zhuMul W u v
  map_add' := zhuMul_add_right W u
  map_smul' c v := zhuMul_smul_right W c u v

/-- Left multiplication `u ↦ u * v` as a `ℂ`-linear map. -/
noncomputable def zhuL (W : VertexOperatorAlgebra 𝒱) (v : 𝒱) : 𝒱 →ₗ[ℂ] 𝒱 where
  toFun u := zhuMul W u v
  map_add' u₁ u₂ := zhuMul_add_left W u₁ u₂ v
  map_smul' c u := zhuMul_smul_left W c u v

@[simp] theorem zhuR_apply (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    zhuR W u v = zhuMul W u v := rfl

@[simp] theorem zhuL_apply (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    zhuL W v u = zhuMul W u v := rfl

@[simp] theorem zhuMul_zero_left (W : VertexOperatorAlgebra 𝒱) (v : 𝒱) :
    zhuMul W 0 v = 0 := (zhuL W v).map_zero

@[simp] theorem zhuMul_zero_right (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) :
    zhuMul W u 0 = 0 := (zhuR W u).map_zero

/-! ## Generating set of `O W` -/

/-- The generating set of `O W`: `{ (L₋₁a+L₀a)*b }`. -/
def Ogen (W : VertexOperatorAlgebra 𝒱) : Set 𝒱 :=
  {x | ∃ u v : 𝒱, x = zhuMul W (W.L (-1) u + W.L 0 u) v}

theorem O_eq_span (W : VertexOperatorAlgebra 𝒱) : O W = Submodule.span ℂ (Ogen W) := rfl

theorem gen_mem_O (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) :
    zhuMul W (W.L (-1) a + W.L 0 a) b ∈ O W :=
  Submodule.subset_span ⟨a, b, rfl⟩

/-! ## Reduction principles for the ideal properties -/

theorem right_ideal_of_gen (W : VertexOperatorAlgebra 𝒱) (u : 𝒱)
    (hgen : ∀ g ∈ Ogen W, zhuMul W u g ∈ O W) :
    ∀ v ∈ O W, zhuMul W u v ∈ O W := by
  intro v hv
  have hle : O W ≤ (O W).comap (zhuR W u) := by
    rw [O_eq_span, Submodule.span_le]
    intro g hg
    simpa [Submodule.mem_comap] using hgen g hg
  have : v ∈ (O W).comap (zhuR W u) := hle hv
  simpa [Submodule.mem_comap] using this

theorem left_ideal_of_gen (W : VertexOperatorAlgebra 𝒱) (v : 𝒱)
    (hgen : ∀ g ∈ Ogen W, zhuMul W g v ∈ O W) :
    ∀ u ∈ O W, zhuMul W u v ∈ O W := by
  intro u hu
  have hle : O W ≤ (O W).comap (zhuL W v) := by
    rw [O_eq_span, Submodule.span_le]
    intro g hg
    simpa [Submodule.mem_comap] using hgen g hg
  have : u ∈ (O W).comap (zhuL W v) := hle hu
  simpa [Submodule.mem_comap] using this

/-! ## `(L₋₁a)₍ₙ₎b = -n·a₍ₙ₋₁₎b` -/

theorem smul_L_neg_one (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) (n : ℤ) :
    W.smul (W.L (-1) a) n b = (-n) • W.smul a (n - 1) b := by
  rw [← L_neg_one_deriv]
  have h := L_comm_mode W a n
  have h2 := LinearMap.congr_fun h b
  rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, LinearMap.smul_apply] at h2
  exact h2

/-! ## Scalar combinatorics -/

/-- **Lower absorption** `i·C(M,i) = (M-i+1)·C(M,i-1)`. -/
theorem cbz_absorption (M : ℕ) (i : ℤ) :
    cbz (M : ℤ) i * (i : ℂ) = cbz (M : ℤ) (i - 1) * ((M : ℂ) - i + 1) := by
  rcases lt_or_ge i 1 with hi | hi
  · rcases lt_or_eq_of_le (by omega : i ≤ 0) with hlt | heq
    · rw [cbz_apply_neg (M : ℤ) hlt, cbz_apply_neg (M : ℤ) (by omega : i - 1 < 0)]; ring
    · subst heq
      rw [cbz_apply_neg (M : ℤ) (by omega : (0 : ℤ) - 1 < 0)]
      simp
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = (j : ℤ) + 1 := ⟨(i - 1).toNat, by omega⟩
    rw [cbz_apply_nonneg (M : ℤ) (by omega : (0 : ℤ) ≤ (j : ℤ) + 1),
        cbz_apply_nonneg (M : ℤ) (by omega : (0 : ℤ) ≤ (j : ℤ) + 1 - 1),
        show ((j : ℤ) + 1).toNat = j + 1 from by omega,
        show ((j : ℤ) + 1 - 1).toNat = j from by omega]
    have e1 := gBinom_mul_factorial (M : ℤ) (j + 1)
    have e2 := gBinom_mul_factorial (M : ℤ) j
    simp only [Int.cast_natCast] at e1 e2
    have hpeel : (∏ p ∈ Finset.range (j + 1), ((M : ℂ) - (p : ℂ)))
        = (∏ p ∈ Finset.range j, ((M : ℂ) - (p : ℂ))) * ((M : ℂ) - (j : ℂ)) := by
      rw [Finset.prod_range_succ]
    have hjfac : ((j.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    refine mul_left_cancel₀ hjfac ?_
    rw [show ((j : ℤ) + 1 : ℤ) = ((j : ℕ) : ℤ) + 1 from rfl]
    push_cast
    have lhs_eq : (j.factorial : ℂ) * (gBinom (M : ℤ) (j + 1) * ((j : ℂ) + 1))
        = ∏ p ∈ Finset.range (j + 1), ((M : ℂ) - (p : ℂ)) := by
      have : ((j + 1).factorial : ℂ) = (j.factorial : ℂ) * ((j : ℂ) + 1) := by
        rw [Nat.factorial_succ]; push_cast; ring
      rw [← e1, this]; ring
    have rhs_eq : (j.factorial : ℂ) * (gBinom (M : ℤ) j * ((M : ℂ) - ((j : ℂ) + 1) + 1))
        = (∏ p ∈ Finset.range j, ((M : ℂ) - (p : ℂ))) * ((M : ℂ) - (j : ℂ)) := by
      rw [show (j.factorial : ℂ) * (gBinom (M : ℤ) j * ((M : ℂ) - ((j : ℂ) + 1) + 1))
          = ((j.factorial : ℂ) * gBinom (M : ℤ) j) * ((M : ℂ) - (j : ℂ)) from by ring, ← e2]
    rw [lhs_eq, rhs_eq, hpeel]

/-- **Upper absorption** `i·C(K,i) = K·C(K-1,i-1)`  (for `K : ℕ`, `i : ℤ`). -/
theorem cbz_upper_absorption (K : ℕ) (i : ℤ) :
    (i : ℂ) * cbz (K : ℤ) i = (K : ℂ) * cbz ((K : ℤ) - 1) (i - 1) := by
  -- Use lower absorption + Pascal to relate cbz K and cbz (K-1).
  -- i·C(K,i) = (K-i+1)·C(K,i-1)  (cbz_absorption)
  -- Want: i·C(K,i) = K·C(K-1,i-1).  Equivalent to (K-i+1)C(K,i-1) = K·C(K-1,i-1).
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    -- K = 0: C(0,i)= δ_{i,0}, C(-1,i-1).  i·C(0,i): nonzero only i=0 ⟹ 0. RHS 0.
    simp only [Nat.cast_zero, zero_mul]
    rcases eq_or_ne i 0 with h0 | h0
    · subst h0; simp
    · rcases lt_or_gt_of_ne h0 with hlt | hgt
      · rw [cbz_apply_neg (0 : ℤ) hlt, mul_zero]
      · rw [cbz_lt (le_refl 0) (by omega : (0 : ℤ) < i), mul_zero]
  · -- K ≥ 1. Pascal: cbz K i = cbz (K-1) i + cbz (K-1) (i-1).
    have hpasc : cbz (K : ℤ) i = cbz ((K : ℤ) - 1) i + cbz ((K : ℤ) - 1) (i - 1) :=
      cbz_pascal (K : ℤ) i
    have hpasc2 : cbz (K : ℤ) (i - 1)
        = cbz ((K : ℤ) - 1) (i - 1) + cbz ((K : ℤ) - 1) (i - 1 - 1) :=
      cbz_pascal (K : ℤ) (i - 1)
    -- lower absorption at K:  cbz K i · i = cbz K (i-1) · (K - i + 1)
    have habs := cbz_absorption K i
    -- lower absorption at (K-1) : need integer K-1 ≥ 0. Write K-1 = (K-1 : ℕ).
    obtain ⟨K', rfl⟩ : ∃ K' : ℕ, K = K' + 1 := ⟨K - 1, by omega⟩
    have habs' := cbz_absorption K' i  -- cbz K' i · i = cbz K' (i-1) · (K' - i + 1)
    -- now relate: cbz (K'+1) · and cbz K'.  ((K'+1):ℤ)-1 = K'.
    rw [show ((K' + 1 : ℕ) : ℤ) - 1 = (K' : ℤ) from by push_cast; ring]
    -- Goal: i · cbz (K'+1) i = (K'+1)·cbz K' (i-1).
    -- From Pascal: cbz (K'+1) i = cbz K' i + cbz K' (i-1).
    have hpasc3 : cbz ((K' + 1 : ℕ) : ℤ) i = cbz (K' : ℤ) i + cbz (K' : ℤ) (i - 1) := by
      have := cbz_pascal ((K' + 1 : ℕ) : ℤ) i
      rwa [show ((K' + 1 : ℕ) : ℤ) - 1 = (K' : ℤ) from by push_cast; ring] at this
    rw [hpasc3, mul_add]
    -- i·cbz K' i  = cbz K' (i-1)·(K'-i+1)   [habs' rearranged]
    -- i·cbz K' (i-1) = ?  use lower absorption at K' with index i-1:
    have habs'' := cbz_absorption K' (i - 1)
    -- cbz K' (i-1)·(i-1) = cbz K' (i-2)·(K'-(i-1)+1)
    -- We want  i·cbz K' i + i·cbz K' (i-1) = (K'+1)·cbz K' (i-1).
    -- i·cbz K' i = (K'-i+1)·cbz K' (i-1) [from habs', commuted].
    have key1 : (i : ℂ) * cbz (K' : ℤ) i = ((K' : ℂ) - i + 1) * cbz (K' : ℤ) (i - 1) := by
      rw [mul_comm (i : ℂ), habs']; ring
    rw [key1]
    push_cast
    ring

/-- **Per-coefficient base Zhu identity** (Pascal + lower absorption). -/
theorem cbz_coeff_identity (M : ℕ) (i : ℤ) :
    cbz ((M : ℤ) + 1) i * (-((i : ℂ) - 1)) + (M : ℂ) * cbz (M : ℤ) (i - 1)
      = cbz (M : ℤ) i := by
  have hpascal := cbz_pascal ((M : ℤ) + 1) i
  rw [show ((M : ℤ) + 1 - 1) = (M : ℤ) from by ring] at hpascal
  have habs := cbz_absorption M i
  rw [hpascal]
  push_cast at habs
  linear_combination (-1 : ℂ) * habs

/-- `L₋₁a ∈ 𝒱_{M+1}` for `a ∈ 𝒱_M`. -/
theorem L_neg_one_mem_grading_succ (W : VertexOperatorAlgebra 𝒱) {M : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading M) : W.L (-1) a ∈ W.grading (M + 1) := by
  have heq : W.L (-1) a = W.smul W.conformalVector 0 a := by
    rw [VertexOperatorAlgebra.L_def, PreVertexAlgebra.smul_def,
      show ((-1 : ℤ) + 1) = 0 from by ring]
  have h := W.smul_mem_grading W.conformalVector_mem_grading_two ha 0
  rw [show (2 + M - 0 - 1 : ℤ) = M + 1 from by ring] at h
  rwa [← heq] at h

/-- **The Zhu base-residue identity** (FZ Lemma 2.1.1, k=0): for `a ∈ 𝒱_M`,
`(L₋₁a + L₀a) * b = ∑_{i=0}^{M} C(M,i) · a₍ᵢ₋₂₎ b`. -/
theorem zhuMul_L_base (W : VertexOperatorAlgebra 𝒱) {M : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (M : ℤ)) (b : 𝒱) :
    zhuMul W (W.L (-1) a + W.L 0 a) b
      = ∑ i ∈ Finset.range (M + 1), cbz (M : ℤ) (i : ℤ) • W.smul a ((i : ℤ) - 2) b := by
  rw [zhuMul_add_left]
  have hL0 : W.L 0 a = (M : ℂ) • a := W.L_zero_grading a ha
  have hT2 : zhuMul W (W.L 0 a) b
      = ∑ i ∈ Finset.range (M + 2),
          ((M : ℂ) * cbz (M : ℤ) ((i : ℤ) - 1)) • W.smul a ((i : ℤ) - 2) b := by
    rw [hL0, zhuMul_smul_left, zhuMul_homogeneous W ha b,
      show ((M : ℤ).toNat + 1) = M + 1 from by simp, Finset.smul_sum]
    rw [Finset.sum_range_succ' (fun i => ((M : ℂ) * cbz (M : ℤ) ((i : ℤ) - 1)) •
        W.smul a ((i : ℤ) - 2) b) (M + 1)]
    rw [show cbz (M : ℤ) ((0 : ℕ) - 1 : ℤ) = 0 from cbz_apply_neg _ (by norm_num),
      mul_zero, zero_smul, add_zero]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [smul_smul]
    congr 2
    · push_cast; ring_nf
    · push_cast; ring_nf
  have hT1 : zhuMul W (W.L (-1) a) b
      = ∑ i ∈ Finset.range (M + 2),
          (cbz ((M : ℤ) + 1) (i : ℤ) * (-((i : ℂ) - 1))) • W.smul a ((i : ℤ) - 2) b := by
    rw [zhuMul_homogeneous W (L_neg_one_mem_grading_succ W ha) b,
      show (((M : ℤ) + 1).toNat + 1) = M + 2 from by omega]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_L_neg_one W a b ((i : ℤ) - 1),
      show ((i : ℤ) - 1 - 1) = (i : ℤ) - 2 from by ring,
      ← Int.cast_smul_eq_zsmul ℂ (-((i : ℤ) - 1)) (W.smul a ((i : ℤ) - 2) b), smul_smul]
    congr 2
    push_cast
    ring
  rw [hT1, hT2, ← Finset.sum_add_distrib]
  have hcombine : ∀ i ∈ Finset.range (M + 2),
      (cbz ((M : ℤ) + 1) (i : ℤ) * (-((i : ℂ) - 1))) • W.smul a ((i : ℤ) - 2) b
        + ((M : ℂ) * cbz (M : ℤ) ((i : ℤ) - 1)) • W.smul a ((i : ℤ) - 2) b
        = cbz (M : ℤ) (i : ℤ) • W.smul a ((i : ℤ) - 2) b := by
    intro i _
    rw [← add_smul]
    congr 1
    have := cbz_coeff_identity M (i : ℤ)
    push_cast at this
    convert this using 3
  rw [Finset.sum_congr rfl hcombine, Finset.sum_range_succ]
  rw [show cbz (M : ℤ) ((M + 1 : ℕ) : ℤ) = 0 from cbz_lt (by positivity) (by exact_mod_cast by omega),
    zero_smul, add_zero]

/-- **Base-residue membership** (FZ Lemma 2.1.1, k=0): for `a ∈ 𝒱_M`,
`∑_{i=0}^{M} C(M,i) a₍ᵢ₋₂₎ b ∈ O W`. -/
theorem residue_base_mem_O (W : VertexOperatorAlgebra 𝒱) {M : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (M : ℤ)) (b : 𝒱) :
    (∑ i ∈ Finset.range (M + 1), cbz (M : ℤ) (i : ℤ) • W.smul a ((i : ℤ) - 2) b) ∈ O W := by
  rw [← zhuMul_L_base W ha b]
  exact gen_mem_O W a b

/-! ## The higher-pole residue recursion (★)

For homogeneous `a ∈ 𝒱_M`, define the depth-`n` residue
`Pres a M n b := ∑_{i=0}^{M+n} C(M+n,i) · a₍ᵢ₋₂₋ₙ₎ b   (= Res_z Y(a,z)b (1+z)^{M+n}/z^{2+n})`.
We prove `Pres … ∈ O W` for all `n` by induction (Frenkel–Zhu Lemma 2.1.2). -/

/-- The depth-`n` Zhu residue `∑_{i} C(M+n,i) a₍ᵢ₋₂₋ₙ₎ b`. -/
noncomputable def Pres (W : VertexOperatorAlgebra 𝒱) (M : ℕ) (a b : 𝒱) (n : ℕ) : 𝒱 :=
  ∑ i ∈ Finset.range (M + n + 1), cbz ((M : ℤ) + n) (i : ℤ) • W.smul a ((i : ℤ) - 2 - n) b

/-- The per-outer-index scalar identity driving the recursion:
`(n+2)·C(M+n+1,i) = C(M+n+1,i)·(-(i-2-n)) + (M+n+1)·C(M+n,i-1)`. -/
theorem pres_coeff_identity (M n : ℕ) (i : ℤ) :
    ((n : ℂ) + 2) * cbz ((M : ℤ) + n + 1) i
      = cbz ((M : ℤ) + n + 1) i * (-((i : ℂ) - 2 - n))
        + ((M : ℂ) + n + 1) * cbz ((M : ℤ) + n) (i - 1) := by
  -- reduces to upper absorption: i·C(M+n+1,i) = (M+n+1)·C(M+n,i-1).
  have hua := cbz_upper_absorption (M + n + 1) i
  rw [show ((((M + n + 1 : ℕ)) : ℤ) - 1) = (M : ℤ) + n from by push_cast; ring,
      show (((M + n + 1 : ℕ)) : ℤ) = (M : ℤ) + n + 1 from by push_cast; ring] at hua
  push_cast at hua ⊢
  linear_combination hua

/-- **(★) Higher-pole residue membership** (Frenkel–Zhu Lemma 2.1.2): for homogeneous
`a ∈ 𝒱_M` and all `n`, `Pres a M n b = ∑_i C(M+n,i) a₍ᵢ₋₂₋ₙ₎ b ∈ O W`. -/
theorem Pres_mem_O (W : VertexOperatorAlgebra 𝒱) {M : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (M : ℤ)) (b : 𝒱) (n : ℕ) : Pres W M a b n ∈ O W := by
  induction n generalizing M a with
  | zero =>
    -- base case: Pres a M 0 = ∑ C(M,i) a₍ᵢ₋₂₎b = residue_base_mem_O.
    have hb := residue_base_mem_O W ha b
    have heq : Pres W M a b 0
        = ∑ i ∈ Finset.range (M + 1), cbz (M : ℤ) (i : ℤ) • W.smul a ((i : ℤ) - 2) b := by
      unfold Pres
      rw [Nat.add_zero]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show ((M : ℤ) + (0 : ℕ)) = (M : ℤ) from by push_cast; ring,
        show ((i : ℤ) - 2 - (0 : ℕ)) = (i : ℤ) - 2 from by push_cast; ring]
    rw [heq]; exact hb
  | succ n ih =>
    -- inductive step: (n+2)•Pres(n+1) = G_n + (M+n+1)•Pres(n), with
    --   G_n := Pres (L₋₁a) (M+1) n ∈ O (IH applied to L₋₁a ∈ 𝒱_{M+1}),
    --   Pres a M n ∈ O (IH).
    -- Hence Pres(n+1) = (1/(n+2))•[G_n + (M+n+1)•Pres(n)] ∈ O.
    have haL : W.L (-1) a ∈ W.grading ((M : ℤ) + 1) := L_neg_one_mem_grading_succ W ha
    -- IH for L₋₁a at level M+1:
    have hG : Pres W (M + 1) (W.L (-1) a) b n ∈ O W := by
      have := ih (M := M + 1) (a := W.L (-1) a) (by
        rwa [show (((M + 1 : ℕ)) : ℤ) = (M : ℤ) + 1 from by push_cast; ring])
      exact this
    have hP : Pres W M a b n ∈ O W := ih ha
    -- Express G_n with (L₋₁a)₍·₎ expanded to a₍·₎ via smul_L_neg_one.
    -- G_n = ∑_{i∈range(M+n+2)} cbz(M+1+n,i)·(-(i-2-n)) • a₍ᵢ₋₃₋ₙ₎b.
    have hGeq : Pres W (M + 1) (W.L (-1) a) b n
        = ∑ i ∈ Finset.range (M + n + 2),
            (cbz ((M : ℤ) + n + 1) (i : ℤ) * (-((i : ℂ) - 2 - n)))
              • W.smul a ((i : ℤ) - 3 - n) b := by
      unfold Pres
      rw [show M + 1 + n + 1 = M + n + 2 from by ring]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hcast1 : (((M + 1 : ℕ) : ℤ)) + (n : ℤ) = (M : ℤ) + n + 1 := by push_cast; ring
      rw [hcast1, smul_L_neg_one W a b ((i : ℤ) - 2 - n),
        show ((i : ℤ) - 2 - n - 1) = (i : ℤ) - 3 - n from by ring,
        ← Int.cast_smul_eq_zsmul ℂ (-((i : ℤ) - 2 - n)) (W.smul a ((i : ℤ) - 3 - n) b), smul_smul]
      congr 2
      push_cast
      ring
    -- Now the cleared sum identity:
    --   (n+2)•Pres(n+1) = G_n + (M+n+1)•Pres(n)  (all over range(M+n+2), inner mode a₍ᵢ₋₃₋ₙ₎b).
    have hsum : ((n : ℂ) + 2) • Pres W M a b (n + 1)
        = Pres W (M + 1) (W.L (-1) a) b n + ((M : ℂ) + n + 1) • Pres W M a b n := by
      rw [hGeq]
      -- expand (n+2)•Pres(n+1)
      have hLHS : ((n : ℂ) + 2) • Pres W M a b (n + 1)
          = ∑ i ∈ Finset.range (M + n + 2),
              (((n : ℂ) + 2) * cbz ((M : ℤ) + (n + 1)) (i : ℤ))
                • W.smul a ((i : ℤ) - 2 - (n + 1)) b := by
        unfold Pres
        rw [show M + (n + 1) + 1 = M + n + 2 from by ring, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [smul_smul]
        congr 2 <;> push_cast <;> ring
      -- expand (M+n+1)•Pres(n), reindex k ↦ i-1 onto range(M+n+2).
      have hPn : ((M : ℂ) + n + 1) • Pres W M a b n
          = ∑ i ∈ Finset.range (M + n + 2),
              (((M : ℂ) + n + 1) * cbz ((M : ℤ) + n) ((i : ℤ) - 1))
                • W.smul a ((i : ℤ) - 3 - n) b := by
        unfold Pres
        rw [Finset.smul_sum]
        -- shift the index: range(M+n+1) → range(M+n+2) via sum_range_succ' (drop the new bottom i=0).
        rw [Finset.sum_range_succ' (fun i => (((M : ℂ) + n + 1) * cbz ((M : ℤ) + n) ((i : ℤ) - 1))
            • W.smul a ((i : ℤ) - 3 - n) b) (M + n + 1)]
        -- bottom i=0 term: cbz(M+n,-1)=0
        rw [show cbz ((M : ℤ) + n) ((0 : ℕ) - 1 : ℤ) = 0 from cbz_apply_neg _ (by norm_num),
          mul_zero, zero_smul, add_zero]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [smul_smul]
        congr 2
        · push_cast; ring_nf
        · push_cast; ring_nf
      rw [hLHS, hPn, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hmode : ((i : ℤ) - 2 - ((n : ℤ) + 1)) = (i : ℤ) - 3 - n := by push_cast; ring
      rw [show ((M : ℤ) + ((n : ℤ) + 1)) = (M : ℤ) + n + 1 from by push_cast; ring, hmode,
        ← add_smul]
      congr 1
      have := pres_coeff_identity M n (i : ℤ)
      push_cast at this ⊢
      linear_combination this
    -- conclude: Pres(n+1) = (1/(n+2))•RHS ∈ O.
    have hne : ((n : ℂ) + 2) ≠ 0 := by
      have : ((n : ℂ) + 2) = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
      rw [this]; exact_mod_cast Nat.succ_ne_zero (n + 1)
    have : Pres W M a b (n + 1)
        = (((n : ℂ) + 2)⁻¹) • (Pres W (M + 1) (W.L (-1) a) b n + ((M : ℂ) + n + 1) • Pres W M a b n) := by
      rw [← hsum, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ hG (Submodule.smul_mem _ _ hP))

/-! ## (D) Theorem 5.3.4 — the easy direction: `M_h` is an `A(W)`-module.

For a `ℂ`-graded module `N` with lowest weight `h` (`IsLowestWeight N h`), the lowest-weight
space `M_h = N.weight h` carries an `A(W)`-module structure `[u]·x := o(u) x`, well-defined
because `o` kills `O(W)` on `M_h` (`oMod_L_translation` 5.3.9b) and multiplicative
(`oMod_zhuMul_lowest` 5.3.9a). -/

section EasyDirection

variable {Mod : Type u} [AddCommGroup Mod] [Module ℂ Mod] {W : VertexOperatorAlgebra 𝒱}

/-- `o(L₋₁a + L₀a) = 0` for **all** `a` (Gannon 5.3.9b, dropping homogeneity by linearity). -/
theorem oMod_L_translation_all (N : OrdVModule W Mod) (a : 𝒱) :
    oMod N (W.L (-1) a + W.L 0 a) = 0 := by
  have hatop : a ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun a => oMod N (W.L (-1) a + W.L 0 a) = 0) hatop ?_ ?_ ?_
  · intro i x hx
    exact oMod_L_translation N hx
  · simp only [map_zero, add_zero]
  · intro x y hx hy
    rw [show (W.L (-1)) (x + y) + (W.L 0) (x + y)
        = ((W.L (-1)) x + (W.L 0) x) + ((W.L (-1)) y + (W.L 0) y) from by
      simp only [map_add]; abel, map_add, hx, hy, add_zero]

/-- `o(u)` preserves the lowest-weight space `M_h` for **all** `u` (by linearity in `u`). -/
theorem oMod_preserves_lowest_all (N : OrdVModule W Mod) {h : ℂ} (u : 𝒱) {x : Mod}
    (hx : x ∈ N.weight h) : oMod N u x ∈ N.weight h := by
  have hutop : u ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun u => oMod N u x ∈ N.weight h) hutop ?_ ?_ ?_
  · intro i y hy
    exact oMod_preserves_lowest N hy hx
  · show oMod N 0 x ∈ N.weight h
    rw [map_zero, LinearMap.zero_apply]; exact (N.weight h).zero_mem
  · intro y z hy hz
    show oMod N (y + z) x ∈ N.weight h
    rw [map_add, LinearMap.add_apply]; exact (N.weight h).add_mem hy hz

end EasyDirection

section EasyDirection2

variable {Mod : Type u} [AddCommGroup Mod] [Module ℂ Mod] {W : VertexOperatorAlgebra 𝒱}

/-- `o(u*v) x = o(u)(o(v) x)` on `M_h` for **all** `u, v` (Gannon 5.3.9a, dropping homogeneity
by bilinearity; negative grades vanish, so the `a,β ≥ 0` hypotheses are automatic). -/
theorem oMod_zhuMul_lowest_all (N : OrdVModule W Mod) {h : ℂ} (hcw : IsLowestWeight N h)
    (u v : 𝒱) {x : Mod} (hx : x ∈ N.weight h) :
    oMod N (zhuMul W u v) x = oMod N u (oMod N v x) := by
  have hutop : u ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun u => oMod N (zhuMul W u v) x = oMod N u (oMod N v x)) hutop ?_ ?_ ?_
  · -- homogeneous u ∈ 𝒱ᵢ; induct on v.
    intro i y hy
    rcases lt_or_ge i 0 with hineg | hipos
    · -- grade < 0 ⟹ y = 0
      rw [W.positivity i hineg, Submodule.mem_bot] at hy
      subst hy
      simp
    · -- now induct on v
      have hvtop : v ∈ ⨆ j, W.grading j := by
        rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
      refine Submodule.iSup_induction W.grading
        (motive := fun v => oMod N (zhuMul W y v) x = oMod N y (oMod N v x)) hvtop ?_ ?_ ?_
      · intro j z hz
        rcases lt_or_ge j 0 with hjneg | hjpos
        · rw [W.positivity j hjneg, Submodule.mem_bot] at hz
          subst hz
          simp
        · exact oMod_zhuMul_lowest (N := N) hcw hy hz hx hipos hjpos
      · show oMod N (zhuMul W y 0) x = oMod N y (oMod N 0 x)
        simp
      · intro z₁ z₂ hz₁ hz₂
        show oMod N (zhuMul W y (z₁ + z₂)) x = oMod N y (oMod N (z₁ + z₂) x)
        rw [zhuMul_add_right, map_add, LinearMap.add_apply, hz₁, hz₂, map_add,
          LinearMap.add_apply, map_add]
  · -- u = 0
    show oMod N (zhuMul W 0 v) x = oMod N 0 (oMod N v x)
    simp
  · -- u = u₁ + u₂
    intro u₁ u₂ h₁ h₂
    show oMod N (zhuMul W (u₁ + u₂) v) x = oMod N (u₁ + u₂) (oMod N v x)
    rw [zhuMul_add_left, map_add, LinearMap.add_apply, h₁, h₂, map_add, LinearMap.add_apply]

end EasyDirection2

section ModuleStructure

variable {Mod : Type u} [AddCommGroup Mod] [Module ℂ Mod] {W : VertexOperatorAlgebra 𝒱}

/-- The representation `ρ_h : 𝒱 →ₗ[ℂ] End ℂ (M_h)`, `u ↦ (o(u) restricted to M_h)`, as the
`h`-weight diagonal block of the module zero mode. -/
noncomputable def rhoLW (N : OrdVModule W Mod) (h : ℂ) : 𝒱 →ₗ[ℂ] End ℂ (N.weight h) where
  toFun u := weightBlock N (oMod N u) h
  map_add' u₁ u₂ := by rw [map_add, weightBlock_add]
  map_smul' c u := by rw [map_smul, weightBlock_smul]; rfl

/-- The action of `ρ_h u` on `x ∈ M_h` is `o(u) x` (which lies in `M_h`). -/
theorem rhoLW_apply_coe (N : OrdVModule W Mod) (h : ℂ) (u : 𝒱) (x : N.weight h) :
    ((rhoLW N h u x : N.weight h) : Mod) = oMod N u (x : Mod) := by
  have hmem : oMod N u (x : Mod) ∈ N.weight h := oMod_preserves_lowest_all N u x.2
  show (internalProjTo N.isInternal h (oMod N u (x : Mod)) : Mod) = oMod N u (x : Mod)
  rw [show oMod N u (x : Mod) = ((⟨oMod N u (x : Mod), hmem⟩ : N.weight h) : Mod) from rfl,
    internalProjTo_coe N.isInternal h ⟨oMod N u (x : Mod), hmem⟩]

/-- `ρ_h` kills `O W` on `M_h`: `O W ≤ ker ρ_h` (well-definedness of the `A(W)`-action).
From `oMod_L_translation_all` (5.3.9b) + `oMod_zhuMul_lowest_all` (5.3.9a). -/
theorem O_le_ker_rhoLW (N : OrdVModule W Mod) {h : ℂ} (hcw : IsLowestWeight N h) :
    O W ≤ LinearMap.ker (rhoLW N h) := by
  rw [O_eq_span, Submodule.span_le]
  rintro g ⟨a, v, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  refine LinearMap.ext fun x => ?_
  apply Subtype.ext
  rw [rhoLW_apply_coe]
  -- o((L₋₁a+L₀a)*v) x = o(L₋₁a+L₀a)(o(v) x) = 0  on M_h.
  rw [oMod_zhuMul_lowest_all N hcw _ _ x.2, oMod_L_translation_all N a, LinearMap.zero_apply]
  rfl

/-- `ρ_h` is **multiplicative**: `ρ_h (u*v) = ρ_h u ∘ ρ_h v` on `M_h` (5.3.9a). -/
theorem rhoLW_zhuMul (N : OrdVModule W Mod) {h : ℂ} (hcw : IsLowestWeight N h) (u v : 𝒱) :
    rhoLW N h (zhuMul W u v) = (rhoLW N h u) * (rhoLW N h v) := by
  refine LinearMap.ext fun x => ?_
  apply Subtype.ext
  rw [rhoLW_apply_coe]
  show oMod N (zhuMul W u v) (x : Mod) = ((rhoLW N h u (rhoLW N h v x) : N.weight h) : Mod)
  rw [rhoLW_apply_coe, rhoLW_apply_coe, oMod_zhuMul_lowest_all N hcw u v x.2]

/-- `ρ_h 𝟙 = id`: the vacuum acts as the identity on `M_h`. -/
theorem rhoLW_vacuum (N : OrdVModule W Mod) (h : ℂ) :
    rhoLW N h W.vacuum = 1 := by
  refine LinearMap.ext fun x => ?_
  apply Subtype.ext
  rw [rhoLW_apply_coe, oMod_vacuum]
  rfl

end ModuleStructure

section DescendedAction

variable {Mod : Type u} [AddCommGroup Mod] [Module ℂ Mod] {W : VertexOperatorAlgebra 𝒱}

/-- **The descended `A(W)`-action on `M_h`** (Theorem 5.3.4, easy direction): the representation
`ρ_h : 𝒱 →ₗ[ℂ] End ℂ M_h` descends through the quotient `A(W) = 𝒱/O(W)` (well-defined by
`O_le_ker_rhoLW`) to a `ℂ`-linear `actA : A(W) →ₗ[ℂ] End ℂ M_h`. -/
noncomputable def actA (N : OrdVModule W Mod) {h : ℂ} (hcw : IsLowestWeight N h) :
    A W →ₗ[ℂ] End ℂ (N.weight h) :=
  (O W).liftQ (rhoLW N h) (O_le_ker_rhoLW N hcw)

@[simp] theorem actA_mk (N : OrdVModule W Mod) {h : ℂ} (hcw : IsLowestWeight N h) (u : 𝒱) :
    actA N hcw (mk W u) = rhoLW N h u := by
  rw [actA, mk, Submodule.mkQ_apply, Submodule.liftQ_apply]

/-- The action on representatives: `[u] · x = o(u) x` (in `M_h`). -/
theorem actA_mk_apply_coe (N : OrdVModule W Mod) {h : ℂ} (hcw : IsLowestWeight N h)
    (u : 𝒱) (x : N.weight h) :
    ((actA N hcw (mk W u) x : N.weight h) : Mod) = oMod N u (x : Mod) := by
  rw [actA_mk, rhoLW_apply_coe]

/-- **Unit acts as identity:** `[𝟙] · x = x` (Theorem 5.3.4). -/
theorem actA_one (N : OrdVModule W Mod) {h : ℂ} (hcw : IsLowestWeight N h) :
    actA N hcw (one W) = 1 := by
  rw [one, actA_mk, rhoLW_vacuum]

/-- **Multiplicativity of the action:** `[u*v] · x = [u] · ([v] · x)` (the key
`A(W)`-module-compatibility 5.3.9a). On representatives,
`actA [u*v] = actA [u] ∘ actA [v]`. -/
theorem actA_mk_mul (N : OrdVModule W Mod) {h : ℂ} (hcw : IsLowestWeight N h) (u v : 𝒱) :
    actA N hcw (mk W (zhuMul W u v)) = (actA N hcw (mk W u)) * (actA N hcw (mk W v)) := by
  rw [actA_mk, actA_mk, actA_mk, rhoLW_zhuMul N hcw]

end DescendedAction

/-! ## Unit-compatibility and special-case associativity for `*` (genuine partial pieces of
the two-sided ideal / associativity frontier).

The full two-sided ideal property and associativity mod `O W` are Zhu Thm 2.1.1/2.1.2 (the
remaining genuine frontier; the higher-pole residue family `Pres_mem_O` (★) is the principal
input). The unit `𝟙` cases below are unconditional consequences of the unit laws
`zhuMul_vacuum_left`/`right` on `𝒱`. -/

/-- `g ∈ O ⟹ 𝟙 * g ∈ O` (left-mult by the unit). -/
theorem vacuum_left_mem_O (W : VertexOperatorAlgebra 𝒱) {g : 𝒱} (hg : g ∈ O W) :
    zhuMul W W.vacuum g ∈ O W := by rwa [zhuMul_vacuum_left]

/-- `g ∈ O ⟹ g * 𝟙 ∈ O` (right-mult by the unit). -/
theorem vacuum_right_mem_O (W : VertexOperatorAlgebra 𝒱) {g : 𝒱} (hg : g ∈ O W) :
    zhuMul W g W.vacuum ∈ O W := by rwa [zhuMul_vacuum_right]

/-- **Associativity with a unit factor** (special cases of associativity mod `O W`, here exact
on `𝒱`): `(𝟙*v)*w = 𝟙*(v*w)`, `(u*𝟙)*w = u*(𝟙*w)`, `(u*v)*𝟙 = u*(v*𝟙)`. -/
theorem zhuMul_assoc_vacuum_left (W : VertexOperatorAlgebra 𝒱) (v w : 𝒱) :
    zhuMul W (zhuMul W W.vacuum v) w = zhuMul W W.vacuum (zhuMul W v w) := by
  rw [zhuMul_vacuum_left, zhuMul_vacuum_left]

theorem zhuMul_assoc_vacuum_mid (W : VertexOperatorAlgebra 𝒱) (u w : 𝒱) :
    zhuMul W (zhuMul W u W.vacuum) w = zhuMul W u (zhuMul W W.vacuum w) := by
  rw [zhuMul_vacuum_right, zhuMul_vacuum_left]

theorem zhuMul_assoc_vacuum_right (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    zhuMul W (zhuMul W u v) W.vacuum = zhuMul W u (zhuMul W v W.vacuum) := by
  rw [zhuMul_vacuum_right, zhuMul_vacuum_right]

end VOA
