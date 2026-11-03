/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.SuperZhuRing
import VOA.Core.SuperBorcherds

/-!
# The super Zhu residue layer — `superPres`, and the bi-homogeneous reductions

This is the first of three files discharging `SuperZhuRingData` (Dong–Zhao Thm 3.1) for a
`SuperNearVOA` with integral weights.  It ports, to the super side, the *sign-free* half of the
bosonic `Modules/ZhuModule` + `Modules/ZhuRingResidue` layer:

* `superZhuMul_L_base` — `(L₋₁a + L₀a) ∗ b = ∑_{i≤M} C(M,i) a₍ᵢ₋₂₎b` (Frenkel–Zhu Lemma 2.1.1);
* `superPres` / `superPres_mem_superO` — the higher-pole residue family
  `Res_z Y(a,z)b (1+z)^{M+n}/z^{2+n}` and its membership in `O(V)` (Frenkel–Zhu Lemma 2.1.2);
* the reduction principles that let the two analytic cores be proved for **bi-homogeneous**
  arguments (homogeneous in *both* conformal weight and parity) only.

## Why none of this carries a Koszul sign

Every statement here involves the modes of a *single* state `a` (and `L₋₁`, `L₀`, which are modes
of the **even** vector `ω`).  No two odd states are exchanged, so no `koszul` factor can appear.
Concretely `smul_T_applyε` — the super `(L₋₁w)₍ₙ₎v = −n·w₍ₙ₋₁₎v` — needs no parity hypothesis
(it is `Core.SuperTranslationCovariance`, ultimately `L_comm_Ycoeffε`, which holds for arbitrary
`u`).  The signs enter only in the two files downstream, where `u` and `a` (resp. `u` and `v`) are
genuinely commuted past one another.

## The two extra hypotheses that the super side must make explicit

1. **Bi-homogeneity.**  The super cores need parity-homogeneous inputs (`mode_iterateε`,
   `commBoundε`), not just weight-homogeneous ones.  `parity_le_iSup_gradingZ_inf`
   (`Modules.SuperZhuRing`) supplies the joint decomposition: the weight components of a
   parity-homogeneous vector are again parity-homogeneous, because `ω` is even.
2. **Positivity.**  `SuperNearVOA` has no `positivity` axiom (the bosonic
   `VertexOperatorAlgebra` does).  Wherever the bosonic proof kills a negative grade, the super
   proof takes `hpos : ∀ k : ℤ, k < 0 → V.gradingZ k = ⊥` as a **named, visible** hypothesis.

## Status
`sorry`-free, with no project axioms.

## References
* Dong–Zhao, arXiv:math/0601571, §3; Frenkel–Zhu Lemmas 2.1.1–2.1.2; Zhu [574] Thm 2.1.1.
-/

namespace VOA

open scoped BigOperators
open Classical

set_option autoImplicit false

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace SuperNearVOA

variable (V : SuperNearVOA 𝒱)

/-! ## §1  Zero laws and the generating set of `O(V)` -/

@[simp] theorem superZhuMul_zero_left (hV : V.IntegralWeights) (v : 𝒱) :
    V.superZhuMul hV 0 v = 0 := by
  have h := V.superZhuMul_smul_left hV 0 0 v
  simp only [zero_smul] at h
  exact h

@[simp] theorem superZhuMul_zero_right (hV : V.IntegralWeights) (u : 𝒱) :
    V.superZhuMul hV u 0 = 0 := by
  have h := V.superZhuMul_smul_right hV 0 u 0
  simp only [zero_smul] at h
  exact h

/-- The generating set of `O(V)`: `{ (L₋₁a + L₀a) ∗ b }`. -/
def superOgen (hV : V.IntegralWeights) : Set 𝒱 :=
  {x | ∃ u v : 𝒱, x = V.superZhuMul hV (V.L (-1) u + V.L 0 u) v}

theorem superO_eq_span (hV : V.IntegralWeights) :
    V.superO hV = Submodule.span ℂ (V.superOgen hV) := rfl

theorem superGen_mem_superOgen (hV : V.IntegralWeights) (a b : 𝒱) :
    V.superZhuMul hV (V.L (-1) a + V.L 0 a) b ∈ V.superOgen hV := ⟨a, b, rfl⟩

/-- A `finsum` of `𝒱`-valued terms lying in `O(V)` lies in `O(V)`. -/
theorem finsum_mem_superO {ι : Type*} (hV : V.IntegralWeights) (F : ι → 𝒱)
    (hF : ∀ i, F i ∈ V.superO hV) : (∑ᶠ i, F i) ∈ V.superO hV := by
  by_cases hfin : (Function.support F).Finite
  · rw [finsum_eq_finsetSum_of_support_subset F (s := hfin.toFinset)
        (fun i hi => hfin.mem_toFinset.mpr hi)]
    exact Submodule.sum_mem _ (fun i _ => hF i)
  · rw [finsum_of_infinite_support (by rwa [Set.not_finite] at hfin)]
    exact (V.superO hV).zero_mem

/-! ## §2  `L₋₁` raises the weight by one -/

/-- `L₋₁a ∈ 𝒱_{M+1}` for `a ∈ 𝒱_M`.  `L₋₁ = ω₍₀₎` and `ω` has weight `2`. -/
theorem L_neg_one_mem_gradingZ_succ {M : ℤ} {a : 𝒱} (ha : a ∈ V.gradingZ M) :
    V.L (-1) a ∈ V.gradingZ (M + 1) := by
  have heq : V.L (-1) a = V.smul V.conformalVector 0 a := by
    rw [SuperNearVOA.L_def, SuperVertexAlgebra.smul_def, show ((-1 : ℤ) + 1) = 0 from by ring]
  have h := V.smul_mem_grading V.conformal_mem
    (show a ∈ V.grading ((M : ℤ) : ℂ) from ha) (0 : ℤ)
  have hcast : (2 + ((M : ℤ) : ℂ) - ((0 : ℤ) : ℂ) - 1) = (((M + 1 : ℤ)) : ℂ) := by
    push_cast; ring
  rw [hcast] at h
  rw [gradingZ_apply, heq]
  exact h

/-- **VA1 in `ℤ`-graded mode form.**  Weights add and drop by `n+1`. -/
theorem smul_mem_gradingZ {h k : ℤ} {u v : 𝒱} (hu : u ∈ V.gradingZ h)
    (hv : v ∈ V.gradingZ k) (n : ℤ) : V.smul u n v ∈ V.gradingZ (h + k - n - 1) := by
  have hres := V.smul_mem_grading (show u ∈ V.grading ((h : ℤ) : ℂ) from hu)
    (show v ∈ V.grading ((k : ℤ) : ℂ) from hv) n
  rw [gradingZ_apply]
  have hcast : (((h : ℤ) : ℂ) + ((k : ℤ) : ℂ) - (n : ℂ) - 1) = (((h + k - n - 1 : ℤ)) : ℂ) := by
    push_cast; ring
  rwa [hcast] at hres

/-! ## §3  The base residue identity (Frenkel–Zhu Lemma 2.1.1) -/

/-- **The super Zhu base-residue identity**: for `a ∈ 𝒱_M`,
`(L₋₁a + L₀a) ∗ b = ∑_{i=0}^{M} C(M,i) · a₍ᵢ₋₂₎ b`.  Sign-free: `L₋₁` and `L₀` are modes of the
even vector `ω`. -/
theorem superZhuMul_L_base (hV : V.IntegralWeights) {M : ℕ} {a : 𝒱}
    (ha : a ∈ V.gradingZ (M : ℤ)) (b : 𝒱) :
    V.superZhuMul hV (V.L (-1) a + V.L 0 a) b
      = ∑ i ∈ Finset.range (M + 1), cbz (M : ℤ) (i : ℤ) • V.smul a ((i : ℤ) - 2) b := by
  rw [V.superZhuMul_add_left hV]
  have hL0 : V.L 0 a = (M : ℂ) • a := by
    have h := V.L0_eigenvalue (show a ∈ V.grading (((M : ℕ) : ℤ) : ℂ) from ha)
    rwa [show ((((M : ℕ) : ℤ)) : ℂ) = (M : ℂ) from by push_cast; ring] at h
  have hT2 : V.superZhuMul hV (V.L 0 a) b
      = ∑ i ∈ Finset.range (M + 2),
          ((M : ℂ) * cbz (M : ℤ) ((i : ℤ) - 1)) • V.smul a ((i : ℤ) - 2) b := by
    rw [hL0, V.superZhuMul_smul_left hV, V.superZhuMul_homogeneous hV ha b,
      show ((M : ℤ).toNat + 1) = M + 1 from by simp, Finset.smul_sum]
    rw [Finset.sum_range_succ' (fun i => ((M : ℂ) * cbz (M : ℤ) ((i : ℤ) - 1)) •
        V.smul a ((i : ℤ) - 2) b) (M + 1)]
    rw [show cbz (M : ℤ) ((0 : ℕ) - 1 : ℤ) = 0 from cbz_apply_neg _ (by norm_num),
      mul_zero, zero_smul, add_zero]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [smul_smul]
    congr 2
    · push_cast; ring_nf
    · push_cast; ring_nf
  have hT1 : V.superZhuMul hV (V.L (-1) a) b
      = ∑ i ∈ Finset.range (M + 2),
          (cbz ((M : ℤ) + 1) (i : ℤ) * (-((i : ℂ) - 1))) • V.smul a ((i : ℤ) - 2) b := by
    rw [V.superZhuMul_homogeneous hV (V.L_neg_one_mem_gradingZ_succ ha) b,
      show (((M : ℤ) + 1).toNat + 1) = M + 2 from by omega]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [V.smul_T_applyε a b ((i : ℤ) - 1),
      show ((i : ℤ) - 1 - 1) = (i : ℤ) - 2 from by ring,
      ← Int.cast_smul_eq_zsmul ℂ (-((i : ℤ) - 1)) (V.smul a ((i : ℤ) - 2) b), smul_smul]
    congr 2
    push_cast
    ring
  rw [hT1, hT2, ← Finset.sum_add_distrib]
  have hcombine : ∀ i ∈ Finset.range (M + 2),
      (cbz ((M : ℤ) + 1) (i : ℤ) * (-((i : ℂ) - 1))) • V.smul a ((i : ℤ) - 2) b
        + ((M : ℂ) * cbz (M : ℤ) ((i : ℤ) - 1)) • V.smul a ((i : ℤ) - 2) b
        = cbz (M : ℤ) (i : ℤ) • V.smul a ((i : ℤ) - 2) b := by
    intro i _
    rw [← add_smul]
    congr 1
    have := cbz_coeff_identity M (i : ℤ)
    push_cast at this
    convert this using 3
  rw [Finset.sum_congr rfl hcombine, Finset.sum_range_succ]
  have hzero : cbz (M : ℤ) ((M + 1 : ℕ) : ℤ) = 0 :=
    cbz_lt (by positivity) (by exact_mod_cast by omega)
  rw [hzero, zero_smul, add_zero]

/-- **Base-residue membership**: for `a ∈ 𝒱_M`, `∑_{i≤M} C(M,i) a₍ᵢ₋₂₎b ∈ O(V)`. -/
theorem superResidue_base_mem_superO (hV : V.IntegralWeights) {M : ℕ} {a : 𝒱}
    (ha : a ∈ V.gradingZ (M : ℤ)) (b : 𝒱) :
    (∑ i ∈ Finset.range (M + 1), cbz (M : ℤ) (i : ℤ) • V.smul a ((i : ℤ) - 2) b)
      ∈ V.superO hV := by
  rw [← V.superZhuMul_L_base hV ha b]
  exact V.superO_mem_of_L hV a b

/-! ## §4  The higher-pole residue family (Frenkel–Zhu Lemma 2.1.2) -/

/-- The depth-`n` super Zhu residue `∑_i C(M+n,i) a₍ᵢ₋₂₋ₙ₎ b`, i.e.
`Res_z Y(a,z)b (1+z)^{M+n}/z^{2+n}`. -/
noncomputable def superPres (M : ℕ) (a b : 𝒱) (n : ℕ) : 𝒱 :=
  ∑ i ∈ Finset.range (M + n + 1), cbz ((M : ℤ) + n) (i : ℤ) • V.smul a ((i : ℤ) - 2 - n) b

/-- **(★) Higher-pole residue membership** (Frenkel–Zhu Lemma 2.1.2, super form): for
`a ∈ 𝒱_M` and every `n`, `superPres M a b n ∈ O(V)`.  Sign-free — only `a`'s own modes and the
even `L₋₁` occur. -/
theorem superPres_mem_superO (hV : V.IntegralWeights) {M : ℕ} {a : 𝒱}
    (ha : a ∈ V.gradingZ (M : ℤ)) (b : 𝒱) (n : ℕ) :
    V.superPres M a b n ∈ V.superO hV := by
  induction n generalizing M a with
  | zero =>
    have hb := V.superResidue_base_mem_superO hV ha b
    have heq : V.superPres M a b 0
        = ∑ i ∈ Finset.range (M + 1), cbz (M : ℤ) (i : ℤ) • V.smul a ((i : ℤ) - 2) b := by
      unfold superPres
      rw [Nat.add_zero]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show ((M : ℤ) + (0 : ℕ)) = (M : ℤ) from by push_cast; ring,
        show ((i : ℤ) - 2 - (0 : ℕ)) = (i : ℤ) - 2 from by push_cast; ring]
    rw [heq]; exact hb
  | succ n ih =>
    have haL : V.L (-1) a ∈ V.gradingZ ((M : ℤ) + 1) := V.L_neg_one_mem_gradingZ_succ ha
    have hG : V.superPres (M + 1) (V.L (-1) a) b n ∈ V.superO hV := by
      exact ih (M := M + 1) (a := V.L (-1) a) (by
        rwa [show (((M + 1 : ℕ)) : ℤ) = (M : ℤ) + 1 from by push_cast; ring])
    have hP : V.superPres M a b n ∈ V.superO hV := ih ha
    have hGeq : V.superPres (M + 1) (V.L (-1) a) b n
        = ∑ i ∈ Finset.range (M + n + 2),
            (cbz ((M : ℤ) + n + 1) (i : ℤ) * (-((i : ℂ) - 2 - n)))
              • V.smul a ((i : ℤ) - 3 - n) b := by
      unfold superPres
      rw [show M + 1 + n + 1 = M + n + 2 from by ring]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hcast1 : (((M + 1 : ℕ) : ℤ)) + (n : ℤ) = (M : ℤ) + n + 1 := by push_cast; ring
      rw [hcast1, V.smul_T_applyε a b ((i : ℤ) - 2 - n),
        show ((i : ℤ) - 2 - n - 1) = (i : ℤ) - 3 - n from by ring,
        ← Int.cast_smul_eq_zsmul ℂ (-((i : ℤ) - 2 - n)) (V.smul a ((i : ℤ) - 3 - n) b), smul_smul]
      congr 2
      push_cast
      ring
    have hsum : ((n : ℂ) + 2) • V.superPres M a b (n + 1)
        = V.superPres (M + 1) (V.L (-1) a) b n + ((M : ℂ) + n + 1) • V.superPres M a b n := by
      rw [hGeq]
      have hLHS : ((n : ℂ) + 2) • V.superPres M a b (n + 1)
          = ∑ i ∈ Finset.range (M + n + 2),
              (((n : ℂ) + 2) * cbz ((M : ℤ) + (n + 1)) (i : ℤ))
                • V.smul a ((i : ℤ) - 2 - (n + 1)) b := by
        unfold superPres
        rw [show M + (n + 1) + 1 = M + n + 2 from by ring, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [smul_smul]
        congr 2 <;> push_cast <;> ring
      have hPn : ((M : ℂ) + n + 1) • V.superPres M a b n
          = ∑ i ∈ Finset.range (M + n + 2),
              (((M : ℂ) + n + 1) * cbz ((M : ℤ) + n) ((i : ℤ) - 1))
                • V.smul a ((i : ℤ) - 3 - n) b := by
        unfold superPres
        rw [Finset.smul_sum]
        rw [Finset.sum_range_succ' (fun i => (((M : ℂ) + n + 1) * cbz ((M : ℤ) + n) ((i : ℤ) - 1))
            • V.smul a ((i : ℤ) - 3 - n) b) (M + n + 1)]
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
    have hne : ((n : ℂ) + 2) ≠ 0 := by
      have h2 : ((n : ℂ) + 2) = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
      rw [h2]; exact_mod_cast Nat.succ_ne_zero (n + 1)
    have hfin : V.superPres M a b (n + 1)
        = (((n : ℂ) + 2)⁻¹) • (V.superPres (M + 1) (V.L (-1) a) b n
            + ((M : ℂ) + n + 1) • V.superPres M a b n) := by
      rw [← hsum, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [hfin]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ hG (Submodule.smul_mem _ _ hP))

/-! ## §5  Bi-homogeneous reductions

Both super cores need arguments homogeneous in **weight and parity**.  These reductions turn a
statement about bi-homogeneous vectors into the general statement, using
`parity_le_iSup_gradingZ_inf` for the weight refinement of a parity-homogeneous vector and
`parity_isInternal` for the parity decomposition. -/

/-- **Bi-homogeneous induction.**  A predicate closed under `0` and `+`, holding on every
`𝒱ₖ ∩ 𝒱_p`, holds everywhere. -/
theorem reduce_bihomogeneous (hV : V.IntegralWeights) {P : 𝒱 → Prop}
    (hhom : ∀ (k : ℤ) (p : ZMod 2), ∀ u ∈ V.gradingZ k ⊓ V.parity p, P u)
    (hzero : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (u : 𝒱) : P u := by
  -- first split `u` by parity, then each parity slice by weight
  have hpar : ∀ (p : ZMod 2), ∀ x ∈ V.parity p, P x := by
    intro p x hx
    have hx' : x ∈ ⨆ k : ℤ, (V.gradingZ k ⊓ V.parity p) :=
      V.parity_le_iSup_gradingZ_inf hV p hx
    refine Submodule.iSup_induction (fun k : ℤ => V.gradingZ k ⊓ V.parity p)
      (motive := P) hx' ?_ hzero hadd
    intro k y hy
    exact hhom k p y hy
  have hutop : u ∈ ⨆ p : ZMod 2, V.parity p := by
    rw [V.parity_isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction V.parity (motive := P) hutop ?_ hzero hadd
  intro p x hx
  exact hpar p x hx

/-- **(right-ideal) reduced**: the right-ideal generator condition holds for all `(u,a,b)` as soon
as it holds for bi-homogeneous `u` and `a`. -/
theorem right_ideal_gen_of_bihomogeneous (hV : V.IntegralWeights)
    (H : ∀ (K : ℤ) (p : ZMod 2), ∀ u ∈ V.gradingZ K ⊓ V.parity p,
      ∀ (M : ℤ) (q : ZMod 2), ∀ a ∈ V.gradingZ M ⊓ V.parity q, ∀ b : 𝒱,
      V.superZhuMul hV u (V.superZhuMul hV (V.L (-1) a + V.L 0 a) b) ∈ V.superO hV) :
    ∀ u a b : 𝒱,
      V.superZhuMul hV u (V.superZhuMul hV (V.L (-1) a + V.L 0 a) b) ∈ V.superO hV := by
  intro u a b
  refine V.reduce_bihomogeneous hV (P := fun u =>
    V.superZhuMul hV u (V.superZhuMul hV (V.L (-1) a + V.L 0 a) b) ∈ V.superO hV) ?_ ?_ ?_ u
  · intro K p u hu
    refine V.reduce_bihomogeneous hV (P := fun a =>
      V.superZhuMul hV u (V.superZhuMul hV (V.L (-1) a + V.L 0 a) b) ∈ V.superO hV) ?_ ?_ ?_ a
    · intro M q a ha; exact H K p u hu M q a ha b
    · simp only [map_zero, add_zero, superZhuMul_zero_left, superZhuMul_zero_right]
      exact (V.superO hV).zero_mem
    · intro x y hx hy
      rw [show (V.L (-1)) (x + y) + (V.L 0) (x + y)
          = ((V.L (-1)) x + (V.L 0) x) + ((V.L (-1)) y + (V.L 0) y) from by
        simp only [map_add]; abel, V.superZhuMul_add_left hV, V.superZhuMul_add_right hV]
      exact (V.superO hV).add_mem hx hy
  · simp only [superZhuMul_zero_left]; exact (V.superO hV).zero_mem
  · intro x y hx hy
    rw [V.superZhuMul_add_left hV]; exact (V.superO hV).add_mem hx hy

/-- **(associator) reduced**: the associator lies in `O(V)` for all `(u,v,w)` as soon as it does
for bi-homogeneous `u` and `v` (`w` is arbitrary throughout). -/
theorem assoc_of_bihomogeneous (hV : V.IntegralWeights)
    (H : ∀ (K : ℤ) (p : ZMod 2), ∀ u ∈ V.gradingZ K ⊓ V.parity p,
      ∀ (L : ℤ) (q : ZMod 2), ∀ v ∈ V.gradingZ L ⊓ V.parity q, ∀ w : 𝒱,
      V.superZhuMul hV (V.superZhuMul hV u v) w - V.superZhuMul hV u (V.superZhuMul hV v w)
        ∈ V.superO hV) :
    ∀ u v w : 𝒱,
      V.superZhuMul hV (V.superZhuMul hV u v) w - V.superZhuMul hV u (V.superZhuMul hV v w)
        ∈ V.superO hV := by
  intro u v w
  refine V.reduce_bihomogeneous hV (P := fun u =>
    V.superZhuMul hV (V.superZhuMul hV u v) w - V.superZhuMul hV u (V.superZhuMul hV v w)
      ∈ V.superO hV) ?_ ?_ ?_ u
  · intro K p u hu
    refine V.reduce_bihomogeneous hV (P := fun v =>
      V.superZhuMul hV (V.superZhuMul hV u v) w - V.superZhuMul hV u (V.superZhuMul hV v w)
        ∈ V.superO hV) ?_ ?_ ?_ v
    · intro L q v hv; exact H K p u hu L q v hv w
    · simp only [superZhuMul_zero_right, superZhuMul_zero_left, sub_self]
      exact (V.superO hV).zero_mem
    · intro x y hx hy
      simp only [V.superZhuMul_add_right hV, V.superZhuMul_add_left hV]
      rw [show V.superZhuMul hV (V.superZhuMul hV u x) w + V.superZhuMul hV (V.superZhuMul hV u y) w
          - (V.superZhuMul hV u (V.superZhuMul hV x w)
              + V.superZhuMul hV u (V.superZhuMul hV y w))
          = (V.superZhuMul hV (V.superZhuMul hV u x) w
              - V.superZhuMul hV u (V.superZhuMul hV x w))
            + (V.superZhuMul hV (V.superZhuMul hV u y) w
              - V.superZhuMul hV u (V.superZhuMul hV y w)) from by abel]
      exact (V.superO hV).add_mem hx hy
  · simp only [superZhuMul_zero_left, superZhuMul_zero_right, sub_self]
    exact (V.superO hV).zero_mem
  · intro x y hx hy
    rw [V.superZhuMul_add_left hV, V.superZhuMul_add_left hV, V.superZhuMul_add_left hV,
      show V.superZhuMul hV (V.superZhuMul hV x v) w + V.superZhuMul hV (V.superZhuMul hV y v) w
        - (V.superZhuMul hV x (V.superZhuMul hV v w) + V.superZhuMul hV y (V.superZhuMul hV v w))
        = (V.superZhuMul hV (V.superZhuMul hV x v) w
            - V.superZhuMul hV x (V.superZhuMul hV v w))
          + (V.superZhuMul hV (V.superZhuMul hV y v) w
            - V.superZhuMul hV y (V.superZhuMul hV v w)) from by abel]
    exact (V.superO hV).add_mem hx hy

/-- **The left ideal is free from associativity** (verbatim the bosonic argument; no sign):
`((L₋₁a+L₀a)∗b)∗v = (L₋₁a+L₀a)∗(b∗v) + [associator] ∈ O(V)`. -/
theorem left_ideal_gen_of_assocε (hV : V.IntegralWeights)
    (hA : ∀ u v w : 𝒱,
      V.superZhuMul hV (V.superZhuMul hV u v) w - V.superZhuMul hV u (V.superZhuMul hV v w)
        ∈ V.superO hV) :
    ∀ g ∈ V.superOgen hV, ∀ v, V.superZhuMul hV g v ∈ V.superO hV := by
  rintro g ⟨a, b, rfl⟩ v
  have h1 : V.superZhuMul hV (V.L (-1) a + V.L 0 a) (V.superZhuMul hV b v) ∈ V.superO hV :=
    V.superO_mem_of_L hV a _
  have h2 := hA (V.L (-1) a + V.L 0 a) b v
  have heq : V.superZhuMul hV (V.superZhuMul hV (V.L (-1) a + V.L 0 a) b) v
      = V.superZhuMul hV (V.L (-1) a + V.L 0 a) (V.superZhuMul hV b v)
        + (V.superZhuMul hV (V.superZhuMul hV (V.L (-1) a + V.L 0 a) b) v
            - V.superZhuMul hV (V.L (-1) a + V.L 0 a) (V.superZhuMul hV b v)) := by abel
  rw [heq]; exact (V.superO hV).add_mem h1 h2

/-- `O(V)` is a left ideal, from the generator statement. -/
theorem left_ideal_of_gen (hV : V.IntegralWeights) (v : 𝒱)
    (hgen : ∀ g ∈ V.superOgen hV, V.superZhuMul hV g v ∈ V.superO hV) :
    ∀ u ∈ V.superO hV, V.superZhuMul hV u v ∈ V.superO hV := by
  intro u hu
  have hle : V.superO hV ≤ (V.superO hV).comap ((V.superZhuMulₗ hV).flip v) := by
    rw [superO_eq_span, Submodule.span_le]
    intro g hg
    simpa [Submodule.mem_comap] using hgen g hg
  have h := hle hu
  simpa [Submodule.mem_comap] using h

/-- `O(V)` is a right ideal, from the generator statement. -/
theorem right_ideal_of_gen (hV : V.IntegralWeights) (u : 𝒱)
    (hgen : ∀ g ∈ V.superOgen hV, V.superZhuMul hV u g ∈ V.superO hV) :
    ∀ v ∈ V.superO hV, V.superZhuMul hV u v ∈ V.superO hV := by
  intro v hv
  have hle : V.superO hV ≤ (V.superO hV).comap (V.superZhuMulₗ hV u) := by
    rw [superO_eq_span, Submodule.span_le]
    intro g hg
    simpa [Submodule.mem_comap] using hgen g hg
  have h := hle hv
  simpa [Submodule.mem_comap] using h

end SuperNearVOA

end VOA
