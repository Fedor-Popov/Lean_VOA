/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.SuperZhuRightIdeal
import VOA.Modules.ZhuAssociator

/-!
# `associator_coreε` — the super Zhu associativity residue core (Dong–Zhao Thm 3.1)

The super analogue of `VOA.associator_core` (`Modules/ZhuAssociator`): for
**bi-homogeneous** `u ∈ 𝒱_K ∩ 𝒱_p` and `v ∈ 𝒱_L ∩ 𝒱_q` and arbitrary `w`,
`(u ∗ v) ∗ w − u ∗ (v ∗ w) ∈ O(V)`.

## The one shape difference from the bosonic proof

The bosonic argument splits `(u∗v)∗w` (expanded by `mode_iterate`) into a **U-side**
(`u₍ₐ₋₁₋ᵢ₎(v₍ᵣ₋₁₊ᵢ₎w)` terms) and a **V-side** (`v₍ₐ₊ᵣ₋₂₋ᵢ₎(u₍ᵢ₎w)` terms carrying `(-1)^{a-1}`),
proves `USide = Ufam + u∗(v∗w)` and `−VSide = Vfam`, and lands both families in `O(V)` through the
`Pres` tower.

`mode_iterateε` (`Core.SuperBorcherdsIdentity`, the D2 layer) differs from `mode_iterate` in
exactly one scalar: the exchanged term carries `koszul p q * (-1)^ℓ` instead of `(-1)^ℓ`, and
`koszul p q` is **constant in every summation index**.  Consequently:

* the whole U-side development — `uside_*`, `uTerm*`, `USide_eq*`, `RHS_eq`, `Ufam_*` — is the
  bosonic one **verbatim**, since the U-side is sign-free;
* the V-side development is likewise the bosonic one verbatim; the sign is carried by a single
  auxiliary `VSideXε` (the V-side with the constant `ε` attached), and `VSideX_eq_smulε` proves
  `VSideXε = ε • VSideε` in six lines;
* the master split becomes `(u∗v)∗w = USideε − VSideXε` and the decomposition
  `(u∗v)∗w − u∗(v∗w) = Ufamε + ε • Vfamε`, which lies in `O(V)` because `O(V)` is a
  `ℂ`-submodule.

Every **pure-scalar** lemma of the bosonic file — `uCoeffTower`, `vCoeffTower`, `vSideCoeff`,
`vSideCoeff_eq`, `uSideScalar` and its three case lemmas, `uSideScalar_sub_rhs`, `rhsCoeff_m_fin`,
`uCoeffExt_m_fin`, `swap_finsum_NZ`, `smul_support_of_scalar_gen`, `cbz_shift_support_fin'`,
`rangeSmul_eq_finsumZ'` — together with the three binomial cores `ZhuU.u_core`, `ZhuV.v_core`,
`ZhuMu.mu_identity`, is reused **by import**, not ported.

## Status
`sorry`-free, with no project axioms.

## References
* Dong–Zhao, arXiv:math/0601571, Thm 3.1; Zhu [574] Thm 2.1.2; Frenkel–Zhu.
-/

open VOA
open VertexOperatorAlgebra (finsum_nat_to_int)
open scoped BigOperators
open Classical

set_option autoImplicit false

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace SuperZhuAssoc

open VOA.SuperNearVOA

/-- The **u-outer family**: `∑_{b<Bv} ∑_{n=0}^{b} μ(L,b,n) • Pres(u, K, v₍b₎w, n)`. -/
noncomputable def Ufamε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) (Bv : ℕ) : 𝒱 :=
  ∑ b ∈ Finset.range Bv, ∑ n ∈ Finset.range (b + 1),
    ZhuMu.muCoeff L b n • V.superPres K u (V.smul v (b : ℤ) w) n

/-- The **v-outer (swap) family**: `∑_{a<Bu} ∑_{n=0}^{a} μ(K,a,n) • Pres(v, L, u₍a₎w, n)`. -/
noncomputable def Vfamε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) (Bu : ℕ) : 𝒱 :=
  ∑ a ∈ Finset.range Bu, ∑ n ∈ Finset.range (a + 1),
    ZhuMu.muCoeff K a n • V.superPres L v (V.smul u (a : ℤ) w) n

/-- `Ufamε ∈ V.superO hV` (each `Pres(u,K,·,n) ∈ O` by `Pres_mem_O`, `u ∈ 𝒱_K`). -/
theorem Ufam_mem_Oε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) {K L : ℕ} {u : 𝒱}
    (hu : u ∈ V.gradingZ (K : ℤ)) (v w : 𝒱) (Bv : ℕ) : Ufamε V hV K L u v w Bv ∈ V.superO hV := by
  refine Submodule.sum_mem _ (fun b _ => Submodule.sum_mem _ (fun n _ => ?_))
  exact Submodule.smul_mem _ _ (V.superPres_mem_superO hV hu (V.smul v (b : ℤ) w) n)

/-- `Vfamε ∈ V.superO hV` (each `Pres(v,L,·,n) ∈ O` by `Pres_mem_O`, `v ∈ 𝒱_L`). -/
theorem Vfam_mem_Oε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) {K L : ℕ} {v : 𝒱}
    (hv : v ∈ V.gradingZ (L : ℤ)) (u w : 𝒱) (Bu : ℕ) : Vfamε V hV K L u v w Bu ∈ V.superO hV := by
  refine Submodule.sum_mem _ (fun a _ => Submodule.sum_mem _ (fun n _ => ?_))
  exact Submodule.smul_mem _ _ (V.superPres_mem_superO hV hv (V.smul u (a : ℤ) w) n)

/-! ## Finite-sum infrastructure
(general `Finset` sum lemmas used below). -/

/-- **RHS expansion**: `u*(v*w) = ∑_{p≤K} ∑_{c≤L} cbz K p · cbz L c • u₍ₚ₋₁₎(v₍ᵢ₋₁₎w)`. -/
theorem uvw_expandε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) {K L : ℕ} {u v : 𝒱}
    (hu : u ∈ V.gradingZ (K : ℤ)) (hv : v ∈ V.gradingZ (L : ℤ)) (w : 𝒱) :
    V.superZhuMul hV u (V.superZhuMul hV v w)
      = ∑ p ∈ Finset.range (K + 1), ∑ c ∈ Finset.range (L + 1),
          (cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) (c : ℤ))
            • V.smul u ((p : ℤ) - 1) (V.smul v ((c : ℤ) - 1) w) := by
  rw [V.superZhuMul_homogeneous hV hu, show (K : ℤ).toNat + 1 = K + 1 from by simp]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [V.superZhuMul_homogeneous hV hv, show (L : ℤ).toNat + 1 = L + 1 from by simp]
  rw [show V.smul u ((p : ℤ) - 1) (∑ c ∈ Finset.range (L + 1), cbz (L : ℤ) (c : ℤ) • V.smul v ((c : ℤ) - 1) w)
        = ∑ c ∈ Finset.range (L + 1), cbz (L : ℤ) (c : ℤ) • V.smul u ((p : ℤ) - 1) (V.smul v ((c : ℤ) - 1) w) from by
      rw [SuperVertexAlgebra.smul_def, map_sum]
      exact Finset.sum_congr rfl fun c _ => by rw [LinearMap.map_smul]; rfl,
    Finset.smul_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [smul_smul]

/-- `u₍ₐ₋₁₎v ∈ 𝒱_{K+L-a}` for `a ≤ K` (grade `K+L-a ≥ 0`). -/
theorem inner_uv_memε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) {K L : ℕ} {u v : 𝒱}
    (hu : u ∈ V.gradingZ (K : ℤ)) (hv : v ∈ V.gradingZ (L : ℤ)) (a : ℕ) :
    V.smul u ((a : ℤ) - 1) v ∈ V.gradingZ ((K : ℤ) + (L : ℤ) - (a : ℤ)) := by
  have h := V.smul_mem_gradingZ hu hv ((a : ℤ) - 1)
  rwa [show (K : ℤ) + (L : ℤ) - ((a : ℤ) - 1) - 1 = (K : ℤ) + (L : ℤ) - (a : ℤ) from by ring] at h

/-- **LHS expansion (one step)**: `(u*v)*w = ∑_{a≤K} cbz K a • ((u₍ₐ₋₁₎v) * w)`. -/
theorem uvw_lhs_stepε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) {K : ℕ} {u v : 𝒱}
    (hu : u ∈ V.gradingZ (K : ℤ)) (w : 𝒱) :
    V.superZhuMul hV (V.superZhuMul hV u v) w
      = ∑ a ∈ Finset.range (K + 1),
          cbz (K : ℤ) (a : ℤ) • V.superZhuMul hV (V.smul u ((a : ℤ) - 1) v) w := by
  rw [V.superZhuMul_homogeneous hV hu, show (K : ℤ).toNat + 1 = K + 1 from by simp]
  rw [show V.superZhuMul hV (∑ a ∈ Finset.range (K + 1), cbz (K : ℤ) (a : ℤ) • V.smul u ((a : ℤ) - 1) v) w
        = ((V.superZhuMulₗ hV).flip w) (∑ a ∈ Finset.range (K + 1), cbz (K : ℤ) (a : ℤ) • V.smul u ((a : ℤ) - 1) v) from rfl,
    map_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [map_smul]; rfl

/-! ## `Ufamε` as a u-word collection. -/

/-- Per-`b` inner collapse: `∑_{n≤b} μ(L,b,n) • Pres(u,K,v₍b₎w,n) = ∑ᶠ m, uCoeffTower • u₍ₘ₎(v₍b₎w)`. -/
theorem Ufam_innerε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L b : ℕ) (u v w : 𝒱) :
    (∑ n ∈ Finset.range (b + 1), ZhuMu.muCoeff L b n • V.superPres K u (V.smul v (b : ℤ) w) n)
      = ∑ᶠ m : ℤ, uCoeffTower K L b m • V.smul u m (V.smul v (b : ℤ) w) := by
  -- expand each Pres into a finsum, pull the muCoeff scalar inside
  rw [show (∑ n ∈ Finset.range (b + 1), ZhuMu.muCoeff L b n • V.superPres K u (V.smul v (b : ℤ) w) n)
        = ∑ n ∈ Finset.range (b + 1),
            ∑ᶠ m : ℤ, (ZhuMu.muCoeff L b n * cbz ((K : ℤ) + n) (m + 2 + n))
              • V.smul u m (V.smul v (b : ℤ) w) from
      Finset.sum_congr rfl fun n _ => by
        rw [SuperZhuHR.superPres_eq_finsum V K u (V.smul v (b : ℤ) w) n]
        have hfin : Function.HasFiniteSupport
            (fun m : ℤ => cbz ((K : ℤ) + n) (m + 2 + n) • V.smul u m (V.smul v (b : ℤ) w)) :=
          smul_support_of_scalar_gen _ _
            (Set.Finite.subset (cbz_shift_support_fin' (d := (K : ℤ) + n) (by positivity) (2 + n))
              (fun m hm => by
                rw [Function.mem_support] at hm ⊢
                intro h; apply hm
                rw [show m + 2 + (n : ℤ) = m + (2 + (n : ℤ)) from by ring]; exact h))
        rw [smul_finsum' (ZhuMu.muCoeff L b n) hfin]
        refine finsum_congr fun m => ?_
        rw [smul_smul]]
  -- swap the finite n-sum past the finsum
  rw [← finsum_sum_comm (Finset.range (b + 1))
      (fun m n => (ZhuMu.muCoeff L b n * cbz ((K : ℤ) + n) (m + 2 + n))
        • V.smul u m (V.smul v (b : ℤ) w))
      (fun n _ => ?_)]
  · refine finsum_congr fun m => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [uCoeffTower]
    -- ∑_n μ(L,b,n)·cbz(K+n)(m+2+n) = ∑_k cbz K (m+2+k)·cbz L (b-k)  (mu_identity, s = m+2)
    rw [← ZhuMu.mu_identity K L b (m + 2)]
  · -- finite support of m ↦ (μ·cbz)• u₍ₘ₎(...) for fixed n
    refine smul_support_of_scalar_gen _ _ (Set.Finite.subset
      (cbz_shift_support_fin' (d := (K : ℤ) + n) (by positivity) (2 + n)) ?_)
    intro m hm
    rw [Function.mem_support] at hm ⊢
    intro h; apply hm
    rw [show (ZhuMu.muCoeff L b n * cbz ((K : ℤ) + n) (m + 2 + n))
          = (ZhuMu.muCoeff L b n) * cbz ((K : ℤ) + n) (m + (2 + (n : ℤ))) from by
        rw [show m + (2 + (n : ℤ)) = m + 2 + (n : ℤ) from by ring], h, mul_zero]

/-- Per-`a` inner collapse: `∑_{n≤a} μ(K,a,n) • Pres(v,L,u₍a₎w,n) = ∑ᶠ γ, vCoeffTower • v₍ᵧ₎(u₍ₐ₎w)`. -/
theorem Vfam_innerε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L a : ℕ) (u v w : 𝒱) :
    (∑ n ∈ Finset.range (a + 1), ZhuMu.muCoeff K a n • V.superPres L v (V.smul u (a : ℤ) w) n)
      = ∑ᶠ γ : ℤ, vCoeffTower K L a γ • V.smul v γ (V.smul u (a : ℤ) w) := by
  rw [show (∑ n ∈ Finset.range (a + 1), ZhuMu.muCoeff K a n • V.superPres L v (V.smul u (a : ℤ) w) n)
        = ∑ n ∈ Finset.range (a + 1),
            ∑ᶠ γ : ℤ, (ZhuMu.muCoeff K a n * cbz ((L : ℤ) + n) (γ + 2 + n))
              • V.smul v γ (V.smul u (a : ℤ) w) from
      Finset.sum_congr rfl fun n _ => by
        rw [SuperZhuHR.superPres_eq_finsum V L v (V.smul u (a : ℤ) w) n]
        have hfin : Function.HasFiniteSupport
            (fun γ : ℤ => cbz ((L : ℤ) + n) (γ + 2 + n) • V.smul v γ (V.smul u (a : ℤ) w)) :=
          smul_support_of_scalar_gen _ _
            (Set.Finite.subset (cbz_shift_support_fin' (d := (L : ℤ) + n) (by positivity) (2 + n))
              (fun γ hγ => by
                rw [Function.mem_support] at hγ ⊢
                intro h; apply hγ
                rw [show γ + 2 + (n : ℤ) = γ + (2 + (n : ℤ)) from by ring]; exact h))
        rw [smul_finsum' (ZhuMu.muCoeff K a n) hfin]
        refine finsum_congr fun γ => ?_
        rw [smul_smul]]
  rw [← finsum_sum_comm (Finset.range (a + 1))
      (fun γ n => (ZhuMu.muCoeff K a n * cbz ((L : ℤ) + n) (γ + 2 + n))
        • V.smul v γ (V.smul u (a : ℤ) w))
      (fun n _ => ?_)]
  · refine finsum_congr fun γ => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [vCoeffTower]
    rw [← ZhuMu.mu_identity L K a (γ + 2)]
  · refine smul_support_of_scalar_gen _ _ (Set.Finite.subset
      (cbz_shift_support_fin' (d := (L : ℤ) + n) (by positivity) (2 + n)) ?_)
    intro γ hγ
    rw [Function.mem_support] at hγ ⊢
    intro h; apply hγ
    rw [show (ZhuMu.muCoeff K a n * cbz ((L : ℤ) + n) (γ + 2 + n))
          = (ZhuMu.muCoeff K a n) * cbz ((L : ℤ) + n) (γ + (2 + (n : ℤ))) from by
        rw [show γ + (2 + (n : ℤ)) = γ + 2 + (n : ℤ) from by ring], h, mul_zero]

/-! ## LHS expansion via homogeneity + mode_iterate. -/

/-- For `a ≤ K`, expand `(u₍ₐ₋₁₎v)*w` via homogeneity (grade `K+L-a`) and `mode_iterate`,
extending the `r`-range to the fixed `range (K+L+1)` (extra terms vanish via `cbz`). -/
theorem lhs_per_aε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) {K L : ℕ} {p q : ZMod 2}
    {u v : 𝒱} (hu : u ∈ V.gradingZ (K : ℤ)) (hup : u ∈ V.parity p)
    (hv : v ∈ V.gradingZ (L : ℤ)) (hvq : v ∈ V.parity q) (w : 𝒱) {a : ℕ} (haK : a ≤ K) :
    V.superZhuMul hV (V.smul u ((a : ℤ) - 1) v) w
      = ∑ r ∈ Finset.range (K + L + 1),
          ∑ᶠ i : ℕ, (cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
              * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
            • (V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v ((r : ℤ) - 1 + (i : ℤ)) w)
              - (koszul p q * (-1 : ℂ) ^ ((a : ℤ) - 1))
                • V.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (V.smul u (i : ℤ) w)) := by
  have hmem := inner_uv_memε V hV hu hv a
  rw [V.superZhuMul_homogeneous hV hmem]
  -- the toNat of K+L-a is K+L-a since a ≤ K
  have htn : ((K : ℤ) + (L : ℤ) - (a : ℤ)).toNat = K + L - a := by
    have : ((K : ℤ) + (L : ℤ) - (a : ℤ)) = ((K + L - a : ℕ) : ℤ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this, Int.toNat_natCast]
  -- rewrite the range index and apply mode_iterate inside each summand
  rw [show (∑ m ∈ Finset.range (((K : ℤ) + (L : ℤ) - (a : ℤ)).toNat + 1),
            cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (m : ℤ)
              • V.smul (V.smul u ((a : ℤ) - 1) v) ((m : ℤ) - 1) w)
        = ∑ r ∈ Finset.range (K + L + 1),
            cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
              • V.smul (V.smul u ((a : ℤ) - 1) v) ((r : ℤ) - 1) w from ?_]
  · -- now expand the composite mode via mode_iterate per r
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mode_iterateε V hup hvq ((a : ℤ) - 1) ((r : ℤ) - 1) w]
    rw [show ((a : ℤ) - 1) + ((r : ℤ) - 1) = ((a : ℤ) - 1) + ((r : ℤ) - 1) from rfl]
    -- distribute the cbz scalar into the finsum
    have hfin : Function.HasFiniteSupport
        (fun i : ℕ => ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i)
          • (V.smul u (((a : ℤ) - 1) - (i : ℤ)) (V.smul v (((r : ℤ) - 1) + (i : ℤ)) w)
            - (koszul p q * (-1 : ℂ) ^ ((a : ℤ) - 1))
              • V.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (V.smul u (i : ℤ) w))) := by
      -- both v₍ᵣ₋₁₊ᵢ₎w and u₍ᵢ₎w vanish for large i (regularity)
      obtain ⟨Nv, hNv⟩ := V.regularity v w
      obtain ⟨Nu, hNu⟩ := V.regularity u w
      apply Set.Finite.subset (Set.finite_Icc (0 : ℕ) (Nv.toNat + Nu.toNat))
      intro i hi
      rw [Function.mem_support] at hi
      simp only [Set.mem_Icc]
      refine ⟨Nat.zero_le _, ?_⟩
      by_contra hbig
      apply hi
      have hNvle : Nv ≤ (Nv.toNat : ℤ) := Int.self_le_toNat Nv
      have hNule : Nu ≤ (Nu.toNat : ℤ) := Int.self_le_toNat Nu
      have hige : Nv.toNat + Nu.toNat + 1 ≤ i := by omega
      have hige' : ((Nv.toNat : ℤ) + (Nu.toNat : ℤ) + 1) ≤ (i : ℤ) := by exact_mod_cast hige
      have hv0 : V.smul v (((r : ℤ) - 1) + (i : ℤ)) w = 0 := hNv _ (by omega)
      have hu0 : V.smul u (i : ℤ) w = 0 := hNu _ (by omega)
      rw [hv0, hu0]
      simp
    rw [smul_finsum' (cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)) hfin]
    refine finsum_congr fun i => ?_
    rw [smul_smul]
  · -- extend the r-range; extra terms r > K+L-a vanish (cbz = 0)
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      rw [Finset.mem_range, htn] at hx
      rw [Finset.mem_range]; omega
    · intro r hr hrni
      have hrlo : (K + L - a) + 1 ≤ r := by
        rw [htn] at hrni; exact Nat.le_of_not_lt (fun h => hrni (Finset.mem_range.mpr h))
      rw [cbz_lt (by omega) (by
        have : ((K + L - a : ℕ) : ℤ) < (r : ℤ) := by exact_mod_cast (by omega : K + L - a < r)
        rw [Nat.cast_sub (by omega)] at this; push_cast at this ⊢; omega :
        ((K : ℤ) + (L : ℤ) - (a : ℤ)) < (r : ℤ)),
        zero_smul]

/-! ## The U-side and V-side of `(u*v)*w`. -/

/-- The **U-side** of `(u*v)*w`: all `u₍ₐ₋₁₋ᵢ₎(v₍ᵣ₋₁₊ᵢ₎w)` terms. -/
noncomputable def USideε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) : 𝒱 :=
  ∑ a ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (K + L + 1),
    ∑ᶠ i : ℕ, (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
        * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
      • V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v ((r : ℤ) - 1 + (i : ℤ)) w)

/-- The **V-side** of `(u*v)*w`: all `v₍ₐ₊ᵣ₋₂₋ᵢ₎(u₍ᵢ₎w)` terms (carrying the sign `(-1)^(a-1)`). -/
noncomputable def VSideε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) : 𝒱 :=
  ∑ a ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (K + L + 1),
    ∑ᶠ i : ℕ, (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
        * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
      • V.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (V.smul u (i : ℤ) w)

/-- Finiteness of the per-`(a,r)` u-side `i`-finsum (regularity of `v` on `w`). -/
theorem uside_finε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) (a r : ℕ) :
    Function.HasFiniteSupport (fun i : ℕ =>
      (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
          * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
        • V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v ((r : ℤ) - 1 + (i : ℤ)) w)) := by
  obtain ⟨Nv, hNv⟩ := V.regularity v w
  apply Set.Finite.subset (Set.finite_Icc (0 : ℕ) Nv.toNat)
  intro i hi
  rw [Function.mem_support] at hi
  simp only [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  by_contra hbig
  apply hi
  have hNvle : Nv ≤ (Nv.toNat : ℤ) := Int.self_le_toNat Nv
  have hi' : (Nv.toNat : ℤ) + 1 ≤ (i : ℤ) := by exact_mod_cast (by omega : Nv.toNat + 1 ≤ i)
  rw [show V.smul v ((r : ℤ) - 1 + (i : ℤ)) w = (0 : 𝒱) from hNv _ (by omega)]
  simp

/-- Finiteness of the per-`(a,r)` v-side `i`-finsum (regularity of `u` on `w`). -/
theorem vside_finε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) (a r : ℕ) :
    Function.HasFiniteSupport (fun i : ℕ =>
      (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
          * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
        • V.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (V.smul u (i : ℤ) w)) := by
  obtain ⟨Nu, hNu⟩ := V.regularity u w
  apply Set.Finite.subset (Set.finite_Icc (0 : ℕ) Nu.toNat)
  intro i hi
  rw [Function.mem_support] at hi
  simp only [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  by_contra hbig
  apply hi
  have hNule : Nu ≤ (Nu.toNat : ℤ) := Int.self_le_toNat Nu
  have hi' : (Nu.toNat : ℤ) + 1 ≤ (i : ℤ) := by exact_mod_cast (by omega : Nu.toNat + 1 ≤ i)
  rw [show V.smul u (i : ℤ) w = (0 : 𝒱) from hNu _ (by omega)]
  simp

/-- The **`ε`-twisted V-side**: the V-side with the single constant Koszul factor `ε` attached.
This is the *only* shape difference from the bosonic development, and `VSideX_eq_smulε` shows it
is just `ε •` the bosonic V-side. -/
noncomputable def VSideXε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (ε : ℂ) (K L : ℕ)
    (u v w : 𝒱) : 𝒱 :=
  ∑ a ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (K + L + 1),
    ∑ᶠ i : ℕ, (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
        * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * (ε * (-1 : ℂ) ^ ((a : ℤ) - 1)))
      • V.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (V.smul u (i : ℤ) w)

/-- Finiteness of the per-`(a,r)` twisted v-side `i`-finsum. -/
theorem vsideX_finε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (ε : ℂ) (K L : ℕ)
    (u v w : 𝒱) (a r : ℕ) :
    Function.HasFiniteSupport (fun i : ℕ =>
      (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
          * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * (ε * (-1 : ℂ) ^ ((a : ℤ) - 1)))
        • V.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (V.smul u (i : ℤ) w)) := by
  obtain ⟨Nu, hNu⟩ := V.regularity u w
  apply Set.Finite.subset (Set.finite_Icc (0 : ℕ) Nu.toNat)
  intro i hi
  rw [Function.mem_support] at hi
  simp only [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  by_contra hbig
  apply hi
  have hNule : Nu ≤ (Nu.toNat : ℤ) := Int.self_le_toNat Nu
  have hi' : (Nu.toNat : ℤ) + 1 ≤ (i : ℤ) := by exact_mod_cast (by omega : Nu.toNat + 1 ≤ i)
  rw [show V.smul u (i : ℤ) w = (0 : 𝒱) from hNu _ (by omega)]
  simp

/-- The twisted V-side is the bosonic V-side scaled by the constant `ε`. -/
theorem VSideX_eq_smulε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (ε : ℂ) (K L : ℕ)
    (u v w : 𝒱) : VSideXε V hV ε K L u v w = ε • VSideε V hV K L u v w := by
  rw [VSideXε, VSideε, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [smul_finsum' ε (vside_finε V hV K L u v w a r)]
  refine finsum_congr fun i => ?_
  rw [smul_smul]
  ring_nf

/-- **Master split**: `(u*v)*w = USideε − VSideε`. -/
theorem lhs_splitε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) {K L : ℕ} {p q : ZMod 2}
    {u v : 𝒱} (hu : u ∈ V.gradingZ (K : ℤ)) (hup : u ∈ V.parity p)
    (hv : v ∈ V.gradingZ (L : ℤ)) (hvq : v ∈ V.parity q) (w : 𝒱) :
    V.superZhuMul hV (V.superZhuMul hV u v) w
      = USideε V hV K L u v w - VSideXε V hV (koszul p q) K L u v w := by
  rw [uvw_lhs_stepε V hV hu w]
  rw [show (∑ a ∈ Finset.range (K + 1),
            cbz (K : ℤ) (a : ℤ) • V.superZhuMul hV (V.smul u ((a : ℤ) - 1) v) w)
        = ∑ a ∈ Finset.range (K + 1), cbz (K : ℤ) (a : ℤ) •
            (∑ r ∈ Finset.range (K + L + 1),
              ∑ᶠ i : ℕ, (cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                  * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
                • (V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v ((r : ℤ) - 1 + (i : ℤ)) w)
                  - (koszul p q * (-1 : ℂ) ^ ((a : ℤ) - 1))
                    • V.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (V.smul u (i : ℤ) w))) from
      Finset.sum_congr rfl fun a ha =>
        by rw [lhs_per_aε V hV hu hup hv hvq w (Finset.mem_range.mp ha |> Nat.lt_succ_iff.mp)]]
  -- distribute and split each summand into u-part minus v-part
  rw [USideε, VSideXε, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r hr => ?_
  -- split the i-finsum: scalar•(uword - sv•vword) = scalar•uword - (scalar·sv)•vword
  rw [smul_finsum' (cbz (K : ℤ) (a : ℤ)) (by
    -- finite support of the per-(a,r) inner finsum
    obtain ⟨Nv, hNv⟩ := V.regularity v w
    obtain ⟨Nu, hNu⟩ := V.regularity u w
    apply Set.Finite.subset (Set.finite_Icc (0 : ℕ) (Nv.toNat + Nu.toNat))
    intro i hi
    rw [Function.mem_support] at hi
    simp only [Set.mem_Icc]
    refine ⟨Nat.zero_le _, ?_⟩
    by_contra hbig
    apply hi
    have hNvle : Nv ≤ (Nv.toNat : ℤ) := Int.self_le_toNat Nv
    have hNule : Nu ≤ (Nu.toNat : ℤ) := Int.self_le_toNat Nu
    have hi' : ((Nv.toNat : ℤ) + (Nu.toNat : ℤ) + 1) ≤ (i : ℤ) := by
      exact_mod_cast (by omega : Nv.toNat + Nu.toNat + 1 ≤ i)
    have e1 : V.smul v ((r : ℤ) - 1 + (i : ℤ)) w = 0 := hNv _ (by omega)
    have e2 : V.smul u (i : ℤ) w = 0 := hNu _ (by omega)
    rw [show V.smul v ((r : ℤ) - 1 + (i : ℤ)) w = (0 : 𝒱) from e1,
      show V.smul u (i : ℤ) w = (0 : 𝒱) from e2]
    simp)]
  rw [show (∑ᶠ i : ℕ, cbz (K : ℤ) (a : ℤ) •
            ((cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
              • (V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v ((r : ℤ) - 1 + (i : ℤ)) w)
                - (koszul p q * (-1 : ℂ) ^ ((a : ℤ) - 1))
                  • V.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (V.smul u (i : ℤ) w))))
        = ∑ᶠ i : ℕ,
            ((cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
              • V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v ((r : ℤ) - 1 + (i : ℤ)) w)
            - (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i)
                * (koszul p q * (-1 : ℂ) ^ ((a : ℤ) - 1)))
              • V.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (V.smul u (i : ℤ) w)) from
      finsum_congr fun i => by rw [smul_smul, smul_sub, smul_smul]; ring_nf]
  rw [finsum_sub_distrib (uside_finε V hV K L u v w a r)
    (vsideX_finε V hV (koszul p q) K L u v w a r)]

/-! ## V-side reindex: collect v-words by mode value. -/

/-- Per-`(a,i)` reindex of the `r`-sum to a `∑ᶠ γ` over the v-mode value (`γ = a+r-2-i`). -/
theorem vside_r_reindexε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) (a i : ℕ)
    (haK : a ≤ K) :
    (∑ r ∈ Finset.range (K + L + 1),
        cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
          • V.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (V.smul u (i : ℤ) w))
      = ∑ᶠ γ : ℤ, cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
          • V.smul v γ (V.smul u (i : ℤ) w) := by
  rw [show (∑ r ∈ Finset.range (K + L + 1),
            cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
              • V.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (V.smul u (i : ℤ) w))
        = ∑ r ∈ Finset.range (K + L + 1),
            cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
              • V.smul v ((r : ℤ) + ((a : ℤ) - 2 - (i : ℤ))) (V.smul u (i : ℤ) w) from
      Finset.sum_congr rfl fun r _ => by
        rw [show ((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ) = (r : ℤ) + ((a : ℤ) - 2 - (i : ℤ)) from by ring]]
  rw [rangeSmul_eq_finsumZ' (fun q : ℤ => cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) q)
      (fun q => V.smul v q (V.smul u (i : ℤ) w)) ((a : ℤ) - 2 - (i : ℤ))
      (fun q hq => cbz_apply_neg _ hq)
      (fun q hq => cbz_lt (by omega) (by omega))]
  rw [← finsum_comp_equiv (Equiv.addRight ((a : ℤ) - 2 - (i : ℤ)))
      (f := fun γ : ℤ => cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
        • V.smul v γ (V.smul u (i : ℤ) w))]
  refine finsum_congr fun q => ?_
  simp only [Equiv.coe_addRight]
  rw [show (q + ((a : ℤ) - 2 - (i : ℤ))) - (a : ℤ) + 2 + (i : ℤ) = q from by ring]

/-- Per-`i` V-side collapse: the `(a,r)` double sum collapses to `∑ᶠ γ, vSideCoeff • v₍ᵧ₎(u₍ᵢ₎w)`. -/
theorem vside_per_iε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) (i : ℕ) :
    (∑ a ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (K + L + 1),
        (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
            * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
          • V.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (V.smul u (i : ℤ) w))
      = ∑ᶠ γ : ℤ, vSideCoeff K L γ i • V.smul v γ (V.smul u (i : ℤ) w) := by
  -- pull the a-only scalars out of the r-sum and reindex via vside_r_reindexε
  rw [show (∑ a ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (K + L + 1),
            (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
              • V.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (V.smul u (i : ℤ) w))
        = ∑ a ∈ Finset.range (K + 1),
            (cbz (K : ℤ) (a : ℤ) * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i)
                * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
              • ∑ᶠ γ : ℤ, cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
                  • V.smul v γ (V.smul u (i : ℤ) w) from
      Finset.sum_congr rfl fun a ha => by
        rw [← vside_r_reindexε V hV K L u v w a i (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)),
          Finset.smul_sum]
        exact Finset.sum_congr rfl fun r _ => by rw [smul_smul]; ring_nf]
  -- push the a-scalar into each finsum and swap the finite a-sum past ∑ᶠ γ
  rw [show (∑ a ∈ Finset.range (K + 1),
            (cbz (K : ℤ) (a : ℤ) * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i)
                * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
              • ∑ᶠ γ : ℤ, cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
                  • V.smul v γ (V.smul u (i : ℤ) w))
        = ∑ a ∈ Finset.range (K + 1),
            ∑ᶠ γ : ℤ,
              (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
                  * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
                • V.smul v γ (V.smul u (i : ℤ) w) from
      Finset.sum_congr rfl fun a ha => by
        have haK : a ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        have hfin : Function.HasFiniteSupport
            (fun γ : ℤ => cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
              • V.smul v γ (V.smul u (i : ℤ) w)) :=
          smul_support_of_scalar_gen _ _
            (Set.Finite.subset
              (cbz_shift_support_fin' (d := (K : ℤ) + (L : ℤ) - (a : ℤ)) (by omega)
                (-(a : ℤ) + 2 + (i : ℤ)))
              (fun γ hγ => by
                rw [Function.mem_support] at hγ ⊢
                intro h; apply hγ
                rwa [show γ + (-(a : ℤ) + 2 + (i : ℤ)) = γ - (a : ℤ) + 2 + (i : ℤ) from by ring] at h))
        rw [smul_finsum' _ hfin]
        refine finsum_congr fun γ => ?_
        rw [smul_smul]; ring_nf]
  rw [← finsum_sum_comm (Finset.range (K + 1))
      (fun γ a => (cbz (K : ℤ) (a : ℤ)
          * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
          * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
        • V.smul v γ (V.smul u (i : ℤ) w))
      (fun a ha => ?_)]
  · refine finsum_congr fun γ => ?_
    rw [vSideCoeff, Finset.sum_smul]
  · -- finite support of γ ↦ (...)• v₍ᵧ₎(...) for fixed a
    have haK : a ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    refine smul_support_of_scalar_gen _ _ (Set.Finite.subset
      (cbz_shift_support_fin' (d := (K : ℤ) + (L : ℤ) - (a : ℤ)) (by omega)
        (-(a : ℤ) + 2 + (i : ℤ))) ?_)
    intro γ hγ
    rw [Function.mem_support] at hγ ⊢
    intro h; apply hγ
    rw [show (cbz (K : ℤ) (a : ℤ)
            * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
            * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
          = (cbz (K : ℤ) (a : ℤ) * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i)
              * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
              * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ + (-(a : ℤ) + 2 + (i : ℤ))) from by
        rw [show γ + (-(a : ℤ) + 2 + (i : ℤ)) = γ - (a : ℤ) + 2 + (i : ℤ) from by ring]; ring,
      h, mul_zero]

/-- Finite support in `i` of the r-summed v-side term (for fixed `a`). -/
theorem vside_a_finε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) (a : ℕ) :
    Function.HasFiniteSupport (fun i : ℕ => ∑ r ∈ Finset.range (K + L + 1),
      (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
          * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
        • V.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (V.smul u (i : ℤ) w)) := by
  obtain ⟨Nu, hNu⟩ := V.regularity u w
  apply Set.Finite.subset (Set.finite_Icc (0 : ℕ) Nu.toNat)
  intro i hi
  rw [Function.mem_support] at hi
  simp only [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  by_contra hbig
  apply hi
  have hNule : Nu ≤ (Nu.toNat : ℤ) := Int.self_le_toNat Nu
  have hi' : (Nu.toNat : ℤ) + 1 ≤ (i : ℤ) := by exact_mod_cast (by omega : Nu.toNat + 1 ≤ i)
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [show V.smul u (i : ℤ) w = (0 : 𝒱) from hNu _ (by omega)]
  simp

/-- `VSideε` as a double finsum over `(i, γ)`. -/
theorem VSide_eqε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) :
    VSideε V hV K L u v w
      = ∑ᶠ i : ℕ, ∑ᶠ γ : ℤ, vSideCoeff K L γ i • V.smul v γ (V.smul u (i : ℤ) w) := by
  rw [VSideε]
  -- step 1: per a, swap the r-sum past the i-finsum (innermost)
  rw [show (∑ a ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (K + L + 1),
            ∑ᶠ i : ℕ, (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
              • V.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (V.smul u (i : ℤ) w))
        = ∑ a ∈ Finset.range (K + 1),
            ∑ᶠ i : ℕ, ∑ r ∈ Finset.range (K + L + 1),
              (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                  * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
                • V.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (V.smul u (i : ℤ) w) from
      Finset.sum_congr rfl fun a _ => by
        rw [← finsum_sum_comm (Finset.range (K + L + 1))
            (fun i r => (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
              • V.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (V.smul u (i : ℤ) w))
            (fun r _ => vside_finε V hV K L u v w a r)]]
  -- step 2: swap the a-sum past the i-finsum
  rw [← finsum_sum_comm (Finset.range (K + 1))
      (fun i a => ∑ r ∈ Finset.range (K + L + 1),
        (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
            * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
          • V.smul v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (V.smul u (i : ℤ) w))
      (fun a _ => vside_a_finε V hV K L u v w a)]
  -- step 3: apply vside_per_iε per i
  refine finsum_congr fun i => ?_
  rw [vside_per_iε V hV K L u v w i]

/-- `Vfamε` as a double finsum over `(i, γ)` (extending the `i`-range to all `ℕ`). -/
theorem Vfam_eqε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) {Bu : ℕ}
    (hBu : ∀ a : ℕ, Bu ≤ a → V.smul u (a : ℤ) w = 0) :
    Vfamε V hV K L u v w Bu
      = ∑ᶠ i : ℕ, ∑ᶠ γ : ℤ, vCoeffTower K L i γ • V.smul v γ (V.smul u (i : ℤ) w) := by
  rw [Vfamε]
  rw [show (∑ a ∈ Finset.range Bu, ∑ n ∈ Finset.range (a + 1),
            ZhuMu.muCoeff K a n • V.superPres L v (V.smul u (a : ℤ) w) n)
        = ∑ a ∈ Finset.range Bu,
            ∑ᶠ γ : ℤ, vCoeffTower K L a γ • V.smul v γ (V.smul u (a : ℤ) w) from
      Finset.sum_congr rfl fun a _ => Vfam_innerε V hV K L a u v w]
  -- extend the range to all ℕ: terms with i ≥ Bu vanish (u₍ᵢ₎w = 0)
  refine (finsum_eq_finsetSum_of_support_subset _ (s := Finset.range Bu) ?_).symm
  intro i hi
  rw [Function.mem_support] at hi
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hge
  apply hi
  rw [show V.smul u (i : ℤ) w = (0 : 𝒱) from hBu i (by omega)]
  refine finsum_eq_zero_of_forall_eq_zero fun γ => ?_
  rw [SuperVertexAlgebra.smul_zero_right, smul_zero]

/-- **The v-family matches**: `-VSideε = Vfamε`. -/
theorem neg_VSide_eq_Vfamε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) {Bu : ℕ}
    (hBu : ∀ a : ℕ, Bu ≤ a → V.smul u (a : ℤ) w = 0) :
    - VSideε V hV K L u v w = Vfamε V hV K L u v w Bu := by
  rw [VSide_eqε, Vfam_eqε V hV K L u v w hBu, ← VOA.finsum_neg_distrib]
  refine finsum_congr fun i => ?_
  rw [← VOA.finsum_neg_distrib]
  refine finsum_congr fun γ => ?_
  rw [vSideCoeff_eq, neg_smul, neg_neg]

/-! ## U-side reindex: collect u-words by mode value. -/

/-- Per-`(b,i)` reindex of the `a`-sum to a `∑ᶠ m` over the u-mode value (`m = a-1-i`),
for a fixed inner vector `v₍ᵦ₎w`. -/
theorem uside_a_reindexε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) (i : ℕ) (b : ℤ) :
    (∑ a ∈ Finset.range (K + 1),
        (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (b + 1 - (i : ℤ))
            * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
          • V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v b w))
      = ∑ᶠ m : ℤ, (cbz (K : ℤ) (m + 1 + (i : ℤ))
            * cbz ((K : ℤ) + (L : ℤ) - (m + 1 + (i : ℤ))) (b + 1 - (i : ℤ))
            * ((-1 : ℂ) ^ i * gBinom (m + (i : ℤ)) i))
          • V.smul u m (V.smul v b w) := by
  rw [show (∑ a ∈ Finset.range (K + 1),
            (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (b + 1 - (i : ℤ))
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
              • V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v b w))
        = ∑ a ∈ Finset.range (K + 1),
            (fun p : ℤ => cbz (K : ℤ) p * cbz ((K : ℤ) + (L : ℤ) - p) (b + 1 - (i : ℤ))
                * ((-1 : ℂ) ^ i * gBinom (p - 1) i)) (a : ℤ)
              • V.smul u ((a : ℤ) + (-1 - (i : ℤ))) (V.smul v b w) from
      Finset.sum_congr rfl fun a _ => by
        simp only
        rw [show (a : ℤ) + (-1 - (i : ℤ)) = (a : ℤ) - 1 - (i : ℤ) from by ring]]
  rw [rangeSmul_eq_finsumZ'
      (fun p : ℤ => cbz (K : ℤ) p * cbz ((K : ℤ) + (L : ℤ) - p) (b + 1 - (i : ℤ))
        * ((-1 : ℂ) ^ i * gBinom (p - 1) i))
      (fun x => V.smul u x (V.smul v b w)) (-1 - (i : ℤ))
      (fun p hp => by dsimp only; rw [cbz_apply_neg (K : ℤ) hp]; ring)
      (fun p hp => by dsimp only; rw [cbz_lt (by positivity) (by omega)]; ring)]
  -- reindex the summation variable q (= old a) to the mode m via q = m+1+i
  rw [← finsum_comp_equiv (Equiv.addRight (1 + (i : ℤ)))
      (f := fun q : ℤ => (cbz (K : ℤ) q * cbz ((K : ℤ) + (L : ℤ) - q) (b + 1 - (i : ℤ))
          * ((-1 : ℂ) ^ i * gBinom (q - 1) i)) • V.smul u (q + (-1 - (i : ℤ))) (V.smul v b w))]
  refine finsum_congr fun m => ?_
  simp only [Equiv.coe_addRight]
  rw [show (m + (1 + (i : ℤ))) + (-1 - (i : ℤ)) = m from by ring,
    show (m + (1 + (i : ℤ))) = m + 1 + (i : ℤ) from by ring,
    show (m + 1 + (i : ℤ)) - 1 = m + (i : ℤ) from by ring]

/-- Per-`(a,i)` reindex of the `r`-sum to a `∑ᶠ b` over the inner v-mode value (`b = r-1+i`). -/
theorem uside_r_reindexε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) (a i : ℕ)
    (haK : a ≤ K) :
    (∑ r ∈ Finset.range (K + L + 1),
        cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
          • V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v ((r : ℤ) - 1 + (i : ℤ)) w))
      = ∑ᶠ b : ℤ, cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (b + 1 - (i : ℤ))
          • V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v b w) := by
  rw [show (∑ r ∈ Finset.range (K + L + 1),
            cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
              • V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v ((r : ℤ) - 1 + (i : ℤ)) w))
        = ∑ r ∈ Finset.range (K + L + 1),
            cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
              • V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v ((r : ℤ) + ((i : ℤ) - 1)) w) from
      Finset.sum_congr rfl fun r _ => by
        rw [show (r : ℤ) - 1 + (i : ℤ) = (r : ℤ) + ((i : ℤ) - 1) from by ring]]
  rw [rangeSmul_eq_finsumZ' (fun q : ℤ => cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) q)
      (fun x => V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v x w)) ((i : ℤ) - 1)
      (fun q hq => cbz_apply_neg _ hq)
      (fun q hq => cbz_lt (by omega) (by omega))]
  rw [← finsum_comp_equiv (Equiv.addRight ((i : ℤ) - 1))
      (f := fun b : ℤ => cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (b + 1 - (i : ℤ))
        • V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v b w))]
  refine finsum_congr fun q => ?_
  simp only [Equiv.coe_addRight]
  rw [show (q + ((i : ℤ) - 1)) + 1 - (i : ℤ) = q from by ring]

/-- Per-`i` U-side collapse: `∑_a ∑_r [...] • u₍ₐ₋₁₋ᵢ₎(v₍ᵣ₋₁₊ᵢ₎w)
    = ∑ᶠ b ∑ᶠ m, [...] • u₍ₘ₎(v₍ᵦ₎w)`. -/
theorem uside_per_iε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) (i : ℕ) :
    (∑ a ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (K + L + 1),
        (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
            * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
          • V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v ((r : ℤ) - 1 + (i : ℤ)) w))
      = ∑ᶠ b : ℤ, ∑ᶠ m : ℤ,
          (cbz (K : ℤ) (m + 1 + (i : ℤ))
              * cbz ((K : ℤ) + (L : ℤ) - (m + 1 + (i : ℤ))) (b + 1 - (i : ℤ))
              * ((-1 : ℂ) ^ i * gBinom (m + (i : ℤ)) i))
            • V.smul u m (V.smul v b w) := by
  -- step 1: per a, factor the a-scalar and reindex the r-sum to ∑ᶠ b
  rw [show (∑ a ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (K + L + 1),
            (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
              • V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v ((r : ℤ) - 1 + (i : ℤ)) w))
        = ∑ a ∈ Finset.range (K + 1),
            ∑ᶠ b : ℤ, (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (b + 1 - (i : ℤ))
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
              • V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v b w) from
      Finset.sum_congr rfl fun a ha => by
        have haK : a ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        rw [show (∑ r ∈ Finset.range (K + L + 1),
                (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                    * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
                  • V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v ((r : ℤ) - 1 + (i : ℤ)) w))
              = (cbz (K : ℤ) (a : ℤ) * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
                  • ∑ r ∈ Finset.range (K + L + 1),
                      cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                        • V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v ((r : ℤ) - 1 + (i : ℤ)) w) from by
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun r _ => by rw [smul_smul]; ring_nf]
        rw [uside_r_reindexε V hV K L u v w a i haK]
        -- push the a-scalar into the b-finsum
        have hfin : Function.HasFiniteSupport
            (fun b : ℤ => cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (b + 1 - (i : ℤ))
              • V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v b w)) :=
          smul_support_of_scalar_gen _ _
            (Set.Finite.subset
              (cbz_shift_support_fin' (d := (K : ℤ) + (L : ℤ) - (a : ℤ)) (by omega)
                (1 - (i : ℤ)))
              (fun b hb => by
                rw [Function.mem_support] at hb ⊢
                intro h; apply hb
                rwa [show b + (1 - (i : ℤ)) = b + 1 - (i : ℤ) from by ring] at h))
        rw [smul_finsum' _ hfin]
        refine finsum_congr fun b => ?_
        rw [smul_smul]; ring_nf]
  -- step 2: swap the a-sum past the b-finsum, then reindex a→m
  rw [← finsum_sum_comm (Finset.range (K + 1))
      (fun b a => (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (b + 1 - (i : ℤ))
          * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
        • V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v b w))
      (fun a ha => ?_)]
  · refine finsum_congr fun b => ?_
    rw [uside_a_reindexε V hV K L u v w i b]
  · -- finite support in b for fixed a
    have haK : a ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    refine smul_support_of_scalar_gen _ _ (Set.Finite.subset
      (cbz_shift_support_fin' (d := (K : ℤ) + (L : ℤ) - (a : ℤ)) (by omega) (1 - (i : ℤ))) ?_)
    intro b hb
    rw [Function.mem_support] at hb ⊢
    intro h; apply hb
    rw [show (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (b + 1 - (i : ℤ))
            * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
          = (cbz (K : ℤ) (a : ℤ) * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
              * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (b + (1 - (i : ℤ))) from by
        rw [show b + (1 - (i : ℤ)) = b + 1 - (i : ℤ) from by ring]; ring,
      h, mul_zero]

/-- The full `USideε` summand. -/
noncomputable def uTermε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱)
    (i : ℕ) (b m : ℤ) : 𝒱 :=
  (cbz (K : ℤ) (m + 1 + (i : ℤ))
      * cbz ((K : ℤ) + (L : ℤ) - (m + 1 + (i : ℤ))) (b + 1 - (i : ℤ))
      * ((-1 : ℂ) ^ i * gBinom (m + (i : ℤ)) i))
    • V.smul u m (V.smul v b w)

/-- `uTermε` vanishes unless `0 ≤ b+1-i` (i.e. `i ≤ b+1`). -/
theorem uTerm_eq_zero_of_ltε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱)
    (i : ℕ) (b m : ℤ) (h : b + 1 - (i : ℤ) < 0) : uTermε V hV K L u v w i b m = 0 := by
  rw [uTermε, cbz_apply_neg _ h]; simp

/-- Finite support in `i` of the r-summed u-side term (for fixed `a`). -/
theorem uside_a_finε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) (a : ℕ) :
    Function.HasFiniteSupport (fun i : ℕ => ∑ r ∈ Finset.range (K + L + 1),
      (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
          * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
        • V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v ((r : ℤ) - 1 + (i : ℤ)) w)) := by
  obtain ⟨Nv, hNv⟩ := V.regularity v w
  apply Set.Finite.subset (Set.finite_Icc (0 : ℕ) Nv.toNat)
  intro i hi
  rw [Function.mem_support] at hi
  simp only [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  by_contra hbig
  apply hi
  have hNvle : Nv ≤ (Nv.toNat : ℤ) := Int.self_le_toNat Nv
  have hi' : (Nv.toNat : ℤ) + 1 ≤ (i : ℤ) := by exact_mod_cast (by omega : Nv.toNat + 1 ≤ i)
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [show V.smul v ((r : ℤ) - 1 + (i : ℤ)) w = (0 : 𝒱) from hNv _ (by omega)]
  simp

/-- `USideε` as a triple finsum over `(i, b, m)`. -/
theorem USide_eqε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) :
    USideε V hV K L u v w
      = ∑ᶠ i : ℕ, ∑ᶠ b : ℤ, ∑ᶠ m : ℤ, uTermε V hV K L u v w i b m := by
  simp only [uTermε]
  rw [USideε]
  -- step 1: per a, swap the r-sum past the i-finsum
  rw [show (∑ a ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (K + L + 1),
            ∑ᶠ i : ℕ, (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
              • V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v ((r : ℤ) - 1 + (i : ℤ)) w))
        = ∑ a ∈ Finset.range (K + 1),
            ∑ᶠ i : ℕ, ∑ r ∈ Finset.range (K + L + 1),
              (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                  * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
                • V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v ((r : ℤ) - 1 + (i : ℤ)) w) from
      Finset.sum_congr rfl fun a _ => by
        rw [← finsum_sum_comm (Finset.range (K + L + 1))
            (fun i r => (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
              • V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v ((r : ℤ) - 1 + (i : ℤ)) w))
            (fun r _ => uside_finε V hV K L u v w a r)]]
  -- step 2: swap the a-sum past the i-finsum
  rw [← finsum_sum_comm (Finset.range (K + 1))
      (fun i a => ∑ r ∈ Finset.range (K + L + 1),
        (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
            * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
          • V.smul u ((a : ℤ) - 1 - (i : ℤ)) (V.smul v ((r : ℤ) - 1 + (i : ℤ)) w))
      (fun a _ => uside_a_finε V hV K L u v w a)]
  -- step 3: apply uside_per_iε per i
  refine finsum_congr fun i => ?_
  rw [uside_per_iε V hV K L u v w i]

/-! ## Finsum swap helpers. -/

/-- For fixed `(i,b)`, `m ↦ uTermε` has finite support (bounded by `cbz K (m+1+i)`). -/
theorem uTerm_m_finε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) (i : ℕ) (b : ℤ) :
    (Function.support (fun m : ℤ => uTermε V hV K L u v w i b m)).Finite := by
  apply Set.Finite.subset (Set.finite_Icc (-(i : ℤ) - 1) ((K : ℤ) - (i : ℤ)))
  intro m hm
  rw [Function.mem_support] at hm
  simp only [Set.mem_Icc]
  constructor
  · by_contra h
    apply hm; rw [uTermε, cbz_apply_neg (K : ℤ) (by omega), zero_mul, zero_mul, zero_smul]
  · by_contra h
    apply hm; rw [uTermε, cbz_lt (by positivity) (by omega), zero_mul, zero_mul, zero_smul]

/-- For fixed `b`, the pair `(i,m) ↦ uTermε` has finite support. -/
theorem uTerm_im_finε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) (b : ℤ) :
    (Function.support (fun p : ℕ × ℤ => uTermε V hV K L u v w p.1 b p.2)).Finite := by
  apply Set.Finite.subset
    ((Set.finite_Icc (0 : ℕ) (b.toNat + 1)).prod (Set.finite_Icc (-(b) - 2) (K : ℤ)))
  intro p hp
  rw [Function.mem_support] at hp
  simp only [Set.mem_prod, Set.mem_Icc]
  -- from cbz K (m+1+i) ≠ 0: 0 ≤ m+1+i ≤ K; from cbz(...)(b+1-i) ≠ 0: 0 ≤ b+1-i
  have hc1 : cbz (K : ℤ) (p.2 + 1 + (p.1 : ℤ)) ≠ 0 := by
    intro h; apply hp; rw [uTermε, h, zero_mul, zero_mul, zero_smul]
  have hc2 : cbz ((K : ℤ) + (L : ℤ) - (p.2 + 1 + (p.1 : ℤ))) (b + 1 - (p.1 : ℤ)) ≠ 0 := by
    intro h; apply hp; rw [uTermε, h, mul_zero, zero_mul, zero_smul]
  have h1lo : (0 : ℤ) ≤ p.2 + 1 + (p.1 : ℤ) := by
    by_contra h; exact hc1 (cbz_apply_neg (K : ℤ) (by omega))
  have h1hi : p.2 + 1 + (p.1 : ℤ) ≤ (K : ℤ) := by
    by_contra h; exact hc1 (cbz_lt (by positivity) (by omega))
  have h2lo : (0 : ℤ) ≤ b + 1 - (p.1 : ℤ) := by
    by_contra h; exact hc2 (cbz_apply_neg _ (by omega))
  refine ⟨⟨Nat.zero_le _, ?_⟩, by omega, by omega⟩
  -- i ≤ b+1, so i ≤ b.toNat+1
  have : (p.1 : ℤ) ≤ b + 1 := by omega
  omega

/-- The pair `(i,b) ↦ ∑ᶠ m, uTermε` has finite support. -/
theorem uTerm_ib_finε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) :
    (Function.support (fun p : ℕ × ℤ => ∑ᶠ m : ℤ, uTermε V hV K L u v w p.1 p.2 m)).Finite := by
  obtain ⟨Nv, hNv⟩ := V.regularity v w
  apply Set.Finite.subset
    ((Set.finite_Icc (0 : ℕ) Nv.toNat).prod (Set.finite_Icc (-1 : ℤ) (Nv - 1)))
  intro p hp
  rw [Function.mem_support] at hp
  simp only [Set.mem_prod, Set.mem_Icc]
  -- nonzero finsum ⟹ ∃ m, uTermε ≠ 0 ⟹ b+1-i ≥ 0 and v₍b₎w ≠ 0
  have hex : ∃ m : ℤ, uTermε V hV K L u v w p.1 p.2 m ≠ 0 := by
    by_contra hall
    exact hp (finsum_eq_zero_of_forall_eq_zero fun m => not_not.mp (not_exists.mp hall m))
  obtain ⟨m, hm⟩ := hex
  -- from uTermε ≠ 0: cbz(...)(b+1-i) ≠ 0 ⟹ b+1-i ≥ 0
  have h2lo : (0 : ℤ) ≤ p.2 + 1 - (p.1 : ℤ) := by
    by_contra h
    exact hm (uTerm_eq_zero_of_ltε V hV K L u v w p.1 p.2 m (by omega))
  -- from uTermε ≠ 0: v₍b₎w ≠ 0 ⟹ p.2 < Nv
  have hvb : V.smul v p.2 w ≠ 0 := by
    intro h
    apply hm
    rw [uTermε, h, SuperVertexAlgebra.smul_zero_right, smul_zero]
  have hbNv : p.2 < Nv := by
    by_contra h
    exact hvb (hNv p.2 (by omega))
  have hNvle : Nv ≤ (Nv.toNat : ℤ) := Int.self_le_toNat Nv
  refine ⟨⟨Nat.zero_le _, ?_⟩, by omega, by omega⟩
  -- i ≤ b+1 ≤ Nv, so i ≤ Nv.toNat
  have hib : (p.1 : ℤ) ≤ p.2 + 1 := by omega
  have : (p.1 : ℤ) ≤ Nv := by omega
  omega

/-- `USideε` with the `i`-finsum innermost: `∑ᶠ b ∑ᶠ m ∑ᶠ i, uTermε`. -/
theorem USide_eq2ε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) :
    USideε V hV K L u v w
      = ∑ᶠ b : ℤ, ∑ᶠ m : ℤ, ∑ᶠ i : ℕ, uTermε V hV K L u v w i b m := by
  rw [USide_eqε]
  -- swap i and b (outermost two)
  rw [swap_finsum_NZ (fun i b => ∑ᶠ m : ℤ, uTermε V hV K L u v w i b m) (uTerm_ib_finε V hV K L u v w)]
  -- per b, swap i and m
  refine finsum_congr fun b => ?_
  rw [swap_finsum_NZ (fun i m => uTermε V hV K L u v w i b m) (uTerm_im_finε V hV K L u v w b)]

/-- Pull `u₍ₘ₎(v₍ᵦ₎w)` out of the `i`-finsum. -/
theorem uTerm_i_collapseε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) (b m : ℤ) :
    (∑ᶠ i : ℕ, uTermε V hV K L u v w i b m)
      = uSideScalar K L b m • V.smul u m (V.smul v b w) := by
  rw [uSideScalar, finsum_smul]
  refine finsum_congr fun i => ?_
  rw [uTermε]

/-- Inner reindex (per `p`) of the `c`-sum to `∑ᶠ b` over the inner v-mode. -/
theorem rhs_c_reindexε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) (p : ℕ) :
    (∑ c ∈ Finset.range (L + 1),
        (cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) (c : ℤ))
          • V.smul u ((p : ℤ) - 1) (V.smul v ((c : ℤ) - 1) w))
      = ∑ᶠ b : ℤ, (cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) (b + 1))
          • V.smul u ((p : ℤ) - 1) (V.smul v b w) := by
  rw [show (∑ c ∈ Finset.range (L + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) (c : ℤ))
              • V.smul u ((p : ℤ) - 1) (V.smul v ((c : ℤ) - 1) w))
        = ∑ c ∈ Finset.range (L + 1),
            (fun q : ℤ => cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) q) (c : ℤ)
              • V.smul u ((p : ℤ) - 1) (V.smul v ((c : ℤ) + (-1)) w) from
      Finset.sum_congr rfl fun c _ => by
        simp only
        rw [show (c : ℤ) + (-1) = (c : ℤ) - 1 from by ring]]
  rw [rangeSmul_eq_finsumZ'
      (fun q : ℤ => cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) q)
      (fun x => V.smul u ((p : ℤ) - 1) (V.smul v x w)) (-1)
      (fun q hq => by dsimp only; rw [cbz_apply_neg (L : ℤ) hq, mul_zero])
      (fun q hq => by dsimp only
                      rw [cbz_lt (show (0:ℤ) ≤ (L:ℤ) by positivity) (show (L:ℤ) < q by omega),
                        mul_zero])]
  rw [← finsum_comp_equiv (Equiv.addRight (1 : ℤ))
      (f := fun q : ℤ => (cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) q)
        • V.smul u ((p : ℤ) - 1) (V.smul v (q + (-1)) w))]
  refine finsum_congr fun b => ?_
  simp only [Equiv.coe_addRight]
  rw [show (b + (1 : ℤ)) + (-1) = b from by ring]

/-- The full `u*(v*w)` as `∑ᶠ b ∑ᶠ m, cbz K (m+1)·cbz L (b+1) • u₍ₘ₎(v₍ᵦ₎w)`. -/
theorem RHS_eqε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) {K L : ℕ} {u v : 𝒱}
    (hu : u ∈ V.gradingZ (K : ℤ)) (hv : v ∈ V.gradingZ (L : ℤ)) (w : 𝒱) :
    V.superZhuMul hV u (V.superZhuMul hV v w)
      = ∑ᶠ b : ℤ, ∑ᶠ m : ℤ,
          (cbz (K : ℤ) (m + 1) * cbz (L : ℤ) (b + 1)) • V.smul u m (V.smul v b w) := by
  rw [uvw_expandε V hV hu hv w]
  -- reindex each inner c-sum to ∑ᶠ b
  rw [show (∑ p ∈ Finset.range (K + 1), ∑ c ∈ Finset.range (L + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) (c : ℤ))
              • V.smul u ((p : ℤ) - 1) (V.smul v ((c : ℤ) - 1) w))
        = ∑ p ∈ Finset.range (K + 1),
            ∑ᶠ b : ℤ, (cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) (b + 1))
              • V.smul u ((p : ℤ) - 1) (V.smul v b w) from
      Finset.sum_congr rfl fun p _ => rhs_c_reindexε V hV K L u v w p]
  -- swap the finite p-sum past ∑ᶠ b
  rw [← finsum_sum_comm (Finset.range (K + 1))
      (fun b p => (cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) (b + 1))
        • V.smul u ((p : ℤ) - 1) (V.smul v b w))
      (fun p _ => ?_)]
  · -- per b, reindex the p-sum to ∑ᶠ m
    refine finsum_congr fun b => ?_
    rw [show (∑ p ∈ Finset.range (K + 1),
              (cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) (b + 1))
                • V.smul u ((p : ℤ) - 1) (V.smul v b w))
          = ∑ p ∈ Finset.range (K + 1),
              (fun q : ℤ => cbz (K : ℤ) q * cbz (L : ℤ) (b + 1)) (p : ℤ)
                • V.smul u ((p : ℤ) + (-1)) (V.smul v b w) from
        Finset.sum_congr rfl fun p _ => by
          simp only; rw [show (p : ℤ) + (-1) = (p : ℤ) - 1 from by ring]]
    rw [rangeSmul_eq_finsumZ'
        (fun q : ℤ => cbz (K : ℤ) q * cbz (L : ℤ) (b + 1))
        (fun x => V.smul u x (V.smul v b w)) (-1)
        (fun q hq => by dsimp only; rw [cbz_apply_neg (K : ℤ) hq, zero_mul])
        (fun q hq => by dsimp only; rw [cbz_lt (by positivity) (by omega), zero_mul])]
    rw [← finsum_comp_equiv (Equiv.addRight (1 : ℤ))
        (f := fun q : ℤ => (cbz (K : ℤ) q * cbz (L : ℤ) (b + 1))
          • V.smul u (q + (-1)) (V.smul v b w))]
    refine finsum_congr fun m => ?_
    simp only [Equiv.coe_addRight]
    rw [show (m + (1 : ℤ)) + (-1) = m from by ring]
  · -- finite support in b for fixed p
    refine smul_support_of_scalar_gen _ _ (Set.Finite.subset
      (cbz_shift_support_fin' (d := (L : ℤ)) (by positivity) 1) ?_)
    intro b hb
    rw [Function.mem_support] at hb ⊢
    intro h; apply hb
    rw [show (cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) (b + 1))
          = cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) (b + 1) from rfl, h, mul_zero]

/-- `USideε` collapsed: `∑ᶠ b ∑ᶠ m, uSideScalar • u₍ₘ₎(v₍ᵦ₎w)`. -/
theorem USide_eq3ε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) :
    USideε V hV K L u v w
      = ∑ᶠ b : ℤ, ∑ᶠ m : ℤ, uSideScalar K L b m • V.smul u m (V.smul v b w) := by
  rw [USide_eq2ε]
  refine finsum_congr fun b => ?_
  refine finsum_congr fun m => ?_
  rw [uTerm_i_collapseε V hV K L u v w b m]

/-- `Ufamε` as a double `ℤ`-finsum with the extended coefficient. -/
theorem Ufam_eqε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) {Bv : ℕ}
    (hBv : ∀ b : ℕ, Bv ≤ b → V.smul v (b : ℤ) w = 0) :
    Ufamε V hV K L u v w Bv
      = ∑ᶠ b : ℤ, ∑ᶠ m : ℤ,
          (if 0 ≤ b then uCoeffTower K L b.toNat m else 0) • V.smul u m (V.smul v b w) := by
  rw [Ufamε]
  rw [show (∑ b ∈ Finset.range Bv, ∑ n ∈ Finset.range (b + 1),
            ZhuMu.muCoeff L b n • V.superPres K u (V.smul v (b : ℤ) w) n)
        = ∑ b ∈ Finset.range Bv,
            ∑ᶠ m : ℤ, uCoeffTower K L b m • V.smul u m (V.smul v (b : ℤ) w) from
      Finset.sum_congr rfl fun b _ => Ufam_innerε V hV K L b u v w]
  -- convert the finite ℕ-sum over b to a ℤ-finsum (extend by the if-coefficient)
  -- first: ∑_{b∈range Bv} F b = ∑ᶠ b:ℕ F b  (tail vanishes since v₍b₎w = 0)
  rw [show (∑ b ∈ Finset.range Bv,
            ∑ᶠ m : ℤ, uCoeffTower K L b m • V.smul u m (V.smul v (b : ℤ) w))
        = ∑ᶠ b : ℕ, ∑ᶠ m : ℤ, uCoeffTower K L b m • V.smul u m (V.smul v (b : ℤ) w) from by
      refine (finsum_eq_finsetSum_of_support_subset _ (s := Finset.range Bv) ?_).symm
      intro b hb
      rw [Function.mem_support] at hb
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hge
      apply hb
      rw [show V.smul v (b : ℤ) w = (0 : 𝒱) from hBv b (by omega)]
      refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
      rw [SuperVertexAlgebra.smul_zero_right, smul_zero]]
  -- second: ∑ᶠ b:ℕ G b = ∑ᶠ b:ℤ (if 0≤b then G b.toNat else 0)
  rw [finsum_nat_to_int
      (fun b : ℕ => ∑ᶠ m : ℤ, uCoeffTower K L b m • V.smul u m (V.smul v (b : ℤ) w))
      (fun b : ℤ => ∑ᶠ m : ℤ, (if 0 ≤ b then uCoeffTower K L b.toNat m else 0)
        • V.smul u m (V.smul v b w))
      (fun p hp => by
        refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
        rw [if_neg (by omega), zero_smul])
      (fun j => by
        refine finsum_congr fun m => ?_
        rw [if_pos (by positivity), Int.toNat_natCast])]

/-- The RHS-term `b ↦ ∑ᶠ m, rhsCoeff • u₍ₘ₎(v₍ᵦ₎w)` has finite support in `b`. -/
theorem rhs_b_finε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) :
    (Function.support (fun b : ℤ =>
      ∑ᶠ m : ℤ, (cbz (K : ℤ) (m + 1) * cbz (L : ℤ) (b + 1))
        • V.smul u m (V.smul v b w))).Finite := by
  apply Set.Finite.subset (Set.finite_Icc (-1 : ℤ) ((L : ℤ) - 1))
  intro b hb
  rw [Function.mem_support] at hb
  simp only [Set.mem_Icc]
  -- nonzero ⟹ cbz L (b+1) ≠ 0 ⟹ 0 ≤ b+1 ≤ L
  have hex : ∃ m : ℤ, (cbz (K : ℤ) (m + 1) * cbz (L : ℤ) (b + 1))
      • V.smul u m (V.smul v b w) ≠ 0 := by
    by_contra hall
    exact hb (finsum_eq_zero_of_forall_eq_zero fun m => not_not.mp (not_exists.mp hall m))
  obtain ⟨m, hm⟩ := hex
  have hcL : cbz (L : ℤ) (b + 1) ≠ 0 := by
    intro h; apply hm; rw [h, mul_zero, zero_smul]
  constructor
  · by_contra h; exact hcL (cbz_apply_neg (L : ℤ) (by omega))
  · by_contra h; exact hcL (cbz_lt (by positivity) (by omega))

/-- The Ufamε-term `b ↦ ∑ᶠ m, uCoeffExt • u₍ₘ₎(v₍ᵦ₎w)` has finite support in `b`
(needs `v₍ᵦ₎w = 0` for `b ≥ Nv`). -/
theorem ufam_b_finε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (K L : ℕ) (u v w : 𝒱) :
    (Function.support (fun b : ℤ =>
      ∑ᶠ m : ℤ, (if 0 ≤ b then uCoeffTower K L b.toNat m else 0)
        • V.smul u m (V.smul v b w))).Finite := by
  obtain ⟨Nv, hNv⟩ := V.regularity v w
  apply Set.Finite.subset (Set.finite_Icc (0 : ℤ) (Nv - 1))
  intro b hb
  rw [Function.mem_support] at hb
  simp only [Set.mem_Icc]
  have hex : ∃ m : ℤ, (if 0 ≤ b then uCoeffTower K L b.toNat m else 0)
      • V.smul u m (V.smul v b w) ≠ 0 := by
    by_contra hall
    exact hb (finsum_eq_zero_of_forall_eq_zero fun m => not_not.mp (not_exists.mp hall m))
  obtain ⟨m, hm⟩ := hex
  have hb0 : 0 ≤ b := by
    by_contra h; apply hm; rw [if_neg h, zero_smul]
  have hvb : V.smul v b w ≠ 0 := by
    intro h; apply hm; rw [h, SuperVertexAlgebra.smul_zero_right, smul_zero]
  have hNvle : Nv ≤ (Nv.toNat : ℤ) := Int.self_le_toNat Nv
  refine ⟨hb0, ?_⟩
  by_contra h
  exact hvb (hNv b (by omega))

/-- **The U-family matches**: `USideε = Ufamε + u*(v*w)`. -/
theorem USide_eq_Ufam_add_RHSε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) {K L : ℕ} {u v : 𝒱}
    (hu : u ∈ V.gradingZ (K : ℤ)) (hv : v ∈ V.gradingZ (L : ℤ)) (w : 𝒱) {Bv : ℕ}
    (hBv : ∀ b : ℕ, Bv ≤ b → V.smul v (b : ℤ) w = 0) :
    USideε V hV K L u v w = Ufamε V hV K L u v w Bv + V.superZhuMul hV u (V.superZhuMul hV v w) := by
  rw [USide_eq3ε, Ufam_eqε V hV K L u v w hBv, RHS_eqε V hV hu hv w]
  -- combine Ufamε + RHS into a single double finsum (add at b-level then m-level)
  rw [← finsum_add_distrib (ufam_b_finε V hV K L u v w) (rhs_b_finε V hV K L u v w)]
  refine finsum_congr fun b => ?_
  rw [← finsum_add_distrib
      (smul_support_of_scalar_gen _ _ (uCoeffExt_m_fin K L b))
      (smul_support_of_scalar_gen _ _ (rhsCoeff_m_fin K L b))]
  refine finsum_congr fun m => ?_
  rw [← add_smul]
  congr 1
  -- uSideScalar = uCoeffExt + rhsCoeff
  linear_combination uSideScalar_sub_rhs K L b m

/-- **The associator decomposition equality.** -/
theorem assoc_eqε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) {K L : ℕ} {p q : ZMod 2}
    {u v : 𝒱} (hu : u ∈ V.gradingZ (K : ℤ)) (hup : u ∈ V.parity p)
    (hv : v ∈ V.gradingZ (L : ℤ)) (hvq : v ∈ V.parity q) (w : 𝒱)
    {Bu Bv : ℕ}
    (hBv : ∀ b : ℕ, Bv ≤ b → V.smul v (b : ℤ) w = 0)
    (hBu : ∀ a : ℕ, Bu ≤ a → V.smul u (a : ℤ) w = 0) :
    V.superZhuMul hV (V.superZhuMul hV u v) w - V.superZhuMul hV u (V.superZhuMul hV v w)
      = Ufamε V hV K L u v w Bv + (koszul p q) • Vfamε V hV K L u v w Bu := by
  rw [lhs_splitε V hV hu hup hv hvq w, USide_eq_Ufam_add_RHSε V hV hu hv w hBv,
    ← neg_VSide_eq_Vfamε V hV K L u v w hBu,
    VSideX_eq_smulε V hV (koszul p q) K L u v w, smul_neg]
  abel

/-- **The associator core (Zhu Thm 2.1.2 crux).** -/
theorem associator_coreε (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) {K L : ℕ} {p q : ZMod 2}
    {u v : 𝒱} (hu : u ∈ V.gradingZ (K : ℤ)) (hup : u ∈ V.parity p)
    (hv : v ∈ V.gradingZ (L : ℤ)) (hvq : v ∈ V.parity q) (w : 𝒱) :
    V.superZhuMul hV (V.superZhuMul hV u v) w - V.superZhuMul hV u (V.superZhuMul hV v w)
      ∈ V.superO hV := by
  obtain ⟨Nv, hNv⟩ := V.regularity v w
  obtain ⟨Nu, hNu⟩ := V.regularity u w
  refine assoc_eqε V hV hu hup hv hvq w (Bu := Nu.toNat) (Bv := Nv.toNat)
    (fun b hb => hNv (b : ℤ) (by omega)) (fun a ha => hNu (a : ℤ) (by omega)) ▸ ?_
  exact Submodule.add_mem _ (Ufam_mem_Oε V hV hu v w _)
    (Submodule.smul_mem _ _ (Vfam_mem_Oε V hV hv u w _))

end SuperZhuAssoc
