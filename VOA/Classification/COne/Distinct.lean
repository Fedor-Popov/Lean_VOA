/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.AutV2Bridge
import VOA.Moonshine.LatticeGradedDim
import VOA.Classification.COne.LatticeNice
import VOA.Classification.COne.LatticeStronglyRational

/-!
# Pairwise distinctness in Gannon–Rayhaun Theorem 3.1

`GannonRayhaunDistinct` (`Statement.lean`) says a VOA carries at most one label of the list. This
file proves it for every pair of labels except two named residuals, by comparing graded
dimensions.

## Method
* `finrank_grading_eq_of_iso`: isomorphic VOAs have equal `dim V_n` (universe-polymorphic).
* Lattice: `V2m_finrank_lt` (`dim (V_{2m})_k = p(k)`, `k < m`), `V2m_finrank_self`
  (`p(m) + 2`), `V2m_finrank_mid` (`p(k) + 2p(k−m)`, `m ≤ k < 4m`).
* Plus: `V2mPlus_two_mul`: `2 dim (V_{2m}⁺)_k = dim (V_{2m})_k + (P⁺ − P⁻)(k)`
  (from `LatGen.two_mul_finrank_plusK_eq_signed`).
* Exceptional: `commute_of_fixes_weight_one`: a finite `G ≤ Aut V₂` fixing a nonzero vector of
  `(V₂)₁` is abelian (conjugate into the torus). Hence `orbifold_V2_finrank_one`:
  `dim (V₂^G)₁ = 0` for `G ≅ A₄, S₄, A₅`. With `L₁(V₂)₁ = 0` and Virasoro commutators,
  `orbifold_V2_finrank_two_le`, `orbifold_V2_finrank_three_le`: `dim (V₂^G)₂, dim (V₂^G)₃ ≤ 1`
  (`L₁ : (V₂)₂ ↠ (V₂)₁` and `(L₁², L₂) : (V₂)₃ ↠ (V₂)₁²` have one-dimensional kernels).

## Main results (all unconditional)
* (a) `lat_lat_eq`, (b) `plus_plus_eq` (separated at weight `min m m'`);
* (c) `not_lat_plus` (weight 1);
* (d) `not_lat_exceptional` (weight 1), `not_plus_exceptional_small` (`V₄⁺` at weight 2,
  `V₆⁺` at weight 3).
* `gannonRayhaunDistinct_of_residuals : PlusExceptionalResidual → ExceptionalResidual →
  GannonRayhaunDistinct`.

## The two residuals (proved in `DistinctResiduals.lean`, giving `gannonRayhaunDistinct`)
* `PlusExceptionalResidual`: `V_{2m}⁺` (`m ≥ 4`) against `V₂^{A₄,S₄,A₅}`. They agree in
  dimension through weight 3 (`1, 0, 1, 1`); weight 4 gives `≥ 3` vs `2`, which needs the
  `G`-invariants of the spin-two primaries of `(V₂)₄`.
* `ExceptionalResidual`: tetra vs octa vs icosa (first differences at weights 9 and 16).

## Status
`sorry`-free, no new axioms.
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice Module

/-! ## Graded dimensions are isomorphism invariants -/

section Iso

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {𝒲 : Type v} [AddCommGroup 𝒲] [Module ℂ 𝒲]
  {V : VertexOperatorAlgebra 𝒱} {T : VertexOperatorAlgebra 𝒲}

/-- A conformal VOA homomorphism preserves the grading (universe-polymorphic). -/
theorem voaHom_map_grading_poly {φ : 𝒱 →ₗ[ℂ] 𝒲} (hφ : IsVOAHom V T φ)
    (hω : φ V.conformalVector = T.conformalVector) {n : ℤ} {x : 𝒱} (hx : x ∈ V.grading n) :
    φ x ∈ T.grading n := by
  refine mem_grading_of_L0 T ?_
  have h1 : φ (V.L 0 x) = T.L 0 (φ x) := by
    have := hφ.map_smul V.conformalVector (0 + 1) x
    rw [hω] at this
    exact this
  rw [← h1, V.L_zero_grading x hx, map_smul]

/-- **Isomorphic VOAs have the same graded dimensions.** -/
theorem finrank_grading_eq_of_iso (h : VOAIsomorphic V T) (n : ℤ) :
    finrank ℂ (V.grading n) = finrank ℂ (T.grading n) := by
  obtain ⟨e, he, hω⟩ := h
  have he' : IsVOAHom T V e.symm.toLinearMap :=
    { map_vacuum := by
        apply e.injective
        simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
        exact he.map_vacuum.symm
      map_smul := fun u n x => by
        apply e.injective
        simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
        have := he.map_smul (e.symm u) n (e.symm x)
        simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply] at this
        exact this.symm }
  have hω' : e.symm T.conformalVector = V.conformalVector := by
    rw [← hω, LinearEquiv.symm_apply_apply]
  have hmap : (V.grading n).map (e : 𝒱 →ₗ[ℂ] 𝒲) = T.grading n := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact voaHom_map_grading_poly he hω hx
    · intro y hy
      exact ⟨e.symm y, voaHom_map_grading_poly he' hω' hy, by simp⟩
  exact (e.ofSubmodules _ _ hmap).finrank_eq

end Iso

/-! ## Low-weight dimensions of `V_{2m}` -/

section Lattice

variable (m : ℕ) (hm : 1 ≤ m)

theorem normLE_latP_lt (k : ℕ) (hk : k < m) :
    normLE (latP m) (latP_posDef m hm) k = {0} := by
  ext v
  rw [mem_normLE, halfNorm_latP, Finset.mem_singleton]
  have key : ∀ w : ℤ, ((m : ℤ) * w ^ 2 ≤ k ↔ w = 0) := by
    intro w
    constructor
    · intro h
      by_contra hv
      have : 1 ≤ w ^ 2 := by
        have := pow_pos (abs_pos.mpr hv) 2
        rw [sq_abs] at this; omega
      have : (m : ℤ) ≤ (m : ℤ) * w ^ 2 := by nlinarith
      omega
    · rintro rfl
      simp
  exact key v

/-- `dim (V_{2m})_k = p(k)` for `k < m`. -/
theorem V2m_finrank_lt (k : ℕ) (hk : k < m) :
    finrank ℂ ((V2m m hm).grading k) = fockCount 1 k := by
  change finrank ℂ (gradingLatGen (latP m) ((k : ℕ) : ℤ)) = _
  rw [finrank_gradingLatGen_eq_sum (latP m) (latP_posDef m hm) k, normLE_latP_lt m hm k hk,
    Finset.sum_singleton, rank_latP]
  congr 1
  change ((k : ℤ) - LatGen.halfNorm (latP m) (0 : ℤ)).toNat = k
  rw [halfNorm_latP]; simp

open Classical in
theorem normLE_latP_self :
    normLE (latP m) (latP_posDef m hm) m = {0, a1 m, -a1 m} := by
  ext v
  rw [mem_normLE, halfNorm_latP, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  have key : ∀ w : ℤ, ((m : ℤ) * w ^ 2 ≤ m ↔ w = 0 ∨ w = 1 ∨ w = -1) := by
    intro w
    constructor
    · intro h
      have h1 : w ^ 2 ≤ 1 := by
        by_contra h2
        push Not at h2
        have : (m : ℤ) * 1 < (m : ℤ) * w ^ 2 :=
          mul_lt_mul_of_pos_left h2 (by exact_mod_cast hm)
        omega
      have : -1 ≤ w ∧ w ≤ 1 := by
        constructor <;> nlinarith
      omega
    · rintro (rfl | rfl | rfl) <;> simp
  exact key v

/-- `dim (V_{2m})_m = p(m) + 2` (the extra states are `e^{±α}`). -/
theorem V2m_finrank_self :
    finrank ℂ ((V2m m hm).grading m) = fockCount 1 m + 2 := by
  classical
  change finrank ℂ (gradingLatGen (latP m) ((m : ℕ) : ℤ)) = _
  rw [finrank_gradingLatGen_eq_sum (latP m) (latP_posDef m hm) m, normLE_latP_self m hm]
  have h01 : (0 : (latP m).carrier) ∉ ({a1 m, -a1 m} : Finset (latP m).carrier) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    change ¬ ((0 : ℤ) = 1 ∨ (0 : ℤ) = -1); omega
  have h1 : a1 m ∉ ({-a1 m} : Finset (latP m).carrier) := by
    rw [Finset.mem_singleton]
    change ¬ ((1 : ℤ) = -1); omega
  rw [Finset.sum_insert h01, Finset.sum_insert h1, Finset.sum_singleton, rank_latP]
  have e0 : ((m : ℤ) - LatGen.halfNorm (latP m) 0).toNat = m := by
    rw [halfNorm_latP]; simp
  have e1 : ((m : ℤ) - LatGen.halfNorm (latP m) (a1 m)).toNat = 0 := by
    rw [halfNorm_latP]; simp
  have e2 : ((m : ℤ) - LatGen.halfNorm (latP m) (-a1 m)).toNat = 0 := by
    rw [halfNorm_latP]; change ((m : ℤ) - (m : ℤ) * (-1 : ℤ) ^ 2).toNat = 0; simp
  rw [e0, e1, e2, fockCount_zero]
open Classical in
theorem normLE_latP_mid (k : ℕ) (h1 : m ≤ k) (h2 : k < 4 * m) :
    normLE (latP m) (latP_posDef m hm) k = {0, a1 m, -a1 m} := by
  ext v
  rw [mem_normLE, halfNorm_latP, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  have key : ∀ w : ℤ, ((m : ℤ) * w ^ 2 ≤ k ↔ w = 0 ∨ w = 1 ∨ w = -1) := by
    intro w
    constructor
    · intro h
      have h1 : w ^ 2 < 4 := by
        by_contra h2
        push Not at h2
        have : (m : ℤ) * 4 ≤ (m : ℤ) * w ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        omega
      have : -1 ≤ w ∧ w ≤ 1 := by
        constructor <;> nlinarith
      omega
    · rintro (rfl | rfl | rfl) <;> simp <;> omega
  exact key v

/-- `dim (V_{2m})_k = p(k) + 2 p(k - m)` for `m ≤ k < 4m`. -/
theorem V2m_finrank_mid (k : ℕ) (h1 : m ≤ k) (h2 : k < 4 * m) :
    finrank ℂ ((V2m m hm).grading k) = fockCount 1 k + 2 * fockCount 1 (k - m) := by
  classical
  change finrank ℂ (gradingLatGen (latP m) ((k : ℕ) : ℤ)) = _
  rw [finrank_gradingLatGen_eq_sum (latP m) (latP_posDef m hm) k, normLE_latP_mid m hm k h1 h2]
  have h01 : (0 : (latP m).carrier) ∉ ({a1 m, -a1 m} : Finset (latP m).carrier) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    change ¬ ((0 : ℤ) = 1 ∨ (0 : ℤ) = -1); omega
  have h1' : a1 m ∉ ({-a1 m} : Finset (latP m).carrier) := by
    rw [Finset.mem_singleton]
    change ¬ ((1 : ℤ) = -1); omega
  rw [Finset.sum_insert h01, Finset.sum_insert h1', Finset.sum_singleton, rank_latP]
  have e0 : ((k : ℤ) - LatGen.halfNorm (latP m) 0).toNat = k := by
    rw [halfNorm_latP]; simp
  have e1 : ((k : ℤ) - LatGen.halfNorm (latP m) (a1 m)).toNat = k - m := by
    rw [halfNorm_latP]; change ((k : ℤ) - (m : ℤ) * (1 : ℤ) ^ 2).toNat = k - m; omega
  have e2 : ((k : ℤ) - LatGen.halfNorm (latP m) (-a1 m)).toNat = k - m := by
    rw [halfNorm_latP]; change ((k : ℤ) - (m : ℤ) * (-1 : ℤ) ^ 2).toNat = k - m; omega
  rw [e0, e1, e2]; ring

end Lattice

/-! ## Low-weight dimensions of `V_{2m}⁺` -/

section Plus

variable (m : ℕ) (hm : 1 ≤ m)

/-- The weight-`k` space of `V_{2m}⁺` is the `θ`-fixed part of `(V_{2m})_k`. -/
noncomputable def V2mPlusGradingEquiv (k : ℤ) :
    (V2mPlus m hm).grading k ≃ₗ[ℂ] plusK (latP m) k := by
  refine (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).trans
    (LinearEquiv.ofEq _ _ ?_)
  rw [show (V2mPlus m hm).grading k = ((V2m m hm).grading k).comap
      (orbifold (Subgroup.zpowers (thetaV2m m hm))).carrier.subtype from rfl,
    Submodule.map_comap_subtype]
  ext x
  rw [Submodule.mem_inf, mem_plusK, VOA.Classification.COne.mem_orbifold_zpowers_iff, and_comm]
  rfl

/-- `2·dim (V_{2m}⁺)_k = dim (V_{2m})_k + (P⁺ − P⁻)(k)`. -/
theorem V2mPlus_two_mul (k : ℕ) :
    2 * (finrank ℂ ((V2mPlus m hm).grading k) : ℤ)
      = finrank ℂ ((V2m m hm).grading k) + fockSigned 1 k := by
  rw [(V2mPlusGradingEquiv m hm k).finrank_eq]
  have h := two_mul_finrank_plusK_eq_signed (latP m) (latP_posDef m hm) (latP_even m) k
  have hr : fockSigned (rank (latP m)) k = fockSigned 1 k := congrArg (fockSigned · k) (rank_latP m)
  rw [hr] at h
  exact h

end Plus

theorem fockSigned_one_one : fockSigned 1 1 = -1 := by
  rw [fockSigned_one]; decide

theorem fockCount_one_one : fockCount 1 1 = 1 := fockCount_one 1

/-! ## Separating the infinite families -/

section Families

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}

/-- `dim (V_{2m})_1 ≥ 1` (the Heisenberg state). -/
theorem V2m_finrank_one_pos (m : ℕ) (hm : 1 ≤ m) : 1 ≤ finrank ℂ ((V2m m hm).grading 1) := by
  rcases Nat.lt_or_ge 1 m with h | h
  · have := V2m_finrank_lt m hm 1 h
    rw [fockCount_one_one] at this
    exact_mod_cast this.ge
  · obtain rfl : m = 1 := le_antisymm h hm
    have := V2m_finrank_self 1 hm
    push_cast at this
    rw [this]; omega

/-- `dim (V_{2m}⁺)_1 = 0` for `m ≥ 2`. -/
theorem V2mPlus_finrank_one (m : ℕ) (hm : 1 ≤ m) (h2 : 2 ≤ m) :
    finrank ℂ ((V2mPlus m hm).grading 1) = 0 := by
  have h := V2mPlus_two_mul m hm 1
  rw [V2m_finrank_lt m hm 1 (by omega), fockCount_one_one, fockSigned_one_one] at h
  push_cast at h
  omega

/-- **(a)** `V_{2m} ≅ V_{2m'}` forces `m = m'`. -/
theorem lat_lat_eq {m m' : ℕ} (h : HasCOneLabel V (.lat m)) (h' : HasCOneLabel V (.lat m')) :
    m = m' := by
  obtain ⟨hm, e⟩ := h
  obtain ⟨hm', e'⟩ := h'
  have key : ∀ a b : ℕ, ∀ (ha : 1 ≤ a) (hb : 1 ≤ b), a < b →
      VOAIsomorphic V (V2m a ha) → VOAIsomorphic V (V2m b hb) → False := by
    intro a b ha hb hab ea eb
    have h1 := finrank_grading_eq_of_iso ea a
    have h2 := finrank_grading_eq_of_iso eb a
    rw [V2m_finrank_self a ha] at h1
    rw [V2m_finrank_lt b hb a hab] at h2
    omega
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exact (key m m' hm hm' hlt e e').elim
  · exact heq
  · exact (key m' m hm' hm hgt e' e).elim

/-- **(b)** `V_{2m}⁺ ≅ V_{2m'}⁺` forces `m = m'`. -/
theorem plus_plus_eq {m m' : ℕ} (h : HasCOneLabel V (.plus m)) (h' : HasCOneLabel V (.plus m')) :
    m = m' := by
  obtain ⟨hm, -, e⟩ := h
  obtain ⟨hm', -, e'⟩ := h'
  have key : ∀ a b : ℕ, ∀ (ha : 1 ≤ a) (hb : 1 ≤ b), a < b →
      VOAIsomorphic V (V2mPlus a ha) → VOAIsomorphic V (V2mPlus b hb) → False := by
    intro a b ha hb hab ea eb
    have h1 := finrank_grading_eq_of_iso ea a
    have h2 := finrank_grading_eq_of_iso eb a
    have p1 := V2mPlus_two_mul a ha a
    have p2 := V2mPlus_two_mul b hb a
    rw [V2m_finrank_self a ha] at p1
    rw [V2m_finrank_lt b hb a hab] at p2
    rw [← h1] at p1
    rw [← h2] at p2
    push_cast at p1 p2
    omega
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exact (key m m' hm hm' hlt e e').elim
  · exact heq
  · exact (key m' m hm' hm hgt e' e).elim

/-- **(c)** No VOA is both some `V_{2m}` and some `V_{2m'}⁺` (`m' ≥ 2`): `dim V₁ ≥ 1` vs `0`. -/
theorem not_lat_plus {m m' : ℕ} (h : HasCOneLabel V (.lat m)) (h' : HasCOneLabel V (.plus m')) :
    False := by
  obtain ⟨hm, e⟩ := h
  obtain ⟨hm', h2, e'⟩ := h'
  have h1 := finrank_grading_eq_of_iso e 1
  have h3 := finrank_grading_eq_of_iso e' 1
  have := V2m_finrank_one_pos m hm
  rw [V2mPlus_finrank_one m' hm' h2] at h3
  omega

end Families

/-! ## The exceptional orbifolds have `V₁ = 0` -/

section Exceptional

local notation "V1" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)

/-- A nontrivial torus element `g_u` fixes only the multiples of `h` in `(V₂)₁`. -/
theorem fixed_charU_eq_smul_h {u : ℂˣ} (hu : u ≠ 1) {x : LatModuleGen (latP 1)}
    (hx : x ∈ (V1).grading 1) (hfix : charU 1 le_rfl u x = x) :
    ∃ c : ℂ, x = c • hSt (latP 1) (a1 1) := by
  obtain ⟨x₁, x₂, x₃, rfl⟩ := V2_grading_one hx
  rw [charU_vec3] at hfix
  have h1 := vec3_coord_one hfix
  have h3 := vec3_coord_three hfix
  have hu' : (u : ℂ) ≠ 1 := fun e => hu (Units.ext e)
  have hx1 : x₁ = 0 := by
    have : ((u : ℂ) - 1) * x₁ = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hu')
  have hx3 : x₃ = 0 := by
    have hui : (u : ℂ)⁻¹ ≠ 1 := by
      intro e; apply hu'; rw [← inv_inv (u : ℂ), e, inv_one]
    have : ((u : ℂ)⁻¹ - 1) * x₃ = 0 := by linear_combination h3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hui)
  subst hx1 hx3
  refine ⟨x₂, ?_⟩
  rw [hSt_eq_vec3, vec3_smul]
  simp

/-- **A finite group of automorphisms of `V₂` fixing a nonzero vector of `(V₂)₁` is abelian.**
Conjugate a nontrivial element to a torus element `g_u`; its fixed line is `ℂh`, so after
conjugation every element fixes `h`, hence is a torus element (`eq_charU_of_fix_h`). -/
theorem commute_of_fixes_weight_one (G : Subgroup (Aut V1)) [Finite G]
    {x : LatModuleGen (latP 1)} (hx : x ∈ (V1).grading 1) (hx0 : x ≠ 0)
    (hfix : ∀ g ∈ G, g x = x) : ∀ a ∈ G, ∀ b ∈ G, a * b = b * a := by
  by_cases hall : ∀ g ∈ G, g = 1
  · intro a ha b hb; rw [hall a ha, hall b hb]
  push Not at hall
  obtain ⟨g₀, hg₀, hg₀1⟩ := hall
  have hfin : IsOfFinOrder g₀ :=
    G.subtype.isOfFinOrder (isOfFinOrder_of_finite (⟨g₀, hg₀⟩ : G))
  obtain ⟨φ, u, hφ⟩ := exists_conj_charU g₀ hfin
  have hu : u ≠ 1 := by
    rintro rfl
    rw [map_one, mul_inv_eq_one, mul_eq_left] at hφ
    exact hg₀1 hφ
  have hconj : ∀ g ∈ G, (φ * g * φ⁻¹) (φ x) = φ x := by
    intro g hg
    rw [Aut.mul_apply, Aut.mul_apply, Aut.inv_apply, LinearEquiv.symm_apply_apply,
      ← Aut.coe_toLinearEquiv, ← Aut.coe_toLinearEquiv, hfix g hg]
  have hy : φ x ∈ (V1).grading 1 := Aut.map_grading φ hx
  obtain ⟨c, hc⟩ := fixed_charU_eq_smul_h hu hy (by rw [← hφ]; exact hconj g₀ hg₀)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    apply hx0
    have : φ.toLinearEquiv x = φ.toLinearEquiv 0 := by rw [map_zero]; exact hc
    exact φ.toLinearEquiv.injective this
  have htorus : ∀ g ∈ G, ∃ w : ℂˣ, φ * g * φ⁻¹ = charU 1 le_rfl w := by
    intro g hg
    apply eq_charU_of_fix_h
    have h1 := hconj g hg
    rw [hc, Aut.map_smul_c] at h1
    exact smul_right_injective _ hc0 h1
  intro a ha b hb
  obtain ⟨wa, hwa⟩ := htorus a ha
  obtain ⟨wb, hwb⟩ := htorus b hb
  have key : φ * (a * b) * φ⁻¹ = φ * (b * a) * φ⁻¹ := by
    have e1 : φ * (a * b) * φ⁻¹ = (φ * a * φ⁻¹) * (φ * b * φ⁻¹) := by group
    have e2 : φ * (b * a) * φ⁻¹ = (φ * b * φ⁻¹) * (φ * a * φ⁻¹) := by group
    rw [e1, e2, hwa, hwb, ← map_mul, ← map_mul, mul_comm]
  simpa using key

/-- **The orbifold of `V₂` by a finite non-abelian group has no weight-one states.** -/
theorem orbifold_V2_finrank_one (G : Subgroup (Aut V1)) [Finite G]
    (hnc : ∃ a ∈ G, ∃ b ∈ G, a * b ≠ b * a) :
    finrank ℂ ((orbifoldVOA G).grading 1) = 0 := by
  have hbot : (orbifoldVOA G).grading 1 = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Submodule.mem_bot]
    by_contra hz0
    have hz' : (z : LatModuleGen (latP 1)) ∈ (V1).grading 1 := hz
    have hz0' : (z : LatModuleGen (latP 1)) ≠ 0 := fun e => hz0 (Subtype.ext e)
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    exact hab (commute_of_fixes_weight_one G hz' hz0' (fun g hg => z.2 g hg) a ha b hb)
  rw [hbot, finrank_bot]

end Exceptional

section ExceptionalLabels

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}

/-- If `V ≅ V₂^G` with `G ≅ H` finite and non-abelian, then `dim V₁ = 0`. -/
theorem finrank_one_of_isV2Orbifold {H : Type} [Group H] [Finite H]
    (hH : ∃ a b : H, a * b ≠ b * a) (h : IsV2Orbifold V H) :
    finrank ℂ (V.grading 1) = 0 := by
  obtain ⟨G, ⟨e⟩, hV⟩ := h
  have hfin : Finite G := Finite.of_equiv H e.symm.toEquiv
  rw [finrank_grading_eq_of_iso hV 1]
  obtain ⟨a, b, hab⟩ := hH
  refine @orbifold_V2_finrank_one G hfin
    ⟨((e.symm a : G) : Aut (V2m 1 le_rfl)), (e.symm a).2, ((e.symm b : G) : Aut (V2m 1 le_rfl)),
      (e.symm b).2, ?_⟩
  intro hc
  apply hab
  apply e.symm.injective
  rw [map_mul, map_mul]
  exact Subtype.ext hc

theorem alternating4_noncomm : ∃ a b : alternatingGroup (Fin 4), a * b ≠ b * a :=
  ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
   ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩, by decide⟩

theorem perm4_noncomm : ∃ a b : Equiv.Perm (Fin 4), a * b ≠ b * a :=
  ⟨Equiv.swap 0 1, Equiv.swap 1 2, by decide⟩

theorem alternating5_noncomm : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a :=
  ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
   ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩, by decide⟩

/-- The exceptional labels. -/
def COneLabel.IsExceptional : COneLabel → Prop
  | .tetra => True
  | .octa => True
  | .icosa => True
  | _ => False

/-- **`V₂^{A₄}`, `V₂^{S₄}`, `V₂^{A₅}` have `dim V₁ = 0`.** -/
theorem finrank_one_of_exceptional {l : COneLabel} (hl : l.IsExceptional)
    (h : HasCOneLabel V l) : finrank ℂ (V.grading 1) = 0 := by
  cases l with
  | tetra => exact finrank_one_of_isV2Orbifold alternating4_noncomm h
  | octa => exact finrank_one_of_isV2Orbifold perm4_noncomm h
  | icosa => exact finrank_one_of_isV2Orbifold alternating5_noncomm h
  | lat _ => exact hl.elim
  | plus _ => exact hl.elim

/-- **(d, lattice half)** No `V_{2m}` is isomorphic to an exceptional orbifold. -/
theorem not_lat_exceptional {m : ℕ} {l : COneLabel} (hl : l.IsExceptional)
    (h : HasCOneLabel V (.lat m)) (h' : HasCOneLabel V l) : False := by
  obtain ⟨hm, e⟩ := h
  have h1 := finrank_grading_eq_of_iso e 1
  have := V2m_finrank_one_pos m hm
  rw [finrank_one_of_exceptional hl h'] at h1
  omega

end ExceptionalLabels

/-! ## Weights two and three of the exceptional orbifolds -/

section Virasoro

universe w

variable {𝒰 : Type w} [AddCommGroup 𝒰] [Module ℂ 𝒰] (W : VertexOperatorAlgebra 𝒰)

/-- The Virasoro relation applied to a vector, for `a + b ≠ 0`. -/
theorem L_comm_apply {a b : ℤ} (hab : a + b ≠ 0) (x : 𝒰) :
    W.L a (W.L b x) = W.L b (W.L a x) + ((a : ℂ) - b) • W.L (a + b) x := by
  have h := LinearMap.congr_fun (W.L_virasoro a b) x
  rw [if_neg hab, add_zero] at h
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply] at h
  rw [← h]; abel

/-- The Virasoro relation applied to a vector, for `b = -a`. -/
theorem L_comm_apply_neg (a : ℤ) (x : 𝒰) :
    W.L a (W.L (-a) x) = W.L (-a) (W.L a x) + ((a : ℂ) - (-a : ℤ)) • W.L 0 x
      + (((a : ℂ) ^ 3 - a) / 12 * W.centralCharge) • x := by
  have h := LinearMap.congr_fun (W.L_virasoro a (-a)) x
  rw [if_pos (by ring), show a + -a = 0 by ring] at h
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply] at h
  rw [add_assoc, ← h]; abel

theorem L_mem_grading' {ℓ : ℤ} {x : 𝒰} (hx : x ∈ W.grading ℓ) (n : ℤ) :
    W.L n x ∈ W.grading (ℓ - n) := by
  have h := W.grading_mode W.conformalVector W.conformal_mem x hx (n + 1)
  rw [show (2 : ℤ) + ℓ - (n + 1) - 1 = ℓ - n by ring] at h
  exact h

theorem eq_zero_of_mem_grading_neg {n : ℤ} (hn : n < 0) {x : 𝒰} (hx : x ∈ W.grading n) : x = 0 := by
  rw [W.positivity n hn] at hx; exact (Submodule.mem_bot ℂ).mp hx

end Virasoro

section V2Low

local notation "V1" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)

variable {y : LatModuleGen (latP 1)} (hy : y ∈ (V1).grading 1)

include hy

theorem V2_L1_y : (V1).L 1 y = 0 :=
  (V2m_stronglyRational 1 le_rfl).L_one_grading_one_eq_zero hy

theorem V2_L2_y : (V1).L 2 y = 0 :=
  eq_zero_of_mem_grading_neg _ (n := -1) (by norm_num) (by simpa using L_mem_grading' (V1) hy 2)

theorem V2_L0_y : (V1).L 0 y = y := by
  rw [(V1).L_zero_grading y hy]; simp

theorem V2_Lm1_mem : (V1).L (-1) y ∈ (V1).grading 2 := by
  simpa using L_mem_grading' (V1) hy (-1)

theorem V2_Lm1m1_mem : (V1).L (-1) ((V1).L (-1) y) ∈ (V1).grading 3 := by
  simpa using L_mem_grading' (V1) (V2_Lm1_mem hy) (-1)

theorem V2_Lm2_mem : (V1).L (-2) y ∈ (V1).grading 3 := by
  simpa using L_mem_grading' (V1) hy (-2)

/-- `L₁ L₋₁ y = 2y`. -/
theorem V2_L1_Lm1 : (V1).L 1 ((V1).L (-1) y) = (2 : ℂ) • y := by
  have h := L_comm_apply_neg (V1) 1 y
  rw [V2_L1_y hy, map_zero, zero_add, V2_L0_y hy] at h
  rw [h]; norm_num

/-- `L₁ L₋₁² y = 6 L₋₁ y`. -/
theorem V2_L1_Lm1m1 : (V1).L 1 ((V1).L (-1) ((V1).L (-1) y)) = (6 : ℂ) • (V1).L (-1) y := by
  have h := L_comm_apply_neg (V1) 1 ((V1).L (-1) y)
  rw [V2_L1_Lm1 hy, map_smul, (V1).L_zero_grading _ (V2_Lm1_mem hy)] at h
  rw [h]; simp only [smul_smul]; norm_num; module

/-- `L₂ L₋₁² y = 6 y`. -/
theorem V2_L2_Lm1m1 : (V1).L 2 ((V1).L (-1) ((V1).L (-1) y)) = (6 : ℂ) • y := by
  have h0 : (V1).L 2 ((V1).L (-1) y) = 0 := by
    rw [L_comm_apply (V1) (a := 2) (b := -1) (by norm_num), show (2 : ℤ) + -1 = 1 by norm_num,
      V2_L2_y hy, V2_L1_y hy]; simp
  rw [L_comm_apply (V1) (a := 2) (b := -1) (by norm_num), show (2 : ℤ) + -1 = 1 by norm_num, h0,
    V2_L1_Lm1 hy]
  norm_num; module

/-- `L₁ L₋₂ y = 3 L₋₁ y`. -/
theorem V2_L1_Lm2 : (V1).L 1 ((V1).L (-2) y) = (3 : ℂ) • (V1).L (-1) y := by
  rw [L_comm_apply (V1) (a := 1) (b := -2) (by norm_num), show (1 : ℤ) + -2 = -1 by norm_num,
    V2_L1_y hy]; norm_num

/-- `L₂ L₋₂ y = (9/2) y` (central charge `1`). -/
theorem V2_L2_Lm2 : (V1).L 2 ((V1).L (-2) y) = (9 / 2 : ℂ) • y := by
  have h := L_comm_apply_neg (V1) 2 y
  rw [V2_L2_y hy, map_zero, zero_add, V2_L0_y hy] at h
  have hc : (V1).centralCharge = 1 := V2m_centralCharge 1 le_rfl
  rw [hc] at h
  rw [h]; norm_num; module

end V2Low

section V2Bounds

local notation "V1" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)

theorem V2_finrank_one : finrank ℂ ((V1).grading 1) = 3 := by
  have := V2m_finrank_self 1 le_rfl
  rw [fockCount_one_one] at this
  exact_mod_cast this

theorem V2_finrank_two : finrank ℂ ((V1).grading 2) = 4 := by
  have := V2m_finrank_mid 1 le_rfl 2 (by norm_num) (by norm_num)
  rw [fockCount_two, fockCount_one_one] at this
  exact_mod_cast this

theorem V2_finrank_three : finrank ℂ ((V1).grading 3) = 7 := by
  have := V2m_finrank_mid 1 le_rfl 3 (by norm_num) (by norm_num)
  rw [fockCount_three, fockCount_two] at this
  exact_mod_cast this

variable (G : Subgroup (Aut V1)) [Finite G] (hnc : ∃ a ∈ G, ∃ b ∈ G, a * b ≠ b * a)

include hnc in
theorem fixed_weight_one_eq_zero {y : LatModuleGen (latP 1)} (hy : y ∈ (V1).grading 1)
    (hfix : ∀ g ∈ G, g y = y) : y = 0 := by
  by_contra hy0
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  exact hab (commute_of_fixes_weight_one G hy hy0 hfix a ha b hb)

omit [Finite G] in
theorem fixed_L {x : LatModuleGen (latP 1)} (hfix : ∀ g ∈ G, g x = x) (n : ℤ) :
    ∀ g ∈ G, g ((V1).L n x) = (V1).L n x := by
  intro g hg
  rw [VertexOperatorAlgebra.aut_comm_L, hfix g hg]

include hnc in
/-- **`dim (V₂^G)₂ ≤ 1`** for a finite non-abelian `G`: a fixed weight-two vector is killed
by `L₁` (its image is a fixed weight-one vector), and `L₁ : (V₂)₂ → (V₂)₁` is onto
(`L₁ L₋₁ y = 2y`), so its kernel is `4 − 3 = 1`-dimensional. -/
theorem orbifold_V2_finrank_two_le : finrank ℂ ((orbifoldVOA G).grading 2) ≤ 1 := by
  haveI := (V1).finrank 2
  haveI := (V1).finrank 1
  let f : (V1).grading 2 →ₗ[ℂ] (V1).grading 1 :=
    ((V1).L 1).restrict (p := (V1).grading 2) (q := (V1).grading 1)
      (fun x hx => by simpa using L_mem_grading' (V1) hx 1)
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨⟨(1 / 2 : ℂ) • (V1).L (-1) y, Submodule.smul_mem _ _ (V2_Lm1_mem y.2)⟩, ?_⟩
    apply Subtype.ext
    change (V1).L 1 ((1 / 2 : ℂ) • (V1).L (-1) y) = y
    rw [map_smul, V2_L1_Lm1 y.2, smul_smul]; norm_num
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, V2_finrank_one, V2_finrank_two] at hrk
  let ι : (orbifoldVOA G).grading 2 →ₗ[ℂ] LinearMap.ker f :=
    { toFun := fun z => ⟨⟨z.1.1, z.2⟩, by
        rw [LinearMap.mem_ker]
        apply Subtype.ext
        change (V1).L 1 z.1.1 = 0
        exact fixed_weight_one_eq_zero G hnc (by simpa using L_mem_grading' (V1) z.2 1)
          (fixed_L G (fun g hg => z.1.2 g hg) 1)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ι := by
    intro z z' h
    have := congrArg (fun w : LinearMap.ker f => ((w : (V1).grading 2) : LatModuleGen (latP 1))) h
    exact Subtype.ext (Subtype.ext this)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  omega

include hnc in
/-- **`dim (V₂^G)₃ ≤ 1`** for a finite non-abelian `G`. A fixed weight-three vector `x` has
`L₂x` and `L₁²x` fixed of weight one, hence zero; and `x ↦ (L₁²x, L₂x)` maps `(V₂)₃` onto
`(V₂)₁ × (V₂)₁` (on `L₋₁²y + L₋₂z` it is `(12y + 6z, 6y + 9z/2)`, determinant `18`), so its
kernel is `7 − 6 = 1`-dimensional. -/
theorem orbifold_V2_finrank_three_le : finrank ℂ ((orbifoldVOA G).grading 3) ≤ 1 := by
  haveI := (V1).finrank 3
  haveI := (V1).finrank 1
  let f₁ : (V1).grading 3 →ₗ[ℂ] (V1).grading 1 :=
    ((V1).L 1 * (V1).L 1).restrict (p := (V1).grading 3) (q := (V1).grading 1)
      (fun x hx => by
        have h1 := L_mem_grading' (V1) hx 1
        simpa using L_mem_grading' (V1) h1 1)
  let f₂ : (V1).grading 3 →ₗ[ℂ] (V1).grading 1 :=
    ((V1).L 2).restrict (p := (V1).grading 3) (q := (V1).grading 1)
      (fun x hx => by simpa using L_mem_grading' (V1) hx 2)
  let F := f₁.prod f₂
  have hsurj : Function.Surjective F := by
    rintro ⟨a, b⟩
    set y : LatModuleGen (latP 1) := (1 / 4 : ℂ) • (a : LatModuleGen (latP 1)) - (1 / 3 : ℂ) • (b : LatModuleGen (latP 1))
    set z : LatModuleGen (latP 1) := (2 / 3 : ℂ) • (b : LatModuleGen (latP 1)) - (1 / 3 : ℂ) • (a : LatModuleGen (latP 1))
    have hy : y ∈ (V1).grading 1 :=
      Submodule.sub_mem _ (Submodule.smul_mem _ _ a.2) (Submodule.smul_mem _ _ b.2)
    have hz : z ∈ (V1).grading 1 :=
      Submodule.sub_mem _ (Submodule.smul_mem _ _ b.2) (Submodule.smul_mem _ _ a.2)
    refine ⟨⟨(V1).L (-1) ((V1).L (-1) y) + (V1).L (-2) z,
      Submodule.add_mem _ (V2_Lm1m1_mem hy) (V2_Lm2_mem hz)⟩, ?_⟩
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change (V1).L 1 ((V1).L 1 ((V1).L (-1) ((V1).L (-1) y) + (V1).L (-2) z)) = a
      rw [map_add, V2_L1_Lm1m1 hy, V2_L1_Lm2 hz, map_add, map_smul, map_smul, V2_L1_Lm1 hy,
        V2_L1_Lm1 hz]
      simp only [y, z, smul_smul, smul_sub]
      module
    · change (V1).L 2 ((V1).L (-1) ((V1).L (-1) y) + (V1).L (-2) z) = b
      rw [map_add, V2_L2_Lm1m1 hy, V2_L2_Lm2 hz]
      simp only [y, z, smul_smul, smul_sub]
      module
  have hrk := LinearMap.finrank_range_add_finrank_ker F
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_prod, V2_finrank_one,
    V2_finrank_three] at hrk
  let ι : (orbifoldVOA G).grading 3 →ₗ[ℂ] LinearMap.ker F :=
    { toFun := fun z => ⟨⟨z.1.1, z.2⟩, by
        have hfix : ∀ g ∈ G, g z.1.1 = z.1.1 := fun g hg => z.1.2 g hg
        have h1 : (V1).L 1 z.1.1 ∈ (V1).grading 2 := by simpa using L_mem_grading' (V1) z.2 1
        have e1 : (V1).L 1 ((V1).L 1 z.1.1) = 0 :=
          fixed_weight_one_eq_zero G hnc (by simpa using L_mem_grading' (V1) h1 1)
            (fixed_L G (fixed_L G hfix 1) 1)
        have e2 : (V1).L 2 z.1.1 = 0 :=
          fixed_weight_one_eq_zero G hnc (by simpa using L_mem_grading' (V1) z.2 2)
            (fixed_L G hfix 2)
        rw [LinearMap.mem_ker]
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · exact e1
        · exact e2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ι := by
    intro z z' h
    have := congrArg (fun w : LinearMap.ker F => ((w : (V1).grading 3) : LatModuleGen (latP 1))) h
    exact Subtype.ext (Subtype.ext this)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  omega

end V2Bounds

/-! ## `V₄⁺` and `V₆⁺` versus the exceptional orbifolds -/

section PlusSmall

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}

theorem fockSigned_one_two : fockSigned 1 2 = 0 := by
  rw [fockSigned_eq, fockCountEven_two, fockCountOdd_two]; decide

theorem fockSigned_one_three : fockSigned 1 3 = -1 := by
  rw [fockSigned_eq, fockCountEven_three, fockCountOdd_three]; decide

/-- `dim (V₄⁺)₂ = 2`. -/
theorem V4Plus_finrank_two (hm : 1 ≤ 2) : finrank ℂ ((V2mPlus 2 hm).grading 2) = 2 := by
  have h := V2mPlus_two_mul 2 hm 2
  rw [V2m_finrank_self 2 hm, fockSigned_one_two, fockCount_two] at h
  rw [show Nat.choose 2 2 = 1 by decide] at h
  push_cast at h
  omega

/-- `dim (V₆⁺)₃ = 2`. -/
theorem V6Plus_finrank_three (hm : 1 ≤ 3) : finrank ℂ ((V2mPlus 3 hm).grading 3) = 2 := by
  have h := V2mPlus_two_mul 3 hm 3
  rw [V2m_finrank_self 3 hm, fockSigned_one_three, fockCount_three] at h
  rw [show Nat.choose 3 3 = 1 by decide] at h
  push_cast at h
  omega

/-- An exceptional label realizes `V` as `V₂^G` with `G` finite and non-abelian. -/
theorem exists_orbifold_of_exceptional {l : COneLabel} (hl : l.IsExceptional)
    (h : HasCOneLabel V l) :
    ∃ (G : Subgroup (Aut (V2m 1 le_rfl))) (_ : Finite G),
      (∃ a ∈ G, ∃ b ∈ G, a * b ≠ b * a) ∧ VOAIsomorphic V (orbifoldVOA G) := by
  have key : ∀ {H : Type} [Group H] [Finite H], (∃ a b : H, a * b ≠ b * a) →
      IsV2Orbifold V H → ∃ (G : Subgroup (Aut (V2m 1 le_rfl))) (_ : Finite G),
        (∃ a ∈ G, ∃ b ∈ G, a * b ≠ b * a) ∧ VOAIsomorphic V (orbifoldVOA G) := by
    intro H _ _ hH hV
    obtain ⟨G, ⟨e⟩, hV⟩ := hV
    obtain ⟨a, b, hab⟩ := hH
    refine ⟨G, Finite.of_equiv H e.symm.toEquiv,
      ⟨((e.symm a : G) : Aut (V2m 1 le_rfl)), (e.symm a).2, ((e.symm b : G) : Aut (V2m 1 le_rfl)),
        (e.symm b).2, ?_⟩, hV⟩
    intro hc
    apply hab
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact Subtype.ext hc
  cases l with
  | tetra => exact key alternating4_noncomm h
  | octa => exact key perm4_noncomm h
  | icosa => exact key alternating5_noncomm h
  | lat _ => exact hl.elim
  | plus _ => exact hl.elim

/-- The exceptional orbifolds have `dim V₂ ≤ 1` and `dim V₃ ≤ 1`. -/
theorem finrank_two_three_of_exceptional {l : COneLabel} (hl : l.IsExceptional)
    (h : HasCOneLabel V l) :
    finrank ℂ (V.grading 2) ≤ 1 ∧ finrank ℂ (V.grading 3) ≤ 1 := by
  obtain ⟨G, hG, hnc, hV⟩ := exists_orbifold_of_exceptional hl h
  rw [finrank_grading_eq_of_iso hV 2, finrank_grading_eq_of_iso hV 3]
  exact ⟨@orbifold_V2_finrank_two_le G hG hnc, @orbifold_V2_finrank_three_le G hG hnc⟩

/-- **(d, small plus half)** `V₄⁺` and `V₆⁺` are not exceptional orbifolds. -/
theorem not_plus_exceptional_small {m : ℕ} (hm23 : m = 2 ∨ m = 3) {l : COneLabel}
    (hl : l.IsExceptional) (h : HasCOneLabel V (.plus m)) (h' : HasCOneLabel V l) : False := by
  obtain ⟨hm, -, e⟩ := h
  obtain ⟨h2, h3⟩ := finrank_two_three_of_exceptional hl h'
  rcases hm23 with rfl | rfl
  · rw [finrank_grading_eq_of_iso e 2, V4Plus_finrank_two] at h2; omega
  · rw [finrank_grading_eq_of_iso e 3, V6Plus_finrank_three] at h3; omega

end PlusSmall

/-! ## Assembly: distinctness up to two named residuals -/

section Assembly

universe u

/-- **Residual 1** (true by GR Thm. 3.1; not proved here): no `V_{2m}⁺` with `m ≥ 4` is an
exceptional orbifold. Expected proof: `dim (V_{2m}⁺)₄ ≥ 3` (from `V2mPlus_two_mul`) against
`dim (V₂^G)₄ = 2`, which needs the `G`-invariants of the five-dimensional spin-two primary space
of `(V₂)₄`. -/
def PlusExceptionalResidual : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱) (m : ℕ)
    (l : COneLabel), 4 ≤ m → l.IsExceptional → HasCOneLabel V (.plus m) → HasCOneLabel V l → False

/-- **Residual 2** (true by GR Thm. 3.1; not proved here): `V₂^{A₄}`, `V₂^{S₄}`, `V₂^{A₅}` are
pairwise non-isomorphic. Their graded dimensions first differ at weight `9` (spin-3 invariant of
`A₄`) and `16` (spin-4 invariant of `S₄`). -/
def ExceptionalResidual : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱) (l l' : COneLabel),
    l.IsExceptional → l'.IsExceptional → HasCOneLabel V l → HasCOneLabel V l' → l = l'

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}

theorem not_plus_exceptional (hR : PlusExceptionalResidual.{u}) {m : ℕ} {l : COneLabel}
    (hl : l.IsExceptional) (h : HasCOneLabel V (.plus m)) (h' : HasCOneLabel V l) : False := by
  have h2 : 2 ≤ m := h.2.1
  by_cases h4 : 4 ≤ m
  · exact hR 𝒱 V m l h4 hl h h'
  · exact not_plus_exceptional_small (by omega) hl h h'

/-- **Gannon–Rayhaun "pairwise non-isomorphic", conditional on the two residuals.**
Every pair is separated here except `plus m` (`m ≥ 4`) against the exceptional orbifolds, and the
exceptional orbifolds among themselves. -/
theorem gannonRayhaunDistinct_of_residuals (hR1 : PlusExceptionalResidual.{u})
    (hR2 : ExceptionalResidual.{u}) : GannonRayhaunDistinct.{u} := by
  intro 𝒱 _ _ V l l' h h'
  cases l with
  | lat m =>
    cases l' with
    | lat m' => rw [lat_lat_eq h h']
    | plus m' => exact (not_lat_plus h h').elim
    | tetra => exact (not_lat_exceptional (by trivial) h h').elim
    | octa => exact (not_lat_exceptional (by trivial) h h').elim
    | icosa => exact (not_lat_exceptional (by trivial) h h').elim
  | plus m =>
    cases l' with
    | lat m' => exact (not_lat_plus h' h).elim
    | plus m' => rw [plus_plus_eq h h']
    | tetra => exact (not_plus_exceptional hR1 (by trivial) h h').elim
    | octa => exact (not_plus_exceptional hR1 (by trivial) h h').elim
    | icosa => exact (not_plus_exceptional hR1 (by trivial) h h').elim
  | tetra =>
    cases l' with
    | lat m' => exact (not_lat_exceptional (by trivial) h' h).elim
    | plus m' => exact (not_plus_exceptional hR1 (by trivial) h' h).elim
    | _ => exact hR2 𝒱 V _ _ (by trivial) (by trivial) h h'
  | octa =>
    cases l' with
    | lat m' => exact (not_lat_exceptional (by trivial) h' h).elim
    | plus m' => exact (not_plus_exceptional hR1 (by trivial) h' h).elim
    | _ => exact hR2 𝒱 V _ _ (by trivial) (by trivial) h h'
  | icosa =>
    cases l' with
    | lat m' => exact (not_lat_exceptional (by trivial) h' h).elim
    | plus m' => exact (not_plus_exceptional hR1 (by trivial) h' h).elim
    | _ => exact hR2 𝒱 V _ _ (by trivial) (by trivial) h h'

end Assembly

end VOA.Classification.COne
