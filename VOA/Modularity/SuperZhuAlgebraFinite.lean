/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GammaThetaStatement
import VOA.Modules.SuperZhuResidue

/-!
# `C₂`-cofinite integral-weight super VOAs have finite-dimensional Zhu algebra

This is the super analogue of `Modularity.ZhuAlgebraFinite`.  The argument is sign-free: the
only Zhu relation used is the residue of one homogeneous state, so no two odd states are
exchanged.  Associativity of the quotient is likewise irrelevant to its finite-dimensionality;
`SuperZhuRingData` is needed to make the quotient a ring, but not for the vector-space theorem.

The hypotheses are exactly those available for an integral-weight
`SuperVertexOperatorAlgebra`: integrality supplies a `ℤ`-grading, and the SVOA positivity axiom
kills negative grades.  No rationality or semisimplicity is assumed.
-/

namespace VOA

open scoped BigOperators
open DirectSum
open GammaThetaStmt

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace SuperNearVOA

/-- A vector is homogeneous for the integral conformal-weight grading. -/
def IsHomogZ (V : SuperNearVOA 𝒱) (x : 𝒱) : Prop :=
  ∃ n : ℤ, x ∈ V.gradingZ n

/-- Integral homogeneous vectors span the whole space. -/
theorem span_isHomogZ_eq_top (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) :
    Submodule.span ℂ {x | V.IsHomogZ x} = ⊤ := by
  rw [eq_top_iff, ← (V.gradingZ_isInternal hV).submodule_iSup_eq_top, Submodule.iSup_eq_span]
  apply Submodule.span_mono
  intro x hx
  simp only [Set.mem_iUnion, SetLike.mem_coe] at hx
  obtain ⟨n, hn⟩ := hx
  exact ⟨n, hn⟩

/-! ## The super `C₂` space is graded -/

/-- Homogeneous generators of the super `C₂` space. -/
def superO₂HomGen (V : SuperNearVOA 𝒱) : Set 𝒱 :=
  {x | ∃ (p q : ℤ) (a b : 𝒱),
    a ∈ V.gradingZ p ∧ b ∈ V.gradingZ q ∧ x = V.smul a (-2) b}

theorem superO₂_genHom_left_mem_span (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights)
    {p : ℤ} {a : 𝒱} (ha : a ∈ V.gradingZ p) (b : 𝒱) :
    V.smul a (-2) b ∈ Submodule.span ℂ (V.superO₂HomGen) := by
  have hb : b ∈ Submodule.span ℂ {x | V.IsHomogZ x} := by
    rw [V.span_isHomogZ_eq_top hV]
    trivial
  refine Submodule.span_induction
    (p := fun b _ => V.smul a (-2) b ∈ Submodule.span ℂ V.superO₂HomGen) ?_ ?_ ?_ ?_ hb
  · rintro y ⟨q, hq⟩
    exact Submodule.subset_span ⟨p, q, a, y, ha, hq, rfl⟩
  · simp
  · intro y z _ _ hy hz
    rw [SuperVertexAlgebra.smul_add_right]
    exact (Submodule.span ℂ V.superO₂HomGen).add_mem hy hz
  · intro c y _ hy
    rw [SuperVertexAlgebra.smul_smul_right]
    exact (Submodule.span ℂ V.superO₂HomGen).smul_mem c hy

theorem superO₂_gen_mem_span (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (a b : 𝒱) :
    V.smul a (-2) b ∈ Submodule.span ℂ V.superO₂HomGen := by
  have ha : a ∈ Submodule.span ℂ {x | V.IsHomogZ x} := by
    rw [V.span_isHomogZ_eq_top hV]
    trivial
  refine Submodule.span_induction
    (p := fun a _ => V.smul a (-2) b ∈ Submodule.span ℂ V.superO₂HomGen) ?_ ?_ ?_ ?_ ha
  · rintro y ⟨p, hp⟩
    exact V.superO₂_genHom_left_mem_span hV hp b
  · simp
  · intro y z _ _ hy hz
    rw [SuperVertexAlgebra.smul_add_left]
    exact (Submodule.span ℂ V.superO₂HomGen).add_mem hy hz
  · intro c y _ hy
    rw [SuperVertexAlgebra.smul_smul_left]
    exact (Submodule.span ℂ V.superO₂HomGen).smul_mem c hy

/-- The mode span defining `C₂` equals the span of its homogeneous generators. -/
theorem superO₂_eq_span_homGen (W : SuperVertexOperatorAlgebra 𝒱)
    (hV : W.toSuperNearVOA.IntegralWeights) :
    superO₂ W = Submodule.span ℂ W.toSuperNearVOA.superO₂HomGen := by
  let V := W.toSuperNearVOA
  apply le_antisymm
  · rw [superO₂, Submodule.span_le]
    rintro x ⟨a, b, rfl⟩
    exact V.superO₂_gen_mem_span hV a b
  · rw [Submodule.span_le]
    rintro x ⟨p, q, a, b, ha, hb, rfl⟩
    exact Submodule.subset_span ⟨a, b, rfl⟩

/-- A homogeneous `C₂` generator has degree `p+q+1`. -/
theorem superO₂HomGen_mem_gradingZ (V : SuperNearVOA 𝒱) {p q : ℤ} {a b : 𝒱}
    (ha : a ∈ V.gradingZ p) (hb : b ∈ V.gradingZ q) :
    V.smul a (-2) b ∈ V.gradingZ (p + q + 1) := by
  have h := V.smul_mem_gradingZ ha hb (-2)
  rwa [show p + q - (-2) - 1 = p + q + 1 from by ring] at h

/-! ## Homogeneous projections for the integral grading -/

/-- Projection onto integral conformal weight `n`. -/
noncomputable def superPiHom (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (n : ℤ) :
    𝒱 →ₗ[ℂ] 𝒱 := by
  letI := DirectSum.IsInternal.chooseDecomposition V.gradingZ (V.gradingZ_isInternal hV)
  exact (V.gradingZ n).subtype.comp
    ((DirectSum.component ℂ ℤ (fun i => (V.gradingZ i : Submodule ℂ 𝒱)) n).comp
      (DirectSum.decomposeLinearEquiv V.gradingZ).toLinearMap)

theorem superPiHom_mem (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) (n : ℤ) (x : 𝒱) :
    V.superPiHom hV n x ∈ V.gradingZ n := by
  letI := DirectSum.IsInternal.chooseDecomposition V.gradingZ (V.gradingZ_isInternal hV)
  change ((DirectSum.decompose V.gradingZ x) n : 𝒱) ∈ V.gradingZ n
  exact ((DirectSum.decompose V.gradingZ x) n).2

theorem superPiHom_of_mem (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights)
    {n : ℤ} {x : 𝒱} (hx : x ∈ V.gradingZ n) : V.superPiHom hV n x = x := by
  letI := DirectSum.IsInternal.chooseDecomposition V.gradingZ (V.gradingZ_isInternal hV)
  change ((DirectSum.decompose V.gradingZ x) n : 𝒱) = x
  have hdec : DirectSum.decompose V.gradingZ x
      = DirectSum.of (fun i => (V.gradingZ i : Submodule ℂ 𝒱)) n ⟨x, hx⟩ :=
    DirectSum.decompose_coe (ℳ := fun i => (V.gradingZ i : Submodule ℂ 𝒱))
      (⟨x, hx⟩ : V.gradingZ n)
  rw [hdec]
  simp

theorem superPiHom_of_mem_ne (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights)
    {n k : ℤ} (hnk : k ≠ n) {x : 𝒱} (hx : x ∈ V.gradingZ k) :
    V.superPiHom hV n x = 0 := by
  letI := DirectSum.IsInternal.chooseDecomposition V.gradingZ (V.gradingZ_isInternal hV)
  change ((DirectSum.decompose V.gradingZ x) n : 𝒱) = 0
  have hdec : DirectSum.decompose V.gradingZ x
      = DirectSum.of (fun i => (V.gradingZ i : Submodule ℂ 𝒱)) k ⟨x, hx⟩ :=
    DirectSum.decompose_coe (ℳ := fun i => (V.gradingZ i : Submodule ℂ 𝒱))
      (⟨x, hx⟩ : V.gradingZ k)
  rw [hdec]
  simp only [DirectSum.of_eq_of_ne (β := fun i => (V.gradingZ i : Submodule ℂ 𝒱))
    k n (⟨x, hx⟩ : V.gradingZ k) hnk.symm, ZeroMemClass.coe_zero]

theorem superPiHom_maps_span_homog (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights)
    (n : ℤ) (G : Set 𝒱) (hG : ∀ g ∈ G, V.IsHomogZ g) {x : 𝒱}
    (hx : x ∈ Submodule.span ℂ G) : V.superPiHom hV n x ∈ Submodule.span ℂ G := by
  refine Submodule.span_induction
    (p := fun x _ => V.superPiHom hV n x ∈ Submodule.span ℂ G) ?_ ?_ ?_ ?_ hx
  · intro g hg
    obtain ⟨k, hk⟩ := hG g hg
    by_cases hkn : k = n
    · subst hkn
      rw [V.superPiHom_of_mem hV hk]
      exact Submodule.subset_span hg
    · rw [V.superPiHom_of_mem_ne hV hkn hk]
      exact (Submodule.span ℂ G).zero_mem
  · simp
  · intro y z _ _ hy hz
    rw [map_add]
    exact (Submodule.span ℂ G).add_mem hy hz
  · intro c y _ hy
    rw [map_smul]
    exact (Submodule.span ℂ G).smul_mem c hy

theorem superPiHom_maps_superO₂ (W : SuperVertexOperatorAlgebra 𝒱)
    (hV : W.toSuperNearVOA.IntegralWeights) (n : ℤ) {x : 𝒱} (hx : x ∈ superO₂ W) :
    W.toSuperNearVOA.superPiHom hV n x ∈ superO₂ W := by
  let V := W.toSuperNearVOA
  rw [superO₂_eq_span_homGen W hV] at hx ⊢
  refine V.superPiHom_maps_span_homog hV n V.superO₂HomGen ?_ hx
  rintro g ⟨p, q, a, b, ha, hb, rfl⟩
  exact ⟨p + q + 1, V.superO₂HomGen_mem_gradingZ ha hb⟩

/-! ## Finite homogeneous lifts from `C₂`-cofiniteness -/

theorem exists_finset_span_sup_of_quot_finite (P : Submodule ℂ 𝒱)
    (hfin : FiniteDimensional ℂ (𝒱 ⧸ P)) :
    ∃ T : Finset 𝒱, (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (T : Set 𝒱) ⊔ P := by
  classical
  have hfin' : Module.Finite ℂ (𝒱 ⧸ P) := hfin
  obtain ⟨S, hS⟩ := Module.finite_def.mp hfin'
  have hsurj : Function.Surjective P.mkQ := Submodule.mkQ_surjective P
  have hlift : ∀ a : 𝒱 ⧸ P, P.mkQ (Function.surjInv hsurj a) = a :=
    fun a => Function.surjInv_eq hsurj a
  refine ⟨S.image (Function.surjInv hsurj), le_antisymm ?_ le_top⟩
  intro x _
  have hle : Submodule.span ℂ (S : Set (𝒱 ⧸ P)) ≤
      Submodule.map P.mkQ
        (Submodule.span ℂ ((S.image (Function.surjInv hsurj) : Finset 𝒱) : Set 𝒱)) := by
    rw [Submodule.span_le]
    intro a ha
    exact ⟨Function.surjInv hsurj a, Submodule.subset_span
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_coe.mp ha))), hlift a⟩
  have hxs : P.mkQ x ∈ Submodule.span ℂ (S : Set (𝒱 ⧸ P)) := by
    rw [hS]
    trivial
  obtain ⟨y, hyN, hyx⟩ := hle hxs
  have hker : x - y ∈ LinearMap.ker P.mkQ := by
    simp only [LinearMap.mem_ker, map_sub, hyx, sub_self]
  rw [Submodule.ker_mkQ] at hker
  have hxeq : x = y + (x - y) := by abel
  rw [hxeq]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hyN) (Submodule.mem_sup_right hker)

theorem exists_finset_homog_span_sup_superO₂ (W : SuperVertexOperatorAlgebra 𝒱)
    (hV : W.toSuperNearVOA.IntegralWeights) (hC2 : SuperC2Cofinite W) :
    ∃ T : Finset 𝒱, (∀ x ∈ (T : Set 𝒱), W.toSuperNearVOA.IsHomogZ x) ∧
      (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (T : Set 𝒱) ⊔ superO₂ W := by
  classical
  let V := W.toSuperNearVOA
  obtain ⟨T, hT⟩ := exists_finset_span_sup_of_quot_finite (superO₂ W) hC2
  have hall : ∀ y : 𝒱, ∃ F : Finset 𝒱,
      (↑F : Set 𝒱) ⊆ {x : 𝒱 | V.IsHomogZ x} ∧ y ∈ Submodule.span ℂ (F : Set 𝒱) := by
    intro y
    have hy : y ∈ Submodule.span ℂ {x : 𝒱 | V.IsHomogZ x} := by
      rw [V.span_isHomogZ_eq_top hV]
      trivial
    exact Submodule.mem_span_finite_of_mem_span hy
  choose F hFsub hFmem using hall
  let U : Finset 𝒱 := T.biUnion F
  have hUhom : ∀ x ∈ U, V.IsHomogZ x := by
    intro x hx
    rw [show U = T.biUnion F from rfl, Finset.mem_biUnion] at hx
    obtain ⟨y, _, hxy⟩ := hx
    exact hFsub y (Finset.mem_coe.mpr hxy)
  have hTU : (T : Set 𝒱) ⊆ (Submodule.span ℂ (U : Set 𝒱) : Set 𝒱) := by
    intro y hy
    refine Submodule.span_mono ?_ (hFmem y)
    intro z hz
    exact Finset.mem_coe.mpr
      (Finset.mem_biUnion.mpr ⟨y, Finset.mem_coe.mp hy, Finset.mem_coe.mp hz⟩)
  refine ⟨U, hUhom, le_antisymm ?_ le_top⟩
  rw [hT]
  exact sup_le_sup_right (Submodule.span_le.mpr hTU) _

/-! ## Exact-degree reduction of `C₂` -/

def superO₂HomGenDeg (V : SuperNearVOA 𝒱) (n : ℤ) : Set 𝒱 :=
  {x | ∃ (p q : ℤ) (a b : 𝒱), a ∈ V.gradingZ p ∧ b ∈ V.gradingZ q ∧
    p + q + 1 = n ∧ x = V.smul a (-2) b}

theorem superPiHom_homGen_mem (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights)
    (n : ℤ) {g : 𝒱} (hg : g ∈ V.superO₂HomGen) :
    V.superPiHom hV n g ∈ Submodule.span ℂ (V.superO₂HomGenDeg n) := by
  obtain ⟨p, q, a, b, ha, hb, rfl⟩ := hg
  by_cases hd : p + q + 1 = n
  · rw [V.superPiHom_of_mem hV (by rw [← hd]; exact V.superO₂HomGen_mem_gradingZ ha hb)]
    exact Submodule.subset_span ⟨p, q, a, b, ha, hb, hd, rfl⟩
  · rw [V.superPiHom_of_mem_ne hV (by omega) (V.superO₂HomGen_mem_gradingZ ha hb)]
    exact (Submodule.span ℂ (V.superO₂HomGenDeg n)).zero_mem

theorem superO₂_inf_gradingZ_le_span_deg (W : SuperVertexOperatorAlgebra 𝒱)
    (hV : W.toSuperNearVOA.IntegralWeights) (n : ℤ) :
    superO₂ W ⊓ W.toSuperNearVOA.gradingZ n ≤
      Submodule.span ℂ (W.toSuperNearVOA.superO₂HomGenDeg n) := by
  let V := W.toSuperNearVOA
  intro x hx
  obtain ⟨hxO, hxg⟩ := hx
  rw [superO₂_eq_span_homGen W hV] at hxO
  rw [← V.superPiHom_of_mem hV hxg]
  refine Submodule.span_induction
    (p := fun y _ => V.superPiHom hV n y ∈ Submodule.span ℂ (V.superO₂HomGenDeg n))
    ?_ ?_ ?_ ?_ hxO
  · intro g hg
    exact V.superPiHom_homGen_mem hV n hg
  · simp
  · intro y z _ _ hy hz
    rw [map_add]
    exact (Submodule.span ℂ (V.superO₂HomGenDeg n)).add_mem hy hz
  · intro c y _ hy
    rw [map_smul]
    exact (Submodule.span ℂ (V.superO₂HomGenDeg n)).smul_mem c hy

theorem gradingZ_le_span_sup_superO₂_inf (W : SuperVertexOperatorAlgebra 𝒱)
    (hV : W.toSuperNearVOA.IntegralWeights) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, W.toSuperNearVOA.IsHomogZ s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ superO₂ W) (n : ℤ) :
    W.toSuperNearVOA.gradingZ n ≤
      Submodule.span ℂ S ⊔ (superO₂ W ⊓ W.toSuperNearVOA.gradingZ n) := by
  let V := W.toSuperNearVOA
  intro x hx
  have hxtop : x ∈ Submodule.span ℂ S ⊔ superO₂ W := htop ▸ Submodule.mem_top
  rw [Submodule.mem_sup] at hxtop
  obtain ⟨a, ha, b, hb, rfl⟩ := hxtop
  have hpix : V.superPiHom hV n (a + b) = a + b := V.superPiHom_of_mem hV hx
  rw [map_add] at hpix
  have hpaS : V.superPiHom hV n a ∈ Submodule.span ℂ S :=
    V.superPiHom_maps_span_homog hV n S hShom ha
  have hpbO : V.superPiHom hV n b ∈ superO₂ W :=
    superPiHom_maps_superO₂ W hV n hb
  have hpbG : V.superPiHom hV n b ∈ V.gradingZ n := V.superPiHom_mem hV n b
  rw [← hpix]
  exact Submodule.add_mem_sup hpaS ⟨hpbO, hpbG⟩

/-! ## Zhu absorption and degree induction -/

theorem smul_negTwo_mem_of_lower_superO (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights)
    {p q : ℤ} {a b : 𝒱} (ha : a ∈ V.gradingZ p) (hb : b ∈ V.gradingZ q)
    (hp : 0 ≤ p) (T : Submodule ℂ 𝒱) (hO : V.superO hV ≤ T)
    (hT : ∀ m : ℤ, m < p + q + 1 → V.gradingZ m ≤ T) :
    V.smul a (-2) b ∈ T := by
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, p = (M : ℤ) := ⟨p.toNat, by omega⟩
  have hres :
      (∑ i ∈ Finset.range (M + 1),
        cbz (M : ℤ) (i : ℤ) • V.smul a ((i : ℤ) - 2) b) ∈ T :=
    hO (V.superResidue_base_mem_superO hV ha b)
  let R : 𝒱 := ∑ k ∈ Finset.range M,
      cbz (M : ℤ) (((k + 1 : ℕ) : ℤ)) • V.smul a (((k + 1 : ℕ) : ℤ) - 2) b
  have hbot : cbz (M : ℤ) (((0 : ℕ) : ℤ)) • V.smul a (((0 : ℕ) : ℤ) - 2) b
      = V.smul a (-2) b := by norm_num
  have hsolve : V.smul a (-2) b =
      (∑ i ∈ Finset.range (M + 1),
        cbz (M : ℤ) (i : ℤ) • V.smul a ((i : ℤ) - 2) b) - R := by
    rw [show R = ∑ k ∈ Finset.range M,
      cbz (M : ℤ) (((k + 1 : ℕ) : ℤ)) •
        V.smul a (((k + 1 : ℕ) : ℤ) - 2) b from rfl]
    rw [Finset.sum_range_succ']
    rw [hbot]
    abel
  rw [hsolve]
  refine Submodule.sub_mem _ hres ?_
  rw [show R = ∑ k ∈ Finset.range M,
    cbz (M : ℤ) (((k + 1 : ℕ) : ℤ)) •
      V.smul a (((k + 1 : ℕ) : ℤ) - 2) b from rfl]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have hw := V.smul_mem_gradingZ ha hb (((i + 1 : ℕ) : ℤ) - 2)
  have heq : (M : ℤ) + q - ((((i + 1 : ℕ)) : ℤ) - 2) - 1
      = (M : ℤ) + q - (i : ℤ) := by push_cast; ring
  rw [heq] at hw
  exact hT _ (by omega) hw

theorem gradingZ_le_span_sup_superO (W : SuperVertexOperatorAlgebra 𝒱)
    (hV : W.toSuperNearVOA.IntegralWeights) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, W.toSuperNearVOA.IsHomogZ s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ superO₂ W) (n : ℤ) :
    W.toSuperNearVOA.gradingZ n ≤
      Submodule.span ℂ S ⊔ W.toSuperNearVOA.superO hV := by
  let V := W.toSuperNearVOA
  let T : Submodule ℂ 𝒱 := Submodule.span ℂ S ⊔ V.superO hV
  have hO : V.superO hV ≤ T := le_sup_right
  rcases lt_or_ge n 0 with hneg | hnn
  · have hz : V.gradingZ n = ⊥ := by
      change W.grading (n : ℂ) = ⊥
      exact W.positivity _ (by rw [Complex.intCast_re]; exact_mod_cast hneg)
    rw [hz]
    exact bot_le
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = (N : ℤ) := ⟨n.toNat, by omega⟩
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
    have hlower : ∀ m : ℤ, m < (N : ℤ) → V.gradingZ m ≤ T := by
      intro m hm
      rcases lt_or_ge m 0 with hm0 | hm0
      · have hz : V.gradingZ m = ⊥ := by
          change W.grading (m : ℂ) = ⊥
          exact W.positivity _ (by rw [Complex.intCast_re]; exact_mod_cast hm0)
        rw [hz]
        exact bot_le
      · obtain ⟨M, rfl⟩ : ∃ M : ℕ, m = (M : ℤ) := ⟨m.toNat, by omega⟩
        exact ihN M (by exact_mod_cast hm) (by exact_mod_cast hm0)
    refine le_trans (gradingZ_le_span_sup_superO₂_inf W hV S hShom htop (N : ℤ)) ?_
    refine sup_le le_sup_left ?_
    refine le_trans (superO₂_inf_gradingZ_le_span_deg W hV (N : ℤ)) ?_
    rw [Submodule.span_le]
    rintro g ⟨p, q, a, b, ha, hb, hpq, rfl⟩
    by_cases hg0 : V.smul a (-2) b = 0
    · rw [hg0]
      exact Submodule.zero_mem _
    have hp0 : 0 ≤ p := by
      by_contra hc
      have hc' : p < 0 := by omega
      exact hg0 (by
        have ha0 : a = 0 := by
          have hz : V.gradingZ p = ⊥ := by
            change W.grading (p : ℂ) = ⊥
            exact W.positivity _ (by rw [Complex.intCast_re]; exact_mod_cast hc')
          rw [hz, Submodule.mem_bot] at ha
          exact ha
        rw [ha0, SuperVertexAlgebra.smul_zero_left])
    exact V.smul_negTwo_mem_of_lower_superO hV ha hb hp0 T hO
      (fun m hm => hlower m (by omega))

theorem span_sup_superO_eq_top (W : SuperVertexOperatorAlgebra 𝒱)
    (hV : W.toSuperNearVOA.IntegralWeights) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, W.toSuperNearVOA.IsHomogZ s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ superO₂ W) :
    (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ S ⊔ W.toSuperNearVOA.superO hV := by
  let V := W.toSuperNearVOA
  refine le_antisymm ?_ le_top
  rw [← (V.gradingZ_isInternal hV).submodule_iSup_eq_top]
  exact iSup_le (gradingZ_le_span_sup_superO W hV S hShom htop)

/-- An integral-weight `C₂`-cofinite super VOA has finite-dimensional Zhu algebra. -/
theorem finiteDimensional_superA_of_superC2Cofinite (W : SuperVertexOperatorAlgebra 𝒱)
    (hV : W.toSuperNearVOA.IntegralWeights) (hC2 : SuperC2Cofinite W) :
    FiniteDimensional ℂ (W.toSuperNearVOA.superA hV) := by
  obtain ⟨T, hThom, hT⟩ := exists_finset_homog_span_sup_superO₂ W hV hC2
  have hspan := span_sup_superO_eq_top W hV (T : Set 𝒱) hThom hT
  have hfin : Module.Finite ℂ (W.toSuperNearVOA.superA hV) := by
    apply Module.finite_def.mpr
    refine Submodule.fg_def.mpr
      ⟨(W.toSuperNearVOA.superO hV).mkQ '' (T : Set 𝒱),
        T.finite_toSet.image (W.toSuperNearVOA.superO hV).mkQ, ?_⟩
    rw [← Submodule.map_span, eq_top_iff]
    intro q _
    obtain ⟨x, rfl⟩ := (W.toSuperNearVOA.superO hV).mkQ_surjective q
    have hx : x ∈ Submodule.span ℂ (T : Set 𝒱) ⊔ W.toSuperNearVOA.superO hV := by
      rw [← hspan]
      trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    have hz0 : (W.toSuperNearVOA.superO hV).mkQ z = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hz
    rw [map_add, hz0, add_zero]
    exact Submodule.mem_map_of_mem hy
  exact hfin

end SuperNearVOA

end VOA
