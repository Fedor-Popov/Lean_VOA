/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.PzTensorTauHat
import VOA.Huang.PzTensorCompatProof

/-!
# From homogeneous-pair functions to honest bilinear forms; `HLZ544`

A bilinear function `G ∈ bilin P₁ P₂` of homogeneous pairs extends uniquely to an honest bilinear
form `Ĝ : P₁ × P₂ → ℂ` (`hatG`; the weight decompositions of `P₁, P₂` are internal direct
sums).  Under this extension

* `copT ha p G` becomes `ρ(a,p) Ĝ` (`hat_copT`), `tauHom hu m G` becomes `τ̂(u,m) Ĝ`
  (`hat_tauHom`);
* lower truncation of `copT` becomes `TruncAt` (`truncAt_hat`), and the `P(1)`-compatibility
  condition `CompatFn G` becomes `CompatAt` (`compatAt_hat`).

Hence the Jacobi identity for `τ̂` (`PzTensorRho.tauHat_jacobi_pt`) transfers back:

`tauAssoc_of_compatFn`: for every bilinear, lower truncated, compatible `G`, the associator
formula for `τ` holds; **`HLZ544_holds : HLZ544 P₁ P₂`** (for all `P₁, P₂`, no
irreducibility needed), `tauAssociator_holds`, `coeffWeakInput_holds`, and
`associativityInput_of_ABD : StronglyRational W → ABDWeakIsAdmissible W →
AssocCoeffIdentityZero W → AssociativityInput W`.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.PzTensorHatBridge

open VOA VOA.Huang.MatrixCoeff VOA.Huang.FusionTop VOA.Huang.AssocTarget
open VOA.Huang.LogRemovalSemisimple VOA.Huang.AssocTauStable VOA.Huang.PzTensorBilin
open VOA.Huang.PzTensorAction VOA.Huang.PzTensorSpan VOA.Huang.PzTensorCompat
open VOA.Huang.PzTensorRho VOA.Huang.PzTensorTwist VOA.Huang.LogRemovalWeak
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {P₁ P₂ : LWModule W}

/-! ## Extensionality from homogeneous vectors -/

theorem mem_iSup_weight (P : LWModule W) (y : P.carrier) : y ∈ ⨆ α, P.isMod.weight α := by
  rw [P.isMod.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top

/-- A function additive in each variable and vanishing on pairs of weight vectors vanishes. -/
theorem eq_zero_of_homog {X : Type*} [AddCommGroup X] (f : P₁.carrier → P₂.carrier → X)
    (h1 : ∀ y y' z, f (y + y') z = f y z + f y' z) (h2 : ∀ y z z', f y (z + z') = f y z + f y z')
    (h : ∀ α₁ α₂ y z, y ∈ P₁.isMod.weight α₁ → z ∈ P₂.isMod.weight α₂ → f y z = 0) :
    ∀ y z, f y z = 0 := by
  have h10 : ∀ z, f 0 z = 0 := fun z => by
    have := h1 0 0 z; rw [add_zero] at this; exact left_eq_add.mp this
  have h20 : ∀ y, f y 0 = 0 := fun y => by
    have := h2 y 0 0; rw [add_zero] at this; exact left_eq_add.mp this
  intro y z
  refine Submodule.iSup_induction P₁.isMod.weight (motive := fun y => f y z = 0)
    (mem_iSup_weight P₁ y) ?_ (h10 z) ?_
  · intro α₁ y hy
    refine Submodule.iSup_induction P₂.isMod.weight (motive := fun z => f y z = 0)
      (mem_iSup_weight P₂ z) ?_ (h20 y) ?_
    · intro α₂ z hz; exact h α₁ α₂ y z hy hz
    · intro z z' hz hz'; rw [h2, hz, hz', add_zero]
  · intro y y' hy hy'; rw [h1, hy, hy', add_zero]

theorem bil_ext_homog {β β' : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] ℂ}
    (h : ∀ α₁ α₂ y z, y ∈ P₁.isMod.weight α₁ → z ∈ P₂.isMod.weight α₂ → β y z = β' y z) :
    β = β' := by
  have := eq_zero_of_homog (fun y z => β y z - β' y z)
    (fun y y' z => by simp only [map_add, LinearMap.add_apply]; ring)
    (fun y z z' => by simp only [map_add]; ring)
    (fun α₁ α₂ y z hy hz => by dsimp only; rw [h α₁ α₂ y z hy hz, sub_self])
  ext y z
  exact sub_eq_zero.mp (this y z)

/-! ## The honest bilinear form of a bilinear function -/

section Hat

variable (G : HomPair P₁ P₂ → ℂ) (hG : IsBilin G)

/-- The weight-space block `P₁(α₁) × P₂(α₂) → ℂ` of a bilinear function. -/
noncomputable def blockL (α₁ α₂ : ℂ) :
    P₁.isMod.weight α₁ →ₗ[ℂ] P₂.isMod.weight α₂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (ev G α₁ α₂) (fun a a' b => (hG α₁ α₂).1 a a' b)
    (fun c a b => (hG α₁ α₂).2.1 c a b) (fun a b b' => (hG α₁ α₂).2.2.1 a b b')
    (fun c a b => (hG α₁ α₂).2.2.2 c a b)

open Classical in
/-- **The honest bilinear form** `Ĝ` extending `G`. -/
noncomputable def hatG : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] ℂ :=
  letI := DirectSum.IsInternal.chooseDecomposition P₁.isMod.weight P₁.isMod.isInternal
  letI := DirectSum.IsInternal.chooseDecomposition P₂.isMod.weight P₂.isMod.isInternal
  ((DFinsupp.lsum ℂ fun α₁ => (DFinsupp.lsum ℂ (M := fun α₂ => P₂.isMod.weight α₂)
      (N := ℂ)).toLinearMap ∘ₗ LinearMap.pi fun α₂ => blockL G hG α₁ α₂)
    ∘ₗ (DirectSum.decomposeLinearEquiv P₁.isMod.weight).toLinearMap).compl₂
    (DirectSum.decomposeLinearEquiv P₂.isMod.weight).toLinearMap

theorem hatG_homog {α₁ α₂ : ℂ} {y : P₁.carrier} {z : P₂.carrier}
    (hy : y ∈ P₁.isMod.weight α₁) (hz : z ∈ P₂.isMod.weight α₂) :
    hatG G hG y z = G ⟨y, α₁, z, α₂, hy, hz⟩ := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition P₁.isMod.weight P₁.isMod.isInternal
  letI := DirectSum.IsInternal.chooseDecomposition P₂.isMod.weight P₂.isMod.isInternal
  have e1 : (DirectSum.decomposeLinearEquiv P₁.isMod.weight) y
      = DirectSum.of (fun i => P₁.isMod.weight i) α₁ ⟨y, hy⟩ :=
    DirectSum.decompose_of_mem _ hy
  have e2 : (DirectSum.decomposeLinearEquiv P₂.isMod.weight) z
      = DirectSum.of (fun i => P₂.isMod.weight i) α₂ ⟨z, hz⟩ :=
    DirectSum.decompose_of_mem _ hz
  simp only [hatG, LinearMap.compl₂_apply, LinearMap.comp_apply]
  erw [e1, e2]
  erw [DFinsupp.lsum_single]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  erw [DFinsupp.lsum_single]
  rfl

theorem hatG_pair (x : HomPair P₁ P₂) : hatG G hG x.w₁ x.w₂ = G x := by
  rw [hatG_homog G hG x.h₁ x.h₂]

end Hat

/-! ## `copT`, `tauHom` under the extension -/

/-- A `ℤ`-indexed finsum supported in `[0, K)` as a `Finset.range` sum. -/
theorem finsum_int_eq_range {X : Type*} [AddCommMonoid X] (f : ℤ → X) (K : ℕ)
    (h : ∀ k : ℤ, (k < 0 ∨ (K : ℤ) ≤ k) → f k = 0) :
    ∑ᶠ k : ℤ, f k = ∑ k ∈ Finset.range K, f (k : ℤ) := by
  rw [finsum_eq_sum_of_support_subset f (s := (Finset.range K).map
      ⟨fun r : ℕ => (r : ℤ), Nat.cast_injective⟩), Finset.sum_map]
  · rfl
  · intro k hk
    rw [Function.mem_support] at hk
    simp only [Finset.coe_map, Finset.coe_range, Set.mem_image, Set.mem_Iio,
      Function.Embedding.coeFn_mk]
    refine ⟨k.toNat, ?_, ?_⟩
    · by_contra hc; exact hk (h k (by omega))
    · by_contra hc; exact hk (h k (by omega))

/-- The modes of `P₁` (resp. `P₂`) as weak-module actions. -/
abbrev A₁ (P₁ : LWModule W) : WeakModule W P₁.carrier := P₁.isMod.toWeakModule

theorem copT_eq_rho {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) {γ : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading γ) (p : ℤ) (x : HomPair P₁ P₂) :
    copT ha p G x = rhoL (A₁ P₁) (A₁ P₂) a p (hatG G hG) x.w₁ x.w₂ := by
  rw [rhoL_apply, copT]
  congr 1
  · rw [hatG_homog G hG x.h₁ (VOA.mode_mem_weight P₂.isMod ha x.h₂ p)]; rfl
  · rw [finsum_int_eq_range _ (PzTensorAction.lowBound P₁.h x.α₁ γ) (fun r hr => by
      rcases hr with hr | hr
      · rw [cbz_neg hr]; ring
      · obtain ⟨rn, rfl⟩ : ∃ k : ℕ, r = k := ⟨r.toNat, by omega⟩
        simp only [A₁]
        rw [mode_eq_zero_of_lowBound P₁.isLow x.h₁ ha (show _ ≤ rn by omega)]; simp)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hatG_homog G hG (VOA.mode_mem_weight P₁.isMod ha x.h₁ r) x.h₂]
    rfl

theorem hat_copT {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) {γ : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading γ) (p : ℤ) :
    hatG (copT ha p G) (copT_mem_bilin hG ha p) = rhoL (A₁ P₁) (A₁ P₂) a p (hatG G hG) := by
  refine bil_ext_homog fun α₁ α₂ y z hy hz => ?_
  rw [hatG_homog _ _ hy hz]
  exact copT_eq_rho hG ha p ⟨y, α₁, z, α₂, hy, hz⟩

theorem tauHom_eq_tauHat {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) {β : ℤ} {u : 𝒱}
    (hu : u ∈ W.grading β) (m : ℤ) (x : HomPair P₁ P₂) :
    tauHom hu m G x = tauHat (A₁ P₁) (A₁ P₂) β u m (hatG G hG) x.w₁ x.w₂ := by
  simp only [tauHom, tauHat, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply,
    smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [copT_eq_rho hG]
  rfl

theorem hat_tauHom {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) {β : ℤ} {u : 𝒱}
    (hu : u ∈ W.grading β) (m : ℤ) :
    hatG (tauHom hu m G) (tauHom_mem_bilin hG hu m)
      = tauHat (A₁ P₁) (A₁ P₂) β u m (hatG G hG) := by
  refine bil_ext_homog fun α₁ α₂ y z hy hz => ?_
  rw [hatG_homog _ _ hy hz]
  exact tauHom_eq_tauHat hG hu m ⟨y, α₁, z, α₂, hy, hz⟩

/-! ## Truncation and compatibility under the extension -/

theorem hatG_zero (hG : IsBilin (0 : HomPair P₁ P₂ → ℂ)) : hatG (0 : HomPair P₁ P₂ → ℂ) hG = 0 :=
  bil_ext_homog fun α₁ α₂ y z hy hz => by rw [hatG_homog _ _ hy hz]; rfl

theorem hatG_congr {G G' : HomPair P₁ P₂ → ℂ} (h : G = G') (hG : IsBilin G) (hG' : IsBilin G') :
    hatG G hG = hatG G' hG' := by subst h; rfl

theorem truncAt_hat {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) {γ : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading γ) (htr : ∃ P : ℤ, ∀ p : ℤ, p ≤ P → copT ha p G = 0) :
    TruncAt (A₁ P₁) (A₁ P₂) a (hatG G hG) := by
  obtain ⟨P, hP⟩ := htr
  refine ⟨P, fun p hp => ?_⟩
  rw [← hat_copT hG ha p]
  have h0 : IsBilin (0 : HomPair P₁ P₂ → ℂ) := (bilin P₁ P₂).zero_mem
  rw [hatG_congr (hP p hp) _ h0, hatG_zero]

/-- Additivity of the slice defect in the first vector. -/
theorem Dsl_add_left {β : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] ℂ} {a : 𝒱}
    (htr : TruncAt (A₁ P₁) (A₁ P₂) a β) (m L : ℤ) (y y' : P₁.carrier) (z : P₂.carrier) :
    Dsl (A₁ P₁) (A₁ P₂) a m L β (y + y') z
      = Dsl (A₁ P₁) (A₁ P₂) a m L β y z + Dsl (A₁ P₁) (A₁ P₂) a m L β y' z := by
  unfold Dsl Out InL InR
  simp only [map_add, LinearMap.add_apply, mul_add]
  rw [finsum_add_distrib (Out_fin _ _ htr m L y z) (Out_fin _ _ htr m L y' z),
    finsum_add_distrib (InL_fin _ a m L β y z) (InL_fin _ a m L β y' z),
    finsum_add_distrib (InR_fin _ a m L β y z) (InR_fin _ a m L β y' z)]
  ring

theorem Dsl_add_right {β : P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] ℂ} {a : 𝒱}
    (htr : TruncAt (A₁ P₁) (A₁ P₂) a β) (m L : ℤ) (y : P₁.carrier) (z z' : P₂.carrier) :
    Dsl (A₁ P₁) (A₁ P₂) a m L β y (z + z')
      = Dsl (A₁ P₁) (A₁ P₂) a m L β y z + Dsl (A₁ P₁) (A₁ P₂) a m L β y z' := by
  unfold Dsl Out InL InR
  simp only [map_add, mul_add]
  rw [finsum_add_distrib (Out_fin _ _ htr m L y z) (Out_fin _ _ htr m L y z'),
    finsum_add_distrib (InL_fin _ a m L β y z) (InL_fin _ a m L β y z'),
    finsum_add_distrib (InR_fin _ a m L β y z) (InR_fin _ a m L β y z')]
  ring

theorem compatAt_hat {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) {γ : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading γ) (htr : ∃ P : ℤ, ∀ p : ℤ, p ≤ P → copT ha p G = 0)
    (hc : CompatFn G) : CompatAt (A₁ P₁) (A₁ P₂) a (hatG G hG) := by
  have hT := truncAt_hat hG ha htr
  intro L y z
  refine eq_zero_of_homog (fun y z => Dsl (A₁ P₁) (A₁ P₂) a 0 L (hatG G hG) y z)
    (fun y y' z => Dsl_add_left hT 0 L y y' z) (fun y z z' => Dsl_add_right hT 0 L y z z')
    (fun α₁ α₂ y z hy hz => ?_) y z
  set x : HomPair P₁ P₂ := ⟨y, α₁, z, α₂, hy, hz⟩ with hxdef
  obtain ⟨K, hK, hid⟩ := hc γ a ha L
  have hx := hid x
  unfold Dsl Out InL InR
  have hO : ∑ᶠ k : ℤ, (negOnePow k * cbz L k)
        * rhoL (A₁ P₁) (A₁ P₂) a (0 + L - k) (hatG G hG) y z
      = ∑ k ∈ Finset.range K, cbz L k * negOnePow k * copT ha (L - k) G x := by
    rw [finsum_int_eq_range _ K (fun k hk => by
      rcases hk with hk | hk
      · rw [cbz_neg hk]; ring
      · obtain ⟨kn, rfl⟩ : ∃ n : ℕ, k = n := ⟨k.toNat, by omega⟩
        have := copT_eq_rho hG ha (L - kn) x
        rw [hK kn (by omega)] at this
        rw [show (0 : ℤ) + L - kn = L - kn by ring, ← show x.w₁ = y from rfl,
          ← show x.w₂ = z from rfl, ← this]
        simp)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (0 : ℤ) + L - k = L - k by ring, copT_eq_rho hG ha (L - k) x]
    ring
  have hIL : ∑ᶠ r : ℤ, cbz 0 r * hatG G hG (mode ((A₁ P₁).YM a) (L + r) y) z
      = G (pairLeft x ha L) := by
    rw [finsum_eq_single _ 0 (fun r hr => by rw [cbz_zero_left, if_neg hr]; ring)]
    rw [cbz_zero, one_mul, add_zero, hatG_homog G hG (VOA.mode_mem_weight P₁.isMod ha hy L) hz]
    rfl
  have hIR : ∑ᶠ j : ℤ, (cbz L j * negOnePow (L - j))
        * hatG G hG y (mode ((A₁ P₂).YM a) (0 + j) z) = locR ha L G x := by
    rw [locR, finsum_int_eq_range _ (PzTensorAction.lowBound P₂.h α₂ γ) (fun j hj => by
      rcases hj with hj | hj
      · rw [cbz_neg hj]; ring
      · obtain ⟨jn, rfl⟩ : ∃ n : ℕ, j = n := ⟨j.toNat, by omega⟩
        simp only [A₁, zero_add]
        rw [mode_eq_zero_of_lowBound P₂.isLow hz ha (show _ ≤ jn by omega)]; simp)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [zero_add, hatG_homog G hG hy (VOA.mode_mem_weight P₂.isMod ha hz j)]
    rfl
  beta_reduce
  rw [hO, hIL, hIR, ← hx]
  ring

/-! ## The associator formula for `τ` on compatible functions -/

/-- Lower truncation of `τ` from that of the transposed coproduct. -/
theorem tauHom_eventually_zero {G : HomPair P₁ P₂ → ℂ}
    (htr : ∀ (γ : ℤ) (a : 𝒱) (ha : a ∈ W.grading γ), ∃ P : ℤ, ∀ p : ℤ, p ≤ P → copT ha p G = 0)
    {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) :
    ∃ N : ℤ, ∀ m : ℤ, N ≤ m → tauHom hu m G = 0 := by
  classical
  choose P hP using fun j : ℕ =>
    htr _ _ (VOA.VertexOperatorAlgebra.L_one_pow_mem W hu j)
  set S : ℕ := (Finset.range (β.toNat + 1)).sup fun j => (-(P j)).toNat with hS
  refine ⟨2 * β + S + 1, fun m hm => ?_⟩
  funext x
  simp only [tauHom, Pi.zero_apply]
  rw [Finset.sum_eq_zero fun j hj => ?_, mul_zero]
  have hle : (-(P j)).toNat ≤ S := Finset.le_sup (f := fun j => (-(P j)).toNat) hj
  rw [hP j (twIdx β m j) (by
    unfold twIdx
    have : -(P j) ≤ ((-(P j)).toNat : ℤ) := Int.self_le_toNat _
    have h2 : (((-(P j)).toNat : ℕ) : ℤ) ≤ (S : ℤ) := by exact_mod_cast hle
    omega)]
  simp

theorem tauHom_zero_fn {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) (m : ℤ) :
    tauHom hu m (0 : HomPair P₁ P₂ → ℂ) = 0 := by
  rw [← tauLin_apply, map_zero]

/-- **The associator formula for `τ` on every bilinear, lower truncated, compatible
function** (HLZ IV Thm. 5.44 at `z = 1`; no stability of a space is needed). -/
theorem tauAssoc_of_compatFn {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G)
    (htr : ∀ (γ : ℤ) (a : 𝒱) (ha : a ∈ W.grading γ), ∃ P : ℤ, ∀ p : ℤ, p ≤ P → copT ha p G = 0)
    (hc : CompatFn G) (β γ : ℤ) (u v : 𝒱) (hu : u ∈ W.grading β) (hv : v ∈ W.grading γ)
    (ell n : ℤ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
        (tauHom hu (ell - i) (tauHom hv (n + i) G)
          - negOnePow ell • tauHom hv (ell + n - i) (tauHom hu i G)))
      = tauHom (W.smul_mem_grading hu hv ell) n G := by
  obtain ⟨Nu, hNu⟩ := tauHom_eventually_zero htr hu
  obtain ⟨Nv, hNv⟩ := tauHom_eventually_zero htr hv
  have hfin : Function.HasFiniteSupport (fun i : ℤ => (negOnePow i * cbz ell i) •
      (tauHom hu (ell - i) (tauHom hv (n + i) G)
        - negOnePow ell • tauHom hv (ell + n - i) (tauHom hu i G))) := by
    refine hfs_of _ 0 (max (Nv - n) Nu) fun i hi => ?_
    rcases hi with hi | hi
    · rw [cbz_neg hi, mul_zero, zero_smul]
    · rw [hNv _ (by omega), hNu _ (by omega), tauHom_zero_fn, tauHom_zero_fn]; simp
  have hT : ∀ (c : 𝒱) (δ : ℤ), c ∈ W.grading δ → TruncAt (A₁ P₁) (A₁ P₂) c (hatG G hG) :=
    fun c δ hc' => truncAt_hat hG hc' (htr δ c hc')
  have hC : ∀ (c : 𝒱) (δ : ℤ), c ∈ W.grading δ → CompatAt (A₁ P₁) (A₁ P₂) c (hatG G hG) :=
    fun c δ hc' => compatAt_hat hG hc' (htr δ c hc') hc
  have hJ := tauHat_jacobi_pt (A₁ P₁) (A₁ P₂) hT hC hu hv ell 0 n
  funext x
  have hev := map_finsum (LinearMap.proj (R := ℂ) (φ := fun _ : HomPair P₁ P₂ => ℂ) x) hfin
  simp only [LinearMap.coe_proj, Function.eval] at hev
  rw [hev]
  have hl : ∀ i, ((negOnePow i * cbz ell i) •
      (tauHom hu (ell - i) (tauHom hv (n + i) G)
        - negOnePow ell • tauHom hv (ell + n - i) (tauHom hu i G))) x
      = (negOnePow i * cbz ell i)
        * (tauHat (A₁ P₁) (A₁ P₂) β u (ell + 0 - i) (tauHat (A₁ P₁) (A₁ P₂) γ v (n + i)
              (hatG G hG)) x.w₁ x.w₂
          - negOnePow ell * tauHat (A₁ P₁) (A₁ P₂) γ v (ell + n - i)
              (tauHat (A₁ P₁) (A₁ P₂) β u (0 + i) (hatG G hG)) x.w₁ x.w₂) := by
    intro i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [tauHom_eq_tauHat (tauHom_mem_bilin hG hv (n + i)) hu, hat_tauHom hG hv,
      tauHom_eq_tauHat (tauHom_mem_bilin hG hu i) hv, hat_tauHom hG hu,
      show ell + 0 - i = ell - i by ring, show (0 : ℤ) + i = i by ring]
  rw [finsum_congr hl, hJ, tauHom_eq_tauHat hG]
  rw [finsum_eq_single _ 0 (fun i hi => by rw [cbz_zero_left, if_neg hi]; ring)]
  simp only [cbz_zero, one_mul, add_zero, sub_zero, zero_add]

/-- **`HLZ544` holds** (for all `P₁, P₂`; the hypotheses of `τ`-stability are not needed). -/
theorem HLZ544_holds (P₁ P₂ : LWModule W) : HLZ544 P₁ P₂ := by
  intro S hSb _hst htr hcomp β γ u v hu hv ell n G hG
  exact tauAssoc_of_compatFn (hSb hG) (fun γ a ha => htr G hG γ a ha) (hcomp G hG) β γ u v
    hu hv ell n

/-- **`TauAssociator` holds** for strongly rational `V`. -/
theorem tauAssociator_holds (hV : StronglyRational W) : TauAssociator W :=
  PzTensorCompatProof.tauAssociator_of_HLZ544 hV fun P₁ P₂ _ _ => HLZ544_holds P₁ P₂

/-- **`CoeffWeakInput` holds** for strongly rational `V`: the span of the coefficient
functions is a weak `V`-module with `L(0) = L'(0)`. -/
theorem coeffWeakInput_holds (hV : StronglyRational W) : CoeffWeakInput W :=
  PzTensorCompatProof.coeffWeakInput_of_HLZ544 hV fun P₁ P₂ _ _ => HLZ544_holds P₁ P₂

/-- **`AssociativityInput` from ABD and the log-free iterate identity.** -/
theorem associativityInput_of_ABD (hV : StronglyRational W) (hABD : ABDWeakIsAdmissible W)
    (hZ : AssocCoeffIdentityZero W) : AssociativityInput W :=
  PzTensorCompatProof.associativityInput_of_HLZ544 hV hABD
    (fun P₁ P₂ _ _ => HLZ544_holds P₁ P₂) hZ

end VOA.Huang.PzTensorHatBridge
