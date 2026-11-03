/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.PzTensorTT
import VOA.Huang.PzTensorSpan

/-!
# The commutator formula for the `P(1)`-action — `TauCommutator`

The `P(1)`-action splits as `τ = τ_R + τ_L` (the part acting on `w₂`, the centre, and the part
acting on `w₁`, at distance `1`):

* `τ_R(u,m) G (w₁, w₂) = G(w₁, tw(u,m) w₂)` — the contragredient mode on `P₂`; its commutator
  formula is the library's module FHL identity (`PzTensorTT.tw_comm`);
* `τ_L(u,m) G (w₁, w₂) = Ĝ(D(u,m) w₁, w₂)` — the translated contragredient mode on `P₁`, read
  through the weight-indexed families of `PzTensorTT`; its commutator formula is
  `PzTensorTT.Dcomm_single` (transport through the skew-symmetry intertwiner);
* the cross terms commute exactly (`tauL_tauR_comm`).

`tauCommutator_holds : TauCommutator P₁ P₂` for all lowest-weight modules `P₁, P₂`
(Huang–Lepowsky–Zhang IV, Prop. 5.9, in the homogeneous-pair presentation, `z = 1`), and hence
`coeffWeakInput_of_tauAssociator : StronglyRational W → TauAssociator W → CoeffWeakInput W`.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.PzTensorCommutator

open VOA VOA.Huang.MatrixCoeff VOA.Huang.FusionTop VOA.Huang.AssocTarget
open VOA.Huang.LogRemovalSemisimple VOA.Huang.AssocTauStable VOA.Huang.PzTensorBilin
open VOA.Huang.PzTensorAction VOA.Huang.PzTensorTT VOA.Huang.PzTensorSpan
open VOA.Huang.LogRemovalWeak
open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {P₁ P₂ : LWModule W}

/-! ## Finite sums in a bilinear function -/

theorem IsBilin.sum_right {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) {ι : Type*}
    (s : Finset ι)
    (c : ι → ℂ) (z : ι → P₂.carrier) {α₁ α₂ : ℂ} {w₁ : P₁.carrier}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (hz : ∀ i, z i ∈ P₂.isMod.weight α₂) :
    G ⟨w₁, α₁, ∑ i ∈ s, c i • z i, α₂, h₁,
        Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hz i)⟩
      = ∑ i ∈ s, c i * G ⟨w₁, α₁, z i, α₂, h₁, hz i⟩ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact hG.zero_right _ rfl
  | insert a s ha ih =>
    rw [hG.addR ⟨w₁, α₁, ∑ i ∈ insert a s, c i • z i, α₂, h₁,
        Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hz i)⟩
      ⟨w₁, α₁, c a • z a, α₂, h₁, Submodule.smul_mem _ _ (hz a)⟩
      ⟨w₁, α₁, ∑ i ∈ s, c i • z i, α₂, h₁,
        Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hz i)⟩ rfl rfl rfl rfl rfl rfl
      (Finset.sum_insert ha)]
    rw [ih, hG.smulR ⟨w₁, α₁, c a • z a, α₂, h₁, Submodule.smul_mem _ _ (hz a)⟩
      ⟨w₁, α₁, z a, α₂, h₁, hz a⟩ (c a) rfl rfl rfl rfl, Finset.sum_insert ha]

/-! ## The two parts of the action -/

/-- The part of `τ(u, m)` acting on `w₂`. -/
noncomputable def tauR {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) (m : ℤ)
    (G : HomPair P₁ P₂ → ℂ) : HomPair P₁ P₂ → ℂ :=
  fun x => (-1 : ℂ) ^ β * ∑ j ∈ Finset.range (β.toNat + 1),
    ((j.factorial : ℂ)⁻¹) * G (pairRight x (VOA.VertexOperatorAlgebra.L_one_pow_mem W hu j)
      (twIdx β m j))

/-- The part of `τ(u, m)` acting on `w₁`. -/
noncomputable def tauL {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) (m : ℤ)
    (G : HomPair P₁ P₂ → ℂ) : HomPair P₁ P₂ → ℂ :=
  fun x => (-1 : ℂ) ^ β * ∑ j ∈ Finset.range (β.toNat + 1), ((j.factorial : ℂ)⁻¹) *
    ∑ r ∈ Finset.range (PzTensorAction.lowBound P₁.h x.α₁ (β - (j : ℤ))),
      cbz (twIdx β m j) r * G (pairLeft x (VOA.VertexOperatorAlgebra.L_one_pow_mem W hu j) r)

theorem tauHom_eq {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) (m : ℤ) (G : HomPair P₁ P₂ → ℂ) :
    tauHom hu m G = tauR hu m G + tauL hu m G := by
  funext x
  simp only [tauHom, tauR, tauL, copT, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem tauR_add {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) (m : ℤ) (G G' : HomPair P₁ P₂ → ℂ) :
    tauR hu m (G + G') = tauR hu m G + tauR hu m G' := by
  funext x
  simp only [tauR, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem tauL_add {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) (m : ℤ) (G G' : HomPair P₁ P₂ → ℂ) :
    tauL hu m (G + G') = tauL hu m G + tauL hu m G' := by
  funext x
  simp only [tauL, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem tauR_sub {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) (m : ℤ) (G G' : HomPair P₁ P₂ → ℂ) :
    tauR hu m (G - G') = tauR hu m G - tauR hu m G' := by
  funext x
  simp only [tauR, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem tauL_sub {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) (m : ℤ) (G G' : HomPair P₁ P₂ → ℂ) :
    tauL hu m (G - G') = tauL hu m G - tauL hu m G' := by
  funext x
  simp only [tauL, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-! ## The `w₂`-part is the contragredient mode on `P₂` -/

theorem matchIdx_eq (β m : ℤ) (j : ℕ) (α : ℂ) :
    α + (((β - (j : ℤ) : ℤ)) : ℂ) - ((twIdx β m j : ℤ) : ℂ) - 1 = matchIdx β m α := by
  simp only [twIdx, matchIdx]; push_cast; ring

/-- `τ_R(u, m) G (w₁, w₂) = G(w₁, tw(u,m) w₂)` on bilinear functions. -/
theorem tauR_eq {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) {β : ℤ} {u : 𝒱}
    (hu : u ∈ W.grading β) (m : ℤ) (x : HomPair P₁ P₂) :
    tauR hu m G x = G ⟨x.w₁, x.α₁, tw P₂.isMod β u m x.w₂, matchIdx β m x.α₂, x.h₁,
      tw_mem P₂.isMod hu m x.h₂⟩ := by
  have hz : ∀ j : ℕ, mode (P₂.isMod.YM ((W.L 1 ^ j) u)) (twIdx β m j) x.w₂
      ∈ P₂.isMod.weight (matchIdx β m x.α₂) := fun j => by
    have := VOA.mode_mem_weight P₂.isMod (VOA.VertexOperatorAlgebra.L_one_pow_mem W hu j)
      x.h₂ (twIdx β m j)
    rwa [matchIdx_eq] at this
  have e1 : G ⟨x.w₁, x.α₁, tw P₂.isMod β u m x.w₂, matchIdx β m x.α₂, x.h₁,
      tw_mem P₂.isMod hu m x.h₂⟩
      = G ⟨x.w₁, x.α₁, ∑ j ∈ Finset.range (β.toNat + 1),
          ((-1 : ℂ) ^ β * (j.factorial : ℂ)⁻¹) •
            mode (P₂.isMod.YM ((W.L 1 ^ j) u)) (twIdx β m j) x.w₂, matchIdx β m x.α₂, x.h₁,
          Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hz j)⟩ :=
    G_congr G rfl rfl (by simp only [tw, twIdx, Finset.smul_sum, smul_smul]) rfl
  classical
  rw [e1, IsBilin.sum_right hG _ _ _ x.h₁ hz, tauR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc]
  congr 1
  exact G_congr G rfl rfl rfl (by simp only [pairRight]; rw [← matchIdx_eq β m j])

theorem tauR_mem_bilin {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) {β : ℤ} {u : 𝒱}
    (hu : u ∈ W.grading β) (m : ℤ) : IsBilin (tauR hu m G) := by
  refine isBilin_of ?_ ?_ ?_ ?_
  · intro x y z h1 h2 h3 h4 h5 h6 h7
    rw [tauR_eq hG hu m x, tauR_eq hG hu m y, tauR_eq hG hu m z]
    exact hG.addL _ _ _ (by simp [h1]) (by simp [h2]) (by simp [h3]) (by simp [h4])
      (by simp [h5]) (by simp [h6]) (by simp [h7])
  · intro x y c h1 h3 h5 h7
    rw [tauR_eq hG hu m x, tauR_eq hG hu m y]
    exact hG.smulL _ _ c (by simp [h1]) (by simp [h3]) (by simp [h5]) (by simp [h7])
  · intro x y z h1 h2 h3 h4 h5 h6 h7
    rw [tauR_eq hG hu m x, tauR_eq hG hu m y, tauR_eq hG hu m z]
    exact hG.addR _ _ _ (by simp [h1]) (by simp [h2]) (by simp [h3]) (by simp [h4])
      (by simp [h5]) (by simp [h6]) (by simp [h7, tw_add])
  · intro x y c h1 h3 h5 h7
    rw [tauR_eq hG hu m x, tauR_eq hG hu m y]
    exact hG.smulR _ _ c (by simp [h1]) (by simp [h3]) (by simp [h5]) (by simp [h7, tw_smul])

theorem G_sub_right {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) {w₁ : P₁.carrier} {α₁ lam : ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) {a b : P₂.carrier} (ha : a ∈ P₂.isMod.weight lam)
    (hb : b ∈ P₂.isMod.weight lam) :
    G ⟨w₁, α₁, a, lam, h₁, ha⟩ - G ⟨w₁, α₁, b, lam, h₁, hb⟩
      = G ⟨w₁, α₁, a - b, lam, h₁, sub_mem ha hb⟩ := by
  rw [sub_eq_iff_eq_add, hG.addR ⟨w₁, α₁, a, lam, h₁, ha⟩ ⟨w₁, α₁, a - b, lam, h₁, sub_mem ha hb⟩
    ⟨w₁, α₁, b, lam, h₁, hb⟩ rfl rfl rfl rfl rfl rfl (by simp)]

/-- The finite range of the products `u_i v`. -/
noncomputable def Sset (u v : 𝒱) : Finset ℤ :=
  Finset.Icc (0 : ℤ) (max 0 (exists_smul_bound (W := W) u v).choose)

theorem smul_eq_zero_of_Sset (u v : 𝒱) {i : ℤ}
    (hi : max 0 (exists_smul_bound (W := W) u v).choose ≤ i) : W.smul u i v = 0 :=
  (exists_smul_bound (W := W) u v).choose_spec i (le_trans (le_max_right _ _) hi)

/-! ### The commutator of the `w₂`-parts -/

theorem tauR_comm {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) {β γ : ℤ} {u v : 𝒱}
    (hu : u ∈ W.grading β) (hv : v ∈ W.grading γ) (m n : ℤ) (x : HomPair P₁ P₂) :
    tauR hu m (tauR hv n G) x - tauR hv n (tauR hu m G) x
      = ∑ i ∈ Sset (W := W) u v,
          cbz m i * tauR (W.smul_mem_grading hu hv i) (m + n - i) G x := by
  classical
  set lam := matchIdx γ n (matchIdx β m x.α₂) with hlam
  have hlam' : matchIdx β m (matchIdx γ n x.α₂) = lam := by
    simp only [hlam, matchIdx]; ring
  have hlami : ∀ i : ℤ, matchIdx (β + γ - i - 1) (m + n - i) x.α₂ = lam := by
    intro i; simp only [hlam, matchIdx]; push_cast; ring
  rw [tauR_eq (tauR_mem_bilin hG hv n) hu m x, tauR_eq hG hv n,
    tauR_eq (tauR_mem_bilin hG hu m) hv n x, tauR_eq hG hu m]
  have ha := tw_mem P₂.isMod hv n (tw_mem P₂.isMod hu m x.h₂)
  have hb := tw_mem P₂.isMod hu m (tw_mem P₂.isMod hv n x.h₂)
  rw [hlam'] at hb
  rw [G_congr G (y := ⟨x.w₁, x.α₁, tw P₂.isMod γ v n (tw P₂.isMod β u m x.w₂), lam, x.h₁, ha⟩)
      rfl rfl rfl rfl,
    G_congr G (x := ⟨x.w₁, x.α₁, tw P₂.isMod β u m (tw P₂.isMod γ v n x.w₂),
      matchIdx β m (matchIdx γ n x.α₂), x.h₁, _⟩)
      (y := ⟨x.w₁, x.α₁, tw P₂.isMod β u m (tw P₂.isMod γ v n x.w₂), lam, x.h₁, hb⟩)
      rfl rfl rfl hlam',
    G_sub_right hG x.h₁ ha hb]
  have hcomm := tw_comm P₂.isMod hu hv m n x.h₂
  rw [finsum_cbz_eq (W := W) m (fun i hi => smul_eq_zero_of_Sset (W := W) u v hi)
    (fun i w => tw P₂.isMod (β + γ - i - 1) w (m + n - i) x.w₂)
    (fun i => tw_zero_state _ _ _ _)] at hcomm
  have hz : ∀ i : ℤ, tw P₂.isMod (β + γ - i - 1) (W.smul u i v) (m + n - i) x.w₂
      ∈ P₂.isMod.weight lam := fun i => by
    have := tw_mem P₂.isMod (W.smul_mem_grading hu hv i) (m + n - i) x.h₂
    rwa [hlami] at this
  rw [G_congr G (x := ⟨x.w₁, x.α₁, tw P₂.isMod γ v n (tw P₂.isMod β u m x.w₂)
        - tw P₂.isMod β u m (tw P₂.isMod γ v n x.w₂), matchIdx γ n (matchIdx β m x.α₂), x.h₁,
        sub_mem ha hb⟩)
      (y := ⟨x.w₁, x.α₁, ∑ i ∈ Sset (W := W) u v, cbz m i •
      tw P₂.isMod (β + γ - i - 1) (W.smul u i v) (m + n - i) x.w₂, lam, x.h₁,
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hz i)⟩) rfl rfl
      (by simp only; rw [hcomm]; rfl) hlam.symm,
    IsBilin.sum_right hG _ _ _ x.h₁ hz]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tauR_eq hG (W.smul_mem_grading hu hv i) (m + n - i) x]
  congr 1
  exact G_congr G rfl rfl rfl (hlami i).symm

/-! ### The cross terms commute -/

theorem tauL_tauR_comm {β γ : ℤ} {u v : 𝒱} (hu : u ∈ W.grading β) (hv : v ∈ W.grading γ)
    (m n : ℤ) (G : HomPair P₁ P₂ → ℂ) :
    tauL hu m (tauR hv n G) = tauR hv n (tauL hu m G) := by
  funext x
  simp only [tauL, tauR, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun r _ => ?_
  have e : ∀ {γ₁ γ₂ : ℤ} {a b : 𝒱} (ha : a ∈ W.grading γ₁) (hb : b ∈ W.grading γ₂) (r k : ℤ),
      G (pairRight (pairLeft x ha r) hb k) = G (pairLeft (pairRight x hb k) ha r) :=
    fun _ _ _ _ => rfl
  rw [e]
  ring

/-! ### The `w₁`-part through weight-indexed families -/

/-- `Ĝ(g) = Σ_δ G(proj_δ g_δ, δ; w₂, α₂)` for a bilinear `G` and fixed second slot. -/
noncomputable def Ghat {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) (x : HomPair P₁ P₂) :
    (ℂ →₀ P₁.carrier) →+ ℂ :=
  Finsupp.liftAddHom fun δ =>
    { toFun := fun z => G ⟨(internalProjTo P₁.isMod.isInternal δ z : P₁.carrier), δ, x.w₂, x.α₂,
        (internalProjTo P₁.isMod.isInternal δ z).2, x.h₂⟩
      map_zero' := hG.zero_left _ (by simp)
      map_add' := fun z z' => hG.addL _ _ _ rfl rfl rfl rfl rfl rfl (by simp) }

theorem Ghat_single {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) (x : HomPair P₁ P₂) {δ : ℂ}
    {z : P₁.carrier} (hz : z ∈ P₁.isMod.weight δ) :
    Ghat hG x (Finsupp.single δ z) = G ⟨z, δ, x.w₂, x.α₂, hz, x.h₂⟩ := by
  rw [Ghat, Finsupp.liftAddHom_apply_single]
  exact G_congr G (internalProjTo_coe_mem P₁.isMod hz) rfl rfl rfl

theorem Ghat_smul {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) (x : HomPair P₁ P₂) (a : ℂ)
    (g : ℂ →₀ P₁.carrier) : Ghat hG x (a • g) = a * Ghat hG x g := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g g' ih ih' => rw [smul_add, map_add, map_add, ih, ih', mul_add]
  | single δ z =>
    rw [Finsupp.smul_single, Ghat, Finsupp.liftAddHom_apply_single,
      Finsupp.liftAddHom_apply_single]
    exact hG.smulL _ _ a rfl rfl rfl (by simp)

theorem Ghat_congr {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) {x y : HomPair P₁ P₂}
    (h1 : x.w₂ = y.w₂) (h2 : x.α₂ = y.α₂) : Ghat hG x = Ghat hG y := by
  rcases x with ⟨xw1, xa1, xw2, xa2, xh1, xh2⟩
  rcases y with ⟨yw1, ya1, yw2, ya2, yh1, yh2⟩
  simp only at h1 h2
  subst h1 h2
  rfl

theorem pairLeft_label {x : HomPair P₁ P₂} {β : ℤ} {a : 𝒱} {j r : ℕ}
    (ha : a ∈ W.grading (β - (j : ℤ))) :
    (pairLeft x ha (r : ℤ)).α₁ = x.α₁ + ((β - (j : ℤ) - (r : ℤ) - 1 : ℤ) : ℂ) := by
  simp only [pairLeft]; push_cast; ring

/-- `τ_L(u, m) G (w₁, w₂) = Ĝ(D(u,m) w₁)` on bilinear functions. -/
theorem tauL_eq {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) {β : ℤ} {u : 𝒱}
    (hu : u ∈ W.grading β) (m : ℤ) (x : HomPair P₁ P₂) :
    tauL hu m G x = Ghat hG x (Dfam P₁.isMod β u m (Finsupp.single x.α₁ x.w₁)) := by
  rw [Dfam_single, Dpiece, map_sum, tauL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have ha := VOA.VertexOperatorAlgebra.L_one_pow_mem W hu j
  rw [map_finsum _ (Dterm_fin P₁.isMod β u m x.α₁ x.w₁ j)]
  have hterm : ∀ r : ℕ, Ghat hG x (Dterm P₁.isMod β u m x.α₁ x.w₁ j r)
      = coefD β m j r * G (pairLeft x ha r) := by
    intro r
    have hmem : coefD β m j r • mode (P₁.isMod.YM ((W.L 1 ^ j) u)) (r : ℤ) x.w₁
        ∈ P₁.isMod.weight (x.α₁ + ((β - (j : ℤ) - (r : ℤ) - 1 : ℤ) : ℂ)) := by
      refine Submodule.smul_mem _ _ ?_
      have := VOA.mode_mem_weight P₁.isMod ha x.h₁ r
      convert this using 2
      push_cast; ring
    rw [Dterm, Ghat_single hG x hmem]
    exact hG.smulL _ (pairLeft x ha r) _ (pairLeft_label ha) rfl rfl rfl
  rw [finsum_congr hterm, finsum_eq_sum_of_support_subset _
    (s := Finset.range (PzTensorAction.lowBound P₁.h x.α₁ (β - (j : ℤ)))) (by
      intro r hr
      rw [Function.mem_support] at hr
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra h
      apply hr
      rw [hG.zero_left _ (mode_eq_zero_of_lowBound P₁.isLow x.h₁ ha (by omega)), mul_zero])]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [coefD, twIdx]
  ring

theorem tauL_mem_bilin {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) {β : ℤ} {u : 𝒱}
    (hu : u ∈ W.grading β) (m : ℤ) : IsBilin (tauL hu m G) := by
  have h1 : tauHom hu m G ∈ bilin P₁ P₂ := tauHom_mem_bilin hG hu m
  have h2 : tauR hu m G ∈ bilin P₁ P₂ := tauR_mem_bilin hG hu m
  have : tauL hu m G = tauHom hu m G - tauR hu m G := by rw [tauHom_eq]; abel
  rw [this]
  exact Submodule.sub_mem _ h1 h2

/-- The iterate of the `w₁`-parts. -/
theorem tauL_iter {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) {β γ : ℤ} {u v : 𝒱}
    (hu : u ∈ W.grading β) (hv : v ∈ W.grading γ) (m n : ℤ) (x : HomPair P₁ P₂) :
    tauL hu m (tauL hv n G) x
      = Ghat hG x (Dfam P₁.isMod γ v n (Dfam P₁.isMod β u m (Finsupp.single x.α₁ x.w₁))) := by
  rw [tauL_eq (tauL_mem_bilin hG hv n) hu m x, Dfam_single, Dpiece, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_finsum _ (Dterm_fin P₁.isMod β u m x.α₁ x.w₁ j),
    map_finsum _ (Dterm_fin P₁.isMod β u m x.α₁ x.w₁ j),
    map_finsum (f := fun r => Dfam P₁.isMod γ v n (Dterm P₁.isMod β u m x.α₁ x.w₁ j r)) _
      ((Dterm_fin P₁.isMod β u m x.α₁ x.w₁ j).subset
      (Function.support_comp_subset (map_zero (Dfam P₁.isMod γ v n)) _))]
  refine finsum_congr fun r => ?_
  have ha := VOA.VertexOperatorAlgebra.L_one_pow_mem W hu j
  set δ := x.α₁ + ((β - (j : ℤ) - (r : ℤ) - 1 : ℤ) : ℂ)
  have hmem : coefD β m j r • mode (P₁.isMod.YM ((W.L 1 ^ j) u)) (r : ℤ) x.w₁
      ∈ P₁.isMod.weight δ := by
    refine Submodule.smul_mem _ _ ?_
    have := VOA.mode_mem_weight P₁.isMod ha x.h₁ r
    convert this using 2
    simp only [δ]; push_cast; ring
  rw [Dterm, Ghat_single _ x hmem, tauL_eq hG hv n]
  exact congrArg _ rfl |>.trans (by rw [Ghat_congr hG (x := ⟨_, δ, x.w₂, x.α₂, hmem, x.h₂⟩)
    (y := x) rfl rfl])

/-! ### The commutator of the `w₁`-parts -/

theorem tauL_comm {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) {β γ : ℤ} {u v : 𝒱}
    (hu : u ∈ W.grading β) (hv : v ∈ W.grading γ) (m n : ℤ) (x : HomPair P₁ P₂) :
    tauL hu m (tauL hv n G) x - tauL hv n (tauL hu m G) x
      = ∑ i ∈ Sset (W := W) u v,
          cbz m i * tauL (W.smul_mem_grading hu hv i) (m + n - i) G x := by
  rw [tauL_iter hG hu hv m n x, tauL_iter hG hv hu n m x, ← map_sub,
    Dcomm_single P₁.isMod hu hv m n x.h₁, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Ghat_smul, tauL_eq hG]

/-! ## The commutator formula -/

theorem tauHom_zero_state {G : HomPair P₁ P₂ → ℂ} (hG : G ∈ bilin P₁ P₂) {β : ℤ}
    (h0 : (0 : 𝒱) ∈ W.grading β) (m : ℤ) : tauHom h0 m G = 0 := by
  funext x
  simp only [tauHom, Pi.zero_apply]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun j _ => ?_)
  rw [copT_zero_state hG _ (map_zero _), mul_zero]

/-- **The commutator formula for the `P(1)`-action on all bilinear functions**
(Huang–Lepowsky–Zhang IV, Prop. 5.9). -/
theorem tauCommutator_holds (P₁ P₂ : LWModule W) : TauCommutator P₁ P₂ := by
  intro β γ u v hu hv m n G hG
  have hB : IsBilin G := hG
  -- the right side as a finite sum
  have hRHS : (∑ᶠ i : ℤ, cbz m i • tauHom (W.smul_mem_grading hu hv i) (m + n - i) G)
      = ∑ i ∈ Sset (W := W) u v, cbz m i • tauHom (W.smul_mem_grading hu hv i) (m + n - i) G := by
    refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
    rw [Function.mem_support] at hi
    rw [Sset, Finset.coe_Icc, Set.mem_Icc]
    by_contra h
    rcases not_and_or.1 h with h | h
    · exact hi (by rw [cbz_apply_neg m (by omega), zero_smul])
    · apply hi
      rw [tauHom_congr (W.smul_mem_grading hu hv i) (Submodule.zero_mem _)
        (smul_eq_zero_of_Sset (W := W) u v (by omega)), tauHom_zero_state hG, smul_zero]
  rw [hRHS]
  funext x
  rw [tauHom_eq hu m (tauHom hv n G), tauHom_eq hv n G, tauHom_eq hv n (tauHom hu m G),
    tauHom_eq hu m G, tauR_add, tauL_add, tauR_add, tauL_add]
  simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    tauHom_eq, mul_add, Finset.sum_add_distrib]
  rw [tauL_tauR_comm hu hv m n G, tauL_tauR_comm hv hu n m G]
  have hR := tauR_comm hB hu hv m n x
  have hL := tauL_comm hB hu hv m n x
  linear_combination hR + hL

/-- **`CoeffWeakInput` from the associator input alone** (strongly rational `V`): the
commutator formula is proved. -/
theorem coeffWeakInput_of_tauAssociator (hV : StronglyRational W) (hA : TauAssociator W) :
    CoeffWeakInput W :=
  coeffWeakInput_of_tau hV (fun P₁ P₂ _ _ => tauCommutator_holds P₁ P₂) hA

/-- **`AssociativityInput` from the remaining named inputs.** -/
theorem associativityInput_of_tauAssociator (hV : StronglyRational W)
    (hABD : ABDWeakIsAdmissible W) (hA : TauAssociator W) (hZ : AssocCoeffIdentityZero W) :
    AssociativityInput W :=
  associativityInput_of_tau hV hABD (fun P₁ P₂ _ _ => tauCommutator_holds P₁ P₂) hA hZ

end VOA.Huang.PzTensorCommutator
