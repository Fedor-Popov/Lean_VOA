/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaTop

/-!
# (R-top) on `T_{s'}⁺`: the block map `φ_ψ` and what is proved about it

Twisted-source analogue of `SigmaTop.lean` for the residual `TopSigmaTT s' s φ`.

## Main results
* `OmegaT_le_span` — `(T_{s'}⁺)₂ = span {h_{w_m}(−½) ⊗ t : t ∈ T_{s'}}` (via
  `gradingT_one_eq`: `S[θ]` at doubled degree 1 is `{h_v(−½)}`, and the projector `projT s'`).
* `ZMT`, `ZMT_span`, `ZMT_of_basis`, `hGφ_TT_of_frame` — basis reduction of the zero-mode
  clause on `G = (V₀⁺)₂` to the frame quadratic and lattice letters on `h_{w_m} ⊗ t`;
  `hGφ_V3_of_frame` is the `V₃⁺` analogue in frame form.
* `phiTT ψ` — `h_{w_m}(−½) ⊗ t ↦ h_{w_m}(−½) ⊗ ψ_m t` for a family `ψ_m : T → T`
  (`compW` extracts the `h_{w_m}`-component); `phiTT_mem_frame`, `phiTT_mem_weight`, `phiTT_hits`.
* `phiTT_ZMT_diag` — diagonal frame letters intertwine for every `ψ`.
* `topSigmaTT_of_offdiag` — `TopSigmaTT s' s φ_ψ` from `ZhuGenerated G2` and the off-diagonal
  and lattice identities; `topSigmaTT_partial` — the unconditional part.

## Status
`sorry`-free; `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
**`TopSigmaTT` itself is NOT proved**; open inputs as for `SigmaTop.lean`.  Reached from the
umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false
set_option maxRecDepth 20000

namespace VOA.Moonshine.SigmaTop

open VOA VOA.Moonshine VOA.Moonshine.TrialityTw VOA.Moonshine.SigmaExist VOA.IntegralLattice
open VOA.LatGen HeisenbergN MvPolynomial VOA.TwistedHeisenberg
open VOA.Moonshine.LatticeTwisted VOA.Moonshine.Extraspecial
open Module (End)
open Submodule
open scoped TensorProduct

/-! ## §1  `(T⁺)₂ = h(−½) ⊗ T` -/

/-- `v ↦ h_v(−½)` as a linear map. -/
noncomputable def hvecL : (Fin (rank leech) → ℂ) →ₗ[ℂ] FockT 24 where
  toFun := hvec
  map_add' := hvec_add
  map_smul' := hvec_smul

theorem coeff_hvec (v : Fin (rank leech) → ℂ) (a : Fin (rank leech)) :
    MvPolynomial.coeff (Finsupp.single (0, cc a) 1) (hvec v) = v a := by
  rw [hvec, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single a]
  · rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_X, smul_eq_mul, mul_one]
  · intro b _ hb
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_X', if_neg, smul_zero]
    intro h
    have := Finsupp.single_left_injective (one_ne_zero) h
    exact hb (cc_inj.mp (Prod.ext_iff.mp this).2)
  · simp

theorem hvecL_injective : Function.Injective hvecL := by
  intro v w h
  funext a
  have := congrArg (MvPolynomial.coeff (Finsupp.single (0, cc a) 1)) h
  change MvPolynomial.coeff _ (hvec v) = MvPolynomial.coeff _ (hvec w) at this
  rwa [coeff_hvec, coeff_hvec] at this

theorem gradingT_one_eq : gradingT 24 1 = LinearMap.range hvecL := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨v, rfl⟩; exact hvec_mem_gradingT v
  · rw [LinearMap.finrank_range_of_inj hvecL_injective, finrank_gradingT_one,
      Module.finrank_fin_fun, leech_rank]

theorem twGrading_one_le_span :
    TwistedSector.twGrading 24 leechT 1 ≤ span ℂ {y | ∃ (v : Fin (rank leech) → ℂ) (t : TLeechT), y = hT v t} := by
  rintro _ ⟨z, rfl⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul p t =>
    obtain ⟨v, hv⟩ : (p : FockT 24) ∈ LinearMap.range hvecL := by rw [← gradingT_one_eq]; exact p.2
    refine subset_span ⟨v, t, ?_⟩
    rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, ← hv]; rfl
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

/-- The projector `½(1 + (−1)^s J)` onto `T_s`. -/
noncomputable def projT (s : ZMod 2) : End ℂ TLeechT := (1 / 2 : ℂ) • (1 + Extraspecial.sgn s • frameJL)

theorem sgn_mul_self (s : ZMod 2) : Extraspecial.sgn s * Extraspecial.sgn s = 1 := by
  rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) s with rfl | rfl
  · rw [Extraspecial.sgn_zero]; norm_num
  · rw [Extraspecial.sgn_one]; norm_num

theorem projT_apply (s : ZMod 2) (t : TLeechT) :
    projT s t = (1 / 2 : ℂ) • (t + Extraspecial.sgn s • frameJL t) := rfl

theorem projT_mem (s : ZMod 2) (t : TLeechT) : projT s t ∈ leechFrameT s := by
  rw [FrameT.mem_frameT, projT_apply]
  change frameJL _ = _
  rw [map_smul, map_add, map_smul, FrameT.frameJ_frameJ]
  have hc := sgn_mul_self s
  calc (1 / 2 : ℂ) • (frameJL t + Extraspecial.sgn s • t)
      = (1 / 2 : ℂ) • (Extraspecial.sgn s • t + (Extraspecial.sgn s * Extraspecial.sgn s) • frameJL t) := by
        rw [hc, one_smul, add_comm]
    _ = _ := by module

theorem projT_of_mem {s : ZMod 2} {t : TLeechT} (ht : t ∈ leechFrameT s) : projT s t = t := by
  have hJ : frameJL t = Extraspecial.sgn s • t := (FrameT.mem_frameT _ _ _).mp ht
  rw [projT_apply, hJ, smul_smul, sgn_mul_self, one_smul, ← two_smul ℂ t, smul_smul]
  norm_num

theorem vec_eq_sum_cw (v : Fin (rank leech) → ℂ) :
    v = ∑ m, ((∑ a, v a * cw m a) / 8) • cw m := by
  funext b
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h : ∀ a, ∑ m, v a * cw m a / 8 * cw m b = v a * (∑ m, cw m a * cw m b) / 8 := by
    intro a; rw [Finset.mul_sum, Finset.sum_div]; exact Finset.sum_congr rfl fun m _ => by ring
  simp only [h, cw_complete]
  rw [Finset.sum_eq_single b (fun a _ hab => by rw [if_neg hab]; ring) (by simp), if_pos rfl]
  ring

theorem hP_mem_span_cw {s : ZMod 2} (v : Fin (rank leech) → ℂ) {t : TLeechT} (ht : t ∈ leechFrameT s) :
    hP v t ∈ span ℂ {y | ∃ (m : Fin 24) (t' : TLeechT), t' ∈ leechFrameT s ∧ y = hP (cw m) t'} := by
  rw [vec_eq_sum_cw v, hP_sum_left]
  exact Submodule.sum_mem _ fun m _ => by
    rw [hP_smul_left]; exact Submodule.smul_mem _ _ (subset_span ⟨m, t, ht, rfl⟩)

/-- **`(T_{s'}⁺)₂ = span {h_{w_m}(−½) ⊗ t : t ∈ T_{s'}}`.** -/
theorem OmegaT_le_span (s' : ZMod 2) :
    OmegaT s' ≤ span ℂ {y | ∃ (m : Fin 24) (t : TLeechT), t ∈ leechFrameT s' ∧ y = hP (cw m) t} := by
  intro y hy
  have hg : (y : Tw) ∈ TwistedSector.twGrading 24 leechT 1 := by
    have hmem : (y : Tw) ∈ (plusModule.weight ((2 : ℚ) : ℂ)).map TP.subtype :=
      ⟨y, by simpa using hy.2, rfl⟩
    rw [map_plusModule_weight] at hmem
    have h := TwistedSector.twWeight_levelT 24 leechT 1
    have h1 : levelT 24 1 = (2 : ℚ) := by
      have := TwistedSector.levelT_24_odd 0
      simpa using this
    rw [h1] at h
    rw [← h]; exact hmem.2
  have hs := twGrading_one_le_span hg
  set Pj : Tw →ₗ[ℂ] Tw := (projT s').lTensor (FockT 24)
  have hPjy : Pj (y : Tw) = y := by
    have hJ : frameJL.lTensor (FockT 24) (y : Tw) = Extraspecial.sgn s' • (y : Tw) :=
      mem_twFrameL.mp hy.1
    change ((1 / 2 : ℂ) • (1 + Extraspecial.sgn s' • frameJL)).lTensor (FockT 24) (y : Tw) = _
    rw [LinearMap.lTensor_smul, LinearMap.lTensor_add, LinearMap.lTensor_smul]
    simp only [LinearMap.smul_apply, LinearMap.add_apply]
    rw [show (1 : End ℂ TLeechT) = LinearMap.id from rfl, LinearMap.lTensor_id, LinearMap.id_apply, hJ,
      smul_smul, sgn_mul_self, one_smul, ← two_smul ℂ (y : Tw), smul_smul]
    norm_num
  have hPj : ∀ z ∈ span ℂ {y | ∃ (v : Fin (rank leech) → ℂ) (t : TLeechT), y = hT v t},
      Pj z ∈ span ℂ {w | ∃ (v : Fin (rank leech) → ℂ) (t : TLeechT), t ∈ leechFrameT s' ∧ w = hT v t} := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, t, rfl⟩ := hz
      exact subset_span ⟨v, projT s' t, projT_mem s' t, by
        change (projT s').lTensor (FockT 24) (hvec v ⊗ₜ t) = hvec v ⊗ₜ projT s' t
        rw [LinearMap.lTensor_tmul]⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  have hy' := hPj _ hs
  rw [hPjy] at hy'
  -- pull back to `TP`
  have hS : {w | ∃ (v : Fin (rank leech) → ℂ) (t : TLeechT), t ∈ leechFrameT s' ∧ w = hT v t}
      = TP.subtype '' {y | ∃ (v : Fin (rank leech) → ℂ) (t : TLeechT), t ∈ leechFrameT s' ∧ y = hP v t} := by
    ext w
    constructor
    · rintro ⟨v, t, ht, rfl⟩; exact ⟨hP v t, ⟨v, t, ht, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨v, t, ht, rfl⟩, rfl⟩; exact ⟨v, t, ht, rfl⟩
  rw [hS, Submodule.span_image] at hy'
  obtain ⟨y', hy'1, hy'2⟩ := hy'
  rw [show y' = y from Subtype.ext hy'2] at hy'1
  have hle : span ℂ {y | ∃ (v : Fin (rank leech) → ℂ) (t : TLeechT), t ∈ leechFrameT s' ∧ y = hP v t}
      ≤ span ℂ {y | ∃ (m : Fin 24) (t : TLeechT), t ∈ leechFrameT s' ∧ y = hP (cw m) t} := by
    rw [span_le]
    rintro _ ⟨v, t, ht, rfl⟩
    exact hP_mem_span_cw v ht
  exact hle hy'1

/-! ## §2  Basis reduction for the source `T_{s'}⁺` -/

/-- The zero-mode identity for a letter `g` on a set `X ⊆ TP`. -/
def ZMT (φ : TP →ₗ[ℂ] TP) (X : Set TP) (g : V0Sub.carrier) : Prop :=
  ∀ x ∈ X, φ (actT g 1 x) = actT (sig g) 1 (φ x)

theorem ZMT_span (φ : TP →ₗ[ℂ] TP) (X : Set TP) {S : Set V0Sub.carrier}
    (hS : ∀ g ∈ S, ZMT φ X g) : ∀ g ∈ span ℂ S, ZMT φ X g := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg => exact hS g hg
  | zero =>
    intro x _
    rw [sig_zero]
    simp only [actT, ZeroMemClass.coe_zero, map_zero, mode_zero, LinearMap.zero_apply]
  | add u v _ _ hu hv =>
    intro x hx
    rw [actT_add_left, map_add, hu x hx, hv x hx, sig_add, actT_add_left]
  | smul c u _ hu =>
    intro x hx
    rw [actT_smul_left, map_smul, hu x hx, sig_smul, actT_smul_left]

theorem ZMT_of_basis (φ : TP →ₗ[ℂ] TP) (s' : ZMod 2) (g : V0Sub.carrier)
    (h : ∀ (m : Fin 24) (t : TLeechT), t ∈ leechFrameT s' →
      φ (actT g 1 (hP (cw m) t)) = actT (sig g) 1 (φ (hP (cw m) t))) :
    ZMT φ (OmegaT s') g := by
  intro x hx
  have hxs := OmegaT_le_span s' hx
  clear hx
  induction hxs using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨m, t, ht, rfl⟩ := hy
    exact h m t ht
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]
  | smul c y _ hy => rw [map_smul, map_smul, hy, map_smul, map_smul]

/-- **Basis reduction of the zero-mode clause on `G = (V₀⁺)₂`, source `T_{s'}⁺`**, in frame
form: the frame quadratic letters `w_j(−1)w_k(−1)𝟙` and the lattice letters `e^γ + e^{−γ}`
(`γ ∈ S₀`) suffice.  The output is the `hGφ` input of `topSigmaTT_of_zhuGenerated`. -/
theorem hGφ_TT_of_frame (φ : TP →ₗ[ℂ] TP) (s' : ZMod 2)
    (hD : ∀ j k : Fin 24, ZMT φ (OmegaT s') (dV (fw j) (fw k)))
    (hL : ∀ γ ∈ halfFourChi 0, ZMT φ (OmegaT s') (lV' γ)) :
    ∀ g ∈ G2, ∃ k : ℤ, (g : VPlus) ∈ leechVOAPlus.grading k ∧
      ∀ x ∈ OmegaT s', φ (actT g (k - 1) x) = actT (sig g) (k - 1) (φ x) := by
  intro g hg
  refine ⟨2, hg, ?_⟩
  rw [show (2 : ℤ) - 1 = 1 by norm_num]
  have hspan := G2_le_span hg
  have hbasis : ∀ g' ∈ Set.range (fun p : Fin (rank leech) × Fin (rank leech) => qV p.1 p.2)
      ∪ lV' '' (halfFourChi 0 : Set leech.carrier), ZMT φ (OmegaT s') g' := by
    rintro g' (⟨p, rfl⟩ | ⟨γ, hγ, rfl⟩)
    · exact ZMT_span φ _ (S := Set.range fun p : Fin 24 × Fin 24 => dV (fw p.1) (fw p.2))
        (by rintro _ ⟨q, rfl⟩; exact hD q.1 q.2) _ (qV_mem_span_dV p.1 p.2)
    · exact hL γ hγ
  exact ZMT_span φ _ hbasis g hspan

/-- The `V₃⁺` analogue in frame form. -/
theorem hGφ_V3_of_frame (φ : VPlus →ₗ[ℂ] TP)
    (hD : ∀ j k : Fin 24, ZM φ OmegaV3 (dV (fw j) (fw k)))
    (hL : ∀ γ ∈ halfFourChi 0, ZM φ OmegaV3 (lV' γ)) :
    ∀ g ∈ G2, ∃ k : ℤ, (g : VPlus) ∈ leechVOAPlus.grading k ∧
      ∀ x ∈ OmegaV3, φ (actV g (k - 1) x) = actT (sig g) (k - 1) (φ x) := by
  refine hGφ_V3_of_basis φ (fun a b n hn => ?_) (fun γ hγ n hn => hL γ hγ _ (frameX0P_mem_OmegaV3 hn))
  exact ZM_span φ OmegaV3 (S := Set.range fun p : Fin 24 × Fin 24 => dV (fw p.1) (fw p.2))
    (by rintro _ ⟨p, rfl⟩; exact hD p.1 p.2) (qV a b) (qV_mem_span_dV a b) _ (frameX0P_mem_OmegaV3 hn)

/-! ## §3  The block map `φ_ψ` on `(T_{s'}⁺)₂` -/

/-- The `h_a(−½)`-component of a vector of `S[θ] ⊗ T`. -/
noncomputable def compA (a : Fin (rank leech)) : Tw →ₗ[ℂ] TLeechT :=
  (TensorProduct.lid ℂ TLeechT).toLinearMap ∘ₗ
    (MvPolynomial.lcoeff ℂ (Finsupp.single (0, cc a) 1)).rTensor TLeechT

theorem compA_hT (a : Fin (rank leech)) (v : Fin (rank leech) → ℂ) (t : TLeechT) :
    compA a (hT v t) = v a • t := by
  change (TensorProduct.lid ℂ TLeechT) ((MvPolynomial.lcoeff ℂ _).rTensor TLeechT (hvec v ⊗ₜ t)) = _
  rw [LinearMap.rTensor_tmul, MvPolynomial.lcoeff_apply, coeff_hvec, TensorProduct.lid_tmul]

/-- The `h_{w_m}(−½)`-component of a vector of `(T⁺)₂`. -/
noncomputable def compW (m : Fin 24) : TP →ₗ[ℂ] TLeechT :=
  (1 / 8 : ℂ) • ∑ a, cw m a • (compA a ∘ₗ TP.subtype)

theorem compW_hP (m m' : Fin 24) (t : TLeechT) :
    compW m (hP (cw m') t) = if m = m' then t else 0 := by
  simp only [compW, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, hP_coe]
  change (1 / 8 : ℂ) • ∑ a, cw m a • compA a (hT (cw m') t) = _
  simp only [compA_hT, smul_smul, ← Finset.sum_smul]
  rw [cw_orth]
  split_ifs <;> simp

/-- `t ↦ h_{w_m}(−½) ⊗ t` as a linear map. -/
noncomputable def hPL (m : Fin 24) : TLeechT →ₗ[ℂ] TP where
  toFun t := hP (cw m) t
  map_add' t t' := by apply Subtype.ext; simp [hP_coe, TensorProduct.tmul_add]
  map_smul' c t := by apply Subtype.ext; simp [hP_coe, TensorProduct.tmul_smul]

/-- **The block top map** `φ_ψ (h_{w_m}(−½) ⊗ t) = h_{w_m}(−½) ⊗ ψ_m t`, for an arbitrary family
`ψ_m : T → T`. -/
noncomputable def phiTT (ψ : Fin 24 → TLeechT →ₗ[ℂ] TLeechT) : TP →ₗ[ℂ] TP :=
  ∑ m, hPL m ∘ₗ ψ m ∘ₗ compW m

theorem phiTT_hP (ψ : Fin 24 → TLeechT →ₗ[ℂ] TLeechT) (m : Fin 24) (t : TLeechT) :
    phiTT ψ (hP (cw m) t) = hP (cw m) (ψ m t) := by
  rw [phiTT, LinearMap.sum_apply, Finset.sum_eq_single m]
  · simp only [LinearMap.comp_apply, compW_hP]; rfl
  · intro m' _ hm
    simp only [LinearMap.comp_apply, compW_hP, if_neg hm, map_zero]
  · simp

theorem phiTT_mem_weight (ψ : Fin 24 → TLeechT →ₗ[ℂ] TLeechT) (x : TP) :
    phiTT ψ x ∈ plusModule.weight (2 : ℂ) := by
  rw [phiTT, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun m _ => hP_mem_weight _ _

theorem phiTT_mem_frame {s : ZMod 2} {ψ : Fin 24 → TLeechT →ₗ[ℂ] TLeechT}
    (hψ : ∀ m t, ψ m t ∈ leechFrameT s) (x : TP) : phiTT ψ x ∈ TPframe s := by
  rw [phiTT, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun m _ => hP_mem_frame _ (hψ m _)

theorem hP_mem_OmegaT {s' : ZMod 2} (v : Fin (rank leech) → ℂ) {t : TLeechT} (ht : t ∈ leechFrameT s') :
    hP v t ∈ OmegaT s' := ⟨hP_mem_frame v ht, hP_mem_weight v t⟩

theorem phiTT_hits {s' : ZMod 2} {ψ : Fin 24 → TLeechT →ₗ[ℂ] TLeechT} {t₁ t₀ : TLeechT}
    (ht₁ : t₁ ∈ leechFrameT s') (hblk : ∀ m, ψ m t₁ = t₀) :
    ∃ x ∈ OmegaT s', phiTT ψ x = x0T t₀ := by
  set c0 : Fin (rank leech) := Fin.cast leech_rank.symm 0
  refine ⟨∑ m, (cw m c0 / 8) • hP (cw m) t₁,
    Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hP_mem_OmegaT _ ht₁), ?_⟩
  rw [map_sum, x0T_eq_hP, single_eq_sum_cw, hP_sum_left]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, phiTT_hP, hblk, hP_smul_left]

/-- **The diagonal frame letters intertwine on `T_{s'}⁺`**, for every block family `ψ`. -/
theorem phiTT_ZMT_diag (ψ : Fin 24 → TLeechT →ₗ[ℂ] TLeechT) (s' : ZMod 2) (j : Fin 24) :
    ZMT (phiTT ψ) (OmegaT s') (dV (fw j) (fw j)) := by
  refine ZMT_of_basis _ s' _ fun m t _ => ?_
  rw [actT_dV_fw_hP, map_smul, phiTT_hP, sig_dV_fw, actT_dV_fw_hP]

/-! ## §4  Assembly for `T_{s'}⁺` -/

/-- **`TopSigmaTT` for `φ_ψ`, conditional on the off-diagonal and lattice letters.** -/
theorem topSigmaTT_of_offdiag {s' s : ZMod 2} {ψ : Fin 24 → TLeechT →ₗ[ℂ] TLeechT}
    (hψ : ∀ m t, ψ m t ∈ leechFrameT s) {t₁ t₀ : TLeechT} (ht₁ : t₁ ∈ leechFrameT s')
    (ht₀ : t₀ ∈ leechFrameT s) (h0 : t₀ ≠ 0) (hblk : ∀ m, ψ m t₁ = t₀) (hZhu : ZhuGenerated G2)
    (hoff : ∀ j k : Fin 24, j ≠ k → ZMT (phiTT ψ) (OmegaT s') (dV (fw j) (fw k)))
    (hlat : ∀ γ ∈ halfFourChi 0, ZMT (phiTT ψ) (OmegaT s') (lV' γ)) :
    TopSigmaTT s' s (phiTT ψ) := by
  refine topSigmaTT_of_zhuGenerated (fun x _ => phiTT_mem_frame hψ x)
    (fun x _ => phiTT_mem_weight ψ x) hZhu ?_ ⟨t₀, ht₀, h0, phiTT_hits ht₁ hblk⟩
  refine hGφ_TT_of_frame _ s' (fun j k => ?_) hlat
  by_cases hjk : j = k
  · subst hjk; exact phiTT_ZMT_diag ψ s' j
  · exact hoff j k hjk

/-- **The proved part of (R-top) on `T_{s'}⁺`.** For all `s', s` there is a linear
`φ : TP → TP` with `φ (T_{s'}⁺)₂ ⊆ (T_s⁺)₂`, hitting a cyclic vector `x0T t₀`, and intertwining
the zero modes of the 24 diagonal frame letters `w_j(−1)²𝟙` with those of their `σ`-images. -/
theorem topSigmaTT_partial (s' s : ZMod 2) :
    ∃ φ : TP →ₗ[ℂ] TP, (∀ x ∈ OmegaT s', φ x ∈ TPframe s) ∧
      (∀ x ∈ OmegaT s', φ x ∈ plusModule.weight (2 : ℂ)) ∧
      (∃ t₀ : TLeechT, t₀ ∈ leechFrameT s ∧ t₀ ≠ 0 ∧ ∃ x ∈ OmegaT s', φ x = x0T t₀) ∧
      (∀ j : Fin 24, ∀ x ∈ OmegaT s',
        φ (actT (dV (fw j) (fw j)) 1 x) = actT (sig (dV (fw j) (fw j))) 1 (φ x)) := by
  obtain ⟨t₀, ht₀, h0⟩ := exists_ne_zero_leechFrameT s
  obtain ⟨t₁, ht₁, h1⟩ := exists_ne_zero_leechFrameT s'
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h1
  let ψ : Fin 24 → TLeechT →ₗ[ℂ] TLeechT := fun _ => f.smulRight t₀
  have hψ : ∀ m t, ψ m t ∈ leechFrameT s := fun m t => Submodule.smul_mem _ _ ht₀
  have hblk : ∀ m, ψ m t₁ = t₀ := fun m => by
    change f t₁ • t₀ = t₀; rw [hf, one_smul]
  exact ⟨phiTT ψ, fun x _ => phiTT_mem_frame hψ x, fun x _ => phiTT_mem_weight ψ x,
    ⟨t₀, ht₀, h0, phiTT_hits ht₁ hblk⟩, fun j => phiTT_ZMT_diag ψ s' j⟩

end VOA.Moonshine.SigmaTop
