/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SigmaExistLeech
import VOA.Modules.OrdSubmodule
import VOA.Modules.ZhuModule
import VOA.Moonshine.PlusWeightOne

/-!
# The top-level residual for `σ`, reduced to Zhu-algebra generators
(Moonshine step M8g twisted half)

`SigmaExistLeech.lean` reduced the existence of `σ` on `V₃⁺` (resp. `T_{s'}⁺`) to the top-level
residual `TopSigmaV3` (resp. `TopSigmaTT`), whose hard clause is the zero-mode intertwining
`φ (o(a) x) = o(σ a) φ x` for **every** homogeneous `a ∈ V₀⁺`.  This file shows that clause
follows from the same identity on any set `G` of homogeneous letters that **generates the Zhu
algebra** `A(V₀⁺)` in the sense of `ZhuGenerated G` (every subspace containing `𝟙`, `O(V₀⁺)` and
`G` and closed under Zhu's product `∗` is everything).

The proof is Zhu's easy direction, from the library (`ZhuModule`): on a lowest-weight space,
`o(a ∗ b) = o(a) o(b)` (`oMod_zhuMul_lowest_all`) and `o(O(V)) = 0` (`O_le_ker_rhoLW`).  To apply
it, `V₃⁺` (resp. `T_{s'}⁺`) and the `σ`-twisted `TP` are made into ordinary `V₀⁺`-modules with
lowest weight 2 (`MV3`, `MTsrc`, `MT`; `isLowestWeight_*`).

## Main results
* `twistOrd` — an ordinary module twisted by a VOA automorphism.
* `isLowestWeight_MV3`, `isLowestWeight_MT`, `isLowestWeight_MTsrc` — lowest weight 2
  (`V₃⁺` has nothing in weight 0, 1 since `(V_Λ⁺)₁ = 0` and `𝟙 ∈ V₀⁺`).
* `zero_mode_V3_of_zhuGenerated`, `topSigmaV3_of_zhuGenerated` — the zero-mode clause of
  `TopSigmaV3` from Zhu generators.
* `zero_mode_TT_of_zhuGenerated`, `topSigmaTT_of_zhuGenerated` — same for `T_{s'}⁺`.

## Status
`sorry`-free; `#print axioms`: `[propext, Classical.choice, Quot.sound]` (no `VOA.pbw`: only the
easy direction of Zhu's theorem is used).  Conditional on `ZhuGenerated G` and on the
zero-mode identities on `G`, neither of which is proved here.  Imported by the
umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.SigmaExist

open VOA VOA.Moonshine VOA.Moonshine.TrialityTw
open VOA.Moonshine.InvForm
open Module (End)
open Submodule

/-! ## §1  Twisted ordinary modules -/

section Twist

variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- An ordinary module twisted by a VOA automorphism (same grading, `Y^g(u) = Y(g u)`). -/
noncomputable def twistOrd (N : OrdVModule W M) (g : Aut W) : OrdVModule W M where
  toWeakModule := twistModule N.toWeakModule g
  weight := N.weight
  isInternal := N.isInternal
  L0_weight α x hx := by
    change mode (N.YM (g W.conformalVector)) 1 x = α • x
    rw [g.map_omega]
    exact N.L0_weight α x hx
  finrank := N.finrank
  boundedBelow := N.boundedBelow

end Twist

/-! ## §2  The ordinary `V₀⁺`-modules -/

/-- `V_Λ⁺` as an ordinary `V₀⁺`-module. -/
noncomputable def N0 : OrdVModule V0P VPlus := V0Sub.restrictOrdVModule (adjointModule leechVOAPlus)

/-- `TP` as an ordinary `V₀⁺`-module. -/
noncomputable def NT : OrdVModule V0P TP := V0Sub.restrictOrdVModule plusModule

/-- `V₃⁺` as a weak submodule of `N0`. -/
noncomputable def P3 : WeakModule.Submodule' N0.toWeakModule where
  carrier := frameSector 1
  act_mem u n x hx := actV_stab u (Set.mem_univ _) n x hx

/-- `T_{s'}⁺` as a weak submodule of `NT`. -/
noncomputable def PT (s' : ZMod 2) : WeakModule.Submodule' NT.toWeakModule where
  carrier := TPframe s'
  act_mem u n x hx := actT_stab s' u (Set.mem_univ _) n x hx

/-- `V₃⁺` as an ordinary `V₀⁺`-module. -/
noncomputable def MV3 : OrdVModule V0P (frameSector 1) := OrdVModule.submodule N0 P3

/-- `T_{s'}⁺` as an ordinary `V₀⁺`-module. -/
noncomputable def MTsrc (s' : ZMod 2) : OrdVModule V0P (TPframe s') := OrdVModule.submodule NT (PT s')

/-- `TP` with the `v0Sigma`-twisted action, as an ordinary `V₀⁺`-module. -/
noncomputable def MT : OrdVModule V0P TP := twistOrd NT v0Sigma

theorem mem_MV3_weight {α : ℂ} {x : frameSector 1} :
    x ∈ MV3.weight α ↔ (x : VPlus) ∈ adjWeight leechVOAPlus α := Iff.rfl

theorem mem_MV3_weight_two {x : frameSector 1} :
    x ∈ MV3.weight (2 : ℂ) ↔ (x : VPlus) ∈ leechVOAPlus.grading 2 := by
  rw [mem_MV3_weight, show (2 : ℂ) = ((2 : ℤ) : ℂ) by norm_num, adjWeight_cast]

/-- `V₃⁺` has lowest weight 2. -/
theorem isLowestWeight_MV3 : IsLowestWeight MV3 (2 : ℂ) := by
  intro α hα
  by_cases hint : ∃ m : ℤ, (m : ℂ) = α
  · obtain ⟨m, rfl⟩ := hint
    have hne : ∃ x : VPlus, x ∈ frameSector 1 ∧ x ∈ leechVOAPlus.grading m ∧ x ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hα
      rw [eq_bot_iff]
      intro x hx
      rw [Submodule.mem_bot]
      apply Subtype.ext
      have hx' : (x : VPlus) ∈ leechVOAPlus.grading m := by
        rw [← adjWeight_cast]; exact hx
      exact hcon x x.2 hx'
    obtain ⟨x, hx1, hxm, hx0⟩ := hne
    have hm2 : 2 ≤ m := by
      by_contra hlt
      push_neg at hlt
      apply hx0
      rcases lt_trichotomy m 0 with h | h | h
      · rw [leechVOAPlus.positivity m h] at hxm; exact (Submodule.mem_bot ℂ).mp hxm
      · subst h
        rw [leechVOAPlus.vacuum_grade, Submodule.mem_span_singleton] at hxm
        obtain ⟨c, rfl⟩ := hxm
        have h0 : c • leechVOAPlus.vacuum ∈ frameSector 0 := by
          rw [← V0Sub_carrier]; exact V0Sub.carrier.smul_mem c V0Sub.vacuum_mem
        have hdisj := frameSector_isInternal.submodule_iSupIndep.pairwiseDisjoint
          (show (0 : ZMod 2) ≠ 1 by decide)
        exact (Submodule.disjoint_def.mp hdisj) _ h0 hx1
      · have h1 : m = 1 := by omega
        subst h1
        rw [leechVOAPlus_grading_one] at hxm
        exact (Submodule.mem_bot ℂ).mp hxm
    exact ⟨(m - 2).toNat, by rw [show ((((m - 2).toNat : ℕ)) : ℂ) = ((m - 2 : ℤ) : ℂ) by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]]; push_cast; ring⟩
  · push_neg at hint
    exfalso
    apply hα
    change (adjWeight leechVOAPlus α).comap (frameSector 1).subtype = ⊥
    rw [adjWeight_eq_bot leechVOAPlus hint, Submodule.comap_bot]
    exact LinearMap.ker_eq_bot.mpr (frameSector 1).subtype_injective

theorem isLowestWeight_plus : ∀ α : ℂ, plusModule.weight α ≠ ⊥ → ∃ n : ℕ, α = (2 : ℂ) + n := by
  intro α hα
  obtain ⟨n, rfl, hn⟩ := plusModule_weight_ne_bot hα
  exact ⟨(n - 2).toNat, by rw [show ((((n - 2).toNat : ℕ)) : ℂ) = ((n - 2 : ℤ) : ℂ) by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]]; push_cast; ring⟩

/-- The twisted `TP` has lowest weight 2. -/
theorem isLowestWeight_MT : IsLowestWeight MT (2 : ℂ) := isLowestWeight_plus

/-- `T_{s'}⁺` has lowest weight 2. -/
theorem isLowestWeight_MTsrc (s' : ZMod 2) : IsLowestWeight (MTsrc s') (2 : ℂ) := by
  intro α hα
  apply isLowestWeight_plus α
  intro hbot
  apply hα
  change (plusModule.weight α).comap (TPframe s').subtype = ⊥
  rw [hbot, Submodule.comap_bot]
  exact LinearMap.ker_eq_bot.mpr (TPframe s').subtype_injective

theorem oMod_MV3 {k : ℤ} {a : V0Sub.carrier} (ha : (a : VPlus) ∈ leechVOAPlus.grading k)
    (x : frameSector 1) : ((oMod MV3 a x : frameSector 1) : VPlus) = actV a (k - 1) x := by
  rw [oMod_homogeneous MV3 (show a ∈ V0P.grading k from ha)]
  rfl

theorem oMod_MTsrc {s' : ZMod 2} {k : ℤ} {a : V0Sub.carrier} (ha : (a : VPlus) ∈ leechVOAPlus.grading k)
    (x : TPframe s') : ((oMod (MTsrc s') a x : TPframe s') : TP) = actT a (k - 1) x := by
  rw [oMod_homogeneous (MTsrc s') (show a ∈ V0P.grading k from ha)]
  rfl

theorem oMod_MT {k : ℤ} {a : V0Sub.carrier} (ha : (a : VPlus) ∈ leechVOAPlus.grading k) (y : TP) :
    oMod MT a y = actT (sig a) (k - 1) y := by
  rw [oMod_homogeneous MT (show a ∈ V0P.grading k from ha)]
  rfl

/-- `o(a) = 0` on a lowest-weight space for `a ∈ O(V)`. -/
theorem oMod_O_eq_zero {M : Type} [AddCommGroup M] [Module ℂ M] (N : OrdVModule V0P M)
    (hcw : IsLowestWeight N (2 : ℂ)) {a : V0Sub.carrier} (ha : a ∈ O V0P) {x : M}
    (hx : x ∈ N.weight (2 : ℂ)) : oMod N a x = 0 := by
  have h := O_le_ker_rhoLW N hcw ha
  rw [LinearMap.mem_ker] at h
  have := congrArg (fun f => ((f ⟨x, hx⟩ : N.weight (2 : ℂ)) : M)) h
  simp only at this
  rw [rhoLW_apply_coe] at this
  exact this

/-! ## §3  Zhu generation -/

/-- **Zhu generation**: `G` generates `A(V₀⁺)` — every subspace of `V₀⁺` containing `𝟙`,
`O(V₀⁺)` and `G`, and closed under Zhu's product `∗`, is all of `V₀⁺`.  (A pure statement about
`V₀⁺ ≅ V_{Λ₀}⁺`; not proved in the library.) -/
def ZhuGenerated (G : Set V0Sub.carrier) : Prop :=
  ∀ S : Submodule ℂ V0Sub.carrier, V0P.vacuum ∈ S → O V0P ≤ S →
    (∀ a ∈ S, ∀ b ∈ S, zhuMul V0P a b ∈ S) → G ⊆ S → S = ⊤

/-- The generic closure argument: if `ψ : Ω_M → N` intertwines `o(·)` on a Zhu-generating set,
it intertwines `o(a)` for all `a`. -/
theorem oMod_intertwine_of_zhuGenerated {M₁ M₂ : Type} [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂] (N₁ : OrdVModule V0P M₁) (N₂ : OrdVModule V0P M₂)
    (h₁ : IsLowestWeight N₁ (2 : ℂ)) (h₂ : IsLowestWeight N₂ (2 : ℂ)) (ψ : M₁ →ₗ[ℂ] M₂)
    (hψw : ∀ x ∈ N₁.weight (2 : ℂ), ψ x ∈ N₂.weight (2 : ℂ)) {G : Set V0Sub.carrier}
    (hG : ZhuGenerated G)
    (hGψ : ∀ g ∈ G, ∀ x ∈ N₁.weight (2 : ℂ), ψ (oMod N₁ g x) = oMod N₂ g (ψ x)) :
    ∀ a : V0Sub.carrier, ∀ x ∈ N₁.weight (2 : ℂ), ψ (oMod N₁ a x) = oMod N₂ a (ψ x) := by
  let S : Submodule ℂ V0Sub.carrier :=
    { carrier := {a | ∀ x ∈ N₁.weight (2 : ℂ), ψ (oMod N₁ a x) = oMod N₂ a (ψ x)}
      add_mem' := by
        intro a b ha hb x hx
        simp only [map_add, LinearMap.add_apply, ha x hx, hb x hx]
      zero_mem' := by
        intro x _
        simp only [map_zero, LinearMap.zero_apply]
      smul_mem' := by
        intro c a ha x hx
        simp only [map_smul, LinearMap.smul_apply, ha x hx] }
  have hS : S = ⊤ := by
    refine hG S ?_ ?_ ?_ hGψ
    · intro x _
      rw [oMod_vacuum, oMod_vacuum]; rfl
    · intro a ha x hx
      rw [oMod_O_eq_zero N₁ h₁ ha hx, oMod_O_eq_zero N₂ h₂ ha (hψw x hx), map_zero]
    · intro a ha b hb x hx
      rw [oMod_zhuMul_lowest_all N₁ h₁ a b hx, oMod_zhuMul_lowest_all N₂ h₂ a b (hψw x hx)]
      have hb' : oMod N₁ b x ∈ N₁.weight (2 : ℂ) := oMod_preserves_lowest_all N₁ b hx
      rw [ha _ hb', hb x hx]
  intro a x hx
  have : a ∈ S := by rw [hS]; trivial
  exact this x hx

/-! ## §4  `V₃⁺` -/

/-- **Zero modes from Zhu generators, on `V₃⁺`.**  If `φ` maps `(V₃⁺)₂` into weight 2 and
intertwines `o(g)` for the (homogeneous) letters of a Zhu-generating set `G`, it intertwines
`o(a)` for every homogeneous `a ∈ V₀⁺` — the `zero_mode` clause of `TopSigmaV3`. -/
theorem zero_mode_V3_of_zhuGenerated {φ : VPlus →ₗ[ℂ] TP}
    (hw : ∀ x ∈ OmegaV3, φ x ∈ plusModule.weight (2 : ℂ)) {G : Set V0Sub.carrier}
    (hG : ZhuGenerated G)
    (hGφ : ∀ g ∈ G, ∃ k : ℤ, (g : VPlus) ∈ leechVOAPlus.grading k ∧
      ∀ x ∈ OmegaV3, φ (actV g (k - 1) x) = actT (sig g) (k - 1) (φ x)) :
    ∀ (k : ℤ) (a : V0Sub.carrier), (a : VPlus) ∈ leechVOAPlus.grading k →
      ∀ x ∈ OmegaV3, φ (actV a (k - 1) x) = actT (sig a) (k - 1) (φ x) := by
  set ψ : frameSector 1 →ₗ[ℂ] TP := φ ∘ₗ (frameSector 1).subtype
  have hψw : ∀ x ∈ MV3.weight (2 : ℂ), ψ x ∈ MT.weight (2 : ℂ) := by
    intro x hx
    exact hw x ⟨x.2, mem_MV3_weight_two.mp hx⟩
  have hall := oMod_intertwine_of_zhuGenerated MV3 MT isLowestWeight_MV3 isLowestWeight_MT ψ hψw
    hG (by
      intro g hg x hx
      obtain ⟨k, hk, hgk⟩ := hGφ g hg
      change φ ((oMod MV3 g x : frameSector 1) : VPlus) = oMod MT g (φ x)
      rw [oMod_MV3 hk, oMod_MT hk]
      exact hgk x ⟨x.2, mem_MV3_weight_two.mp hx⟩)
  intro k a ha x hx
  have h := hall a ⟨x, hx.1⟩ (mem_MV3_weight_two.mpr hx.2)
  change φ ((oMod MV3 a ⟨x, hx.1⟩ : frameSector 1) : VPlus) = oMod MT a (φ x) at h
  rw [oMod_MV3 ha, oMod_MT ha] at h
  exact h

/-- **`TopSigmaV3` from Zhu generators.** -/
theorem topSigmaV3_of_zhuGenerated {s : ZMod 2} {φ : VPlus →ₗ[ℂ] TP}
    (hf : ∀ x ∈ OmegaV3, φ x ∈ TPframe s) (hw : ∀ x ∈ OmegaV3, φ x ∈ plusModule.weight (2 : ℂ))
    {G : Set V0Sub.carrier} (hG : ZhuGenerated G)
    (hGφ : ∀ g ∈ G, ∃ k : ℤ, (g : VPlus) ∈ leechVOAPlus.grading k ∧
      ∀ x ∈ OmegaV3, φ (actV g (k - 1) x) = actT (sig g) (k - 1) (φ x))
    (hc : ∃ t₀ : TLeechT, t₀ ∈ leechFrameT s ∧ t₀ ≠ 0 ∧ ∃ x ∈ OmegaV3, φ x = x0T t₀) :
    TopSigmaV3 s φ :=
  ⟨hf, hw, zero_mode_V3_of_zhuGenerated hw hG hGφ, hc⟩

/-! ## §5  `T_{s'}⁺` -/

theorem mem_MTsrc_weight_two {s' : ZMod 2} {x : TPframe s'} :
    x ∈ (MTsrc s').weight (2 : ℂ) ↔ (x : TP) ∈ plusModule.weight (2 : ℂ) := Iff.rfl

/-- **Zero modes from Zhu generators, on `T_{s'}⁺`.** -/
theorem zero_mode_TT_of_zhuGenerated {s' : ZMod 2} {φ : TP →ₗ[ℂ] TP}
    (hw : ∀ x ∈ OmegaT s', φ x ∈ plusModule.weight (2 : ℂ)) {G : Set V0Sub.carrier}
    (hG : ZhuGenerated G)
    (hGφ : ∀ g ∈ G, ∃ k : ℤ, (g : VPlus) ∈ leechVOAPlus.grading k ∧
      ∀ x ∈ OmegaT s', φ (actT g (k - 1) x) = actT (sig g) (k - 1) (φ x)) :
    ∀ (k : ℤ) (a : V0Sub.carrier), (a : VPlus) ∈ leechVOAPlus.grading k →
      ∀ x ∈ OmegaT s', φ (actT a (k - 1) x) = actT (sig a) (k - 1) (φ x) := by
  set ψ : TPframe s' →ₗ[ℂ] TP := φ ∘ₗ (TPframe s').subtype
  have hψw : ∀ x ∈ (MTsrc s').weight (2 : ℂ), ψ x ∈ MT.weight (2 : ℂ) := by
    intro x hx
    exact hw x ⟨x.2, hx⟩
  have hall := oMod_intertwine_of_zhuGenerated (MTsrc s') MT (isLowestWeight_MTsrc s')
    isLowestWeight_MT ψ hψw hG (by
      intro g hg x hx
      obtain ⟨k, hk, hgk⟩ := hGφ g hg
      change φ ((oMod (MTsrc s') g x : TPframe s') : TP) = oMod MT g (φ x)
      rw [oMod_MTsrc hk, oMod_MT hk]
      exact hgk x ⟨x.2, hx⟩)
  intro k a ha x hx
  have h := hall a ⟨x, hx.1⟩ hx.2
  change φ ((oMod (MTsrc s') a ⟨x, hx.1⟩ : TPframe s') : TP) = oMod MT a (φ x) at h
  rw [oMod_MTsrc ha, oMod_MT ha] at h
  exact h

/-- **`TopSigmaTT` from Zhu generators.** -/
theorem topSigmaTT_of_zhuGenerated {s' s : ZMod 2} {φ : TP →ₗ[ℂ] TP}
    (hf : ∀ x ∈ OmegaT s', φ x ∈ TPframe s) (hw : ∀ x ∈ OmegaT s', φ x ∈ plusModule.weight (2 : ℂ))
    {G : Set V0Sub.carrier} (hG : ZhuGenerated G)
    (hGφ : ∀ g ∈ G, ∃ k : ℤ, (g : VPlus) ∈ leechVOAPlus.grading k ∧
      ∀ x ∈ OmegaT s', φ (actT g (k - 1) x) = actT (sig g) (k - 1) (φ x))
    (hc : ∃ t₀ : TLeechT, t₀ ∈ leechFrameT s ∧ t₀ ≠ 0 ∧ ∃ x ∈ OmegaT s', φ x = x0T t₀) :
    TopSigmaTT s' s φ :=
  ⟨hf, hw, zero_mode_TT_of_zhuGenerated hw hG hGφ, hc⟩

end VOA.Moonshine.SigmaExist
