/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchFunctorEquivGraded
import VOA.Modules.ZhuVermaAnArchActionNaturalLevelShift
import VOA.Modules.ZhuVermaAnArchConstructionAUniform
import VOA.Modules.ZhuVermaAnArchHoleF

/-!
# `MUJNatural` for the CANONICAL `J` — DJ Prop 3.5 functoriality, proved

`Modules.ZhuVermaAnArchFunctorEquivGraded` proved the graded-iso crux of DJ Prop 3.5: the genuine
functor map `M(φ) = MU.functorEquiv φ` carries each level-`n` layer `MU.deg W U n` onto the
level-`n` layer, in particular the bottom `MU.deg W U 0`.  `ZhuVermaAnArchActionNaturalLevelShift`
proved the
action naturality `MUActionNatural F` (DJ Prop 3.4) for the level-shift construction.

This file combines them to **prove `MUJNatural` for the canonical `J`**: define the canonical
maximal bottom-trivial graded invariant submodule

  `Jcanon F U := ⨆ {S | S is F-invariant, layer-graded, and S ⊓ MU.deg W U 0 = ⊥}`,

and show the genuine map `M(φ)` carries `Jcanon F U₁` **onto** `Jcanon F U₂`
(`MUJNatural_of_canonical`).  This is the entire functoriality content of DJ Prop 3.5: `M(φ)` is an
`𝒱`-module iso (`MUActionNatural`) that is graded (`functorEquiv_map_deg`) and bottom-preserving, so
it gives an order-isomorphism of the poset of bottom-trivial graded invariant submodules — hence
carries the canonical (maximal, `= ⨆`) one onto the canonical one.

## What is built (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`InducedAssignment.IsInvSub` / `IsLayerGraded` / `GoodSub`** — the three defining properties of
  a bottom-trivial graded invariant submodule.
* **`InducedAssignment.goodSub_map`** — the transfer bijection: `M(φ)` carries `GoodSub F U₁` onto
  `GoodSub F U₂`.
* **`InducedAssignment.Jcanon`** — the canonical `J = ⨆ {S | GoodSub}`.
* **`InducedAssignment.MUJNatural_of_canonical`** — **DJ Prop 3.5 functoriality**:
  `map M(φ) (Jcanon F U₁) = Jcanon F U₂`.
* **`InducedAssignment.MUJNatural_of_ludata_canonical`** — the bridge: if the carried maximal-`J` is
  the canonical one, then `MUJNatural F` is a **theorem**.

## What remains for `MUJNatural F` on the actual family (honest)

The functoriality (this file) is unconditional given `MUActionNatural F`.  To discharge
`MUJNatural F` on the actual bijection family one needs `(F.ludata U).J.carrier = Jcanon F U` — that
the carried maximal `J` **is** the canonical one, the content of the maximal-`J` existence theorem
(the canonical `⨆` is itself bottom-trivial and its quotient is graded-simple — the deep
DLM/Dong–Jiang theory, carried in `LUMaxData`).  This file discharges the functoriality half.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`), Prop 3.5; DLM3 §4; Gannon §5.3.2, Thm 5.3.4;
`ZhuVermaAnArchFunctorEquivGraded`, `ZhuVermaAnArchActionNaturalLevelShift` (`MUActionNatural`),
`ZhuVermaAnArchHoleMuEquiv` (`MUJNatural`, `MU.functorEquiv`).
-/

namespace VOA

open scoped BigOperators TensorProduct DirectSum
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## The defining properties of a bottom-trivial graded invariant submodule -/

/-- `S` is **invariant** under the `𝒱`-mode action of `M(U)`. -/
def IsInvSub (F : LUFamily W) (U : AMod W) (S : Submodule ℂ (MU W U)) : Prop :=
  ∀ (u : 𝒱) (n : ℤ) (x : MU W U), x ∈ S → (F.mudata U).weak.act u n x ∈ S

/-- `S` is **layer-graded**: `S = ⨆ₙ (S ⊓ MU.deg W U n)` (the ℕ-layer grading, `h`-independent). -/
def IsLayerGraded (U : AMod W) (S : Submodule ℂ (MU W U)) : Prop :=
  S = ⨆ n : ℕ, (S ⊓ MU.deg W U n)

/-- `S` is a **bottom-trivial graded invariant** submodule: invariant, layer-graded, and meeting the
bottom `MU.deg W U 0` trivially. -/
def GoodSub (F : LUFamily W) (U : AMod W) (S : Submodule ℂ (MU W U)) : Prop :=
  IsInvSub F U S ∧ IsLayerGraded U S ∧ S ⊓ MU.deg W U 0 = ⊥

/-! ## The transfer of `GoodSub` under the genuine functor map `M(φ)` -/

/-- **Invariance transfers under `M(φ)`** (`M(φ)` intertwines the actions, `MUActionNatural`). -/
theorem isInvSub_map_iff (F : LUFamily W) (hnat : MUActionNatural F) {U₁ U₂ : AMod W}
    (φ : AModEquiv W U₁ U₂) (S : Submodule ℂ (MU W U₁)) :
    IsInvSub F U₂ (S.map (MU.functorEquiv φ).toLinearMap) ↔ IsInvSub F U₁ S := by
  constructor
  · intro hinv u n x hx
    have hfx : (MU.functorEquiv φ) x ∈ S.map (MU.functorEquiv φ).toLinearMap :=
      Submodule.mem_map_of_mem hx
    have h2 := hinv u n _ hfx
    rw [← hnat φ u n x] at h2
    rw [Submodule.mem_map] at h2
    obtain ⟨y, hy, hxy⟩ := h2
    rwa [(MU.functorEquiv φ).injective hxy] at hy
  · intro hinv u n y hy
    rw [Submodule.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [LinearEquiv.coe_coe, ← hnat φ u n x]
    exact Submodule.mem_map_of_mem (hinv u n x hx)

/-- The level-`n` piece transfers: `M(φ)` carries `S ⊓ MU.deg n` onto `(M(φ) S) ⊓ MU.deg n`
(injectivity of `M(φ)` for `map_inf`, `functorEquiv_map_deg` for the layer). -/
theorem map_inf_deg {U₁ U₂ : AMod W} (φ : AModEquiv W U₁ U₂)
    (S : Submodule ℂ (MU W U₁)) (n : ℕ) :
    (S ⊓ MU.deg W U₁ n).map (MU.functorEquiv φ).toLinearMap
      = (S.map (MU.functorEquiv φ).toLinearMap) ⊓ MU.deg W U₂ n := by
  have hinj : Function.Injective (MU.functorEquiv φ).toLinearMap := (MU.functorEquiv φ).injective
  rw [Submodule.map_inf _ hinj]
  congr 1
  exact MU.functorEquiv_map_deg φ n

/-- **Layer-gradedness transfers under `M(φ)`** (graded iso + injectivity). -/
theorem isLayerGraded_map_iff {U₁ U₂ : AMod W}
    (φ : AModEquiv W U₁ U₂) (S : Submodule ℂ (MU W U₁)) :
    IsLayerGraded U₂ (S.map (MU.functorEquiv φ).toLinearMap) ↔ IsLayerGraded U₁ S := by
  have hsup : (⨆ n : ℕ, (S ⊓ MU.deg W U₁ n)).map (MU.functorEquiv φ).toLinearMap
      = ⨆ n : ℕ, ((S.map (MU.functorEquiv φ).toLinearMap) ⊓ MU.deg W U₂ n) := by
    rw [Submodule.map_iSup]
    exact iSup_congr (fun n => map_inf_deg φ S n)
  unfold IsLayerGraded
  rw [← hsup]
  exact (Submodule.map_injective_of_injective (MU.functorEquiv φ).injective).eq_iff

/-- **Bottom-triviality transfers under `M(φ)`** (bottom-layer preservation + injectivity). -/
theorem bottomTrivial_map_iff {U₁ U₂ : AMod W} (φ : AModEquiv W U₁ U₂)
    (S : Submodule ℂ (MU W U₁)) :
    (S.map (MU.functorEquiv φ).toLinearMap) ⊓ MU.deg W U₂ 0 = ⊥
      ↔ S ⊓ MU.deg W U₁ 0 = ⊥ := by
  rw [← map_inf_deg φ S 0]
  constructor
  · intro h
    refine (Submodule.map_injective_of_injective (MU.functorEquiv φ).injective) ?_
    rw [Submodule.map_bot]; exact h
  · intro h; rw [h, Submodule.map_bot]

/-- **The `GoodSub` transfer bijection.** `M(φ)` carries a bottom-trivial graded invariant submodule
of `M(U₁)` to one of `M(U₂)`, and conversely. -/
theorem goodSub_map (F : LUFamily W) (hnat : MUActionNatural F) {U₁ U₂ : AMod W}
    (φ : AModEquiv W U₁ U₂) (S : Submodule ℂ (MU W U₁)) :
    GoodSub F U₁ S ↔ GoodSub F U₂ (S.map (MU.functorEquiv φ).toLinearMap) := by
  rw [GoodSub, GoodSub, isInvSub_map_iff F hnat φ, isLayerGraded_map_iff φ,
    bottomTrivial_map_iff φ]

/-! ## The canonical `J` and `MUJNatural` -/

/-- **The canonical maximal bottom-trivial graded invariant submodule** `J = ⨆ {S | GoodSub}`. -/
noncomputable def Jcanon (F : LUFamily W) (U : AMod W) : Submodule ℂ (MU W U) :=
  sSup {S | GoodSub F U S}

/-! ## The canonical `J` is itself bottom-trivial (NOT deep — layer-gradedness only)

A pleasant, *non-deep* fact: `Jcanon` — the sup of all bottom-trivial layer-graded invariant
submodules — is itself bottom-trivial.  Each `GoodSub` piece `S` is layer-graded with
`S ⊓ deg 0 = ⊥`, so `S` lives in the positive layers `⨆_{n≠0} MU.deg n`; hence so does `Jcanon`,
which is disjoint from `deg 0` because the layers are an internal direct sum (`MU.isInternal_deg`).
This turns the maximal-`J` *existence* into just the *maximality* (graded-simplicity) step. -/

/-- Every `GoodSub` submodule lives in the positive layers `⨆_{n≠0} MU.deg n` (layer-graded +
bottom-trivial). -/
theorem goodSub_le_pos {F : LUFamily W} {U : AMod W} {S : Submodule ℂ (MU W U)}
    (hS : GoodSub F U S) : S ≤ ⨆ (j : ℕ) (_ : j ≠ 0), MU.deg W U j := by
  obtain ⟨_, hgr, hbot⟩ := hS
  rw [hgr]
  refine iSup_le fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · rw [hbot]; exact bot_le
  · exact le_trans inf_le_right (le_iSup₂ (f := fun j _ => MU.deg W U j) n hn)

/-- **`Jcanon` is bottom-trivial** — `Jcanon F U ⊓ MU.deg W U 0 = ⊥`.  The canonical maximal
bottom-trivial graded invariant submodule really meets the bottom in `0` (layer independence). -/
theorem Jcanon_inf_deg0_eq_bot (F : LUFamily W) (U : AMod W) :
    Jcanon F U ⊓ MU.deg W U 0 = ⊥ := by
  have hdisj : Disjoint (MU.deg W U 0) (⨆ (j : ℕ) (_ : j ≠ 0), MU.deg W U j) :=
    iSupIndep_def.mp (MU.isInternal_deg W U).submodule_iSupIndep 0
  refine le_antisymm ?_ bot_le
  have hle : Jcanon F U ≤ ⨆ (j : ℕ) (_ : j ≠ 0), MU.deg W U j := by
    rw [Jcanon, sSup_le_iff]
    exact fun S hS => goodSub_le_pos hS
  calc Jcanon F U ⊓ MU.deg W U 0
      ≤ (⨆ (j : ℕ) (_ : j ≠ 0), MU.deg W U j) ⊓ MU.deg W U 0 := inf_le_inf_right _ hle
    _ = ⊥ := by rw [inf_comm]; exact disjoint_iff.mp hdisj

/-- **`Jcanon` is invariant** under the `𝒱`-action — the sup of invariant submodules is invariant
(the action `mode (YM u) n` is ℂ-linear, so `Jcanon ≤ Jcanon.comap (mode …)`). -/
theorem Jcanon_isInvSub (F : LUFamily W) (U : AMod W) : IsInvSub F U (Jcanon F U) := by
  intro u n x hx
  have hle : Jcanon F U ≤ (Jcanon F U).comap (mode ((F.mudata U).weak.YM u) n) := by
    refine sSup_le fun S hS => ?_
    intro y hy
    rw [Submodule.mem_comap]
    have h1 : (F.mudata U).weak.act u n y ∈ S := hS.1 u n y hy
    rw [WeakModule.act_def] at h1
    exact le_sSup hS h1
  have h2 := hle hx
  rw [Submodule.mem_comap, ← WeakModule.act_def] at h2
  exact h2

/-- **`IsGradedSubmodule ⟹ IsLayerGraded`** — a ℂ-weight-graded submodule of `M(U)` is layer-graded.
The ℂ-grading `⨆_α (P ⊓ weight α)` reindexes to the ℕ-layer grading `⨆_n (P ⊓ MU.deg n)`: at
`α = h + n` the weight space is `cweight (h+n) = MU.deg n`, and at every other `α` it is `⊥`. -/
theorem layerGraded_of_isGraded {U : AMod W} {h : ℂ} {D : MUModuleData W U h}
    {P : WeakModule.Submodule' D.toOrdVModule.toWeakModule}
    (hgr : OrdVModule.IsGradedSubmodule D.toOrdVModule P) :
    IsLayerGraded U P.carrier := by
  unfold IsLayerGraded
  conv_lhs => rw [hgr]
  simp only [MUModuleData.toOrdVModule_weight]
  apply le_antisymm
  · refine iSup_le fun α => ?_
    by_cases hα : ∃ n : ℕ, (h : ℂ) + (n : ℂ) = α
    · obtain ⟨n, rfl⟩ := hα
      rw [D.cweight_cast n]
      exact le_iSup (fun n => P.carrier ⊓ MU.deg W U n) n
    · rw [D.cweight_eq_bot (fun n heq => hα ⟨n, heq⟩), inf_bot_eq]
      exact bot_le
  · refine iSup_le fun n => ?_
    rw [← D.cweight_cast n]
    exact le_iSup (fun α => P.carrier ⊓ D.cweight α) ((h : ℂ) + (n : ℂ))

/-- **DJ Prop 3.5 functoriality — `M(φ)` carries the canonical `J₁` onto `J₂`.** The map is an
order-iso of the poset of bottom-trivial graded invariant submodules (`goodSub_map`), and `map`
commutes with `sSup`, so it carries the sup onto the sup. -/
theorem MUJNatural_of_canonical (F : LUFamily W) (hnat : MUActionNatural F) {U₁ U₂ : AMod W}
    (φ : AModEquiv W U₁ U₂) :
    (Jcanon F U₁).map (MU.functorEquiv φ).toLinearMap = Jcanon F U₂ := by
  have himg : (fun S : Submodule ℂ (MU W U₁) => S.map (MU.functorEquiv φ).toLinearMap) ''
        {S | GoodSub F U₁ S} = {S | GoodSub F U₂ S} := by
    ext T
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact (goodSub_map F hnat φ S).mp hS
    · intro hT
      refine ⟨T.comap (MU.functorEquiv φ).toLinearMap, ?_, ?_⟩
      · rw [goodSub_map F hnat φ,
          Submodule.map_comap_eq_of_surjective (MU.functorEquiv φ).surjective]
        exact hT
      · exact Submodule.map_comap_eq_of_surjective (MU.functorEquiv φ).surjective T
  rw [Jcanon, Jcanon,
    (Submodule.gc_map_comap (MU.functorEquiv φ).toLinearMap).l_sSup, ← sSup_image, himg]

/-! ## `J = Jcanon` — the maximal-`J` identity, proved from `LUMaxData` (discharges `hJcanon`) -/

/-- **The carried maximal `J` IS the canonical `Jcanon`** — for the `LUMaxData` form.  Both
inclusions:
* `J ≤ Jcanon`: `J` is invariant (`act_mem`), layer-graded (`layerGraded_of_isGraded J_graded`), and
  bottom-trivial (`bottom_disjoint`), so `J ∈ GoodSub` and `J ≤ sSup = Jcanon`.
* `Jcanon ≤ J`: the image `mkQ(Jcanon)` is a *weak* submodule of the graded-simple quotient
  `M(U)/J`, hence graded (`quot_submodule_graded`), hence `⊥` or `⊤` (`quot_graded_simple`).  It is
  not `⊤` (else `Jcanon = ⊤`, contradicting `Jcanon ⊓ MU.deg 0 = ⊥` with the realized bottom), so it
  is `⊥`, i.e. `Jcanon ≤ J`.

This discharges the maximal-`J` characterization `hJcanon` from the genuine `LUMaxData` data — the
last `hiso`-side residual. -/
theorem LUMaxData.J_eq_Jcanon (F : LUFamily W) (U : AMod W)
    (L : MUModuleData.LUMaxData (F.mudata U)) :
    L.J.carrier = Jcanon F U := by
  -- `J` is bottom-trivial (bottom = `cweight (hU) = MU.deg 0`).
  have hbotdeg : (F.mudata U).cweight (F.hU U) = MU.deg W U 0 := by
    have := (F.mudata U).cweight_cast 0; simpa using this
  have hJbot : L.J.carrier ⊓ MU.deg W U 0 = ⊥ := by
    have hbd := L.bottom_disjoint
    rwa [MUModuleData.toOrdVModule_weight, hbotdeg] at hbd
  -- `J ∈ GoodSub`, hence `J ≤ Jcanon`.
  have hJgood : GoodSub F U L.J.carrier :=
    ⟨fun u n x hx => L.J.act_mem u n hx, layerGraded_of_isGraded L.J_graded, hJbot⟩
  have hJle : L.J.carrier ≤ Jcanon F U := le_sSup hJgood
  refine le_antisymm hJle ?_
  -- Maximality: `mkQ(Jcanon)` as a weak submodule of the quotient.
  set Q : WeakModule.Submodule'
      (OrdVModule.quotient (F.mudata U).toOrdVModule L.J L.J_graded).toWeakModule :=
    { carrier := (Jcanon F U).map L.J.carrier.mkQ
      act_mem := by
        intro u n y hy
        rw [Submodule.mem_map] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        rw [Submodule.mem_map]
        exact ⟨(F.mudata U).weak.act u n x, Jcanon_isInvSub F U u n x hx,
          (WeakModule.quotient_action_mk _ _ u n x).symm⟩ } with hQdef
  have hgr : OrdVModule.IsGradedSubmodule
      (OrdVModule.quotient (F.mudata U).toOrdVModule L.J L.J_graded) Q :=
    L.quot_submodule_graded Q
  rcases L.quot_graded_simple Q hgr with hbot | htop
  · -- `Q.carrier = ⊥` ⟹ `Jcanon ≤ J`.
    have : (Jcanon F U).map L.J.carrier.mkQ = ⊥ := hbot
    exact (OrdVModule.map_mkQ_eq_bot_iff (F.mudata U).toOrdVModule L.J _).mp this
  · -- `Q.carrier = ⊤` ⟹ `Jcanon = ⊤` ⟹ contradiction.
    exfalso
    have htop' : (Jcanon F U).map L.J.carrier.mkQ = ⊤ := htop
    have hcomap : Submodule.comap L.J.carrier.mkQ ((Jcanon F U).map L.J.carrier.mkQ) = ⊤ := by
      rw [htop']; exact Submodule.comap_top _
    rw [Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.mpr hJle] at hcomap
    -- `hcomap : Jcanon = ⊤`.
    have hdeg : MU.deg W U 0 = ⊥ := by
      have hJc := Jcanon_inf_deg0_eq_bot F U
      rw [hcomap, top_inf_eq] at hJc
      exact hJc
    have hne : MU.deg W U 0 ≠ ⊥ := by
      have := (F.mudata U).bottom_weight_ne_bot
      rwa [MUModuleData.toOrdVModule_weight, hbotdeg] at this
    exact hne hdeg

/-! ## `lumax` from `Jcanon` — `J`/`J_graded`/`bottom_disjoint` as genuine TERMS

Reusing the canonical-`J` machinery, the maximal-`J` datum `LUMaxData` has three of its five fields
supplied as terms: `J := Jcanon` (invariant, `Jcanon_isInvSub`), `J_graded` (`Jcanon` is graded, via
`Jcanon_layerGraded` + the reverse bridge), and `bottom_disjoint` (`Jcanon_inf_deg0_eq_bot`).  Only
the two genuine `L(U)`-simplicity fields — `quot_submodule_graded` (`L₀`-semisimplicity of `M(U)/J`)
and `quot_graded_simple` (generation-from-bottom / maximality) — stay carried (deep DLM content). -/

/-- **Reverse bridge `IsLayerGraded ⟹ IsGradedSubmodule`** — a layer-graded submodule is ℂ-weight
graded (reindex ℕ-layers `MU.deg n` to ℂ-weights `cweight (h+n)`, `⊥` elsewhere). -/
theorem isGradedSubmodule_of_layerGraded {U : AMod W} {h : ℂ} {D : MUModuleData W U h}
    (P : WeakModule.Submodule' D.toOrdVModule.toWeakModule)
    (hlay : IsLayerGraded U P.carrier) :
    OrdVModule.IsGradedSubmodule D.toOrdVModule P := by
  rw [OrdVModule.IsGradedSubmodule]
  simp only [MUModuleData.toOrdVModule_weight]
  conv_lhs => rw [hlay]
  apply le_antisymm
  · refine iSup_le fun n => ?_
    rw [← D.cweight_cast n]
    exact le_iSup (fun α => P.carrier ⊓ D.cweight α) ((h : ℂ) + (n : ℂ))
  · refine iSup_le fun α => ?_
    by_cases hα : ∃ n : ℕ, (h : ℂ) + (n : ℂ) = α
    · obtain ⟨n, rfl⟩ := hα
      rw [D.cweight_cast n]
      exact le_iSup (fun n => P.carrier ⊓ MU.deg W U n) n
    · rw [D.cweight_eq_bot (fun n heq => hα ⟨n, heq⟩), inf_bot_eq]
      exact bot_le

/-- **`Jcanon` is layer-graded** — the sup of layer-graded submodules is layer-graded. -/
theorem Jcanon_layerGraded (F : LUFamily W) (U : AMod W) :
    IsLayerGraded U (Jcanon F U) := by
  refine le_antisymm ?_ (iSup_le fun _ => inf_le_left)
  refine sSup_le fun S hS => ?_
  have hgood : GoodSub F U S := hS
  rw [hgood.2.1]
  refine iSup_le fun n => ?_
  exact le_trans (inf_le_inf_right _ (le_sSup hS))
    (le_iSup (fun n => Jcanon F U ⊓ MU.deg W U n) n)

/-- **`Jcanon` as an invariant submodule** of `M(U)`. -/
noncomputable def JcanonSubmodule' (F : LUFamily W) (U : AMod W) :
    WeakModule.Submodule' (F.mudata U).toOrdVModule.toWeakModule where
  carrier := Jcanon F U
  act_mem := by
    intro u n x hx
    exact Jcanon_isInvSub F U u n x hx

@[simp] theorem JcanonSubmodule'_carrier (F : LUFamily W) (U : AMod W) :
    (JcanonSubmodule' F U).carrier = Jcanon F U := rfl

/-- **`Jcanon` is graded** (`IsGradedSubmodule`) — `Jcanon_layerGraded` + the reverse bridge. -/
theorem Jcanon_isGraded (F : LUFamily W) (U : AMod W) :
    OrdVModule.IsGradedSubmodule (F.mudata U).toOrdVModule (JcanonSubmodule' F U) :=
  isGradedSubmodule_of_layerGraded (JcanonSubmodule' F U) (Jcanon_layerGraded F U)

/-- **`LUMaxData` from `Jcanon`** — the maximal-`J` datum with `J := Jcanon`, `J_graded`, and
`bottom_disjoint` all genuine TERMS; only the two deep `L(U)`-simplicity fields
(`quot_submodule_graded` = `L₀`-semisimplicity, `quot_graded_simple` = generation-from-bottom) are
carried.  Reduces `lumax` from five carried fields to two. -/
noncomputable def lumaxFromJcanon (F : LUFamily W) (U : AMod W)
    (hsub : ∀ Q : WeakModule.Submodule'
        (OrdVModule.quotient (F.mudata U).toOrdVModule (JcanonSubmodule' F U)
          (Jcanon_isGraded F U)).toWeakModule,
      OrdVModule.IsGradedSubmodule
        (OrdVModule.quotient (F.mudata U).toOrdVModule (JcanonSubmodule' F U) (Jcanon_isGraded F U)) Q)
    (hsimple : ∀ Q : WeakModule.Submodule'
        (OrdVModule.quotient (F.mudata U).toOrdVModule (JcanonSubmodule' F U)
          (Jcanon_isGraded F U)).toWeakModule,
      OrdVModule.IsGradedSubmodule
          (OrdVModule.quotient (F.mudata U).toOrdVModule (JcanonSubmodule' F U) (Jcanon_isGraded F U)) Q →
        Q.carrier = ⊥ ∨ Q.carrier = ⊤) :
    MUModuleData.LUMaxData (F.mudata U) where
  J := JcanonSubmodule' F U
  J_graded := Jcanon_isGraded F U
  bottom_disjoint := by
    have hw : (F.mudata U).toOrdVModule.weight (F.hU U) = MU.deg W U 0 := by
      rw [MUModuleData.toOrdVModule_weight]
      have := (F.mudata U).cweight_cast 0; simpa using this
    rw [JcanonSubmodule'_carrier, hw]
    exact Jcanon_inf_deg0_eq_bot F U
  quot_submodule_graded := hsub
  quot_graded_simple := hsimple

/-- **The bridge — `MUJNatural F` when the carried maximal `J` is the canonical one.** If for every
bottom `(F.ludata U).J.carrier = Jcanon F U`, then DJ Prop 3.5 (`MUJNatural F`) holds as a theorem,
via `MUJNatural_of_canonical`. -/
theorem MUJNatural_of_ludata_canonical (F : LUFamily W) (hnat : MUActionNatural F)
    (hJ : ∀ U : AMod W, (F.ludata U).J.carrier = Jcanon F U) :
    MUJNatural F := by
  intro U₁ U₂ φ
  rw [hJ U₁, hJ U₂]
  exact MUJNatural_of_canonical F hnat φ

/-- **`MUActionNatural` for the uniform construction is a term** (via `hact` +
`MUActionNatural_of_levelShift`). -/
theorem BimodGenuineConstructionAUniform.actionNatural
    (G : BimodGenuineConstructionAUniform W)
    (ludata : ∀ U : AMod W,
      MUModuleData.LUData ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U)) :
    MUActionNatural (G.toLUFamily ludata) :=
  MUActionNatural_of_levelShift (G.toLUFamily ludata) G.σ G.hL G.hR (G.hact ludata)

/-- **`MUJNatural` for the uniform construction from `J = Jcanon`.**  Combining the term
`MUActionNatural` (uniform `hact`) with the canonical-`J` functoriality, `MUJNatural` for the
uniform family is a theorem given only that the carried maximal `J` is the canonical one. -/
theorem BimodGenuineConstructionAUniform.mujNatural_of_canonicalJ
    (G : BimodGenuineConstructionAUniform W)
    (ludata : ∀ U : AMod W,
      MUModuleData.LUData ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U))
    (hJcanon : ∀ U : AMod W,
      ((G.toLUFamily ludata).ludata U).J.carrier = Jcanon (G.toLUFamily ludata) U) :
    MUJNatural (G.toLUFamily ludata) :=
  MUJNatural_of_ludata_canonical (G.toLUFamily ludata) (G.actionNatural ludata) hJcanon

end InducedAssignment

/-! ## Main theorem — the faithful bijection with `hiso` FULLY a theorem (modulo `J = Jcanon`) -/

/-- **`phase4_of_dj28_uniform_canonicalJ` — the faithful Zhu 5.3.4 bijection with the functoriality
clause `hiso` FULLY discharged for the uniform Construction-A family, modulo `J = Jcanon`.**

For the genuine uniform Construction-A family both halves of `hiso` are theorems: DJ Prop 3.4
(`MUActionNatural`, via `hact`) and DJ Prop 3.5 (`MUJNatural`, via the canonical-`J` functoriality
of this file).  The single remaining `hiso`-side hypothesis is the **characterization**
`hJcanon : (F.ludata U).J = Jcanon F U` — that the carried maximal `J` *is* the canonical maximal
bottom-trivial graded invariant submodule (the maximal-`J` identity, which the DLM/Dong–Jiang theory
supplies and which `L(U)`'s irreducibility already requires).  The other inputs are the keystone
`NeededSliceMems`, the maximal-`J` datum `ludata` (inside `F`), the generation-from-bottom family
`G'`, and `A`/`hirr`. -/
theorem phase4_of_dj28_uniform_canonicalJ {W : VertexOperatorAlgebra 𝒱}
    (hslice : NeededSliceMems W)
    (A : InducedAssignment W) (hirr : A.RealizeIrreducible)
    (G : InducedAssignment.BimodGenuineConstructionAUniform W)
    (ludata : ∀ U : AMod W,
      MUModuleData.LUData ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U))
    (hJcanon : ∀ U : AMod W,
      ((G.toLUFamily ludata).ludata U).J.carrier
        = InducedAssignment.Jcanon (G.toLUFamily ludata) U)
    (G' : InducedAssignment.GenFromBottomGFamily (G.toLUFamily ludata)) :
    Function.Bijective (forwardMapIrr W) :=
  phase4_of_dj28_uniform hslice A hirr G ludata
    (G.mujNatural_of_canonicalJ ludata hJcanon) G'

/-- **`phase4_of_dj28_uniform_lumax` — the faithful Zhu 5.3.4 bijection with `hiso` FULLY
unconditional for the uniform Construction-A family with a genuine `LUMaxData` maximal-`J` datum.**

The functoriality clause `hiso` is a complete theorem with **no** `hJcanon` hypothesis: DJ Prop
3.4 (`MUActionNatural`, via `hact`) and DJ Prop 3.5 (`MUJNatural`) are both discharged, the latter
because `LUMaxData.J_eq_Jcanon` **proves** `(F.ludata U).J = Jcanon F U` from the genuine
maximal-`J` data `lumax` (bottom-triviality + graded-simplicity).  So `hiso` rests on nothing beyond
the Construction-A datum `G` and the maximal-`J` datum `lumax` themselves.

The remaining bijection inputs are exactly: the keystone `NeededSliceMems`, `A`/`hirr`, the uniform
Construction-A datum `G`, the maximal-`J` datum `lumax` (the genuine DLM/Dong–Jiang deep content
that makes `L(U)` irreducible), and the generation-from-bottom family `G'`. -/
theorem phase4_of_dj28_uniform_lumax {W : VertexOperatorAlgebra 𝒱}
    (hslice : NeededSliceMems W)
    (A : InducedAssignment W) (hirr : A.RealizeIrreducible)
    (G : InducedAssignment.BimodGenuineConstructionAUniform W)
    (lumax : ∀ U : AMod W,
      MUModuleData.LUMaxData ((G.toBimodGenuineConstructionA).toMURepFamily.mudata U))
    (G' : InducedAssignment.GenFromBottomGFamily
      (G.toLUFamily (fun U => (lumax U).toLUData))) :
    Function.Bijective (forwardMapIrr W) := by
  have hJcanon : ∀ U : AMod W,
      ((G.toLUFamily (fun U => (lumax U).toLUData)).ludata U).J.carrier
        = InducedAssignment.Jcanon (G.toLUFamily (fun U => (lumax U).toLUData)) U := by
    intro U
    exact InducedAssignment.LUMaxData.J_eq_Jcanon
      (G.toLUFamily (fun U => (lumax U).toLUData)) U (lumax U)
  exact phase4_of_dj28_uniform_canonicalJ hslice A hirr G (fun U => (lumax U).toLUData) hJcanon G'

end VOA
