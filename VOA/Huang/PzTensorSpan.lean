/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.PzTensorAction
import VOA.Huang.AssocJacobiBoundary
import VOA.Huang.LogRemovalWeak

/-!
# The span of the coefficient functions as a weak-module candidate

For fixed irreducible modules and intertwining operators `𝒴₁, 𝒴₂` of a strongly rational `V`,
let `Λ = coefSpan 𝒴₁ 𝒴₂` be the span of all coefficient functions `B_{n,k}(f, w₃)` of the
products `⟨f, 𝒴₁(w₁, z₁) 𝒴₂(w₂, z₂) w₃⟩` at the iterate point.  This file equips `Λ` with the
Huang–Lepowsky `P(1)`-action `τ` (`PzTensorAction`) and proves every weak-module axiom **except
the two Jacobi boundary families**:

* `tauHom_mem_coefSpan` — `Λ` is `τ`-stable (from the coproduct identity
  `AssocTauStable.coefFun_coproduct_holds`);
* `YMS` — the linear field map `𝒱 → (End Λ)⟦z^±⟧` (homogeneous decomposition of the state),
  `YMS_vacuum` (`Y(𝟙, z) = id`), `YMS_truncated` (lower truncation, from
  `AssocTauStable.coproduct_lower_truncation`), `YMS_L0` (`L(0) = L'(0) = L0T`).

The remaining content is isolated in two named, TRUE propositions:

* `TauCommutator P₁ P₂` — the commutator formula for `τ` on **all** bilinear functions
  (Huang–Lepowsky–Zhang IV, Prop. 5.9: `Y'_{P(z)}` satisfies the commutator formula on the whole
  of `(W₁ ⊗ W₂)*`).  It involves only `P₁` and `P₂`.
* `TauAssociator W` — the associator formula for `τ` on `Λ` (HLZ IV, Thm. 5.44: the Jacobi
  identity holds on every element satisfying the `P(z)`-compatibility condition; the coefficient
  functionals satisfy it — its two parts are `coproduct_lower_truncation` and the left associator
  identity `AssocAssociator.prodValueZ_assoc_left`).

`coeffWeakInput_of_tau : StronglyRational W → (∀ irreducible P₁ P₂, TauCommutator P₁ P₂) →
TauAssociator W → CoeffWeakInput W`.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.PzTensorSpan

open VOA VOA.Huang.MatrixCoeff VOA.Huang.FusionTop VOA.Huang.AssocTarget
open VOA.Huang.LogRemovalSemisimple VOA.Huang.AssocTauStable VOA.Huang.PzTensorBilin
open VOA.Huang.PzTensorAction VOA.Huang.AssocJacobiBoundary VOA.Huang.LogRemovalWeak
open VOA.Huang.LogRemovalAdmissible
open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## The transposed coproduct with any truncation bound -/

theorem copT_eq_sum {P₁ P₂ : LWModule W} {G : HomPair P₁ P₂ → ℂ} (hG : G ∈ bilin P₁ P₂)
    {γ : ℤ} {a : 𝒱} (ha : a ∈ W.grading γ) (p : ℤ) (x : HomPair P₁ P₂) {N : ℕ}
    (hN : ∀ r : ℕ, N ≤ r → mode (P₁.isMod.YM a) r x.w₁ = 0) :
    copT ha p G x
      = G (pairRight x ha p) + ∑ r ∈ Finset.range N, cbz p r * G (pairLeft x ha r) := by
  have hB : IsBilin G := hG
  unfold copT
  congr 1
  set L := PzTensorAction.lowBound P₁.h x.α₁ γ
  have hL : ∀ r : ℕ, L ≤ r → G (pairLeft x ha r) = 0 := fun r hr =>
    hB.zero_left _ (mode_eq_zero_of_lowBound P₁.isLow x.h₁ ha hr)
  have hN' : ∀ r : ℕ, N ≤ r → G (pairLeft x ha r) = 0 := fun r hr => hB.zero_left _ (hN r hr)
  rw [Finset.sum_subset (Finset.range_subset_range.2 (le_max_left L N)) (fun r _ hr => by
      rw [Finset.mem_range, not_lt] at hr; rw [hL r hr, mul_zero]),
    Finset.sum_subset (Finset.range_subset_range.2 (le_max_right L N)) (fun r _ hr => by
      rw [Finset.mem_range, not_lt] at hr; rw [hN' r hr, mul_zero])]

/-! ## The span of the coefficient functions -/

section Span

variable {P₁ P₂ P₃ P₄ Q : LWModule W}

/-- The coefficient functions of the products of `𝒴₁, 𝒴₂` (all outside data, all intermediate
weights, all log indices). -/
def coefSet (Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier)
    (Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier) : Set (HomPair P₁ P₂ → ℂ) :=
  {G | ∃ (f : P₄.carrier →ₗ[ℂ] ℂ) (w₃ : P₃.carrier) (α₃ h₄ n : ℂ) (k : ℕ),
    w₃ ∈ P₃.isMod.weight α₃ ∧ SupportedAt P₄.isMod f h₄ ∧ G = coefFun Y₁ Y₂ f w₃ α₃ h₄ n k}

/-- **`Λ`**: the span of the coefficient functions. -/
noncomputable def coefSpan (Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier)
    (Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier) : Submodule ℂ (HomPair P₁ P₂ → ℂ) :=
  Submodule.span ℂ (coefSet Y₁ Y₂)

theorem coefFun_mem_coefSpan (Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier)
    (Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier) {f : P₄.carrier →ₗ[ℂ] ℂ}
    {w₃ : P₃.carrier} {α₃ h₄ : ℂ} (h₃ : w₃ ∈ P₃.isMod.weight α₃)
    (hf : SupportedAt P₄.isMod f h₄) (n : ℂ) (k : ℕ) :
    coefFun Y₁ Y₂ f w₃ α₃ h₄ n k ∈ coefSpan Y₁ Y₂ :=
  Submodule.subset_span ⟨f, w₃, α₃, h₄, n, k, h₃, hf, rfl⟩

variable (hV : StronglyRational W)
  (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
  (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
  {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
  {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
  (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
  (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)

include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂

theorem coefSpan_le_bilin : coefSpan Y₁ Y₂ ≤ bilin P₁ P₂ := by
  refine Submodule.span_le.2 ?_
  rintro G ⟨f, w₃, α₃, h₄, n, k, h₃, hf, rfl⟩
  exact coefFun_mem_bilin hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf n k

/-- The transposed coproduct maps a coefficient function into `Λ`. -/
theorem copT_coefFun_mem {f : P₄.carrier →ₗ[ℂ] ℂ} {w₃ : P₃.carrier} {α₃ h₄ : ℂ}
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄) (n : ℂ) (k : ℕ)
    {γ : ℤ} {a : 𝒱} (ha : a ∈ W.grading γ) (p : ℤ) :
    copT ha p (coefFun Y₁ Y₂ f w₃ α₃ h₄ n k) ∈ coefSpan Y₁ Y₂ := by
  obtain ⟨NA, hNA⟩ := exists_comp_mode_vanish P₄.isLow hf ha p
  obtain ⟨N₃, hN₃⟩ := exists_nat_truncation P₃.isMod a w₃
  have hw : ∀ i : ℕ, mode (P₃.isMod.YM a) i w₃ ∈ P₃.isMod.weight (α₃ + γ - i - 1) := by
    intro i
    have := VOA.mode_mem_weight P₃.isMod ha h₃ i
    simpa using this
  have key : copT ha p (coefFun Y₁ Y₂ f w₃ α₃ h₄ n k)
      = (∑ i ∈ Finset.range NA, (negOnePow i * cbz p i) •
          coefFun Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM a) (p - i)) w₃ α₃ (h₄ - γ + (p - i : ℤ) + 1)
            (n - γ + p + 1) k)
        - negOnePow p • ∑ i ∈ Finset.range N₃, (negOnePow i * cbz p i) •
          coefFun Y₁ Y₂ f (mode (P₃.isMod.YM a) i w₃) (α₃ + γ - i - 1) h₄ (n - γ + p + 1) k := by
    funext x
    have hco := coefFun_coproduct_holds hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf ha p x hNA
      (N₁ := PzTensorAction.lowBound P₁.h x.α₁ γ)
      (fun r hr => mode_eq_zero_of_lowBound P₁.isLow x.h₁ ha hr) hN₃ n k
    simp only [copT, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hco]
  rw [key]
  refine Submodule.sub_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
    (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_))
  · exact coefFun_mem_coefSpan Y₁ Y₂ h₃ (supportedAt_comp_mode hf ha (p - i)) _ k
  · exact coefFun_mem_coefSpan Y₁ Y₂ (hw i) hf _ k

/-- **`Λ` is stable under the `P(1)`-action.** -/
theorem tauHom_mem_coefSpan {G : HomPair P₁ P₂ → ℂ} (hG : G ∈ coefSpan Y₁ Y₂) {β : ℤ}
    {u : 𝒱} (hu : u ∈ W.grading β) (m : ℤ) : tauHom hu m G ∈ coefSpan Y₁ Y₂ := by
  induction hG using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, w₃, α₃, h₄, n, k, h₃, hf, rfl⟩ := hG
    have key : tauHom hu m (coefFun Y₁ Y₂ f w₃ α₃ h₄ n k)
        = (-1 : ℂ) ^ β • ∑ j ∈ Finset.range (β.toNat + 1), ((j.factorial : ℂ)⁻¹) •
          copT (VOA.VertexOperatorAlgebra.L_one_pow_mem W hu j) (twIdx β m j)
            (coefFun Y₁ Y₂ f w₃ α₃ h₄ n k) := by
      funext x
      simp only [tauHom, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [key]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (copT_coefFun_mem hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf n k _ _))
  | zero => rw [← tauLin_apply, map_zero]; exact Submodule.zero_mem _
  | add G G' _ _ ih ih' => rw [← tauLin_apply, map_add]; exact Submodule.add_mem _ ih ih'
  | smul c G _ ih => rw [← tauLin_apply, map_smul]; exact Submodule.smul_mem _ c ih

/-- **Lower truncation of `τ` on `Λ`** (homogeneous states). -/
theorem tauHom_truncation {G : HomPair P₁ P₂ → ℂ} (hG : G ∈ coefSpan Y₁ Y₂) {β : ℤ}
    {u : 𝒱} (hu : u ∈ W.grading β) : ∃ N : ℤ, ∀ m : ℤ, N ≤ m → tauHom hu m G = 0 := by
  induction hG using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, w₃, α₃, h₄, n, k, h₃, hf, rfl⟩ := hG
    have hB := coefFun_mem_bilin hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf n k
    choose P hP using fun j : ℕ => coproduct_lower_truncation hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf
      (VOA.VertexOperatorAlgebra.L_one_pow_mem W hu j) n k
    set S : ℤ := ∑ j ∈ Finset.range (β.toNat + 1), |P j|
    refine ⟨2 * β + S, fun m hm => ?_⟩
    funext x
    simp only [tauHom, Pi.zero_apply]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun j hj => ?_)
    have hle : |P j| ≤ S := Finset.single_le_sum (f := fun j => |P j|)
      (fun j _ => abs_nonneg _) hj
    have hp : twIdx β m j ≤ P j := by
      unfold twIdx
      have := neg_abs_le (P j)
      omega
    obtain ⟨N₁, hN₁, hz⟩ := hP j (twIdx β m j) hp x
    rw [copT_eq_sum hB _ _ x hN₁, hz, mul_zero]
  | zero => exact ⟨0, fun m _ => by rw [← tauLin_apply, map_zero]⟩
  | add G G' _ _ ih ih' =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨N', hN'⟩ := ih'
    exact ⟨max N N', fun m hm => by
      rw [← tauLin_apply, map_add, tauLin_apply, tauLin_apply, hN m (le_of_max_le_left hm),
        hN' m (le_of_max_le_right hm), add_zero]⟩
  | smul c G _ ih =>
    obtain ⟨N, hN⟩ := ih
    exact ⟨N, fun m hm => by rw [← tauLin_apply, map_smul, tauLin_apply, hN m hm, smul_zero]⟩

/-! ## The field map on `Λ` -/

/-- `τ(·, n)` on homogeneous states of weight `β`, as a linear map into `End Λ`. -/
noncomputable def tauFam (n : ℤ) (β : ℤ) : W.grading β →ₗ[ℂ] End ℂ (coefSpan Y₁ Y₂) where
  toFun a := (tauLin a.2 n).restrict
    (fun G hG => tauHom_mem_coefSpan hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hG a.2 n)
  map_add' a b := by
    ext G : 1
    apply Subtype.ext
    simp only [LinearMap.restrict_apply, LinearMap.add_apply, Submodule.coe_add, tauLin_apply]
    exact tauHom_add_u (coefSpan_le_bilin hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ G.2) a.2 b.2 n
  map_smul' c a := by
    ext G : 1
    apply Subtype.ext
    simp only [LinearMap.restrict_apply, LinearMap.smul_apply, Submodule.coe_smul, tauLin_apply,
      RingHom.id_apply]
    exact tauHom_smul_u (coefSpan_le_bilin hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ G.2) c a.2 n

/-- `τ(·, n)` on all states (homogeneous decomposition). -/
noncomputable def tauAt (n : ℤ) : 𝒱 →ₗ[ℂ] End ℂ (coefSpan Y₁ Y₂) :=
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  (DFinsupp.lsum ℂ (tauFam hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ n)).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap

theorem tauAt_homogeneous (n : ℤ) {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β)
    (G : coefSpan Y₁ Y₂) :
    ((tauAt hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ n u G : coefSpan Y₁ Y₂) : HomPair P₁ P₂ → ℂ)
      = tauHom hu n (G : HomPair P₁ P₂ → ℂ) := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hcollapse : tauAt hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ n u
      = tauFam hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ n β ⟨u, hu⟩ := by
    change (DFinsupp.lsum ℂ (tauFam hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ n))
      (DirectSum.decompose W.grading u) = _
    rw [DirectSum.decompose_of_mem W.grading hu]
    exact DFinsupp.lsum_single ℂ (tauFam hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ n) β ⟨u, hu⟩
  rw [hcollapse]
  rfl

/-- **The field map** `Y_Λ : 𝒱 → (End Λ)⟦z^±⟧`, `Y_Λ(u, z) = Σ_n τ(u, n) z^{−n−1}`. -/
noncomputable def YMS : 𝒱 →ₗ[ℂ] (End ℂ (coefSpan Y₁ Y₂))⟦z^±⟧ where
  toFun u := fun p => tauAt hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ (-p - 1) u
  map_add' u₁ u₂ := by
    funext p
    show tauAt hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ (-p - 1) (u₁ + u₂) = _
    rw [map_add]; rfl
  map_smul' c u := by
    funext p
    change tauAt hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ (-p - 1) (c • u) = _
    rw [map_smul]; rfl

theorem YMS_apply (u : 𝒱) (p : ℤ) :
    YMS hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ u p = tauAt hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ (-p - 1) u := by
  simp only [YMS, LinearMap.coe_mk, AddHom.coe_mk]

theorem mode_YMS (u : 𝒱) (n : ℤ) :
    mode (YMS hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ u) n = tauAt hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ n u := by
  rw [mode_apply, YMS_apply, show -(-n - 1) - 1 = n by ring]

theorem mode_YMS_coe {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) (n : ℤ) (G : coefSpan Y₁ Y₂) :
    ((mode (YMS hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ u) n G : coefSpan Y₁ Y₂) : HomPair P₁ P₂ → ℂ)
      = tauHom hu n (G : HomPair P₁ P₂ → ℂ) := by
  rw [mode_YMS, tauAt_homogeneous hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ n hu G]

/-- **Vacuum**: `Y_Λ(𝟙, z) = id`. -/
theorem YMS_vacuum : YMS hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ W.vacuum = 1 := by
  refine FormalDist.ext fun p => ?_
  ext G : 1
  apply Subtype.ext
  have h := mode_YMS_coe hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ W.vacuum_mem_grading_zero (-p - 1) G
  rw [mode_apply, show -(-p - 1) - 1 = p by ring] at h
  rw [h, tauHom_vacuum (coefSpan_le_bilin hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ G.2), FormalDist.one_apply]
  by_cases hp : p = 0
  · subst hp; simp
  · rw [if_neg (by omega), if_neg hp]; rfl

/-- **Lower truncation** of `Y_Λ`. -/
theorem YMS_truncated : Truncated (YMS hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂) := by
  intro u G
  have hutop : u ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun u => ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      mode (YMS hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ u) n G = 0) hutop ?_ ?_ ?_
  · intro β x hx
    obtain ⟨N, hN⟩ := tauHom_truncation hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ G.2 hx
    refine ⟨N, fun n hn => Subtype.ext ?_⟩
    rw [mode_YMS_coe hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hx n G, hN n hn]
    rfl
  · exact ⟨0, fun n _ => by rw [map_zero, mode_zero, LinearMap.zero_apply]⟩
  · rintro x y ⟨Nx, hx⟩ ⟨Ny, hy⟩
    refine ⟨max Nx Ny, fun n hn => ?_⟩
    rw [map_add, mode_add, LinearMap.add_apply, hx n (le_trans (le_max_left _ _) hn),
      hy n (le_trans (le_max_right _ _) hn), add_zero]

/-- **`L(0) = L'(0)`** on `Λ`. -/
theorem YMS_L0 (G : coefSpan Y₁ Y₂) :
    ((mode (YMS hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ W.conformalVector) 1 G : coefSpan Y₁ Y₂) :
      HomPair P₁ P₂ → ℂ) = L0T P₁ P₂ (G : HomPair P₁ P₂ → ℂ) := by
  rw [mode_YMS_coe hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ W.conformalVector_mem_grading_two 1 G,
    tauHom_conformal_one (coefSpan_le_bilin hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ G.2)]

end Span

/-! ## The two remaining named inputs -/

/-- **The commutator formula for the `P(1)`-action on all bilinear functions** (named; TRUE:
Huang–Lepowsky–Zhang, *Logarithmic tensor category theory IV*, Prop. 5.9 — `Y'_{P(z)}` satisfies
the commutator formula on the whole of `(W₁ ⊗ W₂)*`; here `z = 1` in the homogeneous-pair
presentation).  Pure algebra in `P₁`, `P₂`: the `P₂`-part is the contragredient commutator
(`Modules.ContragredientClose.dualAdjResidualMvec_holds`, `ℓ = 0`), the `P₁`-part its translate. -/
def TauCommutator (P₁ P₂ : LWModule W) : Prop :=
  ∀ (β γ : ℤ) (u v : 𝒱) (hu : u ∈ W.grading β) (hv : v ∈ W.grading γ) (m n : ℤ)
    (G : HomPair P₁ P₂ → ℂ), G ∈ bilin P₁ P₂ →
    tauHom hu m (tauHom hv n G) - tauHom hv n (tauHom hu m G)
      = ∑ᶠ i : ℤ, cbz m i • tauHom (W.smul_mem_grading hu hv i) (m + n - i) G

/-- **The associator formula for the `P(1)`-action on the span of the coefficient functions**
(named; TRUE: HLZ IV, Thm. 5.44 — the Jacobi identity for `Y'_{P(z)}` holds on every element
satisfying the `P(z)`-compatibility condition; the coefficient functionals satisfy it: lower
truncation is `AssocTauStable.coproduct_lower_truncation`, the compatibility identity is the left
associator `AssocAssociator.prodValueZ_assoc_left`; equivalently a consequence of Huang's
associativity theorem). -/
def TauAssociator (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ Q : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW →
    P₃.IsIrreducibleLW → P₄.IsIrreducibleLW → Q.IsIrreducibleLW →
  ∀ (Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier)
    (Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier),
    IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁ →
    IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂ →
  ∀ (β γ : ℤ) (u v : 𝒱) (hu : u ∈ W.grading β) (hv : v ∈ W.grading γ) (ell n : ℤ)
    (G : HomPair P₁ P₂ → ℂ), G ∈ coefSpan Y₁ Y₂ →
    (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
        (tauHom hu (ell - i) (tauHom hv (n + i) G)
          - negOnePow ell • tauHom hv (ell + n - i) (tauHom hu i G)))
      = tauHom (W.smul_mem_grading hu hv ell) n G

/-! ## Assembly: the weak module on `Λ` from the two named inputs -/

theorem coe_finsum_sub {X : Type*} [AddCommGroup X] [Module ℂ X] {S : Submodule ℂ X} {ι : Type*}
    (f : ι → S) (h : (Function.support f).Finite) :
    ((∑ᶠ i, f i : S) : X) = ∑ᶠ i, (f i : X) := by
  have := map_finsum S.subtype h
  simpa using this

section Assembly

variable {P₁ P₂ P₃ P₄ Q : LWModule W}
  (hV : StronglyRational W)
  (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
  (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
  {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
  {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
  (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
  (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)

include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂

/-- The commutator boundary of `Y_Λ` from `TauCommutator`. -/
theorem YMS_commutator (hC : TauCommutator P₁ P₂) :
    CommutatorBoundary W (YMS hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂) := by
  intro u v G m n
  refine borcherdsAt_of_homogeneous (YMS_truncated hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂) G 0 m n
    (fun β γ u v hu hv => ?_) u v
  apply Subtype.ext
  rw [BL_ell_zero, BR, coe_finsum_sub _ (BR_fin u v G 0 m n)]
  simp only [Submodule.coe_sub, Submodule.coe_smul, zero_add]
  rw [mode_YMS_coe hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hu, mode_YMS_coe hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hv,
    mode_YMS_coe hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hv, mode_YMS_coe hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hu,
    hC β γ u v hu hv m n G (coefSpan_le_bilin hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ G.2)]
  exact finsum_congr fun i => by
    rw [mode_YMS_coe hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ (W.smul_mem_grading hu hv i)]

/-- The associator boundary of `Y_Λ` from `TauAssociator`. -/
theorem YMS_associator (hA : TauAssociator W) :
    AssociatorBoundary W (YMS hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂) := by
  have htr := YMS_truncated hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂
  intro u v G ell n
  refine borcherdsAt_of_homogeneous htr G ell 0 n (fun β γ u v hu hv => ?_) u v
  apply Subtype.ext
  rw [BR_m_zero, mode_YMS_coe hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ (W.smul_mem_grading hu hv ell),
    ← hA P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂ β γ u v hu hv ell n G G.2,
    BL_as_finsum htr]
  have hfin : (Function.support fun i : ℤ => (negOnePow i * cbz ell i) •
      (mode (YMS hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ u) (ell + 0 - i)
          (mode (YMS hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ v) (n + i) G)
        - negOnePow ell • mode (YMS hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ v) (ell + n - i)
          (mode (YMS hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ u) (0 + i) G))).Finite := by
    refine ((Puv_fin htr u v G ell 0 n).union (Pvu_fin htr u v G ell 0 n)).subset ?_
    intro i hi
    by_contra hc
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc hi
    apply hi
    rw [smul_sub, hc.1, smul_comm, hc.2, smul_zero, sub_zero]
  rw [coe_finsum_sub _ hfin]
  refine finsum_congr fun i => ?_
  simp only [Submodule.coe_sub, Submodule.coe_smul, zero_add,
    add_zero]
  rw [mode_YMS_coe hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hu, mode_YMS_coe hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hv,
    mode_YMS_coe hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hv, mode_YMS_coe hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hu]

/-- **The weak module on `Λ`**, from the two named inputs. -/
noncomputable def weakModuleS (hC : TauCommutator P₁ P₂) (hA : TauAssociator W) :
    WeakModule W (coefSpan Y₁ Y₂) :=
  ofBoundaries (YMS hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂) (YMS_vacuum hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂)
    (YMS_truncated hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂) (YMS_commutator hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hC)
    (YMS_associator hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hA)

end Assembly

/-- **`CoeffWeakInput` from the two named `P(1)`-action inputs** (strongly rational `V`). -/
theorem coeffWeakInput_of_tau (hV : StronglyRational W)
    (hC : ∀ P₁ P₂ : LWModule W, P₁.IsIrreducibleLW → P₂.IsIrreducibleLW → TauCommutator P₁ P₂)
    (hA : TauAssociator W) : CoeffWeakInput W := by
  intro P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂ α₃ h₄ w₃ f h₃ hf n
  refine ⟨coefSpan Y₁ Y₂,
    weakModuleS hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ (hC P₁ P₂ i₁ i₂) hA, fun G => ?_,
    coefFun_mem_coefSpan Y₁ Y₂ h₃ hf n 0⟩
  exact YMS_L0 hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ G

/-- **`AssociativityInput` from the named inputs** (combining with
`LogRemovalWeak.associativityInput_of_weakInput`). -/
theorem associativityInput_of_tau (hV : StronglyRational W) (hABD : ABDWeakIsAdmissible W)
    (hC : ∀ P₁ P₂ : LWModule W, P₁.IsIrreducibleLW → P₂.IsIrreducibleLW → TauCommutator P₁ P₂)
    (hA : TauAssociator W) (hZ : AssocCoeffIdentityZero W) : AssociativityInput W :=
  associativityInput_of_weakInput hV hABD (coeffWeakInput_of_tau hV hC hA) hZ

end VOA.Huang.PzTensorSpan
