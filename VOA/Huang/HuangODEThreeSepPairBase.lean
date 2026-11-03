import VOA.Huang.HuangODEThreeSepMidBase

/-!
# The pair (two-cluster) shape as a normalized three-slot series

For the pair vertex `(X ⊠ Y) ⊠ (Z ⊠ T)` the coefficient is
`f(𝒴_P(p) (𝒴_{XY}(r) x y) (𝒴_{ZT}(q) z t))`: the root intertwiner has two composite
arguments. It is encoded as a product of three mode families (definitionally),

  `f(pairY₁ p t (pairY₂ q z (𝒴_{XY} r x y)))`,  `pairY₂ q z U = (p ↦ 𝒴_P(p) U ∘ 𝒴_{ZT}(q) z)`,

so the product normalization `normalizedSeries pairY₁ (pairY₂ 𝒴_P 𝒴_{ZT}) 𝒴_{XY}` applies with
product slots `(w₁, w₂, w₃, w₄) = (t, z, x, y)`. Its index pattern `(+m, -m+n, -n)` is the
BLOW-UP chart `m ↔ y = z₃/z₂`, `n ↔ x' = z₀/z₃` (`z₀` the `XY`-separation, `z₃` the
`ZT`-separation, `z₂` the distance between the clusters), with every external level attached
to `z₀`. In the naive chart `(z₀/z₂, z₃/z₂)` no total-level normalization attached to one point
makes all moves regular; in the blow-up chart all five moves are regular.

The encoded `pairY₂` is not an intertwining operator; the strips are controlled by
`PairBase`, which uses the levels of all four vectors (including the terminal `t`).
-/

noncomputable section
namespace VOA.Huang.FivePointSep
open VOA VOA.Huang.FusionTop PowerSeries VOA.Huang.HuangODEThree
open VOA.Huang.HuangODEProduct VOA.Huang.HuangODEModes
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₀ M₁ M₂ M₃ M₄ MU MV : Type u}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup MU] [Module ℂ MU]
  [AddCommGroup MV] [Module ℂ MV]

/-- The evaluation mode family `t, Φ ↦ Φ p t`. -/
def pairY₁ : IntertwiningModes M₁ (ℂ → M₁ →ₗ[ℂ] M₀) M₀ :=
  fun p => LinearMap.mk₂ ℂ (fun t Φ => Φ p t)
    (fun t t' Φ => by simp) (fun a t Φ => by simp) (fun t Φ Φ' => by simp)
    (fun a t Φ => by simp)

/-- The root family: `z, U ↦ (p ↦ 𝒴_P(p) U ∘ 𝒴_{ZT}(q) z)`. -/
def pairY₂ (P : IntertwiningModes MU MV M₀) (ZT : IntertwiningModes M₂ M₁ MV) :
    IntertwiningModes M₂ MU (ℂ → M₁ →ₗ[ℂ] M₀) :=
  fun q => LinearMap.mk₂ ℂ (fun z U => fun p => (P p U).comp (ZT q z))
    (fun z z' U => by funext p; ext t; simp)
    (fun a z U => by funext p; ext t; simp)
    (fun z U U' => by funext p; ext t; simp)
    (fun a z U => by funext p; ext t; simp)

@[simp] theorem pair_apply (P : IntertwiningModes MU MV M₀) (ZT : IntertwiningModes M₂ M₁ MV)
    (XY : IntertwiningModes M₃ M₄ MU) (f : M₀ →ₗ[ℂ] ℂ) (t : M₁) (z : M₂) (x : M₃) (y : M₄)
    (p q r : ℂ) :
    f (pairY₁ p t (pairY₂ P ZT q z (XY r x y))) = f (P p (XY r x y) (ZT q z t)) := rfl

variable {A₀ : OrdVModule W M₀} {A₁ : OrdVModule W M₁}
  {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃} {A₄ : OrdVModule W M₄}
  {AU : OrdVModule W MU} {AV : OrdVModule W MV}
variable {P : IntertwiningModes MU MV M₀} {ZT : IntertwiningModes M₂ M₁ MV}
  {XY : IntertwiningModes M₃ M₄ MU}

theorem pair_mem_weight (hP : IsIntertwiningOperator AU AV A₀ P)
    (hZT : IsIntertwiningOperator A₂ A₁ AV ZT) (hXY : IsIntertwiningOperator A₃ A₄ AU XY)
    {α₁ α₂ α₃ α₄ : ℂ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (h₁ : w₁ ∈ A₁.weight α₁) (h₂ : w₂ ∈ A₂.weight α₂)
    (h₃ : w₃ ∈ A₃.weight α₃) (h₄ : w₄ ∈ A₄.weight α₄) (p q r : ℂ) :
    P p (XY r w₃ w₄) (ZT q w₂ w₁) ∈ A₀.weight (α₁ + α₂ + α₃ + α₄ - p - q - r - 3) := by
  convert mem_weight hP (mem_weight hXY h₃ h₄ r) (mem_weight hZT h₂ h₁ q) p using 1
  congr 1
  ring

/-- Uniform vanishing of both strips for the pair shape (all four levels bounded by `s`). -/
def PairBase (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂) (A₃ : OrdVModule W M₃)
    (A₄ : OrdVModule W M₄) (P : IntertwiningModes MU MV M₀)
    (ZT : IntertwiningModes M₂ M₁ MV) (XY : IntertwiningModes M₃ M₄ MU)
    (h₁ h₂ h₃ h₄ ν μ : ℂ) : Prop :=
  ∀ (N₁ N₂ N₃ N₄ s : ℕ), N₁ + N₂ + N₃ + N₄ ≤ s →
    ∀ (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄),
      w₁ ∈ A₁.weight (h₁ + N₁) → w₂ ∈ A₂.weight (h₂ + N₂) →
      w₃ ∈ A₃.weight (h₃ + N₃) → w₄ ∈ A₄.weight (h₄ + N₄) → ∀ m n : ℤ, m < 0 ∨ n < 0 →
        ∀ p : ℂ, P p (XY (μ + s - n) w₃ w₄) (ZT (ν - μ - m + n) w₂ w₁) = 0

theorem exists_pairBase (hZT : IsIntertwiningOperator A₂ A₁ AV ZT)
    (hXY : IsIntertwiningOperator A₃ A₄ AU XY) (h₁ h₂ h₃ h₄ ν₀ μ₀ : ℂ) :
    ∃ K L : ℕ, PairBase A₁ A₂ A₃ A₄ P ZT XY h₁ h₂ h₃ h₄ (ν₀ + K) (μ₀ + L) := by
  obtain ⟨BU, hBU⟩ := AU.boundedBelow
  obtain ⟨BV, hBV⟩ := AV.boundedBelow
  obtain ⟨L, hL⟩ := exists_nat_gt ((h₃ + h₄ - μ₀ - 1).re - BU)
  obtain ⟨K, hK⟩ := exists_nat_gt ((h₁ + h₂ + h₃ + h₄ - ν₀ - 2).re - BU - BV)
  refine ⟨K, L, ?_⟩
  intro N₁ N₂ N₃ N₄ s hs w₁ w₂ w₃ w₄ hw₁ hw₂ hw₃ hw₄ m n hmn p
  have hs' : (N₁ : ℝ) + N₂ + N₃ + N₄ ≤ s := by exact_mod_cast hs
  have hU := mem_weight hXY hw₃ hw₄ (μ₀ + L + s - n)
  have hV := mem_weight hZT hw₂ hw₁ (ν₀ + K - (μ₀ + L) - m + n)
  by_cases hUz : XY (μ₀ + L + s - n) w₃ w₄ = 0
  · rw [hUz, map_zero, LinearMap.zero_apply]
  by_cases hVz : ZT (ν₀ + K - (μ₀ + L) - m + n) w₂ w₁ = 0
  · rw [hVz, map_zero]
  exfalso
  have hbU := hBU _ (fun hb => hUz (by rw [hb, Submodule.mem_bot] at hU; exact hU))
  have hbV := hBV _ (fun hb => hVz (by rw [hb, Submodule.mem_bot] at hV; exact hV))
  simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re, Complex.intCast_re,
    Complex.one_re] at hbU hbV hK hL
  norm_num at hK
  have hN : (0 : ℝ) ≤ N₁ := Nat.cast_nonneg _
  rcases hmn with hm | hn
  · have hm' : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
    linarith
  · have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    have : (0 : ℝ) ≤ N₂ := Nat.cast_nonneg _
    linarith

theorem pairNC_def (c ν μ : ℂ) (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    (N₀ s : ℕ) (m n : ℂ) :
    normalizedCoeff (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY c ν μ f w₁ w₂ w₃ w₄ N₀ s m n =
      f (P (c - ν - 2 * N₀ + m) (XY (μ + s - n) w₃ w₄) (ZT (ν - μ - m + n) w₂ w₁)) := rfl

/-- Vanishing of the normalized pair coefficient at negative integer offsets. -/
theorem pairNC_neg {h₁ h₂ h₃ h₄ ν μ : ℂ} (hB : PairBase A₁ A₂ A₃ A₄ P ZT XY h₁ h₂ h₃ h₄ ν μ)
    {N₁ N₂ N₃ N₄ s : ℕ} (hs : N₁ + N₂ + N₃ + N₄ ≤ s) {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄))
    (c : ℂ) (f : M₀ →ₗ[ℂ] ℂ) (N₀ : ℕ) :
    ∀ m n : ℤ, m < 0 ∨ n < 0 →
      normalizedCoeff (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY c ν μ f w₁ w₂ w₃ w₄ N₀ s m n = 0 := by
  intro m n hmn
  rw [pairNC_def, hB N₁ N₂ N₃ N₄ s hs w₁ w₂ w₃ w₄ hw₁ hw₂ hw₃ hw₄ m n hmn, map_zero]

/-- Only the selected output weight matters (pair shape). -/
theorem pairSeries_congr_f (hP : IsIntertwiningOperator AU AV A₀ P)
    (hZT : IsIntertwiningOperator A₂ A₁ AV ZT) (hXY : IsIntertwiningOperator A₃ A₄ AU XY)
    {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ} {N₀ N₁ N₂ N₃ N₄ : ℕ}
    {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄))
    {f g : M₀ →ₗ[ℂ] ℂ} (hf : f.domRestrict (A₀.weight (h₀ + N₀)) =
      g.domRestrict (A₀.weight (h₀ + N₀))) :
    normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
      f w₁ w₂ w₃ w₄ N₀ (N₀ + N₁ + N₂ + N₃ + N₄) =
    normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
      g w₁ w₂ w₃ w₄ N₀ (N₀ + N₁ + N₂ + N₃ + N₄) := by
  refine PS2.ext fun m n => ?_
  rw [c2_normalizedSeries, c2_normalizedSeries, pairNC_def, pairNC_def]
  have hw := pair_mem_weight hP hZT hXY hw₁ hw₂ hw₃ hw₄
    (h₁ + h₂ + h₃ + h₄ - h₀ - 3 - ν - 2 * N₀ + m)
    (ν - μ - m + n) (μ + (N₀ + N₁ + N₂ + N₃ + N₄ : ℕ) - n)
  have e : (h₁ + N₁) + (h₂ + N₂) + (h₃ + N₃) + (h₄ + N₄) -
      (h₁ + h₂ + h₃ + h₄ - h₀ - 3 - ν - 2 * N₀ + m) -
      (ν - μ - m + n) - (μ + (N₀ + N₁ + N₂ + N₃ + N₄ : ℕ) - n) - 3 = h₀ + N₀ := by
    push_cast
    ring
  rw [e] at hw
  exact LinearMap.congr_fun hf ⟨_, hw⟩

/-- Finitely many tuples span the pair series at fixed levels. -/
theorem exists_finite_span_pair (hP : IsIntertwiningOperator AU AV A₀ P)
    (hZT : IsIntertwiningOperator A₂ A₁ AV ZT) (hXY : IsIntertwiningOperator A₃ A₄ AU XY)
    (h₀ h₁ h₂ h₃ h₄ ν μ : ℂ) (N₀ N₁ N₂ N₃ N₄ : ℕ) :
    ∃ S : Set PS2, S.Finite ∧
      ∀ (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄),
        w₁ ∈ A₁.weight (h₁ + N₁) → w₂ ∈ A₂.weight (h₂ + N₂) →
        w₃ ∈ A₃.weight (h₃ + N₃) → w₄ ∈ A₄.weight (h₄ + N₄) →
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ w₃ w₄ N₀ (N₀ + N₁ + N₂ + N₃ + N₄) ∈ Submodule.span ℂ S := by
  classical
  haveI := A₀.finrank (h₀ + N₀)
  haveI := A₁.finrank (h₁ + N₁)
  haveI := A₂.finrank (h₂ + N₂)
  haveI := A₃.finrank (h₃ + N₃)
  haveI := A₄.finrank (h₄ + N₄)
  let E₀ := A₀.weight (h₀ + N₀)
  obtain ⟨E', hE'⟩ := Submodule.exists_isCompl E₀
  let π := Submodule.projectionOnto E₀ E' hE'
  let b₀ := Module.finBasis ℂ (Module.Dual ℂ E₀)
  let b₁ := Module.finBasis ℂ (A₁.weight (h₁ + N₁))
  let b₂ := Module.finBasis ℂ (A₂.weight (h₂ + N₂))
  let b₃ := Module.finBasis ℂ (A₃.weight (h₃ + N₃))
  let b₄ := Module.finBasis ℂ (A₄.weight (h₄ + N₄))
  let c := h₁ + h₂ + h₃ + h₄ - h₀ - 3
  let s := N₀ + N₁ + N₂ + N₃ + N₄
  refine ⟨Set.range (fun q : _ × _ × _ × _ × _ =>
    normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY c ν μ ((b₀ q.1).comp π)
      (b₁ q.2.1 : M₁) (b₂ q.2.2.1 : M₂) (b₃ q.2.2.2.1 : M₃) (b₄ q.2.2.2.2 : M₄) N₀ s),
    Set.finite_range _, ?_⟩
  intro f w₁ w₂ w₃ w₄ hw₁ hw₂ hw₃ hw₄
  have hf : f.domRestrict E₀ = ((f.domRestrict E₀).comp π).domRestrict E₀ := by
    ext x
    simp [π, Submodule.projectionOnto_apply_left]
  have he := pairSeries_congr_f hP hZT hXY (ν := ν) (μ := μ) hw₁ hw₂ hw₃ hw₄ hf
  change normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY c ν μ f w₁ w₂ w₃ w₄ N₀ s ∈ _
  rw [he]
  have hψ := b₀.sum_repr (f.domRestrict E₀)
  have hcomp : (f.domRestrict E₀).comp π =
      ∑ a, b₀.repr (f.domRestrict E₀) a • (b₀ a).comp π := by
    ext x
    rw [LinearMap.comp_apply]
    conv_lhs => rw [← hψ]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  change normalizedLinearFunctional (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY c ν μ N₀ s w₁ w₂ w₃ w₄
    ((f.domRestrict E₀).comp π) ∈ _
  rw [hcomp, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  change normalizedLinearFirst (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY c ν μ N₀ s ((b₀ a).comp π)
    w₂ w₃ w₄ w₁ ∈ _
  refine HuangODEProduct.map_mem_span_basis _ _ hw₁ _ fun i => ?_
  change normalizedLinearSecond (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY c ν μ N₀ s ((b₀ a).comp π)
    (b₁ i : M₁) w₃ w₄ w₂ ∈ _
  refine HuangODEProduct.map_mem_span_basis _ _ hw₂ _ fun j => ?_
  change normalizedLinearThird (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY c ν μ N₀ s ((b₀ a).comp π)
    (b₁ i : M₁) (b₂ j : M₂) w₄ w₃ ∈ _
  refine HuangODEProduct.map_mem_span_basis _ _ hw₃ _ fun k => ?_
  change normalizedLinearTerminal (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY c ν μ N₀ s
    ((b₀ a).comp π) (b₁ i : M₁) (b₂ j : M₂) (b₃ k : M₃) w₄ ∈ _
  refine HuangODEProduct.map_mem_span_basis _ _ hw₄ _ fun l => ?_
  exact Submodule.subset_span ⟨(a, i, j, k, l), rfl⟩

theorem exists_finite_span_pair_box (hP : IsIntertwiningOperator AU AV A₀ P)
    (hZT : IsIntertwiningOperator A₂ A₁ AV ZT) (hXY : IsIntertwiningOperator A₃ A₄ AU XY)
    (h₀ h₁ h₂ h₃ h₄ ν μ : ℂ) (B₀ B₁ B₂ B₃ B₄ : ℕ) :
    ∃ S : Set PS2, S.Finite ∧
      ∀ (N₀ N₁ N₂ N₃ N₄ : ℕ), N₀ ≤ B₀ → N₁ ≤ B₁ → N₂ ≤ B₂ → N₃ ≤ B₃ → N₄ ≤ B₄ →
      ∀ (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄),
        w₁ ∈ A₁.weight (h₁ + N₁) → w₂ ∈ A₂.weight (h₂ + N₂) →
        w₃ ∈ A₃.weight (h₃ + N₃) → w₄ ∈ A₄.weight (h₄ + N₄) →
        normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ
          f w₁ w₂ w₃ w₄ N₀ (N₀ + N₁ + N₂ + N₃ + N₄) ∈ Submodule.span ℂ S := by
  classical
  choose S hfin hS using fun q : Fin (B₀ + 1) × Fin (B₁ + 1) × Fin (B₂ + 1) ×
      Fin (B₃ + 1) × Fin (B₄ + 1) =>
    exists_finite_span_pair hP hZT hXY h₀ h₁ h₂ h₃ h₄ ν μ
      q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
  refine ⟨⋃ q, S q, Set.finite_iUnion hfin, ?_⟩
  intro N₀ N₁ N₂ N₃ N₄ b₀ b₁ b₂ b₃ b₄ f w₁ w₂ w₃ w₄ hw₁ hw₂ hw₃ hw₄
  let q : Fin (B₀ + 1) × Fin (B₁ + 1) × Fin (B₂ + 1) × Fin (B₃ + 1) × Fin (B₄ + 1) :=
    (⟨N₀, by omega⟩, ⟨N₁, by omega⟩, ⟨N₂, by omega⟩, ⟨N₃, by omega⟩, ⟨N₄, by omega⟩)
  exact Submodule.span_mono (Set.subset_iUnion S q) (hS q f w₁ w₂ w₃ w₄ hw₁ hw₂ hw₃ hw₄)

end VOA.Huang.FivePointSep
