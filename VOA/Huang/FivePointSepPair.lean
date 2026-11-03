import VOA.Huang.HuangODEThreeSepPairInduction
import VOA.Huang.FivePointSepMid

/-!
# Geometric bounds for the pair (two-cluster) shape

`pairCoeff_geometric` (irreducible external modules) and `ordinaryPair_geometric`
(ordinary external modules): for `f(𝒴_P(a+i) (𝒴_{XY}(c-j) x y) (𝒴_{ZT}(b-i+j) z t))` the
joint bound `K ρ₁^i ρ₂^j` holds whenever the rows (fixed `j`) grow at most like `ρ₁^i` and
`ρ₂ > 1`, `ρ₁ > 1 + 1/ρ₂` (blow-up chart; the polydisc must avoid `x(1-y) = 1`).
-/

noncomputable section
namespace VOA.Huang.FivePointSep
open VOA VOA.Huang.FusionTop VOA.Huang.HuangODEThree VOA.Huang.HuangODEProduct
open VOA.Huang.UniformConv VOA.Huang.TensorCat VOA.Huang.FusionUnit
open VOA.Huang.FusionProduct CategoryTheory
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

variable {M₀ M₁ M₂ M₃ M₄ MU MV : Type u}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup MU] [Module ℂ MU]
  [AddCommGroup MV] [Module ℂ MV]
variable {A₀ : OrdVModule W M₀} {A₁ : OrdVModule W M₁}
  {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃} {A₄ : OrdVModule W M₄}
  {AU : OrdVModule W MU} {AV : OrdVModule W MV}
variable {P : IntertwiningModes MU MV M₀} {ZT : IntertwiningModes M₂ M₁ MV}
  {XY : IntertwiningModes M₃ M₄ MU}

/-- **Joint geometric bound for the pair shape** (irreducible external modules). -/
theorem pairCoeff_geometric
    (hP : IsIntertwiningOperator AU AV A₀ P)
    (hZT : IsIntertwiningOperator A₂ A₁ AV ZT) (hXY : IsIntertwiningOperator A₃ A₄ AU XY)
    {h₀ h₁ h₂ h₃ h₄ : ℂ} {B₀ B₁ B₂ B₃ B₄ : ℕ}
    (hl₀ : IsLowestWeight A₀ h₀) (hl₁ : IsLowestWeight A₁ h₁)
    (hl₂ : IsLowestWeight A₂ h₂) (hl₃ : IsLowestWeight A₃ h₃) (hl₄ : IsLowestWeight A₄ h₄)
    (hD₀ : DualC1Graded A₀ h₀ B₀) (hC₁ : C1Graded A₁ h₁ B₁) (hC₂ : C1Graded A₂ h₂ B₂)
    (hC₃ : C1Graded A₃ h₃ B₃) (hC₄ : C1Graded A₄ h₄ B₄)
    {α₁ α₂ α₃ α₄ : ℂ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight α₁) (hw₂ : w₂ ∈ A₂.weight α₂)
    (hw₃ : w₃ ∈ A₃.weight α₃) (hw₄ : w₄ ∈ A₄.weight α₄)
    (f : M₀ →ₗ[ℂ] ℂ) (a b c : ℂ) {ρ₁ ρ₂ : ℝ} (hρ₂ : 1 < ρ₂) (hρ : 1 + 1 / ρ₂ < ρ₁)
    (hrow : ProductRowBound (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY f w₁ w₂ w₃ w₄ a b c ρ₁) :
    ∃ K : ℝ, ∀ i j : ℕ,
      ‖productCoeff (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY f w₁ w₂ w₃ w₄
        (a + i) (b - i + j) (c - j)‖ ≤ K * ρ₁ ^ i * ρ₂ ^ j := by
  classical
  by_cases z₁ : A₁.weight α₁ = ⊥
  · have : w₁ = 0 := by rw [z₁] at hw₁; exact (Submodule.mem_bot ℂ).mp hw₁
    subst this
    exact ⟨0, fun i j => by simp [productCoeff]⟩
  by_cases z₂ : A₂.weight α₂ = ⊥
  · have : w₂ = 0 := by rw [z₂] at hw₂; exact (Submodule.mem_bot ℂ).mp hw₂
    subst this
    exact ⟨0, fun i j => by simp [productCoeff]⟩
  by_cases z₃ : A₃.weight α₃ = ⊥
  · have : w₃ = 0 := by rw [z₃] at hw₃; exact (Submodule.mem_bot ℂ).mp hw₃
    subst this
    exact ⟨0, fun i j => by simp [productCoeff]⟩
  by_cases z₄ : A₄.weight α₄ = ⊥
  · have : w₄ = 0 := by rw [z₄] at hw₄; exact (Submodule.mem_bot ℂ).mp hw₄
    subst this
    exact ⟨0, fun i j => by simp [productCoeff]⟩
  set α₀ : ℂ := α₁ + α₂ + α₃ + α₄ - (a + b + c) - 3 with hα₀
  have hvec : ∀ (i j : ℕ), P (a + i) (XY (c - j) w₃ w₄) (ZT (b - i + j) w₂ w₁) ∈
      A₀.weight α₀ := by
    intro i j
    have h := pair_mem_weight hP hZT hXY hw₁ hw₂ hw₃ hw₄ (a + i) (b - i + j) (c - j)
    convert h using 2
    rw [hα₀]; ring
  by_cases z₀ : A₀.weight α₀ = ⊥
  · refine ⟨0, fun i j => ?_⟩
    have h := hvec i j
    rw [z₀] at h
    rw [productCoeff, pair_apply, (Submodule.mem_bot ℂ).mp h]
    simp
  obtain ⟨N₁, rfl⟩ := hl₁ α₁ z₁
  obtain ⟨N₂, rfl⟩ := hl₂ α₂ z₂
  obtain ⟨N₃, rfl⟩ := hl₃ α₃ z₃
  obtain ⟨N₄, rfl⟩ := hl₄ α₄ z₄
  obtain ⟨N₀, hN₀⟩ := hl₀ α₀ z₀
  set C := h₁ + h₂ + h₃ + h₄ - h₀ - 3 with hC
  set s := N₀ + N₁ + N₂ + N₃ + N₄ with hs
  set ν₀ : ℂ := C - 2 * N₀ - a with hν₀
  set μ₀ : ℂ := ν₀ - b with hμ₀
  obtain ⟨K, L, hB⟩ := exists_pairBase (P := P) hZT hXY h₁ h₂ h₃ h₄ ν₀ μ₀
  set Q := normalizedSeries (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY C (ν₀ + K) (μ₀ + L)
    f w₁ w₂ w₃ w₄ N₀ s with hQ
  have hcoef : ∀ m n : ℕ, c2 Q m n =
      productCoeff (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY f w₁ w₂ w₃ w₄ (a - K + m)
        (b + K - m + (((n : ℤ) - L : ℤ) : ℂ)) (c - (((n : ℤ) - L : ℤ) : ℂ)) := by
    intro m n
    rw [hQ, c2_normalizedSeries]
    unfold normalizedCoeff
    congr 1
    · rw [hν₀]; ring
    · rw [hν₀, hμ₀]; push_cast; ring
    · have e : (α₀ : ℂ) = h₀ + N₀ := hN₀
      rw [hα₀] at e
      rw [hμ₀, hν₀, hs, hC]; push_cast
      linear_combination e
  obtain ⟨sdeg, g, hs1, hgb, heq⟩ := innerRegular_pairSeries hP hZT hXY hl₀ hl₁ hl₂
    hl₃ hl₄ hB hD₀ hC₁ hC₂ hC₃ hC₄ f hw₁ hw₂ hw₃ hw₄ 0
  obtain ⟨R₁, R₂, hR, hR₁ρ, hR₂ρ⟩ := exists_midAdm_below hρ₂ hρ
  obtain ⟨G, hG⟩ := hgb R₁ R₂ hR
  have hR₁0 : 0 < R₁ := lt_trans zero_lt_one hR.one_lt₁
  have hR₂0 : 0 < R₂ := lt_trans zero_lt_one hR.1
  have hg' : ∀ k < sdeg, ∀ i j, ‖g k i j‖ ≤ max G 0 * R₁ ^ i * R₂ ^ j := by
    intro k hk i j
    refine le_trans (hG k hk i j) ?_
    have : 0 ≤ R₁ ^ i * R₂ ^ j := by positivity
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) this
  have hrows : ∀ n, ∃ K' : ℝ, ∀ m, ‖c2 Q m n‖ ≤ K' * ρ₁ ^ m := by
    intro n
    obtain ⟨K', hK'⟩ := hrow K ((n : ℤ) - L)
    exact ⟨K', fun m => by rw [hcoef]; exact hK' m⟩
  have heq' : DiagonalFuchsian (fun _ n => (0 : ℂ) + n) sdeg g (c2 Q) := heq
  obtain ⟨K₀, hK₀⟩ := geometric_of_rowFuchsian hs1 hR₁0.le hR₂0.le hR₁ρ hR₂ρ hg' heq' hrows
  refine ⟨K₀ * ρ₁ ^ K * ρ₂ ^ L, fun i j => ?_⟩
  have e := hcoef (i + K) (j + L)
  have e' : productCoeff (pairY₁ (M₀ := M₀)) (pairY₂ P ZT) XY f w₁ w₂ w₃ w₄
      (a + i) (b - i + j) (c - j) = c2 Q (i + K) (j + L) := by
    rw [e]
    congr 1
    · push_cast; ring
    · push_cast; ring
    · push_cast; ring
  rw [e']
  calc ‖c2 Q (i + K) (j + L)‖ ≤ K₀ * ρ₁ ^ (i + K) * ρ₂ ^ (j + L) := hK₀ _ _
    _ = K₀ * ρ₁ ^ K * ρ₂ ^ L * ρ₁ ^ i * ρ₂ ^ j := by rw [pow_add, pow_add]; ring

/-- Rows of all endomorphism-modified pair arrays. Slots: `t ∈ T` (`w₁`), `z ∈ Z` (`w₂`),
`x ∈ X` (`w₃`), `y ∈ Y` (`w₄`). -/
def OrdinaryPairRowBound {X Y Z T O MU MV : Ordinary W}
    (P : IntertwiningOperator MU.isMod MV.isMod O.isMod)
    (ZT : IntertwiningOperator Z.isMod T.isMod MV.isMod)
    (XY : IntertwiningOperator X.isMod Y.isMod MU.isMod) (g : O.carrier →ₗ[ℂ] ℂ)
    (t : T.carrier) (z : Z.carrier) (x : X.carrier) (y : Y.carrier) (a₀ b₀ c₀ : ℂ)
    (ρ₁ : ℝ) : Prop :=
  ∀ (πo : O ⟶ O) (πt : T ⟶ T) (πz : Z ⟶ Z) (πx : X ⟶ X) (πy : Y ⟶ Y),
    ProductRowBound (pairY₁ (M₀ := O.carrier)) (pairY₂ P.val ZT.val) XY.val (g ∘ₗ πo.val)
      (πt.val t) (πz.val z) (πx.val x) (πy.val y) a₀ b₀ c₀ ρ₁

/-- **Joint geometric bound for the pair shape among ordinary modules.** -/
theorem ordinaryPair_geometric (hV : StronglyRational W) (hΦ : Finite (Φ W))
    {X Y Z T O MU MV : Ordinary W}
    (P : IntertwiningOperator MU.isMod MV.isMod O.isMod)
    (ZT : IntertwiningOperator Z.isMod T.isMod MV.isMod)
    (XY : IntertwiningOperator X.isMod Y.isMod MU.isMod) (g : O.carrier →ₗ[ℂ] ℂ)
    {αt αz αx αy : ℂ} {t : T.carrier} {z : Z.carrier} {x : X.carrier} {y : Y.carrier}
    (ht : t ∈ T.isMod.weight αt) (hz : z ∈ Z.isMod.weight αz)
    (hx : x ∈ X.isMod.weight αx) (hy : y ∈ Y.isMod.weight αy)
    (a₀ b₀ c₀ : ℂ) {ρ₁ ρ₂ : ℝ} (hρ₂ : 1 < ρ₂) (hρ : 1 + 1 / ρ₂ < ρ₁)
    (hrow : OrdinaryPairRowBound P ZT XY g t z x y a₀ b₀ c₀ ρ₁) :
    ∃ K : ℝ, ∀ i j : ℕ,
      ‖productCoeff (pairY₁ (M₀ := O.carrier)) (pairY₂ P.val ZT.val) XY.val g t z x y
        (a₀ + i) (b₀ - i + j) (c₀ - j)‖ ≤ K * ρ₁ ^ i * ρ₂ ^ j := by
  classical
  obtain ⟨PT⟩ := simplePresentation_nonempty hV hΦ T
  obtain ⟨PZ⟩ := simplePresentation_nonempty hV hΦ Z
  obtain ⟨PX⟩ := simplePresentation_nonempty hV hΦ X
  obtain ⟨PY⟩ := simplePresentation_nonempty hV hΦ Y
  obtain ⟨PO⟩ := simplePresentation_nonempty hV hΦ O
  have hC := moduleC1Data_of_stronglyRational hV
  have hcomp : ∀ j : Fin PO.size × Fin PY.size × Fin PX.size × Fin PZ.size × Fin PT.size,
      ∃ K : ℝ, ∀ i jj : ℕ, ‖g ((PO.proj j.1 ≫ PO.inc j.1).val
        (pairY₁ (M₀ := O.carrier) (a₀ + i) ((PT.proj j.2.2.2.2 ≫ PT.inc j.2.2.2.2).val t)
          (pairY₂ P.val ZT.val (b₀ - i + jj) ((PZ.proj j.2.2.2.1 ≫ PZ.inc j.2.2.2.1).val z)
            (XY.val (c₀ - jj) ((PX.proj j.2.2.1 ≫ PX.inc j.2.2.1).val x)
              ((PY.proj j.2.1 ≫ PY.inc j.2.1).val y)))))‖ ≤ K * ρ₁ ^ i * ρ₂ ^ jj := by
    intro j
    obtain ⟨o, e, γ, β, α⟩ := j
    obtain ⟨B₀, hD₀⟩ := (hC (PO.part o) (PO.irreducible o)).2
    obtain ⟨B₁, hC₁⟩ := (hC (PT.part α) (PT.irreducible α)).1
    obtain ⟨B₂, hC₂⟩ := (hC (PZ.part β) (PZ.irreducible β)).1
    obtain ⟨B₃, hC₃⟩ := (hC (PX.part γ) (PX.irreducible γ)).1
    obtain ⟨B₄, hC₄⟩ := (hC (PY.part e) (PY.irreducible e)).1
    have hP' : IsIntertwiningOperator MU.isMod MV.isMod (PO.part o).isMod
        (fun p => (P.val p).compr₂ (PO.proj o).val) :=
      isIntertwiningOperator_compHom P.property (PO.proj o).property
    have hZT' : IsIntertwiningOperator (PZ.part β).isMod (PT.part α).isMod MV.isMod
        (fun q => ((ZT.val q).comp (PZ.inc β).val).compl₂ (PT.inc α).val) :=
      precomp_right ⟨_, isIntertwiningOperator_precomp ZT.property (PZ.inc β).property⟩
        (PT.inc α)
    have hXY' : IsIntertwiningOperator (PX.part γ).isMod (PY.part e).isMod MU.isMod
        (fun r => ((XY.val r).comp (PX.inc γ).val).compl₂ (PY.inc e).val) :=
      precomp_right ⟨_, isIntertwiningOperator_precomp XY.property (PX.inc γ).property⟩
        (PY.inc e)
    have hrow' := hrow (PO.proj o ≫ PO.inc o) (PT.proj α ≫ PT.inc α) (PZ.proj β ≫ PZ.inc β)
      (PX.proj γ ≫ PX.inc γ) (PY.proj e ≫ PY.inc e)
    exact pairCoeff_geometric hP' hZT' hXY' (PO.part o).isLow (PT.part α).isLow
      (PZ.part β).isLow (PX.part γ).isLow (PY.part e).isLow hD₀ hC₁ hC₂ hC₃ hC₄
      (hom_mem_weight (PT.proj α).property ht) (hom_mem_weight (PZ.proj β).property hz)
      (hom_mem_weight (PX.proj γ).property hx) (hom_mem_weight (PY.proj e).property hy)
      (g ∘ₗ (PO.inc o).val) a₀ b₀ c₀ hρ₂ hρ hrow'
  choose K hK using hcomp
  refine ⟨∑ j, K j, fun i jj => ?_⟩
  rw [productCoeff, prod3_sum_decomp g (pairY₁ (M₀ := O.carrier)) (pairY₂ P.val ZT.val) XY.val
    (fun o => (PO.proj o ≫ PO.inc o).val) (fun α => (PT.proj α ≫ PT.inc α).val)
    (fun β => (PZ.proj β ≫ PZ.inc β).val) (fun γ => (PX.proj γ ≫ PX.inc γ).val)
    (fun e => (PY.proj e ≫ PY.inc e).val) PO.total PT.total PZ.total PX.total PY.total]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ => hK j i jj

end VOA.Huang.FivePointSep
