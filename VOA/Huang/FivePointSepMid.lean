import VOA.Huang.HuangODEThreeSepMidInduction
import VOA.Huang.FivePointSepOrdinary

/-!
# Geometric bounds for the middle (iterate-in-product) shape

`midCoeff_geometric` (irreducible external modules) and `ordinaryMid_geometric`
(ordinary external modules): for `f(𝒴₁(a)_{a₀+i} 𝒴_B(𝒴₃(b)_{c₀-j} c)_{b₀-i+j} e)` the joint
bound `K ρ₁^i ρ₂^j` holds whenever the rows grow at most like `ρ₁^i` and `ρ₁ > 1 + 1/ρ₂`,
`ρ₂ > 1` (the polydisc must avoid the collision divisor `x(1+y) = 1`).
-/

noncomputable section
namespace VOA.Huang.FivePointSep
open VOA VOA.Huang.FusionTop VOA.Huang.HuangODEThree VOA.Huang.HuangODEProduct
open VOA.Huang.UniformConv VOA.Huang.TensorCat VOA.Huang.FusionUnit
open VOA.Huang.FusionProduct CategoryTheory
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- An admissible pair strictly below a target pair. -/
theorem exists_midAdm_below {ρ₁ ρ₂ : ℝ} (h₂ : 1 < ρ₂) (h : 1 + 1 / ρ₂ < ρ₁) :
    ∃ R₁ R₂ : ℝ, MidAdm R₁ R₂ ∧ R₁ < ρ₁ ∧ R₂ < ρ₂ := by
  have hρ₂0 : 0 < ρ₂ := by linarith
  set δ : ℝ := ρ₁ - (1 + 1 / ρ₂) with hδ
  have hδ0 : 0 < δ := by linarith
  have hden : 0 < 1 / ρ₂ + δ / 2 := by positivity
  set R₂ : ℝ := (max 1 (1 / (1 / ρ₂ + δ / 2)) + ρ₂) / 2 with hR₂
  have hlow : 1 / (1 / ρ₂ + δ / 2) < ρ₂ := by
    rw [div_lt_iff₀ hden]
    have : ρ₂ * (1 / ρ₂) = 1 := by field_simp
    nlinarith
  have hmax : max 1 (1 / (1 / ρ₂ + δ / 2)) < ρ₂ := max_lt h₂ hlow
  have hR₂lt : R₂ < ρ₂ := by rw [hR₂]; linarith
  have hR₂gt : max 1 (1 / (1 / ρ₂ + δ / 2)) < R₂ := by rw [hR₂]; linarith
  have hR₂1 : 1 < R₂ := lt_of_le_of_lt (le_max_left _ _) hR₂gt
  have hR₂0 : 0 < R₂ := by linarith
  have hinv : 1 / R₂ < 1 / ρ₂ + δ / 2 := by
    have := lt_of_le_of_lt (le_max_right _ _) hR₂gt
    rw [div_lt_iff₀ hden] at this
    rw [div_lt_iff₀ hR₂0]
    linarith
  refine ⟨ρ₁ - δ / 4, R₂, ⟨hR₂1, by linarith⟩, by linarith, hR₂lt⟩

variable {M₀ M₁ M₂ M₃ M₄ M₅ M₆ : Type u}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup M₅] [Module ℂ M₅]
  [AddCommGroup M₆] [Module ℂ M₆]
variable {A₀ : OrdVModule W M₀} {A₁ : OrdVModule W M₁}
  {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃} {A₄ : OrdVModule W M₄}
  {A₅ : OrdVModule W M₅} {A₆ : OrdVModule W M₆}
variable {Y₁ : IntertwiningModes M₁ M₆ M₀} {YB : IntertwiningModes M₅ M₂ M₆}
  {Y₃ : IntertwiningModes M₃ M₄ M₅}

/-- **Joint geometric bound for the middle shape** (irreducible external modules). -/
theorem midCoeff_geometric
    (hY₁ : IsIntertwiningOperator A₁ A₆ A₀ Y₁)
    (hYB : IsIntertwiningOperator A₅ A₂ A₆ YB)
    (hY₃ : IsIntertwiningOperator A₃ A₄ A₅ Y₃)
    {h₀ h₁ h₂ h₃ h₄ : ℂ} {B₀ B₁ B₂ B₃ B₄ : ℕ}
    (hl₀ : IsLowestWeight A₀ h₀) (hl₁ : IsLowestWeight A₁ h₁)
    (hl₂ : IsLowestWeight A₂ h₂) (hl₃ : IsLowestWeight A₃ h₃) (hl₄ : IsLowestWeight A₄ h₄)
    (hD₀ : DualC1Graded A₀ h₀ B₀) (hC₁ : C1Graded A₁ h₁ B₁) (hC₂ : C1Graded A₂ h₂ B₂)
    (hC₃ : C1Graded A₃ h₃ B₃) (hC₄ : C1Graded A₄ h₄ B₄)
    {α₁ α₂ α₃ α₄ : ℂ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight α₁) (hw₂ : w₂ ∈ A₂.weight α₂)
    (hw₃ : w₃ ∈ A₃.weight α₃) (hw₄ : w₄ ∈ A₄.weight α₄)
    (f : M₀ →ₗ[ℂ] ℂ) (a b c : ℂ) {ρ₁ ρ₂ : ℝ} (hρ₂ : 1 < ρ₂) (hρ : 1 + 1 / ρ₂ < ρ₁)
    (hrow : ProductRowBound Y₁ (swap2 YB) Y₃ f w₁ w₂ w₃ w₄ a b c ρ₁) :
    ∃ K : ℝ, ∀ i j : ℕ,
      ‖productCoeff Y₁ (swap2 YB) Y₃ f w₁ w₂ w₃ w₄ (a + i) (b - i + j) (c - j)‖ ≤
        K * ρ₁ ^ i * ρ₂ ^ j := by
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
  have hvec : ∀ (i j : ℕ), Y₁ (a + i) w₁ (swap2 YB (b - i + j) w₂ (Y₃ (c - j) w₃ w₄)) ∈
      A₀.weight α₀ := by
    intro i j
    have h := mid_mem_weight hY₁ hYB hY₃ hw₁ hw₂ hw₃ hw₄ (a + i) (b - i + j) (c - j)
    convert h using 2
    rw [hα₀]; ring
  by_cases z₀ : A₀.weight α₀ = ⊥
  · refine ⟨0, fun i j => ?_⟩
    have h := hvec i j
    rw [z₀] at h
    rw [productCoeff, (Submodule.mem_bot ℂ).mp h]
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
  obtain ⟨K, L, hB⟩ := exists_midUniformBase hYB hY₃ h₂ h₃ h₄ ν₀ μ₀
  set Q := normalizedSeries Y₁ (swap2 YB) Y₃ C (ν₀ + K) (μ₀ + L) f w₁ w₂ w₃ w₄ N₀ s with hQ
  have hcoef : ∀ m n : ℕ, c2 Q m n =
      productCoeff Y₁ (swap2 YB) Y₃ f w₁ w₂ w₃ w₄ (a - K + m)
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
  obtain ⟨sdeg, g, hs1, hgb, heq⟩ := innerRegularMid_normalizedSeries hY₁ hYB hY₃ hl₀ hl₁ hl₂
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
  have e' : productCoeff Y₁ (swap2 YB) Y₃ f w₁ w₂ w₃ w₄ (a + i) (b - i + j) (c - j) =
      c2 Q (i + K) (j + L) := by
    rw [e]
    congr 1
    · push_cast; ring
    · push_cast; ring
    · push_cast; ring
  rw [e']
  calc ‖c2 Q (i + K) (j + L)‖ ≤ K₀ * ρ₁ ^ (i + K) * ρ₂ ^ (j + L) := hK₀ _ _
    _ = K₀ * ρ₁ ^ K * ρ₂ ^ L * ρ₁ ^ i * ρ₂ ^ j := by rw [pow_add, pow_add]; ring

/-- Rows of all endomorphism-modified middle arrays. -/
def OrdinaryMidRowBound {A B C D O M₅ M₆ : Ordinary W}
    (Y₁ : IntertwiningOperator A.isMod M₆.isMod O.isMod)
    (YB : IntertwiningOperator M₅.isMod B.isMod M₆.isMod)
    (Y₃ : IntertwiningOperator C.isMod D.isMod M₅.isMod) (g : O.carrier →ₗ[ℂ] ℂ)
    (a : A.carrier) (b : B.carrier) (c : C.carrier) (d : D.carrier) (a₀ b₀ c₀ : ℂ)
    (ρ₁ : ℝ) : Prop :=
  ∀ (πo : O ⟶ O) (πa : A ⟶ A) (πb : B ⟶ B) (πc : C ⟶ C) (πd : D ⟶ D),
    ProductRowBound Y₁.val (swap2 YB.val) Y₃.val (g ∘ₗ πo.val) (πa.val a) (πb.val b)
      (πc.val c) (πd.val d) a₀ b₀ c₀ ρ₁

/-- **Joint geometric bound for the middle shape among ordinary modules.** -/
theorem ordinaryMid_geometric (hV : StronglyRational W) (hΦ : Finite (Φ W))
    {A B C D O M₅ M₆ : Ordinary W}
    (Y₁ : IntertwiningOperator A.isMod M₆.isMod O.isMod)
    (YB : IntertwiningOperator M₅.isMod B.isMod M₆.isMod)
    (Y₃ : IntertwiningOperator C.isMod D.isMod M₅.isMod) (g : O.carrier →ₗ[ℂ] ℂ)
    {αa αb αc αd : ℂ} {a : A.carrier} {b : B.carrier} {c : C.carrier} {d : D.carrier}
    (ha : a ∈ A.isMod.weight αa) (hb : b ∈ B.isMod.weight αb)
    (hc : c ∈ C.isMod.weight αc) (hd : d ∈ D.isMod.weight αd)
    (a₀ b₀ c₀ : ℂ) {ρ₁ ρ₂ : ℝ} (hρ₂ : 1 < ρ₂) (hρ : 1 + 1 / ρ₂ < ρ₁)
    (hrow : OrdinaryMidRowBound Y₁ YB Y₃ g a b c d a₀ b₀ c₀ ρ₁) :
    ∃ K : ℝ, ∀ i j : ℕ,
      ‖productCoeff Y₁.val (swap2 YB.val) Y₃.val g a b c d (a₀ + i) (b₀ - i + j) (c₀ - j)‖ ≤
        K * ρ₁ ^ i * ρ₂ ^ j := by
  classical
  obtain ⟨PA⟩ := simplePresentation_nonempty hV hΦ A
  obtain ⟨PB⟩ := simplePresentation_nonempty hV hΦ B
  obtain ⟨PC⟩ := simplePresentation_nonempty hV hΦ C
  obtain ⟨PD⟩ := simplePresentation_nonempty hV hΦ D
  obtain ⟨PO⟩ := simplePresentation_nonempty hV hΦ O
  have hC := moduleC1Data_of_stronglyRational hV
  have hcomp : ∀ j : Fin PO.size × Fin PD.size × Fin PC.size × Fin PB.size × Fin PA.size,
      ∃ K : ℝ, ∀ i jj : ℕ, ‖g ((PO.proj j.1 ≫ PO.inc j.1).val (Y₁.val (a₀ + i)
        ((PA.proj j.2.2.2.2 ≫ PA.inc j.2.2.2.2).val a)
        (swap2 YB.val (b₀ - i + jj) ((PB.proj j.2.2.2.1 ≫ PB.inc j.2.2.2.1).val b)
          (Y₃.val (c₀ - jj) ((PC.proj j.2.2.1 ≫ PC.inc j.2.2.1).val c)
            ((PD.proj j.2.1 ≫ PD.inc j.2.1).val d)))))‖ ≤ K * ρ₁ ^ i * ρ₂ ^ jj := by
    intro j
    obtain ⟨o, e, γ, β, α⟩ := j
    obtain ⟨B₀, hD₀⟩ := (hC (PO.part o) (PO.irreducible o)).2
    obtain ⟨B₁, hC₁⟩ := (hC (PA.part α) (PA.irreducible α)).1
    obtain ⟨B₂, hC₂⟩ := (hC (PB.part β) (PB.irreducible β)).1
    obtain ⟨B₃, hC₃⟩ := (hC (PC.part γ) (PC.irreducible γ)).1
    obtain ⟨B₄, hC₄⟩ := (hC (PD.part e) (PD.irreducible e)).1
    have hY₁ : IsIntertwiningOperator (PA.part α).isMod M₆.isMod (PO.part o).isMod
        (fun p => ((Y₁.val p).comp (PA.inc α).val).compr₂ (PO.proj o).val) :=
      isIntertwiningOperator_compHom (isIntertwiningOperator_precomp Y₁.property
        (PA.inc α).property) (PO.proj o).property
    have hYB : IsIntertwiningOperator M₅.isMod (PB.part β).isMod M₆.isMod
        (fun q => (YB.val q).compl₂ (PB.inc β).val) :=
      precomp_right YB (PB.inc β)
    have hY₃ : IsIntertwiningOperator (PC.part γ).isMod (PD.part e).isMod M₅.isMod
        (fun r => ((Y₃.val r).comp (PC.inc γ).val).compl₂ (PD.inc e).val) :=
      precomp_right ⟨_, isIntertwiningOperator_precomp Y₃.property (PC.inc γ).property⟩
        (PD.inc e)
    have hrow' := hrow (PO.proj o ≫ PO.inc o) (PA.proj α ≫ PA.inc α) (PB.proj β ≫ PB.inc β)
      (PC.proj γ ≫ PC.inc γ) (PD.proj e ≫ PD.inc e)
    exact midCoeff_geometric hY₁ hYB hY₃ (PO.part o).isLow (PA.part α).isLow
      (PB.part β).isLow (PC.part γ).isLow (PD.part e).isLow hD₀ hC₁ hC₂ hC₃ hC₄
      (hom_mem_weight (PA.proj α).property ha) (hom_mem_weight (PB.proj β).property hb)
      (hom_mem_weight (PC.proj γ).property hc) (hom_mem_weight (PD.proj e).property hd)
      (g ∘ₗ (PO.inc o).val) a₀ b₀ c₀ hρ₂ hρ hrow'
  choose K hK using hcomp
  refine ⟨∑ j, K j, fun i jj => ?_⟩
  rw [productCoeff, prod3_sum_decomp g Y₁.val (swap2 YB.val) Y₃.val
    (fun o => (PO.proj o ≫ PO.inc o).val) (fun α => (PA.proj α ≫ PA.inc α).val)
    (fun β => (PB.proj β ≫ PB.inc β).val) (fun γ => (PC.proj γ ≫ PC.inc γ).val)
    (fun e => (PD.proj e ≫ PD.inc e).val) PO.total PA.total PB.total PC.total PD.total]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ => hK j i jj

end VOA.Huang.FivePointSep
