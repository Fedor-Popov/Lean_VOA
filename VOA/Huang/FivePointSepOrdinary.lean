import VOA.Huang.FivePointSepRight

/-!
# Products of three intertwiners among arbitrary ordinary modules

`ordinaryProduct_geometric`: the generic form of the right-tree argument. For intertwining
operators among ORDINARY (possibly reducible) modules of a strongly rational VOA, the
coefficient array of a product of three intertwiners satisfies a joint geometric bound
`K ρ₁^i ρ₂^j` (any `ρ₂ > 1`), provided the rows of every endomorphism-modified array grow at
most like `ρ₁^i`. Finite simple presentations reduce to irreducible external modules, where
`productCoeff_geometric` applies. Used for the right tree and (after skew-symmetry at the
root) for the inner tree.
-/

noncomputable section
namespace VOA.Huang.FivePointSep
open VOA VOA.Huang.FusionTop VOA.Huang.HuangODEThree VOA.Huang.HuangODEProduct
open VOA.Huang.TensorCat VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Rows of all endomorphism-modified arrays of a product of three intertwiners. -/
def OrdinaryRowBound {A B C D O M₅ M₆ : Ordinary W}
    (Y₁ : IntertwiningOperator A.isMod M₆.isMod O.isMod)
    (Y₂ : IntertwiningOperator B.isMod M₅.isMod M₆.isMod)
    (Y₃ : IntertwiningOperator C.isMod D.isMod M₅.isMod) (g : O.carrier →ₗ[ℂ] ℂ)
    (a : A.carrier) (b : B.carrier) (c : C.carrier) (d : D.carrier) (a₀ b₀ c₀ : ℂ)
    (ρ₁ : ℝ) : Prop :=
  ∀ (πo : O ⟶ O) (πa : A ⟶ A) (πb : B ⟶ B) (πc : C ⟶ C) (πd : D ⟶ D),
    ProductRowBound Y₁.val Y₂.val Y₃.val (g ∘ₗ πo.val) (πa.val a) (πb.val b) (πc.val c)
      (πd.val d) a₀ b₀ c₀ ρ₁

/-- **Joint geometric bound for products of three intertwiners among ordinary modules.** -/
theorem ordinaryProduct_geometric (hV : StronglyRational W) (hΦ : Finite (Φ W))
    {A B C D O M₅ M₆ : Ordinary W}
    (Y₁ : IntertwiningOperator A.isMod M₆.isMod O.isMod)
    (Y₂ : IntertwiningOperator B.isMod M₅.isMod M₆.isMod)
    (Y₃ : IntertwiningOperator C.isMod D.isMod M₅.isMod) (g : O.carrier →ₗ[ℂ] ℂ)
    {αa αb αc αd : ℂ} {a : A.carrier} {b : B.carrier} {c : C.carrier} {d : D.carrier}
    (ha : a ∈ A.isMod.weight αa) (hb : b ∈ B.isMod.weight αb)
    (hc : c ∈ C.isMod.weight αc) (hd : d ∈ D.isMod.weight αd)
    (a₀ b₀ c₀ : ℂ) {ρ₁ ρ₂ : ℝ} (hρ₁ : 1 < ρ₁) (hρ₂ : 1 < ρ₂)
    (hrow : OrdinaryRowBound Y₁ Y₂ Y₃ g a b c d a₀ b₀ c₀ ρ₁) :
    ∃ K : ℝ, ∀ i j : ℕ,
      ‖productCoeff Y₁.val Y₂.val Y₃.val g a b c d (a₀ + i) (b₀ - i + j) (c₀ - j)‖ ≤
        K * ρ₁ ^ i * ρ₂ ^ j := by
  classical
  obtain ⟨PA⟩ := simplePresentation_nonempty hV hΦ A
  obtain ⟨PB⟩ := simplePresentation_nonempty hV hΦ B
  obtain ⟨PC⟩ := simplePresentation_nonempty hV hΦ C
  obtain ⟨PD⟩ := simplePresentation_nonempty hV hΦ D
  obtain ⟨PO⟩ := simplePresentation_nonempty hV hΦ O
  have hC := moduleC1Data_of_stronglyRational hV
  -- the bound for one component
  have hcomp : ∀ j : Fin PO.size × Fin PD.size × Fin PC.size × Fin PB.size × Fin PA.size,
      ∃ K : ℝ, ∀ i jj : ℕ, ‖g ((PO.proj j.1 ≫ PO.inc j.1).val (Y₁.val (a₀ + i)
        ((PA.proj j.2.2.2.2 ≫ PA.inc j.2.2.2.2).val a)
        (Y₂.val (b₀ - i + jj) ((PB.proj j.2.2.2.1 ≫ PB.inc j.2.2.2.1).val b)
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
    have hY₂ : IsIntertwiningOperator (PB.part β).isMod M₅.isMod M₆.isMod
        (fun q => (Y₂.val q).comp (PB.inc β).val) :=
      isIntertwiningOperator_precomp Y₂.property (PB.inc β).property
    have hY₃ : IsIntertwiningOperator (PC.part γ).isMod (PD.part e).isMod M₅.isMod
        (fun r => ((Y₃.val r).comp (PC.inc γ).val).compl₂ (PD.inc e).val) :=
      precomp_right ⟨_, isIntertwiningOperator_precomp Y₃.property (PC.inc γ).property⟩
        (PD.inc e)
    have hrow' := hrow (PO.proj o ≫ PO.inc o) (PA.proj α ≫ PA.inc α) (PB.proj β ≫ PB.inc β)
      (PC.proj γ ≫ PC.inc γ) (PD.proj e ≫ PD.inc e)
    exact productCoeff_geometric hY₁ hY₂ hY₃ (PO.part o).isLow (PA.part α).isLow
      (PB.part β).isLow (PC.part γ).isLow (PD.part e).isLow hD₀ hC₁ hC₂ hC₃ hC₄
      (hom_mem_weight (PA.proj α).property ha) (hom_mem_weight (PB.proj β).property hb)
      (hom_mem_weight (PC.proj γ).property hc) (hom_mem_weight (PD.proj e).property hd)
      (g ∘ₗ (PO.inc o).val) a₀ b₀ c₀ hρ₁ hρ₂ hrow'
  choose K hK using hcomp
  refine ⟨∑ j, K j, fun i jj => ?_⟩
  rw [productCoeff, prod3_sum_decomp g Y₁.val Y₂.val Y₃.val
    (fun o => (PO.proj o ≫ PO.inc o).val) (fun α => (PA.proj α ≫ PA.inc α).val)
    (fun β => (PB.proj β ≫ PB.inc β).val) (fun γ => (PC.proj γ ≫ PC.inc γ).val)
    (fun e => (PD.proj e ≫ PD.inc e).val) PO.total PA.total PB.total PC.total PD.total]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ => hK j i jj

end VOA.Huang.FivePointSep
