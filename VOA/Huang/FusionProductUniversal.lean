import VOA.Huang.FusionProductSemisimple

/-! # Unique factorization through the semisimple fusion model -/
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
noncomputable section
namespace VOA.Huang.FusionProduct
open VOA VOA.Huang.FusionUnit Module
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂]
  (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂)
  {ι : Type u} [Fintype ι] (R : ι → LWModule W)
  (κ : ι → Type u) [∀ i, Fintype (κ i)]
  (B : ∀ i, Basis (κ i) ℂ (IntertwiningOperator A₁ A₂ (R i).isMod))

/-- Schur separates distinct channels, even when their lowest weights coincide. -/
theorem channel_injective (iR : ∀ i, (R i).IsIrreducibleLW)
    (hne : ∀ i j, LWModule.Iso W (R i) (R j) → i = j) (i : ι) :
    Function.Injective (postcompose (universalIntertwiner A₁ A₂ R κ B) (R i).isMod) := by
  classical
  letI : DecidableEq (Sigma κ) := Classical.decEq _
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  let g (j : ι) (b : κ j) : (R j).carrier →ₗ[ℂ] (R i).carrier :=
    f.val.comp (sumInclusion (fun p : Sigma κ => (R p.1).isMod) ⟨j,b⟩).val
  have hg (j : ι) (b : κ j) : g j b ∈ homSpace (R j).isMod (R i).isMod := by
    intro a n x
    change f.val ((sumInclusion (fun p : Sigma κ => (R p.1).isMod) ⟨j,b⟩).val (mode ((R j).isMod.YM a) n x)) = _
    exact (congrArg f.val ((sumInclusion (fun p : Sigma κ => (R p.1).isMod) ⟨j,b⟩).property a n x)).trans
      (f.property a n _)
  have hoff (j : ι) (hj : j ≠ i) (b : κ j) : g j b = 0 := by
    by_contra h0
    let e := LinearEquiv.ofBijective (g j b) (bijective_of_hom (iR j) (iR i) (hg j b) h0)
    exact hj (hne j i ⟨⟨e, fun a n x => hg j b a n x⟩⟩)
  have hid : (LinearMap.id : (R i).carrier →ₗ[ℂ] (R i).carrier) ≠ 0 := by
    letI := (iR i).1
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : (R i).carrier)
    exact hx (congrArg (fun g : (R i).carrier →ₗ[ℂ] (R i).carrier => g x) h)
  have hc (b : κ i) : ∃ c : ℂ, c • LinearMap.id = g i b :=
    exists_smul_eq_of_hom (iR i) (iR i) (hg i b) (fun _ _ _ => rfl) hid
  choose c hc using hc
  have hsplit (x : Carrier R κ) : f.val x = ∑ j, ∑ b, g j b (x ⟨j,b⟩) := by
    rw [← Fintype.sum_sigma (fun p : Sigma κ => g p.1 p.2 (x p))]
    change f.val x = ∑ p : Sigma κ, f.val (Pi.single p (x p))
    rw [← map_sum]
    congr 1
    funext p
    simp only [Finset.sum_apply, Finset.sum_pi_single, Finset.mem_univ, if_true]
  have heval (x : Carrier R κ) : f.val x = ∑ b, c b • x ⟨i,b⟩ := by
    rw [hsplit, Finset.sum_eq_single i]
    · apply Finset.sum_congr rfl
      intro b _
      rw [← hc b]
      rfl
    · intro j _ hj
      apply Finset.sum_eq_zero
      intro b _
      rw [hoff j hj b]
      rfl
    · simp
  have hrel : ∑ b, c b • B i b = 0 := by
    apply Subtype.ext
    funext n
    ext x y
    have hz := congrArg (fun Z : IntertwiningOperator A₁ A₂ (R i).isMod => Z.val n x y) hf
    dsimp only at hz
    rw [postcompose_apply, heval] at hz
    simpa only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, LinearMap.sum_apply, LinearMap.smul_apply, universalIntertwiner_apply] using hz
  have hc0 := Fintype.linearIndependent_iff.mp (B i).linearIndependent c hrel
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  rw [heval]
  simp [hc0]

/-- Universality for every chosen simple target. -/
theorem universalFor_channel (iR : ∀ i, (R i).IsIrreducibleLW)
    (hne : ∀ i j, LWModule.Iso W (R i) (R j) → i = j) (i : ι) :
    UniversalFor (universalIntertwiner A₁ A₂ R κ B) (R i).isMod :=
  ⟨channel_injective A₁ A₂ R κ B iR hne i, channel_surjective A₁ A₂ R κ B i⟩

end VOA.Huang.FusionProduct
