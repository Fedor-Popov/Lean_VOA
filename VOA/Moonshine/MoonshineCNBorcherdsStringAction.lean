import VOA.Moonshine.MoonshineCNBorcherdsStringSum
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Levi stability of U and the negative-cone bracket needed by parabolic induction. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton.BorcherdsData

variable {g : Type*} [LieRing g] [LieAlgebra ℂ g] (D : BorcherdsData g)

theorem genSpace_bracket_mem_of_strings (e x : g) (S : Submodule ℂ g)
    (h : ∀ (j : ℤ), 1 ≤ j → ∀ (k : ℕ), (k : ℤ) < j → ∀ v,
      v ∈ D.weightSpace (borcherdsImaginaryRoot j) →
      ⁅x, (LieModule.toEnd ℂ g g e ^ k) v⁆ ∈ S)
    {u : g} (hu : u ∈ D.genSpace e) : ⁅x, u⁆ ∈ S := by
  have hle : D.genSpace e ≤ S.comap (LieModule.toEnd ℂ g g x) := by
    refine iSup_le fun j => iSup_le fun hj => iSup_le fun k => iSup_le fun hk => ?_
    rintro _ ⟨v, hv, rfl⟩
    exact h j hj k hk v hv
  exact hle hu

theorem genSpace_cartan_stable (e : g) (he : e ∈ D.weightSpace borcherdsRealRoot)
    (ξ : ℂ × ℂ) {u : g} (hu : u ∈ D.genSpace e) :
    ⁅D.cartanMap ξ, u⁆ ∈ D.genSpace e := by
  apply D.genSpace_bracket_mem_of_strings e _ _ (fun j hj k hk v hv => ?_) hu
  rw [D.cartan_action ξ _ _ (D.adReal_pow_mem e he j v hv k)]
  exact Submodule.smul_mem _ _
    (D.generatorString_le_genSpace e j hj k hk ⟨v, hv, rfl⟩)

theorem genSpace_raising_stable (e : g) (he : e ∈ D.weightSpace borcherdsRealRoot)
    {u : g} (hu : u ∈ D.genSpace e) : ⁅e, u⁆ ∈ D.genSpace e := by
  apply D.genSpace_bracket_mem_of_strings e _ _ (fun j hj k hk v hv => ?_) hu
  change (LieModule.toEnd ℂ g g e) ((LieModule.toEnd ℂ g g e ^ k) v) ∈ _
  rw [← Module.End.mul_apply, ← pow_succ']
  by_cases hkj : ((k + 1 : ℕ) : ℤ) < j
  · exact D.generatorString_le_genSpace e j hj (k + 1) hkj ⟨v, hv, rfl⟩
  · have hjk : j = ((k + 1 : ℕ) : ℤ) := by omega
    subst j
    rw [D.adReal_pow_simple_vanishes e he (k + 1) v hv]
    exact Submodule.zero_mem _

theorem genSpace_lowering_stable (e f : g)
    (he : e ∈ D.weightSpace borcherdsRealRoot)
    (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1)
    {u : g} (hu : u ∈ D.genSpace e) : ⁅f, u⁆ ∈ D.genSpace e := by
  apply D.genSpace_bracket_mem_of_strings e _ _ (fun j hj k hk v hv => ?_) hu
  cases k with
  | zero =>
      simp only [pow_zero, Module.End.one_apply]
      rw [D.simple_lowering_vanishes j hj f v hf hv]
      exact Submodule.zero_mem _
  | succ k =>
      rw [D.real_lowering_string e f he hf hef j hj v hv k]
      exact Submodule.smul_mem _ _
        (D.generatorString_le_genSpace e j hj k (by omega) ⟨v, hv, rfl⟩)

/-- A nonzero vector spans either one-dimensional real root space. -/
theorem realRoot_vector_eq_smul (γ : ℤ × ℤ)
    (hγ : γ = borcherdsRealRoot ∨ γ = -borcherdsRealRoot)
    (e : g) (he : e ∈ D.weightSpace γ) (he0 : e ≠ 0)
    (x : g) (hx : x ∈ D.weightSpace γ) : ∃ c : ℂ, x = c • e := by
  have hdim : Module.finrank ℂ (D.weightSpace γ) = 1 := by
    rcases hγ with rfl | rfl
    · exact D.real_dimension.1
    · exact D.real_dimension.2
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (K := ℂ)
    (⟨e, he⟩ : D.weightSpace γ) (fun h => he0 (congrArg Subtype.val h))).mp hdim
      (⟨x, hx⟩ : D.weightSpace γ)
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

/-- Every Levi vector preserves U, for the normalized real pair already supplied by BD3--BD4. -/
theorem genSpace_levi_stable (e f : g)
    (he : e ∈ D.weightSpace borcherdsRealRoot)
    (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1)
    {x u : g} (hx : x ∈ D.leviPart) (hu : u ∈ D.genSpace e) :
    ⁅x, u⁆ ∈ D.genSpace e := by
  have he0 : e ≠ 0 := by intro h; simp [h] at hef
  have hf0 : f ≠ 0 := by intro h; simp [h] at hef
  change x ∈ D.weightSpan borcherdsLeviDegree at hx
  induction hx using Submodule.iSup_induction' with
  | mem γ x hx =>
      induction hx using Submodule.iSup_induction' with
      | mem hγ x hx =>
          rcases hγ with rfl | rfl | rfl
          · rw [← D.cartan_range] at hx
            obtain ⟨ξ, rfl⟩ := hx
            exact D.genSpace_cartan_stable e he ξ hu
          · obtain ⟨c, rfl⟩ := D.realRoot_vector_eq_smul _ (Or.inl rfl) e he he0 x hx
            rw [smul_lie]
            exact Submodule.smul_mem _ _ (D.genSpace_raising_stable e he hu)
          · obtain ⟨c, rfl⟩ := D.realRoot_vector_eq_smul _ (Or.inr rfl) f hf hf0 x hx
            rw [smul_lie]
            exact Submodule.smul_mem _ _ (D.genSpace_lowering_stable e f he hf hef hu)
      | zero => simp
      | add x y _ _ hx hy => simpa only [add_lie] using Submodule.add_mem _ hx hy
  | zero => simp
  | add x y _ _ hx hy => simpa only [add_lie] using Submodule.add_mem _ hx hy

theorem genSpace_negative_bracket_simple (j : ℤ) (_hj : 1 ≤ j) {y v : g}
    (hy : y ∈ D.negativePart) (hv : v ∈ D.weightSpace (borcherdsImaginaryRoot j)) :
    ⁅y, v⁆ ∈ D.parabolicPart := by
  have hv' : v ∈ D.weightSpan (fun γ => γ = borcherdsImaginaryRoot j) :=
    D.weightSpace_le_weightSpan (P := fun γ => γ = borcherdsImaginaryRoot j)
      (γ := borcherdsImaginaryRoot j) rfl hv
  apply D.weightSpan_bracket_mem borcherdsNegativeCone
    (fun γ => γ = borcherdsImaginaryRoot j) (fun γ => ¬ borcherdsPositiveCone γ) (by
    intro α β hα hβ _ _ _
    subst β
    simp only [borcherdsNegativeCone, borcherdsPositiveCone, borcherdsImaginaryRoot,
      Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg] at *
    omega) hy hv'

/-- Jacobi induction moves a negative vector through any number of real raising operators. -/
theorem genSpace_negative_bracket_string (e : g)
    (he : e ∈ D.weightSpace borcherdsRealRoot) (j : ℤ) (hj : 1 ≤ j)
    (v : g) (hv : v ∈ D.weightSpace (borcherdsImaginaryRoot j)) (k : ℕ)
    {y : g} (hy : y ∈ D.negativePart) :
    ⁅y, (LieModule.toEnd ℂ g g e ^ k) v⁆ ∈ D.parabolicPart := by
  have heL : e ∈ D.leviPart := D.weightSpace_le_weightSpan (Or.inr (Or.inl rfl)) he
  induction k generalizing y with
  | zero => simpa using D.genSpace_negative_bracket_simple j hj hy hv
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, LieModule.toEnd_apply_apply, leibniz_lie]
      apply D.parabolicPart.add_mem
      · apply ih
        rw [← lie_skew y e]
        exact D.negativePart.neg_mem (D.levi_normalizes_negative heL hy)
      · exact D.parabolicPart.lie_mem (D.leviPart_le_parabolic heL) (ih hy)

/-- The negative cone brackets U into the opposite parabolic; no freeness is assumed. -/
theorem negative_bracket_genSpace (e : g) (he : e ∈ D.weightSpace borcherdsRealRoot)
    {y u : g} (hy : y ∈ D.negativePart) (hu : u ∈ D.genSpace e) :
    ⁅y, u⁆ ∈ D.parabolicPart :=
  D.genSpace_bracket_mem_of_strings e y D.parabolicPart.toSubmodule
    (fun j hj k _ v hv => D.genSpace_negative_bracket_string e he j hj v hv k hy) hu

end VOA.Moonshine.ConwayNorton.BorcherdsData
