import VOA.Moonshine.MoonshineCNBorcherdsStringAction

/-! Generation of the positive cone by U, derived from BD5 and the parabolic complement. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

variable {g : Type*} [LieRing g] [LieAlgebra ℂ g]

/-- Generator-level brackets suffice to control a parabolic against a generated subalgebra. -/
theorem lieSpan_parabolic_bracket_mem (S : Submodule ℂ g) (P : LieSubalgebra ℂ g)
    (h : ∀ p ∈ P, ∀ u ∈ S,
      ⁅p, u⁆ ∈ (LieSubalgebra.lieSpan ℂ g (S : Set g)).toSubmodule ⊔ P.toSubmodule)
    {b : g} (hb : b ∈ LieSubalgebra.lieSpan ℂ g (S : Set g)) :
    ∀ p ∈ P, ⁅p, b⁆ ∈ (LieSubalgebra.lieSpan ℂ g (S : Set g)).toSubmodule ⊔ P.toSubmodule := by
  let B := LieSubalgebra.lieSpan ℂ g (S : Set g)
  let T := B.toSubmodule ⊔ P.toSubmodule
  change ∀ p ∈ P, ⁅p, b⁆ ∈ T
  induction hb using LieSubalgebra.lieSpan_induction with
  | mem b hb => exact fun p hp => h p hp b hb
  | zero => simp
  | add b c _ _ hb hc =>
      intro p hp
      simpa only [lie_add] using T.add_mem (hb p hp) (hc p hp)
  | smul a b _ hb =>
      intro p hp
      simpa only [lie_smul] using T.smul_mem a (hb p hp)
  | lie b c hb hc ihb ihc =>
      intro p hp
      rw [leibniz_lie]
      apply T.add_mem
      · obtain ⟨b', hb', p', hp', heq⟩ := Submodule.mem_sup.mp (ihb p hp)
        rw [← heq, add_lie]
        exact T.add_mem (Submodule.mem_sup_left (B.lie_mem hb' hc)) (ihc p' hp')
      · obtain ⟨b', hb', p', hp', heq⟩ := Submodule.mem_sup.mp (ihc p hp)
        rw [← heq, lie_add]
        apply T.add_mem (Submodule.mem_sup_left (B.lie_mem hb hb'))
        rw [← lie_skew b p']
        exact T.neg_mem (ihb p' hp')

/-- The vector-space sum with the parabolic is a Lie subalgebra. -/
def lieSpan_parabolic_sum (S : Submodule ℂ g) (P : LieSubalgebra ℂ g)
    (h : ∀ p ∈ P, ∀ u ∈ S,
      ⁅p, u⁆ ∈ (LieSubalgebra.lieSpan ℂ g (S : Set g)).toSubmodule ⊔ P.toSubmodule) :
    LieSubalgebra ℂ g where
  __ := (LieSubalgebra.lieSpan ℂ g (S : Set g)).toSubmodule ⊔ P.toSubmodule
  lie_mem' := by
    intro x y hx hy
    obtain ⟨b, hb, p, hp, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, hc, q, hq, rfl⟩ := Submodule.mem_sup.mp hy
    simp only [add_lie, lie_add]
    apply Submodule.add_mem
    · apply Submodule.add_mem
      · exact Submodule.mem_sup_left (LieSubalgebra.lie_mem _ hb hc)
      · exact lieSpan_parabolic_bracket_mem S P h hc p hp
    · apply Submodule.add_mem
      · rw [← lie_skew b q]
        exact Submodule.neg_mem _ (lieSpan_parabolic_bracket_mem S P h hb q hq)
      · exact Submodule.mem_sup_right (P.lie_mem hp hq)

namespace BorcherdsData

variable (D : BorcherdsData g)

theorem lieSpan_genSpace_le_positive (e : g) (he : e ∈ D.weightSpace borcherdsRealRoot) :
    LieSubalgebra.lieSpan ℂ g (D.genSpace e : Set g) ≤ D.positivePart :=
  LieSubalgebra.lieSpan_le.mpr (D.genSpace_le_positive e he)

theorem genSpace_parabolic_bracket_mem (e f : g)
    (he : e ∈ D.weightSpace borcherdsRealRoot)
    (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1)
    {p u : g} (hp : p ∈ D.parabolicPart) (hu : u ∈ D.genSpace e) :
    ⁅p, u⁆ ∈ (LieSubalgebra.lieSpan ℂ g (D.genSpace e : Set g)).toSubmodule ⊔
      D.parabolicPart.toSubmodule := by
  change p ∈ D.parabolicPart.toSubmodule at hp
  rw [D.parabolic_eq_levi_sup_negative] at hp
  obtain ⟨l, hl, n, hn, rfl⟩ := Submodule.mem_sup.mp hp
  rw [add_lie]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (LieSubalgebra.subset_lieSpan
      (D.genSpace_levi_stable e f he hf hef hl hu)))
    (Submodule.mem_sup_right (D.negative_bracket_genSpace e he hn hu))

/-- Generation of the positive part: all positive-cone vectors are Lie polynomials in the string
space U. -/
theorem positivePart_eq_lieSpan_genSpace (e f : g)
    (he : e ∈ D.weightSpace borcherdsRealRoot)
    (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1) :
    D.positivePart = LieSubalgebra.lieSpan ℂ g (D.genSpace e : Set g) := by
  let B := LieSubalgebra.lieSpan ℂ g (D.genSpace e : Set g)
  let T := lieSpan_parabolic_sum (D.genSpace e) D.parabolicPart
    (fun _ hp _ hu => D.genSpace_parabolic_bracket_mem e f he hf hef hp hu)
  have hT : T = ⊤ := by
    apply top_unique
    rw [← D.generated]
    apply LieSubalgebra.lieSpan_le.mpr
    intro x hx
    rcases hx with hx | ⟨α, hα, hx⟩
    · exact Submodule.mem_sup_right (D.weightSpace_le_weightSpan
        (by simp [borcherdsPositiveCone] : ¬ borcherdsPositiveCone 0) hx)
    · rcases hα with rfl | ⟨j, hj, rfl⟩
      · rcases hx with hx | hx
        · exact Submodule.mem_sup_right (D.leviPart_le_parabolic
            (D.weightSpace_le_weightSpan (Or.inr (Or.inl rfl)) hx))
        · exact Submodule.mem_sup_right (D.leviPart_le_parabolic
            (D.weightSpace_le_weightSpan (Or.inr (Or.inr rfl)) hx))
      · rcases hx with hx | hx
        · apply Submodule.mem_sup_left
          apply LieSubalgebra.subset_lieSpan
          apply D.generatorString_le_genSpace e j hj 0 (by omega)
          exact ⟨x, hx, by simp⟩
        · apply Submodule.mem_sup_right
          apply D.weightSpace_le_weightSpan (P := fun γ => ¬ borcherdsPositiveCone γ) _ hx
          simp [borcherdsPositiveCone, borcherdsImaginaryRoot]
  have hsup : B.toSubmodule ⊔ D.parabolicPart.toSubmodule = ⊤ :=
    congrArg LieSubalgebra.toSubmodule hT
  apply le_antisymm
  · intro x hx
    have ht : x ∈ B.toSubmodule ⊔ D.parabolicPart.toSubmodule := by rw [hsup]; trivial
    obtain ⟨b, hb, p, hp, hsum⟩ := Submodule.mem_sup.mp ht
    have hpPos : p ∈ D.positivePart := by
      have hpx : p = x - b := by rw [← hsum]; abel
      rw [hpx]
      exact D.positivePart.sub_mem hx (D.lieSpan_genSpace_le_positive e he hb)
    have hp0 : p = 0 := (Submodule.disjoint_def.mp D.positive_parabolic_isCompl.disjoint) p hpPos hp
    simpa [hp0] using hsum ▸ (show b + p ∈ B from by simpa [hp0] using hb)
  · exact D.lieSpan_genSpace_le_positive e he

end BorcherdsData
end VOA.Moonshine.ConwayNorton
