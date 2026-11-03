import VOA.DeligneAudit.LeviTypeA2CertGradedChain
import VOA.DeligneAudit.LeviTypeA2Step

/-! The all-weight A₂ rank bound from the completed graded key filtration. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.LeviKeyFiltration VOA.DeligneAudit.LeviTypeA

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V)

private theorem a2KeyEnum_first_le (p q : ℕ)
    (i : Fin ((a2KeyBox p q).card)) :
    (a2KeyEnum p q i).d₁ ≤ p := by
  have hmem := a2KeyEnum_mem p q i
  simp only [a2KeyBox, Finset.mem_biUnion, Finset.mem_image] at hmem
  obtain ⟨a, ha, b, _, d, _, hkey⟩ := hmem
  have heq : a = (a2KeyEnum p q i).d₁ := by
    simpa using congrArg A2RadicalKey.d₁ hkey
  have := Finset.mem_range.mp ha
  omega

/-- Every A₂ local Weyl generator has cyclic rank at most `3^p 3^q`. -/
theorem a2_all_weight_rank (p q : ℕ)
    (h : A2LocalWeylRel ρ w p q) :
    FiniteDimensional ℂ (VOA.DeligneAudit.UnivG.cycSubG ρ w) ∧
      Module.finrank ℂ (VOA.DeligneAudit.UnivG.cycSubG ρ w) ≤
        3 ^ p * 3 ^ q := by
  let n := (a2KeyBox p q).card
  let key := a2KeyEnum p q
  let F : ℕ → Submodule ℂ V := fun i => a2KeyPrefix ρ w key i
  let S : ℕ → Submodule ℂ V := fun i =>
    if hi : i < n then a2KeyLayer ρ w (key ⟨i, hi⟩) else ⊥
  let L : ℕ → ℕ := fun i =>
    if hi : i < n then a2KeyOrbitLength q (key ⟨i, hi⟩) else 0
  let g : ℕ → ℕ := fun i =>
    if hi : i < n then a2EffectiveMultiplicity p q (key ⟨i, hi⟩) else 0
  have hS (i : ℕ) (hi : i < n) :
      S i = a2KeyLayer ρ w (key ⟨i, hi⟩) := by
    dsimp [S]
    rw [dif_pos hi]
  have hL (i : ℕ) (hi : i < n) :
      L i = a2KeyOrbitLength q (key ⟨i, hi⟩) := by
    dsimp [L]
    rw [dif_pos hi]
  have hg (i : ℕ) (hi : i < n) :
      g i = a2EffectiveMultiplicity p q (key ⟨i, hi⟩) := by
    dsimp [g]
    rw [dif_pos hi]
  have hz : F 0 = ⊥ := a2KeyPrefix_zero ρ w key
  have ht : F n = VOA.DeligneAudit.UnivG.cycSubG ρ w :=
    a2OrderedPrefix_top ρ w p q h
  have hm : ∀ i < n, F i ≤ F (i + 1) := by
    intro i hi
    exact a2KeyPrefix_mono ρ w hi key
  have hfd : ∀ i < n, FiniteDimensional ℂ (StepQuot F i) := by
    intro i hi
    exact (a2OrderedStep_rank ρ w p q h i hi).1
  have hstep : ∀ i < n,
      Module.finrank ℂ (StepQuot F i) ≤
        L i * Module.finrank ℂ (KeyQuot F S i) := by
    intro i hi
    change Module.finrank ℂ (F (i + 1) ⧸ (F i).comap (F (i + 1)).subtype) ≤
      L i * Module.finrank ℂ (S i ⧸ (F i).comap (S i).subtype)
    rw [hS i hi, hL i hi]
    exact (a2OrderedStep_rank ρ w p q h i hi).2
  have hKS : ∀ i < n,
      Module.finrank ℂ (KeyQuot F S i) ≤ g i := by
    intro i hi
    have hkey := a2KeyEnum_first_le p q ⟨i, hi⟩
    have hmul := a2_key_quot_finrank_le_effective ρ w p q h
      (key ⟨i, hi⟩) hkey
    have hpref := a2OrderedPrefix_eq_higher ρ w p q h i hi
    rw [← hpref] at hmul
    change Module.finrank ℂ (S i ⧸ (F i).comap (S i).subtype) ≤ g i
    rw [hS i hi, hg i hi]
    exact hmul
  have hcount : (∑ i ∈ Finset.range n, L i * g i) ≤
      a2LeviCount p q := by
    have hc := a2_ordered_key_count p q
    rw [Finset.sum_fin_eq_sum_range] at hc
    convert hc using 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    simp [L, g, n, key, hi']
  have hfinite : FiniteDimensional ℂ (F n) :=
    a2_finite_terminal_of_steps n F hz hm hfd
  rw [ht] at hfinite
  refine ⟨hfinite, ?_⟩
  have hbound := a2_terminal_finrank_le_sum n F S L hz hm hfd hstep
  rw [ht] at hbound
  calc
    Module.finrank ℂ (VOA.DeligneAudit.UnivG.cycSubG ρ w) ≤
        ∑ i ∈ Finset.range n,
          L i * Module.finrank ℂ (KeyQuot F S i) := hbound
    _ ≤ ∑ i ∈ Finset.range n, L i * g i := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul_left _ (hKS i (Finset.mem_range.mp hi))
    _ ≤ a2LeviCount p q := hcount
    _ = 3 ^ p * 3 ^ q := a2LeviCount_eq p q

end
end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_all_weight_rank
