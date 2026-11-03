import VOA.DeligneAudit.LeviTypeA3Terminal
import VOA.DeligneAudit.LeviTypeA2CertGradedChain

/-! The finite ordered filtration gives a cyclic finiteness and raw key sum bound. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.LeviKeyFiltration

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

theorem a3_all_weight_finite_and_raw_sum (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c)) :
    FiniteDimensional ℂ (VOA.DeligneAudit.UnivG.cycSubG ρ w) ∧
      Module.finrank ℂ (VOA.DeligneAudit.UnivG.cycSubG ρ w) ≤
        ∑ i : Fin ((a3KeyBox a b c).card),
          a3KeyOrbitLength b c (a3KeyEnum a b c i) *
            Module.finrank ℂ
              (a3KeyLayer ρ w (a3KeyEnum a b c i) ⧸
                (a3KeyPrefix ρ w (a3KeyEnum a b c) i.val).comap
                  (a3KeyLayer ρ w (a3KeyEnum a b c i)).subtype) := by
  let n := (a3KeyBox a b c).card
  let key := a3KeyEnum a b c
  let F : ℕ → Submodule ℂ V := fun i => a3KeyPrefix ρ w key i
  let S : ℕ → Submodule ℂ V := fun i =>
    if hi : i < n then a3KeyLayer ρ w (key ⟨i, hi⟩) else ⊥
  let L : ℕ → ℕ := fun i =>
    if hi : i < n then a3KeyOrbitLength b c (key ⟨i, hi⟩) else 0
  have hS (i : ℕ) (hi : i < n) :
      S i = a3KeyLayer ρ w (key ⟨i, hi⟩) := by
    dsimp [S]
    rw [dif_pos hi]
  have hL (i : ℕ) (hi : i < n) :
      L i = a3KeyOrbitLength b c (key ⟨i, hi⟩) := by
    dsimp [L]
    rw [dif_pos hi]
  have hz : F 0 = ⊥ := a3KeyPrefix_zero ρ w key
  have ht : F n = VOA.DeligneAudit.UnivG.cycSubG ρ w :=
    a3OrderedPrefix_top ρ w a b c h
  have hm : ∀ i < n, F i ≤ F (i + 1) := by
    intro i hi
    exact a3KeyPrefix_mono ρ w hi key
  have hfd : ∀ i < n, FiniteDimensional ℂ (StepQuot F i) := by
    intro i hi
    exact (a3OrderedStep_rank ρ w a b c h i hi).1
  have hstep : ∀ i < n,
      Module.finrank ℂ (StepQuot F i) ≤
        L i * Module.finrank ℂ (KeyQuot F S i) := by
    intro i hi
    change Module.finrank ℂ (F (i + 1) ⧸ (F i).comap (F (i + 1)).subtype) ≤
      L i * Module.finrank ℂ (S i ⧸ (F i).comap (S i).subtype)
    rw [hS i hi, hL i hi]
    exact (a3OrderedStep_rank ρ w a b c h i hi).2
  have hf : FiniteDimensional ℂ (F n) :=
    a2_finite_terminal_of_steps n F hz hm hfd
  rw [ht] at hf
  refine ⟨hf, ?_⟩
  have hb := a2_terminal_finrank_le_sum n F S L hz hm hfd hstep
  rw [ht] at hb
  calc
    Module.finrank ℂ (VOA.DeligneAudit.UnivG.cycSubG ρ w) ≤
        ∑ i ∈ Finset.range n,
          L i * Module.finrank ℂ (KeyQuot F S i) := hb
    _ = _ := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < n := Finset.mem_range.mp hi
      change L i * Module.finrank ℂ
        (S i ⧸ (F i).comap (S i).subtype) = _
      rw [hS i hi', hL i hi']
      simp [hi', n, key, F]

end
end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_all_weight_finite_and_raw_sum
