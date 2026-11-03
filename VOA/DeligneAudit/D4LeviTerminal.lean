import VOA.DeligneAudit.D4LeviStepRank
import VOA.DeligneAudit.LeviTypeA2CertGradedChain

/-! The finite ordered key filtration reaches the all-m cyclic module. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.LeviKeyFiltration

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

theorem d4_all_weight_finite_and_raw_sum
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) :
    FiniteDimensional ℂ (cycSubG ρ w) ∧
      Module.finrank ℂ (cycSubG ρ w) ≤
        ∑ i : Fin (globalKeyBox m).card,
          keyOrbitLength m (keyEnum m i) *
            Module.finrank ℂ
              (keyLayer ρ w (keyEnum m i) ⧸
                (keyPrefix ρ w m i.val).comap
                  (keyLayer ρ w (keyEnum m i)).subtype) := by
  let n := (globalKeyBox m).card
  let key := keyEnum m
  let F : ℕ → Submodule ℂ V := fun i => keyPrefix ρ w m i
  let S : ℕ → Submodule ℂ V := fun i =>
    if hi : i < n then keyLayer ρ w (key ⟨i, hi⟩) else ⊥
  let L : ℕ → ℕ := fun i =>
    if hi : i < n then keyOrbitLength m (key ⟨i, hi⟩) else 0
  have hS (i : ℕ) (hi : i < n) :
      S i = keyLayer ρ w (key ⟨i, hi⟩) := by
    dsimp [S]
    rw [dif_pos hi]
  have hL (i : ℕ) (hi : i < n) :
      L i = keyOrbitLength m (key ⟨i, hi⟩) := by
    dsimp [L]
    rw [dif_pos hi]
  have hz : F 0 = ⊥ := keyPrefix_zero ρ w m
  have ht : F n = cycSubG ρ w := keyPrefix_top ρ w m h
  have hm : ∀ i < n, F i ≤ F (i + 1) := by
    intro i hi
    exact keyPrefix_mono ρ w m i hi
  have hfd : ∀ i < n, FiniteDimensional ℂ (StepQuot F i) := by
    intro i hi
    exact (keyPrefix_step_rank ρ w m h i hi).1
  have hstep : ∀ i < n,
      Module.finrank ℂ (StepQuot F i) ≤
        L i * Module.finrank ℂ (KeyQuot F S i) := by
    intro i hi
    change Module.finrank ℂ (F (i + 1) ⧸ (F i).comap (F (i + 1)).subtype) ≤
      L i * Module.finrank ℂ (S i ⧸ (F i).comap (S i).subtype)
    rw [hS i hi, hL i hi]
    exact (keyPrefix_step_rank ρ w m h i hi).2
  have hf : FiniteDimensional ℂ (F n) :=
    VOA.DeligneAudit.A3Sector.a2_finite_terminal_of_steps n F hz hm hfd
  rw [ht] at hf
  refine ⟨hf, ?_⟩
  have hb := VOA.DeligneAudit.A3Sector.a2_terminal_finrank_le_sum
    n F S L hz hm hfd hstep
  rw [ht] at hb
  calc
    Module.finrank ℂ (cycSubG ρ w) ≤
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
end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.d4_all_weight_finite_and_raw_sum
