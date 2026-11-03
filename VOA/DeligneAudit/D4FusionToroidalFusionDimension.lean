import VOA.DeligneAudit.D4FusionToroidalFusionRank

/-!
# Total dimension bound for the toroidal fusion associated graded

The cyclic pure-evaluation tensor supplies a finite filtration cutoff.
Rank-nullity then bounds the actual associated graded by its tensor source.
-/

namespace VOA.DeligneAudit.Toroidal.FusionGr

open VOA.DeligneAudit.Toroidal VOA.DeligneAudit.D1TensorG
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

variable (S : DeligneSectorData)
variable (hskew : ∀ a b c, S.f a b c = -S.f b a c)
variable {N : ℕ} (z : Fin N → ℂ)

/-- The actual cyclic fusion associated graded has at most the tensor rank. -/
theorem evalGr_rank_le (hz : Function.Injective z) :
    FiniteDimensional ℂ
      (Gr (d1EvalAction S.f S.jacobi hskew z) (D1TensorG.generator S.c₀)) ∧
    Module.finrank ℂ
      (Gr (d1EvalAction S.f S.jacobi hskew z) (D1TensorG.generator S.c₀)) ≤
        (S.n + 1) ^ N := by
  obtain ⟨B, hB⟩ := exists_evalFbelow_top S hskew z hz
  have h := finrank_gr_le_source (d1EvalAction S.f S.jacobi hskew z)
    (D1TensorG.generator S.c₀) B hB
  exact ⟨h.1, by simpa only [D1TensorG.finrank_space] using h.2⟩

theorem d4_evalGr_rank_le (N : ℕ) :
    FiniteDimensional ℂ
      (Gr (D4Fusion.action N) (D4Fusion.generator N)) ∧
    Module.finrank ℂ (Gr (D4Fusion.action N) (D4Fusion.generator N)) ≤ 29 ^ N := by
  simpa only [D4sector, D4Fusion.action, D4Fusion.generator] using
    (evalGr_rank_le D4sector D1SiteG.D4Check.table_skewC
      (D1TensorG.points N) (D1TensorG.points_injective N))

end

end VOA.DeligneAudit.Toroidal.FusionGr

#print axioms VOA.DeligneAudit.Toroidal.FusionGr.evalGr_rank_le
#print axioms VOA.DeligneAudit.Toroidal.FusionGr.d4_evalGr_rank_le
