import VOA.DeligneAudit.D4LeviEmbedding

/-! Restriction of a D4 current module to its signed matrix-unit sl4 Levi. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.SectorWeyl

theorem levi_bracket_outside (x y : Fin 15) (z : Fin 28)
    (hz : z ∉ Set.range leviColour) :
    VOA.DeligneAudit.DeligneSector.D4.fD4 (leviColour x) (leviColour y) z = 0 := by
  have hcheck := levi_support_check x y
  simp only [List.all_eq_true, decide_eq_true_eq] at hcheck
  have hzero : sget
      (VOA.DeligneAudit.DeligneSector.D4.br (leviColour x) (leviColour y)) z = 0 := by
    by_contra hn
    obtain ⟨p, hp, hpc⟩ := exists_of_sget_ne_zero hn
    obtain ⟨i, hi⟩ := hcheck p hp
    exact hz ⟨i, Fin.ext (hi.trans hpc)⟩
  simp [VOA.DeligneAudit.DeligneSector.D4.fD4, fC, fZ, hzero]

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule VOA.DeligneAudit.DeligneSector.D4.fD4 V)

theorem levi_sum (x y : Fin 15) (r s : ℕ) (v : V) :
    ∑ z : Fin 28,
      ((leviSign x : ℂ) * (leviSign y : ℂ) *
        VOA.DeligneAudit.DeligneSector.D4.fD4 (leviColour x) (leviColour y) z) •
        ρ.op z (r + s) v =
      ∑ z : Fin 15,
        (VOA.DeligneAudit.A3Sector.bracketTable x y z * (leviSign z : ℂ)) •
          ρ.op (leviColour z) (r + s) v := by
  let F : Fin 28 → V := fun z =>
    ((leviSign x : ℂ) * (leviSign y : ℂ) *
      VOA.DeligneAudit.DeligneSector.D4.fD4 (leviColour x) (leviColour y) z) •
      ρ.op z (r + s) v
  have hsub : ∑ z ∈ Finset.univ.image leviColour, F z = ∑ z, F z := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro z _ hz
    have hnot : z ∉ Set.range leviColour := by simpa using hz
    simp [F, levi_bracket_outside x y z hnot]
  rw [← hsub]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro z _
    simp only [F]
    rw [levi_bracket_compat]
    rw [mul_comm (leviSign z : ℂ)]
  · intro z _ z' _ heq
    exact leviColour_injective heq

/-- The signed restriction of any D4 current module is an sl4 current module. -/
def leviCurrent : CurrentModule VOA.DeligneAudit.A3Sector.bracketTable V where
  op x r := (leviSign x : ℂ) • ρ.op (leviColour x) r
  comm x y r s v := by
    have h := ρ.comm (leviColour x) (leviColour y) r s v
    have hs := congrArg
      (fun u : V => ((leviSign x : ℂ) * (leviSign y : ℂ)) • u) h
    simp only [smul_sub, Finset.smul_sum, smul_smul, map_smul,
      LinearMap.smul_apply] at hs ⊢
    calc
      _ = ((leviSign x : ℂ) * (leviSign y : ℂ)) •
          (ρ.op (leviColour x) r (ρ.op (leviColour y) s v) -
            ρ.op (leviColour y) s (ρ.op (leviColour x) r v)) := by
              simp [smul_sub, smul_smul, mul_comm]
      _ = ∑ z : Fin 28,
          ((leviSign x : ℂ) * (leviSign y : ℂ) *
            VOA.DeligneAudit.DeligneSector.D4.fD4
              (leviColour x) (leviColour y) z) • ρ.op z (r + s) v := by
              rw [smul_sub]
              exact hs
      _ = ∑ z : Fin 15,
          (VOA.DeligneAudit.A3Sector.bracketTable x y z * (leviSign z : ℂ)) •
            ρ.op (leviColour z) (r + s) v := levi_sum ρ x y r s v
      _ = _ := by simp only [smul_smul]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.levi_bracket_outside
#print axioms VOA.DeligneAudit.D4Levi.levi_sum
#print axioms VOA.DeligneAudit.D4Levi.leviCurrent
