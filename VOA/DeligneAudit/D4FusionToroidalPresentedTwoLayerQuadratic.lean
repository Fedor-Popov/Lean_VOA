import VOA.DeligneAudit.D4FusionToroidalPresentedTwoLayerCollapse
import VOA.DeligneAudit.D4FusionContactTruncationTable

/-! The highest-root u-degree-two tails and a Cartan bracket table. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4FusionContact

noncomputable section

theorem two_h_theta_table (i s : ℕ) (x : PTE 2) :
    (∑ c : Fin 28, D4sector.f (1 : Fin 28) D4sector.c₀ c •
      (ρPTE 2).op c i s x) =
      -(ρPTE 2).op D4sector.c₀ i s x := by
  have ht (c : Fin 28) :
      D4sector.f (1 : Fin 28) D4sector.c₀ c =
        if c = D4sector.c₀ then (-1 : ℂ) else 0 := by
    simpa [negativeCartan, negativeIndex, negativeWeight, D4sector]
      using negative_cartan_table (11 : Fin 12) c
  simp only [ht, ite_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, neg_one_smul]

theorem two_h_theta_comm (i j r s : ℕ) (x : PTE 2)
    (hs : r + s < 2) :
    (ρPTE 2).op (1 : Fin 28) i r
      ((ρPTE 2).op D4sector.c₀ j s x) -
    (ρPTE 2).op D4sector.c₀ j s
      ((ρPTE 2).op (1 : Fin 28) i r x) =
      -(ρPTE 2).op D4sector.c₀ (i + j) (r + s) x := by
  have hc := (ρPTE 2).comm (1 : Fin 28) D4sector.c₀ i j r s x
  rw [if_pos hs] at hc
  calc
    _ = ∑ e : Fin 28, D4sector.f (1 : Fin 28) D4sector.c₀ e •
          (ρPTE 2).op e (i + j) (r + s) x := hc
    _ = _ := two_h_theta_table (i + j) (r + s) x

theorem two_theta_two_zero :
    (ρPTE 2).op D4sector.c₀ 2 0 (pTE 2) = 0 := by
  have ht : [(D4sector.c₀, 4)] ∈ (ravFam D4sector 2 0).tails := by
    right; right; right; left
    refine ⟨D4sector.c₀, ?_, ?_⟩
    · change 16 ≤ (27 : Fin 28).val
      decide
    · decide
  simpa [symbolLetters, wordOpT] using two_syntax_tail [(D4sector.c₀, 4)] ht

theorem two_theta_two_one_zero :
    (ρPTE 2).op D4sector.c₀ 2 1 (pTE 2) = 0 := by
  have hh := two_generator_cartan_mode_one (1 : Fin 28) (by
    change (1 : Fin 28).val < 4
    decide)
  have hcomm := (ρPTE 2).comm (1 : Fin 28) D4sector.c₀
    0 2 1 0 (pTE 2)
  have hsum : (∑ c : Fin 28, D4sector.f (1 : Fin 28) D4sector.c₀ c •
      (ρPTE 2).op c 2 1 (pTE 2)) = 0 := by
    simpa [hh, two_theta_two_zero] using hcomm.symm
  rw [two_h_theta_table] at hsum
  exact neg_eq_zero.mp hsum

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_theta_two_zero
#print axioms VOA.DeligneAudit.Toroidal.two_theta_two_one_zero
#print axioms VOA.DeligneAudit.Toroidal.two_h_theta_table
#print axioms VOA.DeligneAudit.Toroidal.two_h_theta_comm
