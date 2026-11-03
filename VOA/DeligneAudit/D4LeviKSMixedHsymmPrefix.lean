import VOA.DeligneAudit.D4LeviKSMixedColourList

/-! Polynomial forms of the maximal-active Rx and Ry source relations. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.LeviConversion
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem transport_zero (b : ℕ → Module.End ℂ V) :
    transportCurrent b 0 = fCurrent b := by
  ext s
  simp [transportCurrent, fCurrent]

theorem rx_zero_hsymm_prefix
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c s : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hK : 1 ≤ a + b) (hks : m + 1 ≤ c + a + b + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c s) :
    ((yOp ρ 0) ^ b)
      (xyzEvaluation ρ w
        (List.replicate c (5 : Fin 6) ++
          List.replicate (a + b) (1 : Fin 6)).get
        (hsymm (Fin (List.replicate c (5 : Fin 6) ++
          List.replicate (a + b) (1 : Fin 6)).length) ℂ s)) ∈
      keyPrefix ρ w m i := by
  have hr := rx_zero_current_prefix ρ w m i a b c s h hK hks hi hkey
  simp only [transport_zero, List.prod_replicate] at hr
  have he := xyz_hsymm_evaluation_colourList ρ w
    (List.replicate c (5 : Fin 6) ++
      List.replicate (a + b) (1 : Fin 6)) s
  simp only [List.length_append, List.length_replicate,
    List.map_append, List.map_replicate, List.prod_append,
    List.prod_replicate] at he
  simp [xOp, zOp, radicalColour] at he
  rw [he]
  exact hr

theorem ry_zero_hsymm_prefix
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c s : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hK : 1 ≤ b) (hks : m + 1 ≤ c + b + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c s) :
    ((xOp ρ 0) ^ (a + b))
      (xyzEvaluation ρ w
        (List.replicate c (5 : Fin 6) ++
          List.replicate b (4 : Fin 6)).get
        (hsymm (Fin (List.replicate c (5 : Fin 6) ++
          List.replicate b (4 : Fin 6)).length) ℂ s)) ∈
      keyPrefix ρ w m i := by
  have hr := ry_zero_current_prefix ρ w m i a b c s h hK hks hi hkey
  simp only [transport_zero, List.prod_replicate] at hr
  have he := xyz_hsymm_evaluation_colourList ρ w
    (List.replicate c (5 : Fin 6) ++ List.replicate b (4 : Fin 6)) s
  simp only [List.length_append, List.length_replicate,
    List.map_append, List.map_replicate, List.prod_append,
    List.prod_replicate] at he
  simp [yOp, zOp, radicalColour] at he
  rw [he]
  exact hr

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rx_zero_hsymm_prefix
#print axioms VOA.DeligneAudit.D4Levi.ry_zero_hsymm_prefix
