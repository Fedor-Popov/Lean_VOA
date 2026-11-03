import VOA.DeligneAudit.D4LeviKSPairModuleInterface
import VOA.DeligneAudit.D4LeviKSLemma0Steps

/-! Operator-level conversion of one f₃ mode on a radical word. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The operator represented by a word of radical letters. -/
noncomputable def pairRadicalOp (ρ : CurrentModule D4sector.f V)
    (l : List (Fin 6 × ℕ)) : Module.End ℂ V :=
  (l.map fun p => ρ.op (radicalColour p.1) p.2).prod

theorem pairRadicalOp_apply (ρ : CurrentModule D4sector.f V)
    (l : List (Fin 6 × ℕ)) (v : V) :
    pairRadicalOp ρ l v = radicalWord ρ v l := by
  induction l with
  | nil => simp [pairRadicalOp, radicalWord, wordOp]
  | cons p l ih =>
      rcases p with ⟨j, s⟩
      change ρ.op (radicalColour j) s (pairRadicalOp ρ l v) =
        ρ.op (radicalColour j) s (radicalWord ρ v l)
      rw [ih]

theorem pairRadicalOp_sum_apply (ρ : CurrentModule D4sector.f V)
    (ls : List (List (Fin 6 × ℕ))) (v : V) :
    ((ls.map (pairRadicalOp ρ)).sum) v =
      (ls.map (radicalWord ρ v)).sum := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
      simp only [List.map_cons, List.sum_cons, LinearMap.add_apply,
        pairRadicalOp_apply, ih]

/-- The Θ5 one-mode conversion is an exact operator identity. The minus
    sign is the D4 colour-table sign of both X-to-U' and U-to-Y brackets. -/
theorem fThree_adjoint_radicalOp (ρ : CurrentModule D4sector.f V)
    (r : ℕ) (l : List (Fin 6 × ℕ)) :
    ρ.op (17 : Fin 28) r * pairRadicalOp ρ l -
        pairRadicalOp ρ l * ρ.op (17 : Fin 28) r =
      -((threeWords r l).map (pairRadicalOp ρ)).sum := by
  apply LinearMap.ext
  intro v
  have h := fThree_word ρ r l v
  have hd := fThreeDerivative_eq_sum ρ v r l
  simp only [LinearMap.sub_apply, Module.End.mul_apply,
    pairRadicalOp_apply]
  change (ρ.op (17 : Fin 28) r)
      (wordOp ρ (l.map fun p => (radicalColour p.1, p.2)) v) -
    wordOp ρ (l.map fun p => (radicalColour p.1, p.2))
      (ρ.op (17 : Fin 28) r v) = _
  rw [hd] at h
  rw [h]
  all_goals simp [pairRadicalOp_sum_apply]

theorem fThree_adjoint_X_single (ρ : CurrentModule D4sector.f V)
    (r s : ℕ) :
    pairAdjoint (ρ.op (17 : Fin 28)) [r] (pairRadicalOp ρ [(1, s)]) =
      -pairRadicalOp ρ [(3, r + s)] := by
  simpa [pairAdjoint, threeWords] using
    fThree_adjoint_radicalOp ρ r [(1, s)]

theorem fThree_adjoint_U_single (ρ : CurrentModule D4sector.f V)
    (r s : ℕ) :
    pairAdjoint (ρ.op (17 : Fin 28)) [r] (pairRadicalOp ρ [(2, s)]) =
      -pairRadicalOp ρ [(4, r + s)] := by
  simpa [pairAdjoint, threeWords] using
    fThree_adjoint_radicalOp ρ r [(2, s)]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairRadicalOp_apply
#print axioms VOA.DeligneAudit.D4Levi.pairRadicalOp_sum_apply
#print axioms VOA.DeligneAudit.D4Levi.fThree_adjoint_radicalOp
#print axioms VOA.DeligneAudit.D4Levi.fThree_adjoint_X_single
#print axioms VOA.DeligneAudit.D4Levi.fThree_adjoint_U_single
