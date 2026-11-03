import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticProductVanishing
import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRulePowerCutoff

/-! The literal quadratic/cubic polar ideal is contained in the original
power-at-most-three source ideal, by explicit zero-current source words. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

def polarLowerWord (a b c : ℕ) : List (Fin 18 × ℕ) :=
  List.replicate c (9,0) ++ List.replicate b (8,0) ++ List.replicate a (7,0)

theorem polarLowerWord_branch (a b c : ℕ) :
    ∀ x ∈ polarLowerWord a b c, LeviRules.category x.1 = 1 := by
  intro x hx
  simp only [polarLowerWord,List.mem_append,List.mem_replicate,or_assoc] at hx
  rcases hx with ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide

theorem modelWord_replicate_g0 (m : ℕ) (g : Fin 10) (n : ℕ)
    (p : MvPolynomial (Vars m) ℂ) :
    wordOp (LeviRules.representation ℂ m) (List.replicate n (Fin.castAdd 8 g,0)) p =
      ((g0Deriv m g 0 : _ → _)^[n]) p := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ]
      change LeviRules.deriv ℂ m (Fin.castAdd 8 g) 0
        (wordOp (LeviRules.representation ℂ m) (List.replicate n (Fin.castAdd 8 g,0)) p) = _
      rw [LeviRules.deriv_g0,ih,Function.iterate_succ_apply']

/-- Explicit original source representation at its unchanged power/current cutoff. -/
theorem current_orbit_coeff_mem_powerBounded (m R r a b c s : ℕ)
    (hr : 1 ≤ r) (hR : r ≤ R) (hs : m < r + s) :
    PowerSeries.coeff s (currentMap m (orbit ℂ r a b c)) ∈
      LeviRules.powerBoundedIdeal m R := by
  let j : AllM.SeedIndex m := ⟨(false,r,s),⟨hr,hs⟩⟩
  let i : LeviRules.OrbitSourceIndex m :=
    ⟨j,[],polarLowerWord a b c,by
      simpa only [LeviRules.branchCategory,j,Bool.false_eq_true,if_false] using
        polarLowerWord_branch a b c⟩
  let k : LeviRules.PowerBoundedSourceIndex m R := ⟨i,hR⟩
  have he : PowerSeries.coeff s (currentMap m (orbit ℂ r a b c)) =
      LeviRules.powerBoundedSource m R k := by
    change PowerSeries.coeff s (currentMap m (orbit ℂ r a b c)) =
      LeviRules.sourceWord m j [] (polarLowerWord a b c)
    rw [LeviRules.sourceWord,LeviRules.shiftWord,← LeviRules.seed_eq_monoMap]
    change PowerSeries.coeff s (currentMap m (orbit ℂ r a b c)) =
      wordOp (LeviRules.representation ℂ m) (polarLowerWord a b c)
        (PowerSeries.coeff s (AllM.current m 0 ^ r))
    rw [currentMap_orbit,coeff_current_iterate,coeff_current_iterate,coeff_current_iterate]
    rw [polarLowerWord,wordOp_append,wordOp_append]
    rw [show (9 : Fin 18) = Fin.castAdd 8 (9 : Fin 10) from rfl,
      show (8 : Fin 18) = Fin.castAdd 8 (8 : Fin 10) from rfl,
      show (7 : Fin 18) = Fin.castAdd 8 (7 : Fin 10) from rfl]
    rw [modelWord_replicate_g0 m 9,modelWord_replicate_g0 m 8,modelWord_replicate_g0 m 7]
  rw [he]
  exact Ideal.subset_span ⟨k,rfl⟩

theorem quadraticCubicPolarIdeal_le_powerBounded (m : ℕ) :
    quadraticCubicPolarIdeal m ≤ LeviRules.powerBoundedIdeal m 3 := by
  apply Ideal.span_le.mpr
  rintro p ⟨r,a,b,c,s,hr,hs,rfl⟩
  exact current_orbit_coeff_mem_powerBounded m 3 r a b c s (by omega) (by omega) hs

theorem quadratic_cubic_jet_product_coeff_mem_powerBounded
    (m a b N x1 y1 z1 x2 y2 z2 : ℕ) (h : 2 * m < 5 + N + a + b) :
    PowerSeries.coeff N
      (jetDerivative a (currentMap m (orbit ℂ 2 x1 y1 z1)) *
        jetDerivative b (currentMap m (orbit ℂ 3 x2 y2 z2))) ∈
          LeviRules.powerBoundedIdeal m 3 :=
  quadraticCubicPolarIdeal_le_powerBounded m
    (quadratic_cubic_jet_product_coeff_mem_polarIdeal m a b N x1 y1 z1 x2 y2 z2 h)

end
#print axioms current_orbit_coeff_mem_powerBounded
#print axioms quadraticCubicPolarIdeal_le_powerBounded
#print axioms quadratic_cubic_jet_product_coeff_mem_powerBounded
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
