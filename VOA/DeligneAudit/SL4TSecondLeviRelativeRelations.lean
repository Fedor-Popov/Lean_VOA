import VOA.DeligneAudit.SL4TSecondLeviConversion

/-! The converted relative complete-function tail in the compound lowering alphabet. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.LeviConversion

attribute [local instance 2000] Fin.fintype Fin.instOfNat

variable {B V : Type} [CommRing B] [Algebra ℂ B]
variable [AddCommGroup V] [Module ℂ V]
variable (Q : CurrentModule VOA.AffineSl3.bracketTable V) (β : B →ₗ[ℂ] V)

/-- Complete functions in the compound alphabet evaluate to its current coefficients. -/
theorem secondLeviModeEvaluation_secondComplete (e₁ e₂ s : ℕ) (φ : B) :
    secondLeviModeEvaluation Q β e₁ e₂
      (rename Sum.inr (hsymm (Fin e₂) B s) * MvPolynomial.C φ) =
        (Q.op 3 0 ^ e₁)
          ((PowerSeries.coeff s (fCurrent (fun n => Q.op 5 n) ^ e₂)) (β φ)) := by
  classical
  rw [completePolynomial_modeVectors, map_sum, Finset.sum_mul, map_sum,
    currentPower_coeff_modeVectors]
  simp only [LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have he : rename Sum.inr (∏ i : Fin e₂, X i ^ u.val i) =
      ∏ i : SecondLeviModeSlot e₁ e₂, (X i : MvPolynomial _ B) ^
        Sum.elim (fun _ => 0) u.val i := by
    simp [map_prod, map_pow, rename_X, Fintype.prod_sum_type]
  rw [he, secondLeviModeEvaluation, positionModeEvaluation_prod_C,
    secondLeviPositionProduct]
  simp [List.ofFn_const, List.prod_replicate, Module.End.mul_apply]

/-- The second relative complete function includes the full base Newton correction. -/
theorem secondLeviModeEvaluation_secondRelativeComplete (e₁ e₂ s : ℕ) (p : ℕ → B)
    (hb : ∀ n, 1 ≤ n → ∀ φ, Q.op 7 n (β φ) = β (p n * φ)) (φ : B) :
    secondLeviModeEvaluation Q β e₁ e₂
      (secondLeviRelativeComplete e₁ e₂ 1 p s * MvPolynomial.C φ) =
        (Q.op 3 0 ^ e₁)
          ((PowerSeries.coeff s
            (Garland.Fs (fun n => Q.op 5 n) ^ e₂ *
              newtonSeries (fun n => Q.op 7 n))) (β φ)) := by
  classical
  simp only [secondLeviRelativeComplete, show (1 : Fin 2) ≠ 0 by decide, if_false,
    Finset.sum_mul, map_sum, PowerSeries.coeff_mul, LinearMap.sum_apply,
    Module.End.mul_apply, newtonSeries, PowerSeries.coeff_mk, newtonEnd_pi _ β p hb]
  apply Finset.sum_congr rfl
  intro z hz
  rw [mul_assoc, ← map_mul, secondLeviModeEvaluation_secondComplete]
  rfl

/-- Letter conversion commutes with the Newton correction after passing to higher counts. -/
theorem secondLeviConversion_correctedCoefficient (n k s : ℕ) (p : ℕ → B)
    (hb : ∀ t, 1 ≤ t → ∀ φ, Q.op 7 t (β φ) = β (p t * φ)) (φ : B) :
    let N := higherSecondLeviCountClosure Q β n k
    N.mkQ ((Q.op 3 0 ^ (n + k))
      ((PowerSeries.coeff s (Garland.Fs (fun t => Q.op 4 t) ^ k *
        newtonSeries (fun t => Q.op 7 t))) (β φ))) =
      (((-1 : ℂ) ^ k * (k.factorial : ℂ)) * ((n + k).choose k : ℂ)) •
        secondLeviQuotientEvaluation Q β n k
          (secondLeviRelativeComplete n k 1 p s * MvPolynomial.C φ) := by
  classical
  dsimp only
  rw [secondLeviQuotientEvaluation, LinearMap.comp_apply,
    secondLeviModeEvaluation_secondRelativeComplete Q β n k s p hb]
  simp only [PowerSeries.coeff_mul, LinearMap.sum_apply, Module.End.mul_apply,
    newtonSeries, PowerSeries.coeff_mk, newtonEnd_pi _ β p hb, map_sum,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  exact secondLeviConversion_coefficient Q β n k z.1 (newtonCoeff p z.2 * φ)

/-- Corrected Garland and letter conversion kill the second relative complete-function tail. -/
theorem secondLeviQuotientEvaluation_secondRelativeTail (r e₁ e₂ s : ℕ) (p : ℕ → B)
    (he : ∀ n φ, Q.op 1 n (β φ) = 0)
    (hh : ∀ n, 1 ≤ n → ∀ φ, Q.op 7 n (β φ) = β (p n * φ))
    (hf : ∀ φ, (Q.op 4 0 ^ (r + 1)) (β φ) = 0)
    (hk : 1 ≤ e₂) (hs : r + 1 ≤ e₂ + s) (φ : B) :
    secondLeviQuotientEvaluation Q β e₁ e₂
      (secondLeviRelativeComplete e₁ e₂ 1 p s * MvPolynomial.C φ) = 0 := by
  have hg := garland_pi_coeff (leviSimple_currentRelations Q 1) β p he hh r hf
    e₂ s hk hs φ
  simp only [show (1 : Fin 2) ≠ 0 by decide, if_false] at hg
  have hc := secondLeviConversion_correctedCoefficient Q β e₁ e₂ s p hh φ
  dsimp only at hc
  rw [hg, map_zero, map_zero] at hc
  have hn : (((-1 : ℂ) ^ e₂ * (e₂.factorial : ℂ)) *
      ((e₁ + e₂).choose e₂ : ℂ)) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    · exact Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (by omega))
  exact (smul_eq_zero.mp hc.symm).resolve_left hn

variable (ρ : CurrentModule bracketTable V) (w : V)
variable (a b c : ℕ) (h : LocalWeylRel ρ w (weightABC a b c))

set_option synthInstance.maxHeartbeats 100000 in
-- The source coefficient algebra is a tensor product of three quotient rings.
/-- The second relative tail vanishes for the actual Grassmannian multiplicity source. -/
theorem radicalSecondLeviEvaluation_secondRelativeTail (d : Fin 3 → ℕ)
    (hm : 0 ≤ a3KeyLabelInt b c 1 ⟨d 0, d 1, d 2, 0⟩)
    (e₁ e₂ s : ℕ) (hk : 1 ≤ e₂)
    (hs : (a3KeyLabelInt b c 1 ⟨d 0, d 1, d 2, 0⟩).toNat + 1 ≤ e₂ + s)
    (φ : RadicalGrassmannianRing a b c d) :
    let Q := radicalCountQuotCurrent ρ w d
    let β := radicalGrassmannianAmbientEvaluation ρ w a b c h d
    secondLeviQuotientEvaluation Q β e₁ e₂
      (secondLeviRelativeComplete e₁ e₂ 1 (radicalLeviPowerSum a b c d 1) s *
        MvPolynomial.C φ) = 0 :=
  secondLeviQuotientEvaluation_secondRelativeTail _ _ _ _ _ _ _
    (radicalGrassmannianAmbientEvaluation_raising ρ w a b c h d 1)
    (radicalGrassmannianAmbientEvaluation_cartan ρ w a b c h d 1)
    (radicalGrassmannianAmbientEvaluation_lowering ρ w a b c h d 1 hm) hk hs φ

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.secondLeviModeEvaluation_secondComplete
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeEvaluation_secondRelativeComplete
#print axioms VOA.DeligneAudit.SL4T.secondLeviConversion_correctedCoefficient
#print axioms VOA.DeligneAudit.SL4T.secondLeviQuotientEvaluation_secondRelativeTail
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviEvaluation_secondRelativeTail
