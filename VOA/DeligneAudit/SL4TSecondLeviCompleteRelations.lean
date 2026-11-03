import VOA.DeligneAudit.SL4TSecondLeviMultiplicity

/-! Relative complete functions in the first lowering alphabet and corrected Garland vanishing. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.LeviTypeA VOA.DeligneAudit.LeviConversion

attribute [local instance 2000] Fin.fintype Fin.instOfNat

variable {B V : Type} [CommRing B] [Algebra ℂ B]
variable [AddCommGroup V] [Module ℂ V]

/-- The complete function is the sum over all mode assignments with the prescribed total. -/
theorem completePolynomial_modeVectors (k s : ℕ) :
    hsymm (Fin k) B s =
      ∑ u : {u : Fin k → ℕ // ∑ i, u i = s}, ∏ i, X i ^ u.val i := by
  have he := congrArg (MvPolynomial.map (algebraMap ℂ B))
    (D4Levi.rz_hsymm_eq_sum_vectors k s)
  simpa only [map_hsymm, map_sum, map_prod, map_pow, map_X] using he

/-- Evaluation of a full labelled monomial with a base coefficient. -/
theorem positionModeEvaluation_prod_C {σ : Type} [Fintype σ]
    (F : σ → ℕ → Module.End ℂ V) (is : List σ) (β : B →ₗ[ℂ] V)
    (u : σ → ℕ) (φ : B) :
    positionModeEvaluation F is β ((∏ i, X i ^ u i) * MvPolynomial.C φ) =
      positionModeProduct F is u (β φ) := by
  classical
  let v := Finsupp.equivFunOnFinite.symm u
  have he : (monomial v 1 : MvPolynomial σ B) = ∏ i, X i ^ u i := by
    rw [monomial_eq, map_one, one_mul]
    exact v.prod_fintype _ (fun i => pow_zero _)
  rw [← he, mul_comm, C_mul_monomial, mul_one, positionModeEvaluation_monomial]
  rfl

variable (Q : CurrentModule VOA.AffineSl3.bracketTable V) (β : B →ₗ[ℂ] V)

/-- The complete polynomial in the simple alphabet evaluates to its current coefficient. -/
theorem secondLeviModeEvaluation_firstComplete (e₁ e₂ s : ℕ) (φ : B) :
    secondLeviModeEvaluation Q β e₁ e₂
      (rename Sum.inl (hsymm (Fin e₁) B s) * MvPolynomial.C φ) =
        (Q.op 5 0 ^ e₂)
          ((PowerSeries.coeff s (fCurrent (fun n => Q.op 3 n) ^ e₁)) (β φ)) := by
  classical
  rw [completePolynomial_modeVectors, map_sum, Finset.sum_mul, map_sum,
    currentPower_coeff_modeVectors]
  simp only [LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have he : rename Sum.inl (∏ i : Fin e₁, X i ^ u.val i) =
      ∏ i : SecondLeviModeSlot e₁ e₂, (X i : MvPolynomial _ B) ^
        Sum.elim u.val (fun _ => 0) i := by
    simp [map_prod, map_pow, rename_X, Fintype.prod_sum_type]
  rw [he, secondLeviModeEvaluation, positionModeEvaluation_prod_C,
    secondLeviPositionProduct]
  simp only [Sum.elim_inl, Sum.elim_inr, List.ofFn_const, List.map_replicate,
    List.prod_replicate, Module.End.mul_apply]
  have hc : Commute (Q.op 5 0 ^ e₂) ((List.ofFn u.val).map fun n => Q.op 3 n).prod := by
    apply Commute.list_prod_right
    intro x hx
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
    exact (show Commute (Q.op 5 0) (Q.op 3 n) from
      a2RadicalOp_comm Q 1 0 0 n).pow_left e₂
  exact (congrArg (fun T : Module.End ℂ V => T (β φ)) hc.eq).symm

/-- Relative complete functions use the Newton coefficients of the base power sums. -/
def secondLeviRelativeComplete (e₁ e₂ : ℕ) (j : Fin 2) (p : ℕ → B) (s : ℕ) :
    MvPolynomial (SecondLeviModeSlot e₁ e₂) B :=
  ∑ z ∈ Finset.antidiagonal s,
    (if j = 0 then rename Sum.inl (hsymm (Fin e₁) B z.1)
      else rename Sum.inr (hsymm (Fin e₂) B z.1)) * MvPolynomial.C (newtonCoeff p z.2)

/-- The first relative complete function is the full corrected Garland coefficient. -/
theorem secondLeviModeEvaluation_relativeComplete (e₁ e₂ s : ℕ) (p : ℕ → B)
    (hb : ∀ n, 1 ≤ n → ∀ φ, Q.op 6 n (β φ) = β (p n * φ)) (φ : B) :
    secondLeviModeEvaluation Q β e₁ e₂
      (secondLeviRelativeComplete e₁ e₂ 0 p s * MvPolynomial.C φ) =
        (Q.op 5 0 ^ e₂)
          ((PowerSeries.coeff s
            (Garland.Fs (fun n => Q.op 3 n) ^ e₁ *
              newtonSeries (fun n => Q.op 6 n))) (β φ)) := by
  classical
  simp only [secondLeviRelativeComplete, if_true, Finset.sum_mul, map_sum,
    PowerSeries.coeff_mul, LinearMap.sum_apply, Module.End.mul_apply,
    newtonSeries, PowerSeries.coeff_mk, newtonEnd_pi _ β p hb]
  apply Finset.sum_congr rfl
  intro z hz
  rw [mul_assoc, ← map_mul, secondLeviModeEvaluation_firstComplete]
  rfl

/-- Corrected Garland kills the first relative tail at every base vector. -/
theorem secondLeviModeEvaluation_firstRelativeTail (r e₁ e₂ s : ℕ) (p : ℕ → B)
    (he : ∀ n φ, Q.op 0 n (β φ) = 0)
    (hh : ∀ n, 1 ≤ n → ∀ φ, Q.op 6 n (β φ) = β (p n * φ))
    (hf : ∀ φ, (Q.op 3 0 ^ (r + 1)) (β φ) = 0)
    (hk : 1 ≤ e₁) (hs : r + 1 ≤ e₁ + s) (φ : B) :
    secondLeviModeEvaluation Q β e₁ e₂
      (secondLeviRelativeComplete e₁ e₂ 0 p s * MvPolynomial.C φ) = 0 := by
  rw [secondLeviModeEvaluation_relativeComplete Q β e₁ e₂ s p hh]
  have hg := garland_pi_coeff (leviSimple_currentRelations Q 0) β p he hh r hf
    e₁ s hk hs φ
  simp only [if_true] at hg
  rw [hg, map_zero]

variable (ρ : CurrentModule bracketTable V) (w : V)
variable (a b c : ℕ) (h : LocalWeylRel ρ w (weightABC a b c))

set_option synthInstance.maxHeartbeats 100000 in
-- The source coefficient algebra is the tensor product of three quotient rings.
/-- The first relative tail vanishes in the actual second Levi multiplicity quotient. -/
theorem radicalSecondLeviEvaluation_firstRelativeTail (d : Fin 3 → ℕ)
    (hm : 0 ≤ a3KeyLabelInt b c 0 ⟨d 0, d 1, d 2, 0⟩)
    (e₁ e₂ s : ℕ) (hk : 1 ≤ e₁)
    (hs : (a3KeyLabelInt b c 0 ⟨d 0, d 1, d 2, 0⟩).toNat + 1 ≤ e₁ + s)
    (φ : RadicalGrassmannianRing a b c d) :
    let Q := radicalCountQuotCurrent ρ w d
    let β := radicalGrassmannianAmbientEvaluation ρ w a b c h d
    secondLeviQuotientEvaluation Q β e₁ e₂
      (secondLeviRelativeComplete e₁ e₂ 0 (radicalLeviPowerSum a b c d 0) s *
        MvPolynomial.C φ) = 0 := by
  dsimp only
  change (higherSecondLeviCountClosure _ _ _ _).mkQ
    (secondLeviModeEvaluation _ _ _ _ _) = 0
  rw [secondLeviModeEvaluation_firstRelativeTail _ _ _ _ _ _ _
    (radicalGrassmannianAmbientEvaluation_raising ρ w a b c h d 0)
    (radicalGrassmannianAmbientEvaluation_cartan ρ w a b c h d 0)
    (radicalGrassmannianAmbientEvaluation_lowering ρ w a b c h d 0 hm) hk hs,
    map_zero]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.completePolynomial_modeVectors
#print axioms VOA.DeligneAudit.SL4T.positionModeEvaluation_prod_C
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeEvaluation_firstComplete
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeEvaluation_relativeComplete
#print axioms VOA.DeligneAudit.SL4T.secondLeviModeEvaluation_firstRelativeTail
#print axioms VOA.DeligneAudit.SL4T.radicalSecondLeviEvaluation_firstRelativeTail
