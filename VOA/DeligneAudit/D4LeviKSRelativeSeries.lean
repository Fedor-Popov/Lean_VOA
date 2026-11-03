import VOA.DeligneAudit.D4LeviKSRelativeBox

/-! Complete-series convolution in the form used by relative box induction. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

variable {A : Type*} [CommRing A] [Algebra ℂ A]

theorem ksHSeries_coeff_zero (vs : List A) :
    PowerSeries.coeff 0 (ksHSeries vs) = 1 := by
  induction vs with
  | nil => simp [ksHSeries]
  | cons a vs ih =>
      change PowerSeries.coeff 0 (ksGeometricSeries a * ksHSeries vs) = 1
      simpa [PowerSeries.coeff_mul, ksGeometricSeries] using ih

/-- The top new-alphabet degree is isolated; every remaining summand has
    positive outer degree and strictly smaller new-alphabet degree. -/
theorem ksHSeries_append_coeff_relative (vs ws : List A) (s : ℕ) :
    PowerSeries.coeff s (ksHSeries (vs ++ ws)) =
      PowerSeries.coeff s (ksHSeries vs) +
        ∑ t ∈ Finset.range s,
          PowerSeries.coeff (s - t) (ksHSeries ws) *
            PowerSeries.coeff t (ksHSeries vs) := by
  classical
  rw [ksHSeries_append, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
  simp only [Nat.sub_self, ksHSeries_coeff_zero, mul_one]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  exact mul_comm _ _

theorem ksHSeries_aeval_relative (n : ℕ) (v : Fin n → A)
    (ws : List A) (s : ℕ) :
    PowerSeries.coeff s (ksHSeries (List.ofFn v ++ ws)) =
      aeval v (hsymm (Fin n) ℂ s) +
        ∑ t ∈ Finset.range s,
          PowerSeries.coeff (s - t) (ksHSeries ws) *
            aeval v (hsymm (Fin n) ℂ t) := by
  rw [ksHSeries_append_coeff_relative]
  simp only [ksHSeries_coeff_aeval]

/-- Complete series are unaffected by permuting their alphabet. -/
theorem ksHSeries_perm {vs ws : List A} (h : vs.Perm ws) :
    ksHSeries vs = ksHSeries ws :=
  (h.map ksGeometricSeries).prod_eq

theorem ksHSeries_coeff_equiv {σ : Type*} [Fintype σ] [DecidableEq σ] (n s : ℕ)
    (e : Fin n ≃ σ) (v : σ → A) :
    PowerSeries.coeff s (ksHSeries (List.ofFn (v ∘ e))) =
      aeval v (hsymm σ ℂ s) := by
  rw [ksHSeries_coeff_aeval, ← aeval_rename,
    rename_hsymm (Fin n) ℂ s e]

/-- The complete series of two enumerated blocks is their union's polynomial. -/
theorem ksHSeries_coeff_two_blocks (n l s : ℕ) (v : Fin n → A) (w : Fin l → A) :
    PowerSeries.coeff s (ksHSeries (List.ofFn v ++ List.ofFn w)) =
      aeval (Sum.elim v w) (hsymm (Fin n ⊕ Fin l) ℂ s) := by
  have hh := ksHSeries_coeff_equiv (n + l) s finSumFinEquiv.symm (Sum.elim v w)
  have he : List.ofFn (Sum.elim v w ∘ finSumFinEquiv.symm) =
      List.ofFn v ++ List.ofFn w := by
    rw [List.ofFn_add]
    congr 1
    · congr 1
      funext i
      change Sum.elim v w (finSumFinEquiv.symm (Fin.castAdd l i)) = v i
      simp only [finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
    · congr 1
      funext i
      change Sum.elim v w (finSumFinEquiv.symm (Fin.natAdd n i)) = w i
      simp only [finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]
  rwa [he] at hh

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksHSeries_coeff_zero
#print axioms VOA.DeligneAudit.D4Levi.ksHSeries_append_coeff_relative
#print axioms VOA.DeligneAudit.D4Levi.ksHSeries_aeval_relative
#print axioms VOA.DeligneAudit.D4Levi.ksHSeries_perm
#print axioms VOA.DeligneAudit.D4Levi.ksHSeries_coeff_equiv
#print axioms VOA.DeligneAudit.D4Levi.ksHSeries_coeff_two_blocks
