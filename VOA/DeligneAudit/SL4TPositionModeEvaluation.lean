import VOA.DeligneAudit.SL4TRadicalLeviGarland

/-! Polynomial mode evaluation with a coefficient space carrying a Cartan action. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial

variable {σ B V : Type*} [CommRing B] [Algebra ℂ B]
variable [AddCommGroup V] [Module ℂ V]

/-- The ordered current product attached to a list of labelled positions. -/
def positionModeProduct (F : σ → ℕ → Module.End ℂ V) (is : List σ)
    (u : σ → ℕ) : Module.End ℂ V :=
  (is.map fun i => F i (u i)).prod

/-- Polynomial exponents specify modes, while coefficients are evaluated at the base. -/
def positionModeEvaluation (F : σ → ℕ → Module.End ℂ V) (is : List σ)
    (β : B →ₗ[ℂ] V) : MvPolynomial σ B →ₗ[ℂ] V :=
  Finsupp.lsum ℂ fun u : σ →₀ ℕ => (positionModeProduct F is u).comp β

theorem positionModeEvaluation_monomial (F : σ → ℕ → Module.End ℂ V)
    (is : List σ) (β : B →ₗ[ℂ] V) (u : σ →₀ ℕ) (b : B) :
    positionModeEvaluation F is β (monomial u b) =
      positionModeProduct F is u (β b) := by
  exact Finsupp.lsum_single _ _ _ _

/-- The Cartan commutator is the sum of the individual labelled mode shifts. -/
theorem positionModeProduct_cartan
    (F : σ → ℕ → Module.End ℂ V) (H : Module.End ℂ V)
    (c : σ → ℂ) (s : ℕ)
    (hc : ∀ i n, H * F i n - F i n * H = c i • F i (s + n))
    (is : List σ) (his : is.Nodup) (u : σ →₀ ℕ) (v : V) :
    H (positionModeProduct F is u v) =
      positionModeProduct F is u (H v) +
        (is.map fun i => c i •
          positionModeProduct F is (Finsupp.single i s + u : σ →₀ ℕ) v).sum := by
  classical
  induction is with
  | nil => simp [positionModeProduct]
  | cons t ts ih =>
    have ht := (List.nodup_cons.mp his).1
    have hts := (List.nodup_cons.mp his).2
    have hhead : positionModeProduct F ts (Finsupp.single t s + u : σ →₀ ℕ) =
        positionModeProduct F ts u := by
      unfold positionModeProduct
      congr 1
      apply List.map_congr_left
      intro i hi
      have hti : t ≠ i := by intro he; exact ht (he ▸ hi)
      simp [hti]
    have htail (i : σ) (hi : i ∈ ts) : (Finsupp.single i s + u : σ →₀ ℕ) t = u t := by
      have hit : i ≠ t := by intro he; exact ht (he ▸ hi)
      simp [hit]
    have he := congrArg (fun T : Module.End ℂ V =>
      T (positionModeProduct F ts u v)) (hc t (u t))
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply] at he
    rw [sub_eq_iff_eq_add] at he
    simp only [positionModeProduct, List.map_cons, List.prod_cons,
      Module.End.mul_apply] at ⊢
    change H (F t (u t) (positionModeProduct F ts u v)) = _
    rw [he, ih hts, map_add, map_list_sum]
    have hsum :
        (ts.map fun i => F t (u t)
          (c i • positionModeProduct F ts (Finsupp.single i s + u : σ →₀ ℕ) v)).sum =
        (ts.map fun i => c i • positionModeProduct F (t :: ts)
          (Finsupp.single i s + u : σ →₀ ℕ) v).sum := by
      congr 1
      apply List.map_congr_left
      intro i hi
      simp only [positionModeProduct, List.map_cons, List.prod_cons,
        Module.End.mul_apply, htail i hi, map_smul]
    simp only [List.map_map, Function.comp_def] at ⊢
    rw [hsum]
    simp only [List.map_cons, List.sum_cons, positionModeProduct,
      List.prod_cons, Module.End.mul_apply, Finsupp.add_apply, Finsupp.single_eq_same]
    change c t • F t (s + u t) (positionModeProduct F ts u v) +
      (F t (u t) (positionModeProduct F ts u (H v)) + _) =
      F t (u t) (positionModeProduct F ts u (H v)) +
        (c t • F t (s + u t)
          (positionModeProduct F ts (Finsupp.single t s + u : σ →₀ ℕ) v) + _)
    rw [hhead]
    abel

/-- The polynomial encoding a weighted sum of individual mode shifts. -/
def positionModePowerSum (is : List σ) (c : σ → ℂ) (s : ℕ) : MvPolynomial σ B :=
  (is.map fun i => c i • X i ^ s).sum

theorem positionModeEvaluation_powerSum_monomial
    (F : σ → ℕ → Module.End ℂ V) (is : List σ) (β : B →ₗ[ℂ] V)
    (c : σ → ℂ) (s : ℕ) (u : σ →₀ ℕ) (b : B) :
    positionModeEvaluation F is β (positionModePowerSum is c s * monomial u b) =
      (is.map fun i => c i •
        positionModeProduct F is (Finsupp.single i s + u : σ →₀ ℕ) (β b)).sum := by
  classical
  simp only [positionModePowerSum, ← List.sum_map_mul_right, map_list_sum,
    List.map_map, Function.comp_def, smul_mul_assoc, map_smul, X_pow_eq_monomial,
    monomial_mul, one_mul, positionModeEvaluation_monomial]

/-- Cartan action includes both its base action and its mode-shift action. -/
theorem positionModeEvaluation_cartan
    (F : σ → ℕ → Module.End ℂ V) (is : List σ) (his : is.Nodup)
    (β : B →ₗ[ℂ] V) (H : Module.End ℂ V) (U : B) (c : σ → ℂ) (s : ℕ)
    (hc : ∀ i n, H * F i n - F i n * H = c i • F i (s + n))
    (hb : ∀ b, H (β b) = β (U * b)) (P : MvPolynomial σ B) :
    H (positionModeEvaluation F is β P) =
      positionModeEvaluation F is β ((MvPolynomial.C U + positionModePowerSum is c s) * P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u b =>
    rw [positionModeEvaluation_monomial,
      positionModeProduct_cartan F H c s hc is his u (β b), hb,
      add_mul, map_add, C_mul_monomial, positionModeEvaluation_monomial,
      positionModeEvaluation_powerSum_monomial]
  | add P Q hP hQ => simp only [map_add, mul_add, hP, hQ]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.positionModeEvaluation_monomial
#print axioms VOA.DeligneAudit.SL4T.positionModeProduct_cartan
#print axioms VOA.DeligneAudit.SL4T.positionModeEvaluation_powerSum_monomial
#print axioms VOA.DeligneAudit.SL4T.positionModeEvaluation_cartan
