import VOA.Huang.GenusTwoPointSepModes

/-!
# Converting translation relations into monic spatial Euler equations

A relation among translated insertion vectors acts on the normalized trace
coefficients through descending Pochhammer polynomials. Their leading
coefficients are one, so the conversion to powers of the Euler operator
introduces no denominators and preserves the coefficient algebra.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA
open scoped BigOperators

theorem series_ext {f g : BiSeries} (h : ∀ i j, coeff f i j = coeff g i j) : f = g :=
  PowerSeries.ext fun i => PowerSeries.ext fun j => h i j

@[simp] theorem coeff_sum {ι : Type*} (s : Finset ι) (f : ι → BiSeries) (i j : ℕ) :
    coeff (∑ k ∈ s, f k) i j = ∑ k ∈ s, coeff (f k) i j := by simp [coeff]

def polynomialEuler (p : Polynomial ℂ) (e : ℕ → ℕ → ℂ) (f : BiSeries) : BiSeries :=
  ofArray (fun i j => p.eval (e i j) * coeff f i j)

theorem polynomialEuler_eq_sum (p : Polynomial ℂ) (e : ℕ → ℕ → ℂ) (f : BiSeries)
    {s : ℕ} (hs : p.natDegree < s) :
    polynomialEuler p e f = ∑ k ∈ Finset.range s, p.coeff k • (euler e)^[k] f := by
  apply series_ext
  intro i j
  simp only [polynomialEuler, coeff_ofArray, coeff_sum, coeff_smul,
    coeff_euler_iterate, UniformConv.diagPow]
  rw [Polynomial.eval_eq_sum_range' hs, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => mul_assoc _ _ _

theorem fallingEuler_leading (e : ℕ → ℕ → ℂ) (f : BiSeries) (s : ℕ) :
    polynomialEuler (descPochhammer ℂ s) e f =
      (euler e)^[s] f +
        ∑ k ∈ Finset.range s, (descPochhammer ℂ s).coeff k • (euler e)^[k] f := by
  rw [polynomialEuler_eq_sum _ e f (by simp [descPochhammer_natDegree] :
      (descPochhammer ℂ s).natDegree < s + 1), Finset.sum_range_succ]
  have hc : (descPochhammer ℂ s).coeff s = 1 := by
    simpa only [descPochhammer_natDegree] using (monic_descPochhammer ℂ s).coeff_natDegree
  rw [hc, one_smul, add_comm]

/-- Monicity survives the translation-to-Euler conversion over any coefficient
subalgebra. No division by a function, and no regularity loss, occurs. -/
theorem monicEquation_of_fallingRelation (R : Subalgebra ℂ BiSeries)
    (e : ℕ → ℕ → ℂ) (f : BiSeries) {s : ℕ} (hs : 0 < s) (a : ℕ → R)
    (h : polynomialEuler (descPochhammer ℂ s) e f =
      ∑ k ∈ Finset.range s, (a k).val * polynomialEuler (descPochhammer ℂ k) e f) :
    MonicEquation R e f := by
  classical
  let b : ℕ → R := fun l =>
    (∑ k ∈ Finset.range s, (descPochhammer ℂ k).coeff l • a k) -
      algebraMap ℂ R ((descPochhammer ℂ s).coeff l)
  refine ⟨s, b, hs, ?_⟩
  rw [fallingEuler_leading] at h
  have hk : ∀ k ∈ Finset.range s,
      polynomialEuler (descPochhammer ℂ k) e f =
        ∑ l ∈ Finset.range s, (descPochhammer ℂ k).coeff l • (euler e)^[l] f := by
    intro k hk
    exact polynomialEuler_eq_sum _ _ _ (by simpa using hk)
  have hsum : (∑ l ∈ Finset.range s, (b l).val * (euler e)^[l] f) =
      (∑ k ∈ Finset.range s, (a k).val * polynomialEuler (descPochhammer ℂ k) e f) -
        ∑ l ∈ Finset.range s, (descPochhammer ℂ s).coeff l • (euler e)^[l] f := by
    have hb : ∀ l, (b l).val =
        (∑ k ∈ Finset.range s, (descPochhammer ℂ k).coeff l • (a k).val) -
          (descPochhammer ℂ s).coeff l • (1 : BiSeries) := by
      intro l
      change R.val (b l) = _
      simp [b, Algebra.algebraMap_eq_smul_one]
    simp_rw [hb, sub_mul, Finset.sum_sub_distrib, smul_mul_assoc, one_mul]
    congr 1
    calc
      _ = ∑ l ∈ Finset.range s, ∑ k ∈ Finset.range s,
          (a k).val * ((descPochhammer ℂ k).coeff l • (euler e)^[l] f) := by
        simp only [Finset.sum_mul, smul_mul_assoc, mul_smul_comm]
      _ = ∑ k ∈ Finset.range s, ∑ l ∈ Finset.range s,
          (a k).val * ((descPochhammer ℂ k).coeff l • (euler e)^[l] f) :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk'
        rw [hk k hk', Finset.mul_sum]
  rw [hsum]
  exact eq_sub_of_add_eq h

section ActualProduct
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- A relation on actual translated traces supplies the spatial monic equation.
The remaining hypothesis is the relation itself, with shifted weights retained. -/
theorem productSpatialEquation_of_descendantRelation (R : Subalgebra ℂ BiSeries)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ) {s : ℕ} (hs : 0 < s) (a : ℕ → R)
    (h : ofArray (productLevelCoeff Y₁ Y₂ ((P₁.isMod.Lm1)^[s] w₁) w₂ (α₁ + s) α₂) =
      ∑ k ∈ Finset.range s, (a k).val *
        ofArray (productLevelCoeff Y₁ Y₂ ((P₁.isMod.Lm1)^[k] w₁) w₂ (α₁ + k) α₂)) :
    MonicEquation R (fun n k => N.h - Q.h - α₁ + n - k)
      (ofArray (productLevelCoeff Y₁ Y₂ w₁ w₂ α₁ α₂)) := by
  have he : ∀ j, ofArray (productLevelCoeff Y₁ Y₂
      ((P₁.isMod.Lm1)^[j] w₁) w₂ (α₁ + j) α₂) =
      polynomialEuler (descPochhammer ℂ j) (fun n k => N.h - Q.h - α₁ + n - k)
        (ofArray (productLevelCoeff Y₁ Y₂ w₁ w₂ α₁ α₂)) := by
    intro j
    apply series_ext
    intro n k
    simp only [coeff_ofArray, polynomialEuler, productLevelCoeff_Lm1_iterate]
  simp_rw [he] at h
  exact monicEquation_of_fallingRelation R _ _ hs a h

/-- The same algebraic conversion for the collision coordinate. The hypothesis
must already be a relation on the normalized arrays over a regular ring; a
relation with poles at the collision is not sufficient. -/
theorem iterateSpatialEquation_of_descendantRelation (R : Subalgebra ℂ BiSeries)
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ) {s : ℕ} (hs : 0 < s) (a : ℕ → R)
    (h : ofArray (iterateLevelCoeff Y₃ Y₄ ((P₁.isMod.Lm1)^[s] w₁) w₂ (α₁ + s) α₂) =
      ∑ k ∈ Finset.range s, (a k).val *
        ofArray (iterateLevelCoeff Y₃ Y₄ ((P₁.isMod.Lm1)^[k] w₁) w₂ (α₁ + k) α₂)) :
    MonicEquation R (fun _ k => Q.h - α₁ - α₂ + k)
      (ofArray (iterateLevelCoeff Y₃ Y₄ w₁ w₂ α₁ α₂)) := by
  have he : ∀ j, ofArray (iterateLevelCoeff Y₃ Y₄
      ((P₁.isMod.Lm1)^[j] w₁) w₂ (α₁ + j) α₂) =
      polynomialEuler (descPochhammer ℂ j) (fun _ k => Q.h - α₁ - α₂ + k)
        (ofArray (iterateLevelCoeff Y₃ Y₄ w₁ w₂ α₁ α₂)) := by
    intro j
    apply series_ext
    intro n k
    simp only [coeff_ofArray, polynomialEuler, iterateLevelCoeff_Lm1_iterate]
  simp_rw [he] at h
  exact monicEquation_of_fallingRelation R _ _ hs a h

end ActualProduct
end VOA.Huang.GenusTwoPoint.Separate
