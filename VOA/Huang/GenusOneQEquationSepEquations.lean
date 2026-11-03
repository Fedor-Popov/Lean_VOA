import VOA.Huang.GenusTwoPointSepKernels
import VOA.Huang.UniformConvConsumers

/-!
# Separate monic Euler equations from the genus-one relation quotient

Formal double-series equations over a bidisc coefficient algebra imply the
unchanged `ProductSeparateFuchsian` input. Local absolute coefficient sums give
the corresponding implication for `IterateSeparateFuchsian`.

The finite-generation step is also connected to these equations, conditional
on the existing trace descent and on orbits for the *pure diagonal* operators.
Huang's weight-dependent mixed q/coordinate operator is not silently replaced
by a pure q derivative. Neither actual VOA input is discharged by this file.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA VOA.Huang.UniformConv VOA.Huang.HuangODEThree QEquation
open scoped BigOperators

/-- The formal diagonal Euler operator, with the prefactor exponent included. -/
def euler (e : ℕ → ℕ → ℂ) (f : BiSeries) : BiSeries :=
  ofArray (fun i j => e i j * coeff f i j)

theorem coeff_euler_iterate (e : ℕ → ℕ → ℂ) (f : BiSeries) (k i j : ℕ) :
    coeff ((euler e)^[k] f) i j = diagPow e k (coeff f) i j := by
  induction k with
  | zero => simp [diagPow]
  | succ k ih =>
    rw [Function.iterate_succ_apply', euler, coeff_ofArray, ih]
    simp only [diagPow, pow_succ']
    ring

/-- The coefficient form of a monic formal double-series identity. -/
theorem diagonalFuchsian_of_series {e : ℕ → ℕ → ℂ} {f : BiSeries}
    {s : ℕ} {a : ℕ → BiSeries}
    (heq : (euler e)^[s] f = ∑ k ∈ Finset.range s, a k * (euler e)^[k] f) :
    DiagonalFuchsian e s (fun k => coeff (a k)) (coeff f) := by
  apply diagonalFuchsian_of_conv
  intro i j
  have h := congrArg (fun f => coeff f i j) heq
  simp only [coeff_euler_iterate] at h
  rw [coeff, map_sum, map_sum] at h
  change _ = ∑ k ∈ Finset.range s, coeff (a k * (euler e)^[k] f) i j at h
  simpa only [coeff_mul, conv, coeff_euler_iterate] using h

/-- A positive-order monic equation over a specified coefficient subalgebra. -/
def MonicEquation (R : Subalgebra ℂ BiSeries) (e : ℕ → ℕ → ℂ) (f : BiSeries) : Prop :=
  ∃ (s : ℕ) (a : ℕ → R), 0 < s ∧
    (euler e)^[s] f = ∑ k ∈ Finset.range s, (a k).val * (euler e)^[k] f

/-- A pair of monic equations with bidisc coefficients has a common geometric
bound at each rate. Independence is checked on the actual integer forms. -/
theorem separateSystem_of_monic (R : Subalgebra ℂ BiSeries) (hR : R ≤ bidiscAlgebra)
    {f : BiSeries} (lam mu : ℂ) (a₁ b₁ a₂ b₂ : ℤ)
    (hdet : a₁ * b₂ - a₂ * b₁ ≠ 0)
    (h₁ : MonicEquation R (fun i j => lam + ((a₁ * i + b₁ * j : ℤ) : ℂ)) f)
    (h₂ : MonicEquation R (fun i j => mu + ((a₂ * i + b₂ * j : ℤ) : ℂ)) f)
    {r : ℝ} (hr : 1 < r) : Nonempty (SeparateSystem (coeff f) r r) := by
  obtain ⟨s₁, a, hs₁, heq₁⟩ := h₁
  obtain ⟨s₂, b, hs₂, heq₂⟩ := h₂
  obtain ⟨A, hA0, hA⟩ := finite_family_bound (Finset.range s₁) (fun k => (a k).val)
    (fun k _ => hR (a k).property) hr
  obtain ⟨B, hB0, hB⟩ := finite_family_bound (Finset.range s₂) (fun k => (b k).val)
    (fun k _ => hR (b k).property) hr
  apply separateSystem_of_linear lam mu a₁ b₁ a₂ b₂ hdet hs₁ hs₂
    (G := max A B) (g₁ := fun k => coeff (a k).val) (g₂ := fun k => coeff (b k).val)
  · intro k hk i j
    exact (hA k (Finset.mem_range.mpr hk) i j).trans (by
      gcongr
      exact le_max_left A B)
  · intro k hk i j
    exact (hB k (Finset.mem_range.mpr hk) i j).trans (by
      gcongr
      exact le_max_right A B)
  · exact diagonalFuchsian_of_series heq₁
  · exact diagonalFuchsian_of_series heq₂

section Coinvariants
universe u
variable {V M₁ M₂ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  {W : VertexOperatorAlgebra V}

/-- Finite coinvariants produce a monic equation for a genuinely diagonal
orbit. Trace descent and that orbit identity are the only VOA obligations. -/
theorem monicEquation_of_descent (R : Subalgebra ℂ BiSeries) [IsNoetherianRing R]
    (A : AdmissibleModule W M₁) (B : AdmissibleModule W M₂)
    (hA : FusionC2.ModuleC2Cofinite A.toWeakModule)
    (hB : FusionC2.ModuleC2Cofinite B.toWeakModule) (c : Kernels R)
    (φ : Tensor R M₁ M₂ →ₗ[R] BiSeries) (hφ : TraceDescent A.toWeakModule B.toWeakModule c φ)
    (e : ℕ → ℕ → ℂ) (t : ℕ → Tensor R M₁ M₂)
    (ht : QOrbitCompatibility φ t (fun _ => euler e)) :
    MonicEquation R e (φ (t 0)) := by
  obtain ⟨s, a, hs, heq⟩ := exists_uniform_qEquation A B hA hB c t
  have hi : ∀ n, qIterate (fun _ => euler e) (φ (t 0)) n = (euler e)^[n] (φ (t 0)) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [qIterate, ih, Function.iterate_succ_apply']
  refine ⟨s, a, hs, ?_⟩
  have h := heq φ hφ (fun _ => euler e) ht
  simpa only [hi, Algebra.smul_def, Subalgebra.algebraMap_eq] using h

/-- The algebraic genus-one step and the separate-equation majorant are
composable without any radial equation or trace-growth assumption. -/
theorem separateSystem_of_descent (g : Fin 4 → BiSeries)
    (hg : ∀ k, g k ∈ bidiscAlgebra)
    (A : AdmissibleModule W M₁) (B : AdmissibleModule W M₂)
    (hA : FusionC2.ModuleC2Cofinite A.toWeakModule)
    (hB : FusionC2.ModuleC2Cofinite B.toWeakModule)
    (c : Kernels (coefficientAlgebra g))
    (φ : Tensor (coefficientAlgebra g) M₁ M₂ →ₗ[coefficientAlgebra g] BiSeries)
    (hφ : TraceDescent A.toWeakModule B.toWeakModule c φ)
    (t₁ t₂ : ℕ → Tensor (coefficientAlgebra g) M₁ M₂) (hzero : φ (t₁ 0) = φ (t₂ 0))
    (lam mu : ℂ) (a₁ b₁ a₂ b₂ : ℤ) (hdet : a₁ * b₂ - a₂ * b₁ ≠ 0)
    (ht₁ : QOrbitCompatibility φ t₁
      (fun _ => euler (fun i j => lam + ((a₁ * i + b₁ * j : ℤ) : ℂ))))
    (ht₂ : QOrbitCompatibility φ t₂
      (fun _ => euler (fun i j => mu + ((a₂ * i + b₂ * j : ℤ) : ℂ))))
    {r : ℝ} (hr : 1 < r) : Nonempty (SeparateSystem (coeff (φ (t₁ 0))) r r) := by
  apply separateSystem_of_monic (coefficientAlgebra g) (coefficientAlgebra_le_bidisc g hg)
    lam mu a₁ b₁ a₂ b₂ hdet
  · exact monicEquation_of_descent _ A B hA hB c φ hφ _ t₁ ht₁
  · rw [hzero]
    exact monicEquation_of_descent _ A B hA hB c φ hφ _ t₂ ht₂
  · exact hr

end Coinvariants

section Consumers
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- The remaining product obligation after the coefficient estimates: two
monic equations for the actual raw trace array, over a regular coefficient
algebra. This predicate does not assert their existence for arbitrary data. -/
def ProductEulerEquations (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ) : Prop :=
  let f := ofArray (productLevelCoeff Y₁ Y₂ w₁ w₂ α₁ α₂)
  ∃ lam mu : ℂ,
    MonicEquation bidiscAlgebra (fun n _ => lam + n) f ∧
    MonicEquation bidiscAlgebra (fun n k => mu + (n : ℂ) - k) f

/-- Product-chart regularity is automatic once these monic equations exist. -/
theorem productSeparateFuchsian_of_eulerEquations
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ)
    (h : ProductEulerEquations Y₁ Y₂ w₁ w₂ α₁ α₂) :
    ProductSeparateFuchsian Y₁ Y₂ w₁ w₂ α₁ α₂ := by
  obtain ⟨lam, mu, h₁, h₂⟩ := h
  intro r hr
  have hs := separateSystem_of_monic bidiscAlgebra le_rfl lam mu 1 0 1 (-1) (by norm_num)
    (f := ofArray (productLevelCoeff Y₁ Y₂ w₁ w₂ α₁ α₂))
    (by simpa using h₁) (by simpa [sub_eq_add_neg, add_assoc] using h₂) hr
  simpa only [coeff_ofArray_fun] using hs

end Consumers
end VOA.Huang.GenusTwoPoint.Separate
