import VOA.Huang.GenusOneG1eSeries
import VOA.Huang.GenusOneIntCoordVacuumTrace
import VOA.Huang.GenusOneSquareGrading

/-!
# Rows of the genus-one iterate, linearity of one-point functions, square weights

Step (5d) of the proof of (G1).

* `tfLin` — `traceFunction Y h · τ` is linear in the insertion vector (C₂, irreducible insertion);
* `iterF_hasSum_rows` — for ANY iterate channel (general inner module `Q`, outer intertwiner
  `Y₃`): `iterF = Σ_k z^{(h_Q + k) − α − β} · traceFunction Y₃ h_N (Y₄_{(α+β−1−h_Q−k)} x y) τ`,
  with absolute convergence (generalises `IntCoord.vacuum_iterF_eq_tsum_traceFun`);
* `mode_eq_zero_below` — modes landing below the lowest weight vanish;
* `eigen_sqL_nat` — an `L[0]`-eigenvector of a lowest-weight module is zero unless its
  eigenvalue lies in `h + ℕ`.
-/

noncomputable section

namespace VOA.Huang.GenusOneG1e

open VOA VOA.Huang Complex
open VOA.Huang.GenusOne (sqL traceFunction trace insertionSqWeight insertionBelow
  mem_insertionSqWeight insertion_sq_sub_surj sqL_zero_sub_mem_insertionBelow)
open VOA.Huang.GenusOneG1c (iterF)
open VOA.Huang.GenusTwoPoint (IterateSewingSummable iterateTerm qFactor iterateTerm_eq_onePoint)
open scoped BigOperators

universe u

section Lin

variable {V M₁ M : Type u} [AddCommGroup V] [Module ℂ V] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V} {A : OrdVModule W M₁}
  {N : OrdVModule W M}

/-- One-point functions are linear in the insertion vector. -/
def tfLin (hC2 : C2Cofinite W) (hA : A.IsIrreducible) (Y : IntertwiningOperator A N N) {h : ℂ}
    (hcw : HasConformalWeight N h) (τ : UpperHalfPlane) : M₁ →ₗ[ℂ] ℂ where
  toFun w := traceFunction Y h w τ
  map_add' w w' := by
    unfold traceFunction
    rw [map_add]
    exact qEvalAt_add
      (GenusOne.summable_trace_of_irreducible hC2 hA Y hcw (norm_qParam_lt_one τ) w).of_norm
      (GenusOne.summable_trace_of_irreducible hC2 hA Y hcw (norm_qParam_lt_one τ) w').of_norm
  map_smul' c w := by
    unfold traceFunction
    rw [map_smul, qEvalAt_smul]
    rfl

theorem tfLin_apply (hC2 : C2Cofinite W) (hA : A.IsIrreducible) (Y : IntertwiningOperator A N N)
    {h : ℂ} (hcw : HasConformalWeight N h) (τ : UpperHalfPlane) (w : M₁) :
    tfLin hC2 hA Y hcw τ w = traceFunction Y h w τ := rfl

theorem traceFunction_zero (Y : IntertwiningOperator A N N) (h : ℂ) (τ : UpperHalfPlane) :
    traceFunction Y h 0 τ = 0 := by
  unfold traceFunction
  rw [map_zero]
  simp [qEvalAt]

end Lin

section Rows

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- The conformal weight of a bundled lowest-weight module. -/
theorem LWModule.hasConformalWeight (N : LWModule W) : HasConformalWeight N.isMod N.h :=
  ⟨N.realized, N.isLow⟩

/-- One row of the iterate double series. -/
theorem iterate_row (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod) {x : P₁.carrier} {y : P₂.carrier}
    {α β : ℂ} (hx : x ∈ P₁.isMod.weight α) (hy : y ∈ P₂.isMod.weight β)
    (τ : UpperHalfPlane) (z : ℂ) (k : ℕ) :
    (∑' j : ℕ, iterateTerm Y₃ Y₄ x y α β (N.h + j) z 1 k * qFactor N τ j) =
      z ^ ((Q.h + k) - α - β) *
        traceFunction Y₃ N.h (Y₄.val ((α + β - 1 - Q.h) - k) x y) τ := by
  simp only [iterateTerm_eq_onePoint _ _ hx hy, Complex.one_cpow, mul_one]
  have he : -((α + β - 1 - Q.h) - (k : ℂ)) - 1 = (Q.h + k) - α - β := by ring
  rw [he]
  unfold traceFunction qEvalAt
  simp only [qFactor]
  have he' : ∀ j : ℕ, N.h + j - W.centralCharge / 24 = N.h - W.centralCharge / 24 + j := by
    intro j; ring
  simp only [he']
  rw [← tsum_mul_left, ← tsum_mul_left]
  exact tsum_congr fun j => by ring

/-- **Rows of a general iterate**, with absolute convergence. -/
theorem iterF_hasSum_rows (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod) {x : P₁.carrier} {y : P₂.carrier}
    {α β : ℂ} (hx : x ∈ P₁.isMod.weight α) (hy : y ∈ P₂.isMod.weight β)
    (τ : UpperHalfPlane) (z : ℂ) (hs : IterateSewingSummable Y₃ Y₄ x y α β z 1 τ) :
    HasSum (fun k : ℕ => z ^ ((Q.h + k) - α - β) *
        traceFunction Y₃ N.h (Y₄.val ((α + β - 1 - Q.h) - k) x y) τ)
      (iterF Y₃ Y₄ x y α β τ z) ∧
    Summable (fun k : ℕ => ‖z ^ ((Q.h + k) - α - β) *
        traceFunction Y₃ N.h (Y₄.val ((α + β - 1 - Q.h) - k) x y) τ‖) := by
  have hrow := iterate_row Y₃ Y₄ hx hy τ z
  have hn : Summable fun p : ℕ × ℕ =>
      ‖iterateTerm Y₃ Y₄ x y α β (N.h + p.1) z 1 p.2 * qFactor N τ p.1‖ :=
    summable_norm_iff.mpr hs
  refine ⟨?_, ?_⟩
  · have he : iterF Y₃ Y₄ x y α β τ z = ∑' k : ℕ, z ^ ((Q.h + k) - α - β) *
        traceFunction Y₃ N.h (Y₄.val ((α + β - 1 - Q.h) - k) x y) τ := by
      unfold iterF
      rw [hs.tsum_prod]
      rw [← Summable.tsum_comm (f := fun j k : ℕ =>
        iterateTerm Y₃ Y₄ x y α β (N.h + j) z 1 k * qFactor N τ j) hs]
      exact tsum_congr hrow
    rw [he]
    exact (hs.prod_symm.prod.congr hrow).hasSum
  · refine (hn.prod_symm.prod).of_nonneg_of_le (fun k => norm_nonneg _) fun k => ?_
    rw [← hrow k]
    exact norm_tsum_le_tsum_norm (hn.prod_symm.prod_factor k)

/-- A mode landing strictly below the lowest weight vanishes. -/
theorem mode_eq_zero_below (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    {x : P₁.carrier} {y : P₂.carrier} {α β : ℂ} (hx : x ∈ P₁.isMod.weight α)
    (hy : y ∈ P₂.isMod.weight β) (m : ℂ) (j : ℕ) (hj : α + β - m - 1 = Q.h - (j + 1)) :
    Y₄.val m x y = 0 := by
  have hmem := FusionTop.mem_weight Y₄.property hx hy m
  by_contra hne
  have hb : Q.isMod.weight (α + β - m - 1) ≠ ⊥ := fun hb => by
    rw [hb, Submodule.mem_bot] at hmem; exact hne hmem
  obtain ⟨n, hn⟩ := Q.isLow _ hb
  rw [hj] at hn
  have h' : ((n : ℂ) + j + 1) = 0 := by linear_combination -hn
  have h'' : (n + j + 1 : ℕ) = 0 := by exact_mod_cast h'
  omega

theorem iterF_zero_left (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod) {y : P₂.carrier} {α β : ℂ}
    (hy : y ∈ P₂.isMod.weight β) (τ : UpperHalfPlane) (z : ℂ) :
    iterF Y₃ Y₄ 0 y α β τ z = 0 := by
  unfold iterF
  have h0 : ∀ p : ℕ × ℕ, iterateTerm Y₃ Y₄ 0 y α β (N.h + p.1) z 1 p.2 * qFactor N τ p.1 = 0 := by
    intro p
    rw [iterateTerm_eq_onePoint _ _ (Submodule.zero_mem _) hy]
    simp
  simp [h0]

theorem iterF_zero_right (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod) {x : P₁.carrier} {α β : ℂ}
    (hx : x ∈ P₁.isMod.weight α) (τ : UpperHalfPlane) (z : ℂ) :
    iterF Y₃ Y₄ x 0 α β τ z = 0 := by
  unfold iterF
  have h0 : ∀ p : ℕ × ℕ, iterateTerm Y₃ Y₄ x 0 α β (N.h + p.1) z 1 p.2 * qFactor N τ p.1 = 0 := by
    intro p
    rw [iterateTerm_eq_onePoint _ _ hx (Submodule.zero_mem _)]
    simp
  simp [h0]

end Rows

section Square

variable {V M : Type u} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V}

theorem insertionBelow_le_natSqWeights (A : OrdVModule W M) {h : ℂ}
    (hlow : IsLowestWeight A h) :
    ∀ n, insertionBelow A h n ≤ ⨆ m : ℕ, insertionSqWeight A (h + m) := by
  intro n
  induction n with
  | zero => exact bot_le
  | succ n ih =>
    refine sup_le (fun x hx => ?_) ih
    obtain ⟨y, hy, he⟩ := insertion_sq_sub_surj A hlow n n le_rfl _
      (sqL_zero_sub_mem_insertionBelow A hlow hx)
    have heig : x - y ∈ insertionSqWeight A (h + n) := by
      rw [mem_insertionSqWeight, map_sub, smul_sub]
      linear_combination (norm := module) -he
    have hx' : x = (x - y) + y := by abel
    rw [hx']
    exact Submodule.add_mem _ (Submodule.mem_iSup_of_mem n heig) (ih hy)

theorem natSqWeights_eq_top (A : OrdVModule W M) {h : ℂ} (hlow : IsLowestWeight A h) :
    (⨆ m : ℕ, insertionSqWeight A (h + m)) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  refine FusionTop.induction_weight A x (Submodule.zero_mem _)
    (fun _ _ hx hy => Submodule.add_mem _ hx hy) ?_
  intro α y hy
  by_cases hb : A.weight α = ⊥
  · rw [hb, Submodule.mem_bot] at hy
    rw [hy]; exact Submodule.zero_mem _
  obtain ⟨n, rfl⟩ := hlow α hb
  exact insertionBelow_le_natSqWeights A hlow (n + 1) (Submodule.mem_sup_left hy)

/-- **`L[0]`-eigenvalues of a lowest-weight module lie in `h + ℕ`.** -/
theorem eigen_sqL_nat (A : OrdVModule W M) {h : ℂ} (hlow : IsLowestWeight A h) {v : M} {β : ℂ}
    (hv : sqL A 0 v = β • v) (hne : v ≠ 0) : ∃ n : ℕ, β = h + n := by
  by_contra hno
  push Not at hno
  apply hne
  have h1 : v ∈ insertionSqWeight A β := (mem_insertionSqWeight A β v).mpr hv
  have h2 : v ∈ ⨆ μ, ⨆ (_ : μ ≠ β), insertionSqWeight A μ := by
    have hv' : v ∈ ⨆ m : ℕ, insertionSqWeight A (h + m) := by
      rw [natSqWeights_eq_top A hlow]; exact Submodule.mem_top
    have hle : (⨆ m : ℕ, insertionSqWeight A (h + m)) ≤
        ⨆ μ, ⨆ (_ : μ ≠ β), insertionSqWeight A μ := iSup_le fun m =>
      le_iSup₂_of_le (f := fun μ (_ : μ ≠ β) => insertionSqWeight A μ) (h + m)
        (fun he => hno m he.symm) le_rfl
    exact hle hv'
  have hd := (Module.End.eigenspaces_iSupIndep (sqL A 0)) β
  exact (Submodule.disjoint_def.mp hd) v h1 h2

end Square

end VOA.Huang.GenusOneG1e
