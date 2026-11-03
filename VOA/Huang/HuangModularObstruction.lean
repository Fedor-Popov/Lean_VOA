import VOA.Huang.HuangRigidAssembly
import VOA.Huang.SPinning

/-!
# Remark: a character-only `IsModularData` does not pin the `S`-matrix

A modular-data predicate that constrains the `S`-matrix only through
`S_transform` (`ch_a(−1/τ) = Σ_b S_ab ch_b(τ)`, characters = graded dimensions), the vacuum
row/column, and the bound `‖S_ab‖ ≤ S₀₀ d_a d_b`. That predicate is stated here as
`IsModularDataWeak`. Characters do **not** separate inequivalent modules: `ch_M = ch_{M'}` for a
module and its contragredient. So if `b ≠ b'` have equal characters (on `ℍ`), the entries
`S_ab`, `S_ab'` are only constrained through their sum and — away from the vacuum and with slack
in the bound — can be moved continuously (`perturbS`, `isModularDataWeak_perturbS`,
`weak_S_not_unique_of_witness`).

With that predicate, `HuangModularityInput` / `HuangRibbonNumericalInput` would be refutable from a
single witness (`SNonuniquenessWitness`; mathematically `V_{A₂} ⊗ L_{G₂,1}`): the categorical
`S̃` of the canonical model does not see `D.S` (`catS`, `perturb_pinned`), and three distinct
perturbations cannot fit the two values `S₀₀ S̃_ab`, `S₀₀ conj S̃_ab` (`not_three_in_pair`).

**Why `IsModularData` is not affected.** `IsModularData` carries `S_pinned : D.SPinned D.S` (Zhu's
`S`-law on ALL
one-point functions), and `S` is unique (`VOA.Huang.SPinning.S_unique_of_pinned`). The
perturbation argument does not apply to it: `not_isModularData_perturbS` proves that for a nice `W`
every nonzero perturbation `withS D (perturbS D a b b' t)` FAILS `IsModularData`. Consequently
the refutation does not apply to `HuangModularityInput`; what survives is the
statement about the weak predicate (`weak_S_not_unique_of_witness`).

## Status
No `sorry`, no new axioms.
-/

set_option linter.style.longLine false

noncomputable section

namespace VOA.Huang.HuangModular

open CategoryTheory VOA VOA.Classification.COne VOA.Huang.TensorCat
  VOA.Huang.TensorCat.RepPackaging VOA.Huang.HuangRigid

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## §0 The weak predicate (character-only `S`) -/

/-- **The old, character-only `IsModularData`** — every clause of the current predicate except
`S_pinned`. Kept as the record of the statement-level flaw: it does not determine `S`. -/
structure IsModularDataWeak (D : VOA.Classification.COne.ModularData W) : Prop where
  irred : ∀ a, (D.module a).IsIrreducible
  exhaust : ∀ (M : Type u) [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M),
    N.IsIrreducible → ∃ a, Nonempty (ModuleEquiv W N (D.module a))
  distinct : ∀ a b, Nonempty (ModuleEquiv W (D.module a) (D.module b)) → a = b
  vac_iso : Nonempty (ModuleEquiv W (D.module D.vac) (adjointModule W))
  weight_support : ∀ a (α : ℂ), (D.module a).weight α ≠ ⊥ → ∃ n : ℕ, α = (D.h a : ℂ) + n
  weight_lowest : ∀ a, (D.module a).weight (D.h a : ℂ) ≠ ⊥
  h_vac : D.h D.vac = 0
  char : ∀ a (τ : ℂ), 0 < τ.im →
    HasSum (fun n : ℕ => (Module.finrank ℂ ((D.module a).weight ((D.h a : ℂ) + n)) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * ((D.h a : ℂ) + n - W.centralCharge / 24) * τ))
      (D.ch a τ)
  char_vac : ∀ τ : ℂ, 0 < τ.im →
    HasSum (fun n : ℕ => (Module.finrank ℂ (W.grading n) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) - W.centralCharge / 24) * τ))
      (D.ch D.vac τ)
  S_transform : ∀ a (τ : ℂ), 0 < τ.im → D.ch a (-1 / τ) = ∑ b, D.S a b * D.ch b τ
  S00_pos : 0 < D.S00
  S_vac_vac : D.S D.vac D.vac = D.S00
  d_ge_one : ∀ a, 1 ≤ D.d a
  S_vac_left : ∀ a, D.S D.vac a = D.S00 * D.d a
  S_vac_right : ∀ a, D.S a D.vac = D.S00 * D.d a
  S_bound : ∀ a b, ‖D.S a b‖ ≤ D.S00 * D.d a * D.d b

/-- The current predicate implies the old one (it only adds `S_pinned`). -/
theorem IsModularData.toWeak {D : VOA.Classification.COne.ModularData W} (hD : D.IsModularData) :
    IsModularDataWeak D where
  irred := hD.irred
  exhaust := hD.exhaust
  distinct := hD.distinct
  vac_iso := hD.vac_iso
  weight_support := hD.weight_support
  weight_lowest := hD.weight_lowest
  h_vac := hD.h_vac
  char := hD.char
  char_vac := hD.char_vac
  S_transform := hD.S_transform
  S00_pos := hD.S00_pos
  S_vac_vac := hD.S_vac_vac
  d_ge_one := hD.d_ge_one
  S_vac_left := hD.S_vac_left
  S_vac_right := hD.S_vac_right
  S_bound := hD.S_bound

/-! ## §1 Replacing the `S`-matrix -/

/-- `D` with its `S`-matrix replaced by `S'` (all other data unchanged). -/
def withS (D : VOA.Classification.COne.ModularData W) (S' : D.ι → D.ι → ℂ) : VOA.Classification.COne.ModularData W :=
  { D with S := S' }

/-- The `S`-matrix moved by `t` along the `(a, b) / (a, b')` direction, keeping `S_ab + S_ab'`. -/
def perturbS (D : VOA.Classification.COne.ModularData W) (a b b' : D.ι) (t : ℂ) : D.ι → D.ι → ℂ :=
  fun x y => D.S x y + (if x = a ∧ y = b then t else 0) - (if x = a ∧ y = b' then t else 0)

theorem perturbS_apply_ab (D : VOA.Classification.COne.ModularData W) {a b b' : D.ι} (hbb : b ≠ b') (t : ℂ) :
    perturbS D a b b' t a b = D.S a b + t := by
  simp [perturbS, hbb]

theorem perturbS_apply_ab' (D : VOA.Classification.COne.ModularData W) {a b b' : D.ι} (hbb : b ≠ b') (t : ℂ) :
    perturbS D a b b' t a b' = D.S a b' - t := by
  simp [perturbS, Ne.symm hbb]

theorem perturbS_apply_of_ne (D : VOA.Classification.COne.ModularData W) {a b b' x : D.ι} (hx : x ≠ a) (t : ℂ) (y : D.ι) :
    perturbS D a b b' t x y = D.S x y := by
  simp [perturbS, hx]

theorem perturbS_apply_of_ne_right (D : VOA.Classification.COne.ModularData W) {a b b' y : D.ι} (hb : y ≠ b) (hb' : y ≠ b')
    (t : ℂ) (x : D.ι) : perturbS D a b b' t x y = D.S x y := by
  simp [perturbS, hb, hb']

/-- **The perturbed data still satisfy the weak (character-only) predicate.** This is the
statement-level flaw of a character-only modular-data predicate. -/
theorem isModularDataWeak_perturbS (D : VOA.Classification.COne.ModularData W) (hD : IsModularDataWeak D) {a b b' : D.ι}
    (hbb : b ≠ b') (ha : a ≠ D.vac) (hb : b ≠ D.vac) (hb' : b' ≠ D.vac)
    (hch : ∀ τ : ℂ, 0 < τ.im → D.ch b τ = D.ch b' τ) (t : ℂ)
    (hbd : ‖D.S a b + t‖ ≤ D.S00 * D.d a * D.d b)
    (hbd' : ‖D.S a b' - t‖ ≤ D.S00 * D.d a * D.d b') :
    IsModularDataWeak (withS D (perturbS D a b b' t)) where
  irred := hD.irred
  exhaust := hD.exhaust
  distinct := hD.distinct
  vac_iso := hD.vac_iso
  weight_support := hD.weight_support
  weight_lowest := hD.weight_lowest
  h_vac := hD.h_vac
  char := hD.char
  char_vac := hD.char_vac
  S_transform := by
    intro x τ hτ
    change D.ch x (-1 / τ) = ∑ y, perturbS D a b b' t x y * D.ch y τ
    rw [hD.S_transform x τ hτ]
    by_cases hx : x = a
    · rw [hx]
      simp only [perturbS, true_and, add_mul, sub_mul, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hch τ hτ]
      ring
    · exact Finset.sum_congr rfl fun y _ => by rw [perturbS_apply_of_ne D hx]
  S00_pos := hD.S00_pos
  S_vac_vac := by
    change perturbS D a b b' t D.vac D.vac = _
    rw [perturbS_apply_of_ne D (Ne.symm ha)]
    exact hD.S_vac_vac
  d_ge_one := hD.d_ge_one
  S_vac_left := fun x => by
    change perturbS D a b b' t D.vac x = _
    rw [perturbS_apply_of_ne D (Ne.symm ha)]
    exact hD.S_vac_left x
  S_vac_right := fun x => by
    change perturbS D a b b' t x D.vac = _
    rw [perturbS_apply_of_ne_right D (Ne.symm hb) (Ne.symm hb')]
    exact hD.S_vac_right x
  S_bound := by
    intro x y
    change ‖perturbS D a b b' t x y‖ ≤ D.S00 * D.d x * D.d y
    by_cases hx : x = a
    · rw [hx]
      by_cases hy : y = b
      · rw [hy, perturbS_apply_ab D hbb]; exact hbd
      · by_cases hy' : y = b'
        · rw [hy', perturbS_apply_ab' D hbb]; exact hbd'
        · rw [perturbS_apply_of_ne_right D hy hy']; exact hD.S_bound a y
    · rw [perturbS_apply_of_ne D hx]; exact hD.S_bound x y

/-! ## §2 The categorical side does not see the `S`-matrix -/

/-- The categorical `S̃` of the canonical model, for a choice of right duals. -/
def catS (hW : Nice W) (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData)
    (r : RightRigidCategory (canonicalModel hW D hD).C) (a b : D.ι) : ℂ :=
  letI := r
  letI := (canonicalModel hW D hD).fusion D hD
  ((canonicalModel hW D hD).ribbon (modelPivotal (canonicalModel hW D hD))
    (ribbonDualInput_of_nice hW (canonicalModel hW D hD) D hD)).sTilde a b

/-- (The hypothesis `hDt` is unsatisfiable for `t ≠ 0`
on a nice `W`, by `not_isModularData_perturbS`.)
`HuangModularityInput` pins `S_ab` of every perturbation to the TWO values
`S₀₀ S̃_ab`, `S₀₀ conj S̃_ab` of the unperturbed canonical model (the model, its duals and its
`S̃` are literally those of `D`). -/
theorem perturb_pinned (h : HuangModularityInput.{u}) {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    {W : VertexOperatorAlgebra 𝒱} (hW : Nice W) (D : VOA.Classification.COne.ModularData W)
    (hD : D.IsModularData) (r : RightRigidCategory (canonicalModel hW D hD).C)
    {a b b' : D.ι} (hbb : b ≠ b') (t : ℂ)
    (hDt : (withS D (perturbS D a b b' t)).IsModularData) :
    D.S a b + t = (D.S00 : ℂ) * catS hW D hD r a b ∨
      D.S a b + t = (D.S00 : ℂ) * star (catS hW D hD r a b) := by
  have key := (h 𝒱 W hW (withS D (perturbS D a b b' t)) hDt r).1 a b
  rw [← perturbS_apply_ab D hbb t]
  exact key

/-! ## §3 The refutation -/

/-- Three distinct values cannot all lie in a two-element set. -/
theorem not_three_in_pair {x₁ x₂ x₃ p q : ℂ} (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃)
    (h1 : x₁ = p ∨ x₁ = q) (h2 : x₂ = p ∨ x₂ = q) (h3 : x₃ = p ∨ x₃ = q) : False := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    first
    | exact h12 (h1.trans h2.symm)
    | exact h13 (h1.trans h3.symm)
    | exact h23 (h2.trans h3.symm)

/-- **A witness of non-uniqueness of the `S`-matrix in the weak predicate**: a nice `W` with
modular data `D`, a non-vacuum label `a`, two distinct non-vacuum labels `b ≠ b'` with the same
character on `ℍ` (e.g. `b' = b*`), and strict slack in the bound at `(a, b)` and `(a, b')`.
(Mathematically `V_{A₂} ⊗ L_{G₂,1}`; not constructed in the library.) -/
def SNonuniquenessWitness : Prop :=
  ∃ (𝒱 : Type u) (_ : AddCommGroup 𝒱) (_ : Module ℂ 𝒱) (W : VertexOperatorAlgebra 𝒱)
    (_ : Nice W) (D : VOA.Classification.COne.ModularData W) (_ : D.IsModularData)
    (a b b' : D.ι), b ≠ b' ∧ a ≠ D.vac ∧ b ≠ D.vac ∧ b' ≠ D.vac ∧
      (∀ τ : ℂ, 0 < τ.im → D.ch b τ = D.ch b' τ) ∧
      ‖D.S a b‖ < D.S00 * D.d a * D.d b ∧ ‖D.S a b'‖ < D.S00 * D.d a * D.d b'

/-- **The old predicate does not determine `S`**: from a witness, a second `S`-matrix
`S' ≠ D.S` on the same modules satisfies `IsModularDataWeak`. -/
theorem weak_S_not_unique_of_witness (hw : SNonuniquenessWitness.{u}) :
    ∃ (𝒱 : Type u) (_ : AddCommGroup 𝒱) (_ : Module ℂ 𝒱) (W : VertexOperatorAlgebra 𝒱)
      (_ : Nice W) (D : VOA.Classification.COne.ModularData W) (_ : D.IsModularData)
      (S' : D.ι → D.ι → ℂ), S' ≠ D.S ∧ IsModularDataWeak (withS D S') := by
  obtain ⟨𝒱, i1, i2, W, hW, D, hD, a, b, b', hbb, ha, hb, hb', hch, hs, hs'⟩ := hw
  set δ : ℝ := min (D.S00 * D.d a * D.d b - ‖D.S a b‖) (D.S00 * D.d a * D.d b' - ‖D.S a b'‖)
    with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ1 : δ ≤ D.S00 * D.d a * D.d b - ‖D.S a b‖ := min_le_left _ _
  have hδ2 : δ ≤ D.S00 * D.d a * D.d b' - ‖D.S a b'‖ := min_le_right _ _
  have hn : ‖((δ : ℝ) : ℂ)‖ = δ := by rw [Complex.norm_real, Real.norm_of_nonneg hδ0.le]
  refine ⟨𝒱, i1, i2, W, hW, D, hD, perturbS D a b b' (δ : ℂ), ?_,
    isModularDataWeak_perturbS D (IsModularData.toWeak hD) hbb ha hb hb' hch (δ : ℂ) ?_ ?_⟩
  · intro e
    have := congrFun (congrFun e a) b
    rw [perturbS_apply_ab D hbb] at this
    have h0 : ((δ : ℝ) : ℂ) = 0 := by linear_combination this
    exact hδ0.ne' (Complex.ofReal_eq_zero.mp h0)
  · calc ‖D.S a b + (δ : ℂ)‖ ≤ ‖D.S a b‖ + ‖(δ : ℂ)‖ := norm_add_le _ _
      _ ≤ _ := by rw [hn]; linarith
  · calc ‖D.S a b' - (δ : ℂ)‖ ≤ ‖D.S a b'‖ + ‖(δ : ℂ)‖ := norm_sub_le _ _
      _ ≤ _ := by rw [hn]; linarith

/-! ## §4 The fix closes the gap -/

/-- **After the S-pinning refactor, no nonzero perturbation is modular data** (nice `W`;
PBW via `VOA.pbw`): `withS D (perturbS D a b b' t)` has the same modules, weights and trace
functions as `D`, so its pinned `S` must equal `D.S` (`S_eq_of_pinned`), forcing `t = 0`. -/
theorem not_isModularData_perturbS (hW : Nice W) (D : VOA.Classification.COne.ModularData W)
    (hD : D.IsModularData) {a b b' : D.ι} (hbb : b ≠ b') {t : ℂ} (ht : t ≠ 0) :
    ¬ (withS D (perturbS D a b b' t)).IsModularData := by
  intro hDt
  have hpin : D.SPinned (perturbS D a b b' t) := hDt.S_pinned
  have he := VOA.Huang.SPinning.S_eq_of_pinned hW D hD hpin
  have := congrFun (congrFun he a) b
  rw [perturbS_apply_ab D hbb] at this
  exact ht (by linear_combination this)

end VOA.Huang.HuangModular
