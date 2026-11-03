import VOA.Huang.GenusOneG1ProductGrowth

/-!
# A-cycle and B-cycle transport of the genus-one product channel

The genus-one two-point product trace `Tr_N Y₁(x,z₁) Y₂(y,z₂) q^{L₀ − c/24}` is
multivalued in `z₁, z₂`. On the universal cover it is the single-valued function
`prodLift Y₁ Y₂ x y α₁ α₂ ℓ₁ ℓ₂ τ` of the logarithms `ℓᵢ = log zᵢ`, the double sum
over the traced level `n` (of `N`) and the intermediate level `k` (of `Q`) of
`τ(n,k) e^{ℓ₁(−s−1)} e^{ℓ₂(−r−1)} e^{2πiτ(h_N − c/24 + n)}`, where `s, r` are the
modes carrying the levels. It is absolutely convergent on Huang's region
`|q| e^{Re ℓ₁} < e^{Re ℓ₂} < e^{Re ℓ₁}` (`summable_liftTerm`, from the double
convergence `phi_mem_Sub2`), and at `ℓᵢ = log zᵢ` it is the library's product
sewing sum (`liftTerm_log_eq`).

* **A-cycle** (`prodLift_acycle_left`, `prodLift_acycle_right`): `ℓ₁ ↦ ℓ₁ + 2πi`
  multiplies the product channel by `e^{2πi(h_N − h_Q − α₁)}`; `ℓ₂ ↦ ℓ₂ + 2πi` by
  `e^{2πi(h_Q − h_N − α₂)}`. Exact, termwise.
* **B-cycle** (`prodLift_bcycle`): `ℓ₁ ↦ ℓ₁ + 2πiτ` (i.e. `z₁ ↦ q z₁`) turns the
  product channel with traced module `N` and intermediate `Q` into the product
  channel with traced module `Q` and intermediate `N` (insertions in the opposite
  order), times `e^{−2πiτα₁}` (`q^{L₀}`-conjugation of `Y₁` and trace cyclicity,
  Huang 2008 Lemma 4.2, the genus-one input of (4.11)). The formal content is
  `tauZ_swap`; the evaluated identity is a reindexing of one absolutely
  convergent double sum.

What is NOT here: the passage between product and iterate channels (genus-zero
associativity on the overlap, which needs the iterate-channel convergence), and the
identification of the resulting matrices with `transferMatrix`.
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open VOA Module Complex
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

section Lift
variable (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
  (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)

/-- The `(n,k)` term of the product channel on the universal cover. -/
def liftTerm (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ ℓ₁ ℓ₂ τ : ℂ) (p : ℕ × ℕ) : ℂ :=
  tauZ Y₁ Y₂ x y α₁ α₂ p.1 p.2 * exp (ℓ₁ * (-sMode N Q α₁ p.1 p.2 - 1)) *
    exp (ℓ₂ * (-rMode N Q α₂ p.1 p.2 - 1)) *
    exp (2 * (Real.pi : ℂ) * I * τ * (N.h - W.centralCharge / 24 + p.1))

/-- The product channel on the universal cover. -/
def prodLift (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ ℓ₁ ℓ₂ τ : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, liftTerm Y₁ Y₂ x y α₁ α₂ ℓ₁ ℓ₂ τ p

theorem liftTerm_eq_exp (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ ℓ₁ ℓ₂ τ : ℂ) (p : ℕ × ℕ) :
    liftTerm Y₁ Y₂ x y α₁ α₂ ℓ₁ ℓ₂ τ p = tauZ Y₁ Y₂ x y α₁ α₂ p.1 p.2 *
      exp (ℓ₁ * (-sMode N Q α₁ p.1 p.2 - 1) + ℓ₂ * (-rMode N Q α₂ p.1 p.2 - 1) +
        2 * (Real.pi : ℂ) * I * τ * (N.h - W.centralCharge / 24 + p.1)) := by
  rw [liftTerm, exp_add, exp_add]; ring

/-- A-cycle of the first insertion: a scalar phase. -/
theorem liftTerm_acycle_left (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ ℓ₁ ℓ₂ τ : ℂ)
    (p : ℕ × ℕ) :
    liftTerm Y₁ Y₂ x y α₁ α₂ (ℓ₁ + 2 * (Real.pi : ℂ) * I) ℓ₂ τ p =
      exp (2 * (Real.pi : ℂ) * I * (N.h - Q.h - α₁)) * liftTerm Y₁ Y₂ x y α₁ α₂ ℓ₁ ℓ₂ τ p := by
  rw [liftTerm_eq_exp, liftTerm_eq_exp]
  have h : exp ((ℓ₁ + 2 * (Real.pi : ℂ) * I) * (-sMode N Q α₁ p.1 p.2 - 1) +
        ℓ₂ * (-rMode N Q α₂ p.1 p.2 - 1) +
        2 * (Real.pi : ℂ) * I * τ * (N.h - W.centralCharge / 24 + p.1)) =
      exp (2 * (Real.pi : ℂ) * I * (N.h - Q.h - α₁)) *
        exp (((((p.1 : ℤ) - p.2 : ℤ)) : ℂ) * (2 * (Real.pi : ℂ) * I)) *
        exp (ℓ₁ * (-sMode N Q α₁ p.1 p.2 - 1) + ℓ₂ * (-rMode N Q α₂ p.1 p.2 - 1) +
          2 * (Real.pi : ℂ) * I * τ * (N.h - W.centralCharge / 24 + p.1)) := by
    rw [← exp_add, ← exp_add]
    congr 1
    unfold sMode
    push_cast
    ring
  rw [h, exp_int_mul_two_pi_mul_I, mul_one]
  ring

/-- A-cycle of the second insertion: a scalar phase. -/
theorem liftTerm_acycle_right (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ ℓ₁ ℓ₂ τ : ℂ)
    (p : ℕ × ℕ) :
    liftTerm Y₁ Y₂ x y α₁ α₂ ℓ₁ (ℓ₂ + 2 * (Real.pi : ℂ) * I) τ p =
      exp (2 * (Real.pi : ℂ) * I * (Q.h - N.h - α₂)) * liftTerm Y₁ Y₂ x y α₁ α₂ ℓ₁ ℓ₂ τ p := by
  rw [liftTerm_eq_exp, liftTerm_eq_exp]
  have h : exp (ℓ₁ * (-sMode N Q α₁ p.1 p.2 - 1) +
        (ℓ₂ + 2 * (Real.pi : ℂ) * I) * (-rMode N Q α₂ p.1 p.2 - 1) +
        2 * (Real.pi : ℂ) * I * τ * (N.h - W.centralCharge / 24 + p.1)) =
      exp (2 * (Real.pi : ℂ) * I * (Q.h - N.h - α₂)) *
        exp (((((p.2 : ℤ) - p.1 : ℤ)) : ℂ) * (2 * (Real.pi : ℂ) * I)) *
        exp (ℓ₁ * (-sMode N Q α₁ p.1 p.2 - 1) + ℓ₂ * (-rMode N Q α₂ p.1 p.2 - 1) +
          2 * (Real.pi : ℂ) * I * τ * (N.h - W.centralCharge / 24 + p.1)) := by
    rw [← exp_add, ← exp_add]
    congr 1
    unfold rMode
    push_cast
    ring
  rw [h, exp_int_mul_two_pi_mul_I, mul_one]
  ring

/-- **B-cycle, termwise**: `z₁ ↦ q z₁` turns the `(N,Q)` product channel into the
`(Q,N)` product channel with the insertions in the opposite order. -/
theorem liftTerm_bcycle {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) (ℓ₁ ℓ₂ τ : ℂ) (p : ℕ × ℕ) :
    liftTerm Y₂ Y₁ y x α₂ α₁ ℓ₂ (ℓ₁ + 2 * (Real.pi : ℂ) * I * τ) τ p.swap =
      exp (-(2 * (Real.pi : ℂ) * I * τ * α₁)) * liftTerm Y₁ Y₂ x y α₁ α₂ ℓ₁ ℓ₂ τ p := by
  rw [liftTerm_eq_exp, liftTerm_eq_exp, Prod.fst_swap, Prod.snd_swap,
    tauZ_swap Y₁ Y₂ hx hy p.2 p.1]
  have h : exp (ℓ₂ * (-sMode Q N α₂ p.2 p.1 - 1) +
        (ℓ₁ + 2 * (Real.pi : ℂ) * I * τ) * (-rMode Q N α₁ p.2 p.1 - 1) +
        2 * (Real.pi : ℂ) * I * τ * (Q.h - W.centralCharge / 24 + p.2)) =
      exp (-(2 * (Real.pi : ℂ) * I * τ * α₁)) *
        exp (ℓ₁ * (-sMode N Q α₁ p.1 p.2 - 1) + ℓ₂ * (-rMode N Q α₂ p.1 p.2 - 1) +
          2 * (Real.pi : ℂ) * I * τ * (N.h - W.centralCharge / 24 + p.1)) := by
    rw [← exp_add]
    congr 1
    unfold sMode rMode
    push_cast
    ring
  rw [h]
  ring

/-- **A-cycle of the product channel** (first insertion). -/
theorem prodLift_acycle_left (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ ℓ₁ ℓ₂ τ : ℂ) :
    prodLift Y₁ Y₂ x y α₁ α₂ (ℓ₁ + 2 * (Real.pi : ℂ) * I) ℓ₂ τ =
      exp (2 * (Real.pi : ℂ) * I * (N.h - Q.h - α₁)) * prodLift Y₁ Y₂ x y α₁ α₂ ℓ₁ ℓ₂ τ := by
  unfold prodLift
  rw [← tsum_mul_left]
  exact tsum_congr fun p => liftTerm_acycle_left Y₁ Y₂ x y α₁ α₂ ℓ₁ ℓ₂ τ p

/-- **A-cycle of the product channel** (second insertion). -/
theorem prodLift_acycle_right (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ ℓ₁ ℓ₂ τ : ℂ) :
    prodLift Y₁ Y₂ x y α₁ α₂ ℓ₁ (ℓ₂ + 2 * (Real.pi : ℂ) * I) τ =
      exp (2 * (Real.pi : ℂ) * I * (Q.h - N.h - α₂)) * prodLift Y₁ Y₂ x y α₁ α₂ ℓ₁ ℓ₂ τ := by
  unfold prodLift
  rw [← tsum_mul_left]
  exact tsum_congr fun p => liftTerm_acycle_right Y₁ Y₂ x y α₁ α₂ ℓ₁ ℓ₂ τ p

/-- **B-cycle of the product channel** (Huang 2008, Lemma 4.2, genus-one part of
(4.11)): `q^{L₀}`-conjugation and trace cyclicity. -/
theorem prodLift_bcycle {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) (ℓ₁ ℓ₂ τ : ℂ) :
    prodLift Y₂ Y₁ y x α₂ α₁ ℓ₂ (ℓ₁ + 2 * (Real.pi : ℂ) * I * τ) τ =
      exp (-(2 * (Real.pi : ℂ) * I * τ * α₁)) * prodLift Y₁ Y₂ x y α₁ α₂ ℓ₁ ℓ₂ τ := by
  unfold prodLift
  rw [← tsum_mul_left, ← (Equiv.prodComm ℕ ℕ).tsum_eq]
  exact tsum_congr fun p => liftTerm_bcycle Y₁ Y₂ hx hy ℓ₁ ℓ₂ τ p

/-- The level coefficients of `Phi` are the level traces. -/
theorem c2_Phi_homog {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) (n k : ℕ) :
    c2 (Phi Y₁ Y₂ x y) n k = tauZ Y₁ Y₂ x y α₁ α₂ n k := by
  rw [Phi_homog Y₁ Y₂ hx hy, phiH, c2_mk2]

/-- The term in geometric form. -/
theorem liftTerm_eq_geom (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ ℓ₁ ℓ₂ τ : ℂ) (p : ℕ × ℕ) :
    liftTerm Y₁ Y₂ x y α₁ α₂ ℓ₁ ℓ₂ τ p =
      exp (ℓ₁ * (N.h - Q.h - α₁) + ℓ₂ * (Q.h - N.h - α₂) +
          2 * (Real.pi : ℂ) * I * τ * (N.h - W.centralCharge / 24)) *
        (tauZ Y₁ Y₂ x y α₁ α₂ p.1 p.2 *
          (exp (2 * (Real.pi : ℂ) * I * τ) * exp (ℓ₁ - ℓ₂)) ^ p.1 * exp (ℓ₂ - ℓ₁) ^ p.2) := by
  rw [liftTerm_eq_exp, ← exp_add (2 * (Real.pi : ℂ) * I * τ) (ℓ₁ - ℓ₂), ← exp_nat_mul,
    ← exp_nat_mul]
  have h : exp (ℓ₁ * (N.h - Q.h - α₁) + ℓ₂ * (Q.h - N.h - α₂) +
          2 * (Real.pi : ℂ) * I * τ * (N.h - W.centralCharge / 24)) *
        (tauZ Y₁ Y₂ x y α₁ α₂ p.1 p.2 *
          exp ((p.1 : ℂ) * (2 * (Real.pi : ℂ) * I * τ + (ℓ₁ - ℓ₂))) *
          exp ((p.2 : ℂ) * (ℓ₂ - ℓ₁))) =
      tauZ Y₁ Y₂ x y α₁ α₂ p.1 p.2 *
        exp (ℓ₁ * (N.h - Q.h - α₁) + ℓ₂ * (Q.h - N.h - α₂) +
          2 * (Real.pi : ℂ) * I * τ * (N.h - W.centralCharge / 24) +
          (p.1 : ℂ) * (2 * (Real.pi : ℂ) * I * τ + (ℓ₁ - ℓ₂)) + (p.2 : ℂ) * (ℓ₂ - ℓ₁)) := by
    simp only [exp_add]; ring
  rw [h]
  congr 2
  unfold sMode rMode
  push_cast
  ring

/-- **Absolute convergence of the lifted product channel** on Huang's region. -/
theorem summable_liftTerm (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    (ℓ₁ ℓ₂ : ℂ) (τ : UpperHalfPlane) (hz : ℓ₂.re < ℓ₁.re)
    (hq : ‖qParam τ‖ * Real.exp ℓ₁.re < Real.exp ℓ₂.re) :
    Summable (liftTerm Y₁ Y₂ x y α₁ α₂ ℓ₁ ℓ₂ τ) := by
  set X : ℂ := exp (2 * (Real.pi : ℂ) * I * (τ : ℂ)) * exp (ℓ₁ - ℓ₂) with hX
  set T : ℂ := exp (ℓ₂ - ℓ₁) with hT
  have hXn : ‖X‖ < 1 := by
    have hq' : ‖exp (2 * (Real.pi : ℂ) * I * (τ : ℂ))‖ = ‖qParam τ‖ := rfl
    rw [hX, norm_mul, hq', norm_exp, sub_re, Real.exp_sub, mul_div_assoc',
      div_lt_one (Real.exp_pos _)]
    exact hq
  have hTn : ‖T‖ < 1 := by
    rw [hT, norm_exp, sub_re, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  -- a margin `a > 1` with `a‖X‖ < 1` and `a‖T‖ < 1`
  obtain ⟨a, ha, hmargin⟩ := GenusTwoPoint.exists_geometric_margin
    (le_trans (norm_nonneg _) (le_max_left ‖X‖ ‖T‖)) (max_lt hXn hTn)
  obtain ⟨C, hC⟩ := phi_mem_Sub2 Y₁ Y₂ hV i₁ i₂ iN x y a ha
  have hC0 := Geo2.const_nonneg hC
  have hbound : GenusTwoPoint.TwoLevelBound
      (fun n k => tauZ Y₁ Y₂ x y α₁ α₂ n k) C a a := by
    intro n k
    change ‖tauZ Y₁ Y₂ x y α₁ α₂ n k‖ ≤ C * a ^ n * a ^ k
    rw [← c2_Phi_homog Y₁ Y₂ hx hy, mul_assoc, ← pow_add]
    exact hC n k
  have hs := GenusTwoPoint.summable_twoLevel_of_bound hC0 (by linarith) (by linarith) hbound
    (x := X) (y := T)
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)) hmargin)
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)) hmargin)
  refine (hs.mul_left (exp (ℓ₁ * (N.h - Q.h - α₁) + ℓ₂ * (Q.h - N.h - α₂) +
      2 * (Real.pi : ℂ) * I * τ * (N.h - W.centralCharge / 24)))).congr fun p => ?_
  rw [liftTerm_eq_geom]

/-- At `ℓᵢ = log zᵢ` the lifted channel is the library's product sewing sum. -/
theorem liftTerm_log_eq {z₁ z₂ : ℂ} (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ : ℂ) (τ : UpperHalfPlane) (p : ℕ × ℕ) :
    liftTerm Y₁ Y₂ x y α₁ α₂ (log z₁) (log z₂) τ p =
      GenusTwoPoint.productTerm Y₁ Y₂ x y α₁ α₂ (N.h + p.1) z₁ z₂ p.2 *
        GenusTwoPoint.qFactor N τ p.1 := by
  unfold liftTerm GenusTwoPoint.productTerm GenusTwoPoint.qFactor
  rw [cpow_def_of_ne_zero hz₁, cpow_def_of_ne_zero hz₂, qParam, ← exp_nat_mul]
  have hs : sMode N Q α₁ (p.1 : ℤ) (p.2 : ℤ) =
      (α₁ + α₂ - 2) - (α₂ + (N.h + p.1) - 1 - Q.h) + p.2 := by
    unfold sMode; push_cast; ring
  have hr : rMode N Q α₂ (p.1 : ℤ) (p.2 : ℤ) = (α₂ + (N.h + p.1) - 1 - Q.h) - p.2 := by
    unfold rMode; push_cast; ring
  have he : N.h - W.centralCharge / 24 + (((p.1 : ℤ)) : ℂ) =
      (N.h + p.1) - W.centralCharge / 24 := by push_cast; ring
  unfold tauZ lvl GenusTwoPoint.productModeTrace
  rw [hs, hr, he]
  have e3 : exp (2 * (Real.pi : ℂ) * I * (τ : ℂ) * (N.h - W.centralCharge / 24 + p.1)) =
      exp (2 * (Real.pi : ℂ) * I * (τ : ℂ) * (N.h - W.centralCharge / 24)) *
        exp ((p.1 : ℂ) * (2 * (Real.pi : ℂ) * I * (τ : ℂ))) := by
    rw [← exp_add]; congr 1; ring
  rw [e3]

end Lift

end VOA.Huang.GenusOneWard
