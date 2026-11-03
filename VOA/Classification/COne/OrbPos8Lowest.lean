import VOA.Classification.COne.OrbPos8Exceptional

/-! # Lowest-energy classification without isomorphism classification

Opposite charged fields move nonzero vacuum eigenvectors by both root steps.
Consequently the minimum energy of any nonzero ordinary inner-twisted module
is the minimum of one of the two constructed shifted lattice modules.
-/

namespace VOA.Classification.COne.OrbPos8
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet HeisenbergN
open OrbPos2 OrbPos3 OrbPos4 OrbPos5 LatMod

section Shift
variable {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} {a : ℤ}

/-- An actual nonzero Heisenberg vacuum eigenvector with the indicated charge. -/
def HasVacuumCharge (P : TwistedModule (shiftAut n a) n M) (hn : 0 < n) (b : ℤ) : Prop :=
  ∃ (μ : ℂ) (x : M), x ≠ 0 ∧ x ∈ (torusHeisenberg P hn).vac ∧
    P.YM (hb 1) 0 x = μ • x ∧ rootCoord * μ = (b : ℂ) - (a : ℂ) / n

private theorem signed_root_pair (β : ℤ) (hβ : β = 1 ∨ β = -1) :
    (V2m 1 le_rfl).smul (latChargeGen (latP 1) (-β)) 1
      (latChargeGen (latP 1) β) =
        latticeCocycle (latP 1) (-β) β • (V2m 1 le_rfl).vacuum := by
  rw [V2m_smul_neg_charge (m := 1) (hm := le_rfl) β 1]
  rcases hβ with rfl | rfl
  all_goals
    norm_num only
    rw [EEVec_vacuum, if_pos (by norm_num), Int.toNat_zero, vSchur_zero]
    rfl

private theorem signed_root_pair_high (β : ℤ) (hβ : β = 1 ∨ β = -1)
    (i : ℕ) (hi : 2 ≤ i) :
    (V2m 1 le_rfl).smul (latChargeGen (latP 1) (-β)) i
      (latChargeGen (latP 1) β) = 0 := by
  rw [V2m_smul_neg_charge (m := 1) (hm := le_rfl) β i, EEVec_vacuum]
  rcases hβ with rfl | rfl
  all_goals
    rw [if_neg (by omega)]
    simp [latStateGen]

/-- Both signs of the root field have a nonzero mode on every nonzero vector. -/
theorem shifted_signed_root_nonvanishing (P : TwistedModule (shiftAut n a) n M)
    (hn : 0 < n) (β : ℤ) (hβ : β = 1 ∨ β = -1) {x : M} (hx : x ≠ 0) :
    ∃ q : ℤ, P.YM (latChargeGen (latP 1) β) q x ≠ 0 :=
  twisted_field_nonvanishing (W := V2m 1 le_rfl) P hn _ _ _
    (shift_charge_eigen hn a (-β)) _ (LatMod.latticeCocycle_ne_zero _ _ _)
    (signed_root_pair β hβ) (signed_root_pair_high β hβ) hx

/-- Nonzero vacuum charges are closed under both lattice root steps. -/
theorem vacuumCharge_step (P : TwistedModule (shiftAut n a) n M) (hn : 0 < n)
    {b : ℤ} (hb : HasVacuumCharge P hn b) (β : ℤ) (hβ : β = 1 ∨ β = -1) :
    HasVacuumCharge P hn (b + 2 * β) := by
  obtain ⟨μ, x, hx0, hx, hμ, hcharge⟩ := hb
  obtain ⟨q, hq, htop⟩ := twisted_field_top P _ x
    (shifted_signed_root_nonvanishing P hn β hβ hx0)
  refine ⟨μ + chargeCoord (latP 1) β (a0 1), P.YM (latChargeGen (latP 1) β) q x,
    hq, torus_charge_top_vac P hn β q hx htop, torus_charge_eigen P β q hμ, ?_⟩
  have hroot : rootCoord * chargeCoord (latP 1) β (a0 1) = 2 * (β : ℂ) := by
    rcases hβ with rfl | rfl
    · change rootCoord * rootCoord = 2 * ((1 : ℤ) : ℂ)
      norm_num only [Int.cast_one, mul_one]
      linear_combination rootCoord_sq
    · have hneg : chargeCoord (latP 1) (-1 : ℤ) (a0 1) = -rootCoord :=
        chargeCoord_neg (latP 1) (1 : ℤ) (a0 1)
      rw [hneg]
      change rootCoord * -rootCoord = 2 * ((-1 : ℤ) : ℂ)
      norm_num only [Int.cast_neg, Int.cast_one]
      linear_combination -rootCoord_sq
  rw [mul_add, hcharge, hroot]
  push_cast
  ring

theorem vacuumCharge_translate (P : TwistedModule (shiftAut n a) n M) (hn : 0 < n)
    {b : ℤ} (hb : HasVacuumCharge P hn b) (k : ℤ) : HasVacuumCharge P hn (b + 2 * k) := by
  induction k using Int.induction_on with
  | zero => simpa using hb
  | succ k ih =>
    rw [show b + 2 * ((k : ℤ) + 1) = (b + 2 * k) + 2 * 1 by ring]
    exact vacuumCharge_step P hn ih 1 (Or.inl rfl)
  | pred k ih =>
    rw [show b + 2 * (-(k : ℤ) - 1) = (b + 2 * -k) + 2 * (-1) by ring]
    exact vacuumCharge_step P hn ih (-1) (Or.inr rfl)

/-- Every realized vacuum-charge orbit contains its parity representative. -/
theorem vacuumCharge_normalize (P : TwistedModule (shiftAut n a) n M) (hn : 0 < n)
    {b : ℤ} (hb : HasVacuumCharge P hn b) : HasVacuumCharge P hn (b % 2) := by
  have h := vacuumCharge_translate P hn hb (-(b / 2))
  convert h using 1
  have := Int.emod_add_mul_ediv b 2
  omega

private theorem charge_energy {μ : ℂ} {b : ℤ}
    (hb : rootCoord * μ = (b : ℂ) - (a : ℂ) / n) :
    μ ^ 2 / 2 = (innerEnergy n a b 0 0 : ℂ) := by
  have hsq : 2 * μ ^ 2 = ((b : ℂ) - (a : ℂ) / n) ^ 2 := by
    calc
      _ = (rootCoord * μ) ^ 2 := by rw [mul_pow, rootCoord_sq]
      _ = _ := by rw [hb]
  simp only [innerEnergy]
  push_cast
  calc
    _ = ((b : ℂ) - (a : ℂ) / n) ^ 2 / 4 := by linear_combination hsq / 4
    _ = _ := by ring

/-- Each vacuum charge is an actually realized conformal energy. -/
theorem vacuumCharge_weight (P : TwistedModule (shiftAut n a) n M) (hn : 0 < n)
    {b : ℤ} (hb : HasVacuumCharge P hn b) :
    P.weight (innerEnergy n a b 0 0 : ℂ) ≠ ⊥ := by
  obtain ⟨μ, x, hx0, hx, hμ, hcharge⟩ := hb
  have he := torus_vac_energy P hn hx hμ
  rw [charge_energy hcharge] at he
  have hm : x ∈ P.weight (innerEnergy n a b 0 0 : ℂ) := by
    apply eigenvector_mem_weight (cyclicRestriction P hn)
    change mode (restrictedFields P _ _) 1 x = _
    rw [mode_restrictedFields, mul_one]
    exact he
  intro hz
  rw [hz, Submodule.mem_bot] at hm
  exact hx0 hm

/-- Below every realized weight is a realized ground energy of one of the
two parity representatives. This also proves that the spectral bound is attained. -/
theorem shifted_weight_has_ground_below (P : TwistedModule (shiftAut n a) n M)
    (hn : 0 < n) (ha : 0 ≤ a) (han : a ≤ n) {α : ℂ} (hα : P.weight α ≠ ⊥) :
    ∃ ε : ℤ, (ε = 0 ∨ ε = 1) ∧ P.weight (innerEnergy n a ε 0 0 : ℂ) ≠ ⊥ ∧
      (innerEnergy n a ε 0 0 : ℝ) ≤ α.re := by
  obtain ⟨r, hr, hle⟩ := torus_weight_has_vac_below P hn hα
  obtain ⟨μ, x, hx0, hx, hμ, hE⟩ := torus_vac_weight_charge P hn hr hle
  obtain ⟨b, hb⟩ := shifted_vac_charge_quantized P hn hx0 hx hμ
  have hv : HasVacuumCharge P hn b := ⟨μ, x, hx0, hx, hμ, hb⟩
  have hε : b % 2 = 0 ∨ b % 2 = 1 := by omega
  refine ⟨b % 2, hε, vacuumCharge_weight P hn (vacuumCharge_normalize P hn hv), ?_⟩
  rw [charge_energy hb] at hE
  have hre : α.re = (innerEnergy n a b 0 0 : ℝ) + r := by
    have := congrArg Complex.re hE
    simp only [Complex.sub_re, Complex.natCast_re, Complex.ratCast_re] at this
    linarith
  rw [hre, innerEnergy_normalize n a b 0 0]
  have hmin := innerEnergy_minimum hn ha han hε (0 + b / 2) 0
  have hminR : (innerEnergy n a (b % 2) 0 0 : ℝ) ≤
      (innerEnergy n a (b % 2) (0 + b / 2) 0 : ℝ) := by exact_mod_cast hmin
  exact hminR.trans (le_add_of_nonneg_right (Nat.cast_nonneg r))

end Shift

/-- An attained minimum of the real conformal energy. The spectral theorems
also prove that all weights under consideration are real. -/
def HasLowestEnergy {g : Aut (V2m 1 le_rfl)} {n : ℕ}
    {M : Type} [AddCommGroup M] [Module ℂ M] (P : TwistedModule g n M) (h : ℂ) : Prop :=
  P.weight h ≠ ⊥ ∧ ∀ α : ℂ, P.weight α ≠ ⊥ → h.re ≤ α.re

/-- Lowest-energy classification for every nonzero ordinary shifted module.
No isomorphism classification or uniform parity of its whole spectrum is asserted. -/
theorem shifted_lowest_energy {n : ℕ} {a : ℤ}
    {M : Type} [AddCommGroup M] [Module ℂ M] [Nontrivial M]
    (P : TwistedModule (shiftAut n a) n M) (hn : 0 < n) (ha : 0 ≤ a) (han : a ≤ n) :
    ∃ ε : ℤ, (ε = 0 ∨ ε = 1) ∧ HasLowestEnergy P (innerEnergy n a ε 0 0 : ℂ) := by
  have hbelow {α : ℂ} (hα : P.weight α ≠ ⊥) :=
    shifted_weight_has_ground_below P hn ha han hα
  have hsome : ∃ ε : ℤ, (ε = 0 ∨ ε = 1) ∧
      P.weight (innerEnergy n a ε 0 0 : ℂ) ≠ ⊥ := by
    obtain ⟨α, hα⟩ := (cyclicRestriction P hn).exists_weight_ne_bot inferInstance
    obtain ⟨ε, hε, he, _⟩ := hbelow hα
    exact ⟨ε, hε, he⟩
  by_cases h0 : P.weight (innerEnergy n a 0 0 0 : ℂ) ≠ ⊥
  · by_cases h1 : P.weight (innerEnergy n a 1 0 0 : ℂ) ≠ ⊥
    · rcases le_total (innerEnergy n a 0 0 0 : ℝ) (innerEnergy n a 1 0 0 : ℝ) with h | h
      · refine ⟨0, Or.inl rfl, h0, fun α hα => ?_⟩
        obtain ⟨ε, hε, _, he⟩ := hbelow hα
        simp only [Complex.ratCast_re]
        rcases hε with rfl | rfl
        · exact he
        · exact h.trans he
      · refine ⟨1, Or.inr rfl, h1, fun α hα => ?_⟩
        obtain ⟨ε, hε, _, he⟩ := hbelow hα
        simp only [Complex.ratCast_re]
        rcases hε with rfl | rfl
        · exact h.trans he
        · exact he
    · refine ⟨0, Or.inl rfl, h0, fun α hα => ?_⟩
      obtain ⟨ε, hε, hreal, he⟩ := hbelow hα
      rcases hε with rfl | rfl
      · simpa only [Complex.ratCast_re] using he
      · exact (h1 hreal).elim
  · obtain ⟨ε, hε, he⟩ := hsome
    rcases hε with rfl | rfl
    · exact (h0 he).elim
    · refine ⟨1, Or.inr rfl, he, fun α hα => ?_⟩
      obtain ⟨ε, hε, hreal, hle⟩ := hbelow hα
      rcases hε with rfl | rfl
      · exact (h0 hreal).elim
      · simpa only [Complex.ratCast_re] using hle

/-- Each constructed module realizes exactly its advertised minimum. -/
theorem constructed_lowest_energy {n : ℕ} (hn : 0 < n) {a ε : ℤ}
    (ha : 0 ≤ a) (han : a ≤ n) (hε : ε = 0 ∨ ε = 1) :
    HasLowestEnergy (OrbPos7.latticeShiftedTwistedModule hn a ε)
      (innerEnergy n a ε 0 0 : ℂ) := by
  change energyGrade n a ε (innerEnergy n a ε 0 0 : ℂ) ≠ ⊥ ∧
    ∀ α : ℂ, energyGrade n a ε α ≠ ⊥ → (innerEnergy n a ε 0 0 : ℂ).re ≤ α.re
  simp only [energyGrade_eq_eigenspace, Complex.ratCast_re]
  exact energyOperator_lowest hn ha han hε

/-- Every nonzero ordinary module at a normalized inner angle has the same
attained lowest energy as one of the two unconditionally constructed modules. -/
theorem shifted_lowest_matches_constructed {n : ℕ} {a : ℤ}
    {M : Type} [AddCommGroup M] [Module ℂ M] [Nontrivial M]
    (P : TwistedModule (shiftAut n a) n M) (hn : 0 < n) (ha : 0 ≤ a) (han : a ≤ n) :
    ∃ ε : ℤ, (ε = 0 ∨ ε = 1) ∧
      HasLowestEnergy P (innerEnergy n a ε 0 0 : ℂ) ∧
      HasLowestEnergy (OrbPos7.latticeShiftedTwistedModule hn a ε)
        (innerEnergy n a ε 0 0 : ℂ) := by
  obtain ⟨ε, hε, h⟩ := shifted_lowest_energy P hn ha han
  exact ⟨ε, hε, h, constructed_lowest_energy hn ha han hε⟩

/-- Lowest-energy classification for every irreducible nonidentity finite-order
V₂-twisted module. This includes all exceptional orders, and in fact every
positive finite order. The angle is chosen after torus conjugation. -/
theorem inner_twisted_lowest_matches_constructed
    {g : Aut (V2m 1 le_rfl)} {n : ℕ} (hn : 0 < n) (ho : orderOf g = n) (hg : g ≠ 1)
    {M : Type} [AddCommGroup M] [Module ℂ M] (P : TwistedModule g n M)
    (hi : TwistedIrreducible P) :
    ∃ (a ε : ℤ), 0 < a ∧ a < n ∧ orderOf (shiftAut n a) = n ∧ (ε = 0 ∨ ε = 1) ∧
      HasLowestEnergy P (innerEnergy n a ε 0 0 : ℂ) ∧
      HasLowestEnergy (OrbPos7.latticeShiftedTwistedModule hn a ε)
        (innerEnergy n a ε 0 0 : ℂ) := by
  haveI : Nontrivial M := hi.1
  obtain ⟨u, Q, hQord, _, hQweight⟩ := v2_twisted_torus_reduction hn ho P hi
  have hu : charU 1 le_rfl u ≠ 1 := by
    intro h
    have hn1 : n = 1 := by simpa [h] using hQord.symm
    exact hg (orderOf_eq_one_iff.mp (ho.trans hn1))
  obtain ⟨a, ha, han, he⟩ := torus_eq_shiftAut u hn
    (by rw [← hQord]; exact pow_orderOf_eq_one _) hu
  obtain ⟨ε, hε, hP, hmodel⟩ :=
    shifted_lowest_matches_constructed (castTwisted he Q) hn ha.le han.le
  refine ⟨a, ε, ha, han, he ▸ hQord, hε, ?_, hmodel⟩
  simpa only [HasLowestEnergy, castTwisted_weight, hQweight] using hP

/-- The zero angle is the identity automorphism. -/
theorem shiftAut_zero (n : ℕ) : shiftAut n 0 = 1 := by
  have hu : torusUnit n 0 = 1 := by
    apply Units.ext
    simp [torusUnit, phase]
  rw [shiftAut, hu, map_one]
  rfl

/-- All finite-order sectors, including the identity: every irreducible ordinary
twisted module has the same attained lowest energy as a constructed module. -/
theorem finite_order_twisted_lowest_matches_constructed
    {g : Aut (V2m 1 le_rfl)} {n : ℕ} (hn : 0 < n) (ho : orderOf g = n)
    {M : Type} [AddCommGroup M] [Module ℂ M] (P : TwistedModule g n M)
    (hi : TwistedIrreducible P) :
    ∃ (a ε : ℤ), 0 ≤ a ∧ a < n ∧ orderOf (shiftAut n a) = n ∧ (ε = 0 ∨ ε = 1) ∧
      HasLowestEnergy P (innerEnergy n a ε 0 0 : ℂ) ∧
      HasLowestEnergy (OrbPos7.latticeShiftedTwistedModule hn a ε)
        (innerEnergy n a ε 0 0 : ℂ) := by
  by_cases hg : g = 1
  · haveI : Nontrivial M := hi.1
    have he : g = shiftAut n 0 := hg.trans (shiftAut_zero n).symm
    obtain ⟨ε, hε, hP, hmodel⟩ := shifted_lowest_matches_constructed
      (castTwisted he P) hn (by omega) (by omega)
    refine ⟨0, ε, le_rfl, by omega, he ▸ ho, hε, ?_, hmodel⟩
    simpa only [HasLowestEnergy, castTwisted_weight] using hP
  · obtain ⟨a, ε, ha, han, hord, hε, hP, hmodel⟩ :=
      inner_twisted_lowest_matches_constructed hn ho hg P hi
    exact ⟨a, ε, ha.le, han, hord, hε, hP, hmodel⟩

end VOA.Classification.COne.OrbPos8
