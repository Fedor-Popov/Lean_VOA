import VOA.Classification.COne.OrbPos8Nonvanishing

/-! # A universal spectral bound for arbitrary inner-twisted modules

Each integral conformal-weight coset has a bottom, and positive Heisenberg
modes annihilate that bottom. A current eigenvector there has quantized charge.
This proves a spectral inclusion without assuming full module classification.
-/

namespace VOA.Classification.COne.OrbPos8
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet HeisenbergN
open OrbPos2 OrbPos5 DMCOne LatMod

variable {M : Type} [AddCommGroup M] [Module ℂ M] {u : ℂˣ} {n : ℕ}

theorem torus_current_mem_weight (P : TwistedModule (charU 1 le_rfl u) n M)
    (hn : 0 < n) {α : ℂ} {x : M} (hx : x ∈ P.weight α) (p : ℤ) :
    P.YM (hb 1) ((n : ℤ) * p) x ∈ P.weight (α - p) := by
  let H : (orbifold (Subgroup.zpowers (charU 1 le_rfl u))).carrier :=
    ⟨hb 1, (mem_orbifold_zpowers_iff _ _).mpr (charU_hb u)⟩
  have hh : H ∈ (orbifoldVOA (Subgroup.zpowers (charU 1 le_rfl u))).grading 1 :=
    hb_mem_grading 1 le_rfl
  have hm := mode_mem_weight (cyclicRestriction P hn) hh hx p
  norm_num only [Int.cast_one] at hm
  change mode (restrictedFields P _ H) p x ∈ P.weight (α + (1 : ℂ) - p - 1) at hm
  rw [mode_restrictedFields] at hm
  convert hm using 1
  congr 1
  ring

/-- Every realized weight lies a nonnegative integer above a nonzero weight
space entirely contained in the Heisenberg vacuum space. -/
theorem torus_weight_has_vac_below (P : TwistedModule (charU 1 le_rfl u) n M)
    (hn : 0 < n) {α : ℂ} (hα : P.weight α ≠ ⊥) :
    ∃ r : ℕ, P.weight (α - r) ≠ ⊥ ∧
      P.weight (α - r) ≤ (torusHeisenberg P hn).vac := by
  obtain ⟨B, hB⟩ := P.boundedBelow
  have hinh : ∃ k : ℤ, P.weight (α + k) ≠ ⊥ := ⟨0, by simpa using hα⟩
  have hbdd : ∃ b : ℤ, ∀ k : ℤ, P.weight (α + k) ≠ ⊥ → b ≤ k := by
    refine ⟨⌈B - α.re⌉, fun k hk => ?_⟩
    have hre := hB (α + k) hk
    simp only [Complex.add_re, Complex.intCast_re] at hre
    exact Int.ceil_le.mpr (by linarith)
  obtain ⟨k, hk, hmin⟩ := Int.exists_least_of_bdd hbdd hinh
  have hk0 : k ≤ 0 := hmin 0 (by simpa using hα)
  have hcast : (((-k).toNat : ℕ) : ℂ) = -(k : ℂ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega), Int.cast_neg]
  refine ⟨(-k).toNat, ?_, ?_⟩
  · simpa only [hcast, sub_neg_eq_add] using hk
  · rw [hcast, sub_neg_eq_add]
    intro x hx
    rw [HeisSvN.HeisRep.mem_vac]
    intro p hp
    rw [torusHeisenberg_a]
    have hw := torus_current_mem_weight P hn hx p
    have he : α + (k : ℂ) - p = α + ((k - p : ℤ) : ℂ) := by push_cast; ring
    rw [he] at hw
    have hz : P.weight (α + ((k - p : ℤ) : ℂ)) = ⊥ := by
      by_contra h
      have := hmin (k - p) h
      omega
    rwa [hz, Submodule.mem_bot] at hw

/-- A nonzero weight space contained in the vacuum space has an eigenvector
of the current zero mode, and its energy is half the charge square. -/
theorem torus_vac_weight_charge (P : TwistedModule (charU 1 le_rfl u) n M)
    (hn : 0 < n) {α : ℂ} (hα : P.weight α ≠ ⊥)
    (hle : P.weight α ≤ (torusHeisenberg P hn).vac) :
    ∃ (μ : ℂ) (x : M), x ≠ 0 ∧ x ∈ (torusHeisenberg P hn).vac ∧
      P.YM (hb 1) 0 x = μ • x ∧ α = μ ^ 2 / 2 := by
  haveI : FiniteDimensional ℂ (P.weight α) := P.finrank α
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα
  haveI : Nontrivial (P.weight α) :=
    ⟨⟨⟨y, hy⟩, 0, fun h => hy0 (congrArg Subtype.val h)⟩⟩
  let T : Module.End ℂ (P.weight α) :=
    (P.YM (hb 1) 0).restrict (fun _ hx => torus_zero_mem_weight P hn hx)
  obtain ⟨μ, hμ⟩ := T.exists_eigenvalue
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have he : P.YM (hb 1) 0 x.val = μ • x.val := congrArg Subtype.val hx.apply_eq_smul
  have hx0 : x.val ≠ 0 := fun hz => hx.2 (Subtype.ext hz)
  refine ⟨μ, x.val, hx0, hle x.property, he, ?_⟩
  have hE := torus_vac_energy P hn (hle x.property) he
  have hL : P.YM (V2m 1 le_rfl).conformalVector n x.val = α • x.val :=
    P.L0_weight α x.val x.property
  exact (smul_left_injective ℂ hx0) (hL.symm.trans hE)

/-- Every realized weight of every ordinary shifted-torus module has lattice
energy form. The integer coset label may depend on the weight; no exhaustion
or uniform parity statement is hidden in this theorem. -/
theorem shifted_weight_spectrum {a : ℤ} (P : TwistedModule (shiftAut n a) n M)
    (hn : 0 < n) {α : ℂ} (hα : P.weight α ≠ ⊥) :
    ∃ (b : ℤ) (r : ℕ), α = (innerEnergy n a b 0 r : ℂ) := by
  obtain ⟨r, hr, hle⟩ := torus_weight_has_vac_below P hn hα
  obtain ⟨μ, x, hx0, hx, hμ, hE⟩ := torus_vac_weight_charge P hn hr hle
  obtain ⟨b, hb⟩ := shifted_vac_charge_quantized P hn hx0 hx hμ
  have hsq : 2 * μ ^ 2 = ((b : ℂ) - (a : ℂ) / n) ^ 2 := by
    calc
      _ = (rootCoord * μ) ^ 2 := by rw [mul_pow, rootCoord_sq]
      _ = _ := by rw [hb]
  have he : μ ^ 2 / 2 = ((b : ℂ) / 2 - (a : ℂ) / (2 * n)) ^ 2 := by
    calc
      _ = ((b : ℂ) - (a : ℂ) / n) ^ 2 / 4 := by linear_combination hsq / 4
      _ = _ := by ring
  refine ⟨b, r, ?_⟩
  rw [he] at hE
  simp only [innerEnergy]
  push_cast
  linear_combination hE

/-- Universal positive gap, without irreducibility or a module-isomorphism
classification premise. -/
theorem shifted_weight_gap {a : ℤ} (P : TwistedModule (shiftAut n a) n M)
    (hn : 0 < n) (hn5 : n ≤ 5) (ha : 0 < a) (han : a < n)
    {α : ℂ} (hα : P.weight α ≠ ⊥) : (1 : ℝ) / 100 ≤ α.re := by
  obtain ⟨b, r, rfl⟩ := shifted_weight_spectrum P hn hα
  exact innerEnergy_gap hn5 ha han b 0 r

end VOA.Classification.COne.OrbPos8
