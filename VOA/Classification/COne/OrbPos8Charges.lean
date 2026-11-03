import VOA.Classification.COne.OrbPos8Heisenberg
import VOA.Moonshine.HeisenbergTwistedModuleReduction

/-! # Charge relations in arbitrary torus-twisted modules

The current-charge commutator below is extracted from the actual twisted
Jacobi identity, at arbitrary fractional charge modes. The vacuum energy
formula uses the actual conformal mode, via cyclic restriction.
-/

namespace VOA.Classification.COne.OrbPos8
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet HeisenbergN
open OrbPos2 DMCOne

section FixedCurrent
variable {V M : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {g : Aut W} {n : ℕ}

/-- A fixed current with a simple-pole OPE acts on every fractional mode
by the same charge commutator as in the untwisted case. -/
theorem fixed_current_comm (P : TwistedModule g n M) {h v : V}
    (hg : g h = h) (c : ℂ)
    (hv : ∀ i : ℕ, W.smul h i v = if i = 0 then c • v else 0)
    (p q : ℤ) (x : M) :
    P.YM h ((n : ℤ) * p) (P.YM v q x) -
      P.YM v q (P.YM h ((n : ℤ) * p) x) =
        c • P.YM v ((n : ℤ) * p + q) x := by
  have hJ := P.jacobi 0 h (mem_twistedEigenspace_zero hg) v x 0
    ((n : ℤ) * p) q (by simp)
  rw [finsum_eq_single _ (0 : ℤ) (fun i hi => by
    rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul]),
    finsum_eq_single _ (0 : ℕ) (fun i hi => by
      rw [zero_add, hv i, if_neg hi, map_zero]
      simp)] at hJ
  have hzero : W.smul h 0 v = c • v := by simpa using hv 0
  simpa [hzero, cbinom, negOnePow] using hJ

end FixedCurrent

section Energy
variable {V M : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- The normal-ordered current square on the Heisenberg vacuum space,
for an arbitrary weak module. -/
theorem module_normalOrder_on_vac (A : WeakModule W M) (h : V) {x : M}
    (hx : ∀ k : ℤ, 0 < k → mode (A.YM h) k x = 0) :
    mode (A.YM (W.smul h (-1) h)) 1 x =
      mode (A.YM h) 0 (mode (A.YM h) 0 x) := by
  rw [module_iterate0 A h h x (-1) 1,
    finsum_eq_single _ (0 : ℤ) (fun i hi => by
      rcases lt_or_ge i 0 with hneg | hpos
      · rw [cbz_apply_neg _ hneg, mul_zero, zero_smul]
      · rw [hx _ (by omega), hx _ (by omega), map_zero, map_zero,
          smul_zero, sub_zero, smul_zero])]
  rw [hx _ (by norm_num), map_zero]
  simp [negOnePow]

/-- With the lattice conformal vector, the vacuum-space energy is exactly
half the square of the current zero mode. -/
theorem module_L0_on_vac (A : WeakModule W M) (h : V)
    (hω : W.conformalVector = omegaH W h) {x : M}
    (hx : ∀ k : ℤ, 0 < k → mode (A.YM h) k x = 0) :
    mode (A.YM W.conformalVector) 1 x =
      (1 / 2 : ℂ) • mode (A.YM h) 0 (mode (A.YM h) 0 x) := by
  rw [hω, omegaH, map_smul, mode_smul, LinearMap.smul_apply,
    module_normalOrder_on_vac A h hx]

end Energy

section Torus
variable {M : Type} [AddCommGroup M] [Module ℂ M] {u : ℂˣ} {n : ℕ}

/-- The charged lattice states shift the current charge in every torus-twisted
module; the second mode index is genuinely fractional. -/
theorem torus_charge_comm (P : TwistedModule (charU 1 le_rfl u) n M)
    (β p q : ℤ) (x : M) :
    P.YM (hb 1) ((n : ℤ) * p) (P.YM (latChargeGen (latP 1) β) q x) -
      P.YM (latChargeGen (latP 1) β) q (P.YM (hb 1) ((n : ℤ) * p) x) =
      chargeCoord (latP 1) β (LatMod.a0 1) •
        P.YM (latChargeGen (latP 1) β) ((n : ℤ) * p + q) x :=
  fixed_current_comm P (charU_hb u) _ (fun i => by
    simpa using hb_smul_charge 1 le_rfl β (Int.natCast_nonneg i)) p q x

/-- Every nonzero charged-mode image of a current eigenvector has the
predicted shifted eigenvalue, without any classification assumption. -/
theorem torus_charge_eigen (P : TwistedModule (charU 1 le_rfl u) n M)
    (β q : ℤ) {μ : ℂ} {x : M} (hx : P.YM (hb 1) 0 x = μ • x) :
    P.YM (hb 1) 0 (P.YM (latChargeGen (latP 1) β) q x) =
      (μ + chargeCoord (latP 1) β (LatMod.a0 1)) •
        P.YM (latChargeGen (latP 1) β) q x := by
  have hc := torus_charge_comm P β 0 q x
  simp only [mul_zero, zero_add, hx, map_smul] at hc
  rw [sub_eq_iff_eq_add] at hc
  rw [hc, add_smul]
  abel

/-- The energy formula holds on the vacuum space of every torus-twisted
module, not only for the explicitly constructed shifted family. -/
theorem torus_L0_on_vac (P : TwistedModule (charU 1 le_rfl u) n M) (hn : 0 < n)
    {x : M} (hx : x ∈ (torusHeisenberg P hn).vac) :
    P.YM (V2m 1 le_rfl).conformalVector n x =
      (1 / 2 : ℂ) • P.YM (hb 1) 0 (P.YM (hb 1) 0 x) := by
  let H : (orbifold (Subgroup.zpowers (charU 1 le_rfl u))).carrier :=
    ⟨hb 1, (mem_orbifold_zpowers_iff _ _).mpr (charU_hb u)⟩
  have hω : (orbifoldVOA (Subgroup.zpowers (charU 1 le_rfl u))).conformalVector =
      omegaH (orbifoldVOA (Subgroup.zpowers (charU 1 le_rfl u))) H := by
    apply Subtype.ext
    exact V2m_conformal_eq_omegaH 1 le_rfl
  have hv := module_L0_on_vac (cyclicRestriction P hn).toWeakModule H hω
    (fun k hk => (torusHeisenberg P hn).mem_vac.mp hx k hk)
  simpa only [cyclicRestriction, restrictedOrdModule, restrictedWeakModule,
    mode_restrictedFields, mul_one, mul_zero] using hv

/-- The conformal weight of a Heisenberg vacuum eigenvector is fixed by its charge. -/
theorem torus_vac_energy (P : TwistedModule (charU 1 le_rfl u) n M) (hn : 0 < n)
    {x : M} (hx : x ∈ (torusHeisenberg P hn).vac) {μ : ℂ}
    (hμ : P.YM (hb 1) 0 x = μ • x) :
    P.YM (V2m 1 le_rfl).conformalVector n x = (μ ^ 2 / 2) • x := by
  rw [torus_L0_on_vac P hn hx, hμ, map_smul, hμ, smul_smul, smul_smul]
  congr 1
  ring

end Torus
end VOA.Classification.COne.OrbPos8
