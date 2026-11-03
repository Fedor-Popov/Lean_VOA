import VOA.Classification.COne.OrbPos8Recursion
import VOA.Classification.COne.OrbPos7Module

/-! # Nonvanishing of charged fields and quantization of twisted vacuum charges

A nonzero second-order pole with an opposite charged state rules out a common
kernel for all modes. Two sufficiently high modes, separated by one integer
step, isolate the central term. This works in an arbitrary twisted module.
-/

namespace VOA.Classification.COne.OrbPos8
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet HeisenbergN
open OrbPos2 OrbPos5 DMCOne LatMod TwistedReduction
open scoped BigOperators

section General
variable {V M : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {g : Aut W} {n : ℕ}

/-- A nonzero second-order pole prevents the second field from annihilating
a nonzero vector at every mode. Only the first state's support is needed. -/
theorem twisted_field_nonvanishing (P : TwistedModule g n M) (hn : 0 < n)
    (j : ℕ) (v w : V) (hv : v ∈ g.twistedEigenspace n j)
    (c : ℂ) (hc : c ≠ 0) (hpair : W.smul v 1 w = c • W.vacuum)
    (hhigh : ∀ i : ℕ, 2 ≤ i → W.smul v i w = 0)
    {x : M} (hx : x ≠ 0) : ∃ q : ℤ, P.YM w q x ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨K, hK⟩ := P.truncation v x
  have hnZ : (0 : ℤ) < n := by omega
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hzero (k : ℤ) (hk : K ≤ k) (hkj : (k + j) % (n : ℤ) = 0) :
      P.YM (W.smul v 0 w) 0 x + ((k : ℂ) / n * c) • x = 0 := by
    have hJ := P.jacobi j v hv w x 0 k (-k) hkj
    rw [finsum_eq_single _ (0 : ℤ) (fun i hi => by
      rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul])] at hJ
    simp only [zero_mul, add_zero, sub_zero, zero_add, cbz_zero, mul_one,
      negOnePow, if_pos (Even.zero : Even (0 : ℤ)), one_smul] at hJ
    rw [h, hK k hk, map_zero, map_zero, sub_self] at hJ
    rw [finsum_nat_eq_sum_range 2 _ (fun i hi => by
      rw [hhigh i hi, map_zero]; simp)] at hJ
    have hc1 : cbinom ((k : ℂ) / n) 1 = (k : ℂ) / n := by simp [cbinom]
    simpa [Finset.sum_range_succ, hc1, hpair, P.vacuum_YM, smul_smul] using hJ.symm
  let k : ℤ := (n : ℤ) * ((K + j) / n + 1) - j
  have hk : K ≤ k := by
    have hdiv := Int.emod_add_mul_ediv (K + j) (n : ℤ)
    have hlt := Int.emod_lt_of_pos (K + j) hnZ
    dsimp [k]
    nlinarith
  have hkj : (k + j) % (n : ℤ) = 0 := by
    dsimp [k]
    rw [sub_add_cancel, Int.mul_emod_right]
  have hk' : K ≤ k + n := by omega
  have hkj' : (k + n + j) % (n : ℤ) = 0 := by
    rw [show k + (n : ℤ) + j = (k + j) + n by ring, Int.add_emod]
    simp [hkj]
  have h0 := hzero k hk hkj
  have h1 := hzero (k + n) hk' hkj'
  have he : ((k + n : ℤ) : ℂ) / n * c = (k : ℂ) / n * c + c := by
    push_cast
    field_simp
  rw [he, add_smul, ← add_assoc, h0, zero_add] at h1
  exact hx ((smul_eq_zero.mp h1).resolve_left hc)

/-- Nonvanishing and truncation give an actual top nonzero mode. -/
theorem twisted_field_top (P : TwistedModule g n M) (w : V) (x : M)
    (hne : ∃ q : ℤ, P.YM w q x ≠ 0) :
    ∃ q : ℤ, P.YM w q x ≠ 0 ∧ ∀ k : ℤ, q < k → P.YM w k x = 0 := by
  obtain ⟨K, hK⟩ := P.truncation w x
  obtain ⟨q, hq, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun k => P.YM w k x ≠ 0)
    ⟨K, fun k hk => by by_contra h; exact hk (hK k (by omega))⟩ hne
  refine ⟨q, hq, fun k hk => ?_⟩
  by_contra h
  have := hmax k h
  omega

end General

/-- Every charged state belongs to its specified torus eigenspace. -/
theorem shift_charge_eigen {n : ℕ} (hn : 0 < n) (a β : ℤ) :
    latChargeGen (latP 1) β ∈ (shiftAut n a).twistedEigenspace n
      ((-(a * β)) % (n : ℤ)).toNat := by
  rw [Aut.twistedEigenspace, Module.End.mem_eigenspace_iff]
  change shiftAut n a (latStateGen (latP 1) (vacuumN _) β) = _
  rw [shiftAut_latState]
  have hj : ((((-(a * β)) % (n : ℤ)).toNat : ℕ) : ℤ) = (-(a * β)) % (n : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have hp : phase n (a * β) = phase n (-(((-(a * β)) % (n : ℤ)).toNat : ℤ)) := by
    apply (phase_eq_iff hn _ _).mpr
    rw [hj, sub_neg_eq_add, Int.add_emod, Int.emod_emod, ← Int.add_emod]
    simp
  rw [hp]
  congr 1
  simp only [phase, Int.cast_neg, Int.cast_natCast]
  congr 1
  ring

private theorem root_pair :
    (V2m 1 le_rfl).smul (latChargeGen (latP 1) (-1 : ℤ)) 1
      (latChargeGen (latP 1) (1 : ℤ)) =
        latticeCocycle (latP 1) (-1 : ℤ) (1 : ℤ) • (V2m 1 le_rfl).vacuum := by
  rw [V2m_smul_neg_charge (m := 1) (hm := le_rfl) 1 1]
  norm_num only
  rw [EEVec_vacuum, if_pos (by norm_num), Int.toNat_zero, vSchur_zero]
  rfl

private theorem root_pair_high (i : ℕ) (hi : 2 ≤ i) :
    (V2m 1 le_rfl).smul (latChargeGen (latP 1) (-1 : ℤ)) i
      (latChargeGen (latP 1) (1 : ℤ)) = 0 := by
  rw [V2m_smul_neg_charge (m := 1) (hm := le_rfl) 1 i,
    EEVec_vacuum, if_neg (by omega)]
  simp [latStateGen]

section Shift
variable {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} {a : ℤ}

/-- The positive root field has a nonzero mode on every nonzero vector in
every inner-twisted module with the specified angle. -/
theorem shifted_root_nonvanishing (P : TwistedModule (shiftAut n a) n M)
    (hn : 0 < n) {x : M} (hx : x ≠ 0) :
    ∃ q : ℤ, P.YM (latChargeGen (latP 1) (1 : ℤ)) q x ≠ 0 :=
  twisted_field_nonvanishing (W := V2m 1 le_rfl) P hn _ _ _
    (shift_charge_eigen hn a (-1)) _ (LatMod.latticeCocycle_ne_zero _ _ _)
    root_pair root_pair_high hx

/-- Every nonzero Heisenberg vacuum eigenvector has the correct shifted
lattice charge. This is a classification of possible vacuum charges; it does
not assert one-dimensionality or a single orbit of the charge spaces. -/
theorem shifted_vac_charge_quantized (P : TwistedModule (shiftAut n a) n M)
    (hn : 0 < n) {x : M} (hx0 : x ≠ 0) (hx : x ∈ (torusHeisenberg P hn).vac)
    {μ : ℂ} (hμ : P.YM (hb 1) 0 x = μ • x) :
    ∃ b : ℤ, rootCoord * μ = (b : ℂ) - (a : ℂ) / n := by
  obtain ⟨q, hq, htop⟩ := twisted_field_top P _ x (shifted_root_nonvanishing P hn hx0)
  let j := ((-(a * (1 : ℤ))) % (n : ℤ)).toNat
  have hv := shift_charge_eigen hn a (1 : ℤ)
  have hs : (q + j) % (n : ℤ) = 0 := by
    by_contra hc
    exact hq (by rw [P.support j _ hv q hc]; rfl)
  have hi := torus_charge_top_index P hn 1 q j hv (by
    rw [show q + 2 * (n : ℤ) + j = (q + j) + 2 * n by ring, Int.add_emod]
    simp [hs]) hx hμ hq htop
  have hj : (j : ℤ) = (-a) % (n : ℤ) := by
    dsimp [j]
    rw [mul_one, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
  have hres : (q - a) % (n : ℤ) = 0 := by
    rw [hj] at hs
    simpa only [Int.add_emod, Int.emod_emod, sub_eq_add_neg] using hs
  obtain ⟨b, hb⟩ := Int.dvd_of_emod_eq_zero hres
  refine ⟨-b - 1, ?_⟩
  change chargeCoord (latP 1) (1 : ℤ) (a0 1) * μ = _
  rw [hi]
  have hbC : (q : ℂ) - a = (n : ℂ) * b := by exact_mod_cast hb
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp
  linear_combination -hbC

end Shift
end VOA.Classification.COne.OrbPos8
