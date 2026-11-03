import VOA.Classification.COne.OrbPos8Vacuum

/-! # Fractional translation and charge recursion

These identities hold in an arbitrary actual twisted module. In particular,
their proofs do not assume that its fields come from a shifted lattice model.
-/

namespace VOA.Classification.COne.OrbPos8
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet HeisenbergN
open OrbPos2 DMCOne LatMod TwistedReduction
open scoped BigOperators

section General
variable {V M : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {g : Aut W} {n : ℕ}

/-- Translation covariance at a supported fractional index, written with the
creation state `v_(-2) 1`. The support condition is essential for applying Jacobi. -/
theorem twisted_translation_supported (P : TwistedModule g n M) (hn : 0 < n)
    (j : ℕ) (v : V) (hv : v ∈ g.twistedEigenspace n j) (k : ℤ)
    (hk : (k + j) % (n : ℤ) = 0) (x : M) :
    P.YM (W.smul v (-2) W.vacuum) (k - n) x =
      (1 - (k : ℂ) / n) • P.YM v (k - 2 * n) x := by
  have hn0 : (n : ℤ) ≠ 0 := by omega
  have hJ := P.jacobi j v hv W.vacuum x (-2) k (-(n : ℤ)) hk
  have hvac (q : ℤ) (y : M) : P.YM W.vacuum q y = if q = -(n : ℤ) then y else 0 := by
    rw [P.vacuum_YM]
    split_ifs <;> rfl
  rw [finsum_eq_single _ (0 : ℤ) (fun i hi => by
    rcases lt_or_ge i 0 with hneg | hpos
    · rw [cbz_apply_neg _ hneg, mul_zero, zero_smul]
    · rw [hvac, if_neg (by
          intro he
          have : i * (n : ℤ) = 0 := by linarith
          exact hi ((mul_eq_zero.mp this).resolve_right hn0)), map_zero,
        hvac, if_neg (by nlinarith), smul_zero, sub_zero, smul_zero])] at hJ
  rw [finsum_nat_eq_sum_range 2 _ (fun i hi => by
    rw [PreVertexAlgebra.smul_vacuum_nonneg _ _ (by omega), map_zero]
    simp)] at hJ
  have hc1 : cbinom ((k : ℂ) / n) 1 = (k : ℂ) / n := by simp [cbinom]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero,
    Nat.cast_one, zero_mul, add_zero, sub_zero, cbinom_zero, hc1,
    one_mul, one_smul] at hJ
  rw [show (-2 : ℤ) + 1 = -1 by omega, PreVertexAlgebra.smul_vacuum_neg_one] at hJ
  simp only [hvac, ite_true, cbz_zero, mul_one, negOnePow,
    if_pos (Even.zero : Even (0 : ℤ))] at hJ
  have h3 : (-2 : ℤ) * n + -(n : ℤ) ≠ -(n : ℤ) := by nlinarith
  rw [if_neg h3, smul_zero, sub_zero, one_smul] at hJ
  have he1 : (-2 : ℤ) * n + k = k - 2 * n := by ring
  have he2 : k + -(n : ℤ) = k - n := by ring
  rw [he1, he2] at hJ
  rw [show k - (n : ℤ) - n = k - 2 * n by ring] at hJ
  rw [sub_smul, one_smul]
  exact (eq_sub_iff_add_eq.mpr hJ.symm)

/-- Jacobi with a fixed first state gives an ordinary iterate in that slot,
while retaining the arbitrary fractional index in the second slot. -/
theorem twisted_fixed_iterate (P : TwistedModule g n M) {h : V} (hg : g h = h)
    (v : V) (x : M) (ℓ q : ℤ) :
    P.YM (W.smul h ℓ v) q x =
      ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (P.YM h ((ℓ - i) * n) (P.YM v (q + i * n) x) -
          negOnePow ℓ • P.YM v (ℓ * n + q - i * n) (P.YM h (i * n) x)) := by
  have hJ := P.jacobi 0 h (mem_twistedEigenspace_zero hg) v x ℓ 0 q (by simp)
  rw [finsum_eq_single _ (0 : ℕ) (fun i hi => by
    rw [Int.cast_zero, zero_div, TwistedReduction.cbinom_zero_left, if_neg hi, zero_smul])] at hJ
  simpa only [Nat.cast_zero, zero_mul, add_zero, zero_add, sub_zero, Int.cast_zero,
    zero_div, cbinom_zero, one_smul, sub_mul] using hJ.symm

end General

section Torus
variable {M : Type} [AddCommGroup M] [Module ℂ M] {u : ℂˣ} {n : ℕ}

/-- The derivative relation for a charged state at a supported fractional index. -/
theorem torus_charge_derivative (P : TwistedModule (charU 1 le_rfl u) n M)
    (hn : 0 < n) (β : ℤ) (j : ℕ)
    (hv : latChargeGen (latP 1) β ∈ (charU 1 le_rfl u).twistedEigenspace n j)
    (q : ℤ) (hq : (q + n + j) % (n : ℤ) = 0) (x : M) :
    chargeCoord (latP 1) β (a0 1) •
      P.YM ((V2m 1 le_rfl).smul (hb 1) (-1) (latChargeGen (latP 1) β)) q x =
      (-(q : ℂ) / n) • P.YM (latChargeGen (latP 1) β) (q - n) x := by
  have h := twisted_translation_supported (W := V2m 1 le_rfl) P hn j _ hv (q + n) hq x
  rw [V2m_smul_charge_neg_two (m := 1) (hm := le_rfl), map_smul] at h
  have hc : (1 : ℂ) - ((q + n : ℤ) : ℂ) / n = -(q : ℂ) / n := by
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp
    ring
  simpa only [Pi.smul_apply, LinearMap.smul_apply, add_sub_cancel_right,
    show q + (n : ℤ) - 2 * n = q - n by ring, hc] using h

/-- The top nonzero charged mode sends a Heisenberg vacuum vector to another
Heisenberg vacuum vector. -/
theorem torus_charge_top_vac (P : TwistedModule (charU 1 le_rfl u) n M)
    (hn : 0 < n) (β q : ℤ) {x : M} (hx : x ∈ (torusHeisenberg P hn).vac)
    (htop : ∀ k : ℤ, q < k → P.YM (latChargeGen (latP 1) β) k x = 0) :
    P.YM (latChargeGen (latP 1) β) q x ∈ (torusHeisenberg P hn).vac := by
  rw [HeisSvN.HeisRep.mem_vac]
  intro p hp
  rw [torusHeisenberg_a]
  have hc := torus_charge_comm P β p q x
  have hv := (torusHeisenberg P hn).mem_vac.mp hx p hp
  rw [torusHeisenberg_a] at hv
  rw [hv, map_zero, sub_zero, htop ((n : ℤ) * p + q) (by
    have hnZ : (0 : ℤ) < n := by omega
    nlinarith), smul_zero] at hc
  exact hc

/-- At the top charged mode, the full iterate collapses to its zero-current term. -/
theorem torus_charge_top_iterate (P : TwistedModule (charU 1 le_rfl u) n M)
    (hn : 0 < n) (β q : ℤ) {x : M} (hx : x ∈ (torusHeisenberg P hn).vac)
    (htop : ∀ k : ℤ, q < k → P.YM (latChargeGen (latP 1) β) k x = 0) :
    P.YM ((V2m 1 le_rfl).smul (hb 1) (-1) (latChargeGen (latP 1) β)) (q + n) x =
      P.YM (latChargeGen (latP 1) β) q (P.YM (hb 1) 0 x) := by
  rw [twisted_fixed_iterate (W := V2m 1 le_rfl) P (charU_hb u),
    finsum_eq_single _ (0 : ℤ) (fun i hi => by
      rcases lt_or_ge i 0 with hneg | hpos
      · rw [cbz_apply_neg _ hneg, mul_zero, zero_smul]
      · have hv := (torusHeisenberg P hn).mem_vac.mp hx i (by omega)
        rw [torusHeisenberg_a, mul_comm (n : ℤ) i] at hv
        rw [htop _ (by nlinarith), hv, map_zero, map_zero, smul_zero,
          sub_zero, smul_zero])]
  rw [htop _ (by simp only [zero_mul, add_zero]; omega), map_zero]
  simp only [cbz_zero, zero_mul, sub_zero, negOnePow, mul_one]
  norm_num

/-- Charge quantization at a nonzero top mode. Once existence of such modes and
their support residue is established, this fixes the shifted charge coset. -/
theorem torus_charge_top_index (P : TwistedModule (charU 1 le_rfl u) n M)
    (hn : 0 < n) (β q : ℤ) (j : ℕ)
    (hv : latChargeGen (latP 1) β ∈ (charU 1 le_rfl u).twistedEigenspace n j)
    (hq : (q + 2 * n + j) % (n : ℤ) = 0)
    {x : M} (hx : x ∈ (torusHeisenberg P hn).vac) {μ : ℂ}
    (hμ : P.YM (hb 1) 0 x = μ • x)
    (hne : P.YM (latChargeGen (latP 1) β) q x ≠ 0)
    (htop : ∀ k : ℤ, q < k → P.YM (latChargeGen (latP 1) β) k x = 0) :
    chargeCoord (latP 1) β (a0 1) * μ = -((q : ℂ) / n + 1) := by
  have h := torus_charge_derivative P hn β j hv (q + n)
    (by convert hq using 1; congr 1; ring) x
  rw [torus_charge_top_iterate P hn β q hx htop, hμ, map_smul,
    smul_smul, add_sub_cancel_right] at h
  have he := (smul_left_injective ℂ hne) h
  rw [he]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp

end Torus

end VOA.Classification.COne.OrbPos8
