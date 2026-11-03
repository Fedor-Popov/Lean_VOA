import VOA.Classification.COne.OrbRat6Sl2

/-! # The `sl₂`-multiplets of `V_{ℤβ+β/2}` in weights `≤ 9/4`

* the spin-`3/2` quartet `q_k = F^k e^{3β/2}` (`qv k`, sectors `1, 0, −1, −2`), with
  `E q_{k+1} = ε (k+1)(3−k) q_k`, `q₄ = 0`, all `q_k ≠ 0` (`k ≤ 3`);
* the spin-`½` doublets of the top `e^{β/2}` (`tv`), of `h(−1)e^{β/2}` (`sv`) and of a vector
  `d₀ ∈ Fock₂ ⊗ e^{β/2}` with `E d₀ = 0` (`dv`);
* the weight spaces `1/4, 5/4, 9/4` in terms of these;
* the action of the lifted rotation `F = lift GR` and of the Klein projector `P`.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbRat6

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod Complex
  MvPolynomial

theorem hEF : ∀ x, Ep (Fm x) - Fm (Ep x) = eps1 • Hm x := comm_EF
theorem hHF : ∀ x, Hm (Fm x) - Fm (Hm x) = (-2 : ℂ) • Fm x := comm_HF

theorem one_mem_Z0 : (1 : FockN (rank (latP 1))) ∈ gradingZN (rank (latP 1)) 0 := by
  rw [gradingZN_of_nonneg le_rfl]
  exact vacuumN_mem_gradingWN _

theorem xo_mem_Z1 : xo 0 ∈ gradingZN (rank (latP 1)) 1 := by
  rw [gradingZN_of_nonneg (by norm_num)]
  have := isWeightedHomogeneous_X ℂ (weightFnN (r := rank (latP 1))) ((0 : ℕ), a0 1)
  simpa using this

theorem ne_zero_of_one (n : ℤ) : latStateGen (latP 1) (1 : FockN (rank (latP 1))) n ≠ 0 :=
  Screen.latStateGen_ne_zero (latP 1) one_ne_zero n

theorem Ep_Sd_zero {n d : ℤ} {x : Sp} (hx : x ∈ Sd n d) (h : d - 2 * n - 2 < 0) : Ep x = 0 := by
  have := Ep_Sd hx
  rwa [Sd_neg h, Submodule.mem_bot] at this

theorem Fm_Sd_zero {n d : ℤ} {x : Sp} (hx : x ∈ Sd n d) (h : d + 2 * n < 0) : Fm x = 0 := by
  have := Fm_Sd hx
  rwa [Sd_neg h, Submodule.mem_bot] at this

theorem Fm_pow_Sd {n d : ℤ} {x : Sp} (hx : x ∈ Sd n d) (k : ℕ) :
    (Fm ^ k) x ∈ Sd (n - k) (d + k * (2 * n - k + 1)) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    have := Fm_Sd ih
    convert this using 2
    · push_cast; ring
    · push_cast; ring

/-! ## §1 The quartet -/

/-- `e^{3β/2}`. -/
abbrev q0 : Sp := latStateGen (latP 1) 1 (1 : ℤ)

/-- `q_k = F^k e^{3β/2}`. -/
abbrev qv (k : ℕ) : Sp := (Fm ^ k) q0

theorem q0_Sd : q0 ∈ Sd 1 0 := latStateGen_mem_Sd (n := 1) one_mem_Z0

theorem Ep_q0 : Ep q0 = 0 := Ep_Sd_zero q0_Sd (by norm_num)

theorem Hm_q0 : Hm q0 = (3 : ℂ) • q0 := by
  rw [Hm_Sd q0_Sd]; norm_num

theorem qv_Sd (k : ℕ) : qv k ∈ Sd (1 - k) (k * (3 - k)) := by
  have := Fm_pow_Sd q0_Sd k
  convert this using 2; ring

theorem Ep_qv (k : ℕ) : Ep (qv (k + 1)) = (eps1 * (k + 1) * (3 - k)) • qv k :=
  E_Fpow hEF hHF Ep_q0 Hm_q0 k

theorem qv_four : qv 4 = 0 := by
  have := qv_Sd 4
  rw [Sd_neg (by norm_num), Submodule.mem_bot] at this
  exact this

theorem Fm_qv (k : ℕ) : Fm (qv k) = qv (k + 1) := by
  rw [qv, qv, pow_succ', Module.End.mul_apply]

theorem eps1_ne : eps1 ≠ 0 := by
  rcases eps1_cases with h | h <;> rw [h] <;> norm_num

theorem qv_ne (k : ℕ) (hk : k ≤ 3) : qv k ≠ 0 := by
  induction k with
  | zero => exact ne_zero_of_one (1 : ℤ)
  | succ k ih =>
    intro h
    have h1 := Ep_qv k
    rw [h, map_zero] at h1
    have hc : (eps1 * (k + 1) * (3 - k) : ℂ) ≠ 0 := by
      have hk' : (k : ℂ) ≠ 3 := by norm_cast; omega
      have : (3 - k : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hk')
      exact mul_ne_zero (mul_ne_zero eps1_ne (by norm_cast)) this
    exact ih (by omega) ((smul_eq_zero.mp h1.symm).resolve_left hc)

theorem qv_zero : qv 0 = q0 := by simp [qv]

theorem Ep_qv0 : Ep (qv 0) = 0 := by rw [qv_zero, Ep_q0]
theorem Ep_qv1 : Ep (qv 1) = (3 * eps1) • qv 0 := by
  rw [Ep_qv 0]; congr 1; push_cast; ring
theorem Ep_qv2 : Ep (qv 2) = (4 * eps1) • qv 1 := by
  rw [Ep_qv 1]; congr 1; push_cast; ring
theorem Ep_qv3 : Ep (qv 3) = (3 * eps1) • qv 2 := by
  rw [Ep_qv 2]; congr 1; push_cast; ring
theorem Fm_qv0 : Fm (qv 0) = qv 1 := Fm_qv 0
theorem Fm_qv1 : Fm (qv 1) = qv 2 := Fm_qv 1
theorem Fm_qv2 : Fm (qv 2) = qv 3 := Fm_qv 2
theorem Fm_qv3 : Fm (qv 3) = 0 := by rw [Fm_qv 3, qv_four]

/-- A vector of the quartet. -/
def Q (a b c d : ℂ) : Sp := a • qv 0 + b • qv 1 + c • qv 2 + d • qv 3

theorem Q_add (a b c d a' b' c' d' : ℂ) :
    Q a b c d + Q a' b' c' d' = Q (a + a') (b + b') (c + c') (d + d') := by
  simp only [Q, add_smul]; abel

theorem Q_smul (t a b c d : ℂ) : t • Q a b c d = Q (t * a) (t * b) (t * c) (t * d) := by
  simp only [Q, smul_add, smul_smul]

theorem Q_congr {a b c d a' b' c' d' : ℂ} (h1 : a = a') (h2 : b = b') (h3 : c = c')
    (h4 : d = d') : Q a b c d = Q a' b' c' d' := by rw [h1, h2, h3, h4]

theorem Ep_Q (a b c d : ℂ) : Ep (Q a b c d) = Q (3 * eps1 * b) (4 * eps1 * c) (3 * eps1 * d) 0 := by
  simp only [Q, map_add, map_smul, Ep_qv0, Ep_qv1, Ep_qv2, Ep_qv3, smul_zero, zero_add,
    smul_smul, zero_smul, add_zero]
  module

theorem Fm_Q (a b c d : ℂ) : Fm (Q a b c d) = Q 0 a b c := by
  simp only [Q, map_add, map_smul, Fm_qv0, Fm_qv1, Fm_qv2, Fm_qv3, smul_zero, add_zero,
    zero_smul, zero_add]

theorem Ep_pow_Q (a b c d : ℂ) : (Ep ^ 4) (Q a b c d) = 0 := by
  simp only [pow_succ, pow_zero, one_mul, Module.End.mul_apply, Ep_Q]
  simp [Q]

theorem Fm_pow_Q (a b c d : ℂ) : (Fm ^ 4) (Q a b c d) = 0 := by
  simp only [pow_succ, pow_zero, one_mul, Module.End.mul_apply, Fm_Q]
  simp [Q]

/-! ## §2 Exponential series in four terms -/

theorem expSum_four {M : Type*} [AddCommGroup M] [Module ℂ M] (D : Module.End ℂ M) (v : M) :
    expSum D 4 v = v + D v + (2⁻¹ : ℂ) • D (D v) + (6⁻¹ : ℂ) • D (D (D v)) := by
  simp only [expSum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_succ, pow_zero,
    one_mul, Module.End.mul_apply, Module.End.one_apply]
  norm_num [Nat.factorial]

theorem lift_GE_Q (t a b c d : ℂ) :
    lift (GE t) (Q a b c d) =
      Q (a + 3 * eps1 * t * b + 6 * eps1 ^ 2 * t ^ 2 * c + 6 * eps1 ^ 3 * t ^ 3 * d)
        (b + 4 * eps1 * t * c + 6 * eps1 ^ 2 * t ^ 2 * d) (c + 3 * eps1 * t * d) d := by
  rw [lift_GX root_pos t (Ep_pow_Q a b c d), expSum_four]
  simp only [LinearMap.smul_apply, map_smul, Ep_Q, Q_smul, Q_add]
  apply Q_congr <;> ring

theorem lift_GF_Q (t a b c d : ℂ) :
    lift (GF t) (Q a b c d) =
      Q a (b + t * a) (c + t * b + t ^ 2 / 2 * a) (d + t * c + t ^ 2 / 2 * b + t ^ 3 / 6 * a) := by
  rw [lift_GX root_neg t (Fm_pow_Q a b c d), expSum_four]
  simp only [LinearMap.smul_apply, map_smul, Fm_Q, Q_smul, Q_add]
  apply Q_congr <;> ring

/-! ## §3 Torus lifts on sectors -/

theorem lift_GC_Sd (u : ℂˣ) {n d : ℤ} {x : Sp} (hx : x ∈ Sd n d) :
    lift (GC u) x = ((u ^ n : ℂˣ) : ℂ) • x := by
  obtain ⟨p, hp, rfl⟩ := hx
  exact lift_GC u p n

theorem qv_Sd0 : qv 0 ∈ Sd 1 0 := by simpa using qv_Sd 0
theorem qv_Sd1 : qv 1 ∈ Sd 0 2 := by simpa using qv_Sd 1
theorem qv_Sd2 : qv 2 ∈ Sd (-1) 2 := by
  have := qv_Sd 2; norm_num at this; exact this
theorem qv_Sd3 : qv 3 ∈ Sd (-2) 0 := by
  have := qv_Sd 3; norm_num at this; exact this

theorem lift_GC_Q (u : ℂˣ) (a b c d : ℂ) :
    lift (GC u) (Q a b c d) =
      Q (((u ^ (1 : ℤ) : ℂˣ) : ℂ) * a) (((u ^ (0 : ℤ) : ℂˣ) : ℂ) * b)
        (((u ^ (-1 : ℤ) : ℂˣ) : ℂ) * c) (((u ^ (-2 : ℤ) : ℂˣ) : ℂ) * d) := by
  simp only [Q, map_add, map_smul]
  rw [lift_GC_Sd u qv_Sd0, lift_GC_Sd u qv_Sd1, lift_GC_Sd u qv_Sd2, lift_GC_Sd u qv_Sd3]
  simp only [smul_smul, mul_comm]

end VOA.Classification.COne.OrbRat6
