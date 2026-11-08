import VOA.Moonshine.MoonshineLRM5Replicable

/-!
# The untwisted denominator identity, formal logarithmic identity

Work in `ℂ((q))[[p]] = PowerSeries (LaurentSeries ℂ)`. For `f = q⁻¹ + Σ_{n≥1} c(n) qⁿ`:
* `faberGen_map_generating`: the Faber generating identity of `MoonshineLRFaberGenerating`, with `X`
  specialised to `f`: `p Φ′ = −Φ H`, where `Φ(p) = p (f(p) − f(q))` and `H = Σ_{m≥1} F_m(f(q)) p^m`;
* `knzSeries c = S = 1 − Σ_{a,b≥1} c(a+b−1) pᵃ qᵇ`;
* `faberGen_map_eq_mul`: the factorisation `Φ = (1 − q⁻¹ p) · S` (the telescoping identity in
  `Notes/moonshine/MOON_BKM.md`);
* `knz_log`: the logarithmic form `p ∂_p S = −S · E`, `E = Σ_{M ≥ 1} (F_M(f) − q^{−M}) p^M`.
-/

namespace VOA.Moonshine.ConwayNorton.M8

open Polynomial

/-- The power-series derivative commutes with coefficient maps. -/
theorem derivative_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (F : PowerSeries R) :
    PowerSeries.derivative S (PowerSeries.map φ F) =
      PowerSeries.map φ (PowerSeries.derivative R F) := by
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_map, PowerSeries.coeff_map,
    PowerSeries.coeff_derivative, map_mul, map_add, map_natCast, map_one]

/-- Specialisation `X ↦ f` from `ℂ[X]` to `ℂ((q))`. -/
noncomputable def evalAtQSeries (c : ℕ → ℂ) : ℂ[X] →+* LaurentSeries ℂ :=
  (aeval (qSeriesLaurent c)).toRingHom

/-- **The generating identity at `X = f`:** `p Φ′ = −Φ · H` in `ℂ((q))[[p]]`. -/
theorem faberGen_map_generating (c : ℕ → ℂ) :
    PowerSeries.X * PowerSeries.derivative (LaurentSeries ℂ)
        (PowerSeries.map (evalAtQSeries c) (faberGen c)) =
      -(PowerSeries.map (evalAtQSeries c) (faberGen c) *
        PowerSeries.map (evalAtQSeries c) (faberSeries c)) := by
  have h := congrArg (PowerSeries.map (evalAtQSeries c)) (faberGen_generating c)
  rw [map_mul, map_neg, map_mul, PowerSeries.map_X, ← derivative_map] at h
  exact h

/-- The `p^a`-coefficient of `S`: `1` for `a = 0`, and `−Σ_{b≥1} c(a+b−1) q^b` for `a ≥ 1`. -/
noncomputable def knzCoeff (c : ℕ → ℂ) (a : ℕ) : LaurentSeries ℂ :=
  if a = 0 then 1 else
    -HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.mk fun b => if b = 0 then 0 else c (a + b - 1))

/-- `S = 1 − Σ_{a,b≥1} c(a+b−1) pᵃ q^b` in `ℂ((q))[[p]]`. -/
noncomputable def knzSeries (c : ℕ → ℂ) : PowerSeries (LaurentSeries ℂ) :=
  PowerSeries.mk (knzCoeff c)

/-- `q⁻¹ ∈ ℂ((q))`. -/
noncomputable abbrev qInv : LaurentSeries ℂ := HahnSeries.single (-1 : ℤ) (1 : ℂ)

theorem coeff_ofPowerSeries_mk (g : ℕ → ℂ) (n : ℤ) :
    (HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.mk g)).coeff n =
      if n < 0 then 0 else g n.natAbs := by
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_mk]

/-- `f = q⁻¹ + Σ_{b ≥ 1} c(b) q^b`. -/
theorem qSeriesLaurent_eq_qInv_add (c : ℕ → ℂ) :
    qSeriesLaurent c = qInv +
      HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.mk fun b => if b = 0 then 0 else c b) := by
  ext n
  rw [HahnSeries.coeff_add, coeff_ofPowerSeries_mk, HahnSeries.coeff_single]
  have h := coeff_qSeriesLaurent_pow c 1 n
  rw [pow_one, pow_one] at h
  rw [h]
  rcases lt_trichotomy n (-1) with hlt | heq | hgt
  · rw [if_pos (by push_cast; omega), if_neg (by omega), if_pos (by omega), add_zero]
  · subst heq
    rw [if_neg (by norm_num), if_pos rfl, if_pos (by norm_num), add_zero]
    norm_num [coeff_qSeriesUnit]
  · rw [if_neg (by push_cast; omega), if_neg (by omega), if_neg (by omega), zero_add,
      coeff_qSeriesUnit]
    rcases (show n = 0 ∨ 0 < n by omega) with h0 | hpos
    · subst h0
      norm_num
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      congr 1
      omega

/-- The telescoping step: `q⁻¹ · Σ_{b≥1} c(a+b) q^b` shifted against `Σ_{b≥1} c(a+b+1) q^b`. -/
theorem qInv_mul_ofPowerSeries_mk (c : ℕ → ℂ) (a : ℕ) :
    qInv * HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.mk fun b => if b = 0 then 0 else c (a + b)) =
      HahnSeries.C (c (a + 1)) +
        HahnSeries.ofPowerSeries ℤ ℂ
          (PowerSeries.mk fun b => if b = 0 then 0 else c (a + 1 + b)) := by
  ext n
  rw [HahnSeries.coeff_single_mul, one_mul, HahnSeries.coeff_add, coeff_ofPowerSeries_mk,
    coeff_ofPowerSeries_mk, HahnSeries.C_apply, HahnSeries.coeff_single]
  rcases lt_trichotomy n 0 with hlt | heq | hgt
  · by_cases hn : n = -1
    · subst hn
      norm_num
    · rw [if_pos (by omega), if_neg (by omega), if_pos hlt]
      ring
  · subst heq
    norm_num
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), zero_add]
    congr 1
    omega

/-- **The factorisation** `Φ(p, f(q)) = (1 − q⁻¹ p) · S(p, q)`. -/
theorem faberGen_map_eq_mul (c : ℕ → ℂ) :
    PowerSeries.map (evalAtQSeries c) (faberGen c) =
      (1 - PowerSeries.C qInv * PowerSeries.X) * knzSeries c := by
  ext k
  rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
  rcases k with _ | _ | k
  · rw [PowerSeries.coeff_zero_X_mul, mul_zero, sub_zero]
    simp [faberGen, knzSeries, knzCoeff, evalAtQSeries]
  · rw [PowerSeries.coeff_succ_X_mul]
    simp only [faberGen, knzSeries, knzCoeff, evalAtQSeries, PowerSeries.coeff_mk]
    simp only [Nat.zero_add, one_ne_zero, ↓reduceIte, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      map_neg, aeval_X, mul_one]
    rw [qSeriesLaurent_eq_qInv_add]
    have e : (fun b : ℕ => if b = 0 then (0 : ℂ) else c (1 + b - 1)) =
        fun b => if b = 0 then 0 else c b := by
      funext b
      split_ifs
      · rfl
      · congr 1
        omega
    rw [e]
    ring_nf
  · rw [PowerSeries.coeff_succ_X_mul]
    simp only [faberGen, knzSeries, knzCoeff, evalAtQSeries, PowerSeries.coeff_mk]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
    have h := qInv_mul_ofPowerSeries_mk c k
    have e1 : (fun b : ℕ => if b = 0 then (0 : ℂ) else c (k + 1 + b - 1)) =
        fun b => if b = 0 then 0 else c (k + b) := by
      funext b
      split_ifs
      · rfl
      · congr 1
        omega
    have e2 : (fun b : ℕ => if b = 0 then (0 : ℂ) else c (k + 1 + 1 + b - 1)) =
        fun b => if b = 0 then 0 else c (k + 1 + b) := by
      funext b
      split_ifs
      · rfl
      · congr 1
        omega
    rw [e1, e2, mul_neg, h, show k + 1 + 1 - 1 = k + 1 by omega]
    have halg : algebraMap ℂ (LaurentSeries ℂ) (c (k + 1)) = HahnSeries.C (c (k + 1)) := by
      rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, HahnSeries.ofPowerSeries_C]
    rw [halg]
    ring_nf

/-! ### The logarithmic form -/

/-- `G = Σ_k q^{−k} pᵏ`, the inverse of `1 − q⁻¹ p`. -/
noncomputable def qInvGeom : PowerSeries (LaurentSeries ℂ) := PowerSeries.mk fun k => qInv ^ k

theorem mul_qInvGeom : (1 - PowerSeries.C qInv * PowerSeries.X) * qInvGeom = 1 := by
  ext M
  rw [sub_mul, one_mul, mul_assoc, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_one]
  rcases M with _ | M
  · rw [PowerSeries.coeff_zero_X_mul, mul_zero, sub_zero, if_pos rfl]
    simp [qInvGeom]
  · rw [PowerSeries.coeff_succ_X_mul, if_neg (by omega)]
    simp only [qInvGeom, PowerSeries.coeff_mk]
    rw [pow_succ]
    ring_nf

/-- The `p^M`-coefficient of `E`: `F_M(f) − q^{−M}` for `M ≥ 1`, and `0` for `M = 0`. -/
noncomputable def knzLogCoeff (c : ℕ → ℂ) (M : ℕ) : LaurentSeries ℂ :=
  if M = 0 then 0 else aeval (qSeriesLaurent c) (faberPoly c M) - qInv ^ M

/-- `E = Σ_{M ≥ 1} (F_M(f) − q^{−M}) p^M`. -/
noncomputable def knzLogSeries (c : ℕ → ℂ) : PowerSeries (LaurentSeries ℂ) :=
  PowerSeries.mk (knzLogCoeff c)

theorem knzLogSeries_eq (c : ℕ → ℂ) :
    knzLogSeries c = PowerSeries.map (evalAtQSeries c) (faberSeries c) -
      PowerSeries.C qInv * PowerSeries.X * qInvGeom := by
  ext M
  rw [map_sub, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
  rcases M with _ | M
  · rw [PowerSeries.coeff_zero_X_mul, mul_zero, sub_zero]
    simp [knzLogSeries, knzLogCoeff, faberSeries]
  · rw [PowerSeries.coeff_succ_X_mul]
    simp only [knzLogSeries, knzLogCoeff, faberSeries, qInvGeom, PowerSeries.coeff_mk,
      if_neg (Nat.succ_ne_zero M), evalAtQSeries, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [pow_succ]
    ring_nf

/-- **The logarithmic form of the denominator identity:** `p ∂_p S = −S · E` in `ℂ((q))[[p]]`,
with `E = Σ_{M ≥ 1} (F_M(f) − q^{−M}) p^M` (blueprint: `Notes/moonshine/MOON_BKM.md`). -/
theorem knz_log (c : ℕ → ℂ) :
    PowerSeries.X * PowerSeries.derivative (LaurentSeries ℂ) (knzSeries c) =
      -(knzSeries c * knzLogSeries c) := by
  set u : PowerSeries (LaurentSeries ℂ) := 1 - PowerSeries.C qInv * PowerSeries.X with hu
  have hu0 : u ≠ 0 := by
    intro h0
    have := congrArg PowerSeries.constantCoeff h0
    simp [hu] at this
  have hG := mul_qInvGeom
  rw [← hu] at hG
  have h := faberGen_map_generating c
  rw [faberGen_map_eq_mul, ← hu, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h
  have hdu : PowerSeries.derivative (LaurentSeries ℂ) u = -PowerSeries.C qInv := by
    rw [hu, map_sub, Derivation.map_one_eq_zero, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
      PowerSeries.derivative_X, PowerSeries.derivative_C, mul_one, mul_zero, add_zero, zero_sub]
  rw [hdu] at h
  apply mul_left_cancel₀ hu0
  rw [knzLogSeries_eq]
  linear_combination h - (knzSeries c * PowerSeries.C qInv * PowerSeries.X) * hG

/-! ### The denominator identity for `J`, logarithmic form -/

/-- For `J`, each `E_M = F_M(J) − q^{−M}` is the Hecke series
`Σ_{r ≥ 1} (Σ_{a∣(M,r)} (M/a) c(Mr/a²)) qʳ` (`(Rep₁)`, `coeff_faberPoly_cJ_eq_qHeckeCoeff`). -/
theorem knzLogCoeff_cJ {M : ℕ} (hM : 0 < M) :
    knzLogCoeff cJ M = HahnSeries.ofPowerSeries ℤ ℂ
      (PowerSeries.mk fun r => if r = 0 then 0 else qHeckeCoeff cJ M r) := by
  rw [knzLogCoeff, if_neg hM.ne']
  ext n
  rw [HahnSeries.coeff_sub, coeff_ofPowerSeries_mk, qInv, HahnSeries.single_pow, one_pow,
    HahnSeries.coeff_single]
  rcases lt_or_ge n 1 with hn | hn
  · rw [coeff_aeval_faberPoly cJ M (by omega)]
    have hsmul : M • (-1 : ℤ) = -(M : ℤ) := by simp
    rw [hsmul]
    by_cases hneg : n < 0
    · rw [if_pos hneg]
      split_ifs <;> simp
    · rw [if_neg hneg, if_neg (by omega), if_neg (by omega), sub_zero,
        if_pos (show n.natAbs = 0 by omega)]
  · obtain ⟨r, rfl⟩ : ∃ r : ℕ, n = (r : ℤ) := ⟨n.toNat, by omega⟩
    have hr : r ≠ 0 := by omega
    rw [coeff_faberPoly_cJ_eq_qHeckeCoeff hM hr, if_neg (by simp; omega), sub_zero,
      if_neg (by omega), Int.natAbs_natCast, if_neg hr]

/-- **The untwisted denominator identity for `J`, logarithmic form:** in `ℂ((q))[[p]]`,
`p ∂_p S = −S · Σ_{M ≥ 1} (Σ_{r ≥ 1} (Σ_{a∣(M,r)} (M/a) c(Mr/a²)) qʳ) p^M`,
`S = 1 − Σ_{a,b ≥ 1} c(a+b−1) pᵃ q^b`. Equivalently
`p ∂_p S = −S · Σ_{k,m,n ≥ 1} m c(mn) p^{mk} q^{nk}`. -/
theorem knz_log_J :
    PowerSeries.X * PowerSeries.derivative (LaurentSeries ℂ) (knzSeries cJ) =
      -(knzSeries cJ * PowerSeries.mk fun M => if M = 0 then 0 else
        HahnSeries.ofPowerSeries ℤ ℂ
          (PowerSeries.mk fun r => if r = 0 then 0 else qHeckeCoeff cJ M r)) := by
  rw [knz_log]
  congr 2
  ext M
  rw [knzLogSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases hM : M = 0
  · rw [if_pos hM, knzLogCoeff, if_pos hM]
  · rw [if_neg hM, knzLogCoeff_cJ (Nat.pos_of_ne_zero hM)]

end VOA.Moonshine.ConwayNorton.M8
