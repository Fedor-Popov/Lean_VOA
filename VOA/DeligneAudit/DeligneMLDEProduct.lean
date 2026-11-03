/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneMLDERamanujan
import VOA.DeligneAudit.DeligneMLDE
import VOA.DeligneAudit.A2CharacterStar

/-!
# `∏(1+q^r)^8` solves the `h∨ = 3` Arakawa–Kawasetsu recurrence

With `f = ∏_{r ≥ 1}(1+q^r)^8`, `θ = q d/dq`, `P₁ = ∑σ₁(n)qⁿ`, `P₃ = ∑σ₃(n)qⁿ`, `B = P₁(q²)`:

* `θ f = g f` with `g = 8 P₁ - 16 B` (logarithmic derivative, and `H₁ = -P₁ + 4B`);
* Ramanujan (`ramanujan`), its image under `q ↦ q²`, and the level-two identity (`level_two`)
  combine to

    `6θ²f + 3θf + 24 P₁ θf + 8 P₁ f - 80 P₃ f = 0`                  (`product_mlde`),

  which is the `h∨ = 3` AK recurrence coefficientwise: `A2.a2ProductMLDE : A2ProductMLDE`.

Everything is formal power series over `ℚ`, derived from the Jacobi triple product
(`VOA.QSeries.JTP.jacobiTriple`) via the heat equation (`DeligneMLDEHeat`).
-/

namespace VOA.DeligneAudit.DeligneMLDE.Heat

open PowerSeries VOA.QSeries VOA.QSeries.JTP

open scoped BigOperators

noncomputable section

/-! ## Lambert series as divisor sums -/

theorem coeff_lamQ_divisors (F : ℕ → ℕ → ℚ) (n : ℕ) :
    coeff n (lamQ F) = ∑ d ∈ n.divisors, F d (n / d) := by
  rw [coeff_lamQ, Nat.divisors, Finset.sum_filter, Finset.sum_Ico_eq_sum_range,
    show n + 1 - 1 = n by omega]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [add_comm 1 m]

theorem coeff_P1 (n : ℕ) : coeff n P1 = (DeligneCharacter.sigmaK 1 n : ℚ) := by
  rw [P1, coeff_lamQ_divisors, DeligneCharacter.sigmaK]
  push_cast
  rw [Nat.sum_div_divisors n (fun d => ((d : ℚ)))]
  simp

theorem coeff_P3 (n : ℕ) : coeff n P3 = (DeligneCharacter.sigmaK 3 n : ℚ) := by
  rw [P3, coeff_lamQ_divisors, DeligneCharacter.sigmaK]
  push_cast
  rw [Nat.sum_div_divisors n (fun d => ((d : ℚ)) ^ 3)]

/-- `q ↦ q²`. -/
abbrev ex2 : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ := expand 2 two_ne_zero

theorem lamQ_even (F : ℕ → ℕ → ℚ) :
    lamQ (fun d k => if Even k then F d k else 0) = ex2 (lamQ fun d k => F d (2 * k)) := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_expand, coeff_lamQ_divisors]
  split_ifs with h2
  · obtain ⟨t, rfl⟩ := h2
    rw [Nat.mul_div_cancel_left _ two_pos, coeff_lamQ_divisors, ← Finset.sum_filter]
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    have hset : (Nat.divisors (2 * t)).filter (fun d => Even (2 * t / d)) = t.divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hd, -⟩, ⟨s, hs⟩⟩
        refine ⟨?_, by omega⟩
        have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
        have : 2 * t = d * (s + s) := by rw [← hs, Nat.mul_div_cancel' hd]
        exact ⟨s, by linarith⟩
      · rintro ⟨hd, -⟩
        refine ⟨⟨Dvd.dvd.mul_left hd 2, by omega⟩, ?_⟩
        rw [Nat.mul_div_assoc _ hd]; exact even_two_mul _
    rw [hset]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Nat.mul_div_assoc _ (Nat.mem_divisors.mp hd).1]
  · refine Finset.sum_eq_zero fun d hd => ?_
    rw [if_neg]
    rintro ⟨s, hs⟩
    apply h2
    have := Nat.div_mul_cancel (Nat.mem_divisors.mp hd).1
    exact ⟨s * d, by rw [← this, hs]; ring⟩

theorem H1_eq : H1 = -P1 + PowerSeries.C 4 * ex2 P1 := by
  have h : lamQ (fun _ k => (-1 : ℚ) ^ k * k) =
      lamQ (fun d k => -1 * (k : ℚ) + 2 * (if Even k then (k : ℚ) else 0)) := by
    refine lamQ_congr fun d k _ => ?_
    rcases Nat.even_or_odd k with he | ho
    · rw [if_pos he, he.neg_one_pow]; ring
    · rw [if_neg (Nat.not_even_iff_odd.mpr ho), ho.neg_one_pow]; ring
  rw [H1, h, lamQ_add, lamQ_smul, lamQ_smul, lamQ_even, P1]
  have : lamQ (fun (_ : ℕ) (k : ℕ) => ((2 * k : ℕ) : ℚ)) = PowerSeries.C 2 * lamQ fun _ k => (k : ℚ) := by
    rw [← lamQ_smul]; exact lamQ_congr fun d k _ => by push_cast; ring
  rw [this, map_mul, map_neg, map_one, show ex2 (PowerSeries.C 2) = PowerSeries.C 2 from by rw [show (PowerSeries.C (2 : ℚ)) = 2 from map_ofNat _ 2, map_ofNat]]
  rw [show (PowerSeries.C (4 : ℚ) : PowerSeries ℚ) = PowerSeries.C 2 * PowerSeries.C 2 by rw [← map_mul]; norm_num]
  ring

theorem H3_eq : H3 = -P3 + PowerSeries.C 16 * ex2 P3 := by
  have h : lamQ (fun _ k => (-1 : ℚ) ^ k * (k : ℚ) ^ 3) =
      lamQ (fun d k => -1 * (k : ℚ) ^ 3 + 2 * (if Even k then (k : ℚ) ^ 3 else 0)) := by
    refine lamQ_congr fun d k _ => ?_
    rcases Nat.even_or_odd k with he | ho
    · rw [if_pos he, he.neg_one_pow]; ring
    · rw [if_neg (Nat.not_even_iff_odd.mpr ho), ho.neg_one_pow]; ring
  rw [H3, h, lamQ_add, lamQ_smul, lamQ_smul, lamQ_even, P3]
  have : lamQ (fun (_ : ℕ) (k : ℕ) => ((2 * k : ℕ) : ℚ) ^ 3) = PowerSeries.C 8 * lamQ fun _ k => (k : ℚ) ^ 3 := by
    rw [← lamQ_smul]; exact lamQ_congr fun d k _ => by push_cast; ring
  rw [this, map_mul, show ex2 (PowerSeries.C 8) = PowerSeries.C 8 from by rw [show (PowerSeries.C (8 : ℚ)) = 8 from map_ofNat _ 8, map_ofNat]]
  rw [show (PowerSeries.C (16 : ℚ) : PowerSeries ℚ) = PowerSeries.C 2 * PowerSeries.C 8 by rw [← map_mul]; norm_num, map_neg, map_one]
  ring

theorem eulerOp_ex2 (F : PowerSeries ℚ) : eulerOp (ex2 F) = 2 * ex2 (eulerOp F) := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_eulerOp, show (2 : PowerSeries ℚ) = PowerSeries.C 2 from rfl, coeff_C_mul, coeff_expand,
    coeff_expand]
  split_ifs with h
  · obtain ⟨t, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ two_pos, coeff_eulerOp]; push_cast; ring
  · simp

/-! ## The product `f = ∏(1+q^r)^8` -/

/-- `f = ∏_{r ≥ 1}(1+q^r)^8` over `ℚ`. -/
def fQ : PowerSeries ℚ := infProd fun k => (1 + X ^ (k + 1)) ^ 8

theorem prodFactors_fQ : ProdFactors fun k => ((1 + X ^ (k + 1)) ^ 8 : PowerSeries ℚ) := by
  have h := (prodFactors_one_add (R := ℚ) 1 (fun k => k + 1) fun k => Nat.lt_succ_self k).pow 8
  intro k
  simpa using h k

theorem coeff_fQ (N : ℕ) : coeff N fQ = (A2.productCoeff N : ℚ) := by
  rw [fQ, infProd, coeff_mk]
  have hmap : (∏ k ∈ Finset.range N, ((1 + X ^ (k + 1)) ^ 8 : PowerSeries ℚ)) =
      PowerSeries.map (Int.castRingHom ℚ) (A2.fermionProd N) := by
    rw [A2.fermionProd, map_prod]
    simp
  rw [hmap, coeff_map, A2.coeff_fermionProd_self]
  simp

/-- The factor log-derivative: `θ(1+qᵈ)^8 = (1+qᵈ)^8 · (-8d)·∑_k (-1)^k q^{dk}`. -/
theorem eulerOp_fQ_factor (m : ℕ) :
    eulerOp ((1 + X ^ (m + 1)) ^ 8 : PowerSeries ℚ)
      = (1 + X ^ (m + 1)) ^ 8 * (PowerSeries.C (-8 * ((m + 1 : ℕ) : ℚ)) * gs (-1 : ℚ) (m + 1)) := by
  have h := one_sub_mul_gs (-1 : ℚ) (by omega : 0 < m + 1)
  rw [map_neg, map_one] at h
  rw [show (8 : ℕ) = 7 + 1 from rfl, eulerOp_pow_succ, eulerOp_add, eulerOp_one, eulerOp_X_pow,
    map_mul, map_neg, map_natCast]
  rw [show ((7 + 1 : ℕ) : PowerSeries ℚ) = 8 by norm_num,
    show (PowerSeries.C (8 : ℚ) : PowerSeries ℚ) = 8 from map_ofNat _ 8]
  linear_combination (8 * ((m + 1 : ℕ) : PowerSeries ℚ) * (1 + X ^ (m + 1)) ^ 7) * h

/-- `g = θ log f`. -/
def gQ : PowerSeries ℚ :=
  tailSum fun m => PowerSeries.C (-8 * ((m + 1 : ℕ) : ℚ)) * gs (-1 : ℚ) (m + 1)

theorem eulerOp_fQ : eulerOp fQ = fQ * gQ := by
  apply eq_of_agreeTo
  intro N
  have hP := agreeTo_infProd prodFactors_fQ N
  have hT := agreeTo_tailSum (fun m => PowerSeries.C (-8 * ((m + 1 : ℕ) : ℚ)) * gs (-1 : ℚ) (m + 1))
    (fun m n h => by rw [coeff_C_mul, coeff_gs_eq_zero _ (by omega), mul_zero]) N
  have hfin := logDeriv_prod eulerOp eulerOp_mul (fun k => ((1 + X ^ (k + 1)) ^ 8 : PowerSeries ℚ))
    (fun m => PowerSeries.C (-8 * ((m + 1 : ℕ) : ℚ)) * gs (-1 : ℚ) (m + 1))
    eulerOp_fQ_factor eulerOp_one N
  exact (hP.eulerOp.trans (AgreeTo.of_eq hfin)).trans (hP.symm.mul hT.symm)

theorem gQ_eq_DS : gQ = PowerSeries.C (-8) * DS := by
  rw [DS, ← lamQ_smul]
  refine PowerSeries.ext fun n => ?_
  rw [gQ, tailSum, coeff_mk, map_sum, coeff_lamQ]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  rw [coeff_C_mul, coeff_gs]
  split_ifs with h1 h2 h2
  · push_cast; ring
  · exact absurd h1.2 h2
  · exact absurd ⟨by omega, h2⟩ h1
  · simp

/-- `g = 8P₁ - 16 P₁(q²)`. -/
theorem gQ_eq : gQ = 8 * P1 - 16 * ex2 P1 := by
  have h0 := order_zero_two
  rw [H1_eq] at h0
  rw [gQ_eq_DS]
  have e8 : (PowerSeries.C (-8 : ℚ) : PowerSeries ℚ) = -8 := by rw [map_neg, map_ofNat]
  have e4 : (PowerSeries.C (4 : ℚ) : PowerSeries ℚ) = 4 := map_ofNat _ 4
  have e2 : (PowerSeries.C (2 : ℚ) : PowerSeries ℚ) = 2 := map_ofNat _ 2
  rw [e4, e2] at h0
  rw [e8]
  linear_combination 4 * h0

/-! ## The MLDE for `f` -/

/-- **`f = ∏(1+q^r)^8` satisfies the `h∨ = 3` AK MLDE** (Zhu-normalised, coefficient form):
`6θ²f + 3θf + 24 P₁ θf + 8 P₁ f - 80 P₃ f = 0`. -/
theorem product_mlde :
    6 * eulerOp (eulerOp fQ) + 3 * eulerOp fQ + 24 * (P1 * eulerOp fQ) + 8 * (P1 * fQ)
      - 80 * (P3 * fQ) = 0 := by
  have hR1 := ramanujan
  simp only [map_ofNat] at hR1
  have hR2 := congrArg ex2 hR1
  simp only [map_mul, map_add, map_sub, map_ofNat] at hR2
  have hL2 := level_two
  have hθH1 : eulerOp H1 = -eulerOp P1 + 8 * ex2 (eulerOp P1) := by
    rw [H1_eq, eulerOp_add, show -P1 = PowerSeries.C (-1) * P1 by rw [map_neg, map_one]; ring,
      eulerOp_C_mul, eulerOp_C_mul, eulerOp_ex2, map_neg, map_one,
      show (PowerSeries.C (4 : ℚ) : PowerSeries ℚ) = 4 from map_ofNat _ 4]
    ring
  rw [hθH1, H1_eq, H3_eq] at hL2
  simp only [map_ofNat] at hL2
  have hθg : eulerOp gQ = 8 * eulerOp P1 - 32 * ex2 (eulerOp P1) := by
    rw [gQ_eq, eulerOp_sub, show (8 : PowerSeries ℚ) = PowerSeries.C 8 from (map_ofNat _ 8).symm,
      show (16 : PowerSeries ℚ) = PowerSeries.C 16 from (map_ofNat _ 16).symm, eulerOp_C_mul,
      eulerOp_C_mul, eulerOp_ex2]
    simp only [map_ofNat]; ring
  have h2 : eulerOp (eulerOp fQ) = fQ * (gQ * gQ) + fQ * eulerOp gQ := by
    rw [eulerOp_fQ, eulerOp_mul, eulerOp_fQ]; ring
  rw [h2, hθg, eulerOp_fQ, gQ_eq]
  linear_combination fQ * (60 * hL2 + 28 * hR1 - 192 * hR2)

/-! ## Coefficient form: the AK recurrence -/

theorem coeff_ofNat_mul (c : ℕ) [c.AtLeastTwo] (F : PowerSeries ℚ) (n : ℕ) :
    coeff n ((OfNat.ofNat c : PowerSeries ℚ) * F) = (OfNat.ofNat c : ℚ) * coeff n F := by
  rw [show (OfNat.ofNat c : PowerSeries ℚ) = PowerSeries.C (OfNat.ofNat c) from (map_ofNat _ c).symm,
    coeff_C_mul]

theorem coeff_mul_range (F G : PowerSeries ℚ) (hF : coeff 0 F = 0) (N : ℕ) :
    coeff N (F * G) = ∑ r ∈ Finset.range N, coeff (r + 1) F * coeff (N - (r + 1)) G := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ']
  simp [hF]

theorem a2ProductMLDE_isAKSolution :
    IsAKSolution (K := ℚ) 3 (fun N => (A2.productCoeff N : ℚ)) := by
  refine ⟨by rw [← coeff_fQ]; simp [fQ, infProd], ?_⟩
  intro N hN
  have h0 := product_mlde
  rw [show (6 : PowerSeries ℚ) = PowerSeries.C 6 from (map_ofNat _ 6).symm,
    show (3 : PowerSeries ℚ) = PowerSeries.C 3 from (map_ofNat _ 3).symm,
    show (24 : PowerSeries ℚ) = PowerSeries.C 24 from (map_ofNat _ 24).symm,
    show (8 : PowerSeries ℚ) = PowerSeries.C 8 from (map_ofNat _ 8).symm,
    show (80 : PowerSeries ℚ) = PowerSeries.C 80 from (map_ofNat _ 80).symm] at h0
  have h := congrArg (coeff N) h0
  simp only [map_add, map_sub, map_zero, coeff_C_mul, coeff_eulerOp] at h
  rw [coeff_mul_range _ _ (by rw [coeff_P1]; simp [DeligneCharacter.sigmaK]),
    coeff_mul_range _ _ (by rw [coeff_P1]; simp [DeligneCharacter.sigmaK]),
    coeff_mul_range _ _ (by rw [coeff_P3]; simp [DeligneCharacter.sigmaK])] at h
  simp only [coeff_eulerOp, coeff_fQ, coeff_P1, coeff_P3] at h
  have hterm : ∀ r ∈ Finset.range N, (akKernel 3 N (r + 1) : ℚ) * (A2.productCoeff (N - (r + 1)) : ℚ)
      = -(24 * ((DeligneCharacter.sigmaK 1 (r + 1) : ℚ) * (((N - (r + 1) : ℕ) : ℚ) * (A2.productCoeff (N - (r + 1)) : ℚ)))
        + 8 * ((DeligneCharacter.sigmaK 1 (r + 1) : ℚ) * (A2.productCoeff (N - (r + 1)) : ℚ))
        - 80 * ((DeligneCharacter.sigmaK 3 (r + 1) : ℚ) * (A2.productCoeff (N - (r + 1)) : ℚ))) := by
    intro r hr
    rw [Finset.mem_range] at hr
    simp only [akKernel]
    push_cast [Nat.cast_sub (by omega : r + 1 ≤ N)]
    ring
  show (N : ℚ) * (6 * N + ((3 : ℕ) : ℚ)) * (A2.productCoeff N : ℚ) = _
  simp only [Rat.cast_id]
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  set S1 := ∑ r ∈ Finset.range N,
    (DeligneCharacter.sigmaK 1 (r + 1) : ℚ) * (((N - (r + 1) : ℕ) : ℚ) * (A2.productCoeff (N - (r + 1)) : ℚ))
  set S2 := ∑ r ∈ Finset.range N, (DeligneCharacter.sigmaK 1 (r + 1) : ℚ) * (A2.productCoeff (N - (r + 1)) : ℚ)
  set S3 := ∑ r ∈ Finset.range N, (DeligneCharacter.sigmaK 3 (r + 1) : ℚ) * (A2.productCoeff (N - (r + 1)) : ℚ)
  push_cast
  linear_combination h

end

end VOA.DeligneAudit.DeligneMLDE.Heat

namespace VOA.DeligneAudit.A2

/-- **`A2ProductMLDE` is a theorem**: `∏(1+q^r)^8` solves the `h∨ = 3` AK recurrence.
Proof: Jacobi triple product + heat equation (`DeligneMLDEHeat`) → Ramanujan and its level-two
companion (`DeligneMLDERamanujan`) → `product_mlde`. -/
theorem a2ProductMLDE : A2ProductMLDE :=
  ⟨DeligneMLDE.Heat.a2ProductMLDE_isAKSolution⟩

/-- `[q^N]∏(1+q^r)^8 = mldeCoeff 3 N` for every `N`. -/
theorem productCoeff_eq_mldeCoeff' (N : ℕ) :
    (productCoeff N : ℚ) = DeligneCharacter.mldeCoeff 3 N :=
  productCoeff_eq_mldeCoeff a2ProductMLDE N

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneMLDE.Heat.ramanujan
#print axioms VOA.DeligneAudit.DeligneMLDE.Heat.level_two
#print axioms VOA.DeligneAudit.DeligneMLDE.Heat.product_mlde
#print axioms VOA.DeligneAudit.A2.a2ProductMLDE
end AxiomAudit
