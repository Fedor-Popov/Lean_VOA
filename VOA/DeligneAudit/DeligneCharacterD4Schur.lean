/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4ListBridge
import VOA.DeligneAudit.A2CharacterStar

/-!
# The unflavoured D₄ identity: Demazure sum = Schur index (layer 7, part 5)

* `ev1`: `z = 1` (sum of coefficients), `R → 𝕜`;
* `d4SchurQ N`: the coefficient of `q^N` in the Schur index `½ CT_x Θ(x) M(s = q^{1/2}, x, z = 1)`,
  read off at `t = q` from the `s`-coefficients of `Ikernel`;
* `hilbInt m N`: the integer coefficients of the computable Demazure character;
* `D4DemazurePositivity`: Demazure characters have nonnegative energies and multiplicities
  (classically a consequence of the Demazure character formula, i.e. of the input that reads `C_m`
  as the character of the module `D(1,mθ)`; that input is not formalized).  The Lean route
  (`DeligneCharacterD4Positivity.lean`): `energy` is proved (`D4Wp.energy_holds`), `coeff` follows
  from the open U5 (`D4Wp.d4DemazurePositivity_of_U5Z`);
* **`d4_demazure_eq_schur`**: `D4FiniteIdentity → D4DemazurePositivity →
  demazureSumCoeff d4DemazureHilb N = d4SchurQ N`.
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4K

open PowerSeries VOA.DeligneAudit.DeligneCharacter

noncomputable section

/-- `z = 1` (and `x = 1`): the sum of the coefficients. -/
def ev1 : R →ₗ[Kq] Kq := Finsupp.linearCombination Kq fun _ => (1 : Kq)

theorem ev1_mon (v : V) (c : Kq) : ev1 (mon v c) = c := by
  change (Finsupp.linearCombination Kq _) (Finsupp.single v c) = _
  rw [Finsupp.linearCombination_single, smul_eq_mul, mul_one]

theorem qq_zpow (j : ℤ) : qq ^ j = HahnSeries.single (2 * j) (1 : ℚ) := by
  rw [qq, show (HahnSeries.single (2 : ℤ) (1 : ℚ) : Kq) = HahnSeries.single (1 : ℤ) 1 ^ (2 : ℤ) from
      RatFunc.single_zpow 2, ← zpow_mul, ← RatFunc.single_zpow]

/-- The integer coefficients `[q^N] q^{m²}·(demazureChar m)|_{z=1}`. -/
def hilbInt (m : ℕ) (N : ℤ) : ℤ :=
  (((demazureChar cartanD4 thetaD4 wordD4 m).filter fun (t : Term) =>
    decide (t.1.2 + (m : ℤ) * m = N)).map fun (t : Term) => t.2).sum

theorem d4DemazureHilb_eq_toNat (m N : ℕ) : d4DemazureHilb m N = (hilbInt m N).toNat := rfl

/-- **Demazure positivity** (named input; classically from the Demazure character formula).
In Lean: `energy` is proved (`D4Wp.energy_holds`); `coeff` follows from U5
(`D4Wp.d4DemazurePositivity_of_U5Z`). -/
structure D4DemazurePositivity : Prop where
  energy : ∀ m : ℕ, ∀ t ∈ demazureChar cartanD4 thetaD4 wordD4 m, 0 ≤ t.1.2 + (m : ℤ) * m
  coeff : ∀ (m : ℕ) (N : ℕ), 0 ≤ hilbInt m N

theorem ev1_toR (f : LPoly) : ev1 (toR f) = (f.map fun t => qq ^ t.1.2 * (t.2 : Kq)).sum := by
  rw [toR, map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp [termR, ev1_mon]

/-- `ev1 C_m` as a finite sum of monomials `c · q^{e + m²}`. -/
theorem ev1_Cdem (m : ℕ) :
    ev1 (Cdem m) = ((demazureChar cartanD4 thetaD4 wordD4 m).map fun t =>
      HahnSeries.single (2 * (t.1.2 + (m : ℤ) * m)) (t.2 : ℚ)).sum := by
  rw [Cdem, map_smul, ← (toR_demazureChar m).2, ev1_toR, smul_eq_mul, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t _
  rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀ qq_ne_zero, qq_zpow]
  rw [show ((t.2 : ℤ) : Kq) = HahnSeries.C (t.2 : ℚ) by rfl, HahnSeries.C_apply,
    HahnSeries.single_mul_single, one_mul, add_zero]
  congr 1
  push_cast; ring_nf

/-! ## `q`-series from `ℤ⟦q⟧` -/

/-- `ℤ⟦q⟧ → 𝕜`, `q ↦ qq = r²`. -/
def jmap : PowerSeries ℤ →+* Kq :=
  (HahnSeries.ofPowerSeries ℤ ℚ).comp
    ((PowerSeries.map (Int.castRingHom ℚ)).comp (PowerSeries.expand 2 two_ne_zero).toRingHom)

theorem jmap_X : jmap X = qq := by
  simp [jmap, qq, HahnSeries.single_pow]

theorem jmap_coeff_even (f : PowerSeries ℤ) (k : ℕ) :
    (jmap f).coeff (2 * (k : ℤ)) = ((PowerSeries.coeff k f : ℤ) : ℚ) := by
  rw [show 2 * (k : ℤ) = ((2 * k : ℕ) : ℤ) by push_cast; ring]
  simp only [jmap, RingHom.coe_comp, Function.comp_apply]
  rw [HahnSeries.ofPowerSeries_apply_coeff, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    coeff_expand_mul]
  rfl

theorem jmap_coeff_neg (f : PowerSeries ℤ) (g : ℤ) (hg : g < 0) : (jmap f).coeff g = 0 := by
  simp only [jmap, RingHom.coe_comp, Function.comp_apply]
  rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range]
  rintro ⟨n, hn⟩
  simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk] at hn
  omega

theorem jmap_poch (n : ℕ) : jmap (VOA.DeligneAudit.A2.poch n) = qpoch n := by
  rw [VOA.DeligneAudit.A2.poch, map_prod, qpoch]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_sub, map_one, map_pow, jmap_X]

theorem jmap_partSeries (n : ℕ) : jmap (VOA.DeligneAudit.A2.partSeries n) = (qpoch n)⁻¹ := by
  have h := congrArg jmap (VOA.DeligneAudit.A2.partSeries_mul_poch n)
  rw [map_mul, jmap_poch, map_one] at h
  exact eq_inv_of_mul_eq_one_left h

/-- Regrouping a list of terms by `q`-exponent. -/
theorem sum_regroup (l : LPoly) (a : Term → ℤ) (hpos : ∀ t ∈ l, 0 ≤ a t) (K : ℕ) (P : ℕ → ℚ) :
    (l.map fun t => (t.2 : ℚ) * (if a t ≤ K then P (K - (a t).toNat) else 0)).sum =
      ∑ i ∈ Finset.range (K + 1),
        (((l.filter fun t => decide (a t = i)).map fun t => t.2).sum : ℚ) * P (K - i) := by
  induction l with
  | nil => simp
  | cons t l ih =>
      rw [List.map_cons, List.sum_cons, ih fun u hu => hpos u (List.mem_cons_of_mem _ hu)]
      have ht := hpos t List.mem_cons_self
      have hsplit : ∀ i ∈ Finset.range (K + 1),
          ((((t :: l).filter fun t => decide (a t = i)).map fun t => t.2).sum : ℚ) * P (K - i) =
            (if a t = i then (t.2 : ℚ) * P (K - i) else 0) +
              (((l.filter fun t => decide (a t = i)).map fun t => t.2).sum : ℚ) * P (K - i) := by
        intro i _
        rw [List.filter_cons]
        split_ifs with h1 h2 h2 <;> simp_all [add_mul]
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
      congr 1
      obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le ht
      simp only [hn, Nat.cast_inj, Int.toNat_natCast, Nat.cast_le]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_range, Nat.lt_succ_iff]
      split_ifs <;> simp

/-! ## The Schur target and the identity -/

/-- **The D₄ Schur index**: `[q^N] ½ CT_x Θ(x) M(s, x, z)|_{t = q, z = 1}`, read off from the
`s^{2m}`-coefficients of `Ikernel = CT_x Θ M` (each weighted by `q^m`).  In Lean this is just the
constant-term formula; its identification with the Schur index of the 4d theory is not formalized.
-/
def d4SchurQ (N : ℕ) : ℚ :=
  ∑ m ∈ Finset.range (N + 1), ((2 : Kq)⁻¹ * ev1 (coeff (2 * m) Ikernel)).coeff (2 * ((N : ℤ) - m))

theorem coeff_list_sum (l : List Kq) (g : ℤ) : l.sum.coeff g = (l.map fun x => x.coeff g).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

theorem coeff_partSeries (m n : ℕ) :
    PowerSeries.coeff n (VOA.DeligneAudit.A2.partSeries m) = (VOA.DeligneAudit.A2.partitionsLe m n : ℤ) := by
  simp [VOA.DeligneAudit.A2.partSeries]

/-- The `q^K` coefficient of `C_m(1)/(q;q)_m`. -/
theorem coeff_Cdem_div (hpos : D4DemazurePositivity) (m K : ℕ) :
    (ev1 (Cdem m) * (qpoch m)⁻¹).coeff (2 * (K : ℤ)) =
      ∑ i ∈ Finset.range (K + 1), (hilbInt m i : ℚ) * (VOA.DeligneAudit.A2.partitionsLe m (K - i) : ℚ) := by
  rw [ev1_Cdem, ← List.sum_map_mul_right, coeff_list_sum, List.map_map, ← jmap_partSeries]
  have : ∀ t ∈ demazureChar cartanD4 thetaD4 wordD4 m,
      ((fun x : Kq => x.coeff (2 * (K : ℤ))) ∘ fun t : Term =>
        HahnSeries.single (2 * (t.1.2 + (m : ℤ) * m)) (t.2 : ℚ) *
          jmap (VOA.DeligneAudit.A2.partSeries m)) t =
        (t.2 : ℚ) * (if t.1.2 + (m : ℤ) * m ≤ K then
          (VOA.DeligneAudit.A2.partitionsLe m (K - (t.1.2 + (m : ℤ) * m).toNat) : ℚ) else 0) := by
    intro t ht
    simp only [Function.comp_apply]
    rw [HahnSeries.coeff_single_mul]
    have he := hpos.energy m t ht
    split_ifs with h
    · obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le he
      rw [ha] at h ⊢
      have hK : a ≤ K := by exact_mod_cast h
      rw [show 2 * (K : ℤ) - 2 * (a : ℤ) = 2 * ((K - a : ℕ) : ℤ) by push_cast [hK]; ring,
        jmap_coeff_even, coeff_partSeries, Int.toNat_natCast]
      push_cast; rfl
    · rw [jmap_coeff_neg _ _ (by omega), mul_zero]
  rw [List.map_congr_left this]
  rw [sum_regroup _ (fun t => t.1.2 + (m : ℤ) * m) (hpos.energy m) K
    (fun n => ((VOA.DeligneAudit.A2.partitionsLe m n : ℕ) : ℚ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hilbInt]
  push_cast
  rw [List.map_map]
  rfl

/-- **The unflavoured D₄ identity: Demazure sum = Schur index**, conditional on the finite identity
(`D4F.D4FiniteIdentity`) and Demazure positivity (from the Demazure character formula). -/
theorem d4_demazure_eq_schur (hF : D4F.D4FiniteIdentity) (hpos : D4DemazurePositivity) (N : ℕ) :
    (demazureSumCoeff d4DemazureHilb N : ℚ) = d4SchurQ N := by
  rw [d4SchurQ, demazureSumCoeff]
  push_cast
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmN : m ≤ N := by simp only [Finset.mem_range] at hm; omega
  have h2 : (2 : Kq) ≠ 0 := by
    rw [show (2 : Kq) = HahnSeries.C (2 : ℚ) from (map_ofNat HahnSeries.C 2).symm]
    exact HahnSeries.C_ne_zero two_ne_zero
  rw [Ikernel_coeff_even hF m, map_smul, smul_eq_mul, ← mul_assoc, ← mul_assoc,
    inv_mul_cancel₀ h2, one_mul, mul_comm,
    show 2 * ((N : ℤ) - m) = 2 * ((N - m : ℕ) : ℤ) by push_cast [hmN]; ring, coeff_Cdem_div hpos,
    VOA.DeligneAudit.A2.conv]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [d4DemazureHilb_eq_toNat]
  congr 1
  exact_mod_cast Int.toNat_of_nonneg (hpos.coeff m i)

end

end VOA.DeligneAudit.DeligneCharacter.D4K

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.d4_demazure_eq_schur
end AxiomAudit
