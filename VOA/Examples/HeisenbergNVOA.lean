/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.HeisenbergNCentral
import VOA.Examples.HeisenbergNVertex
import VOA.Examples.HeisenbergVOA
import VOA.Core.VertexOperatorAlgebra
import VOA.Core.Goddard
import VOA.Core.Dong

/-!
# The rank-`r` Heisenberg VOA

Builds, on top of `Examples.HeisenbergNCentral` (which stops at
`LvirNa_comm_bulk_window`), the remaining rank-`r` conformal structure, namespaced under
`VOA.HeisenbergN`:

1. **Per-family central closure** `LvirNa_comm` (`c = 1` per family);
2. **Total Virasoro** `L_virasoroN` (`c = r`, via cross-family vanishing);
3. **The bridge** `YN_omega_eq_sugawaraN` and `LvirN_eq_mode_YN_omega`;
4. **VOA1-VOA3** (`conf_virasoroN`, `conf_L0_gradingN`, `translation_allN`, `ωN ∈ F₂`);
5. **The instance** `heisenbergNVOA` and `heisenbergN_central_charge`.

Every rank-1 proof (`Examples.HeisenbergCentral/Conformal/VOA`) is mirrored line-by-line with
the family index `a : Fin r` carried through; the genuinely new finishes are the **cross-family
sum** (2) and the **assembly** (5).
-/

namespace VOA

namespace HeisenbergN

open scoped BigOperators
open MvPolynomial
open Module (End)
open Finset

variable {r : ℕ}

/-! ## §1  Power sums over ℂ and the window scalar — port of `HeisenbergCentral`. -/

open Finset in
/-- `∑_{i<N} i = N(N-1)/2` over ℂ. -/
theorem csum_idN (N : ℕ) : ∑ i ∈ range N, (i : ℂ) = (N : ℂ) * (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, ih]; push_cast; ring

open Finset in
/-- `∑_{i<N} i² = N(N-1)(2N-1)/6` over ℂ. -/
theorem csum_sqN (N : ℕ) : ∑ i ∈ range N, (i : ℂ)^2 = (N : ℂ) * (N - 1) * (2 * N - 1) / 6 := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, ih]; push_cast; ring

open Finset in
/-- `∑_{i<N} (N-i)·i = (N³-N)/6` over ℂ. -/
theorem csum_windowN (N : ℕ) :
    ∑ i ∈ range N, ((N : ℂ) - i) * i = ((N : ℂ)^3 - N) / 6 := by
  have hsplit : ∑ i ∈ range N, ((N : ℂ) - i) * i
      = (N : ℂ) * (∑ i ∈ range N, (i : ℂ)) - ∑ i ∈ range N, (i : ℂ)^2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit, csum_idN, csum_sqN]; ring

open Finset in
/-- A `ℤ`-indexed finsum supported on the window `[base, base + N)` equals the shifted
`range`-sum. -/
theorem finsum_int_windowN (f : ℤ → ℂ) (base : ℤ) (N : ℕ)
    (hsupp : ∀ i : ℤ, f i ≠ 0 → base ≤ i ∧ i < base + N) :
    ∑ᶠ i : ℤ, f i = ∑ j ∈ range N, f (base + j) := by
  classical
  let emb : ℕ ↪ ℤ := ⟨fun j => base + (j : ℤ), by intro a b hab; simpa using hab⟩
  rw [finsum_eq_finsetSum_of_support_subset f (s := (range N).map emb) ?_]
  · rw [Finset.sum_map]; rfl
  · intro i hi
    rw [Function.mem_support] at hi
    obtain ⟨h1, h2⟩ := hsupp i hi
    rw [Finset.coe_map, Set.mem_image]
    refine ⟨(i - base).toNat, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_range]; omega
    · show base + ((i - base).toNat : ℤ) = i; omega

/-- The boundary-window scalar summand `W(m,n,i)` from `SN_sub_tilSN`. -/
noncomputable def winScalarN (k : ℂ) (m n i : ℤ) : ℂ :=
  if m + n = 0 then
    (if (i < 0 ∧ ¬ i < m) then (i : ℂ) * k
     else if (¬ i < 0 ∧ i < m) then -((i : ℂ) * k) else 0)
  else 0

/-- **The window resums to `(m³−m)/6 · k`** (`δ_{m+n,0}`). -/
theorem window_sumN (k : ℂ) (m n : ℤ) :
    (∑ᶠ i : ℤ, ((i : ℂ) - m) * winScalarN k m n i)
      = if m + n = 0 then k * ((m : ℂ)^3 - m) / 6 else 0 := by
  by_cases hmn : m + n = 0
  · rw [if_pos hmn]
    simp only [winScalarN, if_pos hmn]
    rcases le_or_gt 0 m with hm | hm
    · have hcast : ((m.toNat : ℕ) : ℂ) = (m : ℂ) := by
        have := Int.toNat_of_nonneg hm
        rw [← this]; push_cast; rw [this]
      rw [finsum_int_windowN _ 0 m.toNat ?_]
      · rw [show k * ((m : ℂ)^3 - m) / 6
              = k * (((m.toNat : ℂ)^3 - (m.toNat : ℂ)) / 6) from by rw [hcast]; ring]
        rw [← csum_windowN m.toNat, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        have hjm : (0 : ℤ) + (j : ℤ) < m := by
          have : (j : ℤ) < (m.toNat : ℤ) := by exact_mod_cast hj
          rw [Int.toNat_of_nonneg hm] at this; omega
        rw [if_neg (show ¬((0 : ℤ) + (j : ℤ) < 0 ∧ ¬ (0 : ℤ) + (j : ℤ) < m) from by rintro ⟨_, _⟩; omega),
            if_pos (show ¬ ((0 : ℤ) + (j : ℤ) < 0) ∧ (0 : ℤ) + (j : ℤ) < m from ⟨by omega, hjm⟩)]
        rw [show ((0 : ℤ) + (j : ℤ)) = (j : ℤ) from by ring, hcast]
        push_cast; ring
      · intro i hi
        by_contra hc
        push_neg at hc
        rcases lt_or_ge i 0 with hi0 | hi0
        · rw [if_neg (by rintro ⟨_, _⟩; omega), if_neg (by rintro ⟨_, _⟩; omega)] at hi
          simp at hi
        · have : m ≤ i := by have := hc (by omega); omega
          rw [if_neg (by rintro ⟨_, _⟩; omega), if_neg (by rintro ⟨_, _⟩; omega)] at hi
          simp at hi
    · have hmM : ((((-m).toNat : ℕ)) : ℂ) = -(m : ℂ) := by
        have h := Int.toNat_of_nonneg (show (0:ℤ) ≤ -m by omega)
        have : (((-m).toNat : ℤ) : ℂ) = ((-m : ℤ) : ℂ) := by rw [h]
        rw [Int.cast_natCast] at this; rw [this]; push_cast; ring
      rw [finsum_int_windowN _ m (-m).toNat ?_]
      · rw [show k * ((m : ℂ)^3 - m) / 6
              = -(k * ((((-m).toNat : ℂ)^3 - ((-m).toNat : ℂ)) / 6)) from by
              rw [hmM]; ring]
        rw [← csum_windowN (-m).toNat, Finset.mul_sum, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        have hjlt : m + (j : ℤ) < 0 := by
          have : (j : ℤ) < ((-m).toNat : ℤ) := by exact_mod_cast hj
          rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ -m)] at this; omega
        rw [if_pos (show m + (j : ℤ) < 0 ∧ ¬ m + (j : ℤ) < m from ⟨hjlt, by omega⟩)]
        push_cast
        rw [show (((m : ℂ) + j) - m) = (j : ℂ) from by ring]
        rw [show ((((-m).toNat : ℂ)) - j) = -((m : ℂ) + j) from by rw [hmM]; ring]
        ring
      · intro i hi
        by_contra hc
        push_neg at hc
        rcases lt_or_ge i 0 with hi0 | hi0
        · have : i < m := by by_contra h; exact absurd (hc (by omega)) (by omega)
          rw [if_neg (by rintro ⟨_, _⟩; omega), if_neg (by rintro ⟨_, _⟩; omega)] at hi
          simp at hi
        · rw [if_neg (by rintro ⟨_, _⟩; omega), if_neg (by rintro ⟨_, _⟩; omega)] at hi
          simp at hi
  · rw [if_neg hmn]
    simp only [winScalarN, if_neg hmn, mul_zero, finsum_zero]

/-! ## §2  Per-family central closure `LvirNa_comm`, central charge `c = 1`. -/

/-- **The per-family Virasoro relation** with central charge `c = 1`:
`[Lᵃₘ, Lᵃₙ] = (m−n)Lᵃ_{m+n} + δ_{m+n,0}(m³−m)/12·id`. -/
theorem LvirNa_comm (r : ℕ) (k : ℂ) (hk : k ≠ 0) (a : Fin r) (m n : ℤ) :
    LvirNa r k a m * LvirNa r k a n - LvirNa r k a n * LvirNa r k a m
      = ((m : ℂ) - n) • LvirNa r k a (m + n)
        + (if m + n = 0 then ((m : ℂ)^3 - m) / 12 else 0) • (LinearMap.id : End ℂ (FockN r)) := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply]
  rw [LvirNa_comm_bulk_window r k hk a m n x]
  congr 1
  rw [show (∑ᶠ i : ℤ, (((i : ℂ) - m) • (sugTermN r k a (m + n) i x - tilSN r k a m n i x)))
        = ∑ᶠ i : ℤ, (((i : ℂ) - m) * winScalarN k m n i) • x from
      finsum_congr fun i => by
        rw [SN_sub_tilSN r k a m n i x, smul_smul]; rfl]
  rw [← finsum_smul, window_sumN k m n]
  rw [smul_smul]
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos hmn]
    congr 1
    field_simp
    ring
  · rw [if_neg hmn, if_neg hmn, mul_zero, zero_smul]

/-! ## §3  Total Virasoro `L_virasoroN`, central charge `c = r`. -/

/-- `LvirNa a` and `LvirNa b` commute as operators for `a ≠ b` (operator form of the
pointwise `LvirNa_comm_LvirNa_cross`). -/
theorem LvirNa_mul_comm_cross (r : ℕ) (k : ℂ) (hk : k ≠ 0) (a b : Fin r) (hab : a ≠ b)
    (m n : ℤ) :
    LvirNa r k a m * LvirNa r k b n - LvirNa r k b n * LvirNa r k a m = 0 := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, LinearMap.zero_apply,
    LvirNa_comm_LvirNa_cross r k hk a b hab m n x, sub_self]

/-- **The total Virasoro relation** with central charge `c = r`:
`[Lₘ, Lₙ] = (m−n)L_{m+n} + δ_{m+n,0}·r·(m³−m)/12·id`.  Expanding `Lₘ = ∑_a Lᵃₘ`, the diagonal
`a = b` terms each contribute the per-family `c = 1` central term (`LvirNa_comm`), and the
cross-family `a ≠ b` terms vanish (`LvirNa_mul_comm_cross`); summing over the `r` families
yields `c = r`. -/
theorem L_virasoroN (r : ℕ) (k : ℂ) (hk : k ≠ 0) (m n : ℤ) :
    LvirN r k m * LvirN r k n - LvirN r k n * LvirN r k m
      = ((m : ℂ) - n) • LvirN r k (m + n)
        + (if m + n = 0 then (r : ℂ) * ((m : ℂ)^3 - m) / 12 else 0)
            • (LinearMap.id : End ℂ (FockN r)) := by
  -- per-pair commutator: diagonal central, off-diagonal zero
  have hcomm : ∀ a : Fin r, ∀ b : Fin r,
      LvirNa r k a m * LvirNa r k b n - LvirNa r k b n * LvirNa r k a m
        = if a = b then
            (((m : ℂ) - n) • LvirNa r k a (m + n)
              + (if m + n = 0 then ((m : ℂ)^3 - m) / 12 else 0) • (LinearMap.id : End ℂ (FockN r)))
          else 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab; rw [if_pos rfl, LvirNa_comm r k hk a m n]
    · rw [if_neg hab, LvirNa_mul_comm_cross r k hk a b hab m n]
  -- LHS as a double sum of per-pair brackets
  have hLHS : LvirN r k m * LvirN r k n - LvirN r k n * LvirN r k m
      = ∑ a : Fin r, ∑ b : Fin r,
          (LvirNa r k a m * LvirNa r k b n - LvirNa r k b n * LvirNa r k a m) := by
    simp only [LvirN]
    -- first product: ∑a ∑b Lᵃₘ Lᵇₙ
    rw [show (∑ a : Fin r, LvirNa r k a m) * (∑ b : Fin r, LvirNa r k b n)
          = ∑ a : Fin r, ∑ b : Fin r, LvirNa r k a m * LvirNa r k b n from by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun a _ => Finset.mul_sum _ _ _]
    -- second product: (∑a Lᵃₙ)(∑b Lᵇₘ) = ∑a ∑b Lᵃₙ Lᵇₘ, then swap a↔b to ∑a ∑b Lᵇₙ Lᵃₘ
    rw [show (∑ a : Fin r, LvirNa r k a n) * (∑ b : Fin r, LvirNa r k b m)
          = ∑ a : Fin r, ∑ b : Fin r, LvirNa r k b n * LvirNa r k a m from by
        rw [Finset.sum_mul]
        rw [show (∑ a : Fin r, LvirNa r k a n * (∑ b : Fin r, LvirNa r k b m))
              = ∑ a : Fin r, ∑ b : Fin r, LvirNa r k a n * LvirNa r k b m from
            Finset.sum_congr rfl fun a _ => Finset.mul_sum _ _ _]
        exact Finset.sum_comm]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
  rw [hLHS]
  -- collapse each per-pair bracket via hcomm, then the diagonal δ collapses the inner sum
  rw [show (∑ a : Fin r, ∑ b : Fin r,
            (LvirNa r k a m * LvirNa r k b n - LvirNa r k b n * LvirNa r k a m))
        = ∑ a : Fin r,
            (((m : ℂ) - n) • LvirNa r k a (m + n)
              + (if m + n = 0 then ((m : ℂ)^3 - m) / 12 else 0)
                  • (LinearMap.id : End ℂ (FockN r))) from
      Finset.sum_congr rfl fun a _ => by
        rw [show (∑ b : Fin r,
              (LvirNa r k a m * LvirNa r k b n - LvirNa r k b n * LvirNa r k a m))
            = ∑ b : Fin r, (if a = b then
                (((m : ℂ) - n) • LvirNa r k a (m + n)
                  + (if m + n = 0 then ((m : ℂ)^3 - m) / 12 else 0)
                      • (LinearMap.id : End ℂ (FockN r)))
              else 0) from Finset.sum_congr rfl fun b _ => hcomm a b]
        rw [Finset.sum_ite_eq Finset.univ a, if_pos (Finset.mem_univ a)]]
  -- ∑_a (bulk_a + central_a) = bulk + (∑_a central_a) = (m-n)•L_{m+n} + r•(…)•id
  rw [Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [show (∑ _a : Fin r, LvirNa r k _a (m + n)) = LvirN r k (m + n) from rfl]
  congr 1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [show (r • ((if m + n = 0 then ((m : ℂ)^3 - m) / 12 else 0)
              • (LinearMap.id : End ℂ (FockN r))))
        = ((r : ℂ) * (if m + n = 0 then ((m : ℂ)^3 - m) / 12 else 0))
            • (LinearMap.id : End ℂ (FockN r)) from by
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]]
  congr 1
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos hmn]; ring
  · rw [if_neg hmn, if_neg hmn, mul_zero]

/-! ## §4  The conformal bridge `YN(ωN) = sugawaraFieldN` and `LvirN = mode (YN ωN)(·+1)`. -/

/-- `oscN a (-1)(oscN a (-1) vac) = (X (0,a))²` (per family). -/
theorem oscN_neg_one_sq_vacuumN (r : ℕ) (k : ℂ) (a : Fin r) :
    oscN r k a (-1) (oscN r k a (-1) (vacuumN r)) = (X (0, a) : FockN r) ^ 2 := by
  rw [oscN_neg_one_vacuum, oscN_apply_neg r k a (by norm_num : (-1 : ℤ) < 0)]
  rw [show (-(-1 : ℤ) - 1).toNat = (0 : ℕ) from by norm_num]
  ring

/-- `(X (0,a))² = monomial (single (0,a) 2) 1`. -/
theorem X_zero_sq_eq_monomialN (r : ℕ) (a : Fin r) :
    (X (0, a) : FockN r) ^ 2 = monomial (Finsupp.single (0, a) 2) 1 := by
  rw [X_zero_eq_monomialN, monomial_pow, one_pow]
  congr 1
  rw [Finsupp.smul_single, smul_eq_mul]

/-- `monoWordN (single (0,a) 2) = [(0,a),(0,a)]`. -/
theorem monoWordN_single_two (r : ℕ) (a : Fin r) :
    monoWordN (Finsupp.single ((0 : ℕ), a) 2) = [((0 : ℕ), a), ((0 : ℕ), a)] := by
  unfold monoWordN
  rw [show (Finsupp.single ((0 : ℕ), a) 2 : (ℕ × Fin r) →₀ ℕ).support = {((0 : ℕ), a)} from
    Finsupp.support_single ((0 : ℕ), a) (by norm_num : (2 : ℕ) ≠ 0)]
  simp [Finsupp.single_eq_same]

/-- `nprod` depends only on the underlying distributions, not the field-witness proofs. -/
theorem nprodN_eq_nprodN {r : ℕ} {a b a' b' : FormalDist (End ℂ (FockN r))}
    (ha : IsField a) (hb : IsField b) (ha' : IsField a') (hb' : IsField b')
    (haa : a = a') (hbb : b = b') :
    nprod ha hb = nprod ha' hb' := by
  subst haa; subst hbb; rfl

/-- `YwordN [(0,a)] = currentN a`. -/
theorem YwordN_zero_oneN (r : ℕ) (k : ℂ) (a : Fin r) :
    YwordN r k [((0 : ℕ), a)] = currentN r k a := by
  rw [YwordN_cons]
  show nprod (genFieldN_isField r k a 0) (idFieldN_isField r) = currentN r k a
  rw [nprod_idFieldN (genFieldN_isField r k a 0), genFieldN_zero]

/-- `YwordN [(0,a),(0,a)] = nprod (currentN a)(currentN a)`. -/
theorem YwordN_zero_zeroN (r : ℕ) (k : ℂ) (a : Fin r) :
    YwordN r k [((0 : ℕ), a), ((0 : ℕ), a)]
      = nprod (currentN_isField r k a) (currentN_isField r k a) := by
  rw [YwordN_cons]
  exact nprodN_eq_nprodN (genFieldN_isField r k a 0) (YwordN_isField r k [((0 : ℕ), a)])
    (currentN_isField r k a) (currentN_isField r k a) (genFieldN_zero r k a)
    (YwordN_zero_oneN r k a)

/-- **The per-family bridge**: `YN(ωNa) = sugawaraFieldNa`. -/
theorem YN_omega_eq_sugawaraNa (r : ℕ) (k : ℂ) (a : Fin r) :
    YN r k (ωNa r k a) = sugawaraFieldNa r k a := by
  rw [ωNa, map_smul, oscN_neg_one_sq_vacuumN, X_zero_sq_eq_monomialN, YN_monomial_one,
    YmonN, monoWordN_single_two, YwordN_zero_zeroN, sugawaraFieldNa]

/-- **THE BRIDGE** (Gannon 5.2.5d, rank `r`): `YN(ωN) = sugawaraFieldN`. -/
theorem YN_omega_eq_sugawaraN (r : ℕ) (k : ℂ) :
    YN r k (ωN r k) = sugawaraFieldN r k := by
  rw [ωN, map_sum, sugawaraFieldN]
  exact Finset.sum_congr rfl fun a _ => YN_omega_eq_sugawaraNa r k a

/-- `LvirNa a n = mode (YN(ωNa))(n+1) = sugawaraFieldNa(-n-2)` (per family). -/
theorem LvirNa_eq_mode_YN_omegaNa (r : ℕ) (k : ℂ) (a : Fin r) (n : ℤ) :
    LvirNa r k a n = mode (YN r k (ωNa r k a)) (n + 1) := by
  rw [mode_apply, YN_omega_eq_sugawaraNa, show -(n + 1) - 1 = -n - 2 from by ring,
    sugawaraFieldNa]
  rfl

/-- `FormalDist` finset-sum evaluates pointwise. -/
theorem formalDistN_sum_apply {ι : Type*} (s : Finset ι)
    (F : ι → FormalDist (End ℂ (FockN r))) (j : ℤ) :
    (∑ a ∈ s, F a) j = ∑ a ∈ s, F a j := by
  classical
  induction s using Finset.induction with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

/-- **`LvirN n = mode (YN ωN)(n+1)`** (the conformal-weight-2 shift, total). -/
theorem LvirN_eq_mode_YN_omega (r : ℕ) (k : ℂ) (n : ℤ) :
    LvirN r k n = mode (YN r k (ωN r k)) (n + 1) := by
  rw [LvirN, ωN, map_sum, mode_apply]
  show (∑ a : Fin r, LvirNa r k a n) = (∑ a : Fin r, YN r k (ωNa r k a)) (-(n + 1) - 1)
  rw [formalDistN_sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  have := LvirNa_eq_mode_YN_omegaNa r k a n
  rw [mode_apply] at this
  exact this

/-! ## §5  VOA1 — the conformal Virasoro relation for `YN(ωN)`, central charge `c = r`. -/

/-- **VOA1 (conformal symmetry)**, `centralCharge = r`. -/
theorem conf_virasoroN (r : ℕ) (k : ℂ) (hk : k ≠ 0) (m n : ℤ) :
    ⁅mode (YN r k (ωN r k)) (m + 1), mode (YN r k (ωN r k)) (n + 1)⁆
      = ((m : ℂ) - n) • mode (YN r k (ωN r k)) (m + n + 1)
        + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * (r : ℂ)) • (1 : End ℂ (FockN r))
           else 0) := by
  rw [← LvirN_eq_mode_YN_omega, ← LvirN_eq_mode_YN_omega,
    show m + n + 1 = (m + n) + 1 from by ring, ← LvirN_eq_mode_YN_omega]
  rw [Ring.lie_def, L_virasoroN r k hk m n]
  rw [show ((m : ℂ) ^ 3 - m) / 12 * (r : ℂ) = (r : ℂ) * ((m : ℂ) ^ 3 - m) / 12 from by ring]
  rw [show (1 : End ℂ (FockN r)) = (LinearMap.id : End ℂ (FockN r)) from rfl]
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos hmn]
  · rw [if_neg hmn, if_neg hmn, zero_smul]

/-! ## §6  VOA2 — `L₀ = mode (YN ωN) 1` acts as the conformal weight. -/

/-- `LvirN 0` acts as the weighted degree on `gradingWN`: `L₀ p = w • p` for `p ∈ F_w`.  Via
`LvirN_comm_oscN` (the `[L₀, aᵃ_{-i-1}] = (i+1)aᵃ_{-i-1}` Euler step) on the monomial basis. -/
theorem LvirN_zero_oscN_neg (r : ℕ) (k : ℂ) (hk : k ≠ 0) (a : Fin r) (i : ℕ) (p : FockN r) :
    LvirN r k 0 (oscN r k a (-(i : ℤ) - 1) p)
      = ((i : ℂ) + 1) • oscN r k a (-(i : ℤ) - 1) p + oscN r k a (-(i : ℤ) - 1) (LvirN r k 0 p) := by
  rw [LvirN_oscN r k hk a 0 (-(i : ℤ) - 1) p]
  rw [show (0 : ℤ) + (-(i : ℤ) - 1) = -(i : ℤ) - 1 from by ring]
  congr 2
  push_cast; ring

/-- `oscN a (-(i:ℤ)-1) p = X (i,a) * p` (creation = multiplication by the variable). -/
theorem oscN_neg_eq_mulXN (r : ℕ) (k : ℂ) (a : Fin r) (i : ℕ) (p : FockN r) :
    oscN r k a (-(i : ℤ) - 1) p = X (i, a) * p := by
  rw [oscN_apply_neg r k a (by omega : -(i : ℤ) - 1 < 0)]
  rw [show (-(-(i : ℤ) - 1) - 1).toNat = i from by omega]

/-- The **Euler step** for `L₀`: `L₀(X_{(i,a)}·p) = (i+1)·(X_{(i,a)}·p) + X_{(i,a)}·(L₀ p)`. -/
theorem LvirN_zero_mulXN (r : ℕ) (k : ℂ) (hk : k ≠ 0) (a : Fin r) (i : ℕ) (p : FockN r) :
    LvirN r k 0 (X (i, a) * p) = ((i : ℂ) + 1) • (X (i, a) * p) + X (i, a) * LvirN r k 0 p := by
  rw [← oscN_neg_eq_mulXN r k a i p, LvirN_zero_oscN_neg r k hk a i p,
    oscN_neg_eq_mulXN r k a i p, oscN_neg_eq_mulXN r k a i (LvirN r k 0 p)]

/-- `L₀` kills constants: `L₀ (C c) = 0`. -/
theorem LvirN_zero_C (r : ℕ) (k : ℂ) (c : ℂ) : LvirN r k 0 (MvPolynomial.C c : FockN r) = 0 := by
  rw [show (MvPolynomial.C c : FockN r) = c • (vacuumN r) from by
        rw [vacuumN, MvPolynomial.smul_eq_C_mul, mul_one],
    map_smul, LvirN_vacuum r k (by norm_num : (-1 : ℤ) ≤ 0), smul_zero]

/-- The Euler step iterated over a power of one variable. -/
theorem LvirN_zero_mulXN_pow (r : ℕ) (k : ℂ) (hk : k ≠ 0) (a : Fin r) (i : ℕ) (e : ℕ)
    (q : FockN r) :
    LvirN r k 0 (X (i, a) ^ e * q)
      = ((e : ℂ) * ((i : ℂ) + 1)) • (X (i, a) ^ e * q) + X (i, a) ^ e * LvirN r k 0 q := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hpow : (X (i, a) : FockN r) ^ (e + 1) * q = X (i, a) * (X (i, a) ^ e * q) := by
      rw [pow_succ]; ring
    have hpowL : (X (i, a) : FockN r) * (X (i, a) ^ e * LvirN r k 0 q)
        = X (i, a) ^ (e + 1) * LvirN r k 0 q := by rw [pow_succ]; ring
    rw [hpow, LvirN_zero_mulXN r k hk a i (X (i, a) ^ e * q), ih, mul_add]
    rw [mul_smul_comm, ← hpow, hpowL]
    push_cast
    module

/-- **`L₀` acts as the weighted degree on every monomial**. -/
theorem LvirN_zero_monomial (r : ℕ) (k : ℂ) (hk : k ≠ 0) (c : ℂ) (m : (ℕ × Fin r) →₀ ℕ) :
    LvirN r k 0 (monomial m c)
      = ((Finsupp.weight weightFnN m : ℕ) : ℂ) • (monomial m c : FockN r) := by
  classical
  induction m using Finsupp.induction with
  | zero =>
    rw [monomial_zero', LvirN_zero_C r k,
      show (Finsupp.weight weightFnN (0 : (ℕ × Fin r) →₀ ℕ) : ℕ) = 0 from map_zero _,
      Nat.cast_zero, zero_smul]
  | single_add ia e m hmi he ih =>
    rw [monomial_single_add, LvirN_zero_mulXN_pow r k hk ia.2 ia.1 e (monomial m c), ih]
    rw [show (Finsupp.weight weightFnN (Finsupp.single ia e + m) : ℕ)
          = e * (ia.1 + 1) + (Finsupp.weight weightFnN m : ℕ) from by
        rw [map_add, Finsupp.weight_single, weightFnN_apply, smul_eq_mul]]
    rw [mul_smul_comm]
    push_cast
    module

/-- **`L₀` acts as the weighted degree on every homogeneous piece**. -/
theorem LvirN_zero_gradingWN (r : ℕ) (k : ℂ) (hk : k ≠ 0) {w : ℕ} {p : FockN r}
    (hp : p ∈ gradingWN r w) : LvirN r k 0 p = (w : ℂ) • p := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  conv_rhs => rw [p.as_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hwa : Finsupp.weight weightFnN a = w := by
    rw [mem_gradingWN] at hp
    exact hp (MvPolynomial.mem_support_iff.mp ha)
  rw [LvirN_zero_monomial r k hk (MvPolynomial.coeff a p) a, hwa]

/-- **VOA2 (conformal weight)**: `L₀ = mode (YN ωN) 1` acts on `gradingZN n` as `n`. -/
theorem conf_L0_gradingN (r : ℕ) (k : ℂ) (hk : k ≠ 0) {n : ℤ} (v : FockN r)
    (hv : v ∈ gradingZN r n) : mode (YN r k (ωN r k)) 1 v = (n : ℂ) • v := by
  rw [show (1 : ℤ) = (0 : ℤ) + 1 from rfl, ← LvirN_eq_mode_YN_omega]
  rcases lt_or_ge n 0 with hn | hn
  · rw [gradingZN_of_neg hn, Submodule.mem_bot] at hv
    rw [hv, map_zero, smul_zero]
  · rw [gradingZN_of_nonneg hn] at hv
    rw [LvirN_zero_gradingWN r k hk hv]
    congr 1
    have : ((n.toNat : ℤ) : ℂ) = (n : ℂ) := by rw [Int.toNat_of_nonneg hn]
    rwa [Int.cast_natCast] at this

/-! ## §7  VOA3 — translation `YN(L₋₁ v) = ∂ YN(v)` for ALL states, via Goddard. -/

/-- **Base**: the basic current `αᵃ(z)` is `L₋₁`-covariant (`D = LvirN(-1)`). -/
theorem currentN_DCovariant (r : ℕ) (k : ℂ) (hk : k ≠ 0) (a : Fin r) :
    DCovariant (LvirN r k (-1)) (currentN r k a) := by
  intro m
  rw [currentN_apply, currentN_apply, show -(m + 1) - 1 = -m - 2 from by ring]
  have h := LvirN_comm_oscN r k hk a (-1) (-m - 1)
  rw [show (-1 : ℤ) + (-m - 1) = -m - 2 from by ring] at h
  rw [h, show (-(((-m - 1 : ℤ)) : ℂ)) = ((m + 1 : ℤ) : ℂ) from by push_cast; ring,
    Int.cast_smul_eq_zsmul ℂ (m + 1) (oscN r k a (-m - 2))]

/-- The generator fields `genFieldN k a i` are `L₋₁`-covariant. -/
theorem genFieldN_DCovariant (r : ℕ) (k : ℂ) (hk : k ≠ 0) (a : Fin r) (i : ℕ) :
    DCovariant (LvirN r k (-1)) (genFieldN r k a i) := by
  rw [genFieldN, dcurrentN]
  exact ((currentN_DCovariant r k hk a).deriv_iterate i).smul _

/-- The word fields `YwordN k l` are `L₋₁`-covariant. -/
theorem YwordN_DCovariant (r : ℕ) (k : ℂ) (hk : k ≠ 0) : ∀ l : List (ℕ × Fin r),
    DCovariant (LvirN r k (-1)) (YwordN r k l)
  | [] => by rw [YwordN_nil]; exact DCovariant.idField
  | (ia :: rest) => by
      rw [YwordN_cons]
      exact DCovariant.nprod (genFieldN_isField r k ia.2 ia.1) (YwordN_isField r k rest)
        (genFieldN_DCovariant r k hk ia.2 ia.1) (YwordN_DCovariant r k hk rest)

/-- The monomial fields `YmonN k a` are `L₋₁`-covariant. -/
theorem YmonN_DCovariant (r : ℕ) (k : ℂ) (hk : k ≠ 0) (a : (ℕ × Fin r) →₀ ℕ) :
    DCovariant (LvirN r k (-1)) (YmonN r k a) :=
  YwordN_DCovariant r k hk (monoWordN a)

/-- **Operator translation covariance** for EVERY state: `YN k v` is `L₋₁`-covariant. -/
theorem YN_DCovariant (r : ℕ) (k : ℂ) (hk : k ≠ 0) (v : FockN r) :
    DCovariant (LvirN r k (-1)) (YN r k v) := by
  classical
  rw [show YN r k v = Finsupp.linearCombination ℂ (YmonN r k) v from rfl,
    Finsupp.linearCombination_apply, Finsupp.sum]
  exact DCovariant.finsetSum _ _ (fun a _ => (YmonN_DCovariant r k hk a).smul _)

/-- The bare `PreVertexAlgebra (FockN r)` (VA1–VA5), for Goddard uniqueness. -/
noncomputable def heisVAN (r : ℕ) (k : ℂ) (_hk : k ≠ 0) : PreVertexAlgebra (FockN r) where
  grading := gradingZN r
  isInternal := gradingZN_isInternal r
  finrank := gradingZN_finrank r
  Y := YN r k
  vacuum := vacuumN r
  vacuum_mem := mem_gradingZN_of_gradingWN (vacuumN_mem_gradingWN r)
  grading_mode := fun u hu v hv n => va1N_grading_mode r k u hu v hv n
  vacuum_Y := by
    rw [YN_vacuum]
    funext j
    rw [idFieldN_apply, FormalDist.one_apply]
    split_ifs <;> rfl
  creation := fun u => YN_creation r k u
  locality := fun u v => YN_local r k u v
  regularity := fun u v => va5N_regularity r k u v

/-- **The creation recursion** from `L₋₁`-covariance. -/
theorem YN_creation_recursion (r : ℕ) (k : ℂ) (hk : k ≠ 0) (v : FockN r) (m : ℤ) :
    LvirN r k (-1) ((YN r k v) m (vacuumN r)) = ((m + 1 : ℤ)) • ((YN r k v) (m + 1) (vacuumN r)) := by
  have h := congrArg (fun (T : End ℂ (FockN r)) => T (vacuumN r)) (YN_DCovariant r k hk v m)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [LvirN_vacuum r k (by norm_num : (-1 : ℤ) ≤ -1), map_zero, sub_zero] at h
  exact h

/-- **The bridge `T = L₋₁`**: `L₋₁ v = (YN v)_1 1`. -/
theorem LvirN_neg_one_eq_smul_vacuum (r : ℕ) (k : ℂ) (hk : k ≠ 0) (v : FockN r) :
    LvirN r k (-1) v = (YN r k v) 1 (vacuumN r) := by
  have h := YN_creation_recursion r k hk v 0
  rw [show ((YN r k v) 0 (vacuumN r)) = v from YN_creation_zero r k v,
    show (0 : ℤ) + 1 = 1 from rfl, one_smul] at h
  exact h

/-- Both candidate fields vanish below index `0`. -/
theorem translationN_vacuum_cond_neg (r : ℕ) (k : ℂ) (v : FockN r) {m : ℤ} (hm : m < 0) :
    (deriv (YN r k v)) m (vacuumN r) = (YN r k (LvirN r k (-1) v)) m (vacuumN r) := by
  rw [YN_creation_lt r k (LvirN r k (-1) v) hm, deriv_apply]
  show (m + 1 : ℤ) • ((YN r k v) (m + 1) (vacuumN r)) = 0
  rcases lt_or_eq_of_le (by omega : m ≤ -1) with hlt | he
  · rw [YN_creation_lt r k v (by omega : (m + 1 : ℤ) < 0)]; simp
  · rw [show (m + 1 : ℤ) = 0 from by omega, zero_smul]

/-- **The vacuum condition for Goddard**: `(∂ YN(v))_m 1 = (YN(L₋₁v))_m 1` for every `m`. -/
theorem translationN_vacuum_cond (r : ℕ) (k : ℂ) (hk : k ≠ 0) (v : FockN r) (m : ℤ) :
    (deriv (YN r k v)) m (vacuumN r) = (YN r k (LvirN r k (-1) v)) m (vacuumN r) := by
  by_cases hm : 0 ≤ m
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = (j : ℤ) := ⟨m.toNat, by omega⟩
    clear hm
    induction j with
    | zero =>
        rw [Nat.cast_zero, deriv_apply]
        show (0 + 1 : ℤ) • ((YN r k v) (0 + 1) (vacuumN r))
          = (YN r k (LvirN r k (-1) v)) 0 (vacuumN r)
        rw [show (0 : ℤ) + 1 = 1 from rfl, one_smul,
          YN_creation_zero r k (LvirN r k (-1) v), LvirN_neg_one_eq_smul_vacuum r k hk v]
    | succ i ih =>
        have hrecB1 : LvirN r k (-1) ((deriv (YN r k v)) (i : ℤ) (vacuumN r))
            = ((i : ℤ) + 1) • (deriv (YN r k v)) ((i : ℤ) + 1) (vacuumN r) := by
          have e1 : (deriv (YN r k v)) (i : ℤ) (vacuumN r)
              = ((i : ℤ) + 1) • ((YN r k v) ((i : ℤ) + 1) (vacuumN r)) := by
            rw [deriv_apply]; rfl
          have e2 : (deriv (YN r k v)) ((i : ℤ) + 1) (vacuumN r)
              = ((i : ℤ) + 1 + 1) • ((YN r k v) ((i : ℤ) + 1 + 1) (vacuumN r)) := by
            rw [deriv_apply]; rfl
          rw [e1, e2, map_zsmul, YN_creation_recursion r k hk v ((i : ℤ) + 1), smul_smul]
        have hrecB2 : LvirN r k (-1) ((YN r k (LvirN r k (-1) v)) (i : ℤ) (vacuumN r))
            = ((i : ℤ) + 1) • (YN r k (LvirN r k (-1) v)) ((i : ℤ) + 1) (vacuumN r) :=
          YN_creation_recursion r k hk (LvirN r k (-1) v) (i : ℤ)
        have hkey : ((i : ℤ) + 1) • (deriv (YN r k v)) ((i : ℤ) + 1) (vacuumN r)
            = ((i : ℤ) + 1) • (YN r k (LvirN r k (-1) v)) ((i : ℤ) + 1) (vacuumN r) := by
          rw [← hrecB1, ← hrecB2, ih]
        have hc : (((i : ℤ) + 1 : ℤ) : ℂ) ≠ 0 := by rw [Int.cast_ne_zero]; omega
        rw [← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) + 1),
          ← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) + 1)] at hkey
        rw [Nat.cast_succ]
        exact smul_right_injective (FockN r) hc hkey
  · exact translationN_vacuum_cond_neg r k v (by omega)

/-- **VOA3 translation for ALL states**: `YN(L₋₁v) = ∂ YN(v)` (Goddard uniqueness). -/
theorem translation_allN (r : ℕ) (k : ℂ) (hk : k ≠ 0) (v : FockN r) :
    YN r k (LvirN r k (-1) v) = deriv (YN r k v) := by
  classical
  refine (PreVertexAlgebra.goddard_uniqueness (heisVAN r k hk) (deriv (YN r k v)) (LvirN r k (-1) v)
    (fun b => ?_) (fun m => ?_)).symm
  · exact (YN_local r k v b).derivL
  · exact translationN_vacuum_cond r k hk v m

/-- **VOA3 in the structure shape**: `YN(ω₍₀₎ v) = ∂ YN(v)` with `L₋₁ = mode (YN ωN) 0`. -/
theorem conf_translationN (r : ℕ) (k : ℂ) (hk : k ≠ 0) (v : FockN r) :
    YN r k (mode (YN r k (ωN r k)) 0 v) = deriv (YN r k v) := by
  have hbridge : mode (YN r k (ωN r k)) 0 v = LvirN r k (-1) v := by
    have := LvirN_eq_mode_YN_omega r k (-1)
    rw [show (-1 : ℤ) + 1 = 0 from by ring] at this
    rw [this]
  rw [hbridge]
  exact translation_allN r k hk v

/-! ## §8  `ωN ∈ gradingZN 2` (weight 2). -/

/-- Each per-family `ωNa = (1/2k)(X_{(0,a)})²` lies in `gradingWN 2`. -/
theorem ωNa_mem_gradingWN (r : ℕ) (k : ℂ) (a : Fin r) : ωNa r k a ∈ gradingWN r 2 := by
  rw [ωNa, oscN_neg_one_sq_vacuumN]
  refine (gradingWN r 2).smul_mem _ ?_
  rw [mem_gradingWN, X_zero_sq_eq_monomialN]
  exact isWeightedHomogeneous_monomial weightFnN (Finsupp.single (0, a) 2) (1 : ℂ)
    (show Finsupp.weight weightFnN (Finsupp.single ((0 : ℕ), a) 2) = 2 from by
      rw [Finsupp.weight_single, weightFnN_apply, smul_eq_mul]; rfl)

/-- The conformal vector `ωN = ∑_a ωNa` lies in `gradingWN 2`. -/
theorem ωN_mem_gradingWN (r : ℕ) (k : ℂ) : ωN r k ∈ gradingWN r 2 := by
  rw [ωN]
  exact Submodule.sum_mem _ (fun a _ => ωNa_mem_gradingWN r k a)

/-- **`ωN ∈ gradingZN 2`**, the `VertexOperatorAlgebra.conformal_mem` form. -/
theorem ωN_mem_gradingZN_two (r : ℕ) (k : ℂ) : ωN r k ∈ gradingZN r 2 := by
  have h := mem_gradingZN_of_gradingWN (ωN_mem_gradingWN r k)
  rwa [show ((2 : ℕ) : ℤ) = (2 : ℤ) from rfl] at h

/-! ## §9  THE INSTANCE — `heisenbergNVOA r k hk : VertexOperatorAlgebra (FockN r)`. -/

/-- **The rank-`r` Heisenberg / free-boson vertex operator algebra** (Gannon §5.2.2), level
`k ≠ 0`.  Conformal vector `ωN = ∑_a (1/2k)aᵃ₋₁aᵃ₋₁1`, central charge `c = r` (one boson per
family, cross-family commuting).  Every VOA field is supplied by a proved rank-`r` lemma; VOA3
is closed via Goddard uniqueness + `L₋₁`-covariance summed over the families. -/
noncomputable def heisenbergNVOA (r : ℕ) (k : ℂ) (hk : k ≠ 0) :
    VertexOperatorAlgebra (FockN r) where
  toPreVertexAlgebra := heisVAN r k hk
  conformalVector := ωN r k
  conformal_mem := ωN_mem_gradingZN_two r k
  centralCharge := (r : ℂ)
  virasoro := fun m n => conf_virasoroN r k hk m n
  L0_grading := fun v hv => conf_L0_gradingN r k hk v hv
  translation := fun v => conf_translationN r k hk v
  vacuum_grade := gradingZN_zero_eq_span_vacuum r
  positivity := fun n hn => gradingZN_positivity r n hn

/-- **The central charge of the rank-`r` Heisenberg VOA is `r`** (one free boson per family). -/
theorem heisenbergN_central_charge (r : ℕ) (k : ℂ) (hk : k ≠ 0) :
    (heisenbergNVOA r k hk).centralCharge = (r : ℂ) := rfl

/-! ## §10  Axiom audit -/

end HeisenbergN

end VOA

namespace VOA.HeisenbergN
end VOA.HeisenbergN
