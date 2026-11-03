import VOA.Huang.GenusOneWardKernels

/-!
# Abstract assembly of the two-point minus-one Ward identity

Families `F j`, `G j` (left and right descendants), `A p` (mode at the trace
boundary) and `M i` (mode between the two insertions) in `ℂ⟦u⟧⟦t⟧`, subject to
q-graded cyclicity, the zero-mode relation, the commutator relation and the
normal-order expansion of the minus-one mode, satisfy the collected identity
with Eisenstein series `eis` and spatial kernels `piK`. This is the two-point
analogue of `VOA.zhu_abstract_assembly`.
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open PowerSeries
open scoped BigOperators

theorem c2_lsum (T : ℕ → R2) (n k : ℕ) : c2 (lsum T) n k = ∑ᶠ i, c2 (T i) n k := by
  rw [lsum, c2_mk2]

theorem locFin_of_eventually_uu {T : ℕ → R2} (m : ℕ) (U : ℕ → R2)
    (h : ∀ i, m ≤ i → T i = uu ^ (i - m + 1) * U i) : LocFin T := by
  intro n k
  refine ⟨n + m, fun i hi => ?_⟩
  rw [h i (by omega), c2_uu_pow_mul, if_neg (by omega)]

theorem locFin_of_eventually_tt {T : ℕ → R2} (m : ℕ) (U : ℕ → R2)
    (h : ∀ i, m ≤ i → T i = tt ^ (i - m + 1) * U i) : LocFin T := by
  intro n k
  refine ⟨k + m, fun i hi => ?_⟩
  rw [h i (by omega), c2_tt_pow_mul, if_neg (by omega)]

/-- Recentring a doubly infinite coefficientwise-finite sum at `c`. -/
theorem lsum_int_recentre (S : ℤ → R2) (c : ℤ)
    (h1 : LocFin fun i : ℕ => S (-1 - i)) (h2 : LocFin fun i : ℕ => S i) :
    lsum (fun i : ℕ => S (-1 - i) + S i) =
      S c + lsum (fun i : ℕ => S (c - 1 - i) + S (c + 1 + i)) := by
  apply ext2
  intro n k
  set f : ℤ → ℂ := fun p => c2 (S p) n k with hf
  obtain ⟨B₁, hB₁⟩ := h1 n k
  obtain ⟨B₂, hB₂⟩ := h2 n k
  have hfin : (Function.support f).Finite := by
    refine (Set.finite_Icc (-(B₁ : ℤ)) (B₂ : ℤ)).subset fun p hp => ?_
    simp only [Function.mem_support, ne_eq] at hp
    simp only [Set.mem_Icc]
    by_contra hc
    rcases not_and_or.mp hc with h | h
    · push Not at h
      apply hp
      have := hB₁ (-1 - p).toNat (by omega)
      simp only at this
      rw [show -1 - (((-1 - p).toNat : ℕ) : ℤ) = p by omega] at this
      exact this
    · push Not at h
      apply hp
      have := hB₂ p.toNat (by omega)
      simp only at this
      rw [show (((p.toNat : ℕ)) : ℤ) = p by omega] at this
      exact this
  have hsupp (g : ℕ → ℤ) (hg : Function.Injective g) :
      (Function.support fun i : ℕ => f (g i)).Finite :=
    (hfin.preimage (hg.injOn)).subset fun i hi => hi
  rw [c2_add, c2_lsum, c2_lsum]
  simp only [c2_add]
  rw [finsum_add_distrib (hsupp _ (fun a b h => by simpa using h))
      (hsupp _ (fun a b h => by simpa using h)),
    finsum_add_distrib (hsupp _ (fun a b h => by simpa using h))
      (hsupp _ (fun a b h => by simpa using h))]
  have hA := finsum_int_split_at f hfin 0
  have hB := finsum_int_split_three f hfin c
  simp only [zero_add, zero_sub] at hA
  change (∑ᶠ i : ℕ, f (-1 - i)) + ∑ᶠ i : ℕ, f i =
    f c + ((∑ᶠ i : ℕ, f (c - 1 - i)) + ∑ᶠ i : ℕ, f (c + 1 + i))
  rw [add_comm (∑ᶠ i : ℕ, f (-1 - i)), ← hA, hB]
  ring

/-- Odd reindexing for an `R2`-valued sum. -/
theorem sum_range_two_mul_odd_gen (g : ℕ → R2) (N : ℕ) :
    ∑ n ∈ Finset.range (2 * N), (if Odd n then g n else 0) =
      ∑ m ∈ Finset.range N, g (2 * m + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have h1 : ¬Odd (2 * N) := by
      rw [Nat.not_odd_iff_even]; exact ⟨N, by ring⟩
    have h2 : Odd (2 * N + 1) := ⟨N, rfl⟩
    rw [if_neg h1, if_pos h2, add_zero]

/-- The F-coefficient identity: (I1), (I2) and Pascal. -/
theorem f_coeff_identity {kc : ℕ} (hk : 1 ≤ kc) {j K : ℕ} (hj : j < K) :
    ∑ m ∈ Finset.range K, sqBracketCoeff kc m j • xiK m -
        cbz (kc : ℤ) ((j : ℤ) + 1) • (1 : R2) + sqBracketCoeffZ kc (-1) j • (1 : R2) =
      ∑ m ∈ Finset.range K, sqBracketCoeff kc (2 * m + 1) j • eis (m + 1) -
        ((1 / 2 : ℂ) * cbz ((kc : ℤ) - 1) (j : ℤ)) • (1 : R2) := by
  -- odd part of the Lambert sum
  have hext : ∑ m ∈ Finset.range K, sqBracketCoeff kc m j • xiK m =
      ∑ m ∈ Finset.range (2 * K), sqBracketCoeff kc m j • xiK m := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro m _ hm
    rw [Finset.mem_range, not_lt] at hm
    rw [sqBracketCoeff_eq_zero_of_lt kc (by omega), zero_smul]
  have hodd : ∑ m ∈ Finset.range (2 * K), sqBracketCoeff kc m j • xiK m =
      ∑ m ∈ Finset.range K, sqBracketCoeff kc (2 * m + 1) j • xiK (2 * m + 1) := by
    rw [← sum_range_two_mul_odd_gen (fun n => sqBracketCoeff kc n j • xiK n)]
    apply Finset.sum_congr rfl
    intro m _
    split_ifs with h
    · rfl
    · obtain ⟨m', hm'⟩ := Nat.not_odd_iff_even.mp h
      rw [hm', show m' + m' = 2 * m' by ring, xiK_even, smul_zero]
  -- (I2) as a finite sum
  have hI2 := sqBracketCoeffZ_neg_one_eq hk j
  have hfs : (∑ᶠ m : ℕ, zhuG (m + 1) 0 * sqBracketCoeff kc (2 * m + 1) j) =
      ∑ m ∈ Finset.range K, zhuG (m + 1) 0 * sqBracketCoeff kc (2 * m + 1) j := by
    apply finsum_eq_sum_of_support_subset
    intro m hm
    simp only [Function.mem_support, ne_eq] at hm
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hm (by rw [sqBracketCoeff_eq_zero_of_lt kc (by omega), mul_zero])
  rw [hfs] at hI2
  have hpas := cbz_pascal_up ((kc : ℤ) - 1) ((j : ℤ) + 1)
  rw [show (kc : ℤ) - 1 + 1 = kc by ring, show (j : ℤ) + 1 - 1 = j by ring] at hpas
  rw [hext, hodd]
  have heis : ∀ m : ℕ, sqBracketCoeff kc (2 * m + 1) j • eis (m + 1) =
      sqBracketCoeff kc (2 * m + 1) j • xiK (2 * m + 1) +
        (zhuG (m + 1) 0 * sqBracketCoeff kc (2 * m + 1) j) • (1 : R2) := by
    intro m
    rw [eis_eq_const_add_xiK, smul_add, Algebra.algebraMap_eq_smul_one, smul_smul, add_comm,
      mul_comm (sqBracketCoeff kc _ j)]
  simp_rw [heis]
  rw [Finset.sum_add_distrib, ← Finset.sum_smul]
  have hc : sqBracketCoeffZ kc (-1) j = cbz ((kc : ℤ) - 1) ((j : ℤ) + 1) +
      (1 / 2) * cbz ((kc : ℤ) - 1) j +
      ∑ m ∈ Finset.range K, zhuG (m + 1) 0 * sqBracketCoeff kc (2 * m + 1) j := by
    linear_combination hI2
  rw [hc, hpas]
  module

/-- Regrouping a double finite sum of kernel multiples. -/
theorem sum_regroup (K K' : ℕ) (a : ℕ → ℕ → ℂ) (X : ℕ → R2) (F : ℕ → R2) :
    ∑ j ∈ Finset.range K, (∑ m ∈ Finset.range K', a m j • X m) * F j =
      ∑ m ∈ Finset.range K', X m * ∑ j ∈ Finset.range K, a m j • F j := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_mul_assoc, mul_smul_comm]

/-- Termwise expansion of the solved boundary terms. -/
theorem solved_terms_expand (K : ℕ) (F G : ℤ → R2) (kc d : ℕ) :
    -(geo d * (qq ^ d * binSum K F ((kc : ℤ) - 1 - d) + uu ^ d * binSum K G ((kc : ℤ) - 1 - d))) +
      (qq ^ d * geo d * binSum K F ((kc : ℤ) - 1 + d) +
        tt ^ d * geo d * binSum K G ((kc : ℤ) - 1 + d)) =
    ∑ j ∈ Finset.range K,
      ((cbz ((kc : ℤ) - 1 + (d : ℤ)) (j : ℤ) - cbz ((kc : ℤ) - 1 - (d : ℤ)) (j : ℤ)) •
          (qq ^ d * geo d) * F j +
        (cbz ((kc : ℤ) - 1 + (d : ℤ)) (j : ℤ) • (tt ^ d * geo d) -
          cbz ((kc : ℤ) - 1 - (d : ℤ)) (j : ℤ) • (uu ^ d * geo d)) * G j) := by
  simp only [binSum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Algebra.smul_def, map_sub]
  ring

/-- **The abstract two-point minus-one Ward identity.** -/
theorem ward_neg_one_abstract {kc : ℕ} (hk : 1 ≤ kc) (K : ℕ)
    (F G A : ℤ → R2) (M : ℕ → R2)
    (hpos : ∀ d : ℕ, 1 ≤ d → (1 - qq ^ d) * A ((kc : ℤ) - 1 - d) =
      -(qq ^ d * binSum K F ((kc : ℤ) - 1 - d) + uu ^ d * binSum K G ((kc : ℤ) - 1 - d)))
    (hneg : ∀ e : ℕ, 1 ≤ e → (1 - qq ^ e) * A ((kc : ℤ) - 1 + e) =
      binSum K F ((kc : ℤ) - 1 + e) + tt ^ e * binSum K G ((kc : ℤ) - 1 + e))
    (hzero : binSum K F ((kc : ℤ) - 1) + binSum K G ((kc : ℤ) - 1) = 0)
    (hM : ∀ i : ℕ, M i = A i - binSum K F i)
    (hI : F (-1) = lsum fun i : ℕ => A (-1 - i) + M i) :
    F (-1) + ∑ j ∈ Finset.range K, sqBracketCoeffZ kc (-1) j • F j =
      A ((kc : ℤ) - 1) +
      ∑ m ∈ Finset.range K, eis (m + 1) *
        ∑ j ∈ Finset.range K, sqBracketCoeff kc (2 * m + 1) j • F j +
      ∑ m ∈ Finset.range K, (piK m + if m = 0 then algebraMap ℂ R2 (1 / 2) else 0) *
        ∑ j ∈ Finset.range K, sqBracketCoeff kc m j • G j := by
  set L := binSum K F with hLdef
  set R := binSum K G with hRdef
  -- solved boundary terms
  set V₁ : ℕ → R2 := fun d => -(tt ^ d * geo d * L ((kc : ℤ) - 1 - d) + geo d * R ((kc : ℤ) - 1 - d))
    with hV₁
  set V₂ : ℕ → R2 := fun e => uu ^ e * geo e * L ((kc : ℤ) - 1 + e) + geo e * R ((kc : ℤ) - 1 + e)
    with hV₂
  have hA₁ : ∀ d : ℕ, 1 ≤ d → A ((kc : ℤ) - 1 - d) =
      -(geo d * (qq ^ d * L ((kc : ℤ) - 1 - d) + uu ^ d * R ((kc : ℤ) - 1 - d))) := by
    intro d hd
    rw [eq_geo_mul_of hd (hpos d hd)]
    ring
  have hA₁' : ∀ d : ℕ, 1 ≤ d → A ((kc : ℤ) - 1 - d) = uu ^ d * V₁ d := by
    intro d hd
    rw [hA₁ d hd, hV₁, qq_pow]
    ring
  have hA₂ : ∀ e : ℕ, 1 ≤ e → A ((kc : ℤ) - 1 + e) - L ((kc : ℤ) - 1 + e) =
      qq ^ e * geo e * L ((kc : ℤ) - 1 + e) + tt ^ e * geo e * R ((kc : ℤ) - 1 + e) := by
    intro e he
    rw [eq_geo_mul_of he (hneg e he)]
    have h := geo_sub_one he
    linear_combination L ((kc : ℤ) - 1 + e) * h
  have hA₂' : ∀ e : ℕ, 1 ≤ e → A ((kc : ℤ) - 1 + e) - L ((kc : ℤ) - 1 + e) = tt ^ e * V₂ e := by
    intro e he
    rw [hA₂ e he, hV₂, qq_pow]
    ring
  -- the doubly infinite family
  set S : ℤ → R2 := fun p => A p - (if 0 ≤ p then L p else 0) with hS
  have hSneg : ∀ i : ℕ, S (-1 - i) = A (-1 - i) := by
    intro i
    simp only [hS]
    rw [if_neg (by omega), sub_zero]
  have hSnat : ∀ i : ℕ, S i = M i := by
    intro i
    simp only [hS]
    rw [if_pos (by omega), hM]
  have h1 : LocFin fun i : ℕ => S (-1 - i) := by
    apply locFin_of_eventually_uu 0 (fun i => uu ^ (kc - 1) * V₁ (kc + i))
    intro i _
    rw [hSneg, show (-1 - (i : ℤ)) = (kc : ℤ) - 1 - ((kc + i : ℕ) : ℤ) by push_cast; ring,
      hA₁' _ (by omega), ← mul_assoc, ← pow_add]
    congr 2
    omega
  have h2 : LocFin fun i : ℕ => S i := by
    apply locFin_of_eventually_tt kc (fun i => V₂ (i - kc + 1))
    intro i hi
    rw [hSnat, hM, show ((i : ℕ) : ℤ) = (kc : ℤ) - 1 + ((i - kc + 1 : ℕ) : ℤ) by push_cast; omega,
      hA₂' _ (by omega)]
  have hIS : F (-1) = lsum fun i : ℕ => S (-1 - i) + S i := by
    rw [hI]
    apply lsum_congr
    intro i
    rw [hSneg, hSnat]
  rw [lsum_int_recentre S ((kc : ℤ) - 1) h1 h2] at hIS
  -- the recentred terms
  set X : ℕ → R2 := fun i =>
    -(geo (i + 1) * (qq ^ (i + 1) * L ((kc : ℤ) - 1 - ((i + 1 : ℕ) : ℤ)) +
        uu ^ (i + 1) * R ((kc : ℤ) - 1 - ((i + 1 : ℕ) : ℤ)))) +
      (qq ^ (i + 1) * geo (i + 1) * L ((kc : ℤ) - 1 + ((i + 1 : ℕ) : ℤ)) +
        tt ^ (i + 1) * geo (i + 1) * R ((kc : ℤ) - 1 + ((i + 1 : ℕ) : ℤ))) with hX
  set Y : ℕ → R2 := fun i =>
    if ((i : ℤ) ≤ (kc : ℤ) - 2) then L ((kc : ℤ) - 2 - i) else 0 with hY
  have hterm : ∀ i : ℕ, S ((kc : ℤ) - 1 - 1 - i) + S ((kc : ℤ) - 1 + 1 + i) = X i - Y i := by
    intro i
    have e1 : (kc : ℤ) - 1 - 1 - i = (kc : ℤ) - 1 - ((i + 1 : ℕ) : ℤ) := by push_cast; ring
    have e2 : (kc : ℤ) - 1 + 1 + i = (kc : ℤ) - 1 + ((i + 1 : ℕ) : ℤ) := by push_cast; ring
    simp only [hS, hX, hY]
    rw [e1, e2, hA₁ _ (by omega),
      if_pos (show (0 : ℤ) ≤ (kc : ℤ) - 1 + ((i + 1 : ℕ) : ℤ) by omega)]
    have h3 := hA₂ (i + 1) (by omega)
    by_cases hi : (i : ℤ) ≤ (kc : ℤ) - 2
    · rw [if_pos (show (0 : ℤ) ≤ (kc : ℤ) - 1 - ((i + 1 : ℕ) : ℤ) by push_cast; omega),
        if_pos hi, show (kc : ℤ) - 2 - i = (kc : ℤ) - 1 - ((i + 1 : ℕ) : ℤ) by
        push_cast; ring]
      linear_combination h3
    · rw [if_neg (show ¬ (0 : ℤ) ≤ (kc : ℤ) - 1 - ((i + 1 : ℕ) : ℤ) by push_cast; omega),
        if_neg hi]
      linear_combination h3
  have hXloc : LocFin X := by
    have ha : LocFin fun i => uu ^ (i + 1) * V₁ (i + 1) :=
      locFin_uu_pow (fun i => V₁ (i + 1)) (fun i => i + 1) (fun i => Nat.le_succ i)
    have hb : LocFin fun i => tt ^ (i + 1) * V₂ (i + 1) :=
      locFin_tt_pow (fun i => V₂ (i + 1)) (fun i => i + 1) (fun i => Nat.le_succ i)
    have he : X = fun i => uu ^ (i + 1) * V₁ (i + 1) + tt ^ (i + 1) * V₂ (i + 1) := by
      funext i
      simp only [hX, hV₁, hV₂, qq_pow]
      ring
    rw [he]
    exact ha.add hb
  have hYloc : ∀ i, kc - 1 ≤ i → Y i = 0 := by
    intro i hi
    simp only [hY]
    rw [if_neg (by omega)]
  have hYsum : lsum Y = ∑ i ∈ Finset.range (kc - 1), L i := by
    rw [lsum_eq_of_eventually_zero (kc - 1) hYloc]
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    simp only [hY]
    rw [if_pos (by omega)]
    congr 1
    omega
  rw [lsum_congr hterm, lsum_sub hXloc (locFin_of_eventually_zero _ hYloc), hYsum] at hIS
  -- expand X
  have hXexp : ∀ i : ℕ, X i = ∑ j ∈ Finset.range K,
      ((cbz ((kc : ℤ) - 1 + ((i + 1 : ℕ) : ℤ)) (j : ℤ) -
          cbz ((kc : ℤ) - 1 - ((i + 1 : ℕ) : ℤ)) (j : ℤ)) • (qq ^ (i + 1) * geo (i + 1)) * F j +
        (cbz ((kc : ℤ) - 1 + ((i + 1 : ℕ) : ℤ)) (j : ℤ) • (tt ^ (i + 1) * geo (i + 1)) -
          cbz ((kc : ℤ) - 1 - ((i + 1 : ℕ) : ℤ)) (j : ℤ) • (uu ^ (i + 1) * geo (i + 1))) * G j) :=
    fun i => solved_terms_expand K F G kc (i + 1)
  have hlocF : ∀ j : ℕ, LocFin fun i : ℕ =>
      (cbz ((kc : ℤ) - 1 + ((i + 1 : ℕ) : ℤ)) (j : ℤ) -
        cbz ((kc : ℤ) - 1 - ((i + 1 : ℕ) : ℤ)) (j : ℤ)) • (qq ^ (i + 1) * geo (i + 1)) :=
    fun j => locFin_qq_geo _
  have hlocG : ∀ j : ℕ, LocFin fun i : ℕ =>
      cbz ((kc : ℤ) - 1 + ((i + 1 : ℕ) : ℤ)) (j : ℤ) • (tt ^ (i + 1) * geo (i + 1)) -
        cbz ((kc : ℤ) - 1 - ((i + 1 : ℕ) : ℤ)) (j : ℤ) • (uu ^ (i + 1) * geo (i + 1)) :=
    fun j => (locFin_tt_geo _).sub (locFin_uu_geo _)
  have hlsumX : lsum X = ∑ j ∈ Finset.range K,
      ((∑ m ∈ Finset.range K, sqBracketCoeff kc m j • xiK m) * F j +
        (∑ m ∈ Finset.range K, sqBracketCoeff kc m j • piK m) * G j) := by
    rw [lsum_congr hXexp, lsum_finset_sum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [lsum_add ((hlocF j).mul_right _) ((hlocG j).mul_right _),
        lsum_mul_right (hlocF j), lsum_mul_right (hlocG j),
        lsum_lambert_eq_xiK hk hj, lsum_spatial_eq_piK hk hj]
    · intro j _
      exact ((hlocF j).mul_right _).add ((hlocG j).mul_right _)
  rw [hlsumX] at hIS
  -- the hockey-stick constant
  have hhock : L ((kc : ℤ) - 1) + ∑ i ∈ Finset.range (kc - 1), L i =
      ∑ j ∈ Finset.range K, (cbz (kc : ℤ) ((j : ℤ) + 1) • (1 : R2)) * F j := by
    have hsplit : L ((kc : ℤ) - 1) + ∑ i ∈ Finset.range (kc - 1), L i =
        ∑ i ∈ Finset.range kc, L i := by
      conv_rhs => rw [show kc = kc - 1 + 1 by omega, Finset.sum_range_succ]
      rw [add_comm]
      congr 2
      push_cast [Nat.cast_sub hk]
      ring
    rw [hsplit, hLdef]
    simp only [binSum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_smul, sum_range_cbz_eq kc (by omega : (0 : ℤ) ≤ j), smul_mul_assoc, one_mul]
  -- the simplified identity
  have hS0 : S ((kc : ℤ) - 1) = A ((kc : ℤ) - 1) - L ((kc : ℤ) - 1) := by
    simp only [hS]
    rw [if_pos (by omega)]
  have hmain : F (-1) = A ((kc : ℤ) - 1) +
      ∑ j ∈ Finset.range K,
        ((∑ m ∈ Finset.range K, sqBracketCoeff kc m j • xiK m) -
          cbz (kc : ℤ) ((j : ℤ) + 1) • (1 : R2)) * F j +
      ∑ m ∈ Finset.range K, piK m * ∑ j ∈ Finset.range K, sqBracketCoeff kc m j • G j := by
    rw [hIS, hS0, ← sum_regroup K K (fun m j => sqBracketCoeff kc m j) piK (fun j => G j)]
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [← hhock, Finset.sum_add_distrib]
    ring
  -- collect with the coefficient identity
  have hcoef : ∀ j ∈ Finset.range K,
      ((∑ m ∈ Finset.range K, sqBracketCoeff kc m j • xiK m) -
          cbz (kc : ℤ) ((j : ℤ) + 1) • (1 : R2)) * F j +
        sqBracketCoeffZ kc (-1) j • F j =
      (∑ m ∈ Finset.range K, sqBracketCoeff kc (2 * m + 1) j • eis (m + 1)) * F j -
        ((1 / 2 : ℂ) * cbz ((kc : ℤ) - 1) (j : ℤ)) • F j := by
    intro j hj
    have h := f_coeff_identity hk (Finset.mem_range.mp hj)
    rw [← smul_one_mul (sqBracketCoeffZ kc (-1) (j : ℤ)) (F j), ← add_mul,
      ← smul_one_mul ((1 / 2 : ℂ) * cbz ((kc : ℤ) - 1) (j : ℤ)) (F j), ← sub_mul, h]
  -- zero mode
  have h0 : ∀ j : ℕ, sqBracketCoeff kc 0 j = cbz ((kc : ℤ) - 1) (j : ℤ) := by
    intro j
    rw [cbz_eq_sqBracketCoeffZ_zero kc hk, ← sqBracketCoeffZ_of_nonneg, Nat.cast_zero]
  have hz : ∑ j ∈ Finset.range K, ((1 / 2 : ℂ) * cbz ((kc : ℤ) - 1) (j : ℤ)) • F j =
      -(algebraMap ℂ R2 (1 / 2) * ∑ j ∈ Finset.range K, sqBracketCoeff kc 0 j • G j) := by
    have hz' : binSum K F ((kc : ℤ) - 1) = -binSum K G ((kc : ℤ) - 1) := by
      linear_combination hzero
    have e1 : ∑ j ∈ Finset.range K, ((1 / 2 : ℂ) * cbz ((kc : ℤ) - 1) (j : ℤ)) • F j =
        (1 / 2 : ℂ) • binSum K F ((kc : ℤ) - 1) := by
      simp only [binSum, Finset.smul_sum, mul_smul]
    simp only [h0]
    rw [e1, hz', Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_neg, binSum]
  have hE : ∑ j ∈ Finset.range K,
      (((∑ m ∈ Finset.range K, sqBracketCoeff kc m j • xiK m) -
          cbz (kc : ℤ) ((j : ℤ) + 1) • (1 : R2)) * F j + sqBracketCoeffZ kc (-1) j • F j) =
      ∑ m ∈ Finset.range K, eis (m + 1) *
          ∑ j ∈ Finset.range K, sqBracketCoeff kc (2 * m + 1) j • F j +
        algebraMap ℂ R2 (1 / 2) * ∑ j ∈ Finset.range K, sqBracketCoeff kc 0 j • G j := by
    rw [Finset.sum_congr rfl hcoef, Finset.sum_sub_distrib,
      sum_regroup K K (fun m j => sqBracketCoeff kc (2 * m + 1) j) (fun m => eis (m + 1))
        (fun j => F j), hz]
    ring
  have hP : ∑ m ∈ Finset.range K, (piK m + if m = 0 then algebraMap ℂ R2 (1 / 2) else 0) *
        ∑ j ∈ Finset.range K, sqBracketCoeff kc m j • G j =
      ∑ m ∈ Finset.range K, piK m * ∑ j ∈ Finset.range K, sqBracketCoeff kc m j • G j +
        algebraMap ℂ R2 (1 / 2) * ∑ j ∈ Finset.range K, sqBracketCoeff kc 0 j • G j := by
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_range]
    split_ifs with hK
    · rfl
    · have : K = 0 := by omega
      subst this
      simp
  rw [Finset.sum_add_distrib] at hE
  rw [hP]
  linear_combination hmain + hE

end VOA.Huang.GenusOneWard
