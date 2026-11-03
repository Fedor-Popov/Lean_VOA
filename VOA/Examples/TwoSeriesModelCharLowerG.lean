/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesModelCharChain
import VOA.Examples.TwoSeriesModelCharLower

/-!
# Independence of the Gordon-profile functionals on `S_{n,r}`, for every `n`

For a profile `P` (a list of length `n` of colour multiplicities), a charge `k`, a row `λ` and
exponents `x`, the functional

  `Λ_{P,k,λ,x} = [u_λ v_0^l] ∘ E_{top(x)} ∘ Φ_{ψ(fFS P x)}`              (`LamG`)

evaluates on the block products of `P`'s own colouring to `[t^a] (N_P · VL · FamL · Apol)`
(`LamG_push_own`), and on the block products of another profile `P0` to `0` whenever `P` has
smaller `T`-degree (`LamG_push_lt`) or no valid slot assignment (`LamG_push_noValid`).
Choosing `P0` with maximal `T`-degree and then minimal copy-count potential gives

* `idxP_indep` — independence of the functionals of one profile;
* `tIdxG_indep` — **joint independence of all profile functionals with `r` letters** on the
  weight-`N` part of `S_{n,r}`;
* `card_tIdxG_le_finrank` — `#indices ≤ dim S_{n,r,N}`.

Everything is proved outright.
-/

namespace VOA.TwoSeries.ModelChar

open MvPolynomial VOA.SymbolModel VOA.TwoSeries.StrictModel VOA.JetProduct
open scoped BigOperators

noncomputable section

/-! ### The top exponent -/

/-- The exponent of the operator `E` of a profile functional. -/
def topExp : (P : List ℕ) → ExpL P → Fin (nbL P) → ℕ
  | [], _ => Fin.elim0
  | _ :: P, x => (Fin.append x.1 (fun _ : Fin (nbL P) => 0) : Fin (_ + nbL P) → ℕ)

theorem esymmPow_topExp : ∀ (P : List ℕ) (x : ExpL P), esymmPow (topExp P x) = topL P x
  | [], x => by
    show (∏ i : Fin 0, esymm (Fin 0) ℂ ((i : ℕ) + 1) ^ topExp [] x i) = 1
    simp
  | _ :: _, _ => rfl

theorem awt_topExp : ∀ (P : List ℕ) (x : ExpL P), awt (topExp P x) = degTop P x
  | [], x => by
    show (∑ i : Fin 0, ((i : ℕ) + 1) * topExp [] x i) = 0
    simp
  | _ :: _, x => awt_append' x.1

theorem sum_colL (P : List ℕ) : ∑ b, colL P b = tsL P := by
  calc ∑ b, colL P b = ∑ b, (Finset.univ.filter fun v => rhoL P v = b).card := by
        simp only [card_rhoL]
    _ = (Finset.univ : Finset (Fin (tsL P))).card :=
        (Finset.card_eq_sum_card_fiberwise (f := rhoL P) (t := Finset.univ)
          (fun _ _ => Finset.mem_univ _)).symm
    _ = tsL P := by simp

theorem collKill_mono {m n s : ℕ} (hmn : m ≤ n) {F : MvPolynomial (Fin s) ℂ} (h : CollKill m F) :
    CollKill n F :=
  fun K ρ b hc => h K ρ b (hmn.trans hc)

/-! ### The profile functionals -/

/-- The index of a profile functional. -/
abbrev IdxG : Type := Σ P : List ℕ, Σ k : Fin (2 * nbL P + 1), Rows (nbL P) k × ExpL P

/-- The functional of an index (zero for profiles that are empty or too long). -/
def LamG (n : ℕ) (i : IdxG) : MPoly (Rn n) →ₗ[ℂ] ℂ :=
  if h : i.1 ≠ [] ∧ i.1.length ≤ n then
    Lam (msOf i.2.2.1) (2 * nbL i.1 - i.2.1) (topExp i.1 i.2.2.2) ∘ₗ
      VOA.TwoSeries.StrictModel.Φ (Rn n) (ψbarG n (fFS i.1 i.2.2.2) (fFS_symm i.1 i.2.2.2)
        (collKill_mono h.2 (fFS_collKill i.1 h.1 i.2.2.2)))
  else 0

theorem LamG_pos {n : ℕ} {i : IdxG} (h : i.1 ≠ [] ∧ i.1.length ≤ n) (X : MPoly TPoly) :
    LamG n i (pushN n X) = Lam (msOf i.2.2.1) (2 * nbL i.1 - i.2.1) (topExp i.1 i.2.2.2)
      (VOA.TwoSeries.StrictModel.Φ TPoly (ψF (fFS i.1 i.2.2.2)) X) := by
  rw [LamG, dif_pos h, LinearMap.comp_apply, Φ_pushN, ψbarG_comp_mk]

/-- **The functional of a profile on its own block products.** -/
theorem LamG_push_own {n : ℕ} {P : List ℕ} (hP : P ≠ [] ∧ P.length ≤ n)
    (k : Fin (2 * nbL P + 1)) (ro : Rows (nbL P) k) (x : ExpL P) (g : Fin (nbL P) → Fin 4)
    (a : Fin (nbL P) → ℕ) :
    LamG n ⟨P, k, ro, x⟩ (pushN n (pblkG TPoly X (colL P) g a)) =
      coeff (toF a) (rename (rhoL P) (fFS P x) *
        (esymmPow (topExp P x) * Apol (msOf ro) (2 * nbL P - k) g)) := by
  rw [LamG_pos (i := ⟨P, k, ro, x⟩) hP, Φ_pblkG (fFS P x) (colL P) (sum_colL P), map_sum,
    coeff_mul]
  simp only [map_smul, smul_eq_mul, ψF_tpow (fFS_symm P x) (rhoL P) (colL P) (card_rhoL P)]
  have h := sum_piFinset_antidiagonal a (fun b d =>
    coeff b (rename (rhoL P) (fFS P x)) *
      coeff d (esymmPow (topExp P x) * Apol (msOf ro) (2 * nbL P - k) g))
  simp only at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro p _
  rw [coeff_esymmPow_mul_Apol (msOf ro) _ (msOf_le ro)]

/-- A functional of smaller `T`-degree vanishes. -/
theorem LamG_push_lt {n : ℕ} (i : IdxG) {P0 : List ℕ} (hlt : tsL i.1 < tsL P0)
    (g : Fin (nbL P0) → Fin 4) (a : Fin (nbL P0) → ℕ) :
    LamG n i (pushN n (pblkG TPoly X (colL P0) g a)) = 0 := by
  by_cases h : i.1 ≠ [] ∧ i.1.length ≤ n
  · rw [LamG_pos h]
    have hlow := pblkG_lowM (colL P0) g a
    rw [sum_colL] at hlow
    rw [Φ_ψF_eq_zero _ (hlow.mono hlt), map_zero]
  · rw [LamG, dif_neg h, LinearMap.zero_apply]

/-- A functional with no valid slot assignment to the colouring of `P0` vanishes. -/
theorem LamG_push_noValid {n : ℕ} (i : IdxG) {P0 : List ℕ} (hts : tsL i.1 = tsL P0)
    (hno : ∀ σ : Equiv.Perm (Fin (tsL i.1)),
      ¬ ValidA (rhoL P0 ∘ Fin.cast hts ∘ σ) (grpL i.1))
    (g : Fin (nbL P0) → Fin 4) (a : Fin (nbL P0) → ℕ) :
    LamG n i (pushN n (pblkG TPoly X (colL P0) g a)) = 0 := by
  by_cases h : i.1 ≠ [] ∧ i.1.length ≤ n
  · rw [LamG_pos h, Φ_pblkG (fFS i.1 i.2.2.2) (colL P0) ((sum_colL P0).trans hts.symm)]
    have hρ : ∀ b, (Finset.univ.filter fun v => (rhoL P0 ∘ Fin.cast hts) v = b).card =
        colL P0 b := fun b =>
      (card_fiber_comp_equiv (rhoL P0) (finCongr hts) b).trans (card_rhoL P0 b)
    have hzero := rename_fFS_eq_zero i.1 P0 hts i.2.2.2 hno
    rw [Finset.sum_eq_zero, map_zero]
    intro p _
    rw [ψF_tpow (fFS_symm _ _) _ (colL P0) hρ, hzero, coeff_zero, zero_smul]
  · rw [LamG, dif_neg h, LinearMap.zero_apply]

/-! ### One profile -/

/-- The weight of a block product of a profile's colouring. -/
theorem sum_bwtG_colL (P : List ℕ) (g : Fin (nbL P) → Fin 4) :
    ∑ i, bwtG (colL P i) (g i) = ((nbL P + 2 * tsL P + jcount g : ℕ) : ℤ) := by
  have h1 : ∑ i, bwtG (colL P i) (g i) =
      ∑ i : Fin (nbL P), (1 : ℤ) + 2 * ∑ i, ((colL P i : ℕ) : ℤ) + ∑ i, (jflag (g i) : ℤ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp [bwtG, jflag]
  rw [h1]
  have h2 : ∑ i, ((colL P i : ℕ) : ℤ) = tsL P := by exact_mod_cast sum_colL P
  rw [h2, jcount]
  push_cast
  simp

/-- The pushed-forward block products of a profile lie in the model. -/
theorem push_pblkG_mem {n r N : ℕ} {P : List ℕ} (hr : nbL P + tsL P = r)
    (g : Fin (nbL P) → Fin 4) (a : Fin (nbL P) → ℕ)
    (hW : ∑ i, a i + jcount g + nbL P + 2 * tsL P = N) :
    pushN n (pblkG TPoly X (colL P) g a) ∈ modelDeg (Rn n) (tn n) r (N : ℤ) := by
  apply map_modelDeg
  have h := pblkG_mem TPoly X (colL P) g a
  have hs : ∑ i, (colL P i + 1) = r := by
    rw [Finset.sum_add_distrib, sum_colL]; simp; omega
  rw [hs, Finset.sum_add_distrib, sum_bwtG_colL] at h
  convert h using 2
  rw [← hW]
  push_cast
  ring

/-- The exponent box. -/
def boxE : (P : List ℕ) → ℕ → Finset (ExpL P)
  | [], _ => {()}
  | r :: P, B => (Fintype.piFinset fun _ : Fin r => Finset.range (B + 1)) ×ˢ boxE P B

/-- The indices of one profile of conformal weight `N`. -/
def idxP (P : List ℕ) (N : ℕ) : Finset (Σ k : Fin (2 * nbL P + 1), Rows (nbL P) k × ExpL P) :=
  Finset.univ.sigma fun _ => (Finset.univ ×ˢ boxE P N).filter
    fun p => (msOf p.1).sum + awtE P p.2 + nbL P + tsL P + sqL P = N

/-- The exponents completing `(k, λ)` to weight `N`. -/
def fibE (P : List ℕ) (N : ℕ) {k : ℕ} (ro : Rows (nbL P) k) : Finset (ExpL P) :=
  (boxE P N).filter fun x => (msOf ro).sum + awtE P x + nbL P + tsL P + sqL P = N

theorem sum_idxP {M : Type*} [AddCommMonoid M] {P : List ℕ} {N : ℕ}
    (f : (Σ k : Fin (2 * nbL P + 1), Rows (nbL P) k × ExpL P) → M) :
    ∑ i ∈ idxP P N, f i =
      ∑ k : Fin (2 * nbL P + 1), ∑ ro : Rows (nbL P) k, ∑ x ∈ fibE P N ro, f ⟨k, (ro, x)⟩ := by
  rw [idxP, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro ro _
  rw [fibE, Finset.sum_filter]

theorem rename_fFS_isHomogeneous (P : List ℕ) (x : ExpL P) :
    (rename (rhoL P) (fFS P x)).IsHomogeneous (degG P x) :=
  (fFS_isHomogeneous P x).rename_isHomogeneous

/-- Homogeneity of the evaluated functional. -/
theorem coeff_eval_eq_zero (P : List ℕ) (x : ExpL P) (ms : Multiset ℕ) (l : ℕ)
    (hms : ∀ j ∈ ms, j ≤ l) (g : Fin (nbL P) → Fin 4) (d : Fin (nbL P) →₀ ℕ)
    (hd : ∑ i, d i + jcount g ≠ degG P x + awt (topExp P x) + ms.sum) :
    coeff d (rename (rhoL P) (fFS P x) * (esymmPow (topExp P x) * Apol ms l g)) = 0 := by
  classical
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.mem_antidiagonal] at hp
  by_contra hne
  have h1 : p.1.degree = degG P x := by
    have := (rename_fFS_isHomogeneous P x) (left_ne_zero_of_mul hne)
    rwa [Finsupp.degree_eq_weight_one]
  have h2 : ∑ i, p.2 i + jcount g = awt (topExp P x) + ms.sum := by
    by_contra h
    exact (right_ne_zero_of_mul hne) (coeff_esymmPow_mul_Apol_eq_zero ms l hms _ g p.2 h)
  apply hd
  have hsum : ∑ i, d i = p.1.degree + ∑ i, p.2 i := by
    rw [← hp, Finsupp.degree_eq_sum]
    simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]
  omega

/-- The evaluated functional at its own colouring, factored. -/
theorem eval_own_eq (P : List ℕ) (x : ExpL P) (ms : Multiset ℕ) (l : ℕ) (g : Fin (nbL P) → Fin 4) :
    rename (rhoL P) (fFS P x) * (esymmPow (topExp P x) * Apol ms l g) =
      ((Finset.univ.filter fun σ : Equiv.Perm (Fin (tsL P)) =>
        ValidA (rhoL P ∘ σ) (grpL P)).card : ℂ) • (VL P * (FamL P x * Apol ms l g)) := by
  rw [rename_rhoL_fFS, esymmPow_topExp, smul_mul_assoc, ← mul_assoc, mul_comm (mainL P x),
    topL_mul_mainL, mul_assoc]

/-- **Independence of the functionals of one profile.** -/
theorem idxP_indep {n : ℕ} {P : List ℕ} (hP : P ≠ [] ∧ P.length ≤ n) {N : ℕ}
    (κ : (Σ k : Fin (2 * nbL P + 1), Rows (nbL P) k × ExpL P) → ℂ)
    (h : ∀ (g : Fin (nbL P) → Fin 4) (a : Fin (nbL P) → ℕ),
      ∑ i, a i + jcount g + nbL P + 2 * tsL P = N →
        ∑ j ∈ idxP P N, κ j * LamG n ⟨P, j⟩ (pushN n (pblkG TPoly X (colL P) g a)) = 0) :
    ∀ j ∈ idxP P N, κ j = 0 := by
  classical
  rintro ⟨k0, ro0, x0⟩ hi
  have hk0 : (k0 : ℕ) ≤ 2 * nbL P := Nat.lt_succ_iff.mp k0.2
  set Nv : ℂ := ((Finset.univ.filter fun σ : Equiv.Perm (Fin (tsL P)) =>
    ValidA (rhoL P ∘ σ) (grpL P)).card : ℂ)
  have hNv : Nv ≠ 0 := Nat.cast_ne_zero.mpr (card_valid_pos P).ne'
  let y : Rows (nbL P) k0 → MvPolynomial (Fin (nbL P)) ℂ := fun ro =>
    ∑ x ∈ fibE P N ro, κ ⟨k0, (ro, x)⟩ • (VL P * FamL P x)
  have hy : ∀ w : Cols (nbL P) k0,
      ∑ ro, y ro * Apol (msOf ro) (2 * nbL P - k0) w.1 = 0 := by
    intro w
    ext d
    rw [coeff_zero, coeff_sum]
    simp only [y, Finset.sum_mul, coeff_sum, smul_mul_assoc, coeff_smul, smul_eq_mul, mul_assoc]
    apply (mul_right_injective₀ hNv)
    simp only [mul_zero, Finset.mul_sum]
    by_cases hW : ∑ i, d i + jcount w.1 + nbL P + 2 * tsL P = N
    · have htot := h w.1 d hW
      rw [sum_idxP, Finset.sum_eq_single k0] at htot
      · rw [← htot]
        apply Finset.sum_congr rfl
        intro ro _
        apply Finset.sum_congr rfl
        intro x _
        rw [LamG_push_own hP, toF_coe, eval_own_eq, coeff_smul, smul_eq_mul]
        ring
      · intro k _ hk
        apply Finset.sum_eq_zero
        intro ro _
        apply Finset.sum_eq_zero
        intro x _
        rw [LamG_push_own hP, Apol_eq_zero _ _ (msOf_le ro) _ (vcount_ne_of_ne k0 k hk w),
          mul_zero, mul_zero, coeff_zero, mul_zero]
      · intro hk; exact absurd (Finset.mem_univ _) hk
    · apply Finset.sum_eq_zero
      intro ro _
      apply Finset.sum_eq_zero
      intro x hx
      have hzero := coeff_eval_eq_zero P x (msOf ro) (2 * nbL P - k0) (msOf_le ro) w.1 d (by
        have hxw := (Finset.mem_filter.mp hx).2
        have := degG_add_degTop P x
        have h1 := tsL_le_sqL P
        rw [awt_topExp]
        omega)
      rw [eval_own_eq, coeff_smul, smul_eq_mul] at hzero
      rw [(mul_eq_zero.mp hzero).resolve_left hNv, mul_zero, mul_zero]
  have hy0 := block_indep (nbL P) k0 hk0 y hy
  have hs0 : VL P * ∑ x ∈ fibE P N ro0, κ ⟨k0, (ro0, x)⟩ • FamL P x = 0 := by
    have := congrFun hy0 ro0
    simp only [y, Pi.zero_apply] at this
    rw [← this, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [mul_smul_comm]
  have hs1 := (mul_eq_zero.mp hs0).resolve_left (VL_ne_zero P)
  have hx0 : x0 ∈ fibE P N ro0 := by
    rw [idxP, Finset.mem_sigma] at hi
    obtain ⟨-, hi⟩ := hi
    rw [Finset.mem_filter, Finset.mem_product] at hi
    exact Finset.mem_filter.mpr ⟨hi.1.2, hi.2⟩
  exact (linearIndependent_iff'.mp (FamL_linearIndependent P)) _
    (fun x => κ ⟨k0, (ro0, x)⟩) hs1 x0 hx0

/-! ### All profiles with `r` letters -/

/-- The profiles of length `k` with entries at most `B`. -/
def profs : ℕ → ℕ → Finset (List ℕ)
  | 0, _ => {[]}
  | k + 1, B => ((Finset.range (B + 1)) ×ˢ profs k B).image fun p => p.1 :: p.2

theorem length_of_mem_profs : ∀ {k B : ℕ} {P : List ℕ}, P ∈ profs k B → P.length = k
  | 0, _, P, h => by simp [profs] at h; simp [h]
  | k + 1, B, P, h => by
    simp only [profs, Finset.mem_image, Finset.mem_product, Finset.mem_range] at h
    obtain ⟨⟨r, P'⟩, ⟨_, hP'⟩, rfl⟩ := h
    simp [length_of_mem_profs hP']

/-- The indices of all profiles of length `n` with `r` letters and weight `N`. -/
def tIdxG (n r N : ℕ) : Finset IdxG :=
  ((profs n N).filter fun P => nbL P + tsL P = r).sigma fun P => idxP P N

/-- **Joint independence of the profile functionals with `r` letters.** -/
theorem tIdxG_indep {n : ℕ} (hn : 1 ≤ n) (r N : ℕ) (κ : IdxG → ℂ)
    (h : ∀ x ∈ modelDeg (Rn n) (tn n) r (N : ℤ), ∑ i ∈ tIdxG n r N, κ i * LamG n i x = 0) :
    ∀ i ∈ tIdxG n r N, κ i = 0 := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨i0, hi0, hκ0⟩ := hne
  set bad := (tIdxG n r N).filter fun i => κ i ≠ 0
  obtain ⟨i1, hi1, hmax⟩ := bad.exists_max_image (fun i => tsL i.1)
    ⟨i0, Finset.mem_filter.mpr ⟨hi0, hκ0⟩⟩
  set bad0 := bad.filter fun i => tsL i.1 = tsL i1.1
  obtain ⟨i2, hi2, hmin⟩ := bad0.exists_min_image (fun i => potL n i.1)
    ⟨i1, Finset.mem_filter.mpr ⟨hi1, rfl⟩⟩
  obtain ⟨P0, j2⟩ := i2
  have hi2' := Finset.mem_filter.mp hi2
  have hi2b := Finset.mem_filter.mp hi2'.1
  have hP0mem := Finset.mem_sigma.mp hi2b.1
  have hP0prof := Finset.mem_filter.mp hP0mem.1
  have hlen0 : P0.length = n := length_of_mem_profs hP0prof.1
  have hP0 : P0 ≠ [] ∧ P0.length ≤ n := ⟨by
    intro h0; rw [h0] at hlen0; simp at hlen0; omega, hlen0.le⟩
  have key := idxP_indep hP0 (N := N) (fun j => κ ⟨P0, j⟩) (fun g a hW => by
    have hx := push_pblkG_mem (n := n) hP0prof.2 g a hW
    have hsum := h _ hx
    rw [tIdxG, Finset.sum_sigma, Finset.sum_eq_single P0] at hsum
    · exact hsum
    · intro P hP hne
      apply Finset.sum_eq_zero
      intro j hj
      have hPprof := Finset.mem_filter.mp hP
      rcases lt_trichotomy (tsL P) (tsL P0) with hlt | heq | hgt
      · rw [LamG_push_lt ⟨P, j⟩ hlt, mul_zero]
      · by_cases hκ : κ ⟨P, j⟩ = 0
        · rw [hκ, zero_mul]
        · have hmem : (⟨P, j⟩ : IdxG) ∈ bad0 := Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr ⟨hP, hj⟩, hκ⟩, heq.trans hi2'.2⟩
          have hpot := hmin _ hmem
          rw [LamG_push_noValid ⟨P, j⟩ heq ?_, mul_zero]
          intro σ hv
          apply hne
          have hlenP : P.length = n := length_of_mem_profs hPprof.1
          have e1 : nbL P + tsL P = r := hPprof.2
          have e2 : nbL P0 + tsL P0 = r := hP0prof.2
          apply eq_of_cntL_le_of_potL P P0 (hlenP.trans hlen0.symm) heq (by omega)
            (cntL_le_of_valid P P0 heq σ hv)
          have hpot' : potL n P0 ≤ potL n P := hpot
          rw [hlenP]; exact hpot'
      · have : κ ⟨P, j⟩ = 0 := by
          by_contra hκ
          have hm : tsL P ≤ tsL i1.1 := hmax ⟨P, j⟩ (Finset.mem_filter.mpr
            ⟨Finset.mem_sigma.mpr ⟨hP, hj⟩, hκ⟩)
          have h12 : tsL P0 = tsL i1.1 := hi2'.2
          omega
        rw [this, zero_mul]
    · intro h'; exact absurd hP0mem.1 h')
  exact hi2b.2 (key j2 hP0mem.2)

/-- **The per-`r` lower bound** `#tIdxG ≤ dim S_{n,r,N}`. -/
theorem card_tIdxG_le_finrank {n : ℕ} (hn : 1 ≤ n) (r N : ℕ) :
    (tIdxG n r N).card ≤ Module.finrank ℂ (modelDeg (Rn n) (tn n) r (N : ℤ)) := by
  classical
  set V := modelDeg (Rn n) (tn n) r (N : ℤ)
  let f : tIdxG n r N → Module.Dual ℂ V := fun i => LamG n i.1 ∘ₗ V.subtype
  have hli : LinearIndependent ℂ f := by
    rw [linearIndependent_iff']
    intro S g hg i hi
    let c : IdxG → ℂ := fun j => if h : j ∈ tIdxG n r N then
      (if (⟨j, h⟩ : tIdxG n r N) ∈ S then g ⟨j, h⟩ else 0) else 0
    have hc : ∀ x ∈ V, ∑ j ∈ tIdxG n r N, c j * LamG n j x = 0 := by
      intro x hx
      have h1 := congrArg (fun φ : Module.Dual ℂ V => φ ⟨x, hx⟩) hg
      simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        LinearMap.zero_apply, f, LinearMap.comp_apply, Submodule.subtype_apply] at h1
      rw [← h1, ← Finset.sum_coe_sort (tIdxG n r N)]
      rw [← Finset.sum_subset (Finset.subset_univ S)]
      · apply Finset.sum_congr rfl
        intro j hj
        simp [c, hj]
      · intro j _ hj
        simp [c, hj]
    have := tIdxG_indep hn r N c hc i.1 i.2
    simpa [c, hi] using this
  have := hli.fintype_card_le_finrank
  rwa [Fintype.card_coe, Subspace.dual_finrank_eq] at this

end

end VOA.TwoSeries.ModelChar
