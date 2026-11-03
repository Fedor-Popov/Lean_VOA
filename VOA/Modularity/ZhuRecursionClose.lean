/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.ZhuCoefficientIdentity

/-!
# Zhu's recursion  (Zhu, J. AMS 9 (1996), Prop. 4.3.2; Gannon 5.3.17)

  `𝒵_M(a[−1]v) = tr_M(o(a)o(v)q^{L₀−c/24}) + Σ_{k≥1} G_{2k} ⋆ 𝒵_M(a[2k−1]v)`

for every `C₂`-independent `OrdVModule`, every homogeneous `a ∈ 𝒱_{kₐ}` with `kₐ ≥ 1`, and **every**
`v` — with the pinned Eisenstein family `zhuG` (`ZhuNormalization`).

## The proof

Only the index `i = −1` of the expansion `a[−1]v = Σ_i c(k,−1,i) a₍ᵢ₎v` is expanded by the iterate
formula (the two-point term lives there, `iterate_twoPoint_cancel`); the higher `a₍ᵢ₎v`, `i ≥ 0`,
are kept as they are.  For `i = −1` the iterate weights are all `1`, so

  `o(a₍₋₁₎v) = Σ_{p ≤ −1} a₍ₚ₎v₍kₐ+ℓ−p−2₎ + Σ_{p ≥ 0} v₍kₐ+ℓ−p−2₎a₍ₚ₎`

is the sum over **all** mode indices `p` of the compensated pair at `p`, standard orientation for
`p ≤ −1`, reversed for `p ≥ 0` (`pairOp`).  The `q`-graded trace of each pair is evaluated by the
trichotomy of `GradedTrace` with the telescope run to a **uniform** depth `D` fixed by the
bounded-below grading (`exists_gradedTraceOp_bound`):

* `p < kₐ − 1`: `−Σ_{j≥1} Cz(p)(e − j·s_p)`, plus `−Cz(p)(e)` if the pair is reversed
  (`0 ≤ p ≤ kₐ−2`), where `Cz(p) = Σ_r C(p,r)𝒵_M(a₍ᵣ₎v)` is the commutator trace;
* `p = kₐ − 1`: the two-point term `tr o(a)o(v)q^{L₀−c/24}` (this is why the telescope must exclude
  the zero mode);
* `p > kₐ − 1`: `+Σ_{j≥1} Cz(p)(e − j·|s_p|)`.

Everything is then an identity between the coefficient families of `Z_r = 𝒵_M(a₍ᵣ₎v)`, and that
identity is `zhu_abstract_assembly` (`ZhuCoefficientIdentity`), whose two inputs are the scalar
identities (I2)/(I3) of `ExpLogBinomial` — the `p`-sum regroups over `(|s_p|, j) ↦ |s_p|·j = n`
into the divisor sums `σ_{2m+1}(n)` of `zhuG`, and the constant term matches through
`u = B(log(1+w))`, up to `½𝒵_M(a[0]v) = 0` (`zhuVanishing_holds`).

## Status
**`zhuRecursionPinned_holds`** — axiom-clean, `pbw`-free, for `a ∈ 𝒱_{kₐ}`, `kₐ ≥ 1`
and every `v` (`zhuRecursionPinned_of_homogeneous` for homogeneous `v`, then linearity).
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## The uniform degree bound -/

/-- **Uniform vanishing**: below some depth every graded trace at degree `e − n` vanishes,
uniformly in the operator (straight from `boundedBelow`). -/
theorem exists_gradedTraceOp_bound (N : OrdVModule W M) (e : ℂ) :
    ∃ D : ℕ, ∀ (A : Module.End ℂ M) (n : ℕ), D < n → gradedTraceOp N A (e - n) = 0 := by
  obtain ⟨B, hB⟩ := N.boundedBelow
  obtain ⟨D, hD⟩ := exists_nat_gt (e.re + (W.centralCharge / 24).re - B)
  refine ⟨D, fun A n hn => gradedTraceOp_eq_zero_of_weight_bot N A _ ?_⟩
  by_contra hne
  have h := hB _ hne
  simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re] at h
  have : (D : ℝ) < n := by exact_mod_cast hn
  linarith

/-- A product whose right factor annihilates the weight space has vanishing graded trace. -/
theorem gradedTraceOp_mul_eq_zero_of_kills (N : OrdVModule W M) (A B : Module.End ℂ M) (e : ℂ)
    (hB : ∀ x ∈ N.weight (e + W.centralCharge / 24), B x = 0) :
    gradedTraceOp N (A * B) e = 0 := by
  haveI := N.finrank (e + W.centralCharge / 24)
  have hblk : weightBlock N (A * B) (e + W.centralCharge / 24) = 0 := by
    refine LinearMap.ext (fun y => Subtype.ext ?_)
    change ((internalProjTo N.isInternal _) (A (B (y : M))) : M) = _
    rw [hB (y : M) y.2, map_zero, map_zero]
    simp
  change LinearMap.trace ℂ _ (weightBlock N (A * B) (e + W.centralCharge / 24)) = 0
  rw [hblk, map_zero]

/-! ## The compensated pair at mode index `p` -/

/-- **The compensated pair at `p`**: standard orientation `a₍ₚ₎v₍kₐ+ℓ−p−2₎` for `p ≤ −1`, reversed
`v₍kₐ+ℓ−p−2₎a₍ₚ₎` for `p ≥ 0` — exactly the two families of the `i = −1` iterate. -/
noncomputable def pairOp (N : OrdVModule W M) (a v : 𝒱) (ka l p : ℤ) : Module.End ℂ M :=
  if p ≤ -1 then mode (N.YM a) p * mode (N.YM v) (ka + l - p - 2)
  else mode (N.YM v) (ka + l - p - 2) * mode (N.YM a) p

section PairFinsum

variable (N : OrdVModule W M) {ka l : ℤ} {a v : 𝒱}

/-- Pointwise: `o(a₍₋₁₎v)x = Σᶠ_p pairOp p x`. -/
theorem oMod_smul_neg_one_eq_finsum_pairOp (ha : a ∈ W.grading ka) (hv : v ∈ W.grading l)
    (x : M) : oMod N (W.smul a (-1) v) x = ∑ᶠ p : ℤ, pairOp N a v ka l p x := by
  rw [oMod_smul_eq_iterate N ha hv (-1) x]
  -- the iterate weights at `i = −1` are the indicator of `j ≥ 0`
  have hw : ∀ j : ℤ, (negOnePow j * cbz (-1) j) •
      (mode (N.YM a) (-1 - j) (mode (N.YM v) (ka + l - (-1 - j) - 2) x)
        - negOnePow (-1) • mode (N.YM v) (ka + l - j - 2) (mode (N.YM a) j x))
      = if 0 ≤ j then (mode (N.YM a) (-1 - j) (mode (N.YM v) (ka + l - (-1 - j) - 2) x)
          + mode (N.YM v) (ka + l - j - 2) (mode (N.YM a) j x)) else 0 := by
    intro j
    by_cases hj : 0 ≤ j
    · rw [if_pos hj, iterate_weight_neg_one hj, one_smul, negOnePow_neg_one, neg_one_smul,
        sub_neg_eq_add]
    · push_neg at hj
      rw [if_neg (not_le.mpr hj), cbz_apply_neg _ hj, mul_zero, zero_smul]
  simp_rw [hw]
  -- finiteness of the two families (pointwise truncation)
  obtain ⟨Nv, hNv⟩ := N.truncation v x
  obtain ⟨Na, hNa⟩ := N.truncation a x
  have hfinA : (Function.support fun j : ℕ =>
      mode (N.YM a) (-1 - j) (mode (N.YM v) (ka + l - (-1 - j) - 2) x)).Finite := by
    refine Set.Finite.subset (Set.finite_Iio (Nv - ka - l + 1).toNat) (fun j hj => ?_)
    simp only [Function.mem_support, ne_eq] at hj
    simp only [Set.mem_Iio]
    by_contra hc; push_neg at hc
    exact hj (by rw [hNv _ (by omega), map_zero])
  have hfinB : (Function.support fun j : ℕ =>
      mode (N.YM v) (ka + l - j - 2) (mode (N.YM a) j x)).Finite := by
    refine Set.Finite.subset (Set.finite_Iio Na.toNat) (fun j hj => ?_)
    simp only [Function.mem_support, ne_eq] at hj
    simp only [Set.mem_Iio]
    by_contra hc; push_neg at hc
    exact hj (by rw [hNa _ (by omega), map_zero])
  -- the `ℤ`-sum of the indicator form is the `ℕ`-sum
  have hL : (∑ᶠ j : ℤ, if 0 ≤ j then (mode (N.YM a) (-1 - j) (mode (N.YM v) (ka + l - (-1 - j) - 2) x)
      + mode (N.YM v) (ka + l - j - 2) (mode (N.YM a) j x)) else 0)
      = ∑ᶠ j : ℕ, (mode (N.YM a) (-1 - j) (mode (N.YM v) (ka + l - (-1 - j) - 2) x)
          + mode (N.YM v) (ka + l - j - 2) (mode (N.YM a) j x)) := by
    rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ Set.univ (Set.range (Nat.cast : ℕ → ℤ))
      (fun j hj => ?_), finsum_mem_range Nat.cast_injective]
    · refine finsum_congr (fun j => ?_)
      rw [if_pos (by positivity)]
    · simp only [Set.mem_univ, Set.mem_range, true_iff]
      rw [Function.mem_support] at hj
      by_cases h0 : 0 ≤ j
      · exact ⟨j.toNat, by omega⟩
      · exact absurd (if_neg h0) hj
  rw [hL, finsum_add_distrib hfinA hfinB]
  -- the `p`-sum splits into `p ≥ 0` (reversed pairs) and `p = −1−j` (standard pairs)
  have hfinP : (Function.support fun p : ℤ => pairOp N a v ka l p x).Finite := by
    refine Set.Finite.subset (Set.finite_Icc (-(Nv - ka - l + 1).toNat - 1 : ℤ) Na.toNat)
      (fun p hp => ?_)
    simp only [Function.mem_support, ne_eq] at hp
    simp only [Set.mem_Icc]
    by_contra hc
    refine hp ?_
    rw [pairOp]
    by_cases hp1 : p ≤ -1
    · rw [if_pos hp1]
      change mode (N.YM a) p (mode (N.YM v) (ka + l - p - 2) x) = 0
      rw [hNv _ (by omega), map_zero]
    · rw [if_neg hp1]
      change mode (N.YM v) (ka + l - p - 2) (mode (N.YM a) p x) = 0
      rw [hNa _ (by omega), map_zero]
  have hsplit := finsum_int_split_two (fun p => pairOp N a v ka l p x) hfinP (fun j : ℕ => (j : ℤ))
    (fun j : ℕ => -1 - j) Nat.cast_injective (fun a b h => by simpa using h) ?_ ?_
  · rw [hsplit, add_comm]
    congr 1
    · refine finsum_congr (fun j => ?_)
      show _ = pairOp N a v ka l (j : ℤ) x
      rw [pairOp, if_neg (by omega)]
      rfl
    · refine finsum_congr (fun j => ?_)
      show _ = pairOp N a v ka l (-1 - (j : ℤ)) x
      rw [pairOp, if_pos (by omega)]
      rfl
  · rw [Set.disjoint_left]
    rintro p ⟨a, rfl⟩ ⟨b, hb⟩
    simp only at hb
    omega
  · refine Set.eq_univ_of_forall (fun p => ?_)
    by_cases hp : 0 ≤ p
    · exact Or.inl ⟨p.toNat, by simp; omega⟩
    · exact Or.inr ⟨(-1 - p).toNat, by simp; omega⟩

/-- **The `i = −1` iterate at a fixed degree, as a sum over all mode indices**:
`𝒵_M(a₍₋₁₎v)(e) = Σᶠ_p 𝒯(pairOp p)(e)`.  Uniform truncation on the (finite-dimensional) weight
space makes the operator sum finite on `M_α`, and outside that window each pair annihilates `M_α`,
so its trace vanishes. -/
theorem onePoint_smul_neg_one_eq_finsum_pairOp (ha : a ∈ W.grading ka) (hv : v ∈ W.grading l)
    (e : ℂ) :
    onePoint N (W.smul a (-1) v) e = ∑ᶠ p : ℤ, gradedTraceOp N (pairOp N a v ka l p) e := by
  set α : ℂ := e + W.centralCharge / 24 with hα
  obtain ⟨Nv, hNv⟩ := mode_eventually_zero_on_weight N v α
  obtain ⟨Na, hNa⟩ := mode_eventually_zero_on_weight N a α
  set lo : ℤ := min (-1) (ka + l - 2 - Nv) with hlo
  set hi : ℤ := max 0 Na with hhi
  -- pairs outside `[lo, hi]` kill `M_α`
  have hkill : ∀ p : ℤ, ¬(lo ≤ p ∧ p ≤ hi) → ∀ x ∈ N.weight α, pairOp N a v ka l p x = 0 := by
    intro p hp x hx
    rw [pairOp]
    by_cases hp1 : p ≤ -1
    · rw [if_pos hp1]
      change mode (N.YM a) p (mode (N.YM v) (ka + l - p - 2) x) = 0
      rw [hNv _ (by omega) x hx, map_zero]
    · rw [if_neg hp1]
      change mode (N.YM v) (ka + l - p - 2) (mode (N.YM a) p x) = 0
      rw [hNa _ (by omega) x hx, map_zero]
  -- on `M_α` the operator is the finite sum over `Icc lo hi`
  set Op : Module.End ℂ M := ∑ p ∈ Finset.Icc lo hi, pairOp N a v ka l p with hOp
  have hagree : ∀ x ∈ N.weight α, oMod N (W.smul a (-1) v) x = Op x := by
    intro x hx
    rw [oMod_smul_neg_one_eq_finsum_pairOp N ha hv x, hOp, LinearMap.sum_apply]
    refine finsum_eq_sum_of_support_subset _ (fun p hp => ?_)
    simp only [Function.mem_support, ne_eq] at hp
    simp only [Finset.coe_Icc, Set.mem_Icc]
    by_contra hc
    exact hp (hkill p hc x hx)
  have hblk : weightBlock N (oMod N (W.smul a (-1) v)) α = weightBlock N Op α := by
    refine LinearMap.ext (fun y => Subtype.ext ?_)
    change ((internalProjTo N.isInternal _) (oMod N (W.smul a (-1) v) (y : M)) : M)
      = ((internalProjTo N.isInternal _) (Op (y : M)) : M)
    rw [hagree (y : M) y.2]
  have hlhs : onePoint N (W.smul a (-1) v) e = gradedTraceOp N Op e := by
    haveI := N.finrank α
    change LinearMap.trace ℂ _ (weightBlock N (oMod N (W.smul a (-1) v)) α) = _
    rw [hblk]
    rfl
  rw [hlhs, hOp, ← gradedTraceAt_apply, map_sum]
  simp only [gradedTraceAt_apply]
  symm
  refine finsum_eq_sum_of_support_subset _ (fun p hp => ?_)
  simp only [Function.mem_support, ne_eq] at hp
  simp only [Finset.coe_Icc, Set.mem_Icc]
  by_contra hc
  refine hp ?_
  rw [pairOp]
  by_cases hp1 : p ≤ -1
  · rw [if_pos hp1]
    exact gradedTraceOp_mul_eq_zero_of_kills N _ _ e (fun x hx => hNv _ (by omega) x hx)
  · rw [if_neg hp1]
    exact gradedTraceOp_mul_eq_zero_of_kills N _ _ e (fun x hx => hNa _ (by omega) x hx)

end PairFinsum

/-! ## The telescopes with explicit depth -/

section Telescopes

variable (N : OrdVModule W M) {ka l : ℤ} {a v : 𝒱}

/-- The mirror telescope with an explicit depth `n` and its vanishing hypothesis. -/
theorem gradedTraceOp_mode_pair_geomSolve_up (ha : a ∈ W.grading ka) (hv : v ∈ W.grading l)
    (i : ℤ) (e : ℂ) (n : ℕ)
    (hvanish : gradedTraceOp N (mode (N.YM a) i * mode (N.YM v) (ka + l - i - 2))
      (e + (n : ℂ) * ((ka : ℂ) - (i : ℂ) - 1)) = 0) :
    gradedTraceOp N (mode (N.YM a) i * mode (N.YM v) (ka + l - i - 2)) e
      = ∑ j ∈ Finset.range n, ∑ᶠ p : ℤ,
          cbz i p * onePoint N (W.smul a p v) (e + (j : ℂ) * ((ka : ℂ) - (i : ℂ) - 1)) := by
  set s : ℂ := (ka : ℂ) - (i : ℂ) - 1 with hs
  have hB : WeightShift N (mode (N.YM a) i) s := weightShift_mode N ha i
  have hA : WeightShift N (mode (N.YM v) (ka + l - i - 2)) (-s) := by
    have h := weightShift_mode N hv (ka + l - i - 2)
    rwa [show ((l : ℂ) - ((ka + l - i - 2 : ℤ) : ℂ) - 1) = -s from by rw [hs]; push_cast; ring] at h
  rw [gradedTrace_geomSolve_up _ _ s (gradedTraceOp_commutator_step N _ _ s hA hB) e n hvanish,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show (mode (N.YM v) (ka + l - i - 2) * mode (N.YM a) i
      - mode (N.YM a) i * mode (N.YM v) (ka + l - i - 2))
    = -(mode (N.YM a) i * mode (N.YM v) (ka + l - i - 2)
      - mode (N.YM v) (ka + l - i - 2) * mode (N.YM a) i) from (neg_sub _ _).symm,
    ← neg_one_smul ℂ (mode (N.YM a) i * mode (N.YM v) (ka + l - i - 2)
      - mode (N.YM v) (ka + l - i - 2) * mode (N.YM a) i),
    gradedTraceOp_smul, Pi.smul_apply, smul_eq_mul,
    gradedTraceOp_compensating_commutator N ha hv i]
  ring

end Telescopes

/-! ## Casting the mode distance -/

theorem modeDist_cast_of_le {ka : ℕ} {p : ℤ} (hp : p ≤ (ka : ℤ) - 1) :
    ((modeDist ka p : ℕ) : ℂ) = (ka : ℂ) - (p : ℂ) - 1 := by
  rw [modeDist, ← Int.cast_natCast, Int.natCast_natAbs, abs_of_nonpos (by omega)]
  push_cast
  ring

theorem modeDist_cast_of_ge {ka : ℕ} {p : ℤ} (hp : (ka : ℤ) - 1 ≤ p) :
    ((modeDist ka p : ℕ) : ℂ) = (p : ℂ) - (ka : ℂ) + 1 := by
  rw [modeDist, ← Int.cast_natCast, Int.natCast_natAbs, abs_of_nonneg (by omega)]
  push_cast
  ring

theorem modeDist_pos_of_ne {ka : ℕ} {p : ℤ} (hp : p ≠ (ka : ℤ) - 1) : 1 ≤ modeDist ka p := by
  rw [modeDist]
  omega

/-! ## The trace of each pair, by regime -/

section Casework

variable (N : OrdVModule W M) {ka : ℕ} {l : ℤ} {a v : 𝒱}

/-- **The graded trace of `pairOp p`, in every regime**, at uniform telescope depth `D`:

  `𝒯(pairOp p)(e) = [p = kₐ−1]·tr o(a)o(v)q^{L₀−c/24}(e) − [0 ≤ p ≤ kₐ−2]·Cz(p)(e)
                     + sgn(p−kₐ+1)·Σ_{j≤D} Cz(p)(e − (j+1)|s_p|)`. -/
theorem gradedTraceOp_pairOp_eq (hk : 1 ≤ ka) (ha : a ∈ W.grading (ka : ℤ)) (hv : v ∈ W.grading l)
    (e : ℂ) (D : ℕ) (hD : ∀ (A : Module.End ℂ M) (n : ℕ), D < n → gradedTraceOp N A (e - n) = 0)
    (p : ℤ) :
    gradedTraceOp N (pairOp N a v ka l p) e
      = (if p = (ka : ℤ) - 1 then torusTwoPoint N a v e else 0)
        + (if 0 ≤ p ∧ p ≤ (ka : ℤ) - 2
            then -(commTraceZ (fun r e' => onePoint N (W.smul a r v) e') p e) else 0)
        + modeSgn ka p * telescopeZ (fun r e' => onePoint N (W.smul a r v) e') ka D e p := by
  set Z : ℤ → ℂ → ℂ := fun r e' => onePoint N (W.smul a r v) e' with hZ
  -- the commutator trace at a shifted degree, in the `commTraceZ` shape
  have hCz : ∀ e' : ℂ, (∑ᶠ r : ℤ, cbz p r * onePoint N (W.smul a r v) e') = commTraceZ Z p e' :=
    fun e' => rfl
  have hD' : ∀ (A : Module.End ℂ M) (n : ℕ), D < n → gradedTraceOp N A (e - n) = 0 := hD
  rcases lt_trichotomy p ((ka : ℤ) - 1) with hlt | heq | hgt
  · -- `p < kₐ − 1`: shift `s = kₐ − p − 1 ≥ 1`, telescope down
    have hdist : ((modeDist ka p : ℕ) : ℂ) = (ka : ℂ) - (p : ℂ) - 1 := modeDist_cast_of_le hlt.le
    have hdpos : 1 ≤ modeDist ka p := modeDist_pos_of_ne hlt.ne
    have hne : p ≠ (ka : ℤ) - 1 := hlt.ne
    rw [if_neg hne, zero_add, modeSgn, if_neg (not_lt.mpr hlt.le), if_pos hlt, neg_one_mul]
    -- the standard-orientation pair trace, telescoped to depth `n`
    have hstd : ∀ n : ℕ, D < n * modeDist ka p →
        gradedTraceOp N (mode (N.YM a) p * mode (N.YM v) (ka + l - p - 2)) e
          = -∑ j ∈ Finset.range n, commTraceZ Z p (e - ((j : ℂ) + 1) * (modeDist ka p : ℂ)) := by
      intro n hn
      rw [gradedTraceOp_mode_pair_geomSolve N ha hv p e n]
      · simp only [Int.cast_natCast, hCz, hdist]
      · simp only [Int.cast_natCast]
        rw [show e - (n : ℂ) * ((ka : ℂ) - (p : ℂ) - 1) = e - ((n * modeDist ka p : ℕ) : ℂ) from by
          rw [Nat.cast_mul, hdist]]
        exact hD' _ _ hn
    by_cases hp0 : 0 ≤ p
    · -- reversed pair: `𝒯(v·a₍ₚ₎)(e) = 𝒯(a₍ₚ₎·v)(e + s)`, telescope to depth `D + 2`
      rw [if_pos ⟨hp0, by omega⟩, pairOp, if_neg (by omega),
        gradedTraceOp_reversed_pair N ha hv p e]
      simp only [Int.cast_natCast]
      have hstd' : ∀ n : ℕ, D < n * modeDist ka p →
          gradedTraceOp N (mode (N.YM a) p * mode (N.YM v) (ka + l - p - 2))
              (e + ((ka : ℂ) - (p : ℂ) - 1))
            = -∑ j ∈ Finset.range (n + 1),
                commTraceZ Z p (e - ((j : ℂ)) * (modeDist ka p : ℂ)) := by
        intro n hn
        rw [gradedTraceOp_mode_pair_geomSolve N ha hv p _ (n + 1)]
        · simp only [Int.cast_natCast, hCz, hdist]
          congr 1
          refine Finset.sum_congr rfl (fun j _ => ?_)
          congr 1
          ring
        · simp only [Int.cast_natCast]
          rw [show e + ((ka : ℂ) - (p : ℂ) - 1) - ((n + 1 : ℕ) : ℂ) * ((ka : ℂ) - (p : ℂ) - 1)
              = e - ((n * modeDist ka p : ℕ) : ℂ) from by
            rw [Nat.cast_mul, hdist]; push_cast; ring]
          exact hD' _ _ hn
      rw [hstd' (D + 1) (by nlinarith), Finset.sum_range_succ', telescopeZ, hZ]
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, sub_zero]
      rw [neg_add, add_comm]
    · -- standard pair (`p ≤ −1`), telescope to depth `D + 1`
      push_neg at hp0
      rw [if_neg (fun h => absurd h.1 (not_le.mpr hp0)), zero_add, pairOp, if_pos (by omega),
        hstd (D + 1) (by nlinarith), telescopeZ]
  · -- `p = kₐ − 1`: the zero-mode pair, i.e. the two-point term
    subst heq
    rw [if_pos rfl, if_neg (fun h => by omega), add_zero, modeSgn_self, zero_mul, add_zero, pairOp,
      if_neg (by omega), gradedTraceOp_reversed_pair N ha hv _ e,
      gradedTraceOp_mode_pair_eq_torusTwoPoint N ha hv]
    all_goals (congr 1; push_cast; ring)
  · -- `p > kₐ − 1`: reversed pair, telescope up to depth `D + 1`
    have hdist : ((modeDist ka p : ℕ) : ℂ) = (p : ℂ) - (ka : ℂ) + 1 := modeDist_cast_of_ge hgt.le
    have hdpos : 1 ≤ modeDist ka p := modeDist_pos_of_ne hgt.ne'
    rw [if_neg hgt.ne', zero_add, if_neg (fun h => by omega), zero_add, modeSgn, if_pos hgt,
      one_mul, pairOp, if_neg (by omega), gradedTraceOp_reversed_pair N ha hv p e,
      gradedTraceOp_mode_pair_geomSolve_up N ha hv p _ (D + 1)]
    · rw [telescopeZ, hZ]
      simp only [Int.cast_natCast]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hdist]
      congr 1
      ring
    · simp only [Int.cast_natCast]
      rw [show e + ((ka : ℂ) - (p : ℂ) - 1) + ((D + 1 : ℕ) : ℂ) * ((ka : ℂ) - (p : ℂ) - 1)
          = e - (((D + 2) * modeDist ka p : ℕ) : ℂ) from by
        rw [Nat.cast_mul, hdist]; push_cast; ring]
      exact hD' _ _ (by nlinarith)

end Casework

/-! ## Zhu's recursion, closed -/

section Main

variable (N : OrdVModule W M)

/-- **Zhu's recursion for homogeneous `a ∈ 𝒱_{kₐ}` (`kₐ ≥ 1`) and homogeneous `v`**, with the
pinned Eisenstein family `zhuG`:

  `𝒵_M(a[−1]v) = tr_M(o(a)o(v)q^{L₀−c/24}) + Σ_{m≥0} G_{2m+2} ⋆ 𝒵_M(a[2m+1]v)`. -/
theorem zhuRecursionPinned_of_homogeneous {ka : ℕ} (hk : 1 ≤ ka) {l : ℤ} {a v : 𝒱}
    (ha : a ∈ W.grading (ka : ℤ)) (hv : v ∈ W.grading l) : ZhuRecursionPinned N a v ka := by
  rw [ZhuRecursionPinned, ZhuRecursionAt]
  funext e
  set Z : ℤ → ℂ → ℂ := fun r e' => onePoint N (W.smul a r v) e' with hZ
  obtain ⟨D, hD⟩ := exists_gradedTraceOp_bound N e
  obtain ⟨R, hR⟩ := W.regularity a v
  -- (1) the left-hand side: `Z_{−1}(e) + Σ_{r≥0} c(k,−1,r) Z_r(e)`
  have hL1 : torusOnePoint N (vSqZ W a ka (-1) v) e
      = onePoint N (W.smul a (-1) v) e
        + ∑ᶠ r : ℤ, (if 0 ≤ r then sqBracketCoeffZ ka (-1) r * Z r e else 0) := by
    rw [torusOnePoint_vSqZ_expand]
    have hsplit : ∀ i : ℤ, sqBracketCoeffZ ka (-1) i * torusOnePoint N (mode (W.Y a) i v) e
        = (if i = -1 then onePoint N (W.smul a (-1) v) e else 0)
          + (if 0 ≤ i then sqBracketCoeffZ ka (-1) i * Z i e else 0) := by
      intro i
      rcases lt_trichotomy i (-1) with h | h | h
      · rw [if_neg h.ne, if_neg (by omega), sqBracketCoeffZ_of_lt ka h, zero_mul, add_zero]
      · subst h
        rw [if_pos rfl, if_neg (by norm_num), add_zero, sqBracketCoeffZ_neg_one_diag, one_mul]
        rfl
      · rw [if_neg h.ne', if_pos (by omega), zero_add]
        rfl
    rw [finsum_congr hsplit, finsum_add_distrib, finsum_eq_single _ (-1 : ℤ) (fun i hi => if_neg hi),
      if_pos rfl]
    · refine Set.Finite.subset (Set.finite_singleton (-1 : ℤ)) (fun i hi => ?_)
      simp only [Function.mem_support, ne_eq] at hi
      simp only [Set.mem_singleton_iff]
      by_contra hc
      exact hi (if_neg hc)
    · refine Set.Finite.subset (Set.finite_Ico (0 : ℤ) R) (fun i hi => ?_)
      simp only [Function.mem_support, ne_eq] at hi
      simp only [Set.mem_Ico]
      refine ⟨?_, ?_⟩
      · by_contra hc; exact hi (if_neg hc)
      · by_contra hc; push_neg at hc
        refine hi ?_
        rw [hZ]
        simp only
        rw [show W.smul a i v = 0 from hR i hc, ← onePointAt_apply, map_zero, mul_zero, ite_self]
  -- (2) `Z_{−1}(e)` as the two-point term plus the abstract `p`-sum
  have hL2 : onePoint N (W.smul a (-1) v) e
      = torusTwoPoint N a v e
        + ∑ᶠ p : ℤ, ((if 0 ≤ p ∧ p ≤ (ka : ℤ) - 2 then -(commTraceZ Z p e) else 0)
            + modeSgn ka p * telescopeZ Z ka D e p) := by
    rw [onePoint_smul_neg_one_eq_finsum_pairOp N ha hv e,
      finsum_congr (fun p => gradedTraceOp_pairOp_eq N hk ha hv e D hD p)]
    have hsupp1 : (Function.support fun p : ℤ =>
        (if p = (ka : ℤ) - 1 then torusTwoPoint N a v e else 0)).Finite := by
      refine Set.Finite.subset (Set.finite_singleton ((ka : ℤ) - 1)) (fun p hp => ?_)
      simp only [Function.mem_support, ne_eq] at hp
      simp only [Set.mem_singleton_iff]
      by_contra hc
      exact hp (if_neg hc)
    have hsupp2 : (Function.support fun p : ℤ =>
        ((if 0 ≤ p ∧ p ≤ (ka : ℤ) - 2 then -(commTraceZ Z p e) else 0)
          + modeSgn ka p * telescopeZ Z ka D e p)).Finite := by
      refine Set.Finite.subset (Set.finite_Icc (-(D : ℤ) - ka) ((ka : ℤ) + D)) (fun p hp => ?_)
      simp only [Function.mem_support, ne_eq] at hp
      simp only [Set.mem_Icc]
      by_contra hc
      have hdist : D < modeDist ka p := by rw [modeDist]; omega
      have hDZ : ∀ r, ∀ n : ℕ, D < n → Z r (e - n) = 0 := fun r n hn => hD _ n hn
      refine hp ?_
      rw [telescopeZ_eq_zero_of_lt hDZ p hdist, mul_zero, add_zero, if_neg (fun h => by omega)]
    simp_rw [add_assoc]
    rw [finsum_add_distrib hsupp1 hsupp2,
      finsum_eq_single _ ((ka : ℤ) - 1) (fun p hp => if_neg hp), if_pos rfl]
  -- (3) hypotheses of the abstract assembly
  have hRZ : ∀ r, R ≤ r → ∀ e', Z r e' = 0 := by
    intro r hr e'
    rw [hZ]
    simp only
    rw [show W.smul a r v = 0 from hR r hr, ← onePointAt_apply, map_zero]
  have hDZ : ∀ r, ∀ n : ℕ, D < n → Z r (e - n) = 0 := fun r n hn => hD _ n hn
  have hvan : ∑ᶠ r : ℤ, sqBracketCoeffZ ka 0 r * Z r e = 0 := by
    have h := zhuVanishing_holds N hk ha hv
    rw [ZhuVanishingAt] at h
    have h' := congrFun h e
    rw [torusOnePoint_vSqZ_expand, Pi.zero_apply] at h'
    exact h'
  -- (4) assemble
  rw [hL1, hL2, add_assoc, zhu_abstract_assembly hk e R D hRZ hDZ hvan, Pi.add_apply,
    finsum_apply (zhuRecursion_support_finite N zhuG a v ka)]
  congr 1
  refine finsum_congr (fun m => ?_)
  rw [qConv]
  refine finsum_congr (fun n => ?_)
  rw [torusOnePoint_vSqZ_expand]
  rfl

/-! ## Linearity in `v`, and the vacuum `a = 𝟙` -/

/-- The two-point term is additive in `v`. -/
theorem torusTwoPoint_add_right (a v w : 𝒱) :
    torusTwoPoint N a (v + w) = torusTwoPoint N a v + torusTwoPoint N a w := by
  rw [torusTwoPoint_eq_gradedTraceOp, torusTwoPoint_eq_gradedTraceOp, torusTwoPoint_eq_gradedTraceOp,
    map_add, mul_add, gradedTraceOp_add]

theorem torusTwoPoint_zero_right (a : 𝒱) : torusTwoPoint N a 0 = 0 := by
  rw [torusTwoPoint_eq_gradedTraceOp, map_zero, mul_zero]
  funext e
  haveI := N.finrank (e + W.centralCharge / 24)
  change LinearMap.trace ℂ _ (weightBlock N 0 (e + W.centralCharge / 24)) = 0
  rw [show weightBlock N (0 : Module.End ℂ M) (e + W.centralCharge / 24) = 0 from by
    simp only [weightBlock, LinearMap.zero_comp, LinearMap.comp_zero], map_zero]

/-- A one-point function times an `ℕ`-indexed family has finite support in the shifted degree. -/
theorem support_mul_torusOnePoint_shift_finite (u : 𝒱) (e : ℂ) (f : ℕ → ℂ) :
    (Function.support fun n : ℕ => f n * torusOnePoint N u (e - n)).Finite := by
  obtain ⟨D, hD⟩ := exists_gradedTraceOp_bound N e
  refine Set.Finite.subset (Set.finite_Iic D) (fun n hn => ?_)
  simp only [Function.mem_support, ne_eq] at hn
  simp only [Set.mem_Iic]
  by_contra hc; push_neg at hc
  exact hn (by rw [show torusOnePoint N u (e - n) = gradedTraceOp N (oMod N u) (e - n) from rfl,
    hD _ n hc, mul_zero])

/-- `qConv` is additive at each degree, given the finiteness the module supplies. -/
theorem qConv_add_apply (f : ℕ → ℂ) (g₁ g₂ : FormalQSeries) (e : ℂ)
    (h₁ : (Function.support fun n : ℕ => f n * g₁ (e - n)).Finite)
    (h₂ : (Function.support fun n : ℕ => f n * g₂ (e - n)).Finite) :
    qConv f (g₁ + g₂) e = qConv f g₁ e + qConv f g₂ e := by
  simp only [qConv, Pi.add_apply, mul_add]
  exact finsum_add_distrib h₁ h₂

/-- `ZhuRecursionAt` is closed under addition in `v`. -/
theorem zhuRecursionAt_add (G : ℕ → (ℕ → ℂ)) (a v w : 𝒱) (ka : ℕ)
    (hv : ZhuRecursionAt N G a v ka) (hw : ZhuRecursionAt N G a w ka) :
    ZhuRecursionAt N G a (v + w) ka := by
  rw [ZhuRecursionAt] at hv hw ⊢
  funext e
  have hv' := congrFun hv e
  have hw' := congrFun hw e
  rw [Pi.add_apply, finsum_apply (zhuRecursion_support_finite N G a v ka)] at hv'
  rw [Pi.add_apply, finsum_apply (zhuRecursion_support_finite N G a w ka)] at hw'
  rw [map_add, torusOnePoint_add, Pi.add_apply, hv', hw', Pi.add_apply,
    finsum_apply (zhuRecursion_support_finite N G a (v + w) ka), torusTwoPoint_add_right,
    Pi.add_apply]
  have hterm : ∀ k : ℕ, qConv (G (k + 1)) (torusOnePoint N (vSqZ W a ka (2 * (k + 1) - 1 : ℤ) (v + w))) e
      = qConv (G (k + 1)) (torusOnePoint N (vSqZ W a ka (2 * (k + 1) - 1 : ℤ) v)) e
        + qConv (G (k + 1)) (torusOnePoint N (vSqZ W a ka (2 * (k + 1) - 1 : ℤ) w)) e := by
    intro k
    rw [map_add, torusOnePoint_add,
      qConv_add_apply _ _ _ e (support_mul_torusOnePoint_shift_finite N _ e _)
        (support_mul_torusOnePoint_shift_finite N _ e _)]
  rw [finsum_congr hterm, finsum_add_distrib]
  · ring
  · exact ((zhuRecursion_support_finite N G a v ka).subset (fun k hk => by
      simp only [Function.mem_support, ne_eq] at hk ⊢
      intro h; exact hk (by rw [h]; rfl)))
  · exact ((zhuRecursion_support_finite N G a w ka).subset (fun k hk => by
      simp only [Function.mem_support, ne_eq] at hk ⊢
      intro h; exact hk (by rw [h]; rfl)))

/-- `ZhuRecursionAt` holds trivially at `v = 0`. -/
theorem zhuRecursionAt_zero (G : ℕ → (ℕ → ℂ)) (a : 𝒱) (ka : ℕ) :
    ZhuRecursionAt N G a 0 ka := by
  rw [ZhuRecursionAt, map_zero, torusOnePoint_zero, torusTwoPoint_zero_right, zero_add]
  symm
  refine finsum_eq_zero_of_forall_eq_zero (fun k => ?_)
  rw [map_zero, torusOnePoint_zero, qConv_zero_right]

/-- **Zhu's recursion (Prop. 4.3.2), for homogeneous `a ∈ 𝒱_{kₐ}` (`kₐ ≥ 1`) and EVERY `v`**:

  `𝒵_M(a[−1]v) = tr_M(o(a)o(v)q^{L₀−c/24}) + Σ_{k≥1} G_{2k} ⋆ 𝒵_M(a[2k−1]v)`,

with the pinned normalisation `G_{2k} = −B_{2k}/(2k)! + (2/(2k−1)!)Σσ_{2k−1}(n)qⁿ` (`zhuG`). -/
theorem zhuRecursionPinned_holds {ka : ℕ} (hk : 1 ≤ ka) {a : 𝒱} (ha : a ∈ W.grading (ka : ℤ))
    (v : 𝒱) : ZhuRecursionPinned N a v ka := by
  have hv : v ∈ ⨆ l : ℤ, W.grading l := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  exact Submodule.iSup_induction (motive := fun v => ZhuRecursionPinned N a v ka) W.grading hv
    (fun l u hu => zhuRecursionPinned_of_homogeneous N hk ha hu)
    (zhuRecursionAt_zero N zhuG a ka)
    (fun u w hu hw => zhuRecursionAt_add N zhuG a u w ka hu hw)

/-- The vacuum on the left: `ZhuRecursionAt N G 𝟙 v 0` holds for every `G` and `v` —
`𝟙[−1] = id`, `𝟙[m] = 0` for `m ≠ −1`, `o(𝟙) = id`. -/
theorem zhuRecursionAt_vacuum_left (G : ℕ → (ℕ → ℂ)) (v : 𝒱) :
    ZhuRecursionAt N G W.vacuum v 0 := by
  rw [ZhuRecursionAt]
  have h1 : vSqZ W W.vacuum 0 (-1) v = v := by
    rw [vSqZ_vacuum_scalar, sqBracketCoeffZ_vacuum_neg_one, one_smul]
  have h2 : torusTwoPoint N W.vacuum v = torusOnePoint N v := by
    rw [torusTwoPoint_eq_gradedTraceOp, oMod_vacuum, ← Module.End.one_eq_id, one_mul]
    rfl
  have htail : ∀ k : ℕ, qConv (G (k + 1))
      (torusOnePoint N (vSqZ W W.vacuum 0 (2 * (k + 1) - 1 : ℤ) v)) = 0 := by
    intro k
    rw [show vSqZ W W.vacuum 0 (2 * (k + 1) - 1 : ℤ) v = 0 from by
      rw [vSqZ_vacuum_scalar, sqBracketCoeffZ_vacuum_of_ne _ (by omega), zero_smul],
      torusOnePoint_zero, qConv_zero_right]
  rw [h1, h2, finsum_congr htail, finsum_zero, add_zero]

/-- The vacuum on the left, pinned family. -/
theorem zhuRecursionPinned_vacuum_left (v : 𝒱) : ZhuRecursionPinned N W.vacuum v 0 :=
  zhuRecursionAt_vacuum_left N zhuG v

end Main

end VOA
