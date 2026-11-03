/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.InvariantFormCanonicalPStep
import Mathlib.Algebra.Group.ForwardDiff

/-!
# Core FHL: the weight-1 quasi-primary matching-mode identity `QPMatch` (Li 1994, Prop 2.6)

This file proves `QPMatch hne u` for a weight-1 current `u ∈ 𝒱₁`, the single residual at which the
`Core.InvariantForm*` reduction of the invariant bilinear form bottoms out.

The genuine ingredients (all axiom-free):
* **`vacCoord_a_raise`** — the raising engine `(2p−M−2)·vacCoord(a₍M+1₎X) = −vacCoord(a₍M₎(L₁X))`
  for a quasi-primary `a` (`L₁a=0`), from the `[L₁,a₍M₎]` bracket and `vacCoord(L₁·)=0`.
* **`vacCoord_a_low_mode_zero`** — low-mode vanishing: `vacCoord(a₍M₎X)=0` for `M ≤ 2p−2`,
  ALL `X` (induction on `grade X` via the engine).
* **`KID`** — the combinatorial collapse `∑_k (n)_k/k!·gBinom(n+k,i) = (−1)^{−n}δ_{i,−n}` (`n≤0`).
* **`vacCoord_iterate`** — the all-integer Borcherds iterate pushed through `vacCoord`.

For `n = p−q ≤ 0`: in the `adjPair` expansion the tower coefficient `∏(−(n+l))` vanishes for
`k > −n`, so every surviving `u`-first term carries a non-positive `u`-mode and dies by
`vacCoord_u_nonpos_eq_zero`; the `a`-first family then collapses by `KID` (off the resonant index)
and `vacCoord_a_low_mode_zero` (above it), leaving the single RHS term — no induction.

## References
* Li, Mem. AMS 104 (1993) Prop 2.6; Frenkel–Huang–Lepowsky [199]; Gannon §5.1.3.
-/

open VOA VOA.VertexOperatorAlgebra
open scoped BigOperators fwdDiff
open Classical
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

namespace VOA

/-! ## The raising engine `(*)` and the low-mode vanishing for a quasi-primary `a`. -/

/-- **The raising engine.** For quasi-primary `a ∈ 𝒱_p` (`L₁a=0`) and any `X`:
`(2p−M−2)·vacCoord(a₍M+1₎X) = − vacCoord(a₍M₎(L₁X))`. -/
theorem vacCoord_a_raise (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {p : ℤ} {a : V} (ha : a ∈ W.grading p)
    (hqpa : W.L 1 a = 0) (M : ℤ) (X : V) :
    (2 * (p : ℂ) - M - 2) • vacCoord W hne (W.smul a (M + 1) X)
      = - vacCoord W hne (W.smul a M (W.L 1 X)) := by
  have hbr := W.L1_bracket_smul ha M X
  rw [hqpa, PreVertexAlgebra.smul_zero_left, add_zero] at hbr
  have h := congrArg (fun y => vacCoord W hne y) hbr
  simp only at h
  rw [map_sub, map_smul, vacCoord_L1_eq_zero hne hqp (W.smul a M X), zero_sub] at h
  exact h.symm

/-- **Low-mode vanishing.** For quasi-primary `a ∈ 𝒱_p` (`L₁a=0`) and ANY `X`,
`vacCoord(a₍M₎X) = 0` whenever `M ≤ 2p − 2`. Induction on the grade of `X`. -/
theorem vacCoord_a_low_mode_zero (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {p : ℤ} {a : V} (ha : a ∈ W.grading p)
    (hqpa : W.L 1 a = 0) :
    ∀ {M : ℤ}, M ≤ 2 * p - 2 → ∀ X : V, vacCoord W hne (W.smul a M X) = 0 := by
  have hbase : ∀ {r : ℤ}, r ≤ 0 → ∀ {X : V}, X ∈ W.grading r → ∀ {M : ℤ}, M ≤ 2 * p - 2 →
      vacCoord W hne (W.smul a M X) = 0 := by
    intro r hr X hX M hM
    rcases lt_or_ge r 0 with hrneg | hr0
    · rw [eq_zero_of_mem_neg_grading W hrneg hX, PreVertexAlgebra.smul_zero_right, map_zero]
    · have hr0' : r = 0 := le_antisymm hr hr0
      subst hr0'
      rw [W.vacuum_grade, Submodule.mem_span_singleton] at hX
      obtain ⟨c, rfl⟩ := hX
      rw [PreVertexAlgebra.smul_smul_right, map_smul]
      rcases eq_or_ne M (p - 1) with hMp | hMp
      · subst hMp
        rw [W.toPreVertexAlgebra.smul_vacuum_nonneg a (by omega : (0:ℤ) ≤ p - 1), map_zero, smul_zero]
      · have hmem : W.smul a M W.vacuum ∈ W.grading (p + 0 - M - 1) :=
          W.smul_mem_grading ha W.vacuum_mem M
        rw [vacCoord_of_mem_ne W hne (by omega : p + 0 - M - 1 ≠ 0) hmem, smul_zero]
  have key : ∀ (N : ℕ) {r : ℤ}, r.toNat ≤ N → ∀ {X : V}, X ∈ W.grading r →
      ∀ {M : ℤ}, M ≤ 2 * p - 2 → vacCoord W hne (W.smul a M X) = 0 := by
    intro N
    induction N with
    | zero => intro r hrN X hX M hM; exact hbase (by omega) hX hM
    | succ K ih =>
        intro r hrN X hX M hM
        rcases lt_or_ge r 1 with hr | hr
        · exact hbase (by omega) hX hM
        · have heng := vacCoord_a_raise hne hqp ha hqpa (M - 1) X
          rw [show (M - 1 + 1 : ℤ) = M by ring] at heng
          have hcoeff : (2 * (p : ℂ) - ((M - 1 : ℤ) : ℂ) - 2) ≠ 0 := by
            have heq : (2 * (p : ℂ) - ((M - 1 : ℤ) : ℂ) - 2)
                = ((2 * p - (M - 1) - 2 : ℤ) : ℂ) := by push_cast; ring
            rw [heq]; exact_mod_cast (show (2 * p - (M - 1) - 2 : ℤ) ≠ 0 by omega)
          have hL1X : W.L 1 X ∈ W.grading (r - 1) := by
            have := L_one_pow_mem W hX 1
            rwa [pow_one, Nat.cast_one] at this
          have hih : vacCoord W hne (W.smul a (M - 1) (W.L 1 X)) = 0 :=
            ih (r := r - 1) (by omega) hL1X (by omega)
          rw [hih, neg_zero] at heng
          rcases smul_eq_zero.mp heng with hc | hv
          · exact absurd hc hcoeff
          · exact hv
  intro M hM X
  have hXtop : X ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading (motive := fun X =>
      vacCoord W hne (W.smul a M X) = 0) hXtop ?_ ?_ ?_
  · intro r X hX; exact key r.toNat le_rfl hX hM
  · show vacCoord W hne (W.smul a M (0 : V)) = 0
    rw [PreVertexAlgebra.smul_zero_right, map_zero]
  · intro X Y hX hY
    show vacCoord W hne (W.smul a M (X + Y)) = 0
    rw [PreVertexAlgebra.smul_add_right, map_add, hX, hY, add_zero]

/-! ## The combinatorial collapse `KID`. -/

lemma gBinom_fwdDiff (c : ℤ) (j : ℕ) :
    Δ_[(1:ℤ)] (fun x : ℤ => gBinom (x + c) (j + 1)) = (fun x : ℤ => gBinom (x + c) j) := by
  funext x
  simp only [fwdDiff]
  have hp := gBinom_succ_pascal (x + 1 + c) j
  rw [show (x + 1 + c - 1) = x + c by ring] at hp
  rw [show (x + (1:ℤ) + c) = (x + 1 + c) by ring, hp]; ring

lemma gBinom_fwdDiff_iter (c : ℤ) (k j : ℕ) :
    Δ_[(1:ℤ)]^[k] (fun x : ℤ => gBinom (x + c) (k + j)) = (fun x : ℤ => gBinom (x + c) j) := by
  induction k generalizing j with
  | zero => simp
  | succ k IH =>
    rw [Function.iterate_succ_apply', show (k + 1 + j) = (k + (j + 1)) by ring, IH (j+1),
        gBinom_fwdDiff]

lemma gBinom_iter_diff_eval (c : ℤ) (m i : ℕ) (hi : i ≤ m) :
    Δ_[(1:ℤ)]^[m] (fun x : ℤ => gBinom (x + c) i) 0 = if i = m then (1:ℂ) else 0 := by
  rcases eq_or_lt_of_le hi with heq | hlt
  · subst heq
    have h := gBinom_fwdDiff_iter c i 0
    rw [show i + 0 = i by ring] at h
    rw [h]; simp [gBinom_zero]
  · have hsplit : m = (m - i) + i := by omega
    have hne : ¬ (i = m) := by omega
    rw [if_neg hne, hsplit, Function.iterate_add_apply]
    have hinner : (Δ_[(1:ℤ)]^[i] (fun x : ℤ => gBinom (x + c) i))
        = (fun _ : ℤ => (1:ℂ)) := by
      have h := gBinom_fwdDiff_iter c i 0
      rw [show i + 0 = i by ring] at h
      rw [h]; funext x; simp [gBinom_zero]
    rw [hinner]
    obtain ⟨pp, hp⟩ : ∃ pp, m - i = pp + 1 := ⟨m - i - 1, by omega⟩
    rw [hp, Function.iterate_succ_apply, fwdDiff_const]
    have : (Δ_[(1:ℤ)]^[pp] (fun _ : ℤ => (0:ℂ))) = (fun _ : ℤ => (0:ℂ)) :=
      Function.iterate_fixed (by funext x; simp [fwdDiff]) pp
    rw [this]

/-- Coefficient rewrite: `(k!)⁻¹·∏_{l<k}(-m+l) = (-1)^k · gBinom(m,k)`. -/
lemma coeff_rw (m k : ℕ) :
    (k.factorial : ℂ)⁻¹ * (∏ l ∈ Finset.range k, ((-(m:ℤ) : ℂ) + (l : ℂ)))
      = (-1:ℂ)^k * gBinom (m:ℤ) k := by
  have hprod : (∏ l ∈ Finset.range k, ((-(m:ℤ) : ℂ) + (l : ℂ)))
      = (-1:ℂ)^k * ∏ l ∈ Finset.range k, ((m:ℂ) - (l:ℂ)) := by
    rw [show ((-1:ℂ)^k) = ∏ _l ∈ Finset.range k, (-1:ℂ) by
          rw [Finset.prod_const, Finset.card_range],
        ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro l _; push_cast; ring
  rw [hprod, gBinom]
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  push_cast; field_simp

theorem KID (m : ℕ) (i : ℕ) (hi : i ≤ m) :
    (∑ k ∈ Finset.range (m + 1),
        (k.factorial : ℂ)⁻¹ * (∏ l ∈ Finset.range k, ((-(m:ℤ) : ℂ) + (l : ℂ))) * gBinom (-(m:ℤ) + (k:ℤ)) i)
      = if i = m then ((-1 : ℂ) ^ m) else 0 := by
  have step1 : (∑ k ∈ Finset.range (m + 1),
        (k.factorial : ℂ)⁻¹ * (∏ l ∈ Finset.range k, ((-(m:ℤ) : ℂ) + (l : ℂ))) * gBinom (-(m:ℤ) + (k:ℤ)) i)
      = ∑ k ∈ Finset.range (m + 1),
          (-1:ℂ)^k * gBinom (m:ℤ) k * gBinom (-(m:ℤ) + (k:ℤ)) i := by
    apply Finset.sum_congr rfl
    intro k _
    rw [show (k.factorial : ℂ)⁻¹ * (∏ l ∈ Finset.range k, ((-(m:ℤ) : ℂ) + (l : ℂ))) * gBinom (-(m:ℤ) + (k:ℤ)) i
          = ((k.factorial : ℂ)⁻¹ * (∏ l ∈ Finset.range k, ((-(m:ℤ) : ℂ) + (l : ℂ)))) * gBinom (-(m:ℤ) + (k:ℤ)) i by ring,
       coeff_rw m k]
  rw [step1]
  have step2 : (∑ k ∈ Finset.range (m + 1),
          (-1:ℂ)^k * gBinom (m:ℤ) k * gBinom (-(m:ℤ) + (k:ℤ)) i)
      = ∑ k ∈ Finset.range (m + 1),
          (-1:ℂ)^k * (m.choose k : ℂ) * gBinom (-(m:ℤ) + (k:ℤ)) i := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    rw [gBinom_natCast_eq_choose hk]
  rw [step2]
  have hshift := fwdDiff_iter_eq_sum_shift (h := (1:ℤ)) (G := ℂ) (M := ℤ)
    (fun x : ℤ => gBinom (x + (-(m:ℤ))) i) m 0
  have hdiff : (Δ_[(1:ℤ)]^[m] (fun x : ℤ => gBinom (x + (-(m:ℤ))) i)) 0
      = if i = m then (1:ℂ) else 0 := gBinom_iter_diff_eval (-(m:ℤ)) m i hi
  have hshift2 : (Δ_[(1:ℤ)]^[m] (fun x : ℤ => gBinom (x + (-(m:ℤ))) i)) 0
      = ∑ k ∈ Finset.range (m + 1),
          ((-1 : ℤ) ^ (m - k) * (m.choose k : ℤ) : ℤ) • gBinom (-(m:ℤ) + (k:ℤ)) i := by
    rw [hshift]
    apply Finset.sum_congr rfl
    intro k _
    congr 2
    ring
  rw [show (if i = m then ((-1 : ℂ) ^ m) else 0)
        = (-1:ℂ)^m * (if i = m then (1:ℂ) else 0) by by_cases h : i = m <;> simp [h],
      ← hdiff, hshift2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  rw [zsmul_eq_mul]
  push_cast
  have hms : (-1:ℂ)^m * (-1:ℂ)^(m-k) = (-1:ℂ)^k := by
    have hmk : m + (m - k) = k + 2 * (m - k) := by omega
    rw [← pow_add, hmk, pow_add, pow_mul]
    norm_num
  rw [show (-1:ℂ)^m * ((-1:ℂ)^(m-k) * (m.choose k : ℂ) * gBinom (-(m:ℤ) + (k:ℤ)) i)
        = ((-1:ℂ)^m * (-1:ℂ)^(m-k)) * ((m.choose k : ℂ) * gBinom (-(m:ℤ) + (k:ℤ)) i) by ring,
      hms]
  ring

/-! ## Pushing `vacCoord` through the all-integer Borcherds iterate `mode_iterate`. -/

/-- `vacCoord` of the two-point reassociation: push the linear `vacCoord` through the `mode_iterate`
finsum (finiteness from `mode_iterate_body_support_finite`). -/
theorem vacCoord_iterate (hne : W.vacuum ≠ 0) (u a b : V) (ℓ N : ℤ) :
    vacCoord W hne (W.smul (W.smul u ℓ a) N b)
      = ∑ᶠ i : ℕ, ((-1:ℂ)^i * gBinom ℓ i) •
          (vacCoord W hne (W.smul u (ℓ - i) (W.smul a (N + i) b))
            - ((-1:ℂ)^ℓ) • vacCoord W hne (W.smul a (ℓ + N - i) (W.smul u i b))) := by
  rw [mode_iterate W u a ℓ N b]
  rw [map_finsum _ (mode_iterate_body_support_finite (W := W) (u := u) (a := a) (b := b) ℓ N)]
  apply finsum_congr
  intro i
  rw [map_smul, map_sub, map_smul]

/-- The `a`-first family `vacCoord(a₍ℓ+N−i₎(u₍i₎b))` has finite support in `i` (since `u₍i₎b=0`
for large `i`). -/
theorem aFirst_support_finite (hne : W.vacuum ≠ 0) (u a b : V) (ℓ N : ℤ) :
    (Function.support (fun i : ℕ => ((-1:ℂ)^i * gBinom ℓ i)
        * vacCoord W hne (W.smul a (ℓ + N - i) (W.smul u i b)))).Finite := by
  obtain ⟨Nub, hNub⟩ := W.toPreVertexAlgebra.smul_eventually_zero u b
  apply Set.Finite.subset (Set.finite_Iio (Nub.toNat))
  intro i hi
  rw [Function.mem_support] at hi
  by_contra hc
  rw [Set.mem_Iio, not_lt] at hc
  apply hi
  have hge : (Nub : ℤ) ≤ (i : ℤ) := by
    rcases le_or_gt 0 Nub with h0 | h0
    · rw [← Int.toNat_of_nonneg h0]; exact_mod_cast hc
    · omega
  rw [hNub i hge, PreVertexAlgebra.smul_zero_right, map_zero, mul_zero]

/-- **`a`-first collapse for non-positive `u`-mode.** For `u ∈ 𝒱₁` and `ℓ ≤ 0`, the `u`-first family
of the iterate dies (`vacCoord(u₍ℓ−i₎·)=0`), leaving only the `a`-first family. -/
theorem iterate_aFirst (hne : W.vacuum ≠ 0) {u : V} (hu : u ∈ W.grading 1) (a b : V)
    {ℓ : ℤ} (hℓ : ℓ ≤ 0) (N : ℤ) :
    vacCoord W hne (W.smul (W.smul u ℓ a) N b)
      = (- (-1:ℂ)^ℓ) * ∑ᶠ i : ℕ, ((-1:ℂ)^i * gBinom ℓ i)
          * vacCoord W hne (W.smul a (ℓ + N - i) (W.smul u i b)) := by
  rw [vacCoord_iterate hne u a b ℓ N, mul_finsum]
  apply finsum_congr
  intro i
  rw [vacCoord_u_nonpos_eq_zero hne hu (by omega : ℓ - (i:ℤ) ≤ 0) (W.smul a (N + i) b)]
  simp only [smul_eq_mul, zero_sub, mul_neg]
  ring

/-- **`QPMatch` for `n = p − q ≤ 0`** (the matching-mode weight-1 quasi-primary identity). -/
theorem qpmatch_nonpos (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {u : V} (hu : u ∈ W.grading 1)
    {a : V} {p : ℤ} (ha : a ∈ W.grading p) (hqpa : W.L 1 a = 0)
    {b : V} {q : ℤ} (hb : b ∈ W.grading q) (hpq : p ≤ q) :
    canBilin W hne (W.smul u (p - q) a) b = - canBilin W hne a (W.smul u (-(p - q)) b) := by
  rcases lt_or_ge p 0 with hpneg | hp0
  · rw [eq_zero_of_mem_neg_grading W hpneg ha]
    simp [PreVertexAlgebra.smul_zero_right]
  -- Now `0 ≤ p`.  Set `m := (q - p).toNat`.
  have hpq0 : (0 : ℤ) ≤ q - p := by omega
  set m : ℕ := (q - p).toNat with hm_def
  have hm : (q - p : ℤ) = (m : ℤ) := (Int.toNat_of_nonneg hpq0).symm
  clear_value m
  have hpqm : (p - q : ℤ) = -(m : ℤ) := by omega
  have hmq : m ≤ q.toNat := by
    have : (m : ℤ) ≤ q := by omega
    omega
  rw [qp_match_rhs_expand hne ha hqpa, qp_match_lhs_expand hne hqp hu ha hqpa hb]
  simp only [smul_eq_mul]
  -- Step 3: restrict the outer `k`-sum to `range (m+1)` (terms with `k > m` carry a vanishing
  -- product, the factor at `l = m` being `-(((p-q):ℂ)+m) = 0`).
  rw [show (∑ k ∈ Finset.range (q.toNat + 1),
        (↑k.factorial)⁻¹ *
          ((∏ l ∈ Finset.range k, -(((p - q : ℤ) : ℂ) + ((l : ℕ) : ℤ))) *
            vacCoord W hne (W.smul (W.smul u (p - q + ↑k) a) (2 * q - 1 - ↑k) b)))
      = ∑ k ∈ Finset.range (m + 1),
        (↑k.factorial)⁻¹ *
          ((∏ l ∈ Finset.range k, -(((p - q : ℤ) : ℂ) + ((l : ℕ) : ℤ))) *
            vacCoord W hne (W.smul (W.smul u (p - q + ↑k) a) (2 * q - 1 - ↑k) b)) from ?_]
  · -- The `a`-first atom (independent of `k`): `f i := vacCoord(a₍p+q-1-i₎(u₍i₎b))`.
    set f : ℕ → ℂ := fun i => vacCoord W hne (W.smul a (p + q - 1 - (i : ℤ)) (W.smul u i b))
      with hf_def
    clear_value f
    -- `f i = 0` for `i ≥ m+1` (a-mode `p+q-1-i ≤ 2p-2`).
    have hf_zero : ∀ i : ℕ, m + 1 ≤ i → f i = 0 := by
      intro i hi
      rw [hf_def]
      exact vacCoord_a_low_mode_zero hne hqp ha hqpa (by omega : p + q - 1 - (i : ℤ) ≤ 2 * p - 2)
        (W.smul u i b)
    -- Rewrite the inner `vacCoord(...)` for each `k ∈ range(m+1)` via `iterate_aFirst`, then
    -- convert the resulting `∑ᶠ i` into `∑ i ∈ range (m+1)`.
    have hkrw : ∀ k ∈ Finset.range (m + 1),
        vacCoord W hne (W.smul (W.smul u (p - q + ↑k) a) (2 * q - 1 - ↑k) b)
          = (-(-1:ℂ)^(p - q + (k:ℤ))) *
              ∑ i ∈ Finset.range (m + 1),
                ((-1:ℂ)^i * gBinom (p - q + (k:ℤ)) i) * f i := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [iterate_aFirst hne hu a b (show (p - q + (k:ℤ)) ≤ 0 by omega) (2 * q - 1 - (k:ℤ))]
      -- normalise the a-mode `ℓ+N-i = p+q-1-i` inside the finsum body, identifying with `f`.
      have hbody : ∀ i : ℕ,
          ((-1:ℂ)^i * gBinom (p - q + (k:ℤ)) i)
              * vacCoord W hne (W.smul a (p - q + (k:ℤ) + (2 * q - 1 - (k:ℤ)) - (i:ℤ))
                  (W.smul u i b))
            = ((-1:ℂ)^i * gBinom (p - q + (k:ℤ)) i) * f i := by
        intro i
        rw [hf_def]
        congr 3
        omega
      rw [finsum_congr hbody]
      congr 1
      -- convert finsum to finite sum
      rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.range (m + 1)) ?_]
      -- support ⊆ range (m+1)
      intro i hi
      rw [Function.mem_support] at hi
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hc
      rw [not_lt] at hc
      apply hi
      rw [hf_zero i (by omega), mul_zero]
    rw [Finset.sum_congr rfl (fun k hk => by
      rw [hkrw k hk])]
    -- Collapse the double sum: distribute, swap, apply `KID` per `i`, keep only `i = m`.
    have hbigsum :
        (∑ k ∈ Finset.range (m + 1),
            (↑k.factorial)⁻¹ *
              ((∏ l ∈ Finset.range k, -(((p - q : ℤ) : ℂ) + ((l : ℕ) : ℤ))) *
                (-(-1:ℂ) ^ (p - q + (k:ℤ)) *
                  ∑ i ∈ Finset.range (m + 1), (-1:ℂ) ^ i * gBinom (p - q + (k:ℤ)) i * f i)))
          = (-(-1:ℂ) ^ (p - q)) * f m := by
      -- 1. Distribute the inner `∑ i` out, swap order to `∑ i ∈ range(m+1), ∑ k ∈ range(m+1)`.
      rw [show (∑ k ∈ Finset.range (m + 1),
            (↑k.factorial)⁻¹ *
              ((∏ l ∈ Finset.range k, -(((p - q : ℤ) : ℂ) + ((l : ℕ) : ℤ))) *
                (-(-1:ℂ) ^ (p - q + (k:ℤ)) *
                  ∑ i ∈ Finset.range (m + 1), (-1:ℂ) ^ i * gBinom (p - q + (k:ℤ)) i * f i)))
          = ∑ k ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (m + 1),
              ((↑k.factorial)⁻¹ * (∏ l ∈ Finset.range k, -(((p - q : ℤ) : ℂ) + ((l : ℕ) : ℤ))) *
                (-(-1:ℂ) ^ (p - q + (k:ℤ))) * ((-1:ℂ) ^ i * gBinom (p - q + (k:ℤ)) i * f i)) by
        apply Finset.sum_congr rfl; intro k _
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _; ring]
      rw [Finset.sum_comm]
      -- 2. For each `i`, the `k`-sum collapses by `KID` to `(-(-1)^(p-q)) * (-1)^i * (if i=m then (-1)^m else 0) * f i`.
      have hinner : ∀ i ∈ Finset.range (m + 1),
          (∑ k ∈ Finset.range (m + 1),
              ((↑k.factorial)⁻¹ * (∏ l ∈ Finset.range k, -(((p - q : ℤ) : ℂ) + ((l : ℕ) : ℤ))) *
                (-(-1:ℂ) ^ (p - q + (k:ℤ))) * ((-1:ℂ) ^ i * gBinom (p - q + (k:ℤ)) i * f i)))
            = (-(-1:ℂ) ^ (p - q)) * ((-1:ℂ) ^ i * f i) * (if i = m then ((-1:ℂ) ^ m) else 0) := by
        intro i hi
        rw [Finset.mem_range, Nat.lt_succ_iff] at hi
        rw [← KID m i hi, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        -- product sign: `∏ -(↑(p-q)+l) = (-1)^k * ∏ (-(m:ℤ)+l)`
        have hprodsign : (∏ l ∈ Finset.range k, -(((p - q : ℤ) : ℂ) + ((l : ℕ) : ℤ)))
            = (-1:ℂ) ^ k * (∏ l ∈ Finset.range k, ((-(m:ℤ) : ℂ) + (l : ℂ))) := by
          rw [show ((-1:ℂ) ^ k) = ∏ _l ∈ Finset.range k, (-1:ℂ) by
                rw [Finset.prod_const, Finset.card_range], ← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro l _; rw [hpqm]; push_cast; ring
        -- exponent sign: `(-1)^(p-q+k) = (-1)^(p-q) * (-1)^k`
        have hexpsign : (-1:ℂ) ^ (p - q + (k:ℤ)) = (-1:ℂ) ^ (p - q) * (-1:ℂ) ^ k := by
          rw [zpow_add₀ (by norm_num : (-1:ℂ) ≠ 0), zpow_natCast]
        -- gBinom rewrite: `p-q = -(m:ℤ)`
        have hgb : gBinom (p - q + (k:ℤ)) i = gBinom (-(m:ℤ) + (k:ℤ)) i := by rw [hpqm]
        rw [hprodsign, hexpsign, hgb]
        have hsq : (-1:ℂ) ^ k * (-1:ℂ) ^ k = 1 := by
          rw [← pow_add, show k + k = 2 * k by ring, pow_mul]; norm_num
        linear_combination
          (-(((k.factorial : ℂ))⁻¹ * (∏ l ∈ Finset.range k, ((-(m:ℤ) : ℂ) + (l : ℂ))) *
            (-1:ℂ) ^ (p - q) * ((-1:ℂ) ^ i * gBinom (-(m:ℤ) + (k:ℤ)) i * f i))) * hsq
      rw [Finset.sum_congr rfl hinner]
      -- `f m` is exactly the RHS atom (`p+q-1-m = 2p-1`, `↑m = -(p-q)`).
      have hfm : f m = vacCoord W hne (W.smul a (2 * p - 1) (W.smul u (-(p - q)) b)) := by
        rw [hf_def]
        simp only []
        rw [show (p + q - 1 - (m : ℤ)) = 2 * p - 1 by omega,
            show ((m : ℕ) : ℤ) = -(p - q) by omega]
      -- 3. Only `i = m` survives; `(-1)^m·(-1)^m = 1`.
      rw [Finset.sum_eq_single m]
      · rw [if_pos rfl, hfm]
        have hsq : (-1:ℂ) ^ m * (-1:ℂ) ^ m = 1 := by
          rw [← pow_add, show m + m = 2 * m by ring, pow_mul]; norm_num
        rw [show (-(-1:ℂ) ^ (p - q) *
              ((-1:ℂ) ^ m * vacCoord W hne (W.smul a (2 * p - 1) (W.smul u (-(p - q)) b))) *
                (-1:ℂ) ^ m)
            = (-(-1:ℂ) ^ (p - q)) * ((-1:ℂ) ^ m * (-1:ℂ) ^ m) *
                vacCoord W hne (W.smul a (2 * p - 1) (W.smul u (-(p - q)) b)) by ring, hsq]
        ring
      · intro i _ hine
        rw [if_neg hine, mul_zero]
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h
    rw [hbigsum]
    -- 4. Final sign: `-((-1)^q * (-(-1)^(p-q)) * f m) = (-1)^p * f m`.
    have hsign : (-1:ℂ) ^ q * (-1:ℂ) ^ (p - q) = (-1:ℂ) ^ p := by
      rw [← zpow_add₀ (by norm_num : (-1:ℂ) ≠ 0)]
      congr 1; ring
    have hfm : f m = vacCoord W hne (W.smul a (2 * p - 1) (W.smul u (-(p - q)) b)) := by
      rw [hf_def]
      simp only []
      rw [show (p + q - 1 - (m : ℤ)) = 2 * p - 1 by omega,
          show ((m : ℕ) : ℤ) = -(p - q) by omega]
    rw [hfm,
        show -((-1:ℂ) ^ q * (-(-1:ℂ) ^ (p - q) *
          vacCoord W hne (W.smul a (2 * p - 1) (W.smul u (-(p - q)) b))))
        = ((-1:ℂ) ^ q * (-1:ℂ) ^ (p - q)) *
          vacCoord W hne (W.smul a (2 * p - 1) (W.smul u (-(p - q)) b)) by ring, hsign]
  -- prove the sum-restriction
  symm
  apply Finset.sum_subset
  · intro k hk
    rw [Finset.mem_range] at hk ⊢
    omega
  · intro k _ hknotin
    rw [Finset.mem_range, not_lt] at hknotin
    have hprod0 : (∏ l ∈ Finset.range k, -(((p - q : ℤ) : ℂ) + ((l : ℕ) : ℤ))) = 0 := by
      apply Finset.prod_eq_zero (i := m) (Finset.mem_range.mpr (by omega))
      have : ((p - q : ℤ) : ℂ) + ((m : ℕ) : ℤ) = 0 := by
        rw [hpqm]; push_cast; ring
      rw [this]; ring
    rw [hprod0, zero_mul, mul_zero]


set_option maxHeartbeats 1600000

/-! ## The finite-difference identity (FDID) — analog of `KID`.

`∑_{j=0}^m (−1)^j C(m,j) gBinom(−j, t) = if m ≤ t then gBinom(−m, t−m) else 0`.
Proved via `fwdDiff_iter_eq_sum_shift`, like `KID`. -/

/-- One-step forward difference: `Δ_[1] (x ↦ gBinom(-x+c, s+1)) = -(x ↦ gBinom(-x+c-1, s))`. -/
lemma gBinom_neg_fwdDiff (c : ℤ) (s : ℕ) :
    Δ_[(1:ℤ)] (fun x : ℤ => gBinom (-x + c) (s + 1))
      = (fun x : ℤ => - gBinom (-x + c - 1) s) := by
  funext x
  simp only [fwdDiff]
  have hp := gBinom_succ_pascal (-x + c) s
  -- gBinom (-x+c) (s+1) = gBinom (-x+c-1) (s+1) + gBinom (-x+c-1) s
  rw [show (-(x + (1:ℤ)) + c) = (-x + c - 1) by ring, hp]
  ring

/-- Iterated forward difference of `x ↦ gBinom(-x+c, m+j)`, `m` steps:
`Δ_[1]^[m] (x ↦ gBinom(-x+c, m+j)) = (-1)^m • (x ↦ gBinom(-x+c-m, j))`. -/
lemma gBinom_neg_fwdDiff_iter (c : ℤ) (m j : ℕ) :
    Δ_[(1:ℤ)]^[m] (fun x : ℤ => gBinom (-x + c) (m + j))
      = (fun x : ℤ => (-1:ℂ)^m * gBinom (-x + c - m) j) := by
  induction m generalizing c j with
  | zero => funext x; simp
  | succ k IH =>
    rw [Function.iterate_succ_apply, show (k + 1 + j) = k + (j + 1) by ring]
    -- Δ_[1] of (fun x => gBinom (-x+c) (k+(j+1)))
    have hstep : Δ_[(1:ℤ)] (fun x : ℤ => gBinom (-x + c) (k + (j + 1)))
        = (fun x : ℤ => (-1:ℂ) • gBinom (-x + (c-1)) (k + j)) := by
      have := gBinom_neg_fwdDiff c (k + j)
      rw [show (k + j + 1) = (k + (j + 1)) by ring] at this
      rw [this]; funext x; rw [show (-x + c - 1) = (-x + (c-1)) by ring]; simp
    rw [hstep]
    -- pull the scalar (-1) through Δ^[k]
    rw [show (fun x : ℤ => (-1:ℂ) • gBinom (-x + (c-1)) (k + j))
          = (-1:ℂ) • (fun x : ℤ => gBinom (-x + (c-1)) (k + j)) from rfl,
        fwdDiff_iter_const_smul, IH (c-1) j]
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    have harg : (-x + (c-1) - (k:ℤ)) = (-x + c - ((k+1:ℕ):ℤ)) := by push_cast; ring
    rw [show (-1:ℂ) * ((-1:ℂ)^k * gBinom (-x + (c-1) - (k:ℤ)) j)
          = (-1:ℂ)^(k+1) * gBinom (-x + (c-1) - (k:ℤ)) j by ring, harg]

/-- The evaluation at `0`: `Δ_[1]^[m] (x ↦ gBinom(-x, t)) 0 = (-1)^m • (if m ≤ t then gBinom(-m, t-m) else 0)`. -/
lemma gBinom_neg_iter_diff_eval (m t : ℕ) :
    Δ_[(1:ℤ)]^[m] (fun x : ℤ => gBinom (-x) t) 0
      = (-1:ℂ)^m * (if m ≤ t then gBinom (-(m:ℤ)) (t - m) else 0) := by
  rcases le_or_gt m t with hmt | hmt
  · -- t = m + (t-m)
    rw [if_pos hmt]
    have h := gBinom_neg_fwdDiff_iter 0 m (t - m)
    rw [show m + (t - m) = t by omega] at h
    simp only [add_zero] at h
    have happ := congrArg (fun f => f (0:ℤ)) h
    simp only at happ
    rw [happ]
    congr 2
    omega
  · -- m > t : the count runs out, becomes 0
    rw [if_neg (by omega)]
    -- write m = (m - (t+1)) + (t+1); first do t+1 steps to reach const then 0
    have hsplit : m = (m - (t + 1)) + (t + 1) := by omega
    rw [hsplit, Function.iterate_add_apply]
    -- inner: Δ^[t+1] (fun x => gBinom (-x) t)
    have hinner : Δ_[(1:ℤ)]^[t + 1] (fun x : ℤ => gBinom (-x) t)
        = (fun _ : ℤ => (0:ℂ)) := by
      rw [Function.iterate_succ_apply']
      -- Δ^[t] (fun x => gBinom (-x) t) = (fun x => (-1)^t gBinom (-x-t) 0) = const (-1)^t
      have h := gBinom_neg_fwdDiff_iter 0 t 0
      rw [show t + 0 = t by ring] at h
      simp only [add_zero] at h
      have hc : (Δ_[(1:ℤ)]^[t] fun x : ℤ => gBinom (-x) t) = (fun _ : ℤ => (-1:ℂ)^t) := by
        rw [h]; funext x; simp [gBinom_zero]
      rw [hc]
      funext x; simp [fwdDiff]
    rw [hinner]
    have : (Δ_[(1:ℤ)]^[m - (t + 1)] (fun _ : ℤ => (0:ℂ))) = (fun _ : ℤ => (0:ℂ)) :=
      Function.iterate_fixed (by funext x; simp [fwdDiff]) (m - (t + 1))
    rw [this]; simp

/-- **FDID.** `∑_{j=0}^m (−1)^j C(m,j) gBinom(−j, t) = if m ≤ t then gBinom(−m, t−m) else 0`. -/
theorem FDID (m t : ℕ) :
    (∑ j ∈ Finset.range (m + 1), (-1:ℂ)^j * (m.choose j : ℂ) * gBinom (-(j:ℤ)) t)
      = if m ≤ t then gBinom (-(m:ℤ)) (t - m) else 0 := by
  have hshift := fwdDiff_iter_eq_sum_shift (h := (1:ℤ)) (G := ℂ) (M := ℤ)
    (fun x : ℤ => gBinom (-x) t) m 0
  -- hshift : Δ^[m] f 0 = ∑_{k∈range(m+1)} (-1)^(m-k) C(m,k) • f (0 + k•1)
  have heval := gBinom_neg_iter_diff_eval m t
  rw [hshift] at heval
  -- heval : ∑_k (-1)^(m-k) C(m,k) • gBinom(-(k)) t = (-1)^m * (if ...)
  -- rewrite the sum: f(0 + k•1) = gBinom(-(k:ℤ)) t
  rw [show (∑ k ∈ Finset.range (m + 1),
        ((-1 : ℤ) ^ (m - k) * (m.choose k : ℤ)) • (fun x : ℤ => gBinom (-x) t) (0 + k • (1:ℤ)))
      = ∑ k ∈ Finset.range (m + 1), ((-1:ℂ)^(m-k) * (m.choose k : ℂ)) * gBinom (-(k:ℤ)) t from ?_] at heval
  · -- now multiply both sides by (-1)^m: ∑ (-1)^m (-1)^(m-k) C gBinom = (-1)^m * (-1)^m (if..)
    have key : (∑ j ∈ Finset.range (m + 1), (-1:ℂ)^j * (m.choose j : ℂ) * gBinom (-(j:ℤ)) t)
        = (-1:ℂ)^m * (∑ k ∈ Finset.range (m + 1), ((-1:ℂ)^(m-k) * (m.choose k : ℂ)) * gBinom (-(k:ℤ)) t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range, Nat.lt_succ_iff] at hk
      have hms : (-1:ℂ)^m * (-1:ℂ)^(m-k) = (-1:ℂ)^k := by
        have hmk : m + (m - k) = k + 2 * (m - k) := by omega
        rw [← pow_add, hmk, pow_add, pow_mul]; norm_num
      rw [show (-1:ℂ)^m * (((-1:ℂ)^(m-k) * (m.choose k : ℂ)) * gBinom (-(k:ℤ)) t)
            = ((-1:ℂ)^m * (-1:ℂ)^(m-k)) * ((m.choose k : ℂ) * gBinom (-(k:ℤ)) t) by ring, hms]
      ring
    rw [key, heval]
    rw [← mul_assoc, ← pow_add, show m + m = 2 * m by ring, pow_mul]
    norm_num
  · apply Finset.sum_congr rfl
    intro k _
    have hidx : (0 : ℤ) + k • (1:ℤ) = (k:ℤ) := by rw [nsmul_eq_mul]; ring
    simp only [hidx]
    rw [zsmul_eq_mul]
    push_cast
    ring

/-! ## The commutator relation `(★_{-j})`.

For `u ∈ 𝒱₁`, `a ∈ 𝒱_p`, `b ∈ 𝒱_q`, and `j ≥ 1`, the Borcherds commutator at `u`-mode `-j`
(where the `u`-first piece `u₍-j₎(a₍p+q-1+j₎b)` dies because `a₍p+q-1+j₎b ∈ 𝒱_{-j} = 0`) gives:
`u₍-j₎(a₍p+q-1+j₎b) − a₍p+q-1+j₎(u₍-j₎b) = ∑_t gBinom(-j,t)·(u₍t₎a)₍p+q-1-t₎b`.

Via `commBound` (which supplies BOTH the commutator value AND the vanishing `u₍t₎a=0, t≥N`,
sharing the bound `N`), the sum's support lies in `range N`. -/
theorem comm_rel (u a b : V) (p q : ℤ) (j : ℕ) :
    ∃ N : ℕ, (∀ t : ℕ, N ≤ t → W.smul u t a = 0)
      ∧ W.smul u (-(j:ℤ)) (W.smul a (p + q - 1 + j) b)
        - W.smul a (p + q - 1 + j) (W.smul u (-(j:ℤ)) b)
      = ∑ t ∈ Finset.range N, gBinom (-(j:ℤ)) t •
          W.smul (W.smul u t a) (p + q - 1 - (t:ℤ)) b := by
  obtain ⟨N, hzero, hN⟩ := commBound W u a (-(j:ℤ)) (p + q - 1 + j)
  refine ⟨N, hzero, ?_⟩
  -- apply both sides to b
  have happ := congrArg (fun (f : Module.End ℂ V) => f b) hN
  simp only at happ
  -- LHS: ⁅mode (Y u)(-j), mode (Y a)(p+q-1+j)⁆ b = u₍-j₎(a₍..₎b) - a₍..₎(u₍-j₎b)
  rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply] at happ
  -- RHS: ∑_{t:Fin N} gBinom(-j,t) • mode (Y (u₍t₎a)) (-j + (p+q-1+j) - t) b
  rw [LinearMap.sum_apply] at happ
  rw [show W.smul u (-(j:ℤ)) (W.smul a (p + q - 1 + j) b)
        = mode (W.Y u) (-(j:ℤ)) (mode (W.Y a) (p + q - 1 + j) b) from rfl,
      show W.smul a (p + q - 1 + j) (W.smul u (-(j:ℤ)) b)
        = mode (W.Y a) (p + q - 1 + j) (mode (W.Y u) (-(j:ℤ)) b) from rfl]
  rw [happ, ← Fin.sum_univ_eq_sum_range
    (fun t => gBinom (-(j:ℤ)) t • W.smul (W.smul u t a) (p + q - 1 - (t:ℤ)) b) N]
  apply Finset.sum_congr rfl
  intro t _
  rw [LinearMap.smul_apply]
  congr 1
  rw [show mode (W.Y (W.smul u (t:ℕ) a)) (-(j:ℤ) + (p + q - 1 + j) - (t:ℕ)) b
        = W.smul (W.smul u (t:ℕ) a) (-(j:ℤ) + (p + q - 1 + j) - (t:ℕ)) b from rfl]
  congr 1
  ring

theorem qpmatch_pos (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {u : V} (hu : u ∈ W.grading 1)
    {a : V} {p : ℤ} (ha : a ∈ W.grading p) (hqpa : W.L 1 a = 0)
    {b : V} {q : ℤ} (hb : b ∈ W.grading q) (hqp_lt : q < p) :
    canBilin W hne (W.smul u (p - q) a) b = - canBilin W hne a (W.smul u (-(p - q)) b) := by
  -- edge case: q < 0 ⟹ b = 0
  rcases lt_or_ge q 0 with hqneg | hq0
  · rw [eq_zero_of_mem_neg_grading W hqneg hb]
    simp [PreVertexAlgebra.smul_zero_right]
  -- now q ≥ 0, p > q so p ≥ 1.  Set m := (p-q).toNat ≥ 1, P := p.toNat, Q := q.toNat.
  have hp1 : 1 ≤ p := by omega
  set m : ℕ := (p - q).toNat with hm_def
  have hm : (p - q : ℤ) = (m : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
  have hm1 : 1 ≤ m := by omega
  set P : ℕ := p.toNat with hP_def
  have hP : (p : ℤ) = (P : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
  set Q : ℕ := q.toNat with hQ_def
  have hQ : (q : ℤ) = (Q : ℤ) := (Int.toNat_of_nonneg hq0).symm
  -- the scalar atom
  set h : ℕ → ℂ := fun t => vacCoord W hne (W.smul (W.smul u t a) (p + q - 1 - (t:ℤ)) b) with hh_def
  -- h vanishes for t > p
  have hh_vanish : ∀ t : ℕ, (p : ℤ) < (t:ℤ) → h t = 0 := by
    intro t ht
    rw [hh_def]
    simp only []
    have huta : W.smul u (t:ℤ) a = 0 := by
      have hmem := W.smul_mem_grading hu ha (t:ℤ)
      exact eq_zero_of_mem_neg_grading W (by omega : (1 + p - (t:ℤ) - 1 : ℤ) < 0) hmem
    rw [huta, PreVertexAlgebra.smul_zero_left, map_zero]
  -- commutator relation R_{-j} over range(P+1):
  --   ∑_{t∈range(P+1)} gBinom(-j,t)·h(t) = -vacCoord(a₍p+q-1+j₎(u₍-j₎b))
  have comm_rel_P : ∀ j : ℕ, 1 ≤ j →
      (∑ t ∈ Finset.range (P + 1), gBinom (-(j:ℤ)) t * h t)
        = - vacCoord W hne (W.smul a (p + q - 1 + j) (W.smul u (-(j:ℤ)) b)) := by
    intro j hj1
    obtain ⟨N, hzero, hrel⟩ := comm_rel (W := W) u a b p q j
    -- apply vacCoord to hrel
    have hvac := congrArg (vacCoord W hne) hrel
    rw [map_sub, map_sum] at hvac
    -- LHS first term vanishes: u₍-j₎(a₍p+q-1+j₎b) with a₍..₎b ∈ gr(-j) = 0
    have hzero1 : vacCoord W hne (W.smul u (-(j:ℤ)) (W.smul a (p + q - 1 + j) b)) = 0 := by
      have hmem := W.smul_mem_grading ha hb (p + q - 1 + j)
      rw [eq_zero_of_mem_neg_grading W (by omega : (p + q - (p + q - 1 + j) - 1 : ℤ) < 0) hmem,
        PreVertexAlgebra.smul_zero_right, map_zero]
    rw [hzero1, zero_sub] at hvac
    -- hvac : -vacCoord(a₍..₎(u₍-j₎b)) = ∑_{t∈range N} vacCoord(gBinom•...) = ∑ gBinom·h(t)
    rw [show (∑ t ∈ Finset.range N, vacCoord W hne (gBinom (-(j:ℤ)) t •
            W.smul (W.smul u t a) (p + q - 1 - (t:ℤ)) b))
          = ∑ t ∈ Finset.range N, gBinom (-(j:ℤ)) t * h t from ?_] at hvac
    · -- the term function vanishes for t ≥ N and for t > p; equate the two ranges via max.
      have hfzeroN : ∀ t : ℕ, N ≤ t → gBinom (-(j:ℤ)) t * h t = 0 := by
        intro t ht
        have : h t = 0 := by
          rw [hh_def]; simp only []
          rw [hzero t ht, PreVertexAlgebra.smul_zero_left, map_zero]
        rw [this, mul_zero]
      have hfzeroP : ∀ t : ℕ, P + 1 ≤ t → gBinom (-(j:ℤ)) t * h t = 0 := by
        intro t ht
        rw [hh_vanish t (by omega : (p:ℤ) < (t:ℤ)), mul_zero]
      set R : ℕ := max N (P + 1) with hR_def
      have e1 : (∑ t ∈ Finset.range N, gBinom (-(j:ℤ)) t * h t)
          = ∑ t ∈ Finset.range R, gBinom (-(j:ℤ)) t * h t := by
        apply Finset.sum_subset (Finset.range_subset_range.mpr (le_max_left N (P + 1)))
        intro t _ htn
        rw [Finset.mem_range, not_lt] at htn
        exact hfzeroN t htn
      have e2 : (∑ t ∈ Finset.range (P + 1), gBinom (-(j:ℤ)) t * h t)
          = ∑ t ∈ Finset.range R, gBinom (-(j:ℤ)) t * h t := by
        apply Finset.sum_subset (Finset.range_subset_range.mpr (le_max_right N (P + 1)))
        intro t _ htn
        rw [Finset.mem_range, not_lt] at htn
        exact hfzeroP t htn
      rw [e2, ← e1, ← hvac]
    · apply Finset.sum_congr rfl
      intro t _
      rw [map_smul, hh_def, smul_eq_mul]
  -- h 0 = 0 : via the iterate at ℓ=0 (u-first dies on 𝒱₀, a-first dies by low_mode since p+q-1 ≤ 2p-2).
  have hh0 : h 0 = 0 := by
    have key : vacCoord W hne (W.smul (W.smul u (0:ℤ) a) (p + q - 1 - (0:ℤ)) b) = 0 := by
      rw [vacCoord_iterate hne u a b (0:ℤ) (p + q - 1 - (0:ℤ))]
      -- only i=0 survives (gBinom 0 i = δ); both pieces vanish
      rw [finsum_eq_single _ 0 (fun i hi => by
          have : gBinom (0:ℤ) i = 0 := by
            rw [show (0:ℤ) = ((0:ℕ):ℤ) by norm_num,
              gBinom_natCast_eq_zero (by omega : 0 < i)]
          rw [this, mul_zero, zero_smul])]
      -- i = 0 term
      simp only [Nat.cast_zero, pow_zero, gBinom_zero, mul_one, one_smul, zpow_zero]
      rw [show (p + q - 1 - (0:ℤ) + 0) = (p + q - 1) by ring,
          show (0 + (p + q - 1 - (0:ℤ)) - 0) = (p + q - 1) by ring,
          show (0:ℤ) - 0 = 0 by ring]
      have hgr0 : W.smul a (p + q - 1) b ∈ W.grading 0 := by
        have := W.smul_mem_grading ha hb (p + q - 1)
        rwa [show (p + q - (p + q - 1) - 1 : ℤ) = 0 by ring] at this
      rw [vacCoord_u0_grade0 hne hgr0,
        vacCoord_a_low_mode_zero hne hqp ha hqpa
          (by omega : (p + q - 1 : ℤ) ≤ 2 * p - 2)]
      simp
    rw [hh_def]; simp only [Nat.cast_zero]
    convert key using 3
  -- ===== ASSEMBLY =====
  -- Step A: the binomial-weighted sum of commutator relations collapses to (-1)^(m+1) • A.
  -- A := vacCoord(a₍2p-1₎(u₍-m₎b)); note 2p-1 = p+q-1+m and -m = -(p-q).
  set A : ℂ := vacCoord W hne (W.smul a (2 * p - 1) (W.smul u (-(p - q)) b)) with hA_def
  -- For j=1..m-1, R_{-j} = 0 (a-mode p+q-1+j ≤ 2p-2); for j=m, R_{-m} = -A.
  have hRzero : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 →
      (∑ t ∈ Finset.range (P + 1), gBinom (-(j:ℤ)) t * h t) = 0 := by
    intro j hj1 hjm
    rw [comm_rel_P j hj1]
    rw [vacCoord_a_low_mode_zero hne hqp ha hqpa
      (by omega : (p + q - 1 + (j:ℤ)) ≤ 2 * p - 2) (W.smul u (-(j:ℤ)) b), neg_zero]
  have hRm : (∑ t ∈ Finset.range (P + 1), gBinom (-(m:ℤ)) t * h t) = - A := by
    rw [comm_rel_P m hm1, hA_def]
    rw [show (p + q - 1 + (m:ℤ)) = 2 * p - 1 by omega, show (-(m:ℤ)) = -(p - q) by omega]
  -- Step B: the binomial-weighted sum equals S' (the LHS expansion sum) via FDID and hh0.
  -- Define the LHS-expansion sum.
  set S' : ℂ := ∑ k ∈ Finset.range (Q + 1), gBinom (-(m:ℤ)) k * h (m + k) with hS'_def
  have hcollapse : (∑ j ∈ Finset.range (m + 1), (-1:ℂ)^j * (m.choose j : ℂ) *
        (∑ t ∈ Finset.range (P + 1), gBinom (-(j:ℤ)) t * h t)) = S' := by
    -- distribute, swap, FDID
    rw [show (∑ j ∈ Finset.range (m + 1), (-1:ℂ)^j * (m.choose j : ℂ) *
          (∑ t ∈ Finset.range (P + 1), gBinom (-(j:ℤ)) t * h t))
        = ∑ j ∈ Finset.range (m + 1), ∑ t ∈ Finset.range (P + 1),
            ((-1:ℂ)^j * (m.choose j : ℂ) * gBinom (-(j:ℤ)) t) * h t from ?_]
    · rw [Finset.sum_comm]
      -- ∑_t (∑_j ...) h t = ∑_t FDID(m,t) h t
      rw [show (∑ t ∈ Finset.range (P + 1), ∑ j ∈ Finset.range (m + 1),
            ((-1:ℂ)^j * (m.choose j : ℂ) * gBinom (-(j:ℤ)) t) * h t)
          = ∑ t ∈ Finset.range (P + 1),
              (if m ≤ t then gBinom (-(m:ℤ)) (t - m) else 0) * h t from ?_]
      · -- restrict to t ≥ m: t = m + k, k ∈ [0, Q]
        rw [show (∑ t ∈ Finset.range (P + 1),
              (if m ≤ t then gBinom (-(m:ℤ)) (t - m) else 0) * h t)
            = ∑ t ∈ Finset.range (P + 1),
                (if m ≤ t then gBinom (-(m:ℤ)) (t - m) * h t else 0) from
            Finset.sum_congr rfl (fun t _ => by by_cases hmt : m ≤ t <;> simp [hmt])]
        rw [hS'_def]
        -- reindex range(P+1) restricted to {t ≥ m} as range(Q+1) via t = m+k
        rw [← Finset.sum_filter]
        rw [show Finset.filter (fun t => m ≤ t) (Finset.range (P + 1))
              = Finset.map (addLeftEmbedding m) (Finset.range (Q + 1)) from ?_]
        · rw [Finset.sum_map]
          apply Finset.sum_congr rfl
          intro k _
          simp only [addLeftEmbedding_apply]
          rw [show m + k - m = k by omega]
        · ext t
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, addLeftEmbedding_apply]
          constructor
          · rintro ⟨ht, hmt⟩
            exact ⟨t - m, by omega, by omega⟩
          · rintro ⟨k, hk, rfl⟩
            exact ⟨by omega, by omega⟩
      · apply Finset.sum_congr rfl
        intro t _
        rw [← Finset.sum_mul, FDID m t]
    · apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
  -- Step C: the binomial-weighted sum also = (-1)^(m+1) • A (only j=m survives, j<m vanish).
  have hAval : (∑ j ∈ Finset.range (m + 1), (-1:ℂ)^j * (m.choose j : ℂ) *
        (∑ t ∈ Finset.range (P + 1), gBinom (-(j:ℤ)) t * h t)) = (-1:ℂ)^(m+1) * A := by
    rw [Finset.sum_range_succ]
    -- the range m part: j=0 gives the FDID j=0 term = h 0 = 0; j=1..m-1 give R=0
    rw [show (∑ j ∈ Finset.range m, (-1:ℂ)^j * (m.choose j : ℂ) *
          (∑ t ∈ Finset.range (P + 1), gBinom (-(j:ℤ)) t * h t)) = 0 from ?_]
    · -- the j=m term:  (-1)^m C(m,m) (∑ gBinom(-m,t) h t) = (-1)^m * (-A)
      rw [hRm, Nat.choose_self, Nat.cast_one, mul_one, zero_add]
      rw [show (-1:ℂ)^(m+1) = (-1:ℂ)^m * (-1) by rw [pow_succ]]
      ring
    · apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_range] at hj
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · -- j = 0 : ∑_t gBinom(0,t) h t = h 0 = 0
        subst hj0
        rw [show (∑ t ∈ Finset.range (P + 1), gBinom (-((0:ℕ):ℤ)) t * h t) = h 0 from ?_, hh0,
          mul_zero]
        rw [Finset.sum_eq_single 0]
        · simp
        · intro t _ ht0
          have : gBinom (-((0:ℕ):ℤ)) t = 0 := by
            rw [show (-((0:ℕ):ℤ)) = ((0:ℕ):ℤ) by norm_num,
              gBinom_natCast_eq_zero (by omega : 0 < t)]
          rw [this, zero_mul]
        · intro hcon
          exact absurd (Finset.mem_range.mpr (by omega)) hcon
      · -- 1 ≤ j ≤ m-1 : R_{-j} = 0
        rw [hRzero j hjpos (by omega), mul_zero]
  -- combine: S' = (-1)^(m+1) • A
  have hkey : S' = (-1:ℂ)^(m+1) * A := by rw [← hcollapse, hAval]
  -- ===== finish: goal via the two expansions =====
  rw [qp_match_rhs_expand hne ha hqpa, qp_match_lhs_expand hne hqp hu ha hqpa hb]
  -- LHS = -((-1)^q • S'') where S'' is the expansion sum; show S'' = S' first
  -- identify the expansion sum with S'
  have hSexp : (∑ k ∈ Finset.range (q.toNat + 1), ((k.factorial:ℂ)⁻¹) •
        ((∏ l ∈ Finset.range k, (-(((p - q : ℤ):ℂ) + (l:ℤ)))) •
          vacCoord W hne (W.smul (W.smul u ((p-q) + k) a) (2*q - 1 - (k:ℤ)) b)))
      = S' := by
    rw [hS'_def, ← hQ_def]
    apply Finset.sum_congr rfl
    intro k _
    -- coefficient: (1/k!)∏(-(n+l)) = gBinom(-m, k)
    have hcoeff : ((k.factorial:ℂ)⁻¹) * (∏ l ∈ Finset.range k, (-(((p - q : ℤ):ℂ) + (l:ℤ))))
        = gBinom (-(m:ℤ)) k := by
      rw [gBinom, div_eq_mul_inv, mul_comm]
      congr 1
      apply Finset.prod_congr rfl
      intro l _
      rw [hm]; push_cast; ring
    -- summand: vacCoord((u₍(p-q)+k₎a)₍2q-1-k₎b) = h(m+k)
    have hsummand : vacCoord W hne (W.smul (W.smul u ((p-q) + (k:ℤ)) a) (2*q - 1 - (k:ℤ)) b)
        = h (m + k) := by
      rw [hh_def]; simp only []
      congr 2
      · rw [hm]; push_cast; ring_nf
      · push_cast; omega
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, hcoeff, hsummand]
  rw [hSexp]
  -- now goal: -((-1)^q • S') = (-1)^p • A
  rw [hkey, smul_eq_mul, smul_eq_mul]
  -- -((-1)^q * ((-1)^(m+1) * A)) = (-1)^p * A ;  q + (m+1) odd-shift: (-1)^q (-1)^(m+1) = -(-1)^p
  have hsign : (-1:ℂ)^q * (-1:ℂ)^(m+1) = -((-1:ℂ)^p) := by
    have hmpow : (-1:ℂ)^(m+1) = (-1:ℂ)^(p - q) * (-1) := by
      rw [pow_succ]
      congr 1
      rw [hm, zpow_natCast]
    rw [hmpow, ← mul_assoc, ← zpow_add₀ (by norm_num : (-1:ℂ) ≠ 0), show q + (p - q) = p by ring]
    ring
  rw [show -((-1:ℂ)^q * ((-1:ℂ)^(m+1) * A)) = ((-1:ℂ)^q * (-1:ℂ)^(m+1)) * (-A) by ring, hsign]
  ring

theorem qpmatch_holds (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {u : V} (hu : u ∈ W.grading 1) :
    QPMatch hne u := by
  intro a p ha hqpa b q hb
  rcases le_or_gt p q with h | h
  · exact qpmatch_nonpos hne hqp hu ha hqpa hb h
  · exact qpmatch_pos hne hqp hu ha hqpa hb h

end VOA
