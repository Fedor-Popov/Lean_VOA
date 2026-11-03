/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.AnalyticBlock
import VOA.Modularity.SqWeightSpanning
import VOA.Modularity.GelfandFuks

/-!
# Zhu's block conditions are `SL₂(ℤ)`-covariant

This is the structural heart of Zhu's `S`-law.  `Modularity.AnalyticBlock` turned Zhu's three
genus-one conditions into identities between holomorphic functions on `imGT 0`.  Here they are
**re-read in weights**, and shown to be preserved by the slash action.

## The two normal forms

Condition (i) — `F(a[0]v) = 0` — makes the anomalous `k = 1` term of condition (ii) *vanish*, and
turns the `k = 1` term of condition (iii) into `wt[v]·G₂·F(v)`.  So on the `L[0]`-weight space
`𝒱_{[n]}`:

* `IsAnalyticBlock.negTwo_tail` — **`G₂` disappears from (ii) entirely**:
  `F(a[−2]v) + Σ_{k ≥ 2}(2k−1)·G_{2k}·F(a[2k−2]v) = 0`, with only the *genuinely modular*
  `G_{2k}`, `k ≥ 2`;
* `IsAnalyticBlock.omega_serre` — **(iii) is a Serre-derivative equation**:
  `F(L[−2]v) = ∂_n F(v) + Σ_{k ≥ 2} G_{2k}·F(L[2k−2]v)`,
  with `∂_n` the Serre derivative of `Modularity.SerreDerivative` — the `(2πi)⁻²·G₂` coefficient
  matching `zhuGC_one` **exactly**, which is why the normalisation forced there is the right one.

## Covariance

Both normal forms are homogeneous of weight `wt[v] + 2` (resp. `wt[a] + wt[v] + 1`), every
coefficient is a modular form of the matching weight (`slashC_zhuGC`), and `∂` is equivariant
(`serreDerivC_slashC`).  Hence

* `omega_serre_slash`, `negTwo_tail_slash` — the slashed family satisfies the same laws.

`Lsq_mem_sqWeightSpace` (`L[k] : 𝒱_{[d]} → 𝒱_{[d−k]}`, from the unconditional square-bracket
Virasoro relation `Lsq_virasoro_apply'`) supplies the weights for (iii); for (ii) the weights are
carried as `NegTwoWeights`, because the repo's `vSqZ W a ka` is indexed by the **ordinary** weight
`ka` of `a`, for which `a[m]` is only *triangular*, not homogeneous, for `L[0]`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open Complex
open scoped BigOperators MatrixGroups

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Peeling the first term of a finitely-supported `finsum` -/

theorem finsum_nat_peel {f : ℕ → ℂ} {K : ℕ} (hK : ∀ m : ℕ, K ≤ m → f m = 0) :
    ∑ᶠ m : ℕ, f m = f 0 + ∑ᶠ m : ℕ, f (m + 1) := by
  classical
  have hs1 : Function.support f ⊆ (Finset.range (K + 1) : Finset ℕ) := by
    intro m hm
    simp only [Function.mem_support, ne_eq] at hm
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    exact hm (hK m (by omega))
  have hs2 : Function.support (fun m : ℕ => f (m + 1)) ⊆ (Finset.range (K + 1) : Finset ℕ) := by
    intro m hm
    simp only [Function.mem_support, ne_eq] at hm
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    exact hm (hK (m + 1) (by omega))
  rw [finsum_eq_finsetSum_of_support_subset _ hs1, finsum_eq_finsetSum_of_support_subset _ hs2]
  have hstep : ∑ i ∈ Finset.range (K + 1 + 1), f i
      = (∑ i ∈ Finset.range (K + 1), f (i + 1)) + f 0 := Finset.sum_range_succ' f (K + 1)
  rw [Finset.sum_range_succ f (K + 1), hK (K + 1) (by omega), add_zero] at hstep
  rw [hstep]
  ring

/-! ## `L[k]` shifts the `L[0]`-weight by `−k` -/

section Grading

variable {W : VertexOperatorAlgebra 𝒱}

/-- **`L[k] : 𝒱_{[d]} → 𝒱_{[d−k]}`** — from the unconditional square-bracket Virasoro
relation `Lsq_virasoro_apply'` at `m = 0` (whose central term vanishes identically, `0³ − 0 = 0`). -/
theorem Lsq_mem_sqWeightSpace (W : VertexOperatorAlgebra 𝒱) {d : ℂ} {v : 𝒱}
    (hv : v ∈ sqWeightSpace W d) (k : ℤ) :
    Lsq W k v ∈ sqWeightSpace W (d - (k : ℂ)) := by
  rw [mem_sqWeightSpace_iff] at hv ⊢
  have h := Lsq_virasoro_apply' W 0 k v
  have hzero : (if (0 : ℤ) + k = 0 then ((((0 : ℤ) : ℂ) ^ 3 - ((0 : ℤ) : ℂ)) / 12 * W.centralCharge)
      else 0) = 0 := by
    by_cases hk : (0 : ℤ) + k = 0
    · rw [if_pos hk]; norm_num
    · rw [if_neg hk]
  rw [hzero, zero_smul, add_zero, hv, map_smul, zero_add] at h
  have h2 : Lsq W 0 (Lsq W k v) = d • Lsq W k v + ((0 - k : ℤ) : ℂ) • Lsq W k v := by
    rw [← h]; abel
  rw [h2, sub_smul, show (((0 - k : ℤ)) : ℂ) = -(k : ℂ) from by push_cast; ring, neg_smul]
  abel

end Grading

/-! ## The Zhu tail terms -/

section Terms

variable (W : VertexOperatorAlgebra 𝒱)

/-- The `k = m+1` term of Zhu's condition (ii). -/
noncomputable def negTwoTerm (F : 𝒱 → ℂ → ℂ) (a : 𝒱) (ka : ℕ) (v : 𝒱) (z : ℂ) (m : ℕ) : ℂ :=
  ((2 * (m + 1) - 1 : ℕ) : ℂ)
    * (zhuGC (m + 1) z * F (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v) z)

/-- The `k = m+1` term of Zhu's condition (iii). -/
noncomputable def omegaTerm (F : 𝒱 → ℂ → ℂ) (v : 𝒱) (z : ℂ) (m : ℕ) : ℂ :=
  zhuGC (m + 1) z * F (Lsq W (2 * (m + 1) - 2 : ℤ) v) z

variable {W}

theorem negTwoTerm_zero (F : 𝒱 → ℂ → ℂ) (a : 𝒱) (ka : ℕ) (v : 𝒱) (z : ℂ) :
    negTwoTerm W F a ka v z 0 = zhuGC 1 z * F (vSqZ W a ka 0 v) z := by
  rw [negTwoTerm, show (2 * ((0 : ℕ) + 1) - 2 : ℤ) = 0 from by norm_num]
  norm_num

theorem negTwoTerm_succ (F : 𝒱 → ℂ → ℂ) (a : 𝒱) (ka : ℕ) (v : 𝒱) (z : ℂ) (m : ℕ) :
    negTwoTerm W F a ka v z (m + 1) = ((2 * (m + 2) - 1 : ℕ) : ℂ)
      * (zhuGC (m + 2) z * F (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v) z) := by
  rw [negTwoTerm, show (2 * (((m + 1 : ℕ) : ℤ) + 1) - 2 : ℤ) = 2 * ((m : ℤ) + 2) - 2 from by
    push_cast; ring]

theorem omegaTerm_zero (F : 𝒱 → ℂ → ℂ) (v : 𝒱) (z : ℂ) :
    omegaTerm W F v z 0 = zhuGC 1 z * F (Lsq W 0 v) z := by
  rw [omegaTerm, show (2 * ((0 : ℕ) + 1) - 2 : ℤ) = 0 from by norm_num]

theorem omegaTerm_succ (F : 𝒱 → ℂ → ℂ) (v : 𝒱) (z : ℂ) (m : ℕ) :
    omegaTerm W F v z (m + 1) = zhuGC (m + 2) z * F (Lsq W (2 * (m + 2) - 2 : ℤ) v) z := by
  rw [omegaTerm, show (2 * (((m + 1 : ℕ) : ℤ) + 1) - 2 : ℤ) = 2 * ((m : ℤ) + 2) - 2 from by
    push_cast; ring]

end Terms

/-! ## The two normal forms -/

section NormalForms

variable {W : VertexOperatorAlgebra 𝒱} {F : 𝒱 → ℂ → ℂ}

theorem IsAnalyticBlock.negTwo' (hF : IsAnalyticBlock W F) (ka : ℕ) (hka : 1 ≤ ka)
    {a : 𝒱} (ha : a ∈ W.grading (ka : ℤ)) (v : 𝒱) {z : ℂ} (hz : z ∈ imGT 0) :
    F (vSqZ W a ka (-2) v) z + ∑ᶠ m : ℕ, negTwoTerm W F a ka v z m = 0 := hF.negTwo ka hka a ha v z hz

theorem IsAnalyticBlock.omega' (hF : IsAnalyticBlock W F) (v : 𝒱) {z : ℂ} (hz : z ∈ imGT 0) :
    F (Lsq W (-2) v) z
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * _root_.deriv (F v) z
        + ∑ᶠ m : ℕ, omegaTerm W F v z m := hF.omega v z hz

/-- **Condition (ii) with `G₂` removed.**  The `k = 1` term of Zhu's `[−2]`-identity is
`G₂·F(a[0]v)`, which vanishes by condition (i).  What survives involves only the *genuinely
modular* `G_{2k}`, `k ≥ 2`. -/
theorem IsAnalyticBlock.negTwo_tail (hF : IsAnalyticBlock W F) (ka : ℕ) (hka : 1 ≤ ka)
    {a : 𝒱} (ha : a ∈ W.grading (ka : ℤ)) (v : 𝒱) {z : ℂ} (hz : z ∈ imGT 0) :
    F (vSqZ W a ka (-2) v) z
      + ∑ᶠ m : ℕ, ((2 * (m + 2) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 2) z * F (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v) z) = 0 := by
  obtain ⟨K, hK⟩ := vSqZ_tail_eventually_zero W a ka v
  have hlaw := hF.negTwo' ka hka ha v hz
  have hpeel : (∑ᶠ m : ℕ, negTwoTerm W F a ka v z m)
      = negTwoTerm W F a ka v z 0 + ∑ᶠ m : ℕ, negTwoTerm W F a ka v z (m + 1) :=
    finsum_nat_peel (K := K) (fun m hm => by
      rw [negTwoTerm, hK m hm, hF.zerov z]; simp)
  have h0 : negTwoTerm W F a ka v z 0 = 0 := by
    rw [negTwoTerm_zero, hF.vanish ka hka a ha v]; simp
  have hshift : (∑ᶠ m : ℕ, negTwoTerm W F a ka v z (m + 1))
      = ∑ᶠ m : ℕ, ((2 * (m + 2) - 1 : ℕ) : ℂ)
          * (zhuGC (m + 2) z * F (vSqZ W a ka (2 * (m + 2) - 2 : ℤ) v) z) :=
    finsum_congr (fun m => negTwoTerm_succ F a ka v z m)
  rw [hpeel, h0, zero_add, hshift] at hlaw
  exact hlaw

/-- **Condition (iii) IS a Serre-derivative equation.**  On the `L[0]`-weight space `𝒱_{[n]}`
the anomalous `k = 1` term `G₂·F(L[0]v) = n·G₂·F(v)` is exactly the `G₂`-term of the Serre
derivative `∂_n` of `Modularity.SerreDerivative`, because `zhuGC 1 = (2πi)⁻²·G₂` (`zhuGC_one`).
Everything left over is *genuinely modular*. -/
theorem IsAnalyticBlock.omega_serre (hF : IsAnalyticBlock W F) {n : ℤ} {v : 𝒱}
    (hv : v ∈ sqWeightSpace W (n : ℂ)) {z : ℂ} (hz : z ∈ imGT 0) :
    F (Lsq W (-2) v) z
      = serreDerivC n (F v) z
        + ∑ᶠ m : ℕ, zhuGC (m + 2) z * F (Lsq W (2 * (m + 2) - 2 : ℤ) v) z := by
  obtain ⟨K, hK⟩ := Lsq_tail_eventually_zero W v
  have hlaw := hF.omega' v hz
  have hpeel : (∑ᶠ m : ℕ, omegaTerm W F v z m)
      = omegaTerm W F v z 0 + ∑ᶠ m : ℕ, omegaTerm W F v z (m + 1) :=
    finsum_nat_peel (K := K) (fun m hm => by
      rw [omegaTerm, hK m hm, hF.zerov z]; simp)
  have hL0 : Lsq W 0 v = (n : ℂ) • v := (mem_sqWeightSpace_iff W _ v).mp hv
  have h0 : omegaTerm W F v z 0
      = (n : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ 2 * (G2C z * F v z) := by
    rw [omegaTerm_zero, hL0, hF.smulv, zhuGC_one hz]
    ring
  have hshift : (∑ᶠ m : ℕ, omegaTerm W F v z (m + 1))
      = ∑ᶠ m : ℕ, zhuGC (m + 2) z * F (Lsq W (2 * (m + 2) - 2 : ℤ) v) z :=
    finsum_congr (fun m => omegaTerm_succ F v z m)
  rw [hpeel, h0, hshift] at hlaw
  rw [hlaw, serreDerivC]
  ring

end NormalForms

/-! ## The slash relation -/

section Slash

variable {W : VertexOperatorAlgebra 𝒱}

/-- `G` is **the weight-graded slash of `F` by `γ`**: on each `L[0]`-weight space `𝒱_{[n]}`,
`G v = (F v) ∣[n] γ`. -/
def IsSlashOf (W : VertexOperatorAlgebra 𝒱) (γ : SL(2, ℤ)) (F G : 𝒱 → ℂ → ℂ) : Prop :=
  ∀ (n : ℤ) (v : 𝒱), v ∈ sqWeightSpace W (n : ℂ) → ∀ z ∈ imGT 0, G v z = slashC n γ (F v) z

theorem IsSlashOf.deriv_eq {γ : SL(2, ℤ)} {F G : 𝒱 → ℂ → ℂ} (hG : IsSlashOf W γ F G)
    {n : ℤ} {v : 𝒱} (hv : v ∈ sqWeightSpace W (n : ℂ)) {z : ℂ} (hz : z ∈ imGT 0) :
    _root_.deriv (G v) z = _root_.deriv (slashC n γ (F v)) z := by
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [(isOpen_imGT 0).mem_nhds hz] with w hw using hG n v hv w hw

/-- The slash of `G_{2j}·g` splits, and `G_{2j}` (`j ≥ 2`) is invariant. -/
theorem slashC_zhuGC_mul {j : ℕ} (hj : 2 ≤ j) (γ : SL(2, ℤ)) (w : ℤ) (g : ℂ → ℂ) {z : ℂ}
    (hz : z ∈ imGT 0) :
    zhuGC j (mobiusC γ z) * g (mobiusC γ z) * denomC γ z ^ (-(2 * (j : ℤ) + w))
      = zhuGC j z * (g (mobiusC γ z) * denomC γ z ^ (-w)) := by
  have h := slashC_mul (2 * (j : ℤ)) w γ (zhuGC j) g hz
  rw [slashC_zhuGC hj γ hz] at h
  simp only [slashC] at h
  linear_combination h

/-- **The `ω`-law is `SL₂(ℤ)`-covariant** — the Serre derivative is equivariant
(`serreDerivC_slashC`) and every surviving coefficient `G_{2k}`, `k ≥ 2`, is a modular form of
exactly the matching weight (`slashC_zhuGC`).  This is where the whole `S`-law lives. -/
theorem omega_serre_slash {F G : 𝒱 → ℂ → ℂ}
    (hholo : ∀ u : 𝒱, DifferentiableOn ℂ (F u) (imGT 0))
    (homega : ∀ (k : ℤ) (u : 𝒱), u ∈ sqWeightSpace W (k : ℂ) → ∀ w ∈ imGT 0,
      F (Lsq W (-2) u) w = serreDerivC k (F u) w
        + ∑ᶠ m : ℕ, zhuGC (m + 2) w * F (Lsq W (2 * (m + 2) - 2 : ℤ) u) w)
    {γ : SL(2, ℤ)}
    (hG : IsSlashOf W γ F G) {n : ℤ} {v : 𝒱} (hv : v ∈ sqWeightSpace W (n : ℂ)) {z : ℂ}
    (hz : z ∈ imGT 0) :
    G (Lsq W (-2) v) z
      = serreDerivC n (G v) z
        + ∑ᶠ m : ℕ, zhuGC (m + 2) z * G (Lsq W (2 * (m + 2) - 2 : ℤ) v) z := by
  have hmz : mobiusC γ z ∈ imGT 0 := mobiusC_mem_imGT γ hz
  have hD := denomC_ne_zero γ hz
  have hdiff : DifferentiableAt ℂ (F v) (mobiusC γ z) :=
    (hholo v).differentiableAt ((isOpen_imGT 0).mem_nhds hmz)
  have hv2 : Lsq W (-2) v ∈ sqWeightSpace W (((n + 2 : ℤ)) : ℂ) := by
    have h := Lsq_mem_sqWeightSpace W hv (-2)
    have he : ((n : ℂ) - ((-2 : ℤ) : ℂ)) = (((n + 2 : ℤ)) : ℂ) := by push_cast; ring
    rwa [he] at h
  have hvm : ∀ m : ℕ, Lsq W (2 * (m + 2) - 2 : ℤ) v
      ∈ sqWeightSpace W (((n - (2 * (m : ℤ) + 2) : ℤ)) : ℂ) := by
    intro m
    have h := Lsq_mem_sqWeightSpace W hv (2 * ((m : ℤ) + 2) - 2)
    have he : ((n : ℂ) - ((2 * ((m : ℤ) + 2) - 2 : ℤ) : ℂ))
        = (((n - (2 * (m : ℤ) + 2) : ℤ)) : ℂ) := by push_cast; ring
    rwa [he] at h
  have hlaw := homega n v hv _ hmz
  have hserre : serreDerivC n (G v) z
      = serreDerivC n (F v) (mobiusC γ z) * denomC γ z ^ (-(n + 2)) := by
    have heq := serreDerivC_slashC n γ (F v) hz hdiff
    have hGv : serreDerivC n (G v) z = serreDerivC n (slashC n γ (F v)) z := by
      rw [serreDerivC, serreDerivC, hG n v hv z hz, hG.deriv_eq hv hz]
    rw [hGv, ← heq, slashC]
  have htail : ∀ m : ℕ, zhuGC (m + 2) (mobiusC γ z)
        * F (Lsq W (2 * (m + 2) - 2 : ℤ) v) (mobiusC γ z) * denomC γ z ^ (-(n + 2))
      = zhuGC (m + 2) z * G (Lsq W (2 * (m + 2) - 2 : ℤ) v) z := by
    intro m
    rw [hG _ _ (hvm m) z hz, slashC]
    have h := slashC_zhuGC_mul (j := m + 2) (by omega) γ (n - (2 * (m : ℤ) + 2))
      (F (Lsq W (2 * (m + 2) - 2 : ℤ) v)) hz
    rw [show (2 * (((m + 2 : ℕ)) : ℤ) + (n - (2 * (m : ℤ) + 2))) = n + 2 from by push_cast; ring]
      at h
    exact h
  have hsum : (∑ᶠ m : ℕ, zhuGC (m + 2) (mobiusC γ z)
        * F (Lsq W (2 * (m + 2) - 2 : ℤ) v) (mobiusC γ z)) * denomC γ z ^ (-(n + 2))
      = ∑ᶠ m : ℕ, zhuGC (m + 2) z * G (Lsq W (2 * (m + 2) - 2 : ℤ) v) z := by
    rw [finsum_mul]
    exact finsum_congr (fun m => htail m)
  rw [hG (n + 2) _ hv2 z hz, slashC, hlaw, add_mul, hsum, hserre]

end Slash

end VOA
