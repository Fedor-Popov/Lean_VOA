/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.AndersonMoore
import VOA.Huang.AndersonMooreWronskian
import VOA.Huang.AndersonMooreEchelon

/-!
# Reduction of `AndersonMooreInput` to its normalized core

`AndersonMooreInput` speaks about functions `f_i(τ) = Σ_m a_{i,m} e^{2πi(λ_i+m)τ}` on `ℍ` with
`a_{i,m} ∈ ℕ`, `a_{i,0} ≠ 0`, spanning an `S`-invariant family. The analytic Anderson–Moore
argument (Wronskian, Fuchsian equation, Galois transport) wants a *normalized* family: pairwise
distinct exponents, rational coefficients, nonzero leading coefficients. This file performs the
normalization.

* `AMCore` : the normalized statement (an `S`-closed `q^ν`-family with rational coefficients,
  injective exponents and nonzero leading coefficients has rational exponents).
* `andersonMooreInput_of_core` : `AMCore → AndersonMooreInput`.

## The reduction

1. `G_i = Σ_m a_{i,m} X^m` lies in `SubexpPS` (the expansion converges on the imaginary axis,
   coefficients are non-negative) and `f_i = amEval λ_i G_i` on the upper half-plane.
2. Exponents are normalized modulo `ℤ`: `λ_i = μ_i + k_i`, `k_i ∈ ℕ`, with `Re μ_i ∈ [-M, 1-M)`
   for one global `M`, so `μ_i = μ_j` exactly when `λ_i - λ_j ∈ ℤ`; then
   `amEval λ_i G_i = amEval μ_i (X^{k_i} G_i)` (`amEval_add_nat`).
3. In each class `μ = b`, a rational echelon basis (`exists_echelon`) of the `X^{k_i} G_i` gives
   series `X^{o_l} U_l` of pairwise distinct orders, with `U_l(0) ≠ 0`; the new exponents
   `b + o_l` are pairwise distinct across the whole family.
4. Old and new families have the same span (as functions on the upper half-plane), so the new
   family is `S`-closed; `AMCore` makes every `b + o_l` rational, hence every `λ_i`.

No `sorry`, no new axioms.
-/

open Complex Filter Topology

noncomputable section

namespace VOA.Huang.AndersonMoore

open VOA

/-- **The normalized Anderson–Moore statement.** An `S`-closed `q^ν`-family with rational
coefficients, distinct exponents and nonzero leading coefficients has rational exponents. -/
def AMCore : Prop :=
  ∀ (n : ℕ) (ν : Fin n → ℂ) (U : Fin n → PowerSeries ℂ),
    (∀ j, U j ∈ SubexpPS) → (∀ j, RatCoeffs (U j)) → Function.Injective ν →
    (∀ j, PowerSeries.coeff 0 (U j) ≠ 0) →
    ∀ S : Matrix (Fin n) (Fin n) ℂ,
    (∀ i, ∀ z ∈ imGT 0, famF ν U i (-1 / z) = ∑ j, S i j * famF ν U j z) →
    ∀ j, ∃ q : ℚ, (q : ℂ) = ν j

/-! ## Evaluation on the upper half-plane as a function space -/

/-- The function `q^ν U` restricted to the upper half-plane. -/
def evH (ν : ℂ) (U : PowerSeries ℂ) : imGT 0 → ℂ := fun z => amEval ν U z

theorem amEval_zero_series (ν z : ℂ) : amEval ν 0 z = 0 := by
  simp [amEval]

/-- **Shift lemma**: `q^{ν+k} U = q^ν (X^k U)`. -/
theorem amEval_add_nat (ν : ℂ) (k : ℕ) (U : PowerSeries ℂ) (z : ℂ) :
    amEval (ν + k) U z = amEval ν (PowerSeries.X ^ k * U) z := by
  rw [amEval, amEval]
  have hre : (∑' n : ℕ, PowerSeries.coeff n (PowerSeries.X ^ k * U) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)) =
      ∑' m : ℕ, PowerSeries.coeff (m + k) (PowerSeries.X ^ k * U) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m + k : ℕ) : ℂ) * z) := by
    refine ((add_left_injective k).tsum_eq (f := fun n : ℕ =>
      PowerSeries.coeff n (PowerSeries.X ^ k * U) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)) ?_).symm
    intro n hn
    refine ⟨n - k, ?_⟩
    by_contra hne
    apply hn
    have hlt : n < k := by
      by_contra hle
      exact hne (by simp only; omega)
    simp [PowerSeries.coeff_X_pow_mul', show ¬ k ≤ n from by omega]
  rw [hre]
  simp_rw [PowerSeries.coeff_X_pow_mul]
  have he : ∀ m : ℕ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m + k : ℕ) : ℂ) * z) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * z) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z * k) := by
    intro m
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [he, ← mul_assoc, tsum_mul_right]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * z * (ν + k) =
    2 * (Real.pi : ℂ) * Complex.I * z * ν + 2 * (Real.pi : ℂ) * Complex.I * z * k from by ring,
    Complex.exp_add]
  ring

theorem evH_add_nat (ν : ℂ) (k : ℕ) (U : PowerSeries ℂ) :
    evH (ν + k) U = evH ν (PowerSeries.X ^ k * U) := by
  funext z; exact amEval_add_nat ν k U z

/-- Formal spans go to spans of evaluations. -/
theorem evH_mem_span {κ : Type*} (ν : ℂ) (Q : κ → PowerSeries ℂ) (hQ : ∀ k, Q k ∈ SubexpPS)
    {P : PowerSeries ℂ} (hP : P ∈ Submodule.span ℂ (Set.range Q)) :
    P ∈ SubexpPS ∧ evH ν P ∈ Submodule.span ℂ (Set.range fun k => evH ν (Q k)) := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact ⟨hQ k, Submodule.subset_span ⟨k, rfl⟩⟩
  | zero =>
    refine ⟨SubexpPS.zero_mem, ?_⟩
    have : evH ν 0 = 0 := by funext z; exact amEval_zero_series ν z
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    refine ⟨SubexpPS.add_mem hx.1 hy.1, ?_⟩
    have : evH ν (x + y) = evH ν x + evH ν y := by
      funext z; exact amEval_add hx.1 hy.1 z.2
    rw [this]; exact Submodule.add_mem _ hx.2 hy.2
  | smul c x _ hx =>
    refine ⟨SubexpPS.smul_mem hx.1 c, ?_⟩
    have : evH ν (c • x) = c • evH ν x := by
      funext z; exact amEval_smul c ν x z
    rw [this]; exact Submodule.smul_mem _ c hx.2

/-! ## One class: the echelon renormalization -/

/-- **One congruence class.** A finite family `H` of convergent rational series with common
exponent `b` is replaced by a family `q^{b + o_l} U_l` with pairwise distinct `o_l ∈ ℕ`,
`U_l(0) ≠ 0`, rational coefficients, and the same span of functions on the upper half-plane. -/
theorem exists_class_family {ι : Type*} [Finite ι] (b : ℂ) (H : ι → PowerSeries ℂ)
    (hH : ∀ i, H i ∈ SubexpPS) (hR : ∀ i, RatCoeffs (H i)) :
    ∃ (d : ℕ) (o : Fin d → ℕ) (U : Fin d → PowerSeries ℂ),
      (∀ l, U l ∈ SubexpPS) ∧ (∀ l, RatCoeffs (U l)) ∧
      (∀ l, PowerSeries.coeff 0 (U l) ≠ 0) ∧ Function.Injective o ∧
      (∀ l, evH (b + o l) (U l) ∈ Submodule.span ℂ (Set.range fun i => evH b (H i))) ∧
      (∀ i, evH b (H i) ∈ Submodule.span ℂ (Set.range fun l => evH (b + o l) (U l))) ∧
      (∀ i, H i ≠ 0 → 0 < d) := by
  obtain ⟨d, E, hER, hE0, hEo, hEH, hHE⟩ := exists_echelon H hR
  have hEs : ∀ l, E l ∈ SubexpPS := fun l => (evH_mem_span 0 H hH (hEH l)).1
  have hord : ∀ l, (E l).order = ((E l).order.toNat : ℕ∞) := fun l =>
    (ENat.coe_toNat (by simpa [PowerSeries.order_eq_top] using hE0 l)).symm
  have hXU : ∀ l, PowerSeries.X ^ (E l).order.toNat * (E l).divXPowOrder = E l := fun l =>
    PowerSeries.X_pow_order_mul_divXPowOrder
  have hev : ∀ l, evH (b + ((E l).order.toNat : ℕ)) (E l).divXPowOrder = evH b (E l) := by
    intro l; rw [evH_add_nat, hXU]
  refine ⟨d, fun l => (E l).order.toNat, fun l => (E l).divXPowOrder, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l
    have h := (hEs l).shift (E l).order.toNat
    rw [mem_subexpPS]
    refine Subexponential.of_le (fun m => le_of_eq ?_) h
    rw [PowerSeries.coeff_divXPowOrder]
  · intro l m
    obtain ⟨r, hr⟩ := hER l (m + (E l).order.toNat)
    exact ⟨r, by rw [PowerSeries.coeff_divXPowOrder, hr]⟩
  · intro l
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_divXPowOrder]
    exact PowerSeries.coeff_order (hE0 l)
  · intro l l' h
    apply hEo
    simp only at h ⊢
    rw [hord l, hord l', h]
  · intro l
    simp only
    rw [hev l]
    exact (evH_mem_span b H hH (hEH l)).2
  · intro i
    have h := (evH_mem_span b E hEs (hHE i)).2
    have hfun : (fun l => evH b (E l)) =
        fun l => evH (b + ((E l).order.toNat : ℕ)) (E l).divXPowOrder := by
      funext l; rw [hev l]
    rw [hfun] at h
    exact h
  · intro i hi
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      exfalso
      have h := hHE i
      rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at h
      exact hi h
    · exact hd

/-! ## The input family as `q^λ`-series -/

/-- A convergent expansion `Σ_m a_m e^{2πi(λ+m)τ}` is `amEval λ (Σ a_m X^m)`. -/
theorem eq_amEval_of_hasSum {lam : ℂ} {a : ℕ → ℕ} {z s : ℂ}
    (h : HasSum (fun m : ℕ => (a m : ℂ) * cexp (2 * Real.pi * I * (lam + m) * z)) s) :
    s = amEval lam (PowerSeries.mk fun m => (a m : ℂ)) z := by
  rw [amEval, ← tsum_mul_left, ← h.tsum_eq]
  refine tsum_congr fun m => ?_
  rw [PowerSeries.coeff_mk, mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

/-- Convergence of a non-negative expansion on the whole upper half-plane forces subexponential
coefficients. -/
theorem mem_subexpPS_of_hasSum {lam : ℂ} {a : ℕ → ℕ} {f : UpperHalfPlane → ℂ}
    (h : ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ => (a m : ℂ) * cexp (2 * Real.pi * I * (lam + m) * τ)) (f τ)) :
    (PowerSeries.mk fun m => (a m : ℂ)) ∈ SubexpPS := by
  rw [mem_subexpPS]
  intro r hr
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  set y : ℝ := Real.log r / (2 * Real.pi) with hy
  have hy0 : 0 < y := div_pos (Real.log_pos hr) (by positivity)
  let τ : UpperHalfPlane := ⟨Complex.I * y, by simpa using hy0⟩
  have ht : Real.exp (-(2 * Real.pi * y)) = r⁻¹ := by
    rw [hy, show -(2 * Real.pi * (Real.log r / (2 * Real.pi))) = -Real.log r from by
      field_simp, Real.exp_neg, Real.exp_log hr0]
  set c : ℂ := cexp (2 * Real.pi * I * (Complex.I * y) * lam) with hc
  have hterm : ∀ m : ℕ, (a m : ℂ) * cexp (2 * Real.pi * I * (lam + m) * τ) =
      c * (((a m : ℝ) * r⁻¹ ^ m : ℝ) : ℂ) := by
    intro m
    have hτ : (τ : ℂ) = Complex.I * y := rfl
    have h1 : cexp (2 * Real.pi * I * (lam + m) * τ) =
        c * cexp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (Complex.I * y)) := by
      rw [hc, ← Complex.exp_add, hτ]; congr 1; ring
    rw [h1, qexp_I_mul, ht]
    push_cast
    ring
  have hsC : Summable fun m : ℕ => ((((a m : ℝ) * r⁻¹ ^ m : ℝ)) : ℂ) := by
    have h0 := ((h τ).summable.mul_left c⁻¹)
    have hc0 : c ≠ 0 := Complex.exp_ne_zero _
    refine h0.congr fun m => ?_
    rw [hterm, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hs : Summable fun m : ℕ => (a m : ℝ) * r⁻¹ ^ m := Complex.summable_ofReal.mp hsC
  refine ⟨∑' m, (a m : ℝ) * r⁻¹ ^ m, fun m => ?_⟩
  have hle := hs.le_tsum m (fun j _ => by positivity)
  simp only [PowerSeries.coeff_mk, Complex.norm_natCast]
  have hrm : 0 < r ^ m := pow_pos hr0 m
  calc (a m : ℝ) = ((a m : ℝ) * r⁻¹ ^ m) * r ^ m := by
        rw [inv_pow, mul_assoc, inv_mul_cancel₀ hrm.ne', mul_one]
    _ ≤ (∑' m, (a m : ℝ) * r⁻¹ ^ m) * r ^ m := mul_le_mul_of_nonneg_right hle hrm.le

theorem ratCoeffs_mk_nat (a : ℕ → ℕ) : RatCoeffs (PowerSeries.mk fun m => (a m : ℂ)) :=
  fun m => ⟨a m, by simp⟩

/-! ## The normalized family -/

theorem X_pow_mul_mem_subexpPS (k : ℕ) {G : PowerSeries ℂ} (hG : G ∈ SubexpPS) :
    PowerSeries.X ^ k * G ∈ SubexpPS := by
  rw [mem_subexpPS]
  refine Subexponential.of_shift k ?_
  simp only [PowerSeries.coeff_X_pow_mul]
  exact hG

theorem RatCoeffs.X_pow (k : ℕ) : RatCoeffs (PowerSeries.X ^ k : PowerSeries ℂ) := by
  intro m
  rw [PowerSeries.coeff_X_pow]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

/-- **The reduction in the `ℂ`-variable.** If `AMCore` holds, then any `S`-closed family
`q^{λ_i} G_i` of nonzero convergent rational series has rational exponents (no distinctness or
normalization needed). -/
theorem rat_of_core (hcore : AMCore) {n : ℕ} (lam : Fin n → ℂ) (G : Fin n → PowerSeries ℂ)
    (hG : ∀ i, G i ∈ SubexpPS) (hR : ∀ i, RatCoeffs (G i)) (h0 : ∀ i, G i ≠ 0)
    (S : Fin n → Fin n → ℂ)
    (hS : ∀ i, ∀ z ∈ imGT 0,
      amEval (lam i) (G i) (-1 / z) = ∑ j, S i j * amEval (lam j) (G j) z) :
    ∀ i, ∃ q : ℚ, (q : ℂ) = lam i := by
  classical
  -- normalization of the exponents modulo `ℤ`
  set fl : Fin n → ℤ := fun i => ⌊(lam i).re⌋ with hfl
  set M : ℤ := ∑ i, |fl i| with hMdef
  have hM : ∀ i, 0 ≤ fl i + M := by
    intro i
    have h1 := Finset.single_le_sum (f := fun j => |fl j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
    have h2 := neg_abs_le (fl i)
    simp only at h1
    linarith
  set k : Fin n → ℕ := fun i => (fl i + M).toNat with hkdef
  have hk : ∀ i, ((k i : ℕ) : ℤ) = fl i + M := fun i => Int.toNat_of_nonneg (hM i)
  set μ : Fin n → ℂ := fun i => lam i - k i with hμdef
  have hlam : ∀ i, μ i + k i = lam i := fun i => by simp [hμdef]
  have hμre : ∀ i, -(M : ℝ) ≤ (μ i).re ∧ (μ i).re < -(M : ℝ) + 1 := by
    intro i
    have hkR : ((k i : ℕ) : ℝ) = (fl i : ℝ) + M := by exact_mod_cast hk i
    have hre : (μ i).re = (lam i).re - (k i : ℝ) := by simp [hμdef]
    have f1 := Int.floor_le (lam i).re
    have f2 := Int.lt_floor_add_one (lam i).re
    rw [hre, hkR]
    simp only [hfl] at f1 f2 ⊢
    constructor <;> linarith
  have hsep : ∀ i j (o o' : ℕ), μ i + o = μ j + o' → o = o' := by
    intro i j o o' h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re] at hre
    have a1 := hμre i
    have a2 := hμre j
    have b1 : (o : ℝ) < o' + 1 := by linarith
    have b2 : (o' : ℝ) < o + 1 := by linarith
    have c1 : o < o' + 1 := by exact_mod_cast b1
    have c2 : o' < o + 1 := by exact_mod_cast b2
    omega
  -- the classes
  set B : Finset ℂ := Finset.univ.image μ with hB
  let H : (b : B) → {i : Fin n // μ i = b.1} → PowerSeries ℂ :=
    fun _ i => PowerSeries.X ^ k i.1 * G i.1
  have hHs : ∀ b i, H b i ∈ SubexpPS := fun b i => X_pow_mul_mem_subexpPS _ (hG i.1)
  have hHR : ∀ b i, RatCoeffs (H b i) := fun b i => (RatCoeffs.X_pow _).mul (hR i.1)
  choose d o U hU hUR hU0 ho hsp1 hsp2 hpos using
    fun b : B => exists_class_family b.1 (H b) (hHs b) (hHR b)
  -- the new family
  let T := Σ b : B, Fin (d b)
  let N := Fintype.card T
  let e : T ≃ Fin N := Fintype.equivFin T
  let ν' : Fin N → ℂ := fun j => (e.symm j).1.1 + (o (e.symm j).1 (e.symm j).2 : ℂ)
  let U' : Fin N → PowerSeries ℂ := fun j => U (e.symm j).1 (e.symm j).2
  have hinjT : ∀ t t' : T, t.1.1 + (o t.1 t.2 : ℂ) = t'.1.1 + o t'.1 t'.2 → t = t' := by
    rintro ⟨b, l⟩ ⟨b', l'⟩ h
    simp only at h
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp b.2
    obtain ⟨i', -, hi'⟩ := Finset.mem_image.mp b'.2
    have hoo : o b l = o b' l' := hsep i i' _ _ (by rw [hi, hi']; exact h)
    have hbb : b = b' := by
      apply Subtype.ext
      rw [hoo] at h
      exact add_right_cancel h
    subst hbb
    have hl := ho b hoo
    subst hl
    rfl
  have hinj : Function.Injective ν' := by
    intro j j' h
    exact e.symm.injective (hinjT _ _ h)
  -- spans of functions on the upper half-plane
  let Φ : Fin n → (imGT 0 → ℂ) := fun i => evH (lam i) (G i)
  let φ : Fin N → (imGT 0 → ℂ) := fun j => evH (ν' j) (U' j)
  have hΦH : ∀ (b : B) (i : {i : Fin n // μ i = b.1}), evH b.1 (H b i) = Φ i.1 := by
    rintro b ⟨i, hi⟩
    simp only [H, Φ]
    rw [← evH_add_nat, ← hi, hlam]
  have hφT : ∀ t : T, φ (e t) = evH (t.1.1 + o t.1 t.2) (U t.1 t.2) := by
    intro t
    dsimp only [φ, ν', U']
    rw [Equiv.symm_apply_apply]
  have hφΦ : ∀ j, φ j ∈ Submodule.span ℂ (Set.range Φ) := by
    intro j
    have h1 := hsp1 (e.symm j).1 (e.symm j).2
    refine Submodule.span_le.mpr ?_ h1
    rintro _ ⟨i, rfl⟩
    beta_reduce
    rw [hΦH]
    exact Submodule.subset_span ⟨i.1, rfl⟩
  have hΦφ : ∀ i, Φ i ∈ Submodule.span ℂ (Set.range φ) := by
    intro i
    let b : B := ⟨μ i, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
    have h1 := hsp2 b ⟨i, rfl⟩
    rw [hΦH] at h1
    refine Submodule.span_le.mpr ?_ h1
    rintro _ ⟨l, rfl⟩
    exact Submodule.subset_span ⟨e ⟨b, l⟩, hφT ⟨b, l⟩⟩
  -- the `S`-transformation as a linear map on functions
  let g : imGT 0 → imGT 0 := fun z => ⟨-1 / (z : ℂ), neg_one_div_mem_imGT z.2⟩
  let L := LinearMap.funLeft ℂ ℂ g
  have hLΦ : ∀ i, L (Φ i) ∈ Submodule.span ℂ (Set.range Φ) := by
    intro i
    have : L (Φ i) = ∑ j, S i j • Φ j := by
      funext z
      simp only [L, g, Φ, LinearMap.funLeft_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, evH]
      exact hS i z z.2
    rw [this]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hLφ : ∀ j, L (φ j) ∈ Submodule.span ℂ (Set.range φ) := by
    intro j
    have hmap : (Submodule.span ℂ (Set.range Φ)).map L ≤ Submodule.span ℂ (Set.range Φ) := by
      rw [Submodule.map_span_le]
      rintro _ ⟨i, rfl⟩
      exact hLΦ i
    have hΦle : Submodule.span ℂ (Set.range Φ) ≤ Submodule.span ℂ (Set.range φ) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hΦφ i
    exact hΦle (hmap (Submodule.mem_map_of_mem (hφΦ j)))
  choose S' hS' using fun j => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hLφ j)
  have hlaw : ∀ j, ∀ z ∈ imGT 0,
      famF ν' U' j (-1 / z) = ∑ j', Matrix.of S' j j' * famF ν' U' j' z := by
    intro j z hz
    have h1 := congrFun (hS' j) ⟨z, hz⟩
    simp only [L, g, φ, LinearMap.funLeft_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, evH] at h1
    simp only [famF, Matrix.of_apply]
    exact h1.symm
  have hrat := hcore N ν' U' (fun j => hU _ _) (fun j => hUR _ _) hinj (fun j => hU0 _ _)
    (Matrix.of S') hlaw
  -- back to the original exponents
  intro i
  let b : B := ⟨μ i, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
  have hHne : H b ⟨i, rfl⟩ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (h0 i)
  let l : Fin (d b) := ⟨0, hpos b ⟨i, rfl⟩ hHne⟩
  obtain ⟨q, hq⟩ := hrat (e ⟨b, l⟩)
  have hν : ν' (e ⟨b, l⟩) = μ i + o b l := by
    dsimp only [ν']
    rw [Equiv.symm_apply_apply]
  refine ⟨q - (o b l : ℚ) + (k i : ℚ), ?_⟩
  push_cast
  rw [hq, hν, ← hlam i]
  ring

/-! ## The reduction -/

/-- **`AndersonMooreInput` from its normalized core.** -/
theorem andersonMooreInput_of_core (h : AMCore) : AndersonMooreInput := by
  intro n lam a f S ha hsum hSlaw
  let G : Fin n → PowerSeries ℂ := fun i => PowerSeries.mk fun m => (a i m : ℂ)
  have hf : ∀ i (τ : UpperHalfPlane), f i τ = amEval (lam i) (G i) τ := fun i τ =>
    eq_amEval_of_hasSum (hsum i τ)
  refine rat_of_core h lam G (fun i => mem_subexpPS_of_hasSum (hsum i))
    (fun i => ratCoeffs_mk_nat _) ?_ S ?_
  · intro i hG0
    apply ha i
    have := congrArg (PowerSeries.coeff 0) hG0
    simpa [G] using this
  · intro i z hz
    let τ : UpperHalfPlane := ⟨z, hz⟩
    have h1 := hSlaw i τ
    simp only [hf] at h1
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk] at h1
    have hτ : (τ : ℂ) = z := rfl
    rw [hτ, inv_neg, ← one_div, ← neg_div] at h1
    exact h1

end VOA.Huang.AndersonMoore
