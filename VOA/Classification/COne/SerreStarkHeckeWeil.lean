/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkHeckeGauss

/-!
# Serre–Stark S3-1c: the coset theta functions in the Weil representation of level `p²`

With `P = p²`, every `θ ∘ A_i` (`A_i` a coset matrix of `T(p²)`) and `θ` itself are finite
combinations of the Weil theta functions `Θ_{P,μ}(τ) = Σ_{m ≡ μ (2P)} q^{m²/4P}`:

* `θ((τ+b)/p²) = Σ_μ [2 ∣ μ] e(b (μ/2)²/p²) Θ_{P,μ}`,
* `θ(τ + h/p) = Σ_μ [2p ∣ μ] e(h (μ/2p)²/p) Θ_{P,μ}`,
* `θ(p²τ) = Θ_{P,0}`, `θ(τ) = Σ_μ [2p ∣ μ] Θ_{P,μ}`

(`thetaRef_cosetMat_eq`, `thetaRef_eq_thvec`). The Weil vectors are `cvec p i`, `thvec p`.
-/

open Complex
open scoped MatrixGroups

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

open WeilGalois

/-- The Weil vectors (as `2p²`-periodic functions on `ℤ`) of the coset theta functions. -/
def cvec (p : ℕ) : HIdx p → ℤ → ℂ
  | .inl b, μ => if (2 : ℤ) ∣ μ then E (p ^ 2) (((b : ℕ) : ℤ) * (μ / 2) ^ 2) else 0
  | .inr (.inl h), μ =>
    if (2 * p : ℤ) ∣ μ then E p (((h : ℕ) : ℤ) * (μ / (2 * p)) ^ 2) else 0
  | .inr (.inr _), μ => if (2 * (p : ℤ) ^ 2) ∣ μ then 1 else 0

/-- The Weil vector of `θ` at level `p²`. -/
def thvec (p : ℕ) (μ : ℤ) : ℂ := if (2 * p : ℤ) ∣ μ then 1 else 0

/-! ## Splitting a theta series by residues modulo `2P` -/

theorem sum_fin_ite_modEq {M : ℕ} (hM : 0 < M) (c : ℤ → ℂ) (hc : ∀ x, c (x + M) = c x)
    (n : ℤ) (x : ℂ) :
    ∑ μ : Fin M, c ((μ : ℕ) : ℤ) * (if n ≡ ((μ : ℕ) : ℤ) [ZMOD M] then x else 0) = c n * x := by
  rw [Finset.sum_eq_single (idxc hM n)]
  · rw [if_pos (idxc_modEq hM n).symm, periodic_congr' hc (idxc_modEq hM n)]
  · intro μ _ hμ
    rw [if_neg, mul_zero]
    intro h
    apply hμ
    exact fin_eq_of_modEq (h.symm.trans (idxc_modEq hM n).symm)
  · simp

/-- `Σ_m c(m) q^{m²/4P} = Σ_{μ mod 2P} c(μ) Θ_{P,μ}` for `2P`-periodic `c`. -/
theorem hasSum_weil_split {P : ℕ} (hP : 0 < P) (c : ℤ → ℂ)
    (hc : ∀ x, c (x + (2 * P : ℕ)) = c x) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun m : ℤ => c m * thetaExp (1 / (4 * (P : ℝ))) τ m)
      (∑ μ : Fin (2 * P), c ((μ : ℕ) : ℤ) * weilTheta P ((μ : ℕ) : ℤ) τ) := by
  have h2P : ((2 * P : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (by omega : 2 * P ≠ 0)
  have ht : (0 : ℝ) < 1 / (4 * (P : ℝ)) := by
    have : (0 : ℝ) < P := Nat.cast_pos.2 hP
    positivity
  have H : HasSum (fun n : ℤ => ∑ μ : Fin (2 * P), c ((μ : ℕ) : ℤ) *
      (if n ≡ ((μ : ℕ) : ℤ) [ZMOD ((2 * P : ℕ) : ℤ)] then
        thetaExp (1 / (4 * (P : ℝ))) τ n else 0))
      (∑ μ : Fin (2 * P), c ((μ : ℕ) : ℤ) * weilTheta P ((μ : ℕ) : ℤ) τ) :=
    hasSum_sum fun μ _ => (hasSum_rankOneTheta_ite ((μ : ℕ) : ℤ) h2P ht hτ).mul_left _
  refine H.congr_fun fun n => ?_
  exact (sum_fin_ite_modEq (by omega) c hc n _).symm

/-- The defining series of `θ`. -/
theorem hasSum_thetaRef {w : ℂ} (hw : 0 < w.im) :
    HasSum (fun m : ℤ => cexp (2 * Real.pi * I * (m : ℂ) ^ 2 * w)) (thetaRef w) := by
  have hs := summable_rankOneThetaTerm 0 (r := 1) one_ne_zero (t := 1) one_pos hw
  have h := hs.hasSum
  refine (h.congr_fun fun m => ?_)
  simp [rankOneThetaTerm]

/-- Re-indexing a series along `m ↦ s m`. -/
theorem hasSum_mul_reindex {s : ℤ} (hs : s ≠ 0) {f : ℤ → ℂ} (hf : ∀ x, ¬ s ∣ x → f x = 0)
    {a : ℂ} (h : HasSum (fun m => f (s * m)) a) : HasSum f a := by
  have hinj : Function.Injective (fun m : ℤ => s * m) := fun x y hxy =>
    mul_left_cancel₀ hs hxy
  refine (hinj.hasSum_iff ?_).1 h
  rintro x hx
  apply hf
  rintro ⟨k, rfl⟩
  exact hx ⟨k, rfl⟩

theorem thetaExp_eq (P : ℕ) (hP : 0 < P) (τ : ℂ) (m : ℤ) :
    thetaExp (1 / (4 * (P : ℝ))) τ m = cexp (2 * Real.pi * I * (m : ℂ) ^ 2 * τ / (4 * P)) := by
  have hP' : (P : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hP.ne'
  unfold thetaExp
  congr 1
  push_cast
  field_simp

section Decomp

variable {p : ℕ} (hp : p.Prime)

include hp in
theorem cvec_periodic (i : HIdx p) (x : ℤ) :
    cvec p i (x + ((2 * p ^ 2 : ℕ) : ℤ)) = cvec p i x := by
  have hp0 := hp.pos
  rcases i with b | h | u
  · simp only [cvec]
    have hd : ((2 : ℤ) ∣ x + ((2 * p ^ 2 : ℕ) : ℤ)) ↔ (2 : ℤ) ∣ x := by
      push_cast; exact (dvd_add_left ⟨(p : ℤ) ^ 2, by ring⟩)
    by_cases h2 : (2 : ℤ) ∣ x
    · rw [if_pos (hd.2 h2), if_pos h2]
      obtain ⟨k, rfl⟩ := h2
      push_cast
      rw [show 2 * k + 2 * (p : ℤ) ^ 2 = 2 * (k + (p : ℤ) ^ 2) by ring,
        Int.mul_ediv_cancel_left _ two_ne_zero, Int.mul_ediv_cancel_left _ two_ne_zero]
      rw [show ((b : ℕ) : ℤ) * (k + (p : ℤ) ^ 2) ^ 2 = ((b : ℕ) : ℤ) * k ^ 2 +
        ((p ^ 2 : ℕ) : ℤ) * (((b : ℕ) : ℤ) * (2 * k + (p : ℤ) ^ 2)) by push_cast; ring]
      exact E_period (pow_pos hp0 2) _ _
    · rw [if_neg (fun h => h2 (hd.1 h)), if_neg h2]
  · simp only [cvec]
    have hd : ((2 * p : ℤ) ∣ x + ((2 * p ^ 2 : ℕ) : ℤ)) ↔ (2 * p : ℤ) ∣ x := by
      push_cast; exact (dvd_add_left ⟨(p : ℤ), by ring⟩)
    by_cases h2 : (2 * p : ℤ) ∣ x
    · rw [if_pos (hd.2 h2), if_pos h2]
      obtain ⟨k, rfl⟩ := h2
      push_cast
      rw [show 2 * (p : ℤ) * k + 2 * (p : ℤ) ^ 2 = 2 * p * (k + p) by ring]
      by_cases hpz : (p : ℤ) = 0
      · simp [hpz]
      have h2p : (2 * (p : ℤ)) ≠ 0 := mul_ne_zero two_ne_zero hpz
      rw [Int.mul_ediv_cancel_left _ h2p, Int.mul_ediv_cancel_left _ h2p,
        show ((h : ℕ) : ℤ) * (k + p) ^ 2 = ((h : ℕ) : ℤ) * k ^ 2 +
          (p : ℕ) * (((h : ℕ) : ℤ) * (2 * k + p)) by ring]
      exact E_period (Nat.pos_of_ne_zero (by exact_mod_cast hpz)) _ _
    · rw [if_neg (fun h => h2 (hd.1 h)), if_neg h2]
  · simp only [cvec]
    have hd : ((2 * (p : ℤ) ^ 2) ∣ x + ((2 * p ^ 2 : ℕ) : ℤ)) ↔ (2 * (p : ℤ) ^ 2) ∣ x := by
      push_cast; exact (dvd_add_left (dvd_refl _))
    by_cases h2 : (2 * (p : ℤ) ^ 2) ∣ x
    · rw [if_pos (hd.2 h2), if_pos h2]
    · rw [if_neg (fun h => h2 (hd.1 h)), if_neg h2]

theorem thvec_periodic (x : ℤ) : thvec p (x + ((2 * p ^ 2 : ℕ) : ℤ)) = thvec p x := by
  simp only [thvec]
  have hd : ((2 * p : ℤ) ∣ x + ((2 * p ^ 2 : ℕ) : ℤ)) ↔ (2 * p : ℤ) ∣ x := by
    push_cast; exact (dvd_add_left ⟨(p : ℤ), by ring⟩)
  by_cases h2 : (2 * p : ℤ) ∣ x
  · rw [if_pos (hd.2 h2), if_pos h2]
  · rw [if_neg (fun h => h2 (hd.1 h)), if_neg h2]

theorem E_eq (c : ℕ) (t : ℤ) : E c t = cexp (2 * Real.pi * I * (t : ℂ) / c) := rfl

include hp in
/-- The coset theta functions as series in `q^{1/4P}`. -/
theorem hasSum_coset (i : HIdx p) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun m : ℤ => cvec p i m * thetaExp (1 / (4 * ((p ^ 2 : ℕ) : ℝ))) τ m)
      (thetaRef (mobZ (cosetMat p i) τ)) := by
  have hp0 := hp.pos
  have hP : 0 < p ^ 2 := pow_pos hp0 2
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp0.ne'
  have hw := im_mobZ_cosetMat hp0 i hτ
  have hθ := hasSum_thetaRef hw
  rcases i with b | h | u
  · refine hasSum_mul_reindex (s := 2) two_ne_zero ?_ ?_
    · intro x hx; simp [cvec, hx]
    · refine hθ.congr_fun fun m => ?_
      simp only [cvec, dvd_mul_right, if_true, Int.mul_ediv_cancel_left _ two_ne_zero]
      rw [thetaExp_eq _ hP, E_eq, ← Complex.exp_add, mobZ_cosetMat_inl]
      congr 1
      push_cast
      field_simp
      ring
  · refine hasSum_mul_reindex (s := 2 * p) (by positivity) ?_ ?_
    · intro x hx; simp [cvec, hx]
    · refine hθ.congr_fun fun m => ?_
      have h2p : (2 * (p : ℤ)) ≠ 0 := by positivity
      simp only [cvec, dvd_mul_right, if_true, Int.mul_ediv_cancel_left _ h2p]
      rw [thetaExp_eq _ hP, E_eq, ← Complex.exp_add, mobZ_cosetMat_inr_inl hp0]
      congr 1
      push_cast
      field_simp
      ring
  · refine hasSum_mul_reindex (s := 2 * (p : ℤ) ^ 2) (by positivity) ?_ ?_
    · intro x hx; simp [cvec, hx]
    · refine hθ.congr_fun fun m => ?_
      simp only [cvec, dvd_mul_right, if_true, one_mul]
      rw [thetaExp_eq _ hP, mobZ_cosetMat_inr_inr]
      congr 1
      push_cast
      field_simp
      ring

include hp in
theorem hasSum_theta_thvec {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun m : ℤ => thvec p m * thetaExp (1 / (4 * ((p ^ 2 : ℕ) : ℝ))) τ m) (thetaRef τ) := by
  have hp0 := hp.pos
  have hP : 0 < p ^ 2 := pow_pos hp0 2
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp0.ne'
  refine hasSum_mul_reindex (s := 2 * p) (by positivity) ?_ ?_
  · intro x hx; simp [thvec, hx]
  · refine (hasSum_thetaRef hτ).congr_fun fun m => ?_
    simp only [thvec, dvd_mul_right, if_true, one_mul]
    rw [thetaExp_eq _ hP]
    congr 1
    push_cast
    field_simp
    ring

include hp in
/-- **Decomposition**: `θ ∘ A_i = Σ_μ cvec_i(μ) Θ_{p²,μ}`. -/
theorem thetaRef_cosetMat_eq (i : HIdx p) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaRef (mobZ (cosetMat p i) τ) =
      ∑ μ : Fin (2 * p ^ 2), cvec p i ((μ : ℕ) : ℤ) * weilTheta (p ^ 2) ((μ : ℕ) : ℤ) τ :=
  (hasSum_coset hp i hτ).unique
    (hasSum_weil_split (pow_pos hp.pos 2) (cvec p i) (cvec_periodic hp i) hτ)

include hp in
theorem thetaRef_eq_thvec {τ : ℂ} (hτ : 0 < τ.im) :
    thetaRef τ = ∑ μ : Fin (2 * p ^ 2), thvec p ((μ : ℕ) : ℤ) * weilTheta (p ^ 2) ((μ : ℕ) : ℤ) τ :=
  (hasSum_theta_thvec hp hτ).unique
    (hasSum_weil_split (pow_pos hp.pos 2) (thvec p) thvec_periodic hτ)

end Decomp


/-! ## Finite Fourier transforms of the Weil vectors -/

section Fourier

variable {p : ℕ} (hp : p.Prime)

/-- Unnormalised finite Fourier transform at level `p²`. -/
def fhat (p : ℕ) (v : ℤ → ℂ) (k : ℤ) : ℂ :=
  ∑ μ : Fin (2 * p ^ 2), v ((μ : ℕ) : ℤ) * E (2 * p ^ 2) (k * ((μ : ℕ) : ℤ))

theorem sum_split_mult {M s n : ℕ} (hM : M = s * n) (hs : 0 < s) (hn : 0 < n) (F : ℤ → ℂ)
    (hF : ∀ x, F (x + M) = F x) (hF0 : ∀ x, ¬ (s : ℤ) ∣ x → F x = 0) :
    ∑ μ : Fin M, F ((μ : ℕ) : ℤ) = ∑ z : Fin n, F (s * ((z : ℕ) : ℤ)) := by
  subst hM
  rw [sum_split rfl (Nat.mul_pos hs hn) F hF, Finset.sum_eq_single ⟨0, hs⟩]
  · simp
  · intro y _ hy
    refine Finset.sum_eq_zero fun z _ => hF0 _ ?_
    intro hd
    have h1 : (s : ℤ) ∣ ((y : ℕ) : ℤ) := (dvd_add_left (dvd_mul_right _ _)).1 hd
    have h2 : ((y : ℕ) : ℤ) = 0 :=
      Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h1 (by simp)
    exact hy (Fin.ext (by exact_mod_cast h2))
  · simp

theorem E_lin_periodic {M : ℕ} (hM : 0 < M) (k x : ℤ) :
    E M (k * (x + M)) = E M (k * x) := by
  rw [show k * (x + M) = k * x + M * k by ring, E_period hM]

include hp in
theorem fhat_per (v : ℤ → ℂ) (hv : ∀ x, v (x + ((2 * p ^ 2 : ℕ) : ℤ)) = v x) (k x : ℤ) :
    v (x + ((2 * p ^ 2 : ℕ) : ℤ)) * E (2 * p ^ 2) (k * (x + ((2 * p ^ 2 : ℕ) : ℤ))) =
      v x * E (2 * p ^ 2) (k * x) := by
  rw [hv, E_lin_periodic (pow_pos hp.pos 2 |>.trans_le' le_rfl |> fun _ => by positivity)]

include hp in
theorem fhat_inl (b : Fin (p ^ 2)) (k : ℤ) :
    fhat p (cvec p (.inl b)) k = gsl (p ^ 2) ((b : ℕ) : ℤ) k := by
  have hP : 0 < p ^ 2 := pow_pos hp.pos 2
  have hs := sum_split_mult (M := 2 * p ^ 2) (s := 2) (n := p ^ 2)
    (F := fun x => cvec p (.inl b) x * E (2 * p ^ 2) (k * x)) rfl two_pos hP
    (fhat_per hp _ (cvec_periodic hp _) k)
    (fun x hx => by simp only [cvec]; push_cast at hx ⊢; simp [hx])
  simp only at hs
  unfold fhat gsl
  rw [hs]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [cvec]
  push_cast
  simp only [dvd_mul_right, if_true, Int.mul_ediv_cancel_left _ two_ne_zero]
  have e := E_mul_left (r := p ^ 2) (s := 2) two_pos (k * ((z : ℕ) : ℤ))
  push_cast at e
  rw [show k * (2 * ((z : ℕ) : ℤ)) = 2 * (k * ((z : ℕ) : ℤ)) by ring,
    show 2 * p ^ 2 = p ^ 2 * 2 by ring, e, ← E_add]

include hp in
theorem fhat_inr_inl (h : Fin p) (k : ℤ) :
    fhat p (cvec p (.inr (.inl h))) k = gsl p ((h : ℕ) : ℤ) k := by
  have hp0 := hp.pos
  have h2p : (2 * (p : ℤ)) ≠ 0 := by positivity
  have hs := sum_split_mult (M := 2 * p ^ 2) (s := 2 * p) (n := p)
    (F := fun x => cvec p (.inr (.inl h)) x * E (2 * p ^ 2) (k * x)) (by ring) (by positivity)
    hp0 (fhat_per hp _ (cvec_periodic hp _) k)
    (fun x hx => by simp only [cvec]; push_cast at hx ⊢; simp [hx])
  simp only at hs
  unfold fhat gsl
  rw [hs]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [cvec]
  push_cast
  simp only [dvd_mul_right, if_true, Int.mul_ediv_cancel_left _ h2p]
  rw [show k * (2 * (p : ℤ) * ((z : ℕ) : ℤ)) = ((2 * p : ℕ) : ℤ) * (k * ((z : ℕ) : ℤ)) by
    push_cast; ring, show 2 * p ^ 2 = p * (2 * p) by ring, E_mul_left (by positivity),
    ← E_add]

include hp in
theorem fhat_inr_inr (u : Unit) (k : ℤ) : fhat p (cvec p (.inr (.inr u))) k = 1 := by
  have hp0 := hp.pos
  have hs := sum_split_mult (M := 2 * p ^ 2) (s := 2 * p ^ 2) (n := 1)
    (F := fun x => cvec p (.inr (.inr u)) x * E (2 * p ^ 2) (k * x)) (by ring) (by positivity)
    one_pos (fhat_per hp _ (cvec_periodic hp _) k)
    (fun x hx => by simp only [cvec]; push_cast at hx ⊢; simp [hx])
  simp only at hs
  unfold fhat
  rw [hs]
  simp [cvec, E_zero]

include hp in
theorem fhat_thvec (k : ℤ) : fhat p (thvec p) k = if (p : ℤ) ∣ k then (p : ℂ) else 0 := by
  have hp0 := hp.pos
  have hs := sum_split_mult (M := 2 * p ^ 2) (s := 2 * p) (n := p)
    (F := fun x => thvec p x * E (2 * p ^ 2) (k * x)) (by ring) (by positivity)
    hp0 (fhat_per hp _ thvec_periodic k)
    (fun x hx => by simp only [thvec]; push_cast at hx ⊢; simp [hx])
  simp only at hs
  unfold fhat
  rw [hs, ← sum_E_lin hp0]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [thvec]
  push_cast
  simp only [dvd_mul_right, if_true, one_mul]
  rw [show k * (2 * (p : ℤ) * ((z : ℕ) : ℤ)) = ((2 * p : ℕ) : ℤ) * (k * ((z : ℕ) : ℤ)) by
    push_cast; ring, show 2 * p ^ 2 = p * (2 * p) by ring, E_mul_left (by positivity)]

end Fourier


/-! ## Weights and the `L^N` relation on Fourier transforms -/

section Weights

/-- The Hecke weights `ω = (p⁻², (h/p)/(p g(p,1)), p⁻¹)`. -/
def hw (p : ℕ) [Fact p.Prime] : HIdx p → ℂ
  | .inl _ => 1 / (p : ℂ) ^ 2
  | .inr (.inl h) => (legendreSym p ((h : ℕ) : ℤ) : ℂ) / ((p : ℂ) * gs p 1)
  | .inr (.inr _) => 1 / (p : ℂ)

/-- `D(k) = e(−K k²/p²)` (the diagonal of the Weil matrix of `T^{−4K}`). -/
def dL (p : ℕ) (K k : ℤ) : ℂ := E (p ^ 2) (-(K * k ^ 2))

theorem zmod_of_modEq {m : ℕ} {a b : ℤ} (h : a ≡ b [ZMOD m]) : (a : ZMod m) = b :=
  (ZMod.intCast_eq_intCast_iff _ _ _).2 h

theorem modEq_of_zmod' {m : ℕ} {a b : ℤ} (h : (a : ZMod m) = b) : a ≡ b [ZMOD m] :=
  (ZMod.intCast_eq_intCast_iff _ _ _).1 h

theorem isUnit_of_coprime {m : ℕ} {u : ℤ} (h : IsCoprime u m) : IsUnit (u : ZMod m) := by
  have := zmod_of_modEq (binv_spec h)
  push_cast at this
  exact IsUnit.of_mul_eq_one _ this

theorem E_eq_of_zmod {m : ℕ} (hm : 0 < m) {x y : ℤ} (h : (x : ZMod m) = y) : E m x = E m y :=
  E_congr hm (modEq_of_zmod' h)

variable {p : ℕ} (hp : p.Prime)

include hp in
theorem hp2' : 0 < p ^ 2 := pow_pos hp.pos 2

include hp in
theorem not_dvd_four_mul (hp2 : p ≠ 2) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) : ¬ (p : ℤ) ∣ 4 * a := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  intro h
  rcases hpp.dvd_or_dvd h with h | h
  · have : (p : ℤ) ∣ 2 ^ 2 := by norm_num; exact h
    have h2 := hpp.dvd_of_dvd_pow this
    have : p ∣ 2 := by exact_mod_cast h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  · exact ha h

include hp in
/-- `4aβ ≡ 1 (mod p^e)` has a solution for `p ∤ a`, `p` odd. -/
theorem exists_inv4 (hp2 : p ≠ 2) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) (e : ℕ) :
    ∃ β : ℤ, ((4 * a * β : ℤ) : ZMod (p ^ e)) = 1 := by
  have hc : IsCoprime (4 * a) ((p ^ e : ℕ) : ℤ) := by
    push_cast; exact (isCoprime_of_not_dvd hp (not_dvd_four_mul hp hp2 ha)).pow_right
  refine ⟨binv (p ^ e) (4 * a), ?_⟩
  have := zmod_of_modEq (binv_spec hc)
  push_cast at this ⊢
  linear_combination this

theorem E_sq_mul_p (hp0 : 0 < p) (β k : ℤ) :
    E (p ^ 2) (-((p * β) * k ^ 2)) = E p (-(β * k ^ 2)) := by
  rw [show p ^ 2 = p * p by ring, show -((p * β) * k ^ 2) = (p : ℤ) * (-(β * k ^ 2)) by ring,
    E_mul_left hp0]

include hp in
theorem gsl_sq_unit (hp2 : p ≠ 2) {a β : ℤ} (ha : ¬ (p : ℤ) ∣ a)
    (hβ : ((4 * a * β : ℤ) : ZMod (p ^ 2)) = 1) (k : ℤ) :
    gsl (p ^ 2) a k = E (p ^ 2) (-(β * k ^ 2)) * p := by
  have hP : 0 < p ^ 2 := pow_pos hp.pos 2
  rw [gsl_complete hP (modEq_of_zmod' (by push_cast at hβ ⊢; exact hβ)) k, gs_p_sq hp hp2 ha]

theorem dL_of_dvd {p : ℕ} (hp0 : 0 < p) (K : ℤ) {k : ℤ} (hk : (p : ℤ) ∣ k) : dL p K k = 1 := by
  obtain ⟨k₁, rfl⟩ := hk
  unfold dL
  rw [show -(K * ((p : ℤ) * k₁) ^ 2) = ((p ^ 2 : ℕ) : ℤ) * (-(K * k₁ ^ 2)) by push_cast; ring]
  exact E_mul_self (pow_pos hp0 2) _

theorem E_mul_E (m : ℕ) (x y : ℤ) : E m x * E m y = E m (x + y) := (E_add m x y).symm

/-! ### The case `A_b`, `p ∤ 1 + N b` -/

include hp in
theorem dRel_inl_unit [Fact p.Prime] (hp2 : p ≠ 2) {N : ℕ} {K : ℤ} (hNK : (N : ℤ) = 4 * K)
    (b : Fin (p ^ 2)) (h1 : ¬ (p : ℤ) ∣ 1 + N * ((b : ℕ) : ℤ)) (k : ℤ) :
    dL p K k * gsl (p ^ 2) ((b : ℕ) : ℤ) k =
      gsl (p ^ 2) (((rep (p ^ 2) (hp2' hp) (((b : ℕ) : ℤ) * binv (p ^ 2)
        (1 + N * ((b : ℕ) : ℤ))) : ℕ) : ℤ)) k := by
  have hp0 := hp.pos
  have hP : 0 < p ^ 2 := pow_pos hp0 2
  have hcop := isCoprime_sq_of_not_dvd hp h1
  have hU : IsUnit (((1 + N * ((b : ℕ) : ℤ) : ℤ)) : ZMod (p ^ 2)) := isUnit_of_coprime hcop
  set u : ℤ := 1 + N * ((b : ℕ) : ℤ) with hu
  have hb'u : ((((rep (p ^ 2) (hp2' hp) (((b : ℕ) : ℤ) * binv (p ^ 2) u)) : ℕ) : ℤ) : ZMod (p ^ 2))
      * (u : ZMod (p ^ 2)) = (((b : ℕ) : ℤ) : ZMod (p ^ 2)) := by
    have e1 := zmod_of_modEq (rep_modEq (hp2' hp) (((b : ℕ) : ℤ) * binv (p ^ 2) u))
    have e2 := zmod_of_modEq (binv_spec hcop)
    push_cast at e1 e2 ⊢
    rw [e1]
    linear_combination (((b : ℕ) : ZMod (p ^ 2))) * e2
  set b' : ℤ := (((rep (p ^ 2) (hp2' hp) (((b : ℕ) : ℤ) * binv (p ^ 2) u)) : ℕ) : ℤ) with hb'
  by_cases hb : (p : ℤ) ∣ ((b : ℕ) : ℤ)
  · -- `b' = b`
    have hpz : ((p : ℕ) : ZMod (p ^ 2)) ^ 2 = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    obtain ⟨b₁, hb₁⟩ := hb
    have hb₁' : ((b : ℕ) : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) * (b₁ : ZMod (p ^ 2)) := by
      have := congrArg (Int.cast : ℤ → ZMod (p ^ 2)) hb₁; push_cast at this; exact this
    have hbb : (b' : ZMod (p ^ 2)) = (((b : ℕ) : ℤ) : ZMod (p ^ 2)) := by
      apply hU.mul_left_cancel
      rw [mul_comm, hb'u, hu]
      push_cast
      rw [hb₁']
      linear_combination (-(N : ZMod (p ^ 2)) * (b₁ : ZMod (p ^ 2)) ^ 2) * hpz
    have hbe : b' = ((b : ℕ) : ℤ) := by
      have := modEq_of_zmod' hbb
      have h1' : (b' : ℤ) % ((p ^ 2 : ℕ) : ℤ) = b' := Int.emod_eq_of_lt (by positivity) (by
        rw [hb']; push_cast; exact_mod_cast (rep (p ^ 2) (hp2' hp) _).2)
      have h2' : ((b : ℕ) : ℤ) % ((p ^ 2 : ℕ) : ℤ) = (b : ℕ) := Int.emod_eq_of_lt (by positivity)
        (by exact_mod_cast b.2)
      unfold Int.ModEq at this
      rw [h1', h2'] at this
      exact this
    rw [hbe, hb₁, gsl_p_mul hp0]
    split_ifs with hk
    · rw [dL_of_dvd hp0 K hk, one_mul]
    · rw [mul_zero]
  · obtain ⟨β, hβ⟩ := exists_inv4 hp hp2 hb 2
    have hb'p : ¬ (p : ℤ) ∣ b' := by
      intro hd
      apply hb
      obtain ⟨c, hc⟩ := hd
      have : (((b : ℕ) : ℤ) : ZMod (p ^ 2)) = ((p * (c * u) : ℤ) : ZMod (p ^ 2)) := by
        rw [← hb'u, hc]; push_cast; ring
      have := (dvd_pow_self (p : ℤ) two_ne_zero).trans (Int.ModEq.dvd (modEq_of_zmod' this))
      have h3 : (p : ℤ) ∣ p * (c * u) := dvd_mul_right _ _
      have := dvd_sub h3 this
      simpa using this
    have hβ' : ((4 * b' * (β + K) : ℤ) : ZMod (p ^ 2)) = 1 := by
      apply hU.mul_left_cancel
      push_cast at hβ ⊢
      rw [hu]; push_cast
      have e := hb'u
      rw [hu] at e; push_cast at e
      have hN : ((N : ℤ) : ZMod (p ^ 2)) = 4 * (K : ZMod (p ^ 2)) := by rw [hNK]; push_cast; ring
      push_cast at hN
      linear_combination (4 * ((β : ZMod (p ^ 2)) + K)) * e + hβ -
        (((b : ℕ) : ZMod (p ^ 2))) * hN
    rw [gsl_sq_unit hp hp2 hb hβ, gsl_sq_unit hp hp2 hb'p hβ', dL, ← mul_assoc, E_mul_E]
    congr 2
    ring

theorem zmod_eq_zero_of_dvd {m : ℕ} {x : ℤ} (h : (m : ℤ) ∣ x) : (x : ZMod m) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd x m).2 h

theorem dvd_of_zmod_eq_zero {m : ℕ} {x : ℤ} (h : (x : ZMod m) = 0) : (m : ℤ) ∣ x :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd x m).1 h

include hp in
theorem isUnit_zmod_of_not_dvd {e : ℕ} {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) : IsUnit (a : ZMod (p ^ e)) :=
  isUnit_of_coprime (by push_cast; exact (isCoprime_of_not_dvd hp ha).pow_right)

include hp in
theorem isUnit_zmod_p_of_not_dvd {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) : IsUnit (a : ZMod p) :=
  isUnit_of_coprime (isCoprime_of_not_dvd hp ha)

/-! ### The case `A_b`, `p ∥ 1 + N b` -/

include hp in
theorem dRel_inl_p [Fact p.Prime] (hp2 : p ≠ 2) {N : ℕ} {K : ℤ} (hNK : (N : ℤ) = 4 * K)
    (b : Fin (p ^ 2)) (h1 : (p : ℤ) ∣ 1 + N * ((b : ℕ) : ℤ))
    (h2 : ¬ (p : ℤ) ^ 2 ∣ 1 + N * ((b : ℕ) : ℤ)) (k : ℤ) :
    1 / (p : ℂ) ^ 2 * dL p K k * gsl (p ^ 2) ((b : ℕ) : ℤ) k =
      hw p (.inr (.inl (rep p (hp0 hp) (((b : ℕ) : ℤ) *
        binv p ((1 + N * ((b : ℕ) : ℤ)) / p))))) *
      gsl p (((rep p (hp0 hp) (((b : ℕ) : ℤ) * binv p ((1 + N * ((b : ℕ) : ℤ)) / p))) : ℕ) : ℤ)
        k := by
  have hp0' := hp.pos
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp0'.ne'
  have hG := gs_p_one_ne_zero hp hp2
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  set u : ℤ := 1 + N * ((b : ℕ) : ℤ) with hu
  have hb : ¬ (p : ℤ) ∣ ((b : ℕ) : ℤ) := by
    intro hd
    have : (p : ℤ) ∣ u - N * ((b : ℕ) : ℤ) := dvd_sub h1 (dvd_mul_of_dvd_right hd _)
    rw [hu, add_sub_cancel_right] at this
    exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
  have hwu := Int.ediv_mul_cancel h1
  set w : ℤ := u / p with hw'
  have hwp : ¬ (p : ℤ) ∣ w := by
    rintro ⟨c, hc⟩; apply h2; exact ⟨c, by rw [← hwu, hc]; ring⟩
  set hh : ℤ := ((rep p (hp0 hp) (((b : ℕ) : ℤ) * binv p w) : ℕ) : ℤ) with hhh
  have hhw : (hh : ZMod p) * w = ((b : ℕ) : ℤ) := by
    have e1 := zmod_of_modEq (rep_modEq (hp0 hp) (((b : ℕ) : ℤ) * binv p w))
    have e2 := zmod_of_modEq (binv_spec (isCoprime_of_not_dvd hp hwp))
    rw [hhh]
    push_cast at e1 e2 ⊢
    rw [e1]
    linear_combination (((b : ℕ) : ZMod p)) * e2
  have hhp : ¬ (p : ℤ) ∣ hh := by
    intro hd
    apply hb
    have : (((b : ℕ) : ℤ) : ZMod p) = 0 := by rw [← hhw, zmod_eq_zero_of_dvd hd, zero_mul]
    exact dvd_of_zmod_eq_zero this
  obtain ⟨β, hβ⟩ := exists_inv4 hp hp2 hb 2
  have hβd : (p : ℤ) ^ 2 ∣ 4 * ((b : ℕ) : ℤ) * β - 1 := by
    have := dvd_of_zmod_eq_zero (m := p ^ 2) (x := 4 * ((b : ℕ) : ℤ) * β - 1)
      (by push_cast at hβ ⊢; rw [hβ]; ring)
    push_cast at this; exact this
  -- `p ∣ β + K`
  have hβK : (p : ℤ) ∣ β + K := by
    have h4b := isUnit_zmod_p_of_not_dvd hp (not_dvd_four_mul hp hp2 hb)
    apply dvd_of_zmod_eq_zero
    apply h4b.mul_left_cancel
    rw [mul_zero]
    have e1 : ((4 * ((b : ℕ) : ℤ) * β - 1 : ℤ) : ZMod p) = 0 :=
      zmod_eq_zero_of_dvd ((dvd_pow_self (p : ℤ) two_ne_zero).trans hβd)
    have e2 : (u : ZMod p) = 0 := zmod_eq_zero_of_dvd h1
    rw [hu] at e2
    have hN' : ((N : ℕ) : ZMod p) = 4 * (K : ZMod p) := by
      have := congrArg (Int.cast : ℤ → ZMod p) hNK; push_cast at this; exact this
    push_cast at e1 e2 ⊢
    linear_combination e1 + e2 - ((b : ℕ) : ZMod p) * hN'
  have hβ₁ := Int.ediv_mul_cancel hβK
  set β₁ : ℤ := (β + K) / p with hβ₁d
  -- `4 hh β₁ ≡ 1 (mod p)`
  have hkey : 4 * hh * β₁ ≡ 1 [ZMOD p] := by
    have hX : (p : ℤ) * (4 * ((b : ℕ) : ℤ) * β₁ - w) = 4 * ((b : ℕ) : ℤ) * β - 1 := by
      have : (p : ℤ) * (4 * ((b : ℕ) : ℤ) * β₁ - w) = 4 * ((b : ℕ) : ℤ) * (β₁ * p) - w * p := by
        ring
      rw [this, hβ₁, hwu, hu, hNK]; ring
    have hd : (p : ℤ) ∣ 4 * ((b : ℕ) : ℤ) * β₁ - w := by
      rw [← hX, sq] at hβd
      exact (mul_dvd_mul_iff_left (by exact_mod_cast hp.ne_zero)).1 hβd
    have e1 : ((4 * ((b : ℕ) : ℤ) * β₁ : ℤ) : ZMod p) = w :=
      (zmod_of_modEq (Int.modEq_iff_dvd.2 (by rw [← neg_sub]; exact (dvd_neg).2 hd)))
    apply modEq_of_zmod'
    apply (isUnit_zmod_p_of_not_dvd hp hwp).mul_left_cancel
    push_cast at e1 hhw ⊢
    linear_combination (4 * (β₁ : ZMod p)) * hhw + e1
  have hhz : ((hh : ℤ) : ZMod p) ≠ 0 := fun h0 => hhp (dvd_of_zmod_eq_zero h0)
  have hleg := legendreSym.sq_one p hhz
  rw [gsl_sq_unit hp hp2 hb hβ, gsl_complete hp0' hkey, gs_prime hp2 hhz]
  simp only [hw]
  rw [← hhh, dL]
  have e3 : E (p ^ 2) (-(K * k ^ 2)) * (E (p ^ 2) (-(β * k ^ 2)) * (p : ℂ)) =
      E p (-(β₁ * k ^ 2)) * p := by
    rw [← mul_assoc, E_mul_E, ← E_sq_mul_p hp0']
    congr 2
    linear_combination (k ^ 2) * hβ₁
  rw [mul_assoc, e3]
  have hl : ((legendreSym p hh : ℤ) : ℂ) ^ 2 = 1 := by exact_mod_cast hleg
  field_simp
  linear_combination (-E p (-(β₁ * k ^ 2))) * hl

/-! ### The case `A_b`, `p² ∣ 1 + N b` -/

include hp in
theorem dRel_inl_p2 (hp2 : p ≠ 2) {N : ℕ} {K : ℤ} (hNK : (N : ℤ) = 4 * K)
    (b : Fin (p ^ 2)) (h2 : (p : ℤ) ^ 2 ∣ 1 + N * ((b : ℕ) : ℤ)) (k : ℤ) :
    1 / (p : ℂ) ^ 2 * dL p K k * gsl (p ^ 2) ((b : ℕ) : ℤ) k = 1 / (p : ℂ) := by
  have hp0' := hp.pos
  have hP : 0 < p ^ 2 := pow_pos hp0' 2
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp0'.ne'
  have hb : ¬ (p : ℤ) ∣ ((b : ℕ) : ℤ) := by
    intro hd
    have h1 : (p : ℤ) ∣ 1 + N * ((b : ℕ) : ℤ) := (dvd_pow_self (p : ℤ) two_ne_zero).trans h2
    have : (p : ℤ) ∣ (1 + N * ((b : ℕ) : ℤ)) - N * ((b : ℕ) : ℤ) :=
      dvd_sub h1 (dvd_mul_of_dvd_right hd _)
    rw [add_sub_cancel_right] at this
    exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
  obtain ⟨β, hβ⟩ := exists_inv4 hp hp2 hb 2
  have hβK : ((β + K : ℤ) : ZMod (p ^ 2)) = 0 := by
    have h4b := isUnit_zmod_of_not_dvd (e := 2) hp (not_dvd_four_mul hp hp2 hb)
    apply h4b.mul_left_cancel
    rw [mul_zero]
    have e2 : ((1 + N * ((b : ℕ) : ℤ) : ℤ) : ZMod (p ^ 2)) = 0 :=
      zmod_eq_zero_of_dvd (by push_cast; exact h2)
    have hN' : ((N : ℕ) : ZMod (p ^ 2)) = 4 * (K : ZMod (p ^ 2)) := by
      have := congrArg (Int.cast : ℤ → ZMod (p ^ 2)) hNK; push_cast at this; exact this
    push_cast at hβ e2 ⊢
    linear_combination hβ + e2 - ((b : ℕ) : ZMod (p ^ 2)) * hN' - 1
  rw [gsl_sq_unit hp hp2 hb hβ, dL]
  have e3 : E (p ^ 2) (-(K * k ^ 2)) * E (p ^ 2) (-(β * k ^ 2)) = 1 := by
    rw [E_mul_E, ← E_zero (p ^ 2)]
    apply E_eq_of_zmod hP
    push_cast at hβK ⊢
    linear_combination (-(k : ZMod (p ^ 2)) ^ 2) * hβK
  rw [mul_assoc, ← mul_assoc (E _ _), e3]
  field_simp

/-! ### The case `A_h`, `h ≠ 0` -/

include hp in
theorem dRel_h [Fact p.Prime] (hp2 : p ≠ 2) {N : ℕ} {K : ℤ} (hNK : (N : ℤ) = 4 * K)
    (hpN : ¬ (p : ℤ) ∣ N) (h : Fin p) (h0 : (h : ℕ) ≠ 0) (k : ℤ) :
    hw p (.inr (.inl h)) * dL p K k * gsl p ((h : ℕ) : ℤ) k =
      1 / (p : ℂ) ^ 2 * gsl (p ^ 2) (((rep (p ^ 2) (hp2' hp) (((h : ℕ) : ℤ) *
        binv (p ^ 2) (p + ((h : ℕ) : ℤ) * N))) : ℕ) : ℤ) k := by
  have hp0' := hp.pos
  have hP : 0 < p ^ 2 := pow_pos hp0' 2
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp0'.ne'
  have hG := gs_p_one_ne_zero hp hp2
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hhp : ¬ (p : ℤ) ∣ ((h : ℕ) : ℤ) := by
    intro hd
    have : p ∣ (h : ℕ) := by exact_mod_cast hd
    exact h0 (Nat.eq_zero_of_dvd_of_lt this h.2)
  set v : ℤ := p + ((h : ℕ) : ℤ) * N with hv
  have hvp : ¬ (p : ℤ) ∣ v := by
    intro hd
    have : (p : ℤ) ∣ ((h : ℕ) : ℤ) * N := by
      have := (dvd_sub hd (dvd_refl (p : ℤ))); rw [hv] at this; simpa using this
    rcases hpp.dvd_or_dvd this with h' | h'
    · exact hhp h'
    · exact hpN h'
  have hcop := isCoprime_sq_of_not_dvd hp hvp
  set b'' : ℤ := ((rep (p ^ 2) (hp2' hp) (((h : ℕ) : ℤ) * binv (p ^ 2) v) : ℕ) : ℤ) with hb''
  have hbv : (b'' : ZMod (p ^ 2)) * v = ((h : ℕ) : ℤ) := by
    have e1 := zmod_of_modEq (rep_modEq (hp2' hp) (((h : ℕ) : ℤ) * binv (p ^ 2) v))
    have e2 := zmod_of_modEq (binv_spec hcop)
    rw [hb'']
    push_cast at e1 e2 ⊢
    rw [e1]
    linear_combination (((h : ℕ) : ZMod (p ^ 2))) * e2
  obtain ⟨γ, hγ⟩ := exists_inv4 hp hp2 hhp 1
  rw [pow_one] at hγ
  have hγd : (p : ℤ) ∣ 4 * ((h : ℕ) : ℤ) * γ - 1 := by
    apply dvd_of_zmod_eq_zero; push_cast at hγ ⊢; rw [hγ]; ring
  have hb''p : ¬ (p : ℤ) ∣ b'' := by
    intro hd
    apply hhp
    obtain ⟨c, hc⟩ := hd
    have e : ((((h : ℕ) : ℤ) : ℤ) : ZMod (p ^ 2)) = ((p * (c * v) : ℤ) : ZMod (p ^ 2)) := by
      rw [← hbv, hc]; push_cast; ring
    have := (dvd_pow_self (p : ℤ) two_ne_zero).trans (Int.ModEq.dvd (modEq_of_zmod' e))
    have := dvd_sub (dvd_mul_right (p : ℤ) (c * v)) this
    simpa using this
  have hβ'' : ((4 * b'' * (p * γ + K) : ℤ) : ZMod (p ^ 2)) = 1 := by
    have hU := isUnit_zmod_of_not_dvd (e := 2) hp hvp
    apply hU.mul_left_cancel
    have hpd : ((p * (4 * ((h : ℕ) : ℤ) * γ - 1) : ℤ) : ZMod (p ^ 2)) = 0 :=
      zmod_eq_zero_of_dvd (by push_cast; rw [sq]; exact mul_dvd_mul_left _ hγd)
    have hN' : ((N : ℕ) : ZMod (p ^ 2)) = 4 * (K : ZMod (p ^ 2)) := by
      have := congrArg (Int.cast : ℤ → ZMod (p ^ 2)) hNK; push_cast at this; exact this
    rw [hv]
    push_cast at hbv hpd ⊢
    rw [hv] at hbv; push_cast at hbv
    linear_combination (4 * ((p : ZMod (p ^ 2)) * γ + K)) * hbv + hpd -
      ((h : ℕ) : ZMod (p ^ 2)) * hN'
  have hhz : ((((h : ℕ) : ℤ) : ℤ) : ZMod p) ≠ 0 := fun h0' => hhp (dvd_of_zmod_eq_zero h0')
  have hleg := legendreSym.sq_one p hhz
  have hl : ((legendreSym p ((h : ℕ) : ℤ) : ℤ) : ℂ) ^ 2 = 1 := by exact_mod_cast hleg
  rw [gsl_complete hp0' (modEq_of_zmod' (by push_cast at hγ ⊢; exact hγ)), gs_prime hp2 hhz,
    gsl_sq_unit hp hp2 hb''p hβ'']
  simp only [hw]
  rw [dL]
  have e3 : E (p ^ 2) (-(K * k ^ 2)) * E p (-(γ * k ^ 2)) = E (p ^ 2) (-((p * γ + K) * k ^ 2)) := by
    rw [← E_sq_mul_p hp0', E_mul_E]; congr 1; ring
  rw [show (legendreSym p ((h : ℕ) : ℤ) : ℂ) / ((p : ℂ) * gs p 1) * E (p ^ 2) (-(K * k ^ 2)) *
      (E p (-(γ * k ^ 2)) * ((legendreSym p ((h : ℕ) : ℤ) : ℂ) * gs p 1)) =
      ((legendreSym p ((h : ℕ) : ℤ) : ℂ) ^ 2 / p) * (E (p ^ 2) (-(K * k ^ 2)) *
        E p (-(γ * k ^ 2))) by field_simp, e3, hl]
  field_simp

/-! ### The case `A_∞` -/

include hp in
theorem dRel_inf (hp2 : p ≠ 2) {N : ℕ} {K : ℤ} (hNK : (N : ℤ) = 4 * K) (hpN : ¬ (p : ℤ) ∣ N)
    (k : ℤ) :
    1 / (p : ℂ) * dL p K k * 1 =
      1 / (p : ℂ) ^ 2 * gsl (p ^ 2) (((rep (p ^ 2) (hp2' hp) (binv (p ^ 2) N)) : ℕ) : ℤ) k := by
  have hp0' := hp.pos
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp0'.ne'
  have hcop := isCoprime_sq_of_not_dvd hp hpN
  set b' : ℤ := (((rep (p ^ 2) (hp2' hp) (binv (p ^ 2) N)) : ℕ) : ℤ) with hb'
  have hNb : ((N * b' : ℤ) : ZMod (p ^ 2)) = 1 := by
    have e1 := zmod_of_modEq (rep_modEq (hp2' hp) (binv (p ^ 2) N))
    have e2 := zmod_of_modEq (binv_spec hcop)
    rw [hb']
    push_cast at e1 e2 ⊢
    rw [e1]; exact e2
  have hb'p : ¬ (p : ℤ) ∣ b' := by
    intro hd
    have h3 : (N : ℤ) * b' ≡ 1 [ZMOD p] :=
      Int.ModEq.of_dvd (by push_cast; exact dvd_pow_self _ two_ne_zero)
        (modEq_of_zmod' (by rw [hNb]; simp))
    have h4 : (p : ℤ) ∣ 1 - N * b' := Int.ModEq.dvd h3
    have h5 : (p : ℤ) ∣ 1 := by
      have := dvd_add h4 (dvd_mul_of_dvd_right hd (N : ℤ)); simpa using this
    exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h5)
  have hN' : ((N : ℕ) : ZMod (p ^ 2)) = 4 * (K : ZMod (p ^ 2)) := by
    have := congrArg (Int.cast : ℤ → ZMod (p ^ 2)) hNK; push_cast at this; exact this
  have hK : ((4 * b' * K : ℤ) : ZMod (p ^ 2)) = 1 := by
    rw [← hNb]; push_cast; rw [hN']; ring
  rw [gsl_sq_unit hp hp2 hb'p hK, dL]
  field_simp

/-! ### The relation for every coset -/

include hp in
/-- **The `L^N` relation on Fourier transforms**: `ω_i D(k) v̂_i(k) = ω_{σ i} v̂_{σ i}(k)`. -/
theorem dRel [Fact p.Prime] (hp2 : p ≠ 2) {N : ℕ} {K : ℤ} (hNK : (N : ℤ) = 4 * K)
    (hpN : ¬ (p : ℤ) ∣ N) (i : HIdx p) (k : ℤ) :
    hw p i * dL p K k * fhat p (cvec p i) k =
      hw p (sigmaL hp N i) * fhat p (cvec p (sigmaL hp N i)) k := by
  rcases i with b | h | u
  · by_cases h1 : (p : ℤ) ∣ 1 + N * ((b : ℕ) : ℤ)
    · by_cases h2 : (p : ℤ) ^ 2 ∣ 1 + N * ((b : ℕ) : ℤ)
      · have hs : sigmaL hp N (.inl b) = .inr (.inr ()) := by simp [sigmaL, h1, h2]
        rw [hs, fhat_inl hp, fhat_inr_inr hp]
        simp only [hw]
        rw [dRel_inl_p2 hp hp2 hNK b h2, mul_one]
      · have hs : sigmaL hp N (.inl b) = .inr (.inl (rep p (hp0 hp) (((b : ℕ) : ℤ) *
            binv p ((1 + N * ((b : ℕ) : ℤ)) / p)))) := by simp [sigmaL, h1, h2]
        rw [hs, fhat_inl hp, fhat_inr_inl hp]
        exact dRel_inl_p hp hp2 hNK b h1 h2 k
    · have hs : sigmaL hp N (.inl b) = .inl (rep (p ^ 2) (hp2' hp) (((b : ℕ) : ℤ) *
          binv (p ^ 2) (1 + N * ((b : ℕ) : ℤ)))) := by simp [sigmaL, h1]
      rw [hs, fhat_inl hp, fhat_inl hp]
      simp only [hw]
      rw [mul_assoc, dRel_inl_unit hp hp2 hNK b h1 k]
  · by_cases h0 : (h : ℕ) = 0
    · have hs : sigmaL hp N (.inr (.inl h)) = .inr (.inl h) := by simp [sigmaL, h0]
      have hw0 : hw p (.inr (.inl h)) = 0 := by simp [hw, h0, legendreSym.at_zero]
      rw [hs, hw0]; ring
    · have hs : sigmaL hp N (.inr (.inl h)) = .inl (rep (p ^ 2) (hp2' hp) (((h : ℕ) : ℤ) *
          binv (p ^ 2) (p + ((h : ℕ) : ℤ) * N))) := by simp [sigmaL, h0]
      rw [hs, fhat_inr_inl hp, fhat_inl hp]
      exact dRel_h hp hp2 hNK hpN h h0 k
  · have hs : sigmaL hp N (.inr (.inr u)) = .inl (rep (p ^ 2) (hp2' hp) (binv (p ^ 2) N)) := by
      simp [sigmaL]
    rw [hs, fhat_inr_inr hp, fhat_inl hp]
    exact dRel_inf hp hp2 hNK hpN k

end Weights


/-! ## The Weil matrix of `L^N` and the contraction -/

section Contraction

variable {p : ℕ} (hp : p.Prime)

/-- `L^N = S T^{−N} S⁻¹`. -/
theorem matL_eq_word (N : ℕ) :
    matL N = ModularGroup.S * (ModularGroup.T⁻¹ ^ N * ModularGroup.S⁻¹) := by
  have hT : ModularGroup.T⁻¹ ^ N = ModularGroup.T ^ (-(N : ℤ)) := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hT]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matL, Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.S,
      Matrix.SpecialLinearGroup.SL2_inv_expl, Matrix.vecMul, dotProduct]

theorem weilWord_Tinv_pow (P : ℕ) {γ : SL(2, ℤ)} {A : Matrix (Fin (2 * P)) (Fin (2 * P)) ℂ}
    (h : WeilWord P γ A) (n : ℕ) :
    WeilWord P (ModularGroup.T⁻¹ ^ n * γ) (weilTinv P ^ n * A) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have := WeilWord.Tinv ih
    rwa [← mul_assoc, ← Matrix.mul_assoc, ← pow_succ', ← pow_succ'] at this

/-- The Weil word of `L^N`. -/
theorem weilWord_matL (P N : ℕ) :
    WeilWord P (matL N) (weilS P * (weilTinv P ^ N * weilS P)) := by
  rw [matL_eq_word]
  have h0 : WeilWord P ModularGroup.S⁻¹ (weilS P) := by
    simpa using WeilWord.Sinv (WeilWord.one (N := P))
  exact WeilWord.S (weilWord_Tinv_pow P h0 N)

/-- The diagonal of `(T⁻¹)^N` at level `p²`: `e(−K μ²/p²)` for `N = 4K`, `24 ∣ N`. -/
theorem weilPhase_inv_pow {N : ℕ} {K : ℤ} (hNK : (N : ℤ) = 4 * K) (h24 : 24 ∣ N) (μ : ℤ) :
    (weilPhase (p ^ 2) μ)⁻¹ ^ N = dL p K μ := by
  obtain ⟨m, rfl⟩ := h24
  rw [inv_pow, weilPhase, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, dL, E_eq]
  have h2 : cexp ((((24 * m : ℕ)) : ℂ) * -(2 * Real.pi * I / 24)) = 1 := by
    convert Complex.exp_int_mul_two_pi_mul_I (-(m : ℤ)) using 2
    push_cast; ring
  rw [h2, mul_one, ← Complex.exp_neg]
  congr 1
  have hK : (K : ℂ) = 6 * m := by
    have : (4 * K : ℤ) = 4 * (6 * m) := by rw [← hNK]; push_cast; ring
    have : K = 6 * m := by omega
    rw [this]; push_cast; ring
  by_cases hp0 : (p : ℂ) = 0
  · simp [hp0]
  push_cast
  rw [hK]
  field_simp
  ring

theorem weilS_eq (P : ℕ) (μ k : Fin (2 * P)) :
    weilS P μ k = (((Real.sqrt (2 * P))⁻¹ : ℝ) : ℂ) *
      E (2 * P) (((k : ℕ) : ℤ) * ((μ : ℕ) : ℤ)) := by
  simp only [weilS, E_eq]
  congr 1
  push_cast
  ring_nf

theorem weilS_symm (P : ℕ) (μ k : Fin (2 * P)) : weilS P μ k = weilS P k μ := by
  rw [weilS_eq, weilS_eq, mul_comm (((k : ℕ) : ℤ))]

/-- Matrix entries of `S D S`. -/
theorem mul_diag_mul_apply {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ)
    (μ j : Fin n) :
    (S * (Matrix.diagonal d * S)) μ j = ∑ k, S μ k * d k * S k j := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diagonal_mul]
  ring

include hp in
/-- **The contraction.** If `c D(k) v̂(k) = c' v̂'(k)` for all `k`, with `v'` even, then
`c Σ_μ v(μ) (S D S)_{μj} = c' v'(j)`. -/
theorem contraction {N : ℕ} {K : ℤ} (hNK : (N : ℤ) = 4 * K) (h24 : 24 ∣ N)
    (v v' : ℤ → ℂ) (hv' : ∀ x, v' (x + ((2 * p ^ 2 : ℕ) : ℤ)) = v' x)
    (hev : ∀ x, v' (-x) = v' x) (c c' : ℂ)
    (hrel : ∀ k : ℤ, c * dL p K k * fhat p v k = c' * fhat p v' k) (j : Fin (2 * p ^ 2)) :
    c * ∑ μ : Fin (2 * p ^ 2), v ((μ : ℕ) : ℤ) *
        ((weilS (p ^ 2) * (weilTinv (p ^ 2) ^ N * weilS (p ^ 2)) :
          Matrix (Fin (2 * p ^ 2)) (Fin (2 * p ^ 2)) ℂ) μ j) = c' * v' ((j : ℕ) : ℤ) := by
  have hp0 := hp.pos
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp0.ne'
  have hM : 0 < 2 * p ^ 2 := by positivity
  have hTi : weilTinv (p ^ 2) ^ N = Matrix.diagonal fun k : Fin (2 * p ^ 2) =>
      dL p K ((k : ℕ) : ℤ) := by
    rw [weilTinv, Matrix.diagonal_pow]
    congr 1; funext k
    rw [Pi.pow_apply, weilPhase_inv_pow hNK h24]
  rw [hTi]
  simp_rw [mul_diag_mul_apply, weilS_eq]
  set s : ℂ := (((Real.sqrt (2 * ((p ^ 2 : ℕ) : ℝ)))⁻¹ : ℝ) : ℂ) with hs
  have hs2 : s ^ 2 * (2 * p ^ 2 : ℕ) = 1 := by
    have h0 : (0 : ℝ) ≤ 2 * ((p ^ 2 : ℕ) : ℝ) := by positivity
    have hne : (2 * ((p ^ 2 : ℕ) : ℝ)) ≠ 0 := by positivity
    rw [hs, ← Complex.ofReal_pow, inv_pow, Real.sq_sqrt h0]
    push_cast
    field_simp
  -- swap the sums
  have step1 : ∑ μ : Fin (2 * p ^ 2), v ((μ : ℕ) : ℤ) * ∑ k : Fin (2 * p ^ 2),
      s * E (2 * p ^ 2) (((k : ℕ) : ℤ) * ((μ : ℕ) : ℤ)) * dL p K ((k : ℕ) : ℤ) *
        (s * E (2 * p ^ 2) (((j : ℕ) : ℤ) * ((k : ℕ) : ℤ))) =
      s ^ 2 * ∑ k : Fin (2 * p ^ 2), dL p K ((k : ℕ) : ℤ) * fhat p v ((k : ℕ) : ℤ) *
        E (2 * p ^ 2) (((j : ℕ) : ℤ) * ((k : ℕ) : ℤ)) := by
    simp only [fhat, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun μ _ => ?_
    ring
  rw [step1]
  have step2 : c * (s ^ 2 * ∑ k : Fin (2 * p ^ 2), dL p K ((k : ℕ) : ℤ) * fhat p v ((k : ℕ) : ℤ) *
      E (2 * p ^ 2) (((j : ℕ) : ℤ) * ((k : ℕ) : ℤ))) =
      s ^ 2 * c' * ∑ k : Fin (2 * p ^ 2), fhat p v' ((k : ℕ) : ℤ) *
        E (2 * p ^ 2) (((j : ℕ) : ℤ) * ((k : ℕ) : ℤ)) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := hrel ((k : ℕ) : ℤ)
    linear_combination (s ^ 2 * E (2 * p ^ 2) (((j : ℕ) : ℤ) * ((k : ℕ) : ℤ))) * this
  rw [step2]
  -- the Fourier inversion
  have step3 : ∑ k : Fin (2 * p ^ 2), fhat p v' ((k : ℕ) : ℤ) *
      E (2 * p ^ 2) (((j : ℕ) : ℤ) * ((k : ℕ) : ℤ)) =
      ∑ μ : Fin (2 * p ^ 2), v' ((μ : ℕ) : ℤ) *
        (if ((2 * p ^ 2 : ℕ) : ℤ) ∣ ((μ : ℕ) : ℤ) + ((j : ℕ) : ℤ) then
          ((2 * p ^ 2 : ℕ) : ℂ) else 0) := by
    simp only [fhat, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← sum_E_lin hM, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, E_mul_E]
    congr 2
    ring
  rw [step3]
  -- only `μ ≡ −j` survives
  rw [Finset.sum_eq_single (idxc hM (-((j : ℕ) : ℤ)))]
  · have hc := idxc_modEq hM (-((j : ℕ) : ℤ))
    rw [if_pos (by
      have h2 := Int.ModEq.dvd hc
      have h3 := (dvd_neg).2 h2
      rwa [show -(-((j : ℕ) : ℤ) - (((idxc hM (-((j : ℕ) : ℤ))) : ℕ) : ℤ)) =
        (((idxc hM (-((j : ℕ) : ℤ))) : ℕ) : ℤ) + ((j : ℕ) : ℤ) by ring] at h3)]
    rw [periodic_congr' hv' hc, hev]
    have : (s ^ 2 * c') * (v' ((j : ℕ) : ℤ) * ((2 * p ^ 2 : ℕ) : ℂ)) =
        c' * v' ((j : ℕ) : ℤ) * (s ^ 2 * (2 * p ^ 2 : ℕ)) := by ring
    rw [this, hs2, mul_one]
  · intro μ _ hμ
    rw [if_neg, mul_zero]
    intro hd
    apply hμ
    apply fin_eq_of_modEq
    refine Int.ModEq.trans ?_ (idxc_modEq hM _).symm
    refine Int.modEq_iff_dvd.2 ?_
    have : -((j : ℕ) : ℤ) - ((μ : ℕ) : ℤ) = -(((μ : ℕ) : ℤ) + ((j : ℕ) : ℤ)) := by ring
    rw [this]
    exact (dvd_neg).2 hd
  · simp

end Contraction


/-! ## Evenness, and the diagonal generators -/

section Diag

variable {p : ℕ} (hp : p.Prime)

theorem neg_ediv_sq {d x : ℤ} (h : d ∣ x) : (-x / d) ^ 2 = (x / d) ^ 2 := by
  rw [Int.neg_ediv_of_dvd h, neg_sq]

theorem cvec_neg (i : HIdx p) (x : ℤ) : cvec p i (-x) = cvec p i x := by
  rcases i with b | h | u <;> simp only [cvec, dvd_neg]
  · split_ifs with h2
    · rw [neg_ediv_sq h2]
    · rfl
  · split_ifs with h2
    · rw [neg_ediv_sq h2]
    · rfl

theorem thvec_neg (x : ℤ) : thvec p (-x) = thvec p x := by
  simp only [thvec, dvd_neg]

theorem dvd_mul_iff_of_coprime {n ℓ' μ : ℤ} (h : IsCoprime ℓ' n) : n ∣ ℓ' * μ ↔ n ∣ μ :=
  ⟨fun hd => h.symm.dvd_of_dvd_mul_left hd, fun hd => dvd_mul_of_dvd_right hd _⟩

theorem mul_ediv_of_dvd' {d ℓ' μ : ℤ} (h : d ∣ μ) : ℓ' * μ / d = ℓ' * (μ / d) := by
  obtain ⟨m, rfl⟩ := h
  by_cases hd : d = 0
  · simp [hd]
  rw [show ℓ' * (d * m) = d * (ℓ' * m) by ring, Int.mul_ediv_cancel_left _ hd,
    Int.mul_ediv_cancel_left _ hd]

include hp in
/-- The diagonal generators permute the Weil vectors: `v_{σ i}(μ) = v_i(ℓ' μ)`. -/
theorem cvec_sigmaG {ℓ' : ℤ} (hℓ : IsCoprime ℓ' (2 * p)) (i : HIdx p) (μ : ℤ) :
    cvec p (sigmaG hp ℓ' i) μ = cvec p i (ℓ' * μ) := by
  have hpos := hp.pos
  have h2 : IsCoprime ℓ' 2 := hℓ.of_mul_right_left
  have hpc : IsCoprime ℓ' (p : ℤ) := hℓ.of_mul_right_right
  rcases i with b | h | u
  · simp only [sigmaG, cvec]
    simp only [dvd_mul_iff_of_coprime h2]
    split_ifs with hμ
    · rw [mul_ediv_of_dvd' hμ]
      apply E_congr (pow_pos hpos 2)
      have := rep_modEq (hp2' hp) (((b : ℕ) : ℤ) * ℓ' ^ 2)
      push_cast at this ⊢
      calc (((rep (p ^ 2) (hp2' hp) (((b : ℕ) : ℤ) * ℓ' ^ 2)) : ℕ) : ℤ) * (μ / 2) ^ 2
          ≡ ((b : ℕ) : ℤ) * ℓ' ^ 2 * (μ / 2) ^ 2 [ZMOD (p ^ 2 : ℕ)] := by
            push_cast; exact this.mul_right _
        _ = ((b : ℕ) : ℤ) * (ℓ' * (μ / 2)) ^ 2 := by ring
    · rfl
  · simp only [sigmaG, cvec]
    simp only [dvd_mul_iff_of_coprime hℓ]
    split_ifs with hμ
    · rw [mul_ediv_of_dvd' hμ]
      apply E_congr hpos
      have := rep_modEq (hp0 hp) (((h : ℕ) : ℤ) * ℓ' ^ 2)
      calc (((rep p (hp0 hp) (((h : ℕ) : ℤ) * ℓ' ^ 2)) : ℕ) : ℤ) * (μ / (2 * p)) ^ 2
          ≡ ((h : ℕ) : ℤ) * ℓ' ^ 2 * (μ / (2 * p)) ^ 2 [ZMOD p] := this.mul_right _
        _ = ((h : ℕ) : ℤ) * (ℓ' * (μ / (2 * p))) ^ 2 := by ring
    · rfl
  · simp only [sigmaG, cvec]
    have h2p : IsCoprime ℓ' (2 * (p : ℤ) ^ 2) := h2.mul_right (hpc.pow_right)
    simp only [dvd_mul_iff_of_coprime h2p]

theorem thvec_mul {ℓ' : ℤ} (hℓ : IsCoprime ℓ' (2 * p)) (μ : ℤ) :
    thvec p (ℓ' * μ) = thvec p μ := by
  simp only [thvec, dvd_mul_iff_of_coprime hℓ]

include hp in
theorem hw_sigmaG [Fact p.Prime] {ℓ' : ℤ} (hℓ : IsCoprime ℓ' (2 * p)) (i : HIdx p) :
    hw p (sigmaG hp ℓ' i) = hw p i := by
  have hpc : IsCoprime ℓ' (p : ℤ) := hℓ.of_mul_right_right
  rcases i with b | h | u
  · rfl
  · simp only [sigmaG, hw]
    congr 2
    rw [legendreSym.mod, (rep_modEq (hp0 hp) (((h : ℕ) : ℤ) * ℓ' ^ 2)).eq, ← legendreSym.mod,
      legendreSym.mul, legendreSym.sq_one' p, mul_one]
    intro h0
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ℓ' p).1 h0
    exact (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).1 hpc.symm this
  · rfl

end Diag

end SSHecke

end VOA.Classification.COne
