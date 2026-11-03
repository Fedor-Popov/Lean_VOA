import VOA.DeligneAudit.DeligneFusionECalc

/-!
# Chari–Venkatesh modules for `sl₂[t]`, part 1 (the relation-shift lemma)

`sl₂[t]` triple `E s, H p, F k` on a module `V`, highest-weight vectors `v` (`E_s v = 0`, `H_{p≥1} v = 0`).
With `X(r,s) w = E₁^s F₀^{r+s} w`:

* `Fspan_stable`: the `F`-span of a highest-weight vector is stable under `E`, `H`, `F`;
* `F_E1pow`: `F_i E₁^s = E₁^s F_i − s E₁^{s−1} H_{i+1} − s(s−1) E₁^{s−2} E_{i+2}`;
* `X_succ` (CV Lemma 6.6, step 1) and `F_X` (step 2):
  `F_i X(r,s) v = X(r,s) F_i v + 2ns X(r,s−1) F_{i+1} v + s(s−1)n(n−1) X(r,s−2) F_{i+2} v`;
* `shift_lemma`: if `X(r,s) v = 0` on `s + r ≥ 1 + rk + T` (`r ≥ 1`) then, for `j ≥ k+1`,
  `X(r,s) F_j v = 0` on `s + r + 2 ≥ 1 + rk + T` (the relation region shifts by `2`), via the exact shifts
  `Δ_j = max(−2, k−1−j)`.
-/

namespace VOA.DeligneAudit.CVsl2

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {E H F : ℕ → Module.End ℂ V}
  (hEF : ∀ s k, E s * F k - F k * E s = H (s + k))
  (hHF : ∀ p k, H p * F k - F k * H p = (-2 : ℂ) • F (p + k))
  (hHE : ∀ p q, H p * E q - E q * H p = (2 : ℂ) • E (p + q))
  (hFF : ∀ i j, F i * F j = F j * F i) (hEE : ∀ i j, E i * E j = E j * E i)

/-! ## The `F`-span of a highest-weight vector -/

/-- The `F`-span `span {F_{k₁} ⋯ F_{k_n} v}`. -/
def Fspan (F : ℕ → Module.End ℂ V) (v : V) : Submodule ℂ V :=
  Submodule.span ℂ (Set.range fun l : List ℕ => ECalc.Fw F l v)

theorem Fw_mem (v : V) (l : List ℕ) : ECalc.Fw F l v ∈ Fspan F v := Submodule.subset_span ⟨l, rfl⟩

theorem self_mem (v : V) : v ∈ Fspan F v := by simpa [ECalc.Fw] using Fw_mem (F := F) v []

theorem Fspan_F (v : V) (k : ℕ) : Fspan F v ≤ (Fspan F v).comap (F k) := by
  rw [Fspan, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  exact Fw_mem v (k :: l)

include hEF hHF in
/-- The `F`-span of a highest-weight vector is stable under all `E_s` and `H_p`. -/
theorem Fspan_EH {v : V} (hE : ∀ s, E s v = 0) (hH : ∀ p, 1 ≤ p → H p v = 0) {c : ℂ}
    (hH0 : H 0 v = c • v) : ∀ l : List ℕ, (∀ s, E s (ECalc.Fw F l v) ∈ Fspan F v) ∧
      (∀ p, H p (ECalc.Fw F l v) ∈ Fspan F v)
  | [] => by
      refine ⟨fun s => by simp [ECalc.Fw, hE s], fun p => ?_⟩
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · simp only [ECalc.Fw, Module.End.one_apply, hH0]; exact Submodule.smul_mem _ _ (self_mem v)
      · simp [ECalc.Fw, hH p hp]
  | (k :: l) => by
      obtain ⟨ihE, ihH⟩ := Fspan_EH hE hH hH0 l
      set X := ECalc.Fw F l v
      have hX : ECalc.Fw F (k :: l) v = F k X := rfl
      refine ⟨fun s => ?_, fun p => ?_⟩
      · rw [hX]
        have := congrArg (fun T => T X) (hEF s k)
        simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
        rw [sub_eq_iff_eq_add.mp this]
        exact Submodule.add_mem _ (ihH _) (Fspan_F v k (ihE s))
      · rw [hX]
        have := congrArg (fun T => T X) (hHF p k)
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply] at this
        rw [sub_eq_iff_eq_add.mp this]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Fw_mem v ((p + k) :: l)))
          (Fspan_F v k (ihH p))

include hEF hHF in
theorem Fspan_stable {v : V} (hE : ∀ s, E s v = 0) (hH : ∀ p, 1 ≤ p → H p v = 0) {c : ℂ}
    (hH0 : H 0 v = c • v) :
    (∀ s, Fspan F v ≤ (Fspan F v).comap (E s)) ∧ (∀ p, Fspan F v ≤ (Fspan F v).comap (H p)) := by
  refine ⟨fun s => ?_, fun p => ?_⟩ <;> rw [Fspan, Submodule.span_le] <;> rintro _ ⟨l, rfl⟩
  · exact (Fspan_EH hEF hHF hE hH hH0 l).1 s
  · exact (Fspan_EH hEF hHF hE hH hH0 l).2 p

/-! ## Commuting `F_i` past powers of `E₁` -/

include hEF hHE hEE in
/-- `F_i E₁^s = E₁^s F_i − s E₁^{s−1} H_{i+1} − s(s−1) E₁^{s−2} E_{i+2}` (as operators). -/
theorem F_E1pow (i : ℕ) : ∀ s : ℕ, F i * E 1 ^ s = E 1 ^ s * F i -
    (s : ℂ) • (E 1 ^ (s - 1) * H (i + 1)) - ((s * (s - 1) : ℕ) : ℂ) • (E 1 ^ (s - 2) * E (i + 2))
  | 0 => by simp
  | s + 1 => by
      have ih := F_E1pow i s
      have h1 : F i * E 1 = E 1 * F i - H (i + 1) := by
        have := hEF 1 i; rw [add_comm] at this; rw [← this]; abel
      have h2 : H (i + 1) * E 1 = E 1 * H (i + 1) + (2 : ℂ) • E (i + 2) := by
        have := hHE (i + 1) 1; rw [show i + 1 + 1 = i + 2 by ring] at this; rw [← this]; abel
      have h3 : E (i + 2) * E 1 = E 1 * E (i + 2) := hEE _ _
      rw [pow_succ, ← mul_assoc, ih, sub_mul, sub_mul, mul_assoc, h1, smul_mul_assoc, mul_assoc, h2,
        smul_mul_assoc, mul_assoc, h3]
      rcases s with _ | s
      · simp
      · rcases s with _ | s
        · simp only [mul_sub, mul_add, mul_smul_comm, ← mul_assoc, ← pow_succ]
          simp; module
        · simp only [mul_sub, mul_add, mul_smul_comm, ← mul_assoc, ← pow_succ,
            show s + 2 - 1 + 1 = s + 2 by omega, show s + 2 - 2 + 1 = s + 1 by omega,
            show s + 1 + 2 - 1 = s + 2 by omega, show s + 1 + 2 - 2 = s + 1 by omega]
          push_cast; module

/-! ## `X(r,s) = E₁^s F₀^{r+s}` and the shift lemma -/

variable (E F) in
/-- `X(r,s) w = E₁^s F₀^{r+s} w`. -/
def X (r s : ℕ) (w : V) : V := (E 1 ^ s) ((F 0 ^ (r + s)) w)

include hFF in
theorem F_F0pow (k n : ℕ) (w : V) : F k ((F 0 ^ n) w) = (F 0 ^ n) (F k w) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply]
  exact congrArg (fun T => T w) ((Commute.pow_right (hFF k 0) n).eq)

theorem X_F0 (r s : ℕ) (w : V) : X E F r s (F 0 w) = X E F (r + 1) s w := by
  simp only [X, ← Module.End.mul_apply, ← pow_succ, show r + 1 + s = r + s + 1 by ring]

variable {v : V} (hE : ∀ s, E s v = 0) (hH : ∀ p, 1 ≤ p → H p v = 0)

include hEF hHF hFF hE hH in
/-- CV Lemma 6.6, step 1: `X(r+1,s+1) v = −(n+2)(n+1) X(r,s) F₁ v`, `n = r + s`. -/
theorem X_succ (r s : ℕ) :
    X E F (r + 1) (s + 1) v = (-(((r + s + 2) * (r + s + 1) : ℕ) : ℂ)) • X E F r s (F 1 v) := by
  simp only [X]
  rw [pow_succ, Module.End.mul_apply, show r + 1 + (s + 1) = r + s + 2 by ring,
    ECalc.E_F0pow hEF hHF hFF hE hH 1 le_rfl (r + s + 2), map_smul,
    show r + s + 2 - 2 = r + s by omega, F_F0pow hFF]
  congr 3

include hEF hHF hHE hFF hEE hE hH in
/-- CV Lemma 6.6, step 2 (the `F_i` commutation identity). -/
theorem F_X (i r s : ℕ) :
    F i (X E F r (s + 2) v) = X E F r (s + 2) (F i v) +
      ((2 * (r + s + 2) * (s + 2) : ℕ) : ℂ) • X E F r (s + 1) (F (i + 1) v) +
      (((s + 2) * (s + 1) * (r + s + 2) * (r + s + 1) : ℕ) : ℂ) • X E F r s (F (i + 2) v) := by
  simp only [X]
  rw [← Module.End.mul_apply (F i), F_E1pow hEF hHE hEE i (s + 2)]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply]
  rw [ECalc.H_F0pow hHF hFF hH (i + 1) (by omega), ECalc.E_F0pow hEF hHF hFF hE hH (i + 2) (by omega),
    map_smul, map_smul, F_F0pow hFF, F_F0pow hFF, F_F0pow hFF,
    show r + (s + 2) - 1 = r + (s + 1) by omega, show r + (s + 2) - 2 = r + s by omega,
    show s + 2 - 1 = s + 1 by omega, show s + 2 - 2 = s by omega]
  simp only [smul_smul, sub_eq_add_neg, ← neg_smul]
  congr 2 <;> [skip; congr 1] <;> push_cast <;> ring

/-- The exact shift of the relation region for `F_j v`. -/
def Dl (k j : ℕ) : ℤ := max (-2) ((k : ℤ) - 1 - j)

include hEF hHF hHE hFF hEE hE hH in
/-- **CV Lemma 6.6 (shift lemma)**, with the exact shifts `Δ_j = max(−2, k−1−j)`. -/
theorem shift_aux (k T d : ℕ)
    (hrel : ∀ r s, 1 ≤ r → 1 + r * k + T ≤ s + r + d → X E F r s v = 0) :
    ∀ j (r s : ℕ), 1 ≤ r → ((1 + r * k + T : ℕ) : ℤ) + Dl k j ≤ ((s + r + d : ℕ) : ℤ) →
      X E F r s (F j v) = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro r s hr hs
  have hk1 : (r + 1) * k = r * k + k := by ring
  rcases j with _ | _ | i
  · rw [X_F0]
    refine hrel (r + 1) s (by omega) ?_
    simp only [Dl] at hs; push_cast at hs; rw [hk1]; omega
  · have h := X_succ hEF hHF hFF hE hH r s
    have hc : (-(((r + s + 2) * (r + s + 1) : ℕ) : ℂ)) ≠ 0 := by
      rw [neg_ne_zero, Nat.cast_ne_zero]; exact Nat.mul_ne_zero (by omega) (by omega)
    have h0 : X E F (r + 1) (s + 1) v = 0 := by
      refine hrel (r + 1) (s + 1) (by omega) ?_
      simp only [Dl] at hs; push_cast at hs; rw [hk1]; omega
    rw [h0, eq_comm, smul_eq_zero] at h
    exact h.resolve_left hc
  · -- `j = i + 2`: use `F_X` at `(r, s+2)`
    have h := F_X hEF hHF hHE hFF hEE hE hH i r s
    simp only [Dl] at hs ih; push_cast at hs
    have hA : X E F r (s + 2) v = 0 := hrel r (s + 2) hr (by omega)
    have hB : X E F r (s + 2) (F i v) = 0 := ih i (by omega) r (s + 2) hr (by push_cast; omega)
    have hC : X E F r (s + 1) (F (i + 1) v) = 0 :=
      ih (i + 1) (by omega) r (s + 1) hr (by push_cast; omega)
    rw [hA, map_zero, hB, hC, smul_zero, add_zero, zero_add, eq_comm, smul_eq_zero] at h
    exact h.resolve_left (Nat.cast_ne_zero.mpr (by positivity))

include hEF hHF hHE hFF hEE hE hH in
/-- The region shifts by `2` for `F_j v`, `j ≥ k + 1`. -/
theorem shift_lemma (k T d : ℕ)
    (hrel : ∀ r s, 1 ≤ r → 1 + r * k + T ≤ s + r + d → X E F r s v = 0) (j : ℕ) (hj : k + 1 ≤ j)
    (r s : ℕ) (hr : 1 ≤ r) (hs : 1 + r * k + T ≤ s + r + d + 2) : X E F r s (F j v) = 0 := by
  refine shift_aux hEF hHF hHE hFF hEE hE hH k T d hrel j r s hr ?_
  have : Dl k j = -2 := by simp only [Dl]; omega
  rw [this]; push_cast; omega

/-! ## The relations in `Q`-form: `Q(r,s) = [u^s] F(u)^r` -/

variable (F) in
/-- `Q(r,s) = [u^s] F(u)^r = Σ_{k₁+⋯+k_r = s} F_{k₁}⋯F_{k_r}`. -/
def Q (r s : ℕ) : Module.End ℂ V := PowerSeries.coeff s (Garland.Fs F ^ r)

theorem Q_succ (r s : ℕ) : Q F (r + 1) s = ∑ x ∈ Finset.antidiagonal s, F x.1 * Q F r x.2 := by
  simp only [Q, pow_succ', PowerSeries.coeff_mul, Garland.Fs, PowerSeries.coeff_mk]

theorem Q_zero_r (s : ℕ) : Q F 0 s = if s = 0 then 1 else 0 := by
  simp [Q, PowerSeries.coeff_one]

theorem Q_s_zero (r : ℕ) : Q F r 0 = F 0 ^ r := by
  simp [Q, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, Garland.Fs]

include hFF in
theorem comm_Q (i : ℕ) : ∀ r s, F i * Q F r s = Q F r s * F i
  | 0, s => by rw [Q_zero_r]; split_ifs <;> simp
  | r + 1, s => by
      rw [Q_succ, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← mul_assoc, hFF, mul_assoc, comm_Q i r x.2, mul_assoc]

include hFF in
theorem Q_F (i r s : ℕ) (w : V) : Q F r s (F i w) = F i (Q F r s w) := by
  rw [← Module.End.mul_apply, ← comm_Q hFF, Module.End.mul_apply]

theorem Q_mem_Fspan (w : V) : ∀ r s, Q F r s w ∈ Fspan F w
  | 0, s => by rw [Q_zero_r]; split_ifs <;> simp [self_mem]
  | r + 1, s => by
      rw [Q_succ, LinearMap.coe_sum, Finset.sum_apply]
      exact Submodule.sum_mem _ fun x _ => Fspan_F w x.1 (Q_mem_Fspan w r x.2)

/-- `Fw` commutes with each `F k`. -/
theorem Fw_F (hFF : ∀ i j, F i * F j = F j * F i) (k : ℕ) :
    ∀ (l : List ℕ) (w : V), ECalc.Fw F l (F k w) = F k (ECalc.Fw F l w)
  | [], w => rfl
  | (j :: l), w => by
      change F j (ECalc.Fw F l (F k w)) = F k (F j (ECalc.Fw F l w))
      rw [Fw_F hFF k l w, ← Module.End.mul_apply (F j), hFF, Module.End.mul_apply]

include hFF in
theorem F_Fspan (k : ℕ) (w : V) : (Fspan F w).map (F k) ≤ Fspan F (F k w) := by
  rw [Fspan, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, ← Fw_F hFF]; exact Fw_mem _ l

section Trunc

variable {L : ℕ} {w : V} (hL : ∀ q, L ≤ q → F q w = 0)
include hFF hL

/-- (P1) Terms of mode `≥ L` vanish: `Q(r,s) w = 0` once `s > (L−1) r`. -/
theorem Q_high : ∀ r s, (L - 1) * r < s → Q F r s w = 0
  | 0, s, hs => by rw [Q_zero_r, if_neg (by omega)]; rfl
  | r + 1, s, hs => by
      rw [Q_succ, LinearMap.coe_sum, Finset.sum_apply]
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [Finset.mem_antidiagonal] at hx
      rw [Module.End.mul_apply]
      by_cases hi : L ≤ x.1
      · rw [← Q_F hFF, hL _ hi, map_zero]
      · rw [Q_high r x.2 (by rw [Nat.mul_succ] at hs; omega), map_zero]

/-- (P3) The top coefficient: `Q(r, (L−1) r) w = F_{L−1}^r w`. -/
theorem Q_top : ∀ r, Q F r ((L - 1) * r) w = (F (L - 1) ^ r) w
  | 0 => by rw [Q_zero_r, if_pos (by ring)]; rfl
  | r + 1 => by
      rw [Q_succ, LinearMap.coe_sum, Finset.sum_apply,
        Finset.sum_eq_single ((L - 1), (L - 1) * r)]
      · rw [Module.End.mul_apply, Q_top r, pow_succ', Module.End.mul_apply]
      · rintro ⟨i, j⟩ hx hne
        rw [Finset.mem_antidiagonal] at hx
        simp only at hx
        rw [Module.End.mul_apply]
        by_cases hi : L ≤ i
        · rw [← Q_F hFF, hL _ hi, map_zero]
        · have hi' : i < L - 1 ∨ i = L - 1 := by omega
          rcases hi' with hi' | rfl
          · rw [Q_high hFF hL r j (by rw [Nat.mul_succ] at hx; omega), map_zero]
          · refine absurd ?_ hne
            have : j = (L - 1) * r := by rw [Nat.mul_succ] at hx; omega
            rw [this]
      · intro h; exact absurd (Finset.mem_antidiagonal.mpr (by ring)) h

/-- (P2) Divisibility: `Q(r,s) w ∈ F-span of F_{L−1}^m w` once `s ≥ (L−2) r + m`. -/
theorem Q_div : ∀ r m s, (L - 2) * r + m ≤ s → Q F r s w ∈ Fspan F ((F (L - 1) ^ m) w)
  | 0, m, s, hs => by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simpa using Q_mem_Fspan w 0 s
      · rw [Q_zero_r, if_neg (by omega)]; exact Submodule.zero_mem _
  | r + 1, m, s, hs => by
      rw [Q_succ, LinearMap.coe_sum, Finset.sum_apply]
      refine Submodule.sum_mem _ fun x hx => ?_
      rw [Finset.mem_antidiagonal] at hx
      rw [Module.End.mul_apply]
      by_cases hi : L ≤ x.1
      · rw [← Q_F hFF, hL _ hi, map_zero]; exact Submodule.zero_mem _
      · rcases Nat.lt_or_ge x.1 (L - 1) with hi' | hi'
        · exact Fspan_F _ _ (Q_div r m x.2 (by rw [Nat.mul_succ] at hs; omega))
        · have hx1 : x.1 = L - 1 := by omega
          rcases Nat.eq_zero_or_pos m with rfl | hm
          · simp only [pow_zero, Module.End.one_apply]
            exact Fspan_F _ _ (by simpa using Q_mem_Fspan w r x.2)
          · have ih := Q_div r (m - 1) x.2 (by rw [Nat.mul_succ] at hs; omega)
            have := F_Fspan hFF (L - 1) _ (Submodule.mem_map_of_mem ih)
            rw [← Module.End.mul_apply, ← pow_succ', show m - 1 + 1 = m by omega] at this
            rw [hx1]; exact this

end Trunc

/-! ## Highest-weight propagation along `F_b` -/

include hEF hHF hFF in
/-- `F_b v` is again highest weight when `F_q v = 0` for `q ≥ b + 1`. -/
theorem hw_Fb {b : ℕ} (hb : 1 ≤ b) {v : V} (hE : ∀ s, E s v = 0) (hH : ∀ p, 1 ≤ p → H p v = 0)
    (hF : ∀ q, b + 1 ≤ q → F q v = 0) :
    (∀ s, E s (F b v) = 0) ∧ (∀ p, 1 ≤ p → H p (F b v) = 0) ∧ (∀ q, b + 1 ≤ q → F q (F b v) = 0) := by
  refine ⟨fun s => ?_, fun p hp => ?_, fun q hq => ?_⟩
  · have := congrArg (fun T => T v) (hEF s b)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hE, map_zero, sub_zero] at this
    rw [this, hH _ (by omega)]
  · have := congrArg (fun T => T v) (hHF p b)
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, hH p hp, map_zero,
      sub_zero] at this
    rw [this, hF _ (by omega), smul_zero]
  · rw [← Module.End.mul_apply, hFF, Module.End.mul_apply, hF q hq, map_zero]

include hHF in
theorem H0_Fb {b : ℕ} {v : V} {c : ℂ} (hH0 : H 0 v = c • v) : H 0 (F b v) = (c - 2) • F b v := by
  have := congrArg (fun T => T v) (hHF 0 b)
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, hH0, map_smul,
    zero_add] at this
  rw [sub_eq_iff_eq_add.mp this, sub_smul]; module

/-! ## `X` versus `Q` for highest-weight vectors, and the iterated shift -/

include hEF hHF hFF in
/-- Garland: for a highest-weight `v` and `r ≥ 1`, `X(r,s) v` is a nonzero multiple of `Q(r,s) v`. -/
theorem X_eq_Q {v : V} (hE : ∀ s, E s v = 0) (hH : ∀ p, 1 ≤ p → H p v = 0) (r s : ℕ) (hr : 1 ≤ r) :
    ∃ c : ℂ, c ≠ 0 ∧ X E F r s v = c • Q F r s v := by
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
  have hEF' : ∀ k, E 1 * F k - F k * E 1 = H (k + 1) := fun k => by rw [hEF 1 k, add_comm]
  obtain ⟨c, hc, h⟩ := Garland.E_iter hEF' (fun m k => hHF (m + 1) k) hFF (hE 1)
    (fun m => hH (m + 1) (by omega)) q s 0
  refine ⟨c, hc, ?_⟩
  simp only [X, Q, zero_add] at h ⊢
  rw [← h, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]
  simp [Garland.Fs]

include hEF hHF hFF in
theorem Q_zero_of_X {v : V} (hE : ∀ s, E s v = 0) (hH : ∀ p, 1 ≤ p → H p v = 0) {r s : ℕ}
    (hr : 1 ≤ r) (h : X E F r s v = 0) : Q F r s v = 0 := by
  obtain ⟨c, hc, he⟩ := X_eq_Q hEF hHF hFF hE hH r s hr
  rw [he, smul_eq_zero] at h; exact h.resolve_left hc

include hEF hHF hFF in
theorem X_zero_of_Q {v : V} (hE : ∀ s, E s v = 0) (hH : ∀ p, 1 ≤ p → H p v = 0) {r s : ℕ}
    (hr : 1 ≤ r) (h : Q F r s v = 0) : X E F r s v = 0 := by
  obtain ⟨c, _, he⟩ := X_eq_Q hEF hHF hFF hE hH r s hr
  rw [he, h, smul_zero]

include hEF hHF hHE hFF hEE in
/-- **The iterated shift (CV Cor. 6.6)**: `F_b^n v` satisfies the relations of region `T − 2n`. -/
theorem shift_iter (k T b : ℕ) (hb : k + 1 ≤ b) : ∀ n (v : V), (∀ s, E s v = 0) →
    (∀ p, 1 ≤ p → H p v = 0) → (∀ q, b + 1 ≤ q → F q v = 0) →
    (∀ r s, 1 ≤ r → 1 + r * k + T ≤ s + r → X E F r s v = 0) →
    ∀ r s, 1 ≤ r → 1 + r * k + T ≤ s + r + 2 * n → X E F r s ((F b ^ n) v) = 0
  | 0, v, _, _, _, hrel, r, s, hr, hs => by simpa using hrel r s hr hs
  | n + 1, v, hE, hH, hF, hrel, r, s, hr, hs => by
      have ih := shift_iter k T b hb n v hE hH hF hrel
      obtain ⟨hE', hH', hF'⟩ : (∀ s, E s ((F b ^ n) v) = 0) ∧ (∀ p, 1 ≤ p → H p ((F b ^ n) v) = 0) ∧
          (∀ q, b + 1 ≤ q → F q ((F b ^ n) v) = 0) := by
        clear ih hrel hs
        induction n with
        | zero => exact ⟨hE, hH, hF⟩
        | succ n ihn =>
            obtain ⟨a1, a2, a3⟩ := ihn
            have := hw_Fb hEF hHF hFF (by omega) a1 a2 a3
            rw [pow_succ', Module.End.mul_apply]; exact this
      rw [pow_succ', Module.End.mul_apply]
      exact shift_lemma hEF hHF hHE hFF hEE hE' hH' k T (2 * n) (fun r s hr hs => ih r s hr hs) b hb
        r s hr (by omega)

/-! ## Intertwining maps -/

section Map

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {F' : ℕ → Module.End ℂ W} (π : V →ₗ[ℂ] W)
  (hπ : ∀ k w, π (F k w) = F' k (π w))
include hπ

theorem map_Fw : ∀ (l : List ℕ) (w : V), π (ECalc.Fw F l w) = ECalc.Fw F' l (π w)
  | [], w => rfl
  | (k :: l), w => by
      change π (F k (ECalc.Fw F l w)) = F' k (ECalc.Fw F' l (π w))
      rw [hπ, map_Fw l w]

theorem map_Q : ∀ (r s : ℕ) (w : V), π (Q F r s w) = Q F' r s (π w)
  | 0, s, w => by rw [Q_zero_r, Q_zero_r]; split_ifs <;> simp
  | r + 1, s, w => by
      rw [Q_succ, Q_succ, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_sum, Finset.sum_apply,
        map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Module.End.mul_apply, Module.End.mul_apply, hπ, map_Q r x.2 w]

theorem map_Fspan (w : V) : (Fspan F w).map π = Fspan F' (π w) := by
  rw [Fspan, Fspan, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨l, rfl⟩, rfl⟩; exact ⟨l, (map_Fw π hπ l w).symm⟩
  · rintro ⟨l, rfl⟩; exact ⟨_, ⟨l, rfl⟩, map_Fw π hπ l w⟩

end Map

end

end VOA.DeligneAudit.CVsl2
