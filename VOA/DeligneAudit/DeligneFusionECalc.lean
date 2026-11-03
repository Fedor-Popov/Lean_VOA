import VOA.DeligneAudit.DeligneFusionCLGT

/-!
# The `E`-calculus for `sl₂[t]` (Chari–Loktev 3.4.2–3.4.4 at the vector level)

For an `sl₂[t]`-current triple `E s, H p, F k` and a vector `y` with `E s y = 0` (all `s`) and
`H p y = 0` (`p ≥ 1`), every `F`-word applied to `y` is a combination of `E`-words (positive modes)
applied to `F₀^m y`, with the bigrading tracked (`fword_mem_EW`).
-/

namespace VOA.DeligneAudit.ECalc

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (E H F : ℕ → Module.End ℂ V)

/-- The `E`-word `E_{s₁} ⋯ E_{s_k}`. -/
def Ew : List ℕ → Module.End ℂ V
  | [] => 1
  | (s :: l) => E s * Ew l

/-- The `F`-word `F_{k₁} ⋯ F_{k_j}`. -/
def Fw : List ℕ → Module.End ℂ V
  | [] => 1
  | (k :: l) => F k * Fw l

/-- `EW ℓ d`: span of `E-word(l) F₀^{ℓ+|l|} y` with positive modes and `Σ l = d`. -/
def EW (y : V) (ℓ d : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ l : List ℕ, (∀ s ∈ l, 1 ≤ s) ∧ l.sum = d ∧
    v = Ew E l ((F 0 ^ (ℓ + l.length)) y)}

variable {E H F}

theorem Ew_append (l l' : List ℕ) : Ew E (l ++ l') = Ew E l * Ew E l' := by
  induction l with
  | nil => simp [Ew]
  | cons s l ih => simp [Ew, ih, mul_assoc]

/-- `E_s` maps `EW (ℓ+1) d` into `EW ℓ (d+s)`. -/
theorem E_EW (y : V) {s : ℕ} (hs : 1 ≤ s) (ℓ d : ℕ) {v : V} (hv : v ∈ EW E F y (ℓ + 1) d) :
    E s v ∈ EW E F y ℓ (d + s) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, hl, hd, rfl⟩ := hv
      refine Submodule.subset_span ⟨s :: l, ?_, ?_, ?_⟩
      · intro t ht; rcases List.mem_cons.mp ht with rfl | ht
        · exact hs
        · exact hl t ht
      · simp [hd, add_comm]
      · simp only [Ew, Module.End.mul_apply, List.length_cons]
        rw [show ℓ + (l.length + 1) = ℓ + 1 + l.length by ring]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

variable (hEF : ∀ s k, E s * F k - F k * E s = H (s + k))
  (hHF : ∀ p k, H p * F k - F k * H p = (-2 : ℂ) • F (p + k))
  (hHE : ∀ p q, H p * E q - E q * H p = (2 : ℂ) • E (p + q))
  (hFF : ∀ i j, F i * F j = F j * F i)
  {y : V} (hE : ∀ s, E s y = 0) (hH : ∀ p, 1 ≤ p → H p y = 0)

include hHF hFF hH in
theorem H_F0pow (k : ℕ) (hk : 1 ≤ k) :
    ∀ j, H k ((F 0 ^ j) y) = (-(2 * j : ℕ) : ℂ) • F k ((F 0 ^ (j - 1)) y)
  | 0 => by simp [hH k hk]
  | j + 1 => by
      have h1 := congrArg (fun T => T ((F 0 ^ j) y)) (hHF k 0)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, add_zero] at h1
      rw [pow_succ', Module.End.mul_apply, sub_eq_iff_eq_add.mp h1, H_F0pow k hk j, map_smul]
      rcases j with _ | j
      · simp
      · rw [show j + 1 + 1 - 1 = j + 1 by omega, show j + 1 - 1 = j by omega,
          ← Module.End.mul_apply (F 0) (F k), hFF 0 k, Module.End.mul_apply, ← Module.End.mul_apply (F 0),
          ← pow_succ']
        rw [← add_smul]; congr 1; push_cast; ring

include hEF hHF hFF hE hH in
theorem E_F0pow (k : ℕ) (hk : 1 ≤ k) :
    ∀ n, E k ((F 0 ^ n) y) = (-((n * (n - 1) : ℕ) : ℂ)) • F k ((F 0 ^ (n - 2)) y)
  | 0 => by simp [hE k]
  | n + 1 => by
      have h1 := congrArg (fun T => T ((F 0 ^ n) y)) (hEF k 0)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, add_zero] at h1
      rw [pow_succ', Module.End.mul_apply, sub_eq_iff_eq_add.mp h1, E_F0pow k hk n, map_smul,
        H_F0pow hHF hFF hH k hk n]
      rcases n with _ | n
      · simp
      · rcases n with _ | n
        · simp
        · rw [show n + 2 - 2 = n by omega, show n + 2 + 1 - 2 = n + 1 by omega,
            show n + 2 - 1 = n + 1 by omega, ← Module.End.mul_apply (F 0) (F k), hFF 0 k,
            Module.End.mul_apply, ← Module.End.mul_apply (F 0), ← pow_succ']
          rw [← add_smul]; congr 1; push_cast; ring

include hEF hHF hFF hE hH in
/-- `F_k F₀^m y ∈ EW` (base case). -/
theorem F_F0pow_mem (k m : ℕ) : F k ((F 0 ^ m) y) ∈ EW E F y (m + 1) k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine Submodule.subset_span ⟨[], by simp, rfl, ?_⟩
    simp [Ew, pow_succ', Module.End.mul_apply]
  · have h2 := E_F0pow hEF hHF hFF hE hH k hk (m + 2)
    rw [show m + 2 - 2 = m by omega] at h2
    have hc : (-(((m + 2) * (m + 2 - 1) : ℕ) : ℂ)) ≠ 0 := by
      rw [neg_ne_zero]
      exact_mod_cast (Nat.mul_ne_zero (by omega) (by omega) : (m + 2) * (m + 2 - 1) ≠ 0)
    have : F k ((F 0 ^ m) y) =
        (-(((m + 2) * (m + 2 - 1) : ℕ) : ℂ))⁻¹ • E k ((F 0 ^ (m + 2)) y) := by
      rw [h2, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨[k], by simpa using hk, by simp, ?_⟩)
    simp [Ew, show m + 1 + 1 = m + 2 by ring]

include hEF hHF hHE hFF hE hH in
/-- `H_p` (`p ≥ 1`) maps `EW ℓ d` into `EW ℓ (d+p)`. -/
theorem H_EW {p : ℕ} (hp : 1 ≤ p) : ∀ (l : List ℕ), (∀ s ∈ l, 1 ≤ s) → ∀ ℓ,
    H p (Ew E l ((F 0 ^ (ℓ + l.length)) y)) ∈ EW E F y ℓ (l.sum + p)
  | [], _, ℓ => by
      simp only [Ew, Module.End.one_apply, List.length_nil, add_zero, List.sum_nil, zero_add]
      rw [H_F0pow hHF hFF hH p hp]
      rcases ℓ with _ | ℓ
      · simp
      · refine Submodule.smul_mem _ _ ?_
        have := F_F0pow_mem hEF hHF hFF hE hH p ℓ
        simpa using this
  | (s :: l), hl, ℓ => by
      have hs := hl s List.mem_cons_self
      have hl' : ∀ t ∈ l, 1 ≤ t := fun t ht => hl t (List.mem_cons_of_mem _ ht)
      have hcomm := congrArg (fun T => T (Ew E l ((F 0 ^ (ℓ + (s :: l).length)) y))) (hHE p s)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at hcomm
      simp only [Ew, Module.End.mul_apply]
      rw [sub_eq_iff_eq_add.mp hcomm]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) ?_
      · refine Submodule.subset_span ⟨(p + s) :: l, ?_, by simp; ring, ?_⟩
        · intro t ht; rcases List.mem_cons.mp ht with rfl | ht
          · omega
          · exact hl' t ht
        · simp [Ew]
      · have ih := H_EW hp l hl' (ℓ + 1)
        rw [show ℓ + 1 + l.length = ℓ + (s :: l).length by simp; ring] at ih
        have := E_EW y hs ℓ (l.sum + p) ih
        convert this using 2; simp; ring

include hEF hHF hHE hFF hE hH in
/-- `F_k` maps `EW ℓ d` into `EW (ℓ+1) (d+k)`. -/
theorem F_EW (k : ℕ) : ∀ (l : List ℕ), (∀ s ∈ l, 1 ≤ s) → ∀ ℓ,
    F k (Ew E l ((F 0 ^ (ℓ + l.length)) y)) ∈ EW E F y (ℓ + 1) (l.sum + k)
  | [], _, ℓ => by
      simpa [Ew] using F_F0pow_mem hEF hHF hFF hE hH k ℓ
  | (s :: l), hl, ℓ => by
      have hs := hl s List.mem_cons_self
      have hl' : ∀ t ∈ l, 1 ≤ t := fun t ht => hl t (List.mem_cons_of_mem _ ht)
      set X := Ew E l ((F 0 ^ (ℓ + (s :: l).length)) y)
      have hcomm := congrArg (fun T => T X) (hEF s k)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at hcomm
      simp only [Ew, Module.End.mul_apply]
      rw [show F k (E s X) = E s (F k X) - H (s + k) X by rw [← hcomm]; abel]
      refine Submodule.sub_mem _ ?_ ?_
      · have ih := F_EW k l hl' (ℓ + 1)
        rw [show ℓ + 1 + l.length = ℓ + (s :: l).length by simp; ring] at ih
        have := E_EW y hs (ℓ + 1) (l.sum + k) ih
        convert this using 2; simp; ring
      · have := H_EW hEF hHF hHE hFF hE hH (p := s + k) (by omega) l hl' (ℓ + 1)
        rw [show ℓ + 1 + l.length = ℓ + (s :: l).length by simp; ring] at this
        convert this using 2; simp; ring

include hEF hHF hHE hFF hE hH in
/-- **CL Cor. 3.4.4 at the vector level**: every `F`-word applied to `y` is a combination of
positive `E`-words applied to `F₀^m y`, bigrading preserved. -/
theorem fword_mem_EW : ∀ l : List ℕ, Fw F l y ∈ EW E F y l.length l.sum
  | [] => Submodule.subset_span ⟨[], by simp, rfl, by simp [Ew, Fw]⟩
  | (k :: l) => by
      have ih := fword_mem_EW l
      simp only [Fw, Module.End.mul_apply, List.length_cons, List.sum_cons]
      generalize Fw F l y = v at ih
      induction ih using Submodule.span_induction with
      | mem v hv =>
          obtain ⟨l', hl', hd, rfl⟩ := hv
          have := F_EW hEF hHF hHE hFF hE hH k l' hl' l.length
          rwa [hd, add_comm l.sum k] at this
      | zero => simp
      | add x z _ _ hx hz => rw [map_add]; exact Submodule.add_mem _ hx hz
      | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

end

end VOA.DeligneAudit.ECalc
