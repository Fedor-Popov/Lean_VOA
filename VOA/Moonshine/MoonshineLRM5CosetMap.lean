import VOA.Moonshine.MoonshineLRM5Cosets

/-!
# Hecke cosets under `S`: the coset involution

Index the Hecke cosets of order `M` by `⟨a, b⟩` with `a ∣ M` and `b < d = M/a`. Put
`g = gcd(b, d)`, `d₁ = d/g`, `b₁ = b/g`, and let `r = negInvMod b₁ d₁` be the residue in
`[0, d₁)` with `r b₁ ≡ −1 (mod d₁)`. The map `σ ⟨a, b⟩ = ⟨g, a r⟩` (`cosetS`):
* sends cosets to cosets (`cosetS_mem`);
* is an involution (`cosetS_cosetS`): `gcd(a r, a d₁) = a`, and the inverse residue of `r` is `b₁`;
* satisfies `f(A (S•τ)) = f(σ(A) τ)` for `SL₂(ℤ)`-invariant `f` (`heckeVal_S_smul`, from the
  point identity `heckePoint_S_smul_eq` with `x = −r`, `y = (1 + r b₁)/d₁`, `t = 0`).

Hence the Hecke sum of an `SL₂(ℤ)`-invariant function is `S`-invariant (`heckeSumOf_S_smul`). With
`T`-invariance (`MoonshineLRM5Invariance`) it is `SL₂(ℤ)`-invariant (`qHeckeSum_smul`).
-/

namespace VOA.Moonshine.ConwayNorton.M8

open UpperHalfPlane Real
open scoped MatrixGroups

/-! ### The inverse residue -/

/-- The residue `r ∈ [0, d₁)` with `r b₁ ≡ −1 (mod d₁)` (for `b₁` prime to `d₁`). -/
noncomputable def negInvMod (b₁ d₁ : ℕ) : ℕ :=
  (-(Nat.gcdA b₁ d₁) % (d₁ : ℤ)).toNat

theorem negInvMod_cast (b₁ d₁ : ℕ) (hd₁ : 0 < d₁) :
    (negInvMod b₁ d₁ : ℤ) = -(Nat.gcdA b₁ d₁) % (d₁ : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hd₁.ne'))

theorem negInvMod_lt (b₁ d₁ : ℕ) (hd₁ : 0 < d₁) : negInvMod b₁ d₁ < d₁ := by
  have h := Int.emod_lt_of_pos (-(Nat.gcdA b₁ d₁)) (by exact_mod_cast hd₁ : (0 : ℤ) < d₁)
  rw [← negInvMod_cast b₁ d₁ hd₁] at h
  exact_mod_cast h

theorem dvd_negInvMod_mul_add_one {b₁ d₁ : ℕ} (hd₁ : 0 < d₁) (hcop : Nat.Coprime b₁ d₁) :
    (d₁ : ℤ) ∣ (negInvMod b₁ d₁ : ℤ) * b₁ + 1 := by
  have hbez : (1 : ℤ) = b₁ * Nat.gcdA b₁ d₁ + d₁ * Nat.gcdB b₁ d₁ := by
    have := Nat.gcd_eq_gcd_ab b₁ d₁
    rwa [hcop.gcd_eq_one, Nat.cast_one] at this
  rw [negInvMod_cast b₁ d₁ hd₁, Int.emod_def]
  refine ⟨Nat.gcdB b₁ d₁ - (-(Nat.gcdA b₁ d₁) / (d₁ : ℤ)) * b₁, ?_⟩
  linear_combination hbez

/-- Uniqueness of the inverse residue. -/
theorem eq_negInvMod {r b₁ d₁ : ℕ} (hd₁ : 0 < d₁) (hcop : Nat.Coprime b₁ d₁) (hr : r < d₁)
    (hdvd : (d₁ : ℤ) ∣ (r : ℤ) * b₁ + 1) : r = negInvMod b₁ d₁ := by
  have h2 := dvd_negInvMod_mul_add_one hd₁ hcop
  have h3 : (d₁ : ℤ) ∣ ((r : ℤ) - negInvMod b₁ d₁) * b₁ := by
    have := dvd_sub hdvd h2
    rwa [show (r : ℤ) * b₁ + 1 - ((negInvMod b₁ d₁ : ℤ) * b₁ + 1) =
      ((r : ℤ) - negInvMod b₁ d₁) * b₁ by ring] at this
  have hcopZ : IsCoprime (d₁ : ℤ) (b₁ : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr hcop.symm
  have h4 : (d₁ : ℤ) ∣ (r : ℤ) - negInvMod b₁ d₁ := hcopZ.dvd_of_dvd_mul_right h3
  have hlt := negInvMod_lt b₁ d₁ hd₁
  obtain ⟨k, hk⟩ := h4
  have : k = 0 := by
    by_contra hk0
    rcases lt_or_gt_of_ne hk0 with h | h
    · have : (d₁ : ℤ) * k ≤ -(d₁ : ℤ) := by nlinarith
      omega
    · have : (d₁ : ℤ) ≤ (d₁ : ℤ) * k := by nlinarith
      omega
  subst this
  omega

/-- A residue `r` with `r b₁ ≡ −1 (mod d₁)` is prime to `d₁`. -/
theorem coprime_of_dvd_mul_add_one {r b₁ d₁ : ℕ} (hdvd : (d₁ : ℤ) ∣ (r : ℤ) * b₁ + 1) :
    Nat.Coprime r d₁ := by
  rw [← Nat.isCoprime_iff_coprime]
  obtain ⟨k, hk⟩ := hdvd
  exact ⟨-(b₁ : ℤ), k, by linear_combination -hk⟩

/-! ### The coset map -/

/-- The Hecke cosets of order `M`: pairs `⟨a, b⟩` with `a ∣ M` and `b < M/a`. -/
def heckeCosets (M : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  M.divisors.sigma fun a => Finset.range (M / a)

/-- The coset map `σ ⟨a, b⟩ = ⟨gcd(b, d), a · r⟩`, `d = M/a`, `r = negInvMod (b/g) (d/g)`. -/
noncomputable def cosetS (M : ℕ) (x : Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ :=
  ⟨Nat.gcd x.2 (M / x.1),
    x.1 * negInvMod (x.2 / Nat.gcd x.2 (M / x.1)) (M / x.1 / Nat.gcd x.2 (M / x.1))⟩

/-- The arithmetic of one coset: `d = g d₁`, `b = g b₁`, `M/g = a d₁`, `b₁` prime to `d₁`. -/
structure CosetData (M a b : ℕ) where
  ha : 0 < a
  hadvd : a ∣ M
  hM : 0 < M
  hb : b < M / a

theorem CosetData.d_pos {M a b : ℕ} (h : CosetData M a b) : 0 < M / a :=
  Nat.div_pos (Nat.le_of_dvd h.hM h.hadvd) h.ha

theorem CosetData.g_pos {M a b : ℕ} (h : CosetData M a b) : 0 < Nat.gcd b (M / a) :=
  Nat.gcd_pos_of_pos_right _ h.d_pos

theorem CosetData.d₁_pos {M a b : ℕ} (h : CosetData M a b) :
    0 < M / a / Nat.gcd b (M / a) :=
  Nat.div_pos (Nat.gcd_le_right _ h.d_pos) h.g_pos

theorem CosetData.coprime {M a b : ℕ} (h : CosetData M a b) :
    Nat.Coprime (b / Nat.gcd b (M / a)) (M / a / Nat.gcd b (M / a)) :=
  Nat.coprime_div_gcd_div_gcd h.g_pos

theorem CosetData.b₁_lt {M a b : ℕ} (h : CosetData M a b) :
    b / Nat.gcd b (M / a) < M / a / Nat.gcd b (M / a) :=
  Nat.div_lt_div_of_lt_of_dvd (Nat.gcd_dvd_right _ _) h.hb

theorem CosetData.g_mul_d₁ {M a b : ℕ} (_h : CosetData M a b) :
    Nat.gcd b (M / a) * (M / a / Nat.gcd b (M / a)) = M / a :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)

theorem CosetData.g_mul_b₁ {M a b : ℕ} (_h : CosetData M a b) :
    Nat.gcd b (M / a) * (b / Nat.gcd b (M / a)) = b :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)

theorem CosetData.M_div_g {M a b : ℕ} (h : CosetData M a b) :
    M / Nat.gcd b (M / a) = a * (M / a / Nat.gcd b (M / a)) := by
  have hM : M = Nat.gcd b (M / a) * (a * (M / a / Nat.gcd b (M / a))) := by
    have h1 : a * (M / a) = M := Nat.mul_div_cancel' h.hadvd
    have h2 := h.g_mul_d₁
    calc M = a * (M / a) := h1.symm
      _ = a * (Nat.gcd b (M / a) * (M / a / Nat.gcd b (M / a))) := by rw [h2]
      _ = _ := by ring
  exact Nat.div_eq_of_eq_mul_right h.g_pos hM

theorem cosetData_of_mem {M : ℕ} {x : Σ _ : ℕ, ℕ} (hx : x ∈ heckeCosets M) :
    CosetData M x.1 x.2 := by
  obtain ⟨ha, hb⟩ := Finset.mem_sigma.mp hx
  exact ⟨Nat.pos_of_mem_divisors ha, Nat.dvd_of_mem_divisors ha,
    Nat.pos_of_ne_zero (Nat.mem_divisors.mp ha).2, Finset.mem_range.mp hb⟩

theorem cosetS_mem {M : ℕ} {x : Σ _ : ℕ, ℕ} (hx : x ∈ heckeCosets M) :
    cosetS M x ∈ heckeCosets M := by
  have h := cosetData_of_mem hx
  refine Finset.mem_sigma.mpr ⟨?_, Finset.mem_range.mpr ?_⟩
  · refine Nat.mem_divisors.mpr ⟨?_, h.hM.ne'⟩
    exact (Nat.gcd_dvd_right _ _).trans (Nat.div_dvd_of_dvd h.hadvd)
  · simp only [cosetS]
    rw [h.M_div_g]
    exact Nat.mul_lt_mul_of_pos_left (negInvMod_lt _ _ h.d₁_pos) h.ha

/-- **`σ` is an involution** on the Hecke cosets. -/
theorem cosetS_cosetS {M : ℕ} {x : Σ _ : ℕ, ℕ} (hx : x ∈ heckeCosets M) :
    cosetS M (cosetS M x) = x := by
  have h := cosetData_of_mem hx
  obtain ⟨a, b⟩ := x
  simp only at h
  simp only [cosetS]
  set g := Nat.gcd b (M / a) with hg
  set d₁ := M / a / g with hd₁
  set b₁ := b / g with hb₁
  set r := negInvMod b₁ d₁ with hr
  have hd₁pos : 0 < d₁ := h.d₁_pos
  have hrdvd : (d₁ : ℤ) ∣ (r : ℤ) * b₁ + 1 := dvd_negInvMod_mul_add_one hd₁pos h.coprime
  have hrcop : Nat.Coprime r d₁ := coprime_of_dvd_mul_add_one hrdvd
  have hMg : M / g = a * d₁ := h.M_div_g
  have hgb : g * b₁ = b := h.g_mul_b₁
  have hb₁lt : b₁ < d₁ := h.b₁_lt
  have hg' : Nat.gcd (a * r) (M / g) = a := by
    rw [hMg, Nat.gcd_mul_left, hrcop.gcd_eq_one, mul_one]
  have hd₁' : M / g / a = d₁ := by rw [hMg, Nat.mul_div_cancel_left _ h.ha]
  have hr' : a * r / a = r := Nat.mul_div_cancel_left _ h.ha
  have hinv : negInvMod r d₁ = b₁ := by
    symm
    refine eq_negInvMod hd₁pos hrcop hb₁lt ?_
    rwa [mul_comm]
  rw [hg', hd₁', hr', hinv, hgb]

/-! ### `S`-invariance of the Hecke sum -/

/-- The value `f((aτ + b)/d)` (zero unless `a, d > 0`). -/
noncomputable def heckeVal (f : ℍ → ℂ) (a d b : ℕ) (τ : ℍ) : ℂ :=
  if h : 0 < a ∧ 0 < d then f (heckePoint a d b h.1 h.2 τ) else 0

/-- The Hecke sum `Σ_{a ∣ M} Σ_{b < M/a} f((aτ+b)/(M/a))` of a function `f` on `ℍ`. -/
noncomputable def heckeSumOf (f : ℍ → ℂ) (M : ℕ) (τ : ℍ) : ℂ :=
  ∑ x ∈ heckeCosets M, heckeVal f x.1 (M / x.1) x.2 τ

theorem qHeckeSum_eq_heckeSumOf (c : ℕ → ℂ) (M : ℕ) (τ : ℍ) :
    qHeckeSum c M τ = heckeSumOf (qSeriesFun c) M τ := by
  rw [qHeckeSum, heckeSumOf, heckeCosets, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hapos := Nat.pos_of_mem_divisors ha
  have hd := Nat.div_pos (Nat.divisor_le ha) hapos
  rw [qHeckeBlock_of_pos c a (M / a) hapos hd]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [heckeVal, dif_pos ⟨hapos, hd⟩]

/-- `f(A (S•τ)) = f(σ(A) τ)` for an `SL₂(ℤ)`-invariant `f`. -/
theorem heckeVal_S_smul {f : ℍ → ℂ} (hf : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ) {M : ℕ}
    {x : Σ _ : ℕ, ℕ} (hx : x ∈ heckeCosets M) (τ : ℍ) :
    heckeVal f x.1 (M / x.1) x.2 (ModularGroup.S • τ) =
      heckeVal f (cosetS M x).1 (M / (cosetS M x).1) (cosetS M x).2 τ := by
  have h := cosetData_of_mem hx
  obtain ⟨a, b⟩ := x
  simp only at h
  simp only [cosetS]
  set g := Nat.gcd b (M / a) with hg
  set d₁ := M / a / g with hd₁
  set b₁ := b / g with hb₁
  set r := negInvMod b₁ d₁ with hr
  have hd₁pos : 0 < d₁ := h.d₁_pos
  have hgpos : 0 < g := h.g_pos
  have hdpos : 0 < M / a := h.d_pos
  have hgd : g * d₁ = M / a := h.g_mul_d₁
  have hgb : g * b₁ = b := h.g_mul_b₁
  have hrdvd : (d₁ : ℤ) ∣ (r : ℤ) * b₁ + 1 := dvd_negInvMod_mul_add_one hd₁pos h.coprime
  obtain ⟨y, hy⟩ := hrdvd
  have hMg : M / g = a * d₁ := h.M_div_g
  have hepos : 0 < M / g := by rw [hMg]; exact Nat.mul_pos h.ha hd₁pos
  rw [heckeVal, dif_pos ⟨h.ha, hdpos⟩, heckeVal, dif_pos ⟨hgpos, hepos⟩]
  have hbez : (-(r : ℤ)) * b₁ + y * d₁ = 1 := by linear_combination -hy
  rw [heckePoint_S_smul_eq a (M / a) b g (M / g) (a * r) h.ha hdpos hgpos hepos b₁ d₁ (-r) y 0
    hbez (by exact_mod_cast hgd.symm) (by exact_mod_cast hgb.symm)
    (by rw [hMg]; push_cast; ring) (by push_cast; ring), hf]

/-- **`S`-invariance of the Hecke sum** of an `SL₂(ℤ)`-invariant function. -/
theorem heckeSumOf_S_smul {f : ℍ → ℂ} (hf : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ)
    (M : ℕ) (τ : ℍ) : heckeSumOf f M (ModularGroup.S • τ) = heckeSumOf f M τ := by
  rw [heckeSumOf, heckeSumOf, Finset.sum_congr rfl fun x hx => heckeVal_S_smul hf hx τ]
  exact Finset.sum_nbij' (cosetS M) (cosetS M) (fun x hx => cosetS_mem hx)
    (fun x hx => cosetS_mem hx) (fun x hx => cosetS_cosetS hx) (fun x hx => cosetS_cosetS hx)
    (fun _ _ => rfl)

/-- **`SL₂(ℤ)`-invariance of the Hecke sum** `R_M` of an `SL₂(ℤ)`-invariant `q`-series. -/
theorem qHeckeSum_smul {c : ℕ → ℂ}
    (hf : ∀ (γ : SL(2, ℤ)) (τ : ℍ), qSeriesFun c (γ • τ) = qSeriesFun c τ) (M : ℕ)
    (γ : SL(2, ℤ)) (τ : ℍ) : qHeckeSum c M (γ • τ) = qHeckeSum c M τ := by
  refine smul_invariant_of_S_T (fun τ => ?_) (fun τ => qHeckeSum_T_smul c M τ) γ τ
  rw [qHeckeSum_eq_heckeSumOf, qHeckeSum_eq_heckeSumOf, heckeSumOf_S_smul hf]

end VOA.Moonshine.ConwayNorton.M8
