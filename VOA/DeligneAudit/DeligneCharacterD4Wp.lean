/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.JacobiTriple

/-!
# Lattice series and the factorisation of products of two theta functions (layer 1)

Toward `D4SchurEqE4` (the elliptic evaluation of the D₄ Schur index), via the classical identity
`℘'(z) = -σ(2z)/σ(z)⁴` in theta form.

Here `L = ℚ[a^{±1}]` (`AddMonoidAlgebra ℚ ℤ`) and series live in `L⟦q⟧`.

* `lat S w`: the series `∑_n (∑_{i ∈ S n} w i) qⁿ`, and `lat_mul_fiber`: the product of two
  fibre series is the fibre series over pairs with additive exponent.
* `Psi = ∑_j (-1)^j a^j q^{j(j-1)/2}` (the Jacobi triple-product sum at `u = a`).
* Factorisations: `Psi² = φ₀ U₀ + φ₁ U₁`.
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4Wp

open PowerSeries VOA.QSeries VOA.QSeries.JTP

open scoped BigOperators

noncomputable section

/-! ## Lattice (fibre) series -/

section Lat

variable {R : Type*} [CommRing R]

/-- `∑_n (∑_{i ∈ S n} w i) qⁿ`. -/
def lat {ι : Type*} (S : ℕ → Finset ι) (w : ι → R) : PowerSeries R :=
  PowerSeries.mk fun n => ∑ i ∈ S n, w i

@[simp] theorem coeff_lat {ι : Type*} (S : ℕ → Finset ι) (w : ι → R) (n : ℕ) :
    coeff n (lat S w) = ∑ i ∈ S n, w i := coeff_mk _ _

/-- Fibres of an exponent function inside finite boxes. -/
def fib {ι : Type*} (box : ℕ → Finset ι) (E : ι → ℕ) (n : ℕ) : Finset ι :=
  (box n).filter fun i => E i = n

theorem mem_fib {ι : Type*} {box : ℕ → Finset ι} {E : ι → ℕ}
    (hbox : ∀ n i, E i ≤ n → i ∈ box n) {n : ℕ} {i : ι} : i ∈ fib box E n ↔ E i = n := by
  rw [fib, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hbox n i h.le, h⟩⟩

/-- **Product of fibre series**: over pairs whose exponents add up. -/
theorem lat_mul_fiber {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (box : ℕ → Finset ι) (E : ι → ℕ) (hbox : ∀ n i, E i ≤ n → i ∈ box n)
    (box' : ℕ → Finset κ) (E' : κ → ℕ) (hbox' : ∀ n i, E' i ≤ n → i ∈ box' n)
    (w : ι → R) (w' : κ → R) :
    lat (fib box E) w * lat (fib box' E') w' =
      lat (fib (fun n => box n ×ˢ box' n) (fun p => E p.1 + E' p.2)) (fun p => w p.1 * w' p.2) := by
  have hb2 : ∀ n (p : ι × κ), E p.1 + E' p.2 ≤ n → p ∈ box n ×ˢ box' n := fun n p hp =>
    Finset.mem_product.mpr ⟨hbox n _ (by omega), hbox' n _ (by omega)⟩
  ext n : 1
  rw [coeff_mul, coeff_lat]
  simp only [coeff_lat, Finset.sum_mul_sum]
  simp_rw [← Finset.sum_product' (f := fun i j => w i * w' j)]
  rw [← Finset.sum_sigma (Finset.antidiagonal n) (fun p => fib box E p.1 ×ˢ fib box' E' p.2)
    (fun x => w x.2.1 * w' x.2.2)]
  refine Finset.sum_nbij' (fun x => x.2) (fun p => ⟨(E p.1, E' p.2), p⟩) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_antidiagonal, Finset.mem_product] at hx
    rw [mem_fib hb2]
    rw [mem_fib hbox] at hx; rw [mem_fib hbox'] at hx
    dsimp only
    omega
  · intro p hp
    rw [mem_fib hb2] at hp
    simp only [Finset.mem_sigma, Finset.mem_antidiagonal, Finset.mem_product]
    exact ⟨hp, (mem_fib hbox).mpr rfl, (mem_fib hbox').mpr rfl⟩
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_antidiagonal, Finset.mem_product] at hx
    rw [mem_fib hbox] at hx; rw [mem_fib hbox'] at hx
    obtain ⟨⟨a, b⟩, ⟨i, k⟩⟩ := x
    simp only at hx ⊢
    rw [hx.2.1, hx.2.2]
  · intro p _; rfl
  · intro x _; rfl

theorem lat_map {S : Type*} [CommRing S] {ι : Type*} (φ : R →+* S) (F : ℕ → Finset ι) (w : ι → R) :
    PowerSeries.map φ (lat F w) = lat F (fun i => φ (w i)) := by
  ext n; simp [map_sum]

end Lat

/-! ## Integer exponents -/

/-- A nonnegative integer as a natural number. -/
def ez (z : ℤ) : ℕ := z.toNat

theorem ez_cast {z : ℤ} (hz : 0 ≤ z) : ((ez z : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz

theorem ez_eq_iff {z : ℤ} (hz : 0 ≤ z) (n : ℕ) : ez z = n ↔ z = n := by
  rw [ez]; omega

theorem ez_le_iff {z : ℤ} (hz : 0 ≤ z) (n : ℕ) : ez z ≤ n ↔ z ≤ n := by
  rw [ez]; omega

/-- The box `[-n-1, n+1]`. -/
def zbox (n : ℕ) : Finset ℤ := Finset.Icc (-(n : ℤ) - 1) (n + 1)

theorem mem_zbox {n : ℕ} {j : ℤ} : j ∈ zbox n ↔ -(n : ℤ) - 1 ≤ j ∧ j ≤ n + 1 := Finset.mem_Icc

/-- Any exponent with `|j| ≤ E j + 1` has its fibres inside `zbox`. -/
theorem zbox_of (E : ℤ → ℕ) (hE : ∀ j, j.natAbs ≤ E j + 1) :
    ∀ n j, E j ≤ n → j ∈ zbox n := by
  intro n j hj
  rw [mem_zbox]
  have := hE j
  omega

/-! ## The theta sum `Ψ` -/

/-- `ℚ[a^{±1}]`. -/
abbrev L := AddMonoidAlgebra ℚ ℤ

/-- The monomial `a^j`. -/
def mono (j : ℤ) : L := AddMonoidAlgebra.single j 1

theorem mono_mul (i j : ℤ) : mono i * mono j = mono (i + j) := by
  rw [mono, mono, mono, AddMonoidAlgebra.single_mul_single, one_mul]

theorem mono_zero : mono 0 = 1 := rfl

/-- `a` as a unit. -/
def ua : Lˣ := ⟨mono 1, mono (-1), by rw [mono_mul]; simp [mono_zero], by rw [mono_mul]; simp [mono_zero]⟩

theorem val_ua_zpow (j : ℤ) : ((ua ^ j : Lˣ) : L) = mono j := by
  induction j using Int.induction_on with
  | zero => simp [mono_zero]
  | succ i ih => rw [zpow_add_one, Units.val_mul, ih]; exact mono_mul i 1
  | pred i ih =>
      rw [zpow_sub_one, Units.val_mul, ih]
      show mono (-i) * mono (-1) = mono (-i - 1)
      rw [mono_mul]; ring_nf

theorem pentExp_add_iff (j k : ℤ) (n : ℕ) :
    pentExp j + pentExp k = n ↔ j * (j - 1) + k * (k - 1) = 2 * n := by
  have h1 := two_mul_cast_pentExp j
  have h2 := two_mul_cast_pentExp k
  omega

/-- `Ψ = ∑_j (-1)^j a^j q^{j(j-1)/2}`. -/
def Psi : PowerSeries L := lat (fib zbox pentExp) fun j => negSign j * mono j

theorem Psi_eq_tripleSum : Psi = tripleSum ua := by
  ext n : 1
  rw [Psi, coeff_lat, tripleSum, coeff_zSeries, fib, zbox]
  exact Finset.sum_congr rfl fun j _ => by rw [tripleCoeff, val_ua_zpow]

/-- **Jacobi triple product** for `Ψ`. -/
theorem Psi_eq_prod : (1 - PowerSeries.C (mono 1)) * infProd (tripleFactor ua) = Psi := by
  rw [Psi_eq_tripleSum]; exact jacobiTriple ua

theorem hbox_pent : ∀ n j, pentExp j ≤ n → j ∈ zbox n := zbox_of pentExp natAbs_le_pentExp

/-! ## The factorisation `Ψ² = φ₀U₀ + φ₁U₁` -/

/-- `e ↦ e²`. -/
def E0 (e : ℤ) : ℕ := ez (e * e)
/-- `e ↦ e² + e`. -/
def E1 (e : ℤ) : ℕ := ez (e * e + e)
/-- `m ↦ m² - m`. -/
def EU0 (m : ℤ) : ℕ := ez (m * m - m)

theorem E0_cast (e : ℤ) : (E0 e : ℤ) = e * e := ez_cast (by nlinarith)
theorem E1_cast (e : ℤ) : (E1 e : ℤ) = e * e + e := ez_cast (by nlinarith)
theorem EU0_cast (m : ℤ) : (EU0 m : ℤ) = m * m - m := ez_cast (by nlinarith)

theorem hbox_E0 : ∀ n j, E0 j ≤ n → j ∈ zbox n :=
  zbox_of E0 fun j => by have := E0_cast j; zify; rw [this]; cases abs_cases j <;> nlinarith
theorem hbox_E1 : ∀ n j, E1 j ≤ n → j ∈ zbox n :=
  zbox_of E1 fun j => by have := E1_cast j; zify; rw [this]; cases abs_cases j <;> nlinarith
theorem hbox_EU0 : ∀ n j, EU0 j ≤ n → j ∈ zbox n :=
  zbox_of EU0 fun j => by have := EU0_cast j; zify; rw [this]; cases abs_cases j <;> nlinarith

/-- `φ₀ = ∑_e q^{e²}`. -/
def phi0 : PowerSeries L := lat (fib zbox E0) fun _ => 1
/-- `φ₁ = ∑_e q^{e² + e}`. -/
def phi1 : PowerSeries L := lat (fib zbox E1) fun _ => 1
/-- `U₀ = ∑_m q^{m² - m} a^{2m}`. -/
def U0 : PowerSeries L := lat (fib zbox EU0) fun m => mono (2 * m)
/-- `U₁ = -∑_m q^{m²} a^{2m+1}`. -/
def U1 : PowerSeries L := lat (fib zbox E0) fun m => -mono (2 * m + 1)

theorem negSign_mul_mono (j k : ℤ) :
    negSign j * mono j * (negSign k * mono k) = negSign (j + k) * mono (j + k) := by
  rw [negSign_add, ← mono_mul]; ring

theorem negSign_two_mul (m : ℤ) : (negSign (2 * m) : L) = 1 := by
  rw [negSign_eq]; simp

theorem negSign_two_mul_add_one (m : ℤ) : (negSign (2 * m + 1) : L) = -1 := by
  rw [negSign_eq]; rw [if_neg (by omega)]

/-- **Pair factorisation**: a weight `h(j-k)` on pairs of theta indices splits by parity. -/
theorem pair_factor (h : ℤ → L) :
    lat (fib (fun n => zbox n ×ˢ zbox n) (fun p => pentExp p.1 + pentExp p.2))
        (fun p => h (p.1 - p.2) * (negSign (p.1 + p.2) * mono (p.1 + p.2))) =
      lat (fib zbox E0) (fun e => h (2 * e)) * U0 + lat (fib zbox E1) (fun e => h (2 * e + 1)) * U1 := by
  rw [U0, U1, lat_mul_fiber _ _ hbox_E0 _ _ hbox_EU0, lat_mul_fiber _ _ hbox_E1 _ _ hbox_E0]
  have hb2 : ∀ (E E' : ℤ → ℕ), (∀ n j, E j ≤ n → j ∈ zbox n) → (∀ n j, E' j ≤ n → j ∈ zbox n) →
      ∀ n (p : ℤ × ℤ), E p.1 + E' p.2 ≤ n → p ∈ zbox n ×ˢ zbox n := fun E E' h h' n p hp =>
    Finset.mem_product.mpr ⟨h n _ (by omega), h' n _ (by omega)⟩
  ext n : 1
  simp only [coeff_lat, map_add]
  rw [← Finset.sum_filter_add_sum_filter_not
    (fib (fun n => zbox n ×ˢ zbox n) (fun p => pentExp p.1 + pentExp p.2) n)
    (fun p : ℤ × ℤ => (p.1 + p.2) % 2 = 0)]
  congr 1
  · refine Finset.sum_nbij' (fun p => ((p.1 - p.2) / 2, (p.1 + p.2) / 2))
      (fun p => (p.2 + p.1, p.2 - p.1)) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨j, k⟩ hp
      rw [Finset.mem_filter, mem_fib (hb2 _ _ hbox_pent hbox_pent), pentExp_add_iff] at hp
      rw [mem_fib (hb2 _ _ hbox_E0 hbox_EU0)]
      dsimp only at hp ⊢
      zify; rw [E0_cast, EU0_cast]
      obtain ⟨h1, h2⟩ := hp
      have he : 2 * ((j - k) / 2) = j - k := by omega
      have hm : 2 * ((j + k) / 2) = j + k := by omega
      generalize (j - k) / 2 = e at he ⊢
      generalize (j + k) / 2 = m at hm ⊢
      have h4 : 4 * (e * e + (m * m - m)) = 4 * (n : ℤ) := by
        linear_combination (2 * e + (j - k)) * he + (2 * m + (j + k) - 2) * hm + 2 * h1
      omega
    · rintro ⟨e, m⟩ hp
      rw [mem_fib (hb2 _ _ hbox_E0 hbox_EU0)] at hp
      zify at hp; rw [E0_cast, EU0_cast] at hp
      rw [Finset.mem_filter, mem_fib (hb2 _ _ hbox_pent hbox_pent), pentExp_add_iff]
      dsimp only at hp ⊢
      exact ⟨by linear_combination 2 * hp, by omega⟩
    · rintro ⟨j, k⟩ hp
      rw [Finset.mem_filter] at hp
      dsimp only at hp ⊢
      ext <;> simp <;> omega
    · rintro ⟨e, m⟩ _
      ext <;> simp <;> omega
    · rintro ⟨j, k⟩ hp
      rw [Finset.mem_filter] at hp
      dsimp only at hp ⊢
      have hs : (negSign (j + k) : L) = 1 := by
        rw [show j + k = 2 * ((j + k) / 2) by omega]; exact negSign_two_mul _
      rw [hs, one_mul, show 2 * ((j - k) / 2) = j - k by omega,
        show 2 * ((j + k) / 2) = j + k by omega]
  · refine Finset.sum_nbij' (fun p => ((p.1 - p.2 - 1) / 2, (p.1 + p.2 - 1) / 2))
      (fun p => (p.2 + p.1 + 1, p.2 - p.1)) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨j, k⟩ hp
      rw [Finset.mem_filter, mem_fib (hb2 _ _ hbox_pent hbox_pent), pentExp_add_iff] at hp
      rw [mem_fib (hb2 _ _ hbox_E1 hbox_E0)]
      dsimp only at hp ⊢
      zify; rw [E1_cast, E0_cast]
      obtain ⟨h1, h2⟩ := hp
      have he : 2 * ((j - k - 1) / 2) = j - k - 1 := by omega
      have hm : 2 * ((j + k - 1) / 2) = j + k - 1 := by omega
      generalize (j - k - 1) / 2 = e at he ⊢
      generalize (j + k - 1) / 2 = m at hm ⊢
      have h4 : 4 * (e * e + e + m * m) = 4 * (n : ℤ) := by
        linear_combination (2 * e + (j - k - 1) + 2) * he + (2 * m + (j + k - 1)) * hm + 2 * h1
      omega
    · rintro ⟨e, m⟩ hp
      rw [mem_fib (hb2 _ _ hbox_E1 hbox_E0)] at hp
      zify at hp; rw [E1_cast, E0_cast] at hp
      rw [Finset.mem_filter, mem_fib (hb2 _ _ hbox_pent hbox_pent), pentExp_add_iff]
      dsimp only at hp ⊢
      exact ⟨by linear_combination 2 * hp, by omega⟩
    · rintro ⟨j, k⟩ hp
      rw [Finset.mem_filter] at hp
      dsimp only at hp ⊢
      ext <;> simp <;> omega
    · rintro ⟨e, m⟩ _
      ext <;> simp <;> omega
    · rintro ⟨j, k⟩ hp
      rw [Finset.mem_filter] at hp
      dsimp only at hp ⊢
      have hs : (negSign (j + k) : L) = -1 := by
        rw [show j + k = 2 * ((j + k - 1) / 2) + 1 by omega]; exact negSign_two_mul_add_one _
      rw [hs, neg_one_mul, mul_neg, show 2 * ((j - k - 1) / 2) + 1 = j - k by omega,
        show 2 * ((j + k - 1) / 2) + 1 = j + k by omega, mul_neg]

/-- **`Ψ² = φ₀U₀ + φ₁U₁`.** -/
theorem Psi_sq : Psi * Psi = phi0 * U0 + phi1 * U1 := by
  rw [Psi, lat_mul_fiber _ _ hbox_pent _ _ hbox_pent, phi0, phi1, ← pair_factor (fun _ => 1)]
  congr 1; funext p; rw [negSign_mul_mono, one_mul]

/-! ## Weight derivations -/

section WD

variable {G : Type*} [AddCommGroup G]

/-- The grading derivation `z^g ↦ w(g) z^g`. -/
def wd (w : G →+ ℤ) (f : AddMonoidAlgebra ℚ G) : AddMonoidAlgebra ℚ G :=
  f.sum fun g c => AddMonoidAlgebra.single g ((w g : ℚ) * c)

theorem wd_single (w : G →+ ℤ) (g : G) (c : ℚ) :
    wd w (AddMonoidAlgebra.single g c) = AddMonoidAlgebra.single g ((w g : ℚ) * c) :=
  Finsupp.sum_single_index (by rw [mul_zero, AddMonoidAlgebra.single_zero])

theorem wd_add (w : G →+ ℤ) (f f' : AddMonoidAlgebra ℚ G) : wd w (f + f') = wd w f + wd w f' :=
  Finsupp.sum_add_index' (fun _ => by rw [mul_zero, AddMonoidAlgebra.single_zero])
    (fun _ _ _ => by rw [mul_add, AddMonoidAlgebra.single_add])

theorem wd_zero (w : G →+ ℤ) : wd w 0 = 0 := Finsupp.sum_zero_index

theorem wd_neg (w : G →+ ℤ) (f : AddMonoidAlgebra ℚ G) : wd w (-f) = -wd w f := by
  have h := wd_add w f (-f)
  rw [add_neg_cancel, wd_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem wd_sub (w : G →+ ℤ) (f f' : AddMonoidAlgebra ℚ G) : wd w (f - f') = wd w f - wd w f' := by
  rw [sub_eq_add_neg, wd_add, wd_neg, ← sub_eq_add_neg]

theorem wd_mul (w : G →+ ℤ) (f f' : AddMonoidAlgebra ℚ G) :
    wd w (f * f') = wd w f * f' + f * wd w f' := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => rw [zero_mul, wd_zero, zero_mul, zero_mul, add_zero]
  | add f₁ f₂ h₁ h₂ => rw [add_mul, wd_add, h₁, h₂, wd_add]; ring
  | single a c =>
    induction f' using AddMonoidAlgebra.induction_linear with
    | zero => rw [mul_zero, wd_zero, mul_zero, mul_zero, add_zero]
    | add g₁ g₂ h₁ h₂ => rw [mul_add, wd_add, h₁, h₂, wd_add]; ring
    | single b d =>
      rw [AddMonoidAlgebra.single_mul_single, wd_single, wd_single, wd_single,
        AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single,
        ← AddMonoidAlgebra.single_add, map_add]
      congr 1; push_cast; ring

theorem wd_one (w : G →+ ℤ) : wd w 1 = 0 := by
  rw [AddMonoidAlgebra.one_def, wd_single, map_zero, Int.cast_zero, zero_mul,
    AddMonoidAlgebra.single_zero]

theorem wd_sum {ι : Type*} (w : G →+ ℤ) (s : Finset ι) (f : ι → AddMonoidAlgebra ℚ G) :
    wd w (∑ i ∈ s, f i) = ∑ i ∈ s, wd w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wd_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, wd_add, ih]

theorem wd_pow (w : G →+ ℤ) (f : AddMonoidAlgebra ℚ G) (hf : wd w f = 0) (n : ℕ) :
    wd w (f ^ n) = 0 := by
  induction n with
  | zero => rw [pow_zero, wd_one]
  | succ n ih => rw [pow_succ, wd_mul, ih, hf]; ring

theorem wd_negSign (w : G →+ ℤ) (j : ℤ) : wd w (negSign j) = 0 := by
  rw [negSign]; exact wd_pow w _ (by rw [wd_neg, wd_one, neg_zero]) _

theorem wd_negSign_mul (w : G →+ ℤ) (j : ℤ) (f : AddMonoidAlgebra ℚ G) :
    wd w (negSign j * f) = negSign j * wd w f := by
  rw [wd_mul, wd_negSign]; ring

/-- `wd` applied coefficientwise. -/
def DQ (w : G →+ ℤ) (F : PowerSeries (AddMonoidAlgebra ℚ G)) : PowerSeries (AddMonoidAlgebra ℚ G) :=
  PowerSeries.mk fun n => wd w (coeff n F)

@[simp] theorem coeff_DQ (w : G →+ ℤ) (F : PowerSeries (AddMonoidAlgebra ℚ G)) (n : ℕ) :
    coeff n (DQ w F) = wd w (coeff n F) := coeff_mk _ _

theorem DQ_add (w : G →+ ℤ) (F F') : DQ w (F + F') = DQ w F + DQ w F' := by
  ext n : 1; simp [wd_add]

theorem DQ_sub (w : G →+ ℤ) (F F') : DQ w (F - F') = DQ w F - DQ w F' := by
  ext n : 1; simp [wd_sub]

theorem DQ_mul (w : G →+ ℤ) (F F' : PowerSeries (AddMonoidAlgebra ℚ G)) :
    DQ w (F * F') = DQ w F * F' + F * DQ w F' := by
  ext n : 1
  simp only [coeff_DQ, coeff_mul, wd_sum, map_add, ← Finset.sum_add_distrib, wd_mul]

theorem DQ_lat {ι : Type*} (w : G →+ ℤ) (S : ℕ → Finset ι) (f : ι → AddMonoidAlgebra ℚ G) :
    DQ w (lat S f) = lat S (fun i => wd w (f i)) := by
  ext n : 1; simp [wd_sum]

end WD

/-- The Euler derivation `a d/da` on `ℚ[a^{±1}]`. -/
abbrev wa : ℤ →+ ℤ := AddMonoidHom.id ℤ

/-- Constants of `L`. -/
abbrev cst : ℚ →+* L := algebraMap ℚ L

theorem cst_apply (c : ℚ) : cst c = AddMonoidAlgebra.single 0 c := by
  simp [cst, AddMonoidAlgebra.coe_algebraMap]

theorem cst_mul_mono (c : ℚ) (j : ℤ) : cst c * mono j = AddMonoidAlgebra.single j c := by
  rw [cst_apply, mono, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]

theorem wd_cst_mul (c : ℚ) (f : L) : wd wa (cst c * f) = cst c * wd wa f := by
  rw [wd_mul, cst_apply, wd_single, map_zero, Int.cast_zero, zero_mul, AddMonoidAlgebra.single_zero,
    zero_mul, zero_add]

theorem wd_mono (j : ℤ) : wd wa (mono j) = cst j * mono j := by
  rw [cst_mul_mono, mono, wd_single, mul_one]; rfl

section LatAlg

variable {R : Type*} [CommRing R] {ι : Type*}

theorem lat_add (S : ℕ → Finset ι) (f g : ι → R) : lat S f + lat S g = lat S (fun i => f i + g i) := by
  ext n : 1; simp [Finset.sum_add_distrib]

theorem lat_sub (S : ℕ → Finset ι) (f g : ι → R) : lat S f - lat S g = lat S (fun i => f i - g i) := by
  ext n : 1; simp [Finset.sum_sub_distrib]

theorem lat_congr (S : ℕ → Finset ι) {f g : ι → R} (h : ∀ i, f i = g i) : lat S f = lat S g := by
  rw [funext h]

end LatAlg

/-- The pair index set `{(j,k) : T(j) + T(k) = n}`. -/
abbrev Ppair : ℕ → Finset (ℤ × ℤ) := fib (fun n => zbox n ×ˢ zbox n) (fun p => pentExp p.1 + pentExp p.2)

theorem hb2_pent : ∀ n (p : ℤ × ℤ), pentExp p.1 + pentExp p.2 ≤ n → p ∈ zbox n ×ˢ zbox n :=
  fun n p hp => Finset.mem_product.mpr ⟨hbox_pent n _ (by omega), hbox_pent n _ (by omega)⟩

theorem lat_Ppair_swap (f : ℤ × ℤ → L) : lat Ppair f = lat Ppair (fun p => f p.swap) := by
  ext n : 1
  rw [coeff_lat, coeff_lat]
  refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
  · intro p hp; rw [mem_fib hb2_pent] at hp ⊢; simp only [Prod.fst_swap, Prod.snd_swap]; omega
  · intro p hp; rw [mem_fib hb2_pent] at hp ⊢; simp only [Prod.fst_swap, Prod.snd_swap]; omega
  · intro p _; rfl
  · intro p _; rfl
  · intro p _; rfl

/-- `DΨ`. -/
theorem DQ_Psi : DQ wa Psi = lat (fib zbox pentExp) fun j => cst j * (negSign j * mono j) := by
  rw [Psi, DQ_lat]
  exact lat_congr _ fun j => by rw [wd_negSign_mul, wd_mono]; ring

theorem DQ_DQ_Psi :
    DQ wa (DQ wa Psi) = lat (fib zbox pentExp) fun j => cst (j * j) * (negSign j * mono j) := by
  rw [DQ_Psi, DQ_lat]
  refine lat_congr _ fun j => ?_
  rw [wd_cst_mul, wd_negSign_mul, wd_mono, map_mul]; ring

/-- `G = ΨD²Ψ - (DΨ)²`. -/
def Gser : PowerSeries L := Psi * DQ wa (DQ wa Psi) - DQ wa Psi * DQ wa Psi

/-- `ψ₀ = ∑_e (2e)² q^{e²}`. -/
def psi0 : PowerSeries L := lat (fib zbox E0) fun e => cst ((2 * e) * (2 * e))
/-- `ψ₁ = ∑_e (2e+1)² q^{e² + e}`. -/
def psi1 : PowerSeries L := lat (fib zbox E1) fun e => cst ((2 * e + 1) * (2 * e + 1))

/-- **`2(ΨD²Ψ - (DΨ)²) = ψ₀U₀ + ψ₁U₁`.** -/
theorem two_Gser : 2 * Gser = psi0 * U0 + psi1 * U1 := by
  have key : Gser = lat Ppair fun p =>
      cst (p.2 * p.2 - p.1 * p.2) * (negSign (p.1 + p.2) * mono (p.1 + p.2)) := by
    rw [Gser, DQ_DQ_Psi, DQ_Psi, Psi, lat_mul_fiber _ _ hbox_pent _ _ hbox_pent,
      lat_mul_fiber _ _ hbox_pent _ _ hbox_pent, lat_sub]
    refine lat_congr _ fun p => ?_
    rw [← negSign_mul_mono]
    simp only [map_sub, map_mul, map_intCast]
    ring
  have hpf := pair_factor (fun d => cst ((d : ℚ) * d))
  have h2 : 2 * Gser = lat Ppair fun p =>
      cst (((p.1 - p.2 : ℤ) : ℚ) * ((p.1 - p.2 : ℤ) : ℚ)) * (negSign (p.1 + p.2) * mono (p.1 + p.2)) := by
    rw [two_mul]
    conv_lhs => arg 2; rw [key, lat_Ppair_swap]
    rw [key, lat_add]
    refine lat_congr _ fun p => ?_
    simp only [Prod.fst_swap, Prod.snd_swap, add_comm p.2 p.1]
    rw [← add_mul, ← map_add]
    congr 2
    push_cast; ring
  rw [h2, hpf, psi0, psi1]
  congr 2 <;> exact lat_congr _ fun e => by push_cast; ring_nf

/-! ## Two variables: `b Ψ(ab) Ψ(a/b) = U₁(a)U₀(b) - U₀(a)U₁(b)` -/

/-- `ℚ[a^{±1}, b^{±1}]`. -/
abbrev L2 := AddMonoidAlgebra ℚ (ℤ × ℤ)

/-- The monomial `a^i b^j`. -/
def mon2 (p : ℤ × ℤ) : L2 := AddMonoidAlgebra.single p 1

theorem mon2_mul (p p' : ℤ × ℤ) : mon2 p * mon2 p' = mon2 (p + p') := by
  rw [mon2, mon2, mon2, AddMonoidAlgebra.single_mul_single, one_mul]

/-- The ring map `ℚ[a^{±1}] → ℚ[a^{±1},b^{±1}]` induced by `f : ℤ →+ ℤ × ℤ`. -/
def emb (f : ℤ →+ ℤ × ℤ) : L →+* L2 := AddMonoidAlgebra.mapDomainRingHom ℚ f

theorem emb_mono (f : ℤ →+ ℤ × ℤ) (j : ℤ) : emb f (mono j) = mon2 (f j) := by
  rw [emb, mono, mon2]
  exact AddMonoidAlgebra.mapDomain_single

theorem emb_negSign (f : ℤ →+ ℤ × ℤ) (j : ℤ) : emb f (negSign j) = negSign j := by
  simp [negSign]

/-- `a ↦ a`, `a ↦ b`, `a ↦ ab`, `a ↦ a/b`. -/
def fa : ℤ →+ ℤ × ℤ := AddMonoidHom.inl ℤ ℤ
def fb : ℤ →+ ℤ × ℤ := AddMonoidHom.inr ℤ ℤ
def fab : ℤ →+ ℤ × ℤ := AddMonoidHom.inl ℤ ℤ + AddMonoidHom.inr ℤ ℤ
def fq : ℤ →+ ℤ × ℤ := AddMonoidHom.inl ℤ ℤ - AddMonoidHom.inr ℤ ℤ

@[simp] theorem fa_apply (j : ℤ) : fa j = (j, 0) := rfl
@[simp] theorem fb_apply (j : ℤ) : fb j = (0, j) := rfl
@[simp] theorem fab_apply (j : ℤ) : fab j = (j, j) := by simp [fab]
@[simp] theorem fq_apply (j : ℤ) : fq j = (j, -j) := by simp [fq]

theorem lat_C_mul {R : Type*} [CommRing R] {ι : Type*} (c : R) (S : ℕ → Finset ι) (f : ι → R) :
    PowerSeries.C c * lat S f = lat S (fun i => c * f i) := by
  ext n : 1; simp [Finset.mul_sum]

theorem map_Psi (f : ℤ →+ ℤ × ℤ) :
    PowerSeries.map (emb f) Psi = lat (fib zbox pentExp) fun j => negSign j * mon2 (f j) := by
  rw [Psi, lat_map]
  exact lat_congr _ fun j => by rw [map_mul, emb_negSign, emb_mono]

theorem map_U0 (f : ℤ →+ ℤ × ℤ) :
    PowerSeries.map (emb f) U0 = lat (fib zbox EU0) fun m => mon2 (f (2 * m)) := by
  rw [U0, lat_map]; exact lat_congr _ fun m => emb_mono f _

theorem map_U1 (f : ℤ →+ ℤ × ℤ) :
    PowerSeries.map (emb f) U1 = lat (fib zbox E0) fun m => -mon2 (f (2 * m + 1)) := by
  rw [U1, lat_map]; exact lat_congr _ fun m => by rw [map_neg, emb_mono]

theorem key_w (j k : ℤ) :
    mon2 (0, 1) * (negSign j * mon2 (fab j) * (negSign k * mon2 (fq k))) =
      negSign (j + k) * mon2 (j + k, j - k + 1) := by
  calc _ = (negSign j * negSign k) * (mon2 (0, 1) * mon2 (fab j) * mon2 (fq k)) := by ring
    _ = _ := by
      rw [mon2_mul, mon2_mul, ← negSign_add, fab_apply, fq_apply]
      congr 2; ext <;> simp; ring

/-- **`b Ψ(ab)Ψ(a/b) = U₁(a)U₀(b) - U₀(a)U₁(b)`.** -/
theorem Psi_ab_mul_Psi_aq :
    PowerSeries.C (mon2 (0, 1)) * (PowerSeries.map (emb fab) Psi * PowerSeries.map (emb fq) Psi) =
      PowerSeries.map (emb fa) U1 * PowerSeries.map (emb fb) U0 -
        PowerSeries.map (emb fa) U0 * PowerSeries.map (emb fb) U1 := by
  rw [map_Psi, map_Psi, map_U0, map_U0, map_U1, map_U1, lat_mul_fiber _ _ hbox_pent _ _ hbox_pent,
    lat_mul_fiber _ _ hbox_E0 _ _ hbox_EU0, lat_mul_fiber _ _ hbox_EU0 _ _ hbox_E0, lat_C_mul]
  have hb2 : ∀ (E E' : ℤ → ℕ), (∀ n j, E j ≤ n → j ∈ zbox n) → (∀ n j, E' j ≤ n → j ∈ zbox n) →
      ∀ n (p : ℤ × ℤ), E p.1 + E' p.2 ≤ n → p ∈ zbox n ×ˢ zbox n := fun E E' h h' n p hp =>
    Finset.mem_product.mpr ⟨h n _ (by omega), h' n _ (by omega)⟩
  ext n : 1
  simp only [coeff_lat, map_sub]
  rw [← Finset.sum_filter_add_sum_filter_not
    (fib (fun n => zbox n ×ˢ zbox n) (fun p => pentExp p.1 + pentExp p.2) n)
    (fun p : ℤ × ℤ => (p.1 + p.2) % 2 = 1), sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_nbij' (fun p => ((p.1 + p.2 - 1) / 2, (p.1 - p.2 + 1) / 2))
      (fun p => (p.1 + p.2, p.1 - p.2 + 1)) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨j, k⟩ hp
      rw [Finset.mem_filter, mem_fib (hb2 _ _ hbox_pent hbox_pent), pentExp_add_iff] at hp
      rw [mem_fib (hb2 _ _ hbox_E0 hbox_EU0)]
      dsimp only at hp ⊢
      zify; rw [E0_cast, EU0_cast]
      obtain ⟨h1, h2⟩ := hp
      have he : 2 * ((j + k - 1) / 2) = j + k - 1 := by omega
      have hm : 2 * ((j - k + 1) / 2) = j - k + 1 := by omega
      generalize (j + k - 1) / 2 = e at he ⊢
      generalize (j - k + 1) / 2 = m at hm ⊢
      have h4 : 4 * (e * e + (m * m - m)) = 4 * (n : ℤ) := by
        linear_combination (2 * e + (j + k - 1)) * he + (2 * m + (j - k + 1) - 2) * hm + 2 * h1
      omega
    · rintro ⟨e, m⟩ hp
      rw [mem_fib (hb2 _ _ hbox_E0 hbox_EU0)] at hp
      zify at hp; rw [E0_cast, EU0_cast] at hp
      rw [Finset.mem_filter, mem_fib (hb2 _ _ hbox_pent hbox_pent), pentExp_add_iff]
      dsimp only at hp ⊢
      exact ⟨by linear_combination 2 * hp, by omega⟩
    · rintro ⟨j, k⟩ hp
      rw [Finset.mem_filter] at hp
      dsimp only at hp ⊢
      ext <;> simp <;> omega
    · rintro ⟨e, m⟩ _
      ext <;> simp <;> omega
    · rintro ⟨j, k⟩ hp
      rw [Finset.mem_filter] at hp
      dsimp only at hp ⊢
      have hs : (negSign (j + k) : L2) = -1 := by rw [negSign_eq, if_neg (by omega)]
      rw [key_w, hs, fa_apply, fb_apply, neg_mul, one_mul, neg_mul, mon2_mul]
      congr 2; ext <;> simp <;> omega
  · refine Finset.sum_nbij' (fun p => ((p.1 + p.2) / 2, (p.1 - p.2) / 2))
      (fun p => (p.1 + p.2, p.1 - p.2)) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨j, k⟩ hp
      rw [Finset.mem_filter, mem_fib (hb2 _ _ hbox_pent hbox_pent), pentExp_add_iff] at hp
      rw [mem_fib (hb2 _ _ hbox_EU0 hbox_E0)]
      dsimp only at hp ⊢
      zify; rw [EU0_cast, E0_cast]
      obtain ⟨h1, h2⟩ := hp
      have he : 2 * ((j + k) / 2) = j + k := by omega
      have hm : 2 * ((j - k) / 2) = j - k := by omega
      generalize (j + k) / 2 = e at he ⊢
      generalize (j - k) / 2 = m at hm ⊢
      have h4 : 4 * (e * e - e + m * m) = 4 * (n : ℤ) := by
        linear_combination (2 * e + (j + k) - 2) * he + (2 * m + (j - k)) * hm + 2 * h1
      omega
    · rintro ⟨e, m⟩ hp
      rw [mem_fib (hb2 _ _ hbox_EU0 hbox_E0)] at hp
      zify at hp; rw [EU0_cast, E0_cast] at hp
      rw [Finset.mem_filter, mem_fib (hb2 _ _ hbox_pent hbox_pent), pentExp_add_iff]
      dsimp only at hp ⊢
      exact ⟨by linear_combination 2 * hp, by omega⟩
    · rintro ⟨j, k⟩ hp
      rw [Finset.mem_filter] at hp
      dsimp only at hp ⊢
      ext <;> simp <;> omega
    · rintro ⟨e, m⟩ _
      ext <;> simp <;> omega
    · rintro ⟨j, k⟩ hp
      rw [Finset.mem_filter] at hp
      dsimp only at hp ⊢
      have hs : (negSign (j + k) : L2) = 1 := by rw [negSign_eq, if_pos (by omega)]
      rw [key_w, hs, fa_apply, fb_apply, mul_neg, neg_neg, mon2_mul, one_mul]
      congr 1; ext <;> simp <;> omega

/-! ## The two-variable identity -/

theorem emb_cst (f : ℤ →+ ℤ × ℤ) (c : ℚ) : emb f (cst c) = algebraMap ℚ L2 c := by
  rw [cst_apply, emb, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single,
    map_zero]
  simp [AddMonoidAlgebra.coe_algebraMap]

theorem map_phi0 (f g : ℤ →+ ℤ × ℤ) :
    PowerSeries.map (emb f) phi0 = PowerSeries.map (emb g) phi0 := by
  rw [phi0, lat_map, lat_map]; simp
theorem map_phi1 (f g : ℤ →+ ℤ × ℤ) :
    PowerSeries.map (emb f) phi1 = PowerSeries.map (emb g) phi1 := by
  rw [phi1, lat_map, lat_map]; simp
theorem map_psi0 (f g : ℤ →+ ℤ × ℤ) :
    PowerSeries.map (emb f) psi0 = PowerSeries.map (emb g) psi0 := by
  rw [psi0, lat_map, lat_map]; simp only [emb_cst]
theorem map_psi1 (f g : ℤ →+ ℤ × ℤ) :
    PowerSeries.map (emb f) psi1 = PowerSeries.map (emb g) psi1 := by
  rw [psi1, lat_map, lat_map]; simp only [emb_cst]

/-- The theta-constant `κ = φ₀ψ₁ - φ₁ψ₀`. -/
def kap : PowerSeries L := phi0 * psi1 - phi1 * psi0

/-- **The two-variable identity**
`Ψ(b)²·2G(a) - Ψ(a)²·2G(b) = κ · b Ψ(ab) Ψ(a/b)`. -/
theorem two_var :
    PowerSeries.map (emb fb) (Psi * Psi) * PowerSeries.map (emb fa) (2 * Gser) -
        PowerSeries.map (emb fa) (Psi * Psi) * PowerSeries.map (emb fb) (2 * Gser) =
      PowerSeries.map (emb fa) kap *
        (PowerSeries.C (mon2 (0, 1)) * (PowerSeries.map (emb fab) Psi * PowerSeries.map (emb fq) Psi)) := by
  rw [Psi_sq, two_Gser, Psi_ab_mul_Psi_aq, kap]
  simp only [map_add, map_mul, map_sub]
  rw [map_phi0 fb fa, map_phi1 fb fa, map_psi0 fb fa, map_psi1 fb fa]
  ring

end

end VOA.DeligneAudit.DeligneCharacter.D4Wp
