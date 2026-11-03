import VOA.Classification.COne.OrbPos6Iterates
import VOA.Classification.COne.OrbPos6Binomial

/-!
# Twisted product formula for every pair of exponential lattice states

This is a proved restriction of the all-state target of `OrbPos5`. It includes
arbitrary shifts and all product indices, not just the singular OPE terms.
The oscillator-descendant extension is a separate obligation.
-/

namespace VOA.Classification.COne.OrbPos6
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet VOA.HeisenbergN
open OrbPos2 OrbPos3 OrbPos4 OrbPos5 LatMod TwistedReduction

/-- The actual shifted iterate identity on two charged exponential states,
on any compatible pair of residue classes. -/
def ChargedProductFormula {n : ℕ} (hn : 0 < n) (a j : ℤ) : Prop :=
  ∀ β γ e f : ℤ, (e - a * β) % (n : ℤ) = 0 → (f - a * γ) % (n : ℤ) = 0 →
    ∀ (ℓ s : ℤ) (x : Space),
    mode (Fld.prod ℓ
      (rescFld hn (shiftedY_truncation hn a j (latChargeGen (latP 1) β)) e)
      (rescFld hn (shiftedY_truncation hn a j (latChargeGen (latP 1) γ)) f)).1 s x =
    ∑ᶠ d : ℕ, cbinom ((e : ℂ) / n) d •
      shiftedY n a j
        ((V2m 1 le_rfl).smul (latChargeGen (latP 1) β) (ℓ + d)
          (latChargeGen (latP 1) γ)) ((n : ℤ) * (s - d) + e + f) x

/-- The zero-mode phases and Δ correction combine by Vandermonde, proving
the complete product formula on every pair of charged exponentials. -/
theorem chargedProductFormula {n : ℕ} (hn : 0 < n) (a j : ℤ) :
    ChargedProductFormula hn a j := by
  intro β γ e f he hf ℓ s x
  let q := (e - a * β) / (n : ℤ)
  let r := (f - a * γ) / (n : ℤ)
  have heq : e = (n : ℤ) * q + a * β := by
    have h := Int.emod_add_mul_ediv (e - a * β) (n : ℤ)
    rw [he, zero_add] at h
    dsimp [q]
    linarith
  have hfr : f = (n : ℤ) * r + a * γ := by
    have h := Int.emod_add_mul_ediv (f - a * γ) (n : ℤ)
    rw [hf, zero_add] at h
    dsimp [r]
    linarith
  let P : ℤ → ℤ → Space := fun l z =>
    mode ((latticeModule 1 le_rfl j).YM
      ((V2m 1 le_rfl).smul (latChargeGen (latP 1) β) l (latChargeGen (latP 1) γ)))
      (q + (r + z)) x
  let Q : ℤ → ℤ → Space := fun l z =>
    shiftedY n a j
      ((V2m 1 le_rfl).smul (latChargeGen (latP 1) β) l (latChargeGen (latP 1) γ))
      ((n : ℤ) * (q + (r + z)) + a * (β + γ)) x
  have hP (l z : ℤ) (hl : -(2 * β * γ) ≤ l) : P l z = 0 := by
    dsimp [P]
    rw [charge_smul_zero β γ l hl, map_zero]
    rfl
  have hQ (l z : ℤ) (hl : -(2 * β * γ) ≤ l) : Q l z = 0 := by
    dsimp [Q]
    rw [charge_smul_zero β γ l hl, map_zero]
    rfl
  have hPQ (l z : ℤ) : Q l z =
      ∑ᶠ i : ℕ, cbinom (-(a : ℂ) * β / n) i • P (l + i) (z - i) := by
    dsimp only [Q]
    rw [shiftedY_charge_smul hn]
    apply finsum_congr
    intro i
    dsimp only [P]
    rw [show q + (r + z) - (i : ℤ) = q + (r + (z - i)) by ring]
  have hc : (e : ℂ) / n + (-(a : ℂ) * β / n) = (q : ℂ) := by
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    have hec : (e : ℂ) = (n : ℂ) * q + (a : ℂ) * β := by exact_mod_cast heq
    rw [hec]
    field_simp
    ring
  have hconv := binomial_convolution ((e : ℂ) / n) (-(a : ℂ) * β / n)
    P Q (-(2 * β * γ)) hP hQ hPQ ℓ s
  rw [hc] at hconv
  rw [charge_product_ordinary hn a j β γ e f ℓ s he hf x]
  calc
    _ = ∑ᶠ d : ℕ, cbinom (q : ℂ) d • P (ℓ + d) (s - d) := by
      apply finsum_congr
      intro d
      dsimp only [P]
      rw [show (e - a * β) / (n : ℤ) + ((f - a * γ) / (n : ℤ) + s) - d =
        q + (r + (s - d)) by dsimp [q, r]; ring]
      rfl
    _ = ∑ᶠ d : ℕ, cbinom ((e : ℂ) / n) d • Q (ℓ + d) (s - d) := hconv.symm
    _ = _ := by
      apply finsum_congr
      intro d
      dsimp only [Q]
      rw [show (n : ℤ) * (q + (r + (s - d))) + a * (β + γ) =
        (n : ℤ) * (s - d) + e + f by rw [heq, hfr]; ring]

/-- The proved charged restriction implies the actual twisted Jacobi mode
identity for the same pair, at every compatible pair of fractional modes. -/
theorem chargedJacobi_of_productFormula {n : ℕ} (hn : 0 < n) (a j : ℤ)
    (hpf : ChargedProductFormula hn a j) (β γ ℓ k m : ℤ)
    (hk : (k - a * β) % (n : ℤ) = 0) (hm : (m - a * γ) % (n : ℤ) = 0) (x : Space) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
      (shiftedY n a j (latChargeGen (latP 1) β) (ℓ * n + k - i * n)
        (shiftedY n a j (latChargeGen (latP 1) γ) (m + i * n) x) -
      negOnePow ℓ • shiftedY n a j (latChargeGen (latP 1) γ) (ℓ * n + m - i * n)
        (shiftedY n a j (latChargeGen (latP 1) β) (k + i * n) x))) =
      ∑ᶠ d : ℕ, cbinom ((k : ℂ) / n) d • shiftedY n a j
        ((V2m 1 le_rfl).smul (latChargeGen (latP 1) β) (ℓ + d)
          (latChargeGen (latP 1) γ)) (k + m - d * n) x := by
  have h := twisted_jacobi_of_local_pf (V2m 1 le_rfl) (shiftedY n a j) hn
    (shiftedY_truncation hn a j) (latChargeGen (latP 1) β) (latChargeGen (latP 1) γ)
    k m (shiftedY_local hn a j k m _ _) (hpf β γ k m hk hm) x ℓ 0 0
  simpa only [mul_zero, zero_add] using h

/-- Unconditional charged-pair twisted Jacobi, including non-dual shifts.
This does not assert Jacobi on arbitrary oscillator descendants. -/
theorem shiftedJacobi_charges {n : ℕ} (hn : 0 < n) (a j : ℤ) (β γ ℓ k m : ℤ)
    (hk : (k - a * β) % (n : ℤ) = 0) (hm : (m - a * γ) % (n : ℤ) = 0) (x : Space) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
      (shiftedY n a j (latChargeGen (latP 1) β) (ℓ * n + k - i * n)
        (shiftedY n a j (latChargeGen (latP 1) γ) (m + i * n) x) -
      negOnePow ℓ • shiftedY n a j (latChargeGen (latP 1) γ) (ℓ * n + m - i * n)
        (shiftedY n a j (latChargeGen (latP 1) β) (k + i * n) x))) =
      ∑ᶠ d : ℕ, cbinom ((k : ℂ) / n) d • shiftedY n a j
        ((V2m 1 le_rfl).smul (latChargeGen (latP 1) β) (ℓ + d)
          (latChargeGen (latP 1) γ)) (k + m - d * n) x :=
  chargedJacobi_of_productFormula hn a j (chargedProductFormula hn a j)
    β γ ℓ k m hk hm x

end VOA.Classification.COne.OrbPos6
