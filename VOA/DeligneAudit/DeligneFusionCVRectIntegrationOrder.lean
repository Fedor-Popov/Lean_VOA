import Mathlib

/-!
# The coefficient-order induction for the commutative upper recursion

The derivative identity for a functional and its normalized primitive
has two terms: differentiating the zero-mode multiplier and
differentiating a chosen current power. The two inductions below show
that this identity transfers the required coefficient vanishing orders
when the chosen site's capacity is maximal among its active sites.

This file proves the order induction and its actual finite-capacity
arithmetic. Constructing the polynomial primitive, deriving the identity
for the source ideal's annihilator, and separating the ideal plus shift
subspace remain separate obligations. No ideal preservation is assumed
or asserted here.
-/

namespace VOA.DeligneAudit.A2.CVRectIntegrationOrder

noncomputable section

/-- All coefficients below the specified degree vanish. -/
def ZeroBelow (f : PowerSeries ℂ) (d : ℕ) : Prop :=
  ∀ j, j < d → PowerSeries.coeff j f = 0

theorem zeroBelow_shift {f : PowerSeries ℂ} {d : ℕ} (hf : ZeroBelow f d) (h : ℕ) :
    ZeroBelow (PowerSeries.X ^ h * f) (d + h) := by
  intro j hj
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with hh
  · exact hf _ (by omega)
  · rfl

theorem scalar_cancel {c z : ℂ} (hc : c ≠ 0) (hz : c * z = 0) : z = 0 :=
  (mul_eq_zero.mp hz).resolve_left hc

/-- The two order inductions in the commutative upper recursion. The
identity supplied here is an ordinary derivative/product identity,
rather than the desired target order bound or an ideal-map premise. -/
theorem order_transfer (F G : ℕ → ℕ → PowerSeries ℂ) (μ : ℕ → ℕ)
    (b K h : ℕ)
    (hF : ∀ a i, ZeroBelow (F a i) (μ a))
    (hder : ∀ a i, F a i = (i : ℂ) • G a (i - 1) +
      (a : ℂ) • (PowerSeries.X ^ h * G (a - 1) i))
    (hlow : ∀ a, a + 1 + b < K → μ (a + 1) ≤ μ a + h)
    (hhigh : ∀ a, K ≤ a + b → μ (a + 1) = μ a + h + 1) :
    ∀ a i, ZeroBelow (G a i) (if a + b < K then μ a else μ a + 1) := by
  have low : ∀ a i, a + b < K → ZeroBelow (G a i) (μ a) := by
    intro a
    induction a with
    | zero =>
        intro i _ j hj
        have he := congrArg (PowerSeries.coeff j) (hder 0 (i + 1))
        simp only [Nat.add_sub_cancel, Nat.cast_zero, zero_smul, add_zero,
          PowerSeries.coeff_smul] at he
        rw [hF 0 (i + 1) j hj] at he
        exact scalar_cancel (by exact_mod_cast Nat.succ_ne_zero i) he.symm
    | succ a ih =>
        intro i ha j hj
        have hg := zeroBelow_shift (ih (i + 1) (by omega)) h
        have hs : PowerSeries.coeff j (PowerSeries.X ^ h * G a (i + 1)) = 0 :=
          hg j (by have := hlow a ha; omega)
        have he := congrArg (PowerSeries.coeff j) (hder (a + 1) (i + 1))
        simp only [Nat.add_sub_cancel, map_add, PowerSeries.coeff_smul] at he
        rw [hF (a + 1) (i + 1) j hj, hs, smul_zero, add_zero] at he
        exact scalar_cancel (by exact_mod_cast Nat.succ_ne_zero i) he.symm
  have high : ∀ i a, K ≤ a + b → ZeroBelow (G a i) (μ a + 1) := by
    intro i
    induction i with
    | zero =>
        intro a ha j hj
        have hf : PowerSeries.coeff (j + h) (F (a + 1) 0) = 0 := by
          apply hF
          rw [hhigh a ha]
          omega
        have he := congrArg (PowerSeries.coeff (j + h)) (hder (a + 1) 0)
        simp only [Nat.cast_zero, zero_smul, zero_add, Nat.add_sub_cancel,
          PowerSeries.coeff_smul, PowerSeries.coeff_X_pow_mul] at he
        rw [hf] at he
        exact scalar_cancel (by exact_mod_cast Nat.succ_ne_zero a) he.symm
    | succ i ih =>
        intro a ha j hj
        have hf : PowerSeries.coeff (j + h) (F (a + 1) (i + 1)) = 0 := by
          apply hF
          rw [hhigh a ha]
          omega
        have hg : PowerSeries.coeff (j + h) (G (a + 1) i) = 0 := by
          apply ih (a + 1) (by omega)
          rw [hhigh a ha]
          omega
        have he := congrArg (PowerSeries.coeff (j + h)) (hder (a + 1) (i + 1))
        simp only [Nat.add_sub_cancel, map_add, PowerSeries.coeff_smul,
          PowerSeries.coeff_X_pow_mul] at he
        rw [hf, hg, smul_zero, zero_add] at he
        exact scalar_cancel (by exact_mod_cast Nat.succ_ne_zero a) he.symm
  intro a i
  split_ifs with ha
  · exact low a i ha
  · exact high i a (by omega)

/-- The active sites other than the chosen one contribute these excesses. -/
def excess (ks : List ℕ) (t : ℕ) : ℕ := (ks.map (fun k => t - k)).sum

theorem excess_succ_le (ks : List ℕ) (t : ℕ) :
    excess ks (t + 1) ≤ excess ks t + ks.length := by
  induction ks with
  | nil => simp [excess]
  | cons k ks ih =>
      simp only [excess, List.map_cons, List.sum_cons, List.length_cons] at *
      omega

theorem excess_succ_eq (ks : List ℕ) (t : ℕ) (ht : ∀ k ∈ ks, k ≤ t) :
    excess ks (t + 1) = excess ks t + ks.length := by
  induction ks with
  | nil => simp [excess]
  | cons k ks ih =>
      have hk := ht k List.mem_cons_self
      have hi := ih (fun k hk => ht k (List.mem_cons_of_mem _ hk))
      simp only [excess, List.map_cons, List.sum_cons, List.length_cons] at *
      omega

/-- The order function of an actual finite list of active capacities,
with a fixed contribution `C` from inactive sites. -/
def siteOrder (ks : List ℕ) (C K b a : ℕ) : ℕ :=
  C + (a + b - K) + excess ks (a + b)

theorem siteOrder_low (ks : List ℕ) (C K b a : ℕ) (ha : a + 1 + b < K) :
    siteOrder ks C K b (a + 1) ≤ siteOrder ks C K b a + ks.length := by
  have he := excess_succ_le ks (a + b)
  rw [show a + b + 1 = a + 1 + b by omega] at he
  dsimp only [siteOrder]
  omega

theorem siteOrder_high (ks : List ℕ) (C K b a : ℕ)
    (hmax : ∀ k ∈ ks, k ≤ K) (ha : K ≤ a + b) :
    siteOrder ks C K b (a + 1) = siteOrder ks C K b a + ks.length + 1 := by
  have he := excess_succ_eq ks (a + b) (fun k hk => (hmax k hk).trans ha)
  rw [show a + b + 1 = a + 1 + b by omega] at he
  dsimp only [siteOrder]
  omega

theorem siteOrder_decrement (ks : List ℕ) (C K b a : ℕ) (hK : 1 ≤ K) :
    siteOrder ks C (K - 1) b a =
      if a + b < K then siteOrder ks C K b a else siteOrder ks C K b a + 1 := by
  dsimp only [siteOrder]
  split_ifs <;> omega

/-- Instantiating the order induction with the actual excess functions
decreases the chosen maximal positive site capacity by one. -/
theorem active_site_order_transfer (F G : ℕ → ℕ → PowerSeries ℂ)
    (ks : List ℕ) (C K b : ℕ) (hK : 1 ≤ K) (hmax : ∀ k ∈ ks, k ≤ K)
    (hF : ∀ a i, ZeroBelow (F a i) (siteOrder ks C K b a))
    (hder : ∀ a i, F a i = (i : ℂ) • G a (i - 1) +
      (a : ℂ) • (PowerSeries.X ^ ks.length * G (a - 1) i)) :
    ∀ a i, ZeroBelow (G a i) (siteOrder ks C (K - 1) b a) := by
  intro a i
  rw [siteOrder_decrement ks C K b a hK]
  exact order_transfer F G (siteOrder ks C K b) b K ks.length hF hder
    (siteOrder_low ks C K b) (siteOrder_high ks C K b · hmax) a i

end

end VOA.DeligneAudit.A2.CVRectIntegrationOrder

#print axioms VOA.DeligneAudit.A2.CVRectIntegrationOrder.order_transfer
#print axioms VOA.DeligneAudit.A2.CVRectIntegrationOrder.active_site_order_transfer
