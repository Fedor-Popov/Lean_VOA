import VOA.DeligneAudit.LeviConversionDefs

/-! A normal-ordering identity for a central commutator in any ring. -/

namespace VOA.DeligneAudit.LeviConversion

noncomputable section

variable {R : Type*} [Ring R]

/-- Moving one letter past a positive power of the current. -/
theorem one_letter_pow_succ {F A B : R} (hFA : F * A - A * F = B)
    (hFB : F * B = B * F) (k : ℕ) :
    A * F ^ (k + 1) = F ^ (k + 1) * A - (k + 1) • (F ^ k * B) := by
  induction k with
  | zero =>
      have hAF : A * F = F * A - B := by rw [← hFA]; abel
      simpa using hAF
  | succ k ih =>
      have hAF : A * F = F * A - B := by rw [← hFA]; abel
      have hBF : (F ^ k * B) * F = F ^ (k + 1) * B := by
        rw [mul_assoc, ← hFB, ← mul_assoc, ← pow_succ]
      calc
        A * F ^ (k + 1 + 1) = (A * F ^ (k + 1)) * F := by
          rw [pow_succ, mul_assoc]
        _ = (F ^ (k + 1) * A - (k + 1) • (F ^ k * B)) * F := by rw [ih]
        _ = F ^ (k + 1 + 1) * A - (k + 1 + 1) • (F ^ (k + 1) * B) := by
          rw [sub_mul, smul_mul_assoc, hBF, mul_assoc, hAF, mul_sub,
            ← mul_assoc, ← pow_succ]
          simp only [add_nsmul, one_nsmul]
          abel

/-- Moving one letter past any power of the current. -/
theorem one_letter_pow {F A B : R} (hFA : F * A - A * F = B)
    (hFB : F * B = B * F) (k : ℕ) :
    A * F ^ k = F ^ k * A - k • (F ^ (k - 1) * B) := by
  cases k with
  | zero => simp
  | succ k => simpa using one_letter_pow_succ hFA hFB k

private theorem b_comm_prod {ι : Type*} (a b : ι → R)
    (hAB : ∀ i j, a i * b j = b j * a i) (x : ι) (xs : List ι) :
    b x * (xs.map a).prod = (xs.map a).prod * b x := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [mul_assoc, ← ih, ← mul_assoc, ← hAB y x, mul_assoc]

private theorem wickTerm_step {ι : Type*} (F : R) (a b : ι → R)
    (hFA : ∀ i, F * a i - a i * F = b i)
    (hFB : ∀ i, F * b i = b i * F)
    (hAB : ∀ i j, a i * b j = b j * a i)
    (k : ℕ) (x : ι) (p : List ι × List ι) :
    a x * wickTerm F a b k p =
      wickTerm F a b k (x :: p.1, p.2) +
        wickTerm F a b k (p.1, x :: p.2) := by
  let t := p.2.length
  by_cases ht : t ≤ k
  · have he : k - (t + 1) = (k - t) - 1 := by omega
    have hc : (-1 : R) ^ (t + 1) * (k.descFactorial (t + 1) : R) =
        -((k - t : ℕ) : R) *
          ((-1 : R) ^ t * (k.descFactorial t : R)) := by
      rw [Nat.descFactorial_succ, Nat.cast_mul, pow_succ]
      simp only [mul_neg_one, neg_mul]
      congr 1
      calc
        (-1 : R) ^ t * ((k - t : ℕ) * (k.descFactorial t : R)) =
            ((-1 : R) ^ t * (k - t : ℕ)) * (k.descFactorial t : R) :=
              (mul_assoc _ _ _).symm
        _ = ((k - t : ℕ) * (-1 : R) ^ t) * (k.descFactorial t : R) := by
          rw [((k - t).cast_commute ((-1 : R) ^ t)).eq]
        _ = (k - t : ℕ) * ((-1 : R) ^ t * (k.descFactorial t : R)) :=
          mul_assoc _ _ _
    have hp := one_letter_pow (hFA x) (hFB x) (k - t)
    have hb := b_comm_prod a b hAB x p.1
    simp only [wickTerm, List.length_cons, List.map_cons, List.prod_cons]
    change _ = _ +
      ((-1 : R) ^ (t + 1) * (k.descFactorial (t + 1) : R)) *
        (F ^ (k - (t + 1)) * (p.1.map a).prod * (b x * (p.2.map b).prod))
    rw [he, hc]
    -- Central natural coefficients may be collected before using the commutator.
    simp only [nsmul_eq_mul] at hp
    have hcentral (y : R) :
        y * ((-1 : R) ^ t * (k.descFactorial t : R)) =
          ((-1 : R) ^ t * (k.descFactorial t : R)) * y := by
      calc
        y * ((-1 : R) ^ t * (k.descFactorial t : R)) =
            (y * (-1 : R) ^ t) * (k.descFactorial t : R) := by rw [mul_assoc]
        _ = ((-1 : R) ^ t * y) * (k.descFactorial t : R) := by
          rw [((Commute.neg_one_right y).pow_right t).eq]
        _ = (-1 : R) ^ t * (y * (k.descFactorial t : R)) := by rw [mul_assoc]
        _ = (-1 : R) ^ t * ((k.descFactorial t : R) * y) := by
          rw [((k.descFactorial t).cast_commute y).eq]
        _ = ((-1 : R) ^ t * (k.descFactorial t : R)) * y := by rw [mul_assoc]
    have hca := hcentral (a x)
    let c : R := (-1 : R) ^ t * (k.descFactorial t : R)
    let P : R := (p.1.map a).prod
    let Q : R := (p.2.map b).prod
    let r : ℕ := k - t
    change a x * c = c * a x at hca
    change a x * F ^ r = F ^ r * a x - (r : R) * (F ^ (r - 1) * b x) at hp
    change b x * P = P * b x at hb
    have hrc : (r : R) * c = c * (r : R) := ((r.cast_commute c)).eq
    change a x * (c * (F ^ r * P * Q)) =
      c * (F ^ r * (a x * P) * Q) +
        (-(r : R) * c) * (F ^ (r - 1) * P * (b x * Q))
    calc
      a x * (c * (F ^ r * P * Q)) = c * ((a x * F ^ r) * P * Q) := by
        rw [← mul_assoc, hca]
        noncomm_ring
      _ = c * ((F ^ r * a x - (r : R) * (F ^ (r - 1) * b x)) * P * Q) := by
        rw [hp]
      _ = c * (F ^ r * (a x * P) * Q) +
          (-(r : R) * c) * (F ^ (r - 1) * P * (b x * Q)) := by
        noncomm_ring [hb, hrc]
  · have hzero : k.descFactorial t = 0 :=
      Nat.descFactorial_of_lt (by omega)
    have hzero' : k.descFactorial (t + 1) = 0 :=
      Nat.descFactorial_of_lt (by omega)
    dsimp [t] at hzero hzero'
    simp [wickTerm, hzero]

/-- The Wick identity for an ordered list, including repeated modes. -/
theorem wick_identity {ι : Type*} (F : R) (a b : ι → R)
    (hFA : ∀ i, F * a i - a i * F = b i)
    (hFB : ∀ i, F * b i = b i * F)
    (hAB : ∀ i j, a i * b j = b j * a i)
    (k : ℕ) (xs : List ι) :
    (xs.map a).prod * F ^ k = wickSum F a b k xs := by
  induction xs with
  | nil => simp [wickSum, choices, wickTerm]
  | cons x xs ih =>
      change (a x * (xs.map a).prod) * F ^ k = _
      rw [mul_assoc, ih]
      simp only [wickSum, choices, List.map_append, List.sum_append,
        List.map_map, Function.comp_def]
      rw [← List.sum_map_mul_left, ← List.sum_map_add]
      congr 1
      apply List.map_congr_left
      intro p hp
      exact wickTerm_step F a b hFA hFB hAB k x p

end
end VOA.DeligneAudit.LeviConversion

#print axioms VOA.DeligneAudit.LeviConversion.one_letter_pow
#print axioms VOA.DeligneAudit.LeviConversion.wick_identity
