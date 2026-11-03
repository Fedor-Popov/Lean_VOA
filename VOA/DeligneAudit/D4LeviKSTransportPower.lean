import VOA.DeligneAudit.D4LeviKSTransportPair

/-! A full-replacement identity for iterated commutators of a power. -/

namespace VOA.DeligneAudit.D4Levi

variable {R : Type} [Ring R]

/-- Nested commutators in an arbitrary associative ring. -/
def iteratedAdjoint (E : ℕ → R) : List ℕ → R → R
  | [], F => F
  | r :: rs, F => E r * iteratedAdjoint E rs F - iteratedAdjoint E rs F * E r

private theorem comm_power_succ (E F B : R)
    (hEF : E * F - F * E = B) (hFB : F * B = B * F) (n : ℕ) :
    E * F ^ (n + 1) - F ^ (n + 1) * E = (n + 1) • (F ^ n * B) := by
  induction n with
  | zero => simpa using hEF
  | succ n ih =>
      have hmove : (F ^ n * B) * F = F ^ (n + 1) * B := by
        rw [mul_assoc, ← hFB, ← mul_assoc, ← pow_succ]
      calc
        E * F ^ (n + 2) - F ^ (n + 2) * E =
            (E * F ^ (n + 1) - F ^ (n + 1) * E) * F +
              F ^ (n + 1) * (E * F - F * E) := by
                rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
                noncomm_ring
        _ = ((n + 1) • (F ^ n * B)) * F + F ^ (n + 1) * B := by
              rw [ih, hEF]
        _ = (n + 2) • (F ^ (n + 1) * B) := by
              rw [show ((n + 1) • (F ^ n * B)) * F =
                (n + 1) • ((F ^ n * B) * F) by
                  simp [nsmul_eq_mul, mul_assoc], hmove]
              simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
              noncomm_ring

private theorem commute_prod (E : R) (B : ℕ → R)
    (hEB : ∀ q, E * B q = B q * E) (rs : List ℕ) :
    E * (rs.map B).prod = (rs.map B).prod * E := by
  induction rs with
  | nil => simp
  | cons q rs ih =>
      simp only [List.map_cons, List.prod_cons]
      calc
        E * (B q * (rs.map B).prod) = (E * B q) * (rs.map B).prod :=
          (mul_assoc _ _ _).symm
        _ = (B q * E) * (rs.map B).prod := by rw [hEB q]
        _ = B q * (E * (rs.map B).prod) := mul_assoc _ _ _
        _ = B q * ((rs.map B).prod * E) := by rw [ih]
        _ = (B q * (rs.map B).prod) * E :=
          (mul_assoc (B q) (rs.map B).prod E).symm

private theorem comm_nsmul (E G : R) (c : ℕ) :
    E * (c • G) - (c • G) * E = c • (E * G - G * E) := by
  simp only [nsmul_eq_mul]
  calc
    E * ((c : R) * G) - ((c : R) * G) * E =
        (E * (c : R)) * G - (c : R) * (G * E) := by noncomm_ring
    _ = ((c : R) * E) * G - (c : R) * (G * E) := by
          rw [← (Nat.cast_commute c E).eq]
    _ = (c : R) * (E * G - G * E) := by noncomm_ring

/-- All commutators of a power replace distinct factors; excess E modes give zero. -/
theorem iteratedAdjoint_power (E B : ℕ → R) (F : R)
    (hEF : ∀ r, E r * F - F * E r = B r)
    (hEB : ∀ r q, E r * B q = B q * E r)
    (hFB : ∀ r, F * B r = B r * F)
    (rs : List ℕ) (n : ℕ) :
    iteratedAdjoint E rs (F ^ (n + rs.length)) =
      (n + rs.length).descFactorial rs.length • (F ^ n * (rs.map B).prod) := by
  induction rs generalizing n with
  | nil => simp [iteratedAdjoint]
  | cons r rs ih =>
      have hp := ih (n + 1)
      have hc := comm_power_succ (E r) F (B r) (hEF r) (hFB r) n
      have hprod := commute_prod (E r) B (hEB r) rs
      have hstep :
          E r * (F ^ (n + 1) * (rs.map B).prod) -
              (F ^ (n + 1) * (rs.map B).prod) * E r =
            (n + 1) • (F ^ n * (B r * (rs.map B).prod)) := by
        calc
          E r * (F ^ (n + 1) * (rs.map B).prod) -
              (F ^ (n + 1) * (rs.map B).prod) * E r =
            (E r * F ^ (n + 1) - F ^ (n + 1) * E r) *
              (rs.map B).prod +
            F ^ (n + 1) * (E r * (rs.map B).prod -
              (rs.map B).prod * E r) := by noncomm_ring
          _ = ((n + 1) • (F ^ n * B r)) * (rs.map B).prod := by
                rw [hc, sub_eq_zero.mpr hprod]
                simp
          _ = (n + 1) • (F ^ n * (B r * (rs.map B).prod)) := by
                simp [nsmul_eq_mul, mul_assoc]
      simp only [iteratedAdjoint, List.length_cons, List.map_cons, List.prod_cons]
      rw [show n + (rs.length + 1) = n + 1 + rs.length by omega]
      rw [hp]
      calc
        E r * ((n + 1 + rs.length).descFactorial rs.length •
            (F ^ (n + 1) * (rs.map B).prod)) -
          ((n + 1 + rs.length).descFactorial rs.length •
            (F ^ (n + 1) * (rs.map B).prod)) * E r =
          (n + 1 + rs.length).descFactorial rs.length •
            (E r * (F ^ (n + 1) * (rs.map B).prod) -
              (F ^ (n + 1) * (rs.map B).prod) * E r) :=
                comm_nsmul (E r) _ _
        _ = (n + 1 + rs.length).descFactorial rs.length •
              ((n + 1) • (F ^ n * (B r * (rs.map B).prod))) := by rw [hstep]
        _ = (n + 1 + rs.length).descFactorial (rs.length + 1) •
              (F ^ n * (B r * (rs.map B).prod)) := by
                rw [smul_smul, Nat.descFactorial_succ]
                congr 1
                have hn : n + 1 + rs.length - rs.length = n + 1 := by omega
                rw [hn, Nat.mul_comm]

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.iteratedAdjoint_power
