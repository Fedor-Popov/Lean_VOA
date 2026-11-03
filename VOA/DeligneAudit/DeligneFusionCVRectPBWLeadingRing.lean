import VOA.DeligneAudit.DeligneFusionCVPolarization

/-!
# The first and second contractions in a mixed current commutator

These operator identities expose the top PBW term and the shorter double
contraction. They do not assume a polynomial initial ideal or a dimension bound.
-/

namespace VOA.DeligneAudit.A2.CVRectPBWLeading

variable {A : Type*} [Ring A]

/-- Move a central-commutator operator through an arbitrary power. -/
theorem power_mul_central {Z X Y : A} (hZX : Z * X - X * Z = Y)
    (hZY : Z * Y = Y * Z) (n : ℕ) :
    Z ^ n * X = X * Z ^ n + n • (Y * Z ^ (n - 1)) := by
  cases n with
  | zero => simp
  | succ n =>
      have hXZ : X * Z - Z * X = -Y := by rw [← hZX]; noncomm_ring
      have hZY' : Z * (-Y) = (-Y) * Z := by simp only [mul_neg, neg_mul, hZY]
      simpa only [Nat.add_sub_cancel, neg_mul, smul_neg, sub_neg_eq_add] using
        CVPolarization.power_mul_operator hXZ hZY' n

/-- The commutator with a quadratic coefficient has a single-contraction
term of top PBW length and a double-contraction term one length shorter. -/
theorem power_mul_two_commutator {Z X₁ X₂ Y₁ Y₂ : A}
    (hZX₁ : Z * X₁ - X₁ * Z = Y₁) (hZX₂ : Z * X₂ - X₂ * Z = Y₂)
    (hZY₁ : Z * Y₁ = Y₁ * Z) (hZY₂ : Z * Y₂ = Y₂ * Z)
    (hY₁X₂ : Y₁ * X₂ = X₂ * Y₁) (r : ℕ) :
    Z ^ (r + 1) * (X₁ * X₂) - (X₁ * X₂) * Z ^ (r + 1) =
      (r + 1) • (X₁ * Y₂ * Z ^ r) +
      (r + 1) • (X₂ * Y₁ * Z ^ r) +
      (r + 1) • (r • (Y₁ * Y₂ * Z ^ (r - 1))) := by
  have h₁ := power_mul_central hZX₁ hZY₁ (r + 1)
  have h₂ := power_mul_central hZX₂ hZY₂ (r + 1)
  have h₃ := power_mul_central hZX₂ hZY₂ r
  simp only [Nat.add_sub_cancel] at h₁ h₂
  have he : Z ^ (r + 1) * (X₁ * X₂) =
      X₁ * (Z ^ (r + 1) * X₂) + (r + 1) • (Y₁ * (Z ^ r * X₂)) := by
    rw [← mul_assoc, h₁, add_mul, smul_mul_assoc, mul_assoc, mul_assoc]
  rw [h₂, h₃] at he
  simp only [mul_add, mul_smul_comm, smul_add, ← mul_assoc] at he
  rw [hY₁X₂] at he
  rw [← mul_assoc, he]
  abel

end VOA.DeligneAudit.A2.CVRectPBWLeading

#print axioms VOA.DeligneAudit.A2.CVRectPBWLeading.power_mul_central
#print axioms VOA.DeligneAudit.A2.CVRectPBWLeading.power_mul_two_commutator
