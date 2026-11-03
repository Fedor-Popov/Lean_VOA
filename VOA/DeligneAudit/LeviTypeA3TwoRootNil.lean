import VOA.DeligneAudit.LeviTypeA3SimpleLength
import VOA.DeligneAudit.DeligneFusionFiniteGAlg
import VOA.DeligneAudit.LeviTypeAStepSl2

/-! An FD-free nilpotence bound for the top of a two-step root string. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.FiniteG

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- A commutator of two lowering operators is nilpotent on the common
highest-weight vector, given the two length-two Serre relations. -/
theorem two_root_nil_large (X Y Z : Module.End ℂ V) (w : V) (p q : ℕ)
    (hXY : adR X Y = Z)
    (hXXY : (adR X)^[2] Y = 0)
    (hYYX : (adR Y)^[2] X = 0)
    (hY : (Y ^ (p + 1)) w = 0)
    (hX : (X ^ (q + 1)) w = 0) :
    (Z ^ (p + 1 + 2 * q)) w = 0 := by
  have hYpow : ∀ b : ℕ, (Y ^ (p + 1 + 2 * b)) ((X ^ b) w) = 0 := by
    intro b
    induction b with
    | zero => simpa using hY
    | succ b ih =>
        have ht := pow_kill_of_ad Y X 2 (p + 1 + 2 * b) ((X ^ b) w)
          hYYX ih
        have hexp : p + 1 + 2 * (b + 1) = 2 + (p + 1 + 2 * b) := by omega
        rw [hexp, pow_add, pow_succ' X b]
        rw [show p + 1 + 2 * b + 2 = 2 + (p + 1 + 2 * b) by omega,
          pow_add] at ht
        simpa only [pow_two, Module.End.mul_apply] using ht
  have hYN : ∀ b < q + 1,
      (Y ^ (p + 1 + 2 * q)) ((X ^ b) w) = 0 := by
    intro b hb
    exact pow_kill_mono Y (hYpow b) (by omega)
  have ht := top_nil X Y 1 (q + 1) (p + 1 + 2 * q) w
    hXXY hX hYN
  simpa only [Function.iterate_one, hXY] using ht

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.two_root_nil_large
