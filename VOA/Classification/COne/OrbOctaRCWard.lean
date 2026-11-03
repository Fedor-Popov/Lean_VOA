import VOA.Classification.COne.OrbOctaRCVirWords
import VOA.Classification.COne.OrbOctaRCCharged
import VOA.Core.InvariantFormDiagonal

/-! Primary-field measurements along Virasoro descendants. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbOctaRC
open VOA VertexOperatorAlgebra OrbSpan OrbC2c

section General
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (A : VertexOperatorAlgebra V)

theorem primary_self_L {h : ℤ} {x : V} (hx : x ∈ prim A h)
    (k : ℕ) (hk : 0 < k) (n : ℤ) :
    A.L (k : ℤ) (A.smul x n x) =
      (((h - 1) * ((k : ℤ) + 1) - n : ℤ) : ℂ) • A.smul x (n + k) x := by
  obtain ⟨hxg, hxp⟩ := (mem_prim A).mp hx
  have hz (j : ℕ) (hj : 2 ≤ j) : A.smul A.conformalVector (j : ℤ) x = 0 := by
    have he : (j : ℤ) = (((j - 2 : ℕ) : ℤ) + 1) + 1 := by omega
    rw [he]
    exact hxp (j - 2)
  obtain ⟨N, hzero, hcomm⟩ := commBound A A.conformalVector x ((k + 1 : ℕ) : ℤ) n
  have hL : A.L (k : ℤ) = mode (A.Y A.conformalVector) ((k + 1 : ℕ) : ℤ) := by
    simp only [L_def, Nat.cast_add, Nat.cast_one]
  have hc : ⁅A.L (k : ℤ), mode (A.Y x) n⁆ =
      mode (A.Y (A.L (-1) x)) ((k : ℤ) + 1 + n) +
        ((k : ℂ) + 1) • mode (A.Y (A.L 0 x)) ((k : ℤ) + n) := by
    rw [hL, hcomm]
    rw [finN_gBinom_collapse (k + 1) N
      (fun j => mode (A.Y (A.smul A.conformalVector (j : ℤ) x))
        (((k + 1 : ℕ) : ℤ) + n - (j : ℤ)))
      (fun j hj => by simp only [hzero j hj, map_zero, mode_zero])]
    rw [← Finset.sum_range_add_sum_Ico _ (show 2 ≤ k + 1 + 1 by omega)]
    have ht : ∑ j ∈ Finset.Ico 2 (k + 1 + 1),
        gBinom ((k + 1 : ℕ) : ℤ) j •
          mode (A.Y (A.smul A.conformalVector (j : ℤ) x))
            (((k + 1 : ℕ) : ℤ) + n - (j : ℤ)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hz j (Finset.mem_Ico.mp hj).1, map_zero, mode_zero, smul_zero]
    rw [ht, add_zero, Finset.sum_range_succ, Finset.sum_range_one]
    rw [gBinom_natCast_eq_choose (Nat.zero_le (k + 1)),
      gBinom_natCast_eq_choose (show 1 ≤ k + 1 by omega)]
    simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, one_smul,
      Nat.cast_zero, Nat.cast_add, sub_zero]
    rw [show (k : ℤ) + 1 + n - 1 = (k : ℤ) + n by ring]
    rfl
  have hh := DFunLike.congr_fun hc x
  rw [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    LinearMap.add_apply, LinearMap.smul_apply] at hh
  have hkx : A.L (k : ℤ) x = 0 := by
    have he : (k : ℤ) = ((k - 1 : ℕ) : ℤ) + 1 := by omega
    rw [he]; exact hxp (k - 1)
  simp only [hkx, map_zero, sub_zero, ← PreVertexAlgebra.smul_def] at hh
  rw [A.L_zero_grading x hxg, PreVertexAlgebra.smul_smul_left,
    smul_Lneg1_shift, show (k : ℤ) + 1 + n - 1 = n + k by ring,
    show (k : ℤ) + n = n + k by ring] at hh
  rw [hh]
  push_cast
  module

def wardCoeff (h n : ℤ) : List ℕ → ℚ
  | [] => 1
  | k :: ks => (((h - 1) * ((k : ℤ) + 1) - n : ℤ) : ℚ) *
      wardCoeff h (n + k) ks

theorem form_self_desc (U : VirUnitaryForm A) {h : ℤ} {x : V}
    (hx : x ∈ prim A h) (ks : List ℕ) (hks : ∀ k ∈ ks, 0 < k) (q : V) (n : ℤ) :
    U.form (A.smul x n x) (virDesc A ks q) =
      (wardCoeff h n ks : ℂ) * U.form (A.smul x (n + ks.sum) x) q := by
  induction ks generalizing n with
  | nil => simp [virDesc, wardCoeff]
  | cons k ks ih =>
    rw [virDesc, ← U.adjoint, primary_self_L A hx k (hks k (by simp))]
    rw [LinearMap.map_smul, LinearMap.smul_apply,
      ih (fun j hj => hks j (by simp [hj]))]
    simp only [wardCoeff, Rat.cast_mul, Rat.cast_intCast, List.sum_cons,
      Nat.cast_add, smul_eq_mul]
    rw [show n + (k : ℤ) + ks.sum = n + ((k : ℤ) + ks.sum) by ring]
    ring

def wardSum (h n : ℤ) (cs : List (ℚ × List ℕ)) : ℚ :=
  (cs.map fun t => t.1 * wardCoeff h n t.2).sum

theorem form_self_combo (U : VirUnitaryForm A) {h : ℤ} {x : V}
    (hx : x ∈ prim A h) (q : V) (n : ℤ) (N : ℕ) (cs : List (ℚ × List ℕ))
    (hcs : ∀ t ∈ cs, t.2.sum = N ∧ ∀ k ∈ t.2, 0 < k) :
    U.form (A.smul x n x) (virCombo A q cs) =
      (wardSum h n cs : ℂ) * U.form (A.smul x (n + N) x) q := by
  induction cs with
  | nil => simp [virCombo, wardSum]
  | cons t cs ih =>
    have ht := hcs t (by simp)
    rw [show virCombo A q (t :: cs) = (t.1 : ℂ) • virDesc A t.2 q +
      virCombo A q cs from rfl, map_add, LinearMap.map_smulₛₗ,
      form_self_desc A U hx _ ht.2, ht.1, ih (fun u hu => hcs u (by simp [hu]))]
    simp only [wardSum, List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul,
      map_ratCast, smul_eq_mul]
    ring

end General
end VOA.Classification.COne.OrbOctaRC
