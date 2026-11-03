import VOA.Classification.COne.OrbIcoVProbeNonzero
import VOA.Classification.COne.OrbIcoZSingular

/-! Actual scalar null-vector recurrences for the Casimir-separated channels.
The recurrence never divides by its leading coefficient, so it retains all resonances. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbIco OrbIcoS OrbOctaRC
  VOA.LatGen VOA.LatGen.Triplet

/-- Evaluate a negative descendant on the right of a primary field after probing. -/
def nullWord (h : ℤ) (s : ℤ → ℂ) (m : ℤ) : List ℕ → ℂ
  | [] => s m
  | k :: ks => (if k = 2 then (1 / 2 : ℂ) else 0) * nullWord h s m ks +
      (((h - 1) * ((k : ℤ) - 1) + m : ℤ) : ℂ) * nullWord h s (m - k) ks

def nullCombo (h : ℤ) (s : ℤ → ℂ) (m : ℤ) (cs : List (ℚ × List ℕ)) : ℂ :=
  (cs.map fun t => (t.1 : ℂ) * nullWord h s m t.2).sum

section Generic
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (A : VertexOperatorAlgebra V) (a b : V) (h : ℤ)
  (ha : a ∈ A.grading h) (hap : ∀ k : ℕ, 1 ≤ k → A.L (k : ℤ) a = 0)
  (f : V →ₗ[ℂ] ℂ)
  (hf : ∀ k : ℕ, 0 < k → ∀ x, f (A.L (-(k : ℤ)) x) =
    (if k = 2 then (1 / 2 : ℂ) else 0) * f x)

include ha hap hf in
theorem probe_primary_negative (k : ℕ) (hk : 0 < k) (m : ℤ) (v : V) :
    f (A.smul a m (A.L (-(k : ℤ)) v)) =
      (if k = 2 then (1 / 2 : ℂ) else 0) * f (A.smul a m v) +
      (((h - 1) * ((k : ℤ) - 1) + m : ℤ) : ℂ) * f (A.smul a (m - k) v) := by
  have he := congrArg f (OrbOdd.L_smul_primary ha hap (-(k : ℤ)) m v)
  rw [map_add, map_smul, hf k hk] at he
  simp only [smul_eq_mul, neg_add_eq_sub] at he
  push_cast at he ⊢
  linear_combination -he

include ha hap hf in
theorem nullWord_sound (m : ℤ) (ks : List ℕ)
    (hks : ∀ k ∈ ks, 0 < k) :
    nullWord h (fun n => f (A.smul a n b)) m ks =
      f (A.smul a m (virDesc A ks b)) := by
  induction ks generalizing m with
  | nil => rfl
  | cons k ks ih =>
    rw [nullWord, virDesc, probe_primary_negative A a h ha hap f hf k (hks k (by simp))]
    rw [ih m (fun j hj => hks j (by simp [hj])),
      ih (m - k) (fun j hj => hks j (by simp [hj]))]

include ha hap hf in
theorem nullCombo_sound (m : ℤ) (cs : List (ℚ × List ℕ))
    (hcs : ∀ t ∈ cs, ∀ k ∈ t.2, 0 < k) :
    nullCombo h (fun n => f (A.smul a n b)) m cs =
      f (A.smul a m (virCombo A b cs)) := by
  induction cs with
  | nil => simp [nullCombo, virCombo]
  | cons t cs ih =>
    rw [nullCombo, List.map_cons, List.sum_cons, nullWord_sound A a b h ha hap f hf
      m t.2 (hcs t (by simp))]
    change _ + nullCombo h (fun n => f (A.smul a n b)) m cs = _
    rw [ih (fun u hu => hcs u (by simp [hu]))]
    simp [virCombo, map_add, map_smul, smul_eq_mul]

end Generic

theorem sixthProbe_negative (k : ℕ) (hk : 0 < k) (x : (orbifold ico).carrier) :
    sixthProbe (Wi.L (-(k : ℤ)) x) =
      (if k = 2 then (1 / 2 : ℂ) else 0) * sixthProbe x := by
  have he := sixthProbe_L (k - 1) x
  rw [show -((k - 1 : ℕ) : ℤ) - 1 = -(k : ℤ) by omega] at he
  simpa only [show k - 1 = 1 ↔ k = 2 by omega] using he

theorem vacuumProbe_negative (k : ℕ) (hk : 0 < k) (x : (orbifold ico).carrier) :
    vacuumProbe (Wi.L (-(k : ℤ)) x) =
      (if k = 2 then (1 / 2 : ℂ) else 0) * vacuumProbe x := by
  rw [vacuumProbe_apply, vacuumProbe_apply, sixthProbe_negative k hk]
  have he := OrbIcoS.neutralProbe_L (k - 1) x
  rw [show -((k - 1 : ℕ) : ℤ) - 1 = -(k : ℤ) by omega] at he
  simp only [show k - 1 = 1 ↔ k = 2 by omega] at he
  rw [he]
  ring

private theorem Xico_positive (k : ℕ) (hk : 1 ≤ k) : Wi.L (k : ℤ) Xico = 0 := by
  have he := ((mem_prim _).mp OrbIcoZ.X_primary).2 (k - 1)
  rwa [show ((k - 1 : ℕ) : ℤ) + 1 = k by omega] at he

private theorem virCombo_s13_zero : virCombo Wi Xico OrbIcoZ.s13v = 0 := by
  exact OrbIcoZ.s13_zero

private theorem s13_positive (t : ℚ × List ℕ) (ht : t ∈ OrbIcoZ.s13v) :
    ∀ k ∈ t.2, 0 < k := by
  have hs := (OrbIcoZ.s13v_spec t ht).2.2
  simpa only [OrbOdd.posW, List.all_eq_true, decide_eq_true_eq] using hs

/-- The vacuum channel obeys the genuine level-thirteen null-vector identity. -/
theorem vacuum_null_equation (m : ℤ) :
    nullCombo 36 (fun n => vacuumProbe (Wi.smul Xico n Xico)) m OrbIcoZ.s13v = 0 := by
  rw [nullCombo_sound Wi Xico Xico 36 Xico_grading Xico_positive vacuumProbe
    vacuumProbe_negative m OrbIcoZ.s13v
    s13_positive]
  rw [virCombo_s13_zero, PreVertexAlgebra.smul_zero_right, map_zero]

/-- The spin-six channel obeys the same identity, retaining the resonant equations. -/
theorem sixth_null_equation (m : ℤ) :
    nullCombo 36 (fun n => sixthProbe (Wi.smul Xico n Xico)) m OrbIcoZ.s13v = 0 := by
  rw [nullCombo_sound Wi Xico Xico 36 Xico_grading Xico_positive sixthProbe
    sixthProbe_negative m OrbIcoZ.s13v
    s13_positive]
  rw [virCombo_s13_zero, PreVertexAlgebra.smul_zero_right, map_zero]

end VOA.Classification.COne.OrbIcoV
