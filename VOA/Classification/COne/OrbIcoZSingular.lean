import VOA.Classification.COne.OrbOddChain
import VOA.Classification.COne.OrbIcoSPrimary

/-! The level-thirteen singular vector of the weight-thirty-six icosahedral primary.

This is a genuine state identity, certified by L(1), L(2), and positivity of
Virasoro's form. Its direct Zhu projection is the zero polynomial; applying
it directly to the primary gives no conformal annihilator. Mixed mode
relations, rather than this direct projection, are needed for that purpose.
-/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000

namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbOdd OrbSpan OrbPrim OrbC2b OrbC2c OrbOcta

/-- The normalized singular vector, with coefficient one on L(-1)^13. -/
def s13v : VVec := ofRaw [
  (32201368288215552, 1, [13]),
  (-6281863658835392, 1, [12, 1]),
  (-4139544511687680, 1, [11, 2]),
  (631608657218720, 1, [11, 1, 1]),
  (-3384108036172800, 1, [10, 3]),
  (878216741754880, 1, [10, 2, 1]),
  (-46025529519168, 1, [10, 1, 1, 1]),
  (-3169018363521024, 1, [9, 4]),
  (709434423742240, 1, [9, 3, 1]),
  (303644410656768, 1, [9, 2, 2]),
  (-96040252136576, 1, [9, 2, 1, 1]),
  (2593931430400, 1, [9, 1, 1, 1, 1]),
  (-3055404163166208, 1, [8, 5]),
  (696796944004608, 1, [8, 4, 1]),
  (516369064624128, 1, [8, 3, 2]),
  (-81859748766880, 1, [8, 3, 1, 1]),
  (-71092192531968, 1, [8, 2, 2, 1]),
  (7748169302592, 1, [8, 2, 1, 1, 1]),
  (-129868071984, 1, [8, 1, 1, 1, 1, 1]),
  (-3001859828259840, 1, [7, 6]),
  (648806323282400, 1, [7, 5, 1]),
  (490513877655552, 1, [7, 4, 2]),
  (-77889248407680, 1, [7, 4, 1, 1]),
  (212115083920128, 1, [7, 3, 3]),
  (-117227177619200, 1, [7, 3, 2, 1]),
  (6391157263776, 1, [7, 3, 1, 1, 1]),
  (-17092479320064, 1, [7, 2, 2, 2]),
  (8441315720448, 1, [7, 2, 2, 1, 1]),
  (-474969251712, 1, [7, 2, 1, 1, 1, 1]),
  (5482065120, 1, [7, 1, 1, 1, 1, 1, 1]),
  (333539980917760, 1, [6, 6, 1]),
  (479117664147456, 1, [6, 5, 2]),
  (-76158830026240, 1, [6, 5, 1, 1]),
  (423935220008448, 1, [6, 4, 3]),
  (-117979970641152, 1, [6, 4, 2, 1]),
  (6459490447488, 1, [6, 4, 1, 1, 1]),
  (-51136285155520, 1, [6, 3, 3, 1]),
  (-44928080068608, 1, [6, 3, 2, 2]),
  (14841229564800, 1, [6, 3, 2, 1, 1]),
  (-419003493952, 1, [6, 3, 1, 1, 1, 1]),
  (4395168817152, 1, [6, 2, 2, 2, 1]),
  (-749783618816, 1, [6, 2, 2, 1, 1, 1]),
  (26248604480, 1, [6, 2, 1, 1, 1, 1, 1]),
  (-224546400, 1, [6, 1, 1, 1, 1, 1, 1, 1]),
  (201030961463424, 1, [5, 5, 3]),
  (-55907120624448, 1, [5, 5, 2, 1]),
  (3058688837280, 1, [5, 5, 1, 1, 1]),
  (205801165221120, 1, [5, 4, 4]),
  (-99817647444032, 1, [5, 4, 3, 1]),
  (-43940508770304, 1, [5, 4, 2, 2]),
  (14552197963136, 1, [5, 4, 2, 1, 1]),
  (-411966054912, 1, [5, 4, 1, 1, 1, 1]),
  (-38200858951680, 1, [5, 3, 3, 2]),
  (6319095457600, 1, [5, 3, 3, 1, 1]),
  (11263816190976, 1, [5, 3, 2, 2, 1]),
  (-1283289506048, 1, [5, 3, 2, 1, 1, 1]),
  (22505497112, 1, [5, 3, 1, 1, 1, 1, 1]),
  (840359411712, 1, [5, 2, 2, 2, 2]),
  (-578688608256, 1, [5, 2, 2, 2, 1, 1]),
  (51129753920, 1, [5, 2, 2, 1, 1, 1, 1]),
  (-1236841424, 1, [5, 2, 1, 1, 1, 1, 1, 1]),
  (8229936, 1, [5, 1, 1, 1, 1, 1, 1, 1, 1]),
  (-17150097101760, 1, [4, 4, 4, 1]),
  (-39492551688192, 1, [4, 4, 3, 2]),
  (6555258747360, 1, [4, 4, 3, 1, 1]),
  (5855739713536, 1, [4, 4, 2, 2, 1]),
  (-669678653376, 1, [4, 4, 2, 1, 1, 1]),
  (11791663920, 1, [4, 4, 1, 1, 1, 1, 1]),
  (-11462977622016, 1, [4, 3, 3, 3]),
  (10197349808128, 1, [4, 3, 3, 2, 1]),
  (-582500196576, 1, [4, 3, 3, 1, 1, 1]),
  (3053023985664, 1, [4, 3, 2, 2, 2]),
  (-1581388667904, 1, [4, 3, 2, 2, 1, 1]),
  (93436902880, 1, [4, 3, 2, 1, 1, 1, 1]),
  (-1133834520, 1, [4, 3, 1, 1, 1, 1, 1, 1]),
  (-239642394624, 1, [4, 2, 2, 2, 2, 1]),
  (57087365120, 1, [4, 2, 2, 2, 1, 1, 1]),
  (-3142927424, 1, [4, 2, 2, 1, 1, 1, 1, 1]),
  (56435808, 1, [4, 2, 1, 1, 1, 1, 1, 1, 1]),
  (-303732, 1, [4, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
  (740561027584, 1, [3, 3, 3, 3, 1]),
  (1331498041344, 1, [3, 3, 3, 2, 2]),
  (-459333245952, 1, [3, 3, 3, 2, 1, 1]),
  (13555628744, 1, [3, 3, 3, 1, 1, 1, 1]),
  (-418006646784, 1, [3, 3, 2, 2, 2, 1]),
  (74604032512, 1, [3, 3, 2, 2, 1, 1, 1]),
  (-2735112016, 1, [3, 3, 2, 1, 1, 1, 1, 1]),
  (24526788, 1, [3, 3, 1, 1, 1, 1, 1, 1, 1]),
  (-38220595200, 1, [3, 2, 2, 2, 2, 2]),
  (34383716352, 1, [3, 2, 2, 2, 2, 1, 1]),
  (-4237076480, 1, [3, 2, 2, 2, 1, 1, 1, 1]),
  (160960800, 1, [3, 2, 2, 1, 1, 1, 1, 1, 1]),
  (-2244528, 1, [3, 2, 1, 1, 1, 1, 1, 1, 1, 1]),
  (10010, 1, [3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
  (2123366400, 1, [2, 2, 2, 2, 2, 2, 1]),
  (-791691264, 1, [2, 2, 2, 2, 2, 1, 1, 1]),
  (75851776, 1, [2, 2, 2, 2, 1, 1, 1, 1, 1]),
  (-2846272, 1, [2, 2, 2, 1, 1, 1, 1, 1, 1, 1]),
  (48048, 1, [2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
  (-364, 1, [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
  (1, 1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])]

def s13chk (m : ℕ) : Bool :=
  match bindV (lowerF 36 1 64 m) s13v with
  | some r => isZeroK (normK r)
  | none => false

set_option maxHeartbeats 2000000 in
-- The kernel normal-orders all 101 level-thirteen words.
theorem s13chk_one : s13chk 1 = true := by decide +kernel

set_option maxHeartbeats 2000000 in
-- The kernel normal-orders all 101 level-thirteen words.
theorem s13chk_two : s13chk 2 = true := by decide +kernel

theorem s13v_spec : ∀ p ∈ s13v, p.2.sum = 13 ∧ p.2 ≠ [] ∧ posW p.2 = true := by
  decide +kernel

/-- The direct Zhu image of this singular vector vanishes identically. -/
theorem s13_zhu_polynomial_zero : zp (zhuV 36 s13v) = 0 := by
  have h : ptrim (zhuV 36 s13v) = [] := by decide +kernel
  rw [← zp_ptrim, h]; rfl

section General
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {W : VertexOperatorAlgebra V} {x : V}

theorem s13chk_sound (hc : W.centralCharge = ((1 : ℚ) : ℂ))
    (hx : ∀ m : ℕ, 1 ≤ m → W.L (m : ℤ) x = 0)
    (hx0 : W.L 0 x = ((36 : ℚ) : ℂ) • x)
    {m : ℕ} (hk : s13chk m = true) : W.L (m : ℤ) (evV W x s13v) = 0 := by
  unfold s13chk at hk
  split at hk
  · rename_i r hr
    rw [← bindV_sound (fun w r h => lowerF_sound hc hx hx0 _ _ w r h) s13v r hr]
    exact evV_eq_zero_of_isZeroK hk
  · exact absurd hk (by simp)
end General

noncomputable section
open OrbIco OrbIcoS

theorem X_primary : Xico ∈ prim Wi 36 := by
  rw [mem_prim]
  refine ⟨Xico_grading, fun m => ?_⟩
  apply Subtype.ext
  exact ((mem_prim _).mp Xico_ambient_primary).2 m

/-- The level-thirteen singular vector vanishes on the actual A5 primary. -/
theorem s13_zero : evV Wi Xico s13v = 0 := by
  have hx : ∀ m : ℕ, 1 ≤ m → Wi.L (m : ℤ) Xico = 0 := by
    intro m hm
    have h := ((mem_prim _).mp X_primary).2 (m - 1)
    rwa [show ((m - 1 : ℕ) : ℤ) + 1 = m by omega] at h
  have hx0 : Wi.L 0 Xico = ((36 : ℚ) : ℂ) • Xico := by
    rw [Wi.L_zero_grading _ Xico_grading]; norm_num
  have hc : Wi.centralCharge = ((1 : ℚ) : ℂ) := by
    change (V2m 1 le_rfl).centralCharge = _
    simpa using V2m_centralCharge 1 le_rfl
  have hp : evV Wi Xico s13v ∈ prim Wi (36 + (13 : ℕ)) := by
    rw [mem_prim]
    refine ⟨evV_mem_grading Xico_grading (fun p hp => (s13v_spec p hp).1), fun m => ?_⟩
    have h := L_pos_of_L1_L2 (s13chk_sound hc hx hx0 s13chk_one)
      (s13chk_sound hc hx hx0 s13chk_two) (m + 1) (by omega)
    simpa using h
  have hl := evV_mem_lowerDesc Xico_grading (N := 13) (v := s13v) s13v_spec
  have hz := prim_inf_lowerDesc (W := Wi)
    ((v2VirUnitary_holds.some).restrict (orbifold ico)) (36 + (13 : ℕ))
  have hmem : evV Wi Xico s13v ∈
      prim Wi (36 + (13 : ℕ)) ⊓ lowerDesc Wi (36 + (13 : ℕ)) := ⟨hp, hl⟩
  rw [hz] at hmem
  exact (Submodule.mem_bot ℂ).mp hmem

end
end VOA.Classification.COne.OrbIcoZ
