import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterContactPolar
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterStaticPolarAll

/-! The three C-contact source shapes of the quintic slice lie in J.
(S0) r static contacts on coeff_T C^r give r! times a static template word.
(SD) One mode-one contact gives a tail factor; z*tail(A) = A - A_0 turns it
into a quintic template minus A_0 times a quartic template.
(SC) A mode-one seed shift obeys S_1 xi_(5,T-1) = 5 xi_(5,T) - 5 C_0 xi_(4,T);
contacts on C_0 xi_(4,T) give A_0 times quartic templates by the one-letter
Leibniz rule. Every statement holds for every m >= 2 with T = 2m-3. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.D4FusionContact.Polynomial
open Cube (tailSeries tailSeries_coeff quadraticCubicPolarIdeal)
open Cube.CenterStaticPolar (QuinticShape QuarticShape bitCount bitCount_perm
  quintic_static_coeff_mem quartic_static_coeff_mem)
noncomputable section

/-- Normalized cube index of an original contact color (the involution 3 <-> 4). -/
def cubeIndex : Fin 8 → Fin 8 := ![0,1,2,4,3,5,6,7]

theorem cubeColor_cubeIndex : ∀ e : Fin 8, Cube.cubeColor (cubeIndex e) = e.castSucc := by
  decide

/-- The normalized color word of a contact list; modes are forgotten. -/
def contactWord (l : List (Fin 8 × ℕ)) : List (Fin 8) := l.map fun x => cubeIndex x.1

theorem tailSeries_zero {A : Type*} [CommRing A] (B : PowerSeries A) : tailSeries 0 B = B := by
  apply PowerSeries.ext
  intro t
  rw [tailSeries_coeff,Nat.add_zero]

theorem colorCurrent_castSucc (m : ℕ) (e : Fin 8) :
    colorCurrent ℂ m e.castSucc = AllM.current m (Cube.cubeColor (cubeIndex e)) := by
  rw [cubeColor_cubeIndex]
  rfl

theorem contactProduct_cons (m : ℕ) (x : Fin 8 × ℕ) (l : List (Fin 8 × ℕ)) :
    contactProduct m (x :: l) =
      tailSeries x.2 (colorCurrent ℂ m x.1.castSucc) * contactProduct m l := by
  simp only [contactProduct,List.map_cons,List.prod_cons]

/-- Static contacts produce exactly the original current word. -/
theorem contactProduct_static (m : ℕ) (l : List (Fin 8 × ℕ)) (hl : ∀ x ∈ l, x.2 = 0) :
    contactProduct m l =
      ((contactWord l).map fun i => AllM.current m (Cube.cubeColor i)).prod := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      rw [contactProduct_cons,hl x List.mem_cons_self,tailSeries_zero,colorCurrent_castSucc,
        ih (fun y hy => hl y (List.mem_cons_of_mem x hy))]
      simp only [contactWord,List.map_cons,List.prod_cons]

theorem contactProduct_perm (m : ℕ) {l l' : List (Fin 8 × ℕ)} (h : l.Perm l') :
    contactProduct m l = contactProduct m l' :=
  (h.map _).prod_eq

theorem contactWord_perm {l l' : List (Fin 8 × ℕ)} (h : l.Perm l') :
    (contactWord l).Perm (contactWord l') :=
  h.map _

theorem quinticShape_perm {w v : List (Fin 8)} (h : w.Perm v) (hw : QuinticShape w) :
    QuinticShape v := by
  obtain ⟨hl,h0,h1,h2⟩ := hw
  exact ⟨h.length_eq.symm.trans hl,(bitCount_perm h 0).symm.trans h0,
    (bitCount_perm h 1).symm.trans h1,(bitCount_perm h 2).symm.trans h2⟩

theorem bitCount_cons (c : Fin 8) (w : List (Fin 8)) (a : ℕ) :
    bitCount (c :: w) a = c.val / 2 ^ a % 2 + bitCount w a := by
  simp only [bitCount,List.map_cons,List.sum_cons]

/-- Removing one letter from a quintic template leaves a quartic template. -/
theorem quarticShape_of_quinticShape_cons (c : Fin 8) (w : List (Fin 8))
    (h : QuinticShape (c :: w)) : QuarticShape w := by
  obtain ⟨hl,h0,h1,h2⟩ := h
  rw [bitCount_cons] at h0 h1 h2
  have b0 : c.val / 2 ^ 0 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have b1 : c.val / 2 ^ 1 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have b2 : c.val / 2 ^ 2 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  simp only [List.length_cons] at hl
  refine ⟨by omega,by omega,by omega,by omega⟩

/-- (S0) Static contacts on a static C^r coefficient give a template in J. -/
theorem static_contacts_mem (m r : ℕ) (l : List (Fin 8 × ℕ)) (hl : ∀ x ∈ l, x.2 = 0)
    (hlen : l.length = r)
    (hshape : (r = 5 ∧ QuinticShape (contactWord l)) ∨
      (r = 4 ∧ QuarticShape (contactWord l))) :
    wordOp (representation ℂ m) (l.map contactOp)
        (PowerSeries.coeff (2 * m - 3) (colorCurrent ℂ m 8 ^ r)) ∈
      quadraticCubicPolarIdeal m := by
  have h := wordOp_contacts_center_pow m r (2 * m - 3) l 1 (contactKilled_one m)
  rw [mul_one] at h
  rw [h,hlen,Nat.sub_self,pow_zero,one_mul,mul_one,contactProduct_static m l hl,map_nsmul]
  apply nsmul_mem
  rcases hshape with ⟨-,hq⟩ | ⟨-,hq⟩
  · exact quintic_static_coeff_mem m _ hq
  · exact quartic_static_coeff_mem m _ hq

/-- Truncated tails: the (T-1)-st coefficient against a first tail. -/
theorem coeff_tail_one {A : Type*} [CommRing A] (B Q : PowerSeries A) (T : ℕ) (hT : 1 ≤ T) :
    PowerSeries.coeff (T - 1) (tailSeries 1 B * Q) =
      PowerSeries.coeff T (B * Q) - PowerSeries.coeff 0 B * PowerSeries.coeff T Q := by
  have h := Cube.coeff_tailSeries_mul B Q (T - 1) 1
  rw [Nat.sub_add_cancel hT] at h
  simpa only [Finset.range_one,Finset.sum_singleton,Nat.sub_zero] using h

/-- (SD) One mode-one contact and four static contacts, at coefficient T-1. -/
theorem single_contact_shift_mem (m : ℕ) (hm : 2 ≤ m) (x : Fin 8 × ℕ) (hx : x.2 = 1)
    (rest : List (Fin 8 × ℕ)) (hrest : ∀ y ∈ rest, y.2 = 0)
    (hshape : QuinticShape (contactWord (x :: rest))) :
    PowerSeries.coeff (2 * m - 3 - 1) (contactProduct m (x :: rest)) ∈
      quadraticCubicPolarIdeal m := by
  rw [contactProduct_cons,hx,coeff_tail_one _ _ _ (by omega)]
  apply Ideal.sub_mem
  · have hs := contactProduct_static m ((x.1,0) :: rest)
      (by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · rfl
        · exact hrest y hy)
    rw [contactProduct_cons,tailSeries_zero] at hs
    rw [hs]
    exact quintic_static_coeff_mem m _ (by simpa [contactWord] using hshape)
  · apply Ideal.mul_mem_left
    rw [contactProduct_static m rest hrest]
    apply quartic_static_coeff_mem m
    exact quarticShape_of_quinticShape_cons _ _ (by simpa [contactWord] using hshape)

theorem monoShift_monoMode (m k r : ℕ) :
    monoShift ℂ m k (monoMode ℂ m r) = monoMode ℂ m (k + r) := by
  by_cases hr : r < m
  · rw [monoMode,dif_pos hr]
    exact MvPolynomial.mkDerivation_X ℂ _ _
  · have hkr : ¬ k + r < m := by omega
    rw [monoMode,dif_neg hr,map_zero,monoMode,dif_neg hkr]

theorem monoShift_series (m k : ℕ) :
    seriesDerivation (monoShift ℂ m k) (monoCurrent ℂ m) =
      tailSeries k (monoCurrent ℂ m) := by
  apply PowerSeries.ext
  intro t
  rw [seriesDerivation_coeff,tailSeries_coeff]
  simp only [monoCurrent,PowerSeries.coeff_mk]
  rw [monoShift_monoMode,add_comm]

/-- The mode-one seed shift of a fifth power, mapped to the C color. -/
theorem shift_one_seed (m s : ℕ) :
    monoMap ℂ m 8 (monoShift ℂ m 1 (PowerSeries.coeff s (monoCurrent ℂ m ^ 5))) =
      5 • PowerSeries.coeff (s + 1) (colorCurrent ℂ m 8 ^ 5) -
        5 • (mode ℂ m 8 0 * PowerSeries.coeff (s + 1) (colorCurrent ℂ m 8 ^ 4)) := by
  have h0 : seriesDerivation (monoShift ℂ m 0) (monoCurrent ℂ m) = monoCurrent ℂ m := by
    rw [monoShift_series,tailSeries_zero]
  have hrec := Cube.coefficient_power_mode_recurrence (monoShift ℂ m 1) (monoShift ℂ m 0)
    (monoCurrent ℂ m) (monoCurrent ℂ m) 4 s 1 (monoShift_series m 1) h0
  rw [Cube.derivation_power_coeff (monoShift ℂ m 0) (monoCurrent ℂ m) (monoCurrent ℂ m) 4
    (s + 1) h0,← pow_succ'] at hrec
  rw [hrec]
  simp only [Finset.range_one,Finset.sum_singleton,Nat.sub_zero,map_sub,map_nsmul,map_mul,
    monoMap_seed]
  congr 3
  simp only [monoCurrent,PowerSeries.coeff_mk,monoMap_mode]

theorem picks_perm {α : Type*} : ∀ (l : List α), ∀ p ∈ picks l, (p.1 :: p.2).Perm l
  | [] => by simp [picks]
  | x :: l => by
      intro p hp
      simp only [picks,List.mem_cons,List.mem_map] at hp
      rcases hp with rfl | ⟨q,hq,rfl⟩
      · exact List.Perm.refl _
      · exact (List.Perm.swap _ _ _).trans ((picks_perm l q hq).cons x)

/-- (SC) Static contacts on the mode-one shift of a fifth-power C seed. -/
theorem shift_seed_contacts_mem (m : ℕ) (hm : 2 ≤ m) (l : List (Fin 8 × ℕ))
    (hl : ∀ x ∈ l, x.2 = 0) (hlen : l.length = 5) (hshape : QuinticShape (contactWord l)) :
    wordOp (representation ℂ m) (l.map contactOp)
        (monoMap ℂ m 8 (monoShift ℂ m 1
          (PowerSeries.coeff (2 * m - 3 - 1) (monoCurrent ℂ m ^ 5)))) ∈
      quadraticCubicPolarIdeal m := by
  rw [shift_one_seed,Nat.sub_add_cancel (by omega : 1 ≤ 2 * m - 3),wordOp_sub,wordOp_nsmul,
    wordOp_nsmul,wordOp_contacts_center_linear]
  apply Ideal.sub_mem
  · exact nsmul_mem (static_contacts_mem m 5 l hl hlen (Or.inl ⟨rfl,hshape⟩)) 5
  · apply nsmul_mem
    apply Ideal.add_mem
    · apply Ideal.mul_mem_left
      have h := wordOp_contacts_center_pow m 4 (2 * m - 3) l 1 (contactKilled_one m)
      rw [mul_one] at h
      rw [h,hlen]
      simp
    · apply list_sum_mem
      intro y hy
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hy
      have hperm := picks_perm l p hp
      apply Ideal.mul_mem_left
      apply static_contacts_mem m 4 p.2
        (fun x hx => hl x (hperm.subset (List.mem_cons_of_mem _ hx)))
        (by have := hperm.length_eq; simp only [List.length_cons] at this; omega)
      refine Or.inr ⟨rfl,quarticShape_of_quinticShape_cons (cubeIndex p.1.1) _ ?_⟩
      exact quinticShape_perm (contactWord_perm hperm.symm) hshape

end
#print axioms static_contacts_mem
#print axioms single_contact_shift_mem
#print axioms shift_seed_contacts_mem
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
