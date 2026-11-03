import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleSeedWords
import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleActual
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeModeRecurrenceBase

/-! Contact words on whole C currents. A contact at mode k sends the C
current to the k-th tail of one A current and kills every A current, so n
contacts polarize a whole coefficient of C^r with the exact falling
factorial r(r-1)...(r-n+1). A single C_0 factor obeys the one-letter Leibniz
rule. All identities hold for every m, with the actual truncated modes. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.SectorWeyl
open Cube (tailSeries tailSeries_coeff)
noncomputable section

/-- The original contact operator of a normalized contact letter. -/
def contactOp (x : Fin 8 × ℕ) : Fin 18 × ℕ := (Fin.natAdd 10 x.1,x.2)

theorem castSucc_ne_center : ∀ e : Fin 8, e.castSucc ≠ (8 : Fin 9) := by decide

theorem wordOp_cons (m : ℕ) (x : Fin 18 × ℕ) (l : List (Fin 18 × ℕ)) (v : Ring ℂ m) :
    wordOp (representation ℂ m) (x :: l) v =
      deriv ℂ m x.1 x.2 (wordOp (representation ℂ m) l v) :=
  rfl

theorem wordOp_smul (m : ℕ) (l : List (Fin 18 × ℕ)) (c : ℂ) (v : Ring ℂ m) :
    wordOp (representation ℂ m) l (c • v) = c • wordOp (representation ℂ m) l v := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [wordOp_cons,wordOp_cons,ih,Derivation.map_smul]

theorem wordOp_nsmul (m : ℕ) (l : List (Fin 18 × ℕ)) (n : ℕ) (v : Ring ℂ m) :
    wordOp (representation ℂ m) l (n • v) = n • wordOp (representation ℂ m) l v := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [wordOp_cons,wordOp_cons,ih,map_nsmul]

theorem wordOp_sub (m : ℕ) (l : List (Fin 18 × ℕ)) (v w : Ring ℂ m) :
    wordOp (representation ℂ m) l (v - w) =
      wordOp (representation ℂ m) l v - wordOp (representation ℂ m) l w := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [wordOp_cons,wordOp_cons,wordOp_cons,ih,map_sub]

theorem contact_mode_center (m : ℕ) (e : Fin 8) (k r : ℕ) :
    deriv ℂ m (Fin.natAdd 10 e) k (mode ℂ m 8 r) = mode ℂ m e.castSucc (k + r) := by
  rw [deriv_mode,actual_contact_coeff,actual_contact_target,if_pos rfl,one_zsmul]

theorem contact_mode_other (m : ℕ) (e : Fin 8) (k r : ℕ) (c : Fin 9) (hc : c ≠ 8) :
    deriv ℂ m (Fin.natAdd 10 e) k (mode ℂ m c r) = 0 := by
  rw [deriv_mode,actual_contact_coeff,if_neg hc,zero_zsmul]

theorem contact_mode_A (m : ℕ) (e e' : Fin 8) (k r : ℕ) :
    deriv ℂ m (Fin.natAdd 10 e) k (mode ℂ m e'.castSucc r) = 0 :=
  contact_mode_other m e k r _ (castSucc_ne_center e')

/-- A contact maps the whole C current to the k-th tail of one A current. -/
theorem contact_series_center (m : ℕ) (e : Fin 8) (k : ℕ) :
    seriesDerivation (deriv ℂ m (Fin.natAdd 10 e) k) (colorCurrent ℂ m 8) =
      tailSeries k (colorCurrent ℂ m e.castSucc) := by
  apply PowerSeries.ext
  intro t
  rw [seriesDerivation_coeff,tailSeries_coeff]
  simp only [colorCurrent,PowerSeries.coeff_mk]
  rw [contact_mode_center,add_comm]

/-- Series annihilated by every contact derivation. -/
def ContactKilled (m : ℕ) (P : PowerSeries (Ring ℂ m)) : Prop :=
  ∀ (e : Fin 8) (k : ℕ), seriesDerivation (deriv ℂ m (Fin.natAdd 10 e) k) P = 0

theorem contactKilled_tail (m : ℕ) (c : Fin 9) (hc : c ≠ 8) (k : ℕ) :
    ContactKilled m (tailSeries k (colorCurrent ℂ m c)) := by
  intro e k'
  apply PowerSeries.ext
  intro t
  rw [seriesDerivation_coeff,tailSeries_coeff]
  simp only [colorCurrent,PowerSeries.coeff_mk,map_zero]
  exact contact_mode_other m e k' _ c hc

theorem contactKilled_mul {m : ℕ} {P Q : PowerSeries (Ring ℂ m)}
    (hP : ContactKilled m P) (hQ : ContactKilled m Q) : ContactKilled m (P * Q) := by
  intro e k
  rw [Derivation.leibniz,hP e k,hQ e k,smul_zero,smul_zero,add_zero]

theorem contactKilled_one (m : ℕ) : ContactKilled m 1 :=
  fun _ _ => Derivation.map_one_eq_zero _

/-- The product of the tails produced by a contact word. -/
def contactProduct (m : ℕ) (l : List (Fin 8 × ℕ)) : PowerSeries (Ring ℂ m) :=
  (l.map fun x => tailSeries x.2 (colorCurrent ℂ m x.1.castSucc)).prod

theorem contactKilled_contactProduct (m : ℕ) (l : List (Fin 8 × ℕ)) :
    ContactKilled m (contactProduct m l) := by
  induction l with
  | nil => exact contactKilled_one m
  | cons x l ih =>
      simp only [contactProduct,List.map_cons,List.prod_cons]
      exact contactKilled_mul (contactKilled_tail m _ (castSucc_ne_center x.1) _) ih

/-- Polarization: n contacts on a whole C^r coefficient, with exact r^(n). -/
theorem wordOp_contacts_center_pow (m r s : ℕ) (l : List (Fin 8 × ℕ))
    (P : PowerSeries (Ring ℂ m)) (hP : ContactKilled m P) :
    wordOp (representation ℂ m) (l.map contactOp)
        (PowerSeries.coeff s (colorCurrent ℂ m 8 ^ r * P)) =
      PowerSeries.coeff s (r.descFactorial l.length •
        (colorCurrent ℂ m 8 ^ (r - l.length) * (contactProduct m l * P))) := by
  induction l with
  | nil => simp [wordOp,contactProduct]
  | cons x l ih =>
      rw [List.map_cons,wordOp_cons,ih]
      change deriv ℂ m (Fin.natAdd 10 x.1) x.2 _ = _
      rw [← seriesDerivation_coeff]
      congr 1
      rw [map_nsmul,Derivation.leibniz,Derivation.leibniz_pow,contact_series_center,
        contactKilled_mul (contactKilled_contactProduct m l) hP x.1 x.2]
      simp only [List.length_cons,contactProduct,List.map_cons,
        List.prod_cons,Nat.descFactorial_succ,smul_eq_mul,nsmul_eq_mul,Nat.cast_mul]
      rw [Nat.sub_sub]
      ring

/-- Each way to remove one letter, with the letter and the rest. -/
def picks {α : Type*} : List α → List (α × List α)
  | [] => []
  | x :: l => (x,l) :: (picks l).map fun p => (p.1,x :: p.2)

theorem derivation_list_sum {A : Type*} [CommRing A] [Algebra ℂ A] (D : Derivation ℂ A A)
    {β : Type*} (L : List β) (f : β → A) :
    D (L.map f).sum = (L.map fun b => D (f b)).sum := by
  induction L with
  | nil => simp
  | cons b L ih => simp only [List.map_cons,List.sum_cons,map_add,ih]

/-- One C_0 factor: exactly one contact of the word may convert it. -/
theorem wordOp_contacts_center_linear (m : ℕ) (l : List (Fin 8 × ℕ)) (Y : Ring ℂ m) :
    wordOp (representation ℂ m) (l.map contactOp) (mode ℂ m 8 0 * Y) =
      mode ℂ m 8 0 * wordOp (representation ℂ m) (l.map contactOp) Y +
        ((picks l).map fun p => mode ℂ m p.1.1.castSucc p.1.2 *
          wordOp (representation ℂ m) (p.2.map contactOp) Y).sum := by
  induction l with
  | nil => simp [wordOp,picks]
  | cons x l ih =>
      have hx : contactOp x = (Fin.natAdd 10 x.1,x.2) := rfl
      rw [List.map_cons,wordOp_cons,ih,hx,map_add,Derivation.leibniz,contact_mode_center,
        derivation_list_sum]
      simp only [picks,List.map_cons,List.sum_cons,List.map_map,Function.comp_def,
        wordOp_cons,hx,smul_eq_mul,Derivation.leibniz,contact_mode_A,mul_zero,add_zero]
      ring

end
#print axioms wordOp_contacts_center_pow
#print axioms wordOp_contacts_center_linear
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
