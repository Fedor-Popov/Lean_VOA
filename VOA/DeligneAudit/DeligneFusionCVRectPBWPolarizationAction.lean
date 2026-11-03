import VOA.DeligneAudit.DeligneFusionCVRectFiltered

/-!
# Positive zero modes preserve the actual PBW filtration

Cartan currents preserve negative-word length. Raising zero modes replace
a highest-root factor by a simple-root factor, or create a Cartan factor
which contributes only a shorter word. All statements concern the actual
current representation; no graded polarization or ideal inclusion is assumed.
-/

namespace VOA.DeligneAudit.A2.CVRectPBWPolarization

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open CVFamily CVRectFiltered

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (R : CurrentModule bracketTable V) (w : V)

def cartanRoot (b : Bool) : Fin 8 := if b then 7 else 6
def raisingRoot (b : Bool) : Fin 8 := if b then 1 else 0

def cartanCoeff (b : Bool) (a : Fin 3) : ℂ :=
  if b then ![1, -1, -2] a else ![-2, -1, 1] a

theorem cartan_comm (b : Bool) (a : Fin 3) (s r : ℕ) (v : V) :
    R.op (cartanRoot b) s (R.op (negRoot a) r v) -
      R.op (negRoot a) r (R.op (cartanRoot b) s v) =
        cartanCoeff b a • R.op (negRoot a) (s + r) v := by
  rw [R.comm]
  cases b <;> fin_cases a <;>
    simp [cartanRoot, cartanCoeff, negRoot, Fin.sum_univ_eight, bracketTable]

theorem nword_mem_Ple (l : List NegLtr) : nword R w l ∈ Ple R w l.length :=
  Submodule.subset_span ⟨l, by simp, rfl⟩

theorem cartan_generator_mem {ε ν ϱ : Weight} {j : ℕ} (h : CV3Rel R w ε ν ϱ j)
    (b : Bool) (s : ℕ) : R.op (cartanRoot b) s w ∈ Ple R w 0 := by
  have hw : w ∈ Ple R w 0 := nword_mem_Ple R w []
  cases s with
  | zero =>
      cases b
      · rw [cartanRoot, if_neg (by decide), h.cartan_first]
        exact Submodule.smul_mem _ _ hw
      · rw [cartanRoot, if_pos rfl, h.cartan_second]
        exact Submodule.smul_mem _ _ hw
  | succ s =>
      have hc : 6 ≤ (cartanRoot b).val := by cases b <;> decide
      rw [h.cartan_pos _ hc _ (by omega)]
      exact Submodule.zero_mem _

theorem cartan_nword_mem {ε ν ϱ : Weight} {j : ℕ} (h : CV3Rel R w ε ν ϱ j)
    (b : Bool) (s : ℕ) (l : List NegLtr) :
    R.op (cartanRoot b) s (nword R w l) ∈ Ple R w l.length := by
  induction l with
  | nil => exact cartan_generator_mem R w h b s
  | cons x l ih =>
      have he := cartan_comm R b x.1 s x.2 (nword R w l)
      have he' : R.op (cartanRoot b) s (R.op (negRoot x.1) x.2 (nword R w l)) =
          R.op (negRoot x.1) x.2 (R.op (cartanRoot b) s (nword R w l)) +
            cartanCoeff b x.1 • R.op (negRoot x.1) (s + x.2) (nword R w l) := by
        simpa only [add_comm] using (sub_eq_iff_eq_add.mp he)
      rw [nword_cons, he']
      apply Submodule.add_mem
      · exact Pbelow_op R w x.1 x.2 (l.length + 1) ih
      · exact Submodule.smul_mem _ _ (nword_mem_Ple R w ((x.1, s + x.2) :: l))

theorem cartan_Pbelow {ε ν ϱ : Weight} {j : ℕ} (h : CV3Rel R w ε ν ϱ j)
    (b : Bool) (s n : ℕ) :
    Pbelow R w n ≤ (Pbelow R w n).comap (R.op (cartanRoot b) s) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, rfl⟩
  exact Pbelow_mono R w (by omega) (cartan_nword_mem R w h b s l)

def raisingTail (b : Bool) (a : Fin 3) (r : ℕ) (v : V) : V :=
  if b then ![0, R.op 3 r v, R.op 7 r v] a
  else ![R.op 6 r v, -R.op 4 r v, 0] a

theorem raising_comm (b : Bool) (a : Fin 3) (r : ℕ) (v : V) :
    R.op (raisingRoot b) 0 (R.op (negRoot a) r v) =
      R.op (negRoot a) r (R.op (raisingRoot b) 0 v) + raisingTail R b a r v := by
  have he := R.comm (raisingRoot b) (negRoot a) 0 r v
  rw [Nat.zero_add] at he
  have he' := sub_eq_iff_eq_add.mp he
  cases b <;> fin_cases a <;>
    simpa [raisingRoot, raisingTail, negRoot, Fin.sum_univ_eight, bracketTable, add_comm] using he'

theorem raising_nword_mem {ε ν ϱ : Weight} {j : ℕ} (h : CV3Rel R w ε ν ϱ j)
    (b : Bool) (l : List NegLtr) :
    R.op (raisingRoot b) 0 (nword R w l) ∈ Ple R w l.length := by
  induction l with
  | nil =>
      rw [nword_nil, h.raising _ (by cases b <;> decide) 0]
      exact Submodule.zero_mem _
  | cons x l ih =>
      rw [nword_cons, raising_comm]
      apply Submodule.add_mem
      · exact Pbelow_op R w x.1 x.2 (l.length + 1) ih
      · have hH1 : R.op 6 x.2 (nword R w l) ∈ Ple R w (l.length + 1) :=
          Pbelow_mono R w (by omega) (cartan_nword_mem R w h false x.2 l)
        have hH2 : R.op 7 x.2 (nword R w l) ∈ Ple R w (l.length + 1) :=
          Pbelow_mono R w (by omega) (cartan_nword_mem R w h true x.2 l)
        have hF1 := nword_mem_Ple R w ((0, x.2) :: l)
        have hF2 := nword_mem_Ple R w ((2, x.2) :: l)
        rcases x with ⟨a, r⟩
        cases b <;> fin_cases a
        · exact hH1
        · exact Submodule.neg_mem _ hF2
        · exact Submodule.zero_mem _
        · exact Submodule.zero_mem _
        · exact hF1
        · exact hH2

theorem raising_Pbelow {ε ν ϱ : Weight} {j : ℕ} (h : CV3Rel R w ε ν ϱ j)
    (b : Bool) (n : ℕ) :
    Pbelow R w n ≤ (Pbelow R w n).comap (R.op (raisingRoot b) 0) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, rfl⟩
  exact Pbelow_mono R w (by omega) (raising_nword_mem R w h b l)

end

end VOA.DeligneAudit.A2.CVRectPBWPolarization

#print axioms VOA.DeligneAudit.A2.CVRectPBWPolarization.cartan_Pbelow
#print axioms VOA.DeligneAudit.A2.CVRectPBWPolarization.raising_Pbelow
