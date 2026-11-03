import VOA.DeligneAudit.LeviTypeA3GradedTwoWords

/-! Rotate the second adjacent-pair box into the ordered three-box target. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.Sl2Weyl
open VOA.DeligneAudit.LeviConversion

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

private theorem a3_single_word_comm (i j : Fin 3) (s : ℕ) (ys : List ℕ) :
    ρ.op (F i) s * (ys.map fun t => ρ.op (F j) t).prod =
      (ys.map fun t => ρ.op (F j) t).prod * ρ.op (F i) s := by
  induction ys with
  | nil => simp
  | cons t ys ih =>
      simp only [List.map_cons, List.prod_cons]
      calc
        ρ.op (F i) s * (ρ.op (F j) t *
            (ys.map fun u => ρ.op (F j) u).prod) =
          (ρ.op (F i) s * ρ.op (F j) t) *
            (ys.map fun u => ρ.op (F j) u).prod := by rw [mul_assoc]
        _ = (ρ.op (F j) t * ρ.op (F i) s) *
            (ys.map fun u => ρ.op (F j) u).prod := by
          rw [a3_conversion_radical_comm ρ i j s t]
        _ = ρ.op (F j) t *
            (ρ.op (F i) s * (ys.map fun u => ρ.op (F j) u).prod) := by
          rw [mul_assoc]
        _ = _ := by rw [ih, mul_assoc]

private theorem a3_word_word_comm (i j : Fin 3) (xs ys : List ℕ) :
    (xs.map fun s => ρ.op (F i) s).prod *
      (ys.map fun s => ρ.op (F j) s).prod =
    (ys.map fun s => ρ.op (F j) s).prod *
      (xs.map fun s => ρ.op (F i) s).prod := by
  induction xs with
  | nil => simp
  | cons s xs ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [mul_assoc, ih, ← mul_assoc, a3_single_word_comm ρ i j s ys,
        mul_assoc]

theorem a3_rotate_radical_words (fs gs hs : List ℕ) :
    (aWord (fun i => ρ.op (F 1) i) gs *
      (hs.map fun i => ρ.op (F 2) i).prod *
      (fs.map fun i => ρ.op (F 0) i).prod) w =
    (aWord (fun i => ρ.op (F 0) i) fs *
      (gs.map fun i => ρ.op (F 1) i).prod *
      (hs.map fun i => ρ.op (F 2) i).prod) w := by
  have hcomm₁ := a3_word_word_comm ρ 2 0 hs fs
  have hcomm₂ := a3_word_word_comm ρ 1 0 gs fs
  simp only [aWord]
  rw [mul_assoc, hcomm₁, ← mul_assoc, hcomm₂, mul_assoc]

/-- The rotated second-pair box, with boxed F₁ and F₂ words, lies in the
effective three-box target. -/
theorem a3_pair_one_box_le_three (a b c : ℕ) (k : A3RadicalKey)
    (h₁ : k.d₁ ≤ a) (h₂ : k.d₂ ≤ b) (h₃ : k.d₃ ≤ c)
    (f g : ℕ →₀ ℕ) (r s t : ℕ)
    (hf : BoxP a f) (hg : BoxP b g)
    (hwf : Finsupp.weight om f = (k.d₁, r))
    (hwg : Finsupp.weight om g = (k.d₂, s))
    (hd : r + s + t = k.degree) :
    a3PairBoxSpan ρ w 1 (VOA.DeligneAudit.CLAssembly.lst g)
      (VOA.DeligneAudit.CLAssembly.lst f) c k.d₃ t ≤
        a3EffectiveTarget ρ w a b c k := by
  rw [a3PairBoxSpan, Submodule.span_le]
  intro v hv
  obtain ⟨h, hh, hwh, rfl⟩ := hv
  rw [a2_evAlg_monomial_word]
  have hword := a3_three_box_word_mem ρ w a b c k h₁ h₂ h₃
    f g h r s t hf hg hh hwf hwg hwh hd
  have hrotate :
      (aWord (fun i => ρ.op (F 1) i) (VOA.DeligneAudit.CLAssembly.lst g) *
        ((VOA.DeligneAudit.CLAssembly.lst h).map fun i => ρ.op (F 2) i).prod *
        ((VOA.DeligneAudit.CLAssembly.lst f).map fun i => ρ.op (F 0) i).prod) w =
      (aWord (fun i => ρ.op (F 0) i) (VOA.DeligneAudit.CLAssembly.lst f) *
        ((VOA.DeligneAudit.CLAssembly.lst g).map fun i => ρ.op (F 1) i).prod *
        ((VOA.DeligneAudit.CLAssembly.lst h).map fun i => ρ.op (F 2) i).prod) w := by
    exact a3_rotate_radical_words ρ w _ _ _
  change (aWord (fun i => ρ.op (F 1) i)
      (VOA.DeligneAudit.CLAssembly.lst g) *
      ((VOA.DeligneAudit.CLAssembly.lst h).map fun i => ρ.op (F 2) i).prod *
      ((VOA.DeligneAudit.CLAssembly.lst f).map fun i => ρ.op (F 0) i).prod) w ∈
        a3EffectiveTarget ρ w a b c k
  rw [hrotate]
  exact hword

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_pair_one_box_le_three
#print axioms VOA.DeligneAudit.A3Sector.a3_rotate_radical_words
