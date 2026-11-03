import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleAImage

/-! Whole seed words: Cartan blocks are single-color shifts; contacts kill
the U branch and negative blocks kill the Cartan-shifted C branch. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.SectorWeyl
noncomputable section

def shiftWord (m : ℕ) : List ℕ → MonoRing ℂ m → MonoRing ℂ m
  | [], p => p
  | k::l, p => monoShift ℂ m k (shiftWord m l p)

def monoSeed (m : ℕ) (j : AllM.SeedIndex m) : MonoRing ℂ m :=
  PowerSeries.coeff j.val.2.2 (monoCurrent ℂ m ^ j.val.2.1)

theorem seed_eq_monoMap (m : ℕ) (j : AllM.SeedIndex m) :
    AllM.seedPoly m j = monoMap ℂ m (sourceColor j.val.1) (monoSeed m j) := by
  rw [monoSeed,monoMap_seed]
  rfl

theorem category_two_iff : ∀ a : Fin 18, category a = 2 ↔ a.val < 4 := by
  decide +kernel

theorem category_one_iff : ∀ a : Fin 18, category a = 1 ↔ 7 ≤ a.val ∧ a.val < 10 := by
  decide +kernel

theorem cartan_mono_any (m : ℕ) (a : Fin 18) (k : ℕ) (b : Bool) (p : MonoRing ℂ m)
    (ha : category a = 2) :
    deriv ℂ m a k (monoMap ℂ m (sourceColor b) p) =
      (coeff a (sourceColor b):ℂ) • monoMap ℂ m (sourceColor b) (monoShift ℂ m k p) := by
  let h : Fin 4 := ⟨a.val,(category_two_iff a).mp ha⟩
  have he : cartan h = a := Fin.ext rfl
  rw [← he,Int.cast_smul_eq_zsmul]
  exact cartan_mono ℂ m h b k p

theorem negative_mono_any (m : ℕ) (a : Fin 18) (k : ℕ) (p : MonoRing ℂ m)
    (ha : category a = 1) : deriv ℂ m a k (monoMap ℂ m 8 p) = 0 := by
  have hb := (category_one_iff a).mp ha
  let d : Fin 3 := ⟨a.val-7,by omega⟩
  have he : negative d = a := by
    apply Fin.ext
    change 7+(a.val-7) = a.val
    omega
  rw [← he]
  exact negative_center_mono ℂ m d k p

def cartanFactor (b : Bool) (l : List (Fin 18 × ℕ)) : ℂ :=
  (l.map fun x => (coeff x.1 (sourceColor b):ℂ)).prod

/-- Exact scalar and whole one-color polynomial for every Cartan block. -/
theorem cartan_word (m : ℕ) (b : Bool) :
    ∀ (l : List (Fin 18 × ℕ)), (∀ x ∈ l, category x.1 = 2) → ∀ p : MonoRing ℂ m,
      wordOp (representation ℂ m) l (monoMap ℂ m (sourceColor b) p) =
        cartanFactor b l • monoMap ℂ m (sourceColor b) (shiftWord m (l.map Prod.snd) p) := by
  intro l
  induction l with
  | nil => intro _ p; simp only [wordOp,cartanFactor,List.map_nil,List.prod_nil,shiftWord,one_smul]
  | cons x l ih =>
      intro hl p
      have hx := hl x (List.mem_cons_self)
      have ht : ∀ y ∈ l, category y.1 = 2 := fun y hy => hl y (List.mem_cons_of_mem _ hy)
      change deriv ℂ m x.1 x.2 (wordOp (representation ℂ m) l (monoMap ℂ m (sourceColor b) p)) = _
      rw [ih ht,Derivation.map_smul,cartan_mono_any m x.1 x.2 b _ hx,smul_smul]
      simp only [cartanFactor,List.map_cons,List.prod_cons,shiftWord]
      rw [mul_comm]

theorem cartan_seed_image (m : ℕ) (j : AllM.SeedIndex m) (l : List (Fin 18 × ℕ))
    (hl : ∀ x ∈ l, category x.1 = 2) :
    ∃ p : MonoRing ℂ m, wordOp (representation ℂ m) l (AllM.seedPoly m j) =
      monoMap ℂ m (sourceColor j.val.1) p := by
  rw [seed_eq_monoMap,cartan_word m j.val.1 l hl]
  refine ⟨cartanFactor j.val.1 l • shiftWord m (l.map Prod.snd) (monoSeed m j),?_⟩
  rw [map_smul]

/-- Contact letters kill every U-source word, even before PBW sorting. -/
theorem u_contact_word_zero (m : ℕ) (j : AllM.SeedIndex m) (hj : j.val.1 = false)
    (l : List (Fin 18 × ℕ)) (hl : ∃ x ∈ l, category x.1 = 0) :
    wordOp (representation ℂ m) l (AllM.seedPoly m j) = 0 := by
  rw [seed_eq_monoMap]
  have hc : sourceColor j.val.1 = 0 := by simp [sourceColor,hj]
  rw [hc,← aMap_top,word_aMap,aWord_contact_zero ℂ m _ l hl,map_zero]

/-- A negative block inside a sorted C-source word is killed after its Cartan block. -/
theorem c_negative_word_zero (m : ℕ) (j : AllM.SeedIndex m) (hj : j.val.1 = true) :
    ∀ (l : List (Fin 18 × ℕ)), l.IsChain (fun x y => key x ≤ key y) →
      (∀ x ∈ l, category x.1 < 3) → (∃ x ∈ l, category x.1 = 1) →
      wordOp (representation ℂ m) l (AllM.seedPoly m j) = 0 := by
  intro l
  induction l with
  | nil => intro _ _ hp; obtain ⟨x,hx,_⟩ := hp; simp at hx
  | cons x l ih =>
      intro hs hn hp
      by_cases ht : ∃ y ∈ l, category y.1 = 1
      · change deriv ℂ m x.1 x.2 (wordOp (representation ℂ m) l (AllM.seedPoly m j)) = 0
        rw [ih hs.tail (fun y hy => hn y (List.mem_cons_of_mem _ hy)) ht,map_zero]
      · have hx : category x.1 = 1 := by
          obtain ⟨y,hy,hc⟩ := hp
          rcases List.mem_cons.mp hy with hy | hy
          · subst y; exact hc
          · exact (ht ⟨y,hy,hc⟩).elim
        have hcart : ∀ y ∈ l, category y.1 = 2 := by
          intro y hy
          have hxy := hs.rel_cons hy
          have hmax := hn y (List.mem_cons_of_mem _ hy)
          have hne : category y.1 ≠ 1 := fun he => ht ⟨y,hy,he⟩
          change category x.1 ≤ category y.1 at hxy
          omega
        obtain ⟨p,hp⟩ := cartan_seed_image m j l hcart
        have hc : sourceColor j.val.1 = 8 := by simp [sourceColor,hj]
        change deriv ℂ m x.1 x.2 (wordOp (representation ℂ m) l (AllM.seedPoly m j)) = 0
        rw [hp,hc]
        exact negative_mono_any m x.1 x.2 p hx

end
#print axioms cartan_word
#print axioms u_contact_word_zero
#print axioms c_negative_word_zero
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
