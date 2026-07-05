import P31AFc

namespace KakeyaMultiplicativity

/-! ### The `𝔽₂⁴` index world -/

/-- Base-2 digit encoding of an `𝔽₂⁴` point. -/
def toIdx2 (p : ResiduePoint 2 4) : Fin 16 :=
  ⟨(p 0).val + 2 * (p 1).val + 4 * (p 2).val + 8 * (p 3).val, by
    have h0 : (p 0).val < 2 := ZMod.val_lt (p 0)
    have h1 : (p 1).val < 2 := ZMod.val_lt (p 1)
    have h2 : (p 2).val < 2 := ZMod.val_lt (p 2)
    have h3 : (p 3).val < 2 := ZMod.val_lt (p 3)
    omega⟩

def ofIdx2 (k : Fin 16) : ResiduePoint 2 4 :=
  ![((k.val % 2 : ℕ) : ZMod 2), ((k.val / 2 % 2 : ℕ) : ZMod 2),
    ((k.val / 4 % 2 : ℕ) : ZMod 2), ((k.val / 8 : ℕ) : ZMod 2)]

theorem ofIdx2_toIdx2 : ∀ p : ResiduePoint 2 4, ofIdx2 (toIdx2 p) = p := by
  decide

theorem toIdx2_ofIdx2 : ∀ k : Fin 16, toIdx2 (ofIdx2 k) = k := by decide

theorem toIdx2_injective : Function.Injective toIdx2 := by
  intro p q h
  rw [← ofIdx2_toIdx2 p, ← ofIdx2_toIdx2 q, h]

theorem mem_image_toIdx2 {S : Finset (ResiduePoint 2 4)}
    {p : ResiduePoint 2 4} :
    toIdx2 p ∈ S.image toIdx2 ↔ p ∈ S := by
  constructor
  · intro h
    obtain ⟨r, hr, he⟩ := Finset.mem_image.mp h
    rw [← toIdx2_injective he]
    exact hr
  · exact Finset.mem_image_of_mem _

/-- Index addition: digitwise mod 2. -/
def addIdx2 (a b : Fin 16) : Fin 16 :=
  ⟨(a.val % 2 + b.val % 2) % 2 +
    ((a.val / 2 % 2 + b.val / 2 % 2) % 2) * 2 +
    ((a.val / 4 % 2 + b.val / 4 % 2) % 2) * 4 +
    ((a.val / 8 + b.val / 8) % 2) * 8, by omega⟩

theorem toIdx2_add :
    ∀ p r : ResiduePoint 2 4,
      toIdx2 (p + r) = addIdx2 (toIdx2 p) (toIdx2 r) := by
  decide

/-- Anchored carrier check over `𝔽₂`: one nonzero parameter. -/
def carriesIdx2 (S : Finset (Fin 16)) (d : Fin 16) : Prop :=
  ∃ p ∈ S, addIdx2 p d ∈ S

instance (S : Finset (Fin 16)) (d : Fin 16) :
    Decidable (carriesIdx2 S d) :=
  inferInstanceAs (Decidable (∃ p ∈ S, _))

theorem zmod2_cases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide

theorem carriesIdx2_iff {S : Finset (ResiduePoint 2 4)}
    {b : ResiduePoint 2 4} :
    carriesIdx2 (S.image toIdx2) (toIdx2 b) ↔ CarriesLine S b := by
  have hline : ∀ p : ResiduePoint 2 4, residueLine p b 1 = p + b := by
    intro p
    funext i
    simp only [residueLine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  constructor
  · rintro ⟨pi, hpi, h1⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hpi
    rw [← toIdx2_add] at h1
    refine ⟨p, fun t => ?_⟩
    rcases zmod2_cases t with rfl | rfl
    · rw [residueLine_zero]
      exact hp
    · rw [hline]
      exact mem_image_toIdx2.mp h1
  · rintro ⟨a, ha⟩
    refine ⟨toIdx2 a, mem_image_toIdx2.mpr (by
        rw [← residueLine_zero a b]; exact ha 0), ?_⟩
    rw [← toIdx2_add, ← hline]
    exact mem_image_toIdx2.mpr (ha 1)

def nzIdx2 : Finset (Fin 16) :=
  {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}

theorem nzIdx2_eq : (nonzeroDirections 2 4).image toIdx2 = nzIdx2 := by
  decide

theorem carriedIdx2_image (S : Finset (ResiduePoint 2 4)) :
    (nzIdx2.filter fun d => carriesIdx2 (S.image toIdx2) d).card =
      ((nonzeroDirections 2 4).filter fun b => CarriesLine S b).card := by
  rw [← nzIdx2_eq, Finset.filter_image,
    Finset.card_image_of_injective _ toIdx2_injective]
  exact congrArg Finset.card (Finset.filter_congr fun b _ => by
    rw [carriesIdx2_iff])



end KakeyaMultiplicativity
