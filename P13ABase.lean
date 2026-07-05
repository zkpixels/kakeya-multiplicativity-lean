import P12Schema

namespace KakeyaMultiplicativity

/-! ## Two sixteen-point certificates: the first prime power and the
first dimension four

`FC(4,2,10)` — the certificate at the true price for the PRIME-POWER
modulus `ℤ/4` — and `FC(2,4,6)` — the certificate at the true price
for `𝔽₂⁴`.  Both spaces have sixteen points, so both certificates are
full-powerset kernel enumerations (`2¹⁶` subsets), run over `Fin 16`
index encodings for evaluation speed and transported back through
one-time structural bridges, exactly as in the `𝔽₃³` endgame.

The transfer theorem never required the small factor to be prime, so
the first certificate yields `K(4M,2) = 10·K(M,2)` for every odd `M` —
exact multiplicativity beyond squarefree moduli — and the second
yields `K(2M,4) = 6·K(M,4)`, the first exact family in dimension
four. -/


/-! ### The `(ℤ/4)²` index world -/

/-- Base-4 digit encoding of a `(ZMod 4)²` point. -/
def toIdx4 (p : ResiduePoint 4 2) : Fin 16 :=
  ⟨(p 0).val + 4 * (p 1).val, by
    have h0 : (p 0).val < 4 := ZMod.val_lt (p 0)
    have h1 : (p 1).val < 4 := ZMod.val_lt (p 1)
    omega⟩

def ofIdx4 (k : Fin 16) : ResiduePoint 4 2 :=
  ![((k.val % 4 : ℕ) : ZMod 4), ((k.val / 4 : ℕ) : ZMod 4)]

theorem ofIdx4_toIdx4 : ∀ p : ResiduePoint 4 2, ofIdx4 (toIdx4 p) = p := by
  decide

theorem toIdx4_ofIdx4 : ∀ k : Fin 16, toIdx4 (ofIdx4 k) = k := by decide

theorem toIdx4_injective : Function.Injective toIdx4 := by
  intro p q h
  rw [← ofIdx4_toIdx4 p, ← ofIdx4_toIdx4 q, h]

theorem mem_image_toIdx4 {S : Finset (ResiduePoint 4 2)}
    {p : ResiduePoint 4 2} :
    toIdx4 p ∈ S.image toIdx4 ↔ p ∈ S := by
  constructor
  · intro h
    obtain ⟨r, hr, he⟩ := Finset.mem_image.mp h
    rw [← toIdx4_injective he]
    exact hr
  · exact Finset.mem_image_of_mem _

/-- Index addition: digitwise mod 4. -/
def addIdx4 (a b : Fin 16) : Fin 16 :=
  ⟨(a.val % 4 + b.val % 4) % 4 + ((a.val / 4 + b.val / 4) % 4) * 4, by
    omega⟩

theorem toIdx4_add :
    ∀ p r : ResiduePoint 4 2,
      toIdx4 (p + r) = addIdx4 (toIdx4 p) (toIdx4 r) := by
  decide

/-- Anchored carrier check over `ℤ/4`: the three nonzero parameters. -/
def carriesIdx4 (S : Finset (Fin 16)) (d : Fin 16) : Prop :=
  ∃ p ∈ S, addIdx4 p d ∈ S ∧ addIdx4 (addIdx4 p d) d ∈ S ∧
    addIdx4 (addIdx4 (addIdx4 p d) d) d ∈ S

instance (S : Finset (Fin 16)) (d : Fin 16) :
    Decidable (carriesIdx4 S d) :=
  inferInstanceAs (Decidable (∃ p ∈ S, _ ∧ _ ∧ _))

/-- Parameter case split over `ZMod 4`. -/
theorem zmod4_cases : ∀ t : ZMod 4, t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by
  decide

/-- Successive line points over `ℤ/4` are successive additions. -/
theorem residueLine_add_step (p b : ResiduePoint 4 2) (t : ZMod 4) :
    residueLine p b (t + 1) = residueLine p b t + b := by
  funext i
  simp only [residueLine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem carriesIdx4_iff {S : Finset (ResiduePoint 4 2)}
    {b : ResiduePoint 4 2} :
    carriesIdx4 (S.image toIdx4) (toIdx4 b) ↔ CarriesLine S b := by
  have hline : ∀ p : ResiduePoint 4 2,
      residueLine p b 1 = p + b ∧
      residueLine p b 2 = p + b + b ∧
      residueLine p b 3 = p + b + b + b := by
    intro p
    refine ⟨?_, ?_, ?_⟩ <;>
      · funext i
        simp only [residueLine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
  constructor
  · rintro ⟨pi, hpi, h1, h2, h3⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hpi
    rw [← toIdx4_add] at h1
    rw [← toIdx4_add, ← toIdx4_add] at h2
    rw [← toIdx4_add, ← toIdx4_add, ← toIdx4_add] at h3
    refine ⟨p, fun t => ?_⟩
    obtain ⟨hl1, hl2, hl3⟩ := hline p
    rcases zmod4_cases t with rfl | rfl | rfl | rfl
    · rw [residueLine_zero]
      exact hp
    · rw [hl1]
      exact mem_image_toIdx4.mp h1
    · rw [hl2]
      exact mem_image_toIdx4.mp h2
    · rw [hl3]
      exact mem_image_toIdx4.mp h3
  · rintro ⟨a, ha⟩
    obtain ⟨hl1, hl2, hl3⟩ := hline a
    refine ⟨toIdx4 a, mem_image_toIdx4.mpr (by
        rw [← residueLine_zero a b]; exact ha 0), ?_, ?_, ?_⟩
    · rw [← toIdx4_add, ← hl1]
      exact mem_image_toIdx4.mpr (ha 1)
    · rw [← toIdx4_add, ← toIdx4_add, ← hl2]
      exact mem_image_toIdx4.mpr (ha 2)
    · rw [← toIdx4_add, ← toIdx4_add, ← toIdx4_add, ← hl3]
      exact mem_image_toIdx4.mpr (ha 3)

/-- The nonzero index menu (image of the direction menu). -/
def nzIdx4 : Finset (Fin 16) :=
  {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}

theorem nzIdx4_eq : (nonzeroDirections 4 2).image toIdx4 = nzIdx4 := by
  decide

/-- Carried-menu count, transported. -/
theorem carriedIdx4_image (S : Finset (ResiduePoint 4 2)) :
    (nzIdx4.filter fun d => carriesIdx4 (S.image toIdx4) d).card =
      ((nonzeroDirections 4 2).filter fun b => CarriesLine S b).card := by
  rw [← nzIdx4_eq, Finset.filter_image,
    Finset.card_image_of_injective _ toIdx4_injective]
  exact congrArg Finset.card (Finset.filter_congr fun b _ => by
    rw [carriesIdx4_iff])



end KakeyaMultiplicativity
