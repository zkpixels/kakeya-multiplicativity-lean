import N00Core
import P32BBase

namespace KakeyaMultiplicativity

/-! The 16-world bitmask layer for the 𝔽₂⁴ cell (two-point carrier
check; otherwise parallel to N16A). -/

/-- Bitmask mirror of `carriesIdx2` (two memberships). -/
def carriesN2 (m : ℕ) (d : Fin 16) : Bool :=
  (List.finRange 16).any fun p =>
    m.testBit p.val && m.testBit (addIdx2 p d).val

/-- Nonzero directions as a bare list. -/
def nzList2 : List (Fin 16) :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- Bitmask mirror of the carried-direction count. -/
def countN2 (m : ℕ) : ℕ := nzList2.countP (carriesN2 m)

/-- Bitmask popcount over 16 positions. -/
def popcountN2 (m : ℕ) : ℕ :=
  (List.finRange 16).countP fun p => m.testBit p.val

theorem nzList2_mem : ∀ d : Fin 16, d ∈ nzList2 ↔ d ∈ nzIdx2 := by decide

theorem nzList2_nodup : nzList2.Nodup := by decide

theorem carriesN2_iff {m : ℕ} {S : Finset (Fin 16)}
    (h : ∀ p : Fin 16, m.testBit p.val = true ↔ p ∈ S) (d : Fin 16) :
    carriesN2 m d = true ↔ carriesIdx2 S d := by
  unfold carriesN2 carriesIdx2
  rw [List.any_eq_true]
  constructor
  · rintro ⟨p, -, hb⟩
    rw [Bool.and_eq_true] at hb
    exact ⟨p, (h p).mp hb.1, (h _).mp hb.2⟩
  · rintro ⟨p, hp, h1⟩
    refine ⟨p, List.mem_finRange p, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨(h p).mpr hp, (h _).mpr h1⟩

/-- COUNT BRIDGE for the certificate count. -/
theorem countN2_eq {m : ℕ} {S : Finset (Fin 16)}
    (h : ∀ p : Fin 16, m.testBit p.val = true ↔ p ∈ S) :
    (nzIdx2.filter fun d => carriesIdx2 S d).card = countN2 m :=
  card_filter_eq_countP nzIdx2 nzList2 nzList2_mem nzList2_nodup _ _
    (fun d _ => (carriesN2_iff h d).symm)

/-- POPCOUNT BRIDGE. -/
theorem popcountN2_eq {m : ℕ} {S : Finset (Fin 16)}
    (h : ∀ p : Fin 16, m.testBit p.val = true ↔ p ∈ S) :
    S.card = popcountN2 m := by
  have h1 : S = Finset.univ.filter fun p : Fin 16 =>
      m.testBit p.val = true := by
    ext p
    simp [h p]
  rw [h1]
  exact card_filter_eq_countP Finset.univ (List.finRange 16)
    (by simp) (List.nodup_finRange 16) _ _ (fun a _ => Iff.rfl)


end KakeyaMultiplicativity
