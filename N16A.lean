import N00Core
import P13ABase

namespace KakeyaMultiplicativity

/-! The 16-world bitmask layer for the ℤ₄² cell: Nat mirrors of
`carriesIdx4` and the certificate count, the popcount bridge, and the
mask bridge.  Heavy decides live in the range slices P14AK*..P29AK*. -/

/-- Bitmask mirror of `carriesIdx4` (four collinear memberships). -/
def carriesN4 (m : ℕ) (d : Fin 16) : Bool :=
  (List.finRange 16).any fun p =>
    m.testBit p.val && m.testBit (addIdx4 p d).val
      && m.testBit (addIdx4 (addIdx4 p d) d).val
      && m.testBit (addIdx4 (addIdx4 (addIdx4 p d) d) d).val

/-- Nonzero directions as a bare list. -/
def nzList4 : List (Fin 16) :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- Bitmask mirror of the carried-direction count. -/
def countN4 (m : ℕ) : ℕ := nzList4.countP (carriesN4 m)

/-- Bitmask popcount over 16 positions. -/
def popcountN4 (m : ℕ) : ℕ :=
  (List.finRange 16).countP fun p => m.testBit p.val

theorem nzList4_mem : ∀ d : Fin 16, d ∈ nzList4 ↔ d ∈ nzIdx4 := by decide

theorem nzList4_nodup : nzList4.Nodup := by decide

theorem carriesN4_iff {m : ℕ} {S : Finset (Fin 16)}
    (h : ∀ p : Fin 16, m.testBit p.val = true ↔ p ∈ S) (d : Fin 16) :
    carriesN4 m d = true ↔ carriesIdx4 S d := by
  unfold carriesN4 carriesIdx4
  rw [List.any_eq_true]
  constructor
  · rintro ⟨p, -, hb⟩
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hb
    exact ⟨p, (h p).mp hb.1.1.1, (h _).mp hb.1.1.2, (h _).mp hb.1.2,
      (h _).mp hb.2⟩
  · rintro ⟨p, hp, h1, h2, h3⟩
    refine ⟨p, List.mem_finRange p, ?_⟩
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨⟨(h p).mpr hp, (h _).mpr h1⟩, (h _).mpr h2⟩, (h _).mpr h3⟩

/-- COUNT BRIDGE for the certificate count. -/
theorem countN4_eq {m : ℕ} {S : Finset (Fin 16)}
    (h : ∀ p : Fin 16, m.testBit p.val = true ↔ p ∈ S) :
    (nzIdx4.filter fun d => carriesIdx4 S d).card = countN4 m :=
  card_filter_eq_countP nzIdx4 nzList4 nzList4_mem nzList4_nodup _ _
    (fun d _ => (carriesN4_iff h d).symm)

/-- POPCOUNT BRIDGE: the window's cardinality is the mask popcount. -/
theorem popcountN4_eq {m : ℕ} {S : Finset (Fin 16)}
    (h : ∀ p : Fin 16, m.testBit p.val = true ↔ p ∈ S) :
    S.card = popcountN4 m := by
  have h1 : S = Finset.univ.filter fun p : Fin 16 =>
      m.testBit p.val = true := by
    ext p
    simp [h p]
  rw [h1]
  exact card_filter_eq_countP Finset.univ (List.finRange 16)
    (by simp) (List.nodup_finRange 16) _ _ (fun a _ => Iff.rfl)


end KakeyaMultiplicativity
