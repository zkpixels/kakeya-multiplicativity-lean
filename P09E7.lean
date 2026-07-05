import N27

namespace KakeyaMultiplicativity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem natA11 :
    ∀ d ∈ freeRepsList, ∀ (a : Fin 27) (b : Fin 27),
      (starMaskN d).testBit a.val = false → (starMaskN d).testBit b.val = false → a.val ≠ b.val →
      classCountN (starMaskN d ||| (1 <<< a.val) ||| (1 <<< b.val)) ≤ 11 := by
  decide +kernel

/-- Case A, `u = 11`. -/
theorem endgame_caseA_eleven :
    ∀ d ∈ freeRepsIdx,
      ∀ extras ∈ ((Finset.univ : Finset (Fin 27)) \ stdStarIdx d).powersetCard 2,
        classCountIdx (stdStarIdx d ∪ extras) ≤ 11 := by
  intro d hd extras hmem
  rw [Finset.mem_powersetCard] at hmem
  obtain ⟨hsub, hcard⟩ := hmem
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  have hfa : (starMaskN d).testBit a.val = false :=
    bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit d hd a).mp ht))
  have hfb : (starMaskN d).testBit b.val = false :=
    bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit d hd b).mp ht))
  have hspec : ∀ p : Fin 27,
      (starMaskN d ||| (1 <<< a.val) ||| (1 <<< b.val)).testBit p.val = true ↔ p ∈ stdStarIdx d ∪ {a, b} := by
    intro p
    simp only [or_testBit, Bool.or_eq_true, shiftF_testBit,
      star_bit d hd p, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    exact or_assoc
  rw [classCountN_eq hspec]
  exact natA11 d ((freeRepsList_mem d).mpr hd) a b hfa hfb (fun h => hab (Fin.val_injective h))

end KakeyaMultiplicativity
