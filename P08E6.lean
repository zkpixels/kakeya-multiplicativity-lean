import N27

namespace KakeyaMultiplicativity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem natA10 :
    ∀ d ∈ freeRepsList, ∀ (a : Fin 27),
      (starMaskN d).testBit a.val = false →
      classCountN (starMaskN d ||| (1 <<< a.val)) ≤ 10 := by
  decide +kernel

/-- Case A, `u = 10`. -/
theorem endgame_caseA_ten :
    ∀ d ∈ freeRepsIdx,
      ∀ extras ∈ ((Finset.univ : Finset (Fin 27)) \ stdStarIdx d).powersetCard 1,
        classCountIdx (stdStarIdx d ∪ extras) ≤ 10 := by
  intro d hd extras hmem
  rw [Finset.mem_powersetCard] at hmem
  obtain ⟨hsub, hcard⟩ := hmem
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
  have hfa : (starMaskN d).testBit a.val = false :=
    bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit d hd a).mp ht))
  have hspec : ∀ p : Fin 27,
      (starMaskN d ||| (1 <<< a.val)).testBit p.val = true ↔ p ∈ stdStarIdx d ∪ {a} := by
    intro p
    simp only [or_testBit, Bool.or_eq_true, shiftF_testBit,
      star_bit d hd p, Finset.mem_union, Finset.mem_singleton]
  rw [classCountN_eq hspec]
  exact natA10 d ((freeRepsList_mem d).mpr hd) a hfa 

end KakeyaMultiplicativity
