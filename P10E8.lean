import N27
import N27A12R0
import N27A12R1
import N27A12R2
import N27A12R3
import N27A12R4
import N27A12R5
import N27A12R6
import N27A12R7
import N27A12R8
import N27A12R9

namespace KakeyaMultiplicativity

-- k=3 decides live in N27A12R0..R9 (rep slices)

/-- Case A, `u = 12`: assembled from the ten rep slices. -/
theorem endgame_caseA_twelve :
    ∀ d ∈ freeRepsIdx,
      ∀ extras ∈ ((Finset.univ : Finset (Fin 27)) \ stdStarIdx d).powersetCard 3,
        classCountIdx (stdStarIdx d ∪ extras) ≤ 12 := by
  intro d hd extras hmem
  rw [Finset.mem_powersetCard] at hmem
  obtain ⟨hsub, hcard⟩ := hmem
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
  have hd' : d ∈ ({4, 7, 10, 13, 16, 19, 22, 25, 12, 21} : Finset (Fin 27)) := by
    have he : freeRepsIdx = ({4, 7, 10, 13, 16, 19, 22, 25, 12, 21} : Finset (Fin 27)) := by decide
    rw [← he]; exact hd
  fin_cases hd'
  · show classCountIdx (stdStarIdx (4 : Fin 27) ∪ {a, b, c}) ≤ 12
    have hfa : (starMaskN (4 : Fin 27)).testBit a.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) a).mp ht))
    have hfb : (starMaskN (4 : Fin 27)).testBit b.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) b).mp ht))
    have hfc : (starMaskN (4 : Fin 27)).testBit c.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) c).mp ht))
    have hspec : ∀ p : Fin 27,
        (starMaskN (4 : Fin 27) ||| (1 <<< a.val) ||| (1 <<< b.val) ||| (1 <<< c.val)).testBit p.val = true ↔
          p ∈ stdStarIdx (4 : Fin 27) ∪ {a, b, c} := by
      intro p
      simp only [or_testBit, Bool.or_eq_true, shiftF_testBit,
        star_bit (4 : Fin 27) (by decide) p, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [classCountN_eq hspec]
    exact natA12_r0 a b c hfa hfb hfc (fun h => hab (Fin.val_injective h)) (fun h => hac (Fin.val_injective h)) (fun h => hbc (Fin.val_injective h))
  · show classCountIdx (stdStarIdx (7 : Fin 27) ∪ {a, b, c}) ≤ 12
    have hfa : (starMaskN (7 : Fin 27)).testBit a.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) a).mp ht))
    have hfb : (starMaskN (7 : Fin 27)).testBit b.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) b).mp ht))
    have hfc : (starMaskN (7 : Fin 27)).testBit c.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) c).mp ht))
    have hspec : ∀ p : Fin 27,
        (starMaskN (7 : Fin 27) ||| (1 <<< a.val) ||| (1 <<< b.val) ||| (1 <<< c.val)).testBit p.val = true ↔
          p ∈ stdStarIdx (7 : Fin 27) ∪ {a, b, c} := by
      intro p
      simp only [or_testBit, Bool.or_eq_true, shiftF_testBit,
        star_bit (7 : Fin 27) (by decide) p, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [classCountN_eq hspec]
    exact natA12_r1 a b c hfa hfb hfc (fun h => hab (Fin.val_injective h)) (fun h => hac (Fin.val_injective h)) (fun h => hbc (Fin.val_injective h))
  · show classCountIdx (stdStarIdx (10 : Fin 27) ∪ {a, b, c}) ≤ 12
    have hfa : (starMaskN (10 : Fin 27)).testBit a.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) a).mp ht))
    have hfb : (starMaskN (10 : Fin 27)).testBit b.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) b).mp ht))
    have hfc : (starMaskN (10 : Fin 27)).testBit c.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) c).mp ht))
    have hspec : ∀ p : Fin 27,
        (starMaskN (10 : Fin 27) ||| (1 <<< a.val) ||| (1 <<< b.val) ||| (1 <<< c.val)).testBit p.val = true ↔
          p ∈ stdStarIdx (10 : Fin 27) ∪ {a, b, c} := by
      intro p
      simp only [or_testBit, Bool.or_eq_true, shiftF_testBit,
        star_bit (10 : Fin 27) (by decide) p, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [classCountN_eq hspec]
    exact natA12_r2 a b c hfa hfb hfc (fun h => hab (Fin.val_injective h)) (fun h => hac (Fin.val_injective h)) (fun h => hbc (Fin.val_injective h))
  · show classCountIdx (stdStarIdx (13 : Fin 27) ∪ {a, b, c}) ≤ 12
    have hfa : (starMaskN (13 : Fin 27)).testBit a.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) a).mp ht))
    have hfb : (starMaskN (13 : Fin 27)).testBit b.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) b).mp ht))
    have hfc : (starMaskN (13 : Fin 27)).testBit c.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) c).mp ht))
    have hspec : ∀ p : Fin 27,
        (starMaskN (13 : Fin 27) ||| (1 <<< a.val) ||| (1 <<< b.val) ||| (1 <<< c.val)).testBit p.val = true ↔
          p ∈ stdStarIdx (13 : Fin 27) ∪ {a, b, c} := by
      intro p
      simp only [or_testBit, Bool.or_eq_true, shiftF_testBit,
        star_bit (13 : Fin 27) (by decide) p, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [classCountN_eq hspec]
    exact natA12_r3 a b c hfa hfb hfc (fun h => hab (Fin.val_injective h)) (fun h => hac (Fin.val_injective h)) (fun h => hbc (Fin.val_injective h))
  · show classCountIdx (stdStarIdx (16 : Fin 27) ∪ {a, b, c}) ≤ 12
    have hfa : (starMaskN (16 : Fin 27)).testBit a.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) a).mp ht))
    have hfb : (starMaskN (16 : Fin 27)).testBit b.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) b).mp ht))
    have hfc : (starMaskN (16 : Fin 27)).testBit c.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) c).mp ht))
    have hspec : ∀ p : Fin 27,
        (starMaskN (16 : Fin 27) ||| (1 <<< a.val) ||| (1 <<< b.val) ||| (1 <<< c.val)).testBit p.val = true ↔
          p ∈ stdStarIdx (16 : Fin 27) ∪ {a, b, c} := by
      intro p
      simp only [or_testBit, Bool.or_eq_true, shiftF_testBit,
        star_bit (16 : Fin 27) (by decide) p, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [classCountN_eq hspec]
    exact natA12_r4 a b c hfa hfb hfc (fun h => hab (Fin.val_injective h)) (fun h => hac (Fin.val_injective h)) (fun h => hbc (Fin.val_injective h))
  · show classCountIdx (stdStarIdx (19 : Fin 27) ∪ {a, b, c}) ≤ 12
    have hfa : (starMaskN (19 : Fin 27)).testBit a.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) a).mp ht))
    have hfb : (starMaskN (19 : Fin 27)).testBit b.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) b).mp ht))
    have hfc : (starMaskN (19 : Fin 27)).testBit c.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) c).mp ht))
    have hspec : ∀ p : Fin 27,
        (starMaskN (19 : Fin 27) ||| (1 <<< a.val) ||| (1 <<< b.val) ||| (1 <<< c.val)).testBit p.val = true ↔
          p ∈ stdStarIdx (19 : Fin 27) ∪ {a, b, c} := by
      intro p
      simp only [or_testBit, Bool.or_eq_true, shiftF_testBit,
        star_bit (19 : Fin 27) (by decide) p, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [classCountN_eq hspec]
    exact natA12_r5 a b c hfa hfb hfc (fun h => hab (Fin.val_injective h)) (fun h => hac (Fin.val_injective h)) (fun h => hbc (Fin.val_injective h))
  · show classCountIdx (stdStarIdx (22 : Fin 27) ∪ {a, b, c}) ≤ 12
    have hfa : (starMaskN (22 : Fin 27)).testBit a.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) a).mp ht))
    have hfb : (starMaskN (22 : Fin 27)).testBit b.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) b).mp ht))
    have hfc : (starMaskN (22 : Fin 27)).testBit c.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) c).mp ht))
    have hspec : ∀ p : Fin 27,
        (starMaskN (22 : Fin 27) ||| (1 <<< a.val) ||| (1 <<< b.val) ||| (1 <<< c.val)).testBit p.val = true ↔
          p ∈ stdStarIdx (22 : Fin 27) ∪ {a, b, c} := by
      intro p
      simp only [or_testBit, Bool.or_eq_true, shiftF_testBit,
        star_bit (22 : Fin 27) (by decide) p, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [classCountN_eq hspec]
    exact natA12_r6 a b c hfa hfb hfc (fun h => hab (Fin.val_injective h)) (fun h => hac (Fin.val_injective h)) (fun h => hbc (Fin.val_injective h))
  · show classCountIdx (stdStarIdx (25 : Fin 27) ∪ {a, b, c}) ≤ 12
    have hfa : (starMaskN (25 : Fin 27)).testBit a.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) a).mp ht))
    have hfb : (starMaskN (25 : Fin 27)).testBit b.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) b).mp ht))
    have hfc : (starMaskN (25 : Fin 27)).testBit c.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) c).mp ht))
    have hspec : ∀ p : Fin 27,
        (starMaskN (25 : Fin 27) ||| (1 <<< a.val) ||| (1 <<< b.val) ||| (1 <<< c.val)).testBit p.val = true ↔
          p ∈ stdStarIdx (25 : Fin 27) ∪ {a, b, c} := by
      intro p
      simp only [or_testBit, Bool.or_eq_true, shiftF_testBit,
        star_bit (25 : Fin 27) (by decide) p, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [classCountN_eq hspec]
    exact natA12_r7 a b c hfa hfb hfc (fun h => hab (Fin.val_injective h)) (fun h => hac (Fin.val_injective h)) (fun h => hbc (Fin.val_injective h))
  · show classCountIdx (stdStarIdx (12 : Fin 27) ∪ {a, b, c}) ≤ 12
    have hfa : (starMaskN (12 : Fin 27)).testBit a.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) a).mp ht))
    have hfb : (starMaskN (12 : Fin 27)).testBit b.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) b).mp ht))
    have hfc : (starMaskN (12 : Fin 27)).testBit c.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) c).mp ht))
    have hspec : ∀ p : Fin 27,
        (starMaskN (12 : Fin 27) ||| (1 <<< a.val) ||| (1 <<< b.val) ||| (1 <<< c.val)).testBit p.val = true ↔
          p ∈ stdStarIdx (12 : Fin 27) ∪ {a, b, c} := by
      intro p
      simp only [or_testBit, Bool.or_eq_true, shiftF_testBit,
        star_bit (12 : Fin 27) (by decide) p, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [classCountN_eq hspec]
    exact natA12_r8 a b c hfa hfb hfc (fun h => hab (Fin.val_injective h)) (fun h => hac (Fin.val_injective h)) (fun h => hbc (Fin.val_injective h))
  · show classCountIdx (stdStarIdx (21 : Fin 27) ∪ {a, b, c}) ≤ 12
    have hfa : (starMaskN (21 : Fin 27)).testBit a.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) a).mp ht))
    have hfb : (starMaskN (21 : Fin 27)).testBit b.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) b).mp ht))
    have hfc : (starMaskN (21 : Fin 27)).testBit c.val = false :=
      bool_eq_false (fun ht => (Finset.mem_sdiff.mp (hsub (by simp))).2 ((star_bit _ (by decide) c).mp ht))
    have hspec : ∀ p : Fin 27,
        (starMaskN (21 : Fin 27) ||| (1 <<< a.val) ||| (1 <<< b.val) ||| (1 <<< c.val)).testBit p.val = true ↔
          p ∈ stdStarIdx (21 : Fin 27) ∪ {a, b, c} := by
      intro p
      simp only [or_testBit, Bool.or_eq_true, shiftF_testBit,
        star_bit (21 : Fin 27) (by decide) p, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [classCountN_eq hspec]
    exact natA12_r9 a b c hfa hfb hfc (fun h => hab (Fin.val_injective h)) (fun h => hac (Fin.val_injective h)) (fun h => hbc (Fin.val_injective h))

end KakeyaMultiplicativity
