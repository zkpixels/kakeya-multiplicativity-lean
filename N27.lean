import N00Core

namespace KakeyaMultiplicativity

/-! The 27-world bitmask layer: Nat-numeral mirrors of `carriesIdx` /
`classCountIdx`, membership-spec decides for the literal windows
(plane, stars, lines), and the schema bridges.  The heavy endgame
decides live in P02Cov/P03E1..P10E8/N27A12R*; this file is cheap. -/

/-- Bitmask mirror of `carriesIdx`: same anchor/step structure, with
`Finset` membership replaced by `Nat.testBit` on the window mask. -/
def carriesN (m : ℕ) (d : Fin 27) : Bool :=
  (List.finRange 27).any fun p =>
    m.testBit p.val && m.testBit (addIdx p d).val
      && m.testBit (addIdx p (dblIdx d)).val

/-- The transversal as a bare list (same order as `classRepsIdx`). -/
def classRepsList : List (Fin 27) := [1, 4, 7, 10, 13, 16, 19, 22, 25, 3, 12, 21, 9]

/-- Bitmask mirror of `classCountIdx`. -/
def classCountN (m : ℕ) : ℕ := classRepsList.countP (carriesN m)

theorem classRepsList_mem :
    ∀ d : Fin 27, d ∈ classRepsList ↔ d ∈ classRepsIdx := by decide

theorem classRepsList_nodup : classRepsList.Nodup := by decide

/-- CARRIER BRIDGE: under a membership spec `testBit ↔ ∈ S`, the
bitmask carrier check is the artifact's carrier check. -/
theorem carriesN_iff {m : ℕ} {S : Finset (Fin 27)}
    (h : ∀ p : Fin 27, m.testBit p.val = true ↔ p ∈ S) (d : Fin 27) :
    carriesN m d = true ↔ carriesIdx S d := by
  unfold carriesN carriesIdx
  rw [List.any_eq_true]
  constructor
  · rintro ⟨p, -, hb⟩
    rw [Bool.and_eq_true, Bool.and_eq_true] at hb
    exact ⟨p, (h p).mp hb.1.1, (h _).mp hb.1.2, (h _).mp hb.2⟩
  · rintro ⟨p, hp, h1, h2⟩
    refine ⟨p, List.mem_finRange p, ?_⟩
    rw [Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨(h p).mpr hp, (h _).mpr h1⟩, (h _).mpr h2⟩

/-- COUNT BRIDGE: under a membership spec, the bitmask count is the
artifact's class count. -/
theorem classCountN_eq {m : ℕ} {S : Finset (Fin 27)}
    (h : ∀ p : Fin 27, m.testBit p.val = true ↔ p ∈ S) :
    classCountIdx S = classCountN m :=
  card_filter_eq_countP classRepsIdx classRepsList classRepsList_mem
    classRepsList_nodup _ _ (fun d _ => (carriesN_iff h d).symm)

/-- Membership spec for the plane mask `511`. -/
theorem zplane_bit :
    ∀ p : Fin 27, (511 : ℕ).testBit p.val = true ↔ p ∈ zPlaneIdx := by
  decide

theorem notZPlane_iff : ∀ a : Fin 27, a ∉ zPlaneIdx ↔ 9 ≤ a.val := by
  decide

/-- Star mask: the three axis lines plus the free line of `d`. -/
def starMaskN (d : Fin 27) : ℕ :=
  262735 ||| (1 <<< d.val) ||| (1 <<< (dblIdx d).val)

/-- The free representatives as a bare list (sdiff evaluation order). -/
def freeRepsList : List (Fin 27) := [4, 7, 10, 13, 16, 19, 22, 25, 12, 21]

theorem freeRepsList_mem :
    ∀ d : Fin 27, d ∈ freeRepsList ↔ d ∈ freeRepsIdx := by decide

/-- Membership spec for star masks (10 reps x 27 positions). -/
theorem star_bit :
    ∀ d ∈ freeRepsIdx, ∀ p : Fin 27,
      (starMaskN d).testBit p.val = true ↔ p ∈ stdStarIdx d := by
  decide

/-- Line mask through the origin. -/
def lineMaskN (d : Fin 27) : ℕ :=
  1 ||| (1 <<< d.val) ||| (1 <<< (dblIdx d).val)

/-- Membership spec for origin-line masks over plane directions. -/
theorem line_bit :
    ∀ d ∈ zPlaneDirsIdx, ∀ p : Fin 27,
      (lineMaskN d).testBit p.val = true ↔ p ∈ lineIdx0 d := by
  decide

/-- Plane directions as a bare list. -/
def zPlaneDirsList : List (Fin 27) := [1, 2, 3, 4, 5, 6, 7, 8]

theorem zPlaneDirsList_mem :
    ∀ d : Fin 27, d ∈ zPlaneDirsList ↔ d ∈ zPlaneDirsIdx := by decide


end KakeyaMultiplicativity
