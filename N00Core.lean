import P01Base

namespace KakeyaMultiplicativity

/-! Generic bit-bridge toolkit: the schema lemmas that tie Nat-bitmask
windows (one GMP numeral per window; membership = `Nat.testBit`) back
to the artifact's `Finset` windows.  Nothing here enumerates anything:
every lemma is structural.  The bitmask representation exists because
kernel reduction of `Finset`-of-`Finset` enumerations drags
quotient-wrapped terms through every step (~150GB per endgame decide);
flat numerals collapse the same decides to laptop scale (pilot:
3.5GB / 321s). -/

/-- `testBit` distributes over `|||` (restated locally to pin the name). -/
theorem or_testBit (a b i : ℕ) :
    (a ||| b).testBit i = (a.testBit i || b.testBit i) :=
  Nat.testBit_or a b i

/-- A shifted one-bit tests true exactly at its own position, stated
for `Fin`-indexed positions (the only form the bridges need). -/
theorem shiftF_testBit {n : ℕ} (x p : Fin n) :
    ((1 <<< x.val : ℕ)).testBit p.val = true ↔ p = x := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
  simp only [decide_eq_true_eq]
  exact ⟨fun h => Fin.val_injective h.symm, fun h => by rw [h]⟩

/-- Bool coercion helper: a refuted `= true` is a `= false`. -/
theorem bool_eq_false {b : Bool} (h : ¬(b = true)) : b = false := by
  cases b <;> simp_all

/-- THE COUNT BRIDGE (generic): a `Finset.filter` cardinality equals a
`List.countP` over any duplicate-free list with the same members and a
pointwise-agreeing Boolean predicate.  This is the single lemma that
lets the kernel count in list-world while the artifact counts in
Finset-world. -/
theorem card_filter_eq_countP {α : Type*} [DecidableEq α]
    (s : Finset α) (l : List α)
    (hl : ∀ a, a ∈ l ↔ a ∈ s) (hnd : l.Nodup)
    (p : α → Prop) [DecidablePred p] (q : α → Bool)
    (hpq : ∀ a ∈ s, (p a ↔ q a = true)) :
    (s.filter p).card = l.countP q := by
  have hts : l.toFinset = s := Finset.ext (by simp [List.mem_toFinset, hl])
  have hfeq : s.filter p = (l.filter q).toFinset := by
    ext a
    simp only [Finset.mem_filter, List.mem_toFinset, List.mem_filter]
    constructor
    · rintro ⟨ha, hp⟩
      exact ⟨(hl a).mpr ha, (hpq a ha).mp hp⟩
    · rintro ⟨ha, hq⟩
      have ha' := (hl a).mp ha
      exact ⟨ha', (hpq a ha').mpr hq⟩
  rw [hfeq, List.card_toFinset, (hnd.filter q).dedup,
    List.countP_eq_length_filter]

/-- Bitmask of a list of positions (fold of one-bits; the arbitrary-`T`
mask constructor for the certificate bridges). -/
def maskOfList {n : ℕ} (l : List (Fin n)) : ℕ :=
  l.foldr (fun p m => (1 <<< p.val) ||| m) 0

theorem testBit_maskOfList {n : ℕ} (l : List (Fin n)) (p : Fin n) :
    (maskOfList l).testBit p.val = true ↔ p ∈ l := by
  induction l with
  | nil =>
    show (0 : ℕ).testBit p.val = true ↔ p ∈ ([] : List (Fin n))
    simp [Nat.zero_testBit]
  | cons a t ih =>
    show ((1 <<< a.val) ||| maskOfList t).testBit p.val = true ↔ _
    rw [or_testBit]
    simp only [Bool.or_eq_true, ih, shiftF_testBit, List.mem_cons]

theorem maskOfList_lt {n : ℕ} (l : List (Fin n)) :
    maskOfList l < 2 ^ n := by
  induction l with
  | nil =>
    show (0 : ℕ) < 2 ^ n
    exact Nat.two_pow_pos n
  | cons a t ih =>
    show (1 <<< a.val) ||| maskOfList t < 2 ^ n
    refine Nat.or_lt_two_pow ?_ ih
    rw [Nat.shiftLeft_eq, one_mul]
    exact Nat.pow_lt_pow_right (by norm_num) a.isLt


end KakeyaMultiplicativity
