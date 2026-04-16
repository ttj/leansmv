/-
  Sorting: Testing vs Verification
  =================================

  WHAT — A complete correctness proof for insertion sort. We prove that
         for EVERY list of integers, the algorithm produces (a) a sorted
         list and (b) a rearrangement (permutation) of the input.

  HOW TO READ THIS FILE — Python first, then Lean
  -----------------------------------------------
  In Python, insertion sort looks like this (operating on a mutable list):

      def sort(a):
          for i in range(1, len(a)):
              key = a[i]
              j = i - 1
              while j >= 0 and a[j] > key:
                  a[j+1] = a[j]
                  j = j - 1
              a[j+1] = key

  We could also extend our IMP language with array operations and write
  the same algorithm there:

      i := 1;
      while i < len(a):
          key := a[i];
          j := i - 1;
          while j >= 0 && a[j] > key do
              a[j+1] := a[j];
              j := j - 1
          end;
          a[j+1] := key;
          i := i + 1

  The Lean version below uses `ins` (insert into a sorted prefix) and
  `sort` (insert each element in turn). Recursion plays the role of
  loops; it's a 1-to-1 translation from the imperative form. The
  ALGORITHM is the same; only the syntax differs. Further down in the
  file we ALSO include a literal Lean-imperative version using `Array`,
  `let mut`, `for`, and `while` — which executes identically and reads
  exactly like the Python.

  THE POINT OF THIS FILE
  ----------------------
  Testing: run the function on a specific input. `#eval sort [3,1,2]`
           produces `[1,2,3]`. One test, one input.
  Verification: prove a universally-quantified theorem about EVERY
                possible input. One theorem, infinitely many cases.

  We prove TWO correctness properties:
    (1) SORTEDNESS:  the output is a sorted list.
    (2) PERMUTATION: the output contains exactly the same elements
                     as the input (uses `List.Perm` from core Lean).

  TACTICS USED HERE — quick glossary:
    • intro / induction / cases / exact / apply / rw / simp / show — see other files
    • by_cases h : P     — split into two cases: P holds (h : P) or not (h : ¬P)
    • subst h            — eliminate a variable named in h := equation
    • rcases h with …    — destructure h with a pattern (Or, And, Exists, …)
    • absurd hp hnp      — from hp:P and hnp:¬P, derive any goal
    • Int.le_of_not_le   — from ¬(x ≤ y) we get y ≤ x (totality of ≤)
    • Int.le_trans       — chain x ≤ y and y ≤ z to get x ≤ z
    • induction xs generalizing y — induct on xs, also generalizing y
                                    so the IH is universally-quantified in y
    • #eval expr         — at compile time, run `expr` and print its value
    • example : ... := by decide  — Lean computes a decidable claim
    • Id.run do …        — execute an imperative do-block and return its result
    • let mut x := …     — declare a mutable local in a do-block
-/

namespace SortDemo

/- ------------------------------------------------------------------- -/
/- The algorithm.                                                      -/

/-- Insert `x` into a list, before the first `y` with `x ≤ y`.
    (Recursive form of the Python inner loop "shift larger items right".) -/
def ins (x : Int) : List Int → List Int
  | []      => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: ins x ys

/-- Insertion sort: insert each element into the sort of the rest.
    (Recursive form of the Python outer loop.) -/
def sort : List Int → List Int
  | []      => []
  | x :: xs => ins x (sort xs)

/- ------------------------------------------------------------------- -/
/- The specification: what does it mean to be sorted?                  -/

/-- A list is sorted if every adjacent pair is in non-decreasing order.
    Three constructors: empty list, singleton list, and "head ≤ next-head
    AND the tail is itself sorted". -/
inductive Sorted : List Int → Prop where
  | nil       : Sorted []
  | singleton : ∀ x, Sorted [x]
  | cons      : ∀ x y ys, x ≤ y → Sorted (y :: ys) → Sorted (x :: y :: ys)

/- ------------------------------------------------------------------- -/
/- TESTING — run on specific inputs. Each line covers ONE input.       -/

#eval sort [3, 1, 4, 1, 5, 9, 2, 6]   -- [1, 1, 2, 3, 4, 5, 6, 9]
#eval sort [5, 4, 3, 2, 1]            -- [1, 2, 3, 4, 5]
#eval sort ([] : List Int)            -- []
#eval sort [-3, 0, -1, 5, -10]        -- [-10, -3, -1, 0, 5]
#eval sort [7]                        -- [7]
#eval sort [2, 2, 2]                  -- [2, 2, 2]

-- Machine-checkable tests: each is a theorem about ONE specific input.
example : sort [3, 1, 4, 1, 5, 9, 2, 6] = [1, 1, 2, 3, 4, 5, 6, 9] := by decide
example : sort [5, 4, 3, 2, 1]          = [1, 2, 3, 4, 5]          := by decide
example : sort ([] : List Int)          = []                       := by decide
example : sort [-3, 0, -1, 5, -10]      = [-10, -3, -1, 0, 5]      := by decide

-- These ten tests give confidence on TEN specific inputs. There are
-- infinitely many possible List Int values; testing cannot cover them all.

/- ------------------------------------------------------------------- -/
/- VERIFICATION — one theorem, infinitely many inputs.                 -/

/-- Helper: in a sorted list `y :: ys`, every element of `ys` is ≥ y.
    STRATEGY: induct on `ys`, generalising over the head `y` so the
    inductive hypothesis is applicable when we recurse into the tail. -/
theorem sorted_head_le (y : Int) : ∀ (ys : List Int),
    Sorted (y :: ys) → ∀ z ∈ ys, y ≤ z := by
  intro ys hs z hz                                -- name list, sortedness proof, the element z and proof z ∈ ys
  induction ys generalizing y with                -- induct on ys; generalising y keeps the IH universal in y
  | nil => exact absurd hz (by simp)              -- ys = [] ⇒ z can't be in []; `simp` proves z ∉ []
  | cons a as ih =>
    rw [List.mem_cons] at hz                      -- rewrite z ∈ a :: as as z = a ∨ z ∈ as
    cases hz with                                 -- split: either z is the head, or it's deeper
    | inl heq =>                                  -- case z = a
      subst heq                                   -- substitute z everywhere by a
      cases hs with                               -- analyse Sorted (y :: a :: as)
      | cons _ _ _ hya _ => exact hya             -- the `cons` constructor gives us y ≤ a directly
    | inr hin =>                                  -- case z ∈ as
      cases hs with                               -- analyse the sortedness again to extract y ≤ a
      | cons _ _ _ hya hsa =>                     -- hya : y ≤ a; hsa : Sorted (a :: as)
        exact Int.le_trans hya (ih a hsa hin)     -- chain y ≤ a (hya) with a ≤ z (from IH applied to a)

/-- If `x` is ≤ every element of `ys`, and `ys` is sorted, then `x :: ys`
    is sorted. Two-line case-split on whether `ys` is empty. -/
theorem sorted_cons_of_le (x : Int) (ys : List Int)
    (hlb : ∀ y ∈ ys, x ≤ y) (hs : Sorted ys) : Sorted (x :: ys) := by
  cases ys with                                                       -- split on ys = [] vs ys = y :: ys'
  | nil => exact Sorted.singleton x                                   -- empty: result is a singleton list, which is sorted
  | cons y ys' =>
    exact Sorted.cons x y ys' (hlb y List.mem_cons_self) hs           -- non-empty: invoke the cons rule, lower-bound from hlb

/-- `ins z ys` preserves a lower bound: if `x ≤ z` and `x ≤` every `y ∈ ys`,
    then `x ≤` every element of `ins z ys`.
    STRATEGY: induct on `ys`. The interesting work is in the cons case,
    where we case-split on whether `z ≤ a` (which determines where in
    the result `z` lands). -/
theorem ins_preserves_lb (x z : Int) (ys : List Int) (hxz : x ≤ z)
    (hlb : ∀ y ∈ ys, x ≤ y) : ∀ y ∈ ins z ys, x ≤ y := by
  induction ys with
  | nil =>                                                            -- ys = []: ins z [] = [z]
    intro y hy                                                        -- pick y ∈ ins z [] = [z]
    show x ≤ y                                                        -- restate the goal explicitly
    have : ins z [] = [z] := rfl                                      -- by definition of `ins`
    rw [this] at hy                                                   -- now hy : y ∈ [z]
    rw [List.mem_singleton] at hy                                     -- hy : y = z
    rw [hy]; exact hxz                                                -- substitute and use x ≤ z
  | cons a as ih =>
    intro y hy                                                        -- pick y ∈ ins z (a :: as)
    by_cases hza : z ≤ a                                              -- two shapes for `ins z (a :: as)` depending on z ≤ a
    · -- case z ≤ a: ins z (a :: as) = z :: a :: as
      have heq : ins z (a :: as) = z :: a :: as := by                 -- compute the unfolded form
        show (if z ≤ a then z :: a :: as else a :: ins z as) = _
        rw [if_pos hza]                                               -- pick the then-branch
      rw [heq] at hy                                                  -- hy : y ∈ z :: a :: as
      rw [List.mem_cons] at hy                                        -- hy : y = z ∨ y ∈ a :: as
      cases hy with
      | inl h => rw [h]; exact hxz                                    -- y = z: use x ≤ z
      | inr h =>
        rw [List.mem_cons] at h                                       -- h : y = a ∨ y ∈ as
        cases h with
        | inl h2 => rw [h2]; exact hlb a List.mem_cons_self           -- y = a: x ≤ a from hlb
        | inr h2 => exact hlb y (List.mem_cons_of_mem a h2)           -- y deeper: x ≤ y from hlb
    · -- case ¬(z ≤ a): ins z (a :: as) = a :: ins z as
      have heq : ins z (a :: as) = a :: ins z as := by
        show (if z ≤ a then z :: a :: as else a :: ins z as) = _
        rw [if_neg hza]                                               -- pick the else-branch
      rw [heq] at hy                                                  -- hy : y ∈ a :: ins z as
      rw [List.mem_cons] at hy                                        -- hy : y = a ∨ y ∈ ins z as
      cases hy with
      | inl h => rw [h]; exact hlb a List.mem_cons_self               -- y = a: x ≤ a from hlb
      | inr h =>
        have hlb' : ∀ y ∈ as, x ≤ y :=                                -- shrink hlb to the tail
          fun y hy => hlb y (List.mem_cons_of_mem a hy)
        exact ih hlb' y h                                             -- recursive call (IH) handles the tail

/-- ★ Key lemma: `ins` preserves sortedness.
    STRATEGY: induct on the input `ys`. When ys is empty, `ins x [] = [x]`,
    which is trivially sorted. For ys = y :: ys', we case-split on whether
    `x ≤ y` (so x goes at the front) or `x > y` (x goes deeper, and we
    rely on the IH plus the lower-bound lemma to glue the head back on). -/
theorem ins_sorted (x : Int) (ys : List Int) (hs : Sorted ys) :
    Sorted (ins x ys) := by
  induction ys with
  | nil =>
    show Sorted [x]                                          -- restate goal: result is a singleton list
    exact Sorted.singleton x                                 -- which is sorted
  | cons y ys' ih =>
    by_cases hxy : x ≤ y                                     -- two cases by where x lands
    · -- ins x (y :: ys') = x :: y :: ys'   (x at the head)
      have heq : ins x (y :: ys') = x :: y :: ys' := by
        show (if x ≤ y then x :: y :: ys' else y :: ins x ys') = _
        rw [if_pos hxy]                                      -- pick the then-branch
      rw [heq]                                               -- rewrite the goal accordingly
      exact Sorted.cons x y ys' hxy hs                       -- close: x ≤ y plus the existing sortedness of y::ys'
    · -- ins x (y :: ys') = y :: ins x ys'   (x goes deeper)
      have heq : ins x (y :: ys') = y :: ins x ys' := by
        show (if x ≤ y then x :: y :: ys' else y :: ins x ys') = _
        rw [if_neg hxy]                                      -- pick the else-branch
      rw [heq]                                               -- rewrite the goal
      have hs' : Sorted ys' := by                            -- extract sortedness of the strict tail
        cases hs with
        | singleton _ => exact Sorted.nil                    -- ys' = []
        | cons _ _ _ _ hss => exact hss                      -- ys' = a :: as : pull out the inner Sorted
      have ih' := ih hs'                                     -- IH: Sorted (ins x ys')
      apply sorted_cons_of_le y (ins x ys') ?_ ih'           -- glue y on the front, leaving "y ≤ everything in ins x ys'" as a sub-goal
      have hyx : y ≤ x := Int.le_of_not_le hxy               -- from ¬(x ≤ y) and totality, y ≤ x
      have hylb : ∀ z ∈ ys', y ≤ z := sorted_head_le y ys' hs -- y was already ≤ everything in ys'
      exact ins_preserves_lb y x ys' hyx hylb                -- combine: y ≤ everything in ins x ys'

/-- ★ Main correctness theorem (1): for ALL lists, sort produces a sorted list.
    STRATEGY: induct on the input list; each step is `ins_sorted` applied
    to the IH. Three lines of actual proof. -/
theorem sort_sorted : ∀ xs : List Int, Sorted (sort xs) := by
  intro xs                                                   -- name the input
  induction xs with
  | nil => exact Sorted.nil                                  -- sort [] = []; the empty list is sorted
  | cons x xs ih =>
    show Sorted (ins x (sort xs))                            -- restate via the recursive definition of `sort`
    exact ins_sorted x (sort xs) ih                          -- ih = Sorted (sort xs); insert preserves sortedness

/- ------------------------------------------------------------------- -/
/- Permutation: the output is a rearrangement of the input.            -/

/-- `ins x ys` is a permutation of `x :: ys`.
    STRATEGY: induct on ys. When inserting at the head, the result is
    literally `x :: ys`; otherwise we use `swap` to move x past the
    head element. -/
theorem ins_perm (x : Int) : ∀ ys : List Int,
    List.Perm (ins x ys) (x :: ys) := by
  intro ys                                                   -- name ys
  induction ys with
  | nil => exact List.Perm.refl _                            -- ins x [] = [x] = x :: []; reflexively a permutation
  | cons y ys' ih =>
    by_cases hxy : x ≤ y                                     -- same dichotomy as before
    · have heq : ins x (y :: ys') = x :: y :: ys' := by      -- ins x (y :: ys') reduces to x :: y :: ys'
        show (if x ≤ y then x :: y :: ys' else y :: ins x ys') = _
        rw [if_pos hxy]
      rw [heq]                                               -- after rewrite, goal is `Perm (x::y::ys') (x::y::ys')` — reflexive
    · have heq : ins x (y :: ys') = y :: ins x ys' := by     -- otherwise the insert recurses past y
        show (if x ≤ y then x :: y :: ys' else y :: ins x ys') = _
        rw [if_neg hxy]
      rw [heq]                                               -- goal: Perm (y :: ins x ys') (x :: y :: ys')
      -- (y :: ins x ys') ~ (y :: x :: ys') by IH on the tail; then swap y and x.
      exact (ih.cons y).trans (List.Perm.swap x y ys')

/-- ★ Main correctness theorem (2): for ALL lists, sort produces a permutation.
    STRATEGY: induct on the list, chain the `ins_perm` lemma with
    the IH's permutation of the tail. -/
theorem sort_perm : ∀ xs : List Int, List.Perm (sort xs) xs := by
  intro xs                                                   -- name input
  induction xs with
  | nil => exact List.Perm.refl _                            -- sort [] = [] = []; trivially permutation
  | cons x xs ih =>
    show List.Perm (ins x (sort xs)) (x :: xs)               -- unfold sort on cons
    exact (ins_perm x (sort xs)).trans (ih.cons x)           -- chain: ins x (sort xs) ~ x :: sort xs ~ x :: xs

/- ------------------------------------------------------------------- -/
/- Corollaries — both follow trivially from the permutation theorem.   -/

/-- Sort preserves length (no element added or lost). -/
theorem sort_length (xs : List Int) : (sort xs).length = xs.length :=
  (sort_perm xs).length_eq    -- permutations have equal lengths (stdlib fact)

/-- An element is in `sort xs` iff it is in `xs`. -/
theorem sort_mem (x : Int) (xs : List Int) : x ∈ sort xs ↔ x ∈ xs :=
  (sort_perm xs).mem_iff      -- permutations have the same membership (stdlib fact)

/- ------------------------------------------------------------------- -/
/- The payoff — one statement, universally quantified.                 -/

/--
  ★ SORT IS CORRECT FOR ALL LISTS ★

  For EVERY list of integers `xs`, `sort xs` is both sorted AND a
  permutation of `xs`. This single theorem covers infinitely many
  inputs simultaneously — something testing fundamentally cannot do.
-/
theorem sort_correct : ∀ xs : List Int,
    Sorted (sort xs) ∧ List.Perm (sort xs) xs :=
  fun xs => ⟨sort_sorted xs, sort_perm xs⟩    -- pair the two main theorems for any xs

/- ------------------------------------------------------------------- -/
/- IMPERATIVE EXECUTABLE VERSION (Lean's real imperative syntax).      -/
/-                                                                     -/
/- Below is an *actually-executable* imperative implementation using   -/
/- mutable arrays — the same sort, written as Python would write it.   -/
/- Lean 4 has full support for `Array`, `do`-blocks, `let mut`, `for`, -/
/- `while`, in-place updates, and early `return`. Compare line-by-line -/
/- with the Python pseudocode at the top of the file.                  -/

/-- Insertion sort, written imperatively with a mutable array.
    Compare line-by-line with the Python pseudocode at the top of the file. -/
def sortArr (input : Array Int) : Array Int := Id.run do
  let mut a := input                                  -- mutable copy of the input array
  let n := a.size                                     -- cache the length
  for i in [1 : n] do                                 -- outer loop: i from 1 to n-1
    let key := a[i]!                                  -- the value being inserted into the sorted prefix
    -- Shift larger neighbors right; j marks the open slot.
    let mut j : Nat := i                              -- j starts at the slot just past the sorted prefix
    while j > 0 ∧ a[j - 1]! > key do                  -- while there's a bigger neighbor to the left,
      a := a.set! j a[j - 1]!                         --   shift it one slot right
      j := j - 1                                      --   move the open slot left
    a := a.set! j key                                 -- drop key into the open slot
  return a                                            -- final sorted array

-- Run the imperative version on the same test inputs as the functional one.
#eval sortArr #[3, 1, 4, 1, 5, 9, 2, 6]   -- #[1, 1, 2, 3, 4, 5, 6, 9]
#eval sortArr #[5, 4, 3, 2, 1]            -- #[1, 2, 3, 4, 5]
#eval sortArr (#[] : Array Int)           -- #[]
#eval sortArr #[-3, 0, -1, 5, -10]        -- #[-10, -3, -1, 0, 5]

/- Why two implementations?                                            -/
/- Both `sort` (functional/recursive) and `sortArr` (imperative/loop)  -/
/- compute the same answer. We proved `sort_correct` for the           -/
/- functional one because (a) recursion is mathematically cleaner to   -/
/- reason about and (b) Lean's term-level reasoning is most direct on  -/
/- recursive definitions. The imperative version is what would ship in -/
/- production code; the functional version is the *specification* we   -/
/- prove correct. They are the same algorithm.                         -/

end SortDemo
