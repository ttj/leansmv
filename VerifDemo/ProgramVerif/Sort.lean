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
/- IMPERATIVE EXECUTABLE VERSION — and its correctness proof.          -/
/-                                                                     -/
/- Below is an *actually-executable* imperative implementation using   -/
/- mutable arrays — the same sort, written as Python would write it.   -/
/- Python pseudocode, for comparison:                                  -/
/-                                                                     -/
/-     def sort(a):                                                    -/
/-         for i in range(1, len(a)):                                  -/
/-             key = a[i]                                              -/
/-             j = i - 1                                               -/
/-             while j >= 0 and a[j] > key:                            -/
/-                 a[j+1] = a[j]                                       -/
/-                 j = j - 1                                           -/
/-             a[j+1] = key                                            -/
/-                                                                     -/
/- We encode the inner `while` and outer `for` as structurally/        -/
/- well-foundedly recursive functions (`insArr` / `sortArrFrom`). This -/
/- makes the algorithm transparent to Lean's equation compiler so we   -/
/- can prove correctness directly. The result executes identically to  -/
/- a `do`/`for`/`while` version — only the control-flow encoding       -/
/- differs.                                                            -/

/-- Insert `key` into a sorted prefix of length `j+1` (inside array `a`).
    Models the inner `while` loop: if `a[j] > key`, shift `a[j]` right
    into position `j+1` and recurse with `j-1`; otherwise, drop `key`
    into position `j+1`. At `j = 0`, we place `key` at position 0. -/
def insArr (a : Array Int) (key : Int) : Nat → Array Int
  | 0     => a.set! 0 key
  | j + 1 =>
    if a[j]! > key then
      insArr (a.set! (j + 1) a[j]!) key j
    else
      a.set! (j + 1) key

/-- Outer loop: for each `i` in `[i, n)`, insert `a[i]` into the sorted
    prefix `a[0..i)`. Well-founded on `n - i`. -/
def sortArrFrom (a : Array Int) (i n : Nat) : Array Int :=
  if h : i < n then
    sortArrFrom (insArr a a[i]! i) (i + 1) n
  else
    a
termination_by n - i
decreasing_by exact Nat.sub_lt_sub_left h (Nat.lt_succ_self i)

/-- Insertion sort on an array: apply `sortArrFrom` from `i = 1`. -/
def sortArr (a : Array Int) : Array Int := sortArrFrom a 1 a.size

-- Run the imperative version on the same test inputs as the functional one.
#eval sortArr #[3, 1, 4, 1, 5, 9, 2, 6]   -- #[1, 1, 2, 3, 4, 5, 6, 9]
#eval sortArr #[5, 4, 3, 2, 1]            -- #[1, 2, 3, 4, 5]
#eval sortArr (#[] : Array Int)           -- #[]
#eval sortArr #[-3, 0, -1, 5, -10]        -- #[-10, -3, -1, 0, 5]

/- ------------------------------------------------------------------- -/
/- Correctness for the imperative version.                             -/
/-                                                                     -/
/- STRATEGY. The functional `ins` / `sort` above is our *specification*.-/
/- We build a bridge showing that `insArr a key j` — acting on a        -/
/- toList whose first `j` elements are sorted — produces the same list  -/
/- as `ins key (take j …) ++ drop (j+1) …`. From that, per-step         -/
/- sortedness/permutation/size properties follow, and the outer-loop    -/
/- invariant `sortArrFrom_spec` chains them across iterations.          -/

/-- `ins key (xs ++ [y]) = ins key xs ++ [y]` when `y > key`.
    PLAIN induction on `xs`; no sortedness required. -/
theorem ins_snoc_gt (key y : Int) (hyk : y > key) :
    ∀ xs : List Int, ins key (xs ++ [y]) = ins key xs ++ [y] := by
  intro xs
  induction xs with
  | nil =>
    -- ins key [y] = [key, y] since key ≤ y.
    have hky : key ≤ y := Int.le_of_lt hyk
    show ins key [y] = ins key [] ++ [y]
    show (if key ≤ y then key :: [y] else y :: ins key []) = [key] ++ [y]
    rw [if_pos hky]; rfl
  | cons x xs' ih =>
    show ins key (x :: (xs' ++ [y])) = ins key (x :: xs') ++ [y]
    by_cases hkx : key ≤ x
    · -- both branches take the then-branch
      show (if key ≤ x then key :: x :: (xs' ++ [y]) else x :: ins key (xs' ++ [y]))
             = (if key ≤ x then key :: x :: xs' else x :: ins key xs') ++ [y]
      rw [if_pos hkx, if_pos hkx]
      simp only [List.cons_append]
    · -- else-branch: recurse, using IH.
      show (if key ≤ x then key :: x :: (xs' ++ [y]) else x :: ins key (xs' ++ [y]))
             = (if key ≤ x then key :: x :: xs' else x :: ins key xs') ++ [y]
      rw [if_neg hkx, if_neg hkx, ih]
      rfl

/-- Every element of a sorted list is ≤ the last element (when the list is
    of the form `xs ++ [y]`). STRATEGY: induct on `xs` with `head` generalized. -/
theorem sorted_snoc_le_last (y : Int) : ∀ (xs : List Int),
    Sorted (xs ++ [y]) → ∀ z ∈ xs ++ [y], z ≤ y := by
  intro xs
  induction xs with
  | nil =>
    intro _ z hz
    rw [List.nil_append, List.mem_singleton] at hz
    rw [hz]; exact Int.le_refl y
  | cons x xs' ih =>
    intro hs z hz
    -- Sorted ((x :: xs') ++ [y]) = Sorted (x :: (xs' ++ [y])).
    have hs' : Sorted (x :: (xs' ++ [y])) := hs
    -- Extract Sorted (xs' ++ [y]). Case on xs' so `xs' ++ [y]` is definitely nonempty.
    have hs_rest : Sorted (xs' ++ [y]) := by
      cases xs' with
      | nil =>
        -- xs' ++ [y] = [y], singleton is sorted.
        exact Sorted.singleton y
      | cons a as =>
        -- hs' : Sorted (x :: (a :: as ++ [y])). Cons case of Sorted.
        cases hs' with
        | cons _ _ _ _ hss => exact hss
    -- z ∈ (x :: xs') ++ [y] = x :: (xs' ++ [y])
    rw [List.cons_append, List.mem_cons] at hz
    cases hz with
    | inl hzx =>
      -- z = x; use x ≤ y via sorted_head_le on hs' with y as the tail member.
      have hy_in : y ∈ xs' ++ [y] :=
        List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
      rw [hzx]
      exact sorted_head_le x (xs' ++ [y]) hs' y hy_in
    | inr hz_rest =>
      -- z ∈ xs' ++ [y]; apply IH.
      exact ih hs_rest z hz_rest

/-- If `xs ++ [y]` is sorted and `y ≤ key`, then `ins key (xs ++ [y]) = xs ++ [y, key]`.
    STRATEGY: induct on xs. In the cons if-pos branch, sortedness + y ≤ key
    force every element of xs' and y itself to equal key. -/
theorem ins_snoc_le_sorted (key y : Int) (hyk : y ≤ key) :
    ∀ xs : List Int, Sorted (xs ++ [y]) →
      ins key (xs ++ [y]) = xs ++ [y, key] := by
  intro xs hs
  induction xs with
  | nil =>
    show ins key [y] = [y, key]
    show (if key ≤ y then key :: [y] else y :: ins key []) = [y, key]
    by_cases hky : key ≤ y
    · -- y ≤ key and key ≤ y ⇒ y = key
      have heq : y = key := Int.le_antisymm hyk hky
      rw [if_pos hky, heq]
    · rw [if_neg hky]; rfl
  | cons x xs' ih =>
    have hs' : Sorted (x :: (xs' ++ [y])) := hs
    -- Extract Sorted (xs' ++ [y]). Case on xs' first.
    have hs_rest : Sorted (xs' ++ [y]) := by
      cases xs' with
      | nil => exact Sorted.singleton y
      | cons a as =>
        cases hs' with
        | cons _ _ _ _ hss => exact hss
    -- x ≤ y.
    have hxy : x ≤ y := by
      have hy_in : y ∈ xs' ++ [y] :=
        List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
      exact sorted_head_le x (xs' ++ [y]) hs' y hy_in
    by_cases hkx : key ≤ x
    · -- key ≤ x ≤ y ≤ key ⇒ x = y = key AND every z ∈ xs' equals key.
      have hxk : x = key := Int.le_antisymm (Int.le_trans hxy hyk) hkx
      have hyk' : y = key := Int.le_antisymm hyk (Int.le_trans hkx hxy)
      -- Every z ∈ xs' equals key: x ≤ z (head-le) and z ≤ y (snoc-le-last).
      have hall : ∀ z ∈ xs', z = key := by
        intro z hz
        have hz_rest : z ∈ xs' ++ [y] := List.mem_append.mpr (Or.inl hz)
        have hxz : x ≤ z := sorted_head_le x (xs' ++ [y]) hs' z hz_rest
        have hzy : z ≤ y := sorted_snoc_le_last y xs' hs_rest z hz_rest
        exact Int.le_antisymm (Int.le_trans hzy hyk) (Int.le_trans hkx hxz)
      -- xs' is a list of `key`s. So xs' ++ [y] = xs' ++ [key] and
      -- key :: x :: (xs' ++ [y]) = x :: xs' ++ [y, key] since both become
      -- key :: key :: xs' ++ [key] with xs' all keys.
      -- Reduce both sides to `(x :: xs') ++ [y, key]` step by step.
      show ins key (x :: (xs' ++ [y])) = (x :: xs') ++ [y, key]
      show (if key ≤ x then key :: x :: (xs' ++ [y]) else x :: ins key (xs' ++ [y]))
             = (x :: xs') ++ [y, key]
      rw [if_pos hkx]
      -- Goal: key :: x :: (xs' ++ [y]) = (x :: xs') ++ [y, key]
      -- Rewrite x and y to key; both sides collapse to a list of `key`s.
      rw [hxk, hyk']
      -- Goal: key :: key :: (xs' ++ [key]) = (key :: xs') ++ [key, key]
      rw [List.cons_append]
      -- Goal: key :: key :: (xs' ++ [key]) = key :: (xs' ++ [key, key])
      congr 1
      -- Goal: key :: (xs' ++ [key]) = xs' ++ [key, key]
      -- Using `hall`: every entry of xs' is key. Prove by induction on xs'.
      clear ih hs hs' hs_rest hxy hkx hxk hyk'
      induction xs' with
      | nil => rfl
      | cons a as ih2 =>
        have hak : a = key := hall a List.mem_cons_self
        have hall' : ∀ z ∈ as, z = key := fun z hz =>
          hall z (List.mem_cons_of_mem a hz)
        rw [hak]
        -- Goal: key :: ((key :: as) ++ [key]) = (key :: as) ++ [key, key]
        show key :: (key :: (as ++ [key])) = key :: (as ++ [key, key])
        congr 1
        exact ih2 hall'
    · -- else-branch: ins key (x :: (xs' ++ [y])) = x :: ins key (xs' ++ [y]); use IH.
      show ins key (x :: (xs' ++ [y])) = (x :: xs') ++ [y, key]
      show (if key ≤ x then key :: x :: (xs' ++ [y]) else x :: ins key (xs' ++ [y]))
             = (x :: xs') ++ [y, key]
      rw [if_neg hkx]
      have ih' := ih hs_rest
      rw [ih']
      rfl

/-- Auxiliary: `Sorted (xs ++ [z])` implies `Sorted xs`. -/
theorem sorted_of_sorted_snoc (xs : List Int) (z : Int) :
    Sorted (xs ++ [z]) → Sorted xs := by
  intro hs
  induction xs with
  | nil => exact Sorted.nil
  | cons x xs' ih =>
    cases xs' with
    | nil => exact Sorted.singleton x
    | cons y ys =>
      have hs' : Sorted (x :: ((y :: ys) ++ [z])) := hs
      cases hs' with
      | cons _ _ _ hxy hss =>
        exact Sorted.cons x y ys hxy (ih hss)

/-- The bridge: under sortedness of the first `j` elements and `j < a.size`,
    `insArr a key j` corresponds to inserting `key` into the sorted prefix
    and leaving the suffix past index `j` alone. -/
theorem insArr_toList (key : Int) :
    ∀ (j : Nat) (a : Array Int), j < a.size → Sorted (a.toList.take j) →
      (insArr a key j).toList
        = ins key (a.toList.take j) ++ a.toList.drop (j + 1) := by
  intro j
  induction j with
  | zero =>
    intro a hsize _
    show (a.set! 0 key).toList = ins key (a.toList.take 0) ++ a.toList.drop 1
    simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
    -- a.toList must be hd :: tl since hsize : 0 < a.size.
    cases h : a.toList with
    | nil =>
      exfalso
      have hlen : a.toList.length = 0 := by rw [h]; rfl
      rw [Array.length_toList] at hlen
      omega
    | cons hd tl =>
      show (hd :: tl).set 0 key = ins key [] ++ (hd :: tl).drop 1
      rfl
  | succ j ih =>
    intro a hsize hs_take
    show (insArr a key (j + 1)).toList
           = ins key (a.toList.take (j + 1)) ++ a.toList.drop (j + 1 + 1)
    -- Unfold insArr at j+1.
    show (if a[j]! > key then insArr (a.set! (j + 1) a[j]!) key j
                       else a.set! (j + 1) key).toList
           = ins key (a.toList.take (j + 1)) ++ a.toList.drop (j + 1 + 1)
    -- Shared facts.
    have hj_lt : j < a.size := Nat.lt_of_succ_lt hsize
    have hj_len : j < a.toList.length := by rw [Array.length_toList]; exact hj_lt
    have hj1_len : j + 1 < a.toList.length := by rw [Array.length_toList]; exact hsize
    have haj : a[j]! = a.toList[j] := by
      rw [show a[j]! = a[j]'hj_lt from getElem!_pos a j hj_lt]
      rfl
    have htake_succ : a.toList.take (j + 1) = a.toList.take j ++ [a.toList[j]] :=
      List.take_succ_eq_append_getElem hj_len
    by_cases hgt : a[j]! > key
    · -- Shift branch.
      rw [if_pos hgt]
      -- Let a' = a.set! (j+1) a[j]!. Prepare its properties.
      have hsize' : (a.set! (j + 1) a[j]!).size = a.size := by
        simp
      have hj_lt' : j < (a.set! (j + 1) a[j]!).size := by rw [hsize']; exact hj_lt
      have ha'_toList : (a.set! (j + 1) a[j]!).toList = a.toList.set (j + 1) a[j]! := by
        simp
      have htake_a' : (a.set! (j + 1) a[j]!).toList.take j = a.toList.take j := by
        rw [ha'_toList, List.take_set_of_le (Nat.le_succ j)]
      -- Sorted prefix of a' at length j is same as a's.
      have hs_take_a' : Sorted ((a.set! (j + 1) a[j]!).toList.take j) := by
        rw [htake_a']
        have hsnoc : Sorted (a.toList.take j ++ [a.toList[j]]) := htake_succ ▸ hs_take
        exact sorted_of_sorted_snoc _ _ hsnoc
      -- Apply IH on a' at j.
      have ih' := ih (a.set! (j + 1) a[j]!) hj_lt' hs_take_a'
      rw [ih', htake_a']
      -- Compute a'.toList.drop (j + 1): set beyond j+1 drops to a.toList.drop (j+1) with head replaced by a[j]!.
      have hdrop_a' : (a.set! (j + 1) a[j]!).toList.drop (j + 1)
                        = a[j]! :: a.toList.drop (j + 1 + 1) := by
        rw [ha'_toList, List.drop_set]
        rw [if_neg (Nat.not_lt.mpr (Nat.le_refl (j + 1)))]
        rw [Nat.sub_self]
        rw [List.drop_eq_getElem_cons hj1_len]
        simp
      rw [hdrop_a']
      -- Now the shift-branch LHS: ins key (take j a.toList) ++ (a[j]! :: drop (j+2) a.toList)
      -- The target RHS: ins key (take (j+1) a.toList) ++ drop (j+2) a.toList
      -- Rewrite take (j+1) = take j ++ [a.toList[j]], then ins_snoc_gt.
      rw [htake_succ]
      have hgt_val : a.toList[j] > key := by rw [← haj]; exact hgt
      rw [ins_snoc_gt key a.toList[j] hgt_val (a.toList.take j)]
      -- Goal: ins key (take j) ++ [a.toList[j]] ++ (a[j]! :: drop (j+2)) = ins key (take j) ++ [a.toList[j]] ++ drop (j+2)
      -- Wait — they need to be equal; show a[j]! = a.toList[j] and restructure the append.
      rw [haj]
      -- Goal: ins key (take j) ++ [a.toList[j]] ++ (a.toList[j] :: drop (j+2)) = ins key (take j) ++ [a.toList[j]] ++ drop (j+2)
      -- That's not right — LHS has [a.toList[j]] ++ a.toList[j] :: drop, RHS has [a.toList[j]] but drop only once.
      -- Look again. Post-rw [ins_snoc_gt], LHS becomes (ins key (take j) ++ [a.toList[j]]) ++ drop_a'.
      -- drop_a' after rw = (a[j]! :: drop (j+2)) but we rw'd haj making it a.toList[j] :: drop (j+2).
      -- RHS is ins key (take j ++ [a.toList[j]]) ++ drop (j+2) — wait, we rw [ins_snoc_gt] on the LHS,
      -- so RHS still has ins key (take j ++ [a.toList[j]])? Actually, ins_snoc_gt rewrites
      -- `ins key (xs ++ [y])` to `ins key xs ++ [y]`. So if RHS had `ins key (take (j+1))`, which we
      -- rewrote to `ins key (take j ++ [a.toList[j]])`, then ins_snoc_gt rewrites it to
      -- `ins key (take j) ++ [a.toList[j]]`. That makes both sides match after list_append_assoc.
      simp [List.append_assoc]
    · -- Else branch: a[j]! ≤ key; drop key at position j+1.
      rw [if_neg hgt]
      show (a.set! (j + 1) key).toList
             = ins key (a.toList.take (j + 1)) ++ a.toList.drop (j + 1 + 1)
      simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
      rw [List.set_eq_take_append_cons_drop]
      rw [if_pos hj1_len]
      -- LHS: a.toList.take (j+1) ++ key :: a.toList.drop (j+1+1)
      -- RHS: ins key (a.toList.take (j+1)) ++ a.toList.drop (j+1+1)
      -- Show ins key (a.toList.take (j+1)) = a.toList.take (j+1) ++ [key] via ins_snoc_le_sorted.
      have hyk : a.toList[j] ≤ key := by
        have h' : a[j]! ≤ key := Int.not_lt.mp hgt
        rw [haj] at h'; exact h'
      have hs_snoc : Sorted (a.toList.take j ++ [a.toList[j]]) := htake_succ ▸ hs_take
      rw [htake_succ]
      rw [ins_snoc_le_sorted key a.toList[j] hyk _ hs_snoc]
      -- Goal: (take j ++ [a.toList[j]]) ++ key :: drop (j+2) = (take j ++ [a.toList[j], key]) ++ drop (j+2)
      simp [List.append_assoc]

/-- Size of `insArr a key j` is the size of `a` (bounded-in-place updates). -/
theorem insArr_size (key : Int) :
    ∀ (j : Nat) (a : Array Int), (insArr a key j).size = a.size := by
  intro j
  induction j with
  | zero => intro a; show (a.set! 0 key).size = a.size; simp
  | succ j ih =>
    intro a
    show (if a[j]! > key then insArr (a.set! (j + 1) a[j]!) key j
                         else a.set! (j + 1) key).size = a.size
    by_cases hgt : a[j]! > key
    · rw [if_pos hgt]
      rw [ih]
      simp
    · rw [if_neg hgt]
      simp

/-- The sorted prefix: after `insArr a (a[j]!) j` (the step in the outer loop),
    the first `j+1` elements of the result are sorted — provided they were sorted
    in `a` for the first `j` elements, and `j < a.size`. -/
theorem insArr_sorted_prefix (a : Array Int) (j : Nat) (hj : j < a.size)
    (hs : Sorted (a.toList.take j)) :
    Sorted ((insArr a a[j]! j).toList.take (j + 1)) := by
  -- By insArr_toList: (insArr a a[j]! j).toList = ins a[j]! (take j) ++ drop (j+1).
  -- Its take (j+1) = ins a[j]! (take j) since ins preserves length (= j+1).
  rw [insArr_toList a[j]! j a hj hs]
  -- Length of ins key (take j a) = (take j a).length + 1 ≥ j+1 (if length = j). take (j+1) of append.
  -- ins extends length by exactly 1.
  have hins_len : (ins a[j]! (a.toList.take j)).length = j + 1 := by
    -- ins key xs has length xs.length + 1. take j of a.toList has length min j a.size = j.
    have hlen_ins : ∀ (key : Int) (xs : List Int), (ins key xs).length = xs.length + 1 := by
      intro key xs
      induction xs with
      | nil => rfl
      | cons x xs' ih =>
        show (if key ≤ x then key :: x :: xs' else x :: ins key xs').length = (x :: xs').length + 1
        by_cases h : key ≤ x
        · rw [if_pos h]; rfl
        · rw [if_neg h]; show (ins key xs').length + 1 = xs'.length + 1 + 1; rw [ih]
    rw [hlen_ins]
    have : (a.toList.take j).length = j := by
      rw [List.length_take, Array.length_toList]
      omega
    omega
  -- take (j+1) of (ins ... ++ drop (j+1)) is ins ... (its length is j+1 ≤ j+1).
  rw [List.take_append_of_le_length (Nat.le_of_eq hins_len.symm)]
  rw [List.take_of_length_le (Nat.le_of_eq hins_len)]
  -- Now goal: Sorted (ins a[j]! (a.toList.take j)). Use ins_sorted.
  exact ins_sorted a[j]! (a.toList.take j) hs

/-- The suffix past `j+1` in `insArr a key j` equals the same suffix in `a`,
    under the preconditions of the bridge. -/
theorem insArr_drop (a : Array Int) (j : Nat) (hj : j < a.size)
    (hs : Sorted (a.toList.take j)) (key : Int) :
    (insArr a key j).toList.drop (j + 1) = a.toList.drop (j + 1) := by
  rw [insArr_toList key j a hj hs]
  -- drop (j+1) of (ins key (take j) ++ drop (j+1) a) = drop (j+1 - (ins ..).length) of drop a if (ins..).length ≤ j+1, else...
  -- ins key (take j) has length j+1 (computed in insArr_sorted_prefix). drop (j+1) of a list of length j+1 ++ rest = rest.
  have hins_len : (ins a[j]! (a.toList.take j)).length = j + 1 := by
    have hlen_ins : ∀ (key : Int) (xs : List Int), (ins key xs).length = xs.length + 1 := by
      intro key xs
      induction xs with
      | nil => rfl
      | cons x xs' ih =>
        show (if key ≤ x then key :: x :: xs' else x :: ins key xs').length = (x :: xs').length + 1
        by_cases h : key ≤ x
        · rw [if_pos h]; rfl
        · rw [if_neg h]; show (ins key xs').length + 1 = xs'.length + 1 + 1; rw [ih]
    rw [hlen_ins]
    have : (a.toList.take j).length = j := by
      rw [List.length_take, Array.length_toList]; omega
    omega
  -- Need same for (ins key ...), not just ins a[j]! ... Do it parametrically.
  have hins_len_k : (ins key (a.toList.take j)).length = j + 1 := by
    have hlen_ins : ∀ (k : Int) (xs : List Int), (ins k xs).length = xs.length + 1 := by
      intro k xs
      induction xs with
      | nil => rfl
      | cons x xs' ih =>
        show (if k ≤ x then k :: x :: xs' else x :: ins k xs').length = (x :: xs').length + 1
        by_cases h : k ≤ x
        · rw [if_pos h]; rfl
        · rw [if_neg h]; show (ins k xs').length + 1 = xs'.length + 1 + 1; rw [ih]
    rw [hlen_ins]
    have : (a.toList.take j).length = j := by
      rw [List.length_take, Array.length_toList]; omega
    omega
  rw [List.drop_append_of_le_length (Nat.le_of_eq hins_len_k.symm)]
  rw [List.drop_eq_nil_of_le (Nat.le_of_eq hins_len_k)]
  rw [List.nil_append]

/-- `insArr a a[j]! j` permutes `a`'s toList — the key step for chaining Perm
    through the outer loop. -/
theorem insArr_perm (a : Array Int) (j : Nat) (hj : j < a.size)
    (hs : Sorted (a.toList.take j)) :
    (insArr a a[j]! j).toList.Perm a.toList := by
  rw [insArr_toList a[j]! j a hj hs]
  -- Goal: (ins a[j]! (take j) ++ drop (j+1)).Perm a.toList.
  -- ins a[j]! (take j) is a permutation of (a[j]! :: take j) by ins_perm.
  -- We want (ins ... ++ drop (j+1)).Perm (take j ++ [a[j]!] ++ drop (j+1)).
  -- And (take j ++ [a[j]!] ++ drop (j+1)) = take (j+1) ++ drop (j+1) = a.toList.
  have hj_len : j < a.toList.length := by rw [Array.length_toList]; exact hj
  have haj : a[j]! = a.toList[j] := by
    rw [show a[j]! = a[j]'hj from getElem!_pos a j hj]; rfl
  -- Step 1: ins a[j]! (take j) ~ a[j]! :: take j.
  have hp1 : (ins a[j]! (a.toList.take j)).Perm (a[j]! :: a.toList.take j) :=
    ins_perm a[j]! (a.toList.take j)
  -- Step 2: (a[j]! :: take j) ~ (take j ++ [a[j]!]).
  have hp2 : (a[j]! :: a.toList.take j).Perm (a.toList.take j ++ [a[j]!]) := by
    have : a[j]! :: a.toList.take j = [a[j]!] ++ a.toList.take j := rfl
    rw [this]
    exact List.perm_append_comm
  -- Chain 1+2: ins a[j]! (take j) ~ take j ++ [a[j]!]
  have hp12 : (ins a[j]! (a.toList.take j)).Perm (a.toList.take j ++ [a[j]!]) :=
    hp1.trans hp2
  -- Append drop (j+1) on both sides.
  have hp3 : (ins a[j]! (a.toList.take j) ++ a.toList.drop (j + 1)).Perm
               (a.toList.take j ++ [a[j]!] ++ a.toList.drop (j + 1)) :=
    hp12.append_right _
  -- Final: a.toList.take j ++ [a[j]!] ++ a.toList.drop (j+1) = a.toList.
  have heq : a.toList.take j ++ [a[j]!] ++ a.toList.drop (j + 1) = a.toList := by
    rw [haj]
    rw [List.append_assoc]
    show a.toList.take j ++ (a.toList[j] :: a.toList.drop (j + 1)) = a.toList
    rw [← List.drop_eq_getElem_cons hj_len]
    exact List.take_append_drop j a.toList
  rw [heq] at hp3
  exact hp3

/-- Outer-loop invariant: `sortArrFrom a i n` preserves size and suffix past `n`,
    is a permutation, and sorts the prefix up to `n` — provided the first `i`
    elements of `a` are already sorted, and `i ≤ n ≤ a.size`. -/
theorem sortArrFrom_spec (a : Array Int) (i n : Nat)
    (hi_le_n : i ≤ n) (hn_le_size : n ≤ a.size)
    (hs : Sorted (a.toList.take i)) :
    Sorted ((sortArrFrom a i n).toList.take n)
    ∧ (sortArrFrom a i n).toList.Perm a.toList
    ∧ (sortArrFrom a i n).toList.drop n = a.toList.drop n
    ∧ (sortArrFrom a i n).size = a.size := by
  -- Well-founded induction on n - i.
  induction h_gap : n - i using Nat.strongRecOn generalizing a i with
  | _ gap ih =>
    by_cases h : i < n
    · -- Step case.
      rw [sortArrFrom]
      rw [dif_pos h]
      have hi_lt_size : i < a.size := Nat.lt_of_lt_of_le h hn_le_size
      -- Produce updated invariants for the recursive call.
      -- Let b = insArr a a[i]! i.
      have hsize_b : (insArr a a[i]! i).size = a.size := insArr_size a[i]! i a
      have hi1_le_n : i + 1 ≤ n := h
      have hn_le_bsize : n ≤ (insArr a a[i]! i).size := by rw [hsize_b]; exact hn_le_size
      have hs_b_take : Sorted ((insArr a a[i]! i).toList.take (i + 1)) :=
        insArr_sorted_prefix a i hi_lt_size hs
      -- Gap decreases: n - (i+1) < n - i.
      have hgap' : n - (i + 1) < gap := by
        have : n - (i + 1) < n - i := Nat.sub_succ_lt_self _ _ h
        omega
      -- Apply IH at i+1.
      have ih_b := ih _ hgap' (insArr a a[i]! i) (i + 1) hi1_le_n hn_le_bsize hs_b_take rfl
      obtain ⟨hs_res, hperm_res, hdrop_res, hsize_res⟩ := ih_b
      refine ⟨hs_res, ?_, ?_, ?_⟩
      · -- Permutation chain.
        have hperm_step : (insArr a a[i]! i).toList.Perm a.toList := insArr_perm a i hi_lt_size hs
        exact hperm_res.trans hperm_step
      · -- Drop n unchanged.
        rw [hdrop_res]
        -- Show (insArr a a[i]! i).toList.drop n = a.toList.drop n.
        have hdrop_step := insArr_drop a i hi_lt_size hs a[i]!
        -- hdrop_step: drop (i+1) (insArr ...) = drop (i+1) a.toList
        -- Goal: drop n (insArr ...) = drop n a.toList
        -- Apply (List.drop (n-(i+1))) to both sides of hdrop_step, then use drop_drop.
        show List.drop n (insArr a a[i]! i).toList = List.drop n a.toList
        have h1 := congrArg (List.drop (n - (i + 1))) hdrop_step
        -- h1 : drop (n-(i+1)) (drop (i+1) b) = drop (n-(i+1)) (drop (i+1) a)
        simp only [List.drop_drop] at h1
        -- h1 : drop (i+1 + (n-(i+1))) b = drop (i+1 + (n-(i+1))) a
        have heq : i + 1 + (n - (i + 1)) = n := by omega
        rwa [heq] at h1
      · -- Size.
        rw [hsize_res, hsize_b]
    · -- Base case: ¬ i < n, so i = n; sortArrFrom returns a.
      rw [sortArrFrom]
      rw [dif_neg h]
      have hi_eq_n : i = n := Nat.le_antisymm hi_le_n (Nat.not_lt.mp h)
      refine ⟨?_, List.Perm.refl _, rfl, rfl⟩
      -- Goal: Sorted (a.toList.take n). Since i = n, hs : Sorted (a.toList.take i) = Sorted (a.toList.take n).
      rw [← hi_eq_n]; exact hs

/-- Helper: `Sorted (a.toList.take 1)` for any nonempty array. -/
private theorem sorted_take_one (a : Array Int) (h : 1 ≤ a.size) :
    Sorted (a.toList.take 1) := by
  have hlen : 0 < a.toList.length := by rw [Array.length_toList]; omega
  cases hl : a.toList with
  | nil => exfalso; rw [hl] at hlen; simp at hlen
  | cons hd tl => exact Sorted.singleton hd

/-- ★ The imperative `sortArr` produces a sorted list. -/
theorem sortArr_sorted (a : Array Int) : Sorted (sortArr a).toList := by
  show Sorted (sortArrFrom a 1 a.size).toList
  by_cases h1 : 1 ≤ a.size
  · -- a.size ≥ 1: invoke the spec.
    obtain ⟨hs_res, _, _, hsize_eq⟩ :=
      sortArrFrom_spec a 1 a.size h1 (Nat.le_refl _) (sorted_take_one a h1)
    -- hs_res: Sorted (result.toList.take a.size). Since result.size = a.size, take = whole list.
    have hlen : (sortArrFrom a 1 a.size).toList.length = a.size := by
      rw [Array.length_toList]; exact hsize_eq
    rw [← List.take_of_length_le (Nat.le_of_eq hlen)]
    exact hs_res
  · -- a.size = 0: sortArrFrom a 1 0 returns a immediately; a.toList = [].
    have hsz : a.size = 0 := by omega
    have hnil : a.toList = [] := List.eq_nil_of_length_eq_zero (by rw [Array.length_toList, hsz])
    have : ¬ (1 < a.size) := by omega
    rw [sortArrFrom, dif_neg this, hnil]
    exact Sorted.nil

/-- ★ The imperative `sortArr` produces a permutation of its input. -/
theorem sortArr_perm (a : Array Int) : (sortArr a).toList.Perm a.toList := by
  show (sortArrFrom a 1 a.size).toList.Perm a.toList
  by_cases h1 : 1 ≤ a.size
  · obtain ⟨_, hperm, _, _⟩ :=
      sortArrFrom_spec a 1 a.size h1 (Nat.le_refl _) (sorted_take_one a h1)
    exact hperm
  · have : ¬ (1 < a.size) := by omega
    rw [sortArrFrom, dif_neg this]

/-- ★ Full correctness of the imperative `sortArr`. -/
theorem sortArr_correct (a : Array Int) :
    Sorted (sortArr a).toList ∧ (sortArr a).toList.Perm a.toList :=
  ⟨sortArr_sorted a, sortArr_perm a⟩

end SortDemo
