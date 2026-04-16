/-
  Cellular Flows — Route Subroutine Proofs (1D Line, Failure-Free)
  =================================================================

  This module proves invariants about the failure-free routing transition
  system `routeFFTS` defined in `Route.lean`. The system models Bellman-Ford
  distance-vector routing on a 1D line of N cells with target at cell 0.

  Paper reference: Lemma 6, Section 3.3.1.

  THEOREMS PROVED
    1. targetCorrect — target cell invariant (inductive + lifted)
    2. distLowerBound — distances never underestimate (inductive invariant)
    3. route_convergence — after k rounds, cells 0..k have correct dist
       (Lemma 6 from the paper)
-/
import VerifDemo.CellularFlows.Route

namespace CellularFlows

/- ------------------------------------------------------------------- -/
/- Target correctness invariant                                        -/

def targetCorrect {n : Nat} (s : RouteState n) : Prop :=
  (∀ i : Fin n, i.val = 0 → s.dist i = .fin 0) ∧
  (∀ i : Fin n, i.val = 0 → s.next i = none) ∧
  (∀ i : Fin n, s.failed i = false)

theorem targetCorrect_init (n : Nat) :
    ∀ s, (routeFFTS n).init s → targetCorrect s := by
  intro s ⟨hdist0, _hdistNon0, hnext, hfailed⟩
  exact ⟨hdist0, fun i hi => hnext i, hfailed⟩

theorem targetCorrect_step (n : Nat) :
    ∀ s s', targetCorrect s → (routeFFTS n).next s s' → targetCorrect s' := by
  intro s s' _htc ⟨hfailed', htarget, _hothers⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i hi; exact (htarget i hi).1
  · intro i hi; exact (htarget i hi).2
  · exact hfailed'

theorem targetCorrect_inductive (n : Nat) :
    InductiveInvariant (routeFFTS n) targetCorrect :=
  ⟨targetCorrect_init n, targetCorrect_step n⟩

theorem targetCorrect_invariant (n : Nat) :
    Invariant (routeFFTS n) (fun s => targetCorrect s) :=
  inductive_invariant_holds (routeFFTS n) targetCorrect (targetCorrect_inductive n)

/- ------------------------------------------------------------------- -/
/- ReachableInK and reachableInK_reachable are now in TransitionSystem.lean -/

/- ------------------------------------------------------------------- -/
/- DistVal helpers                                                     -/

theorem DistVal.dmin_inf_right (a : DistVal) : DistVal.dmin a .inf = a := by
  cases a with | fin _ => rfl | inf => rfl

theorem DistVal.dmin_inf_left (a : DistVal) : DistVal.dmin .inf a = a := by
  cases a with | fin _ => rfl | inf => rfl

theorem DistVal.succ_fin (m : Nat) : DistVal.succ (.fin m) = .fin (m + 1) := rfl
theorem DistVal.succ_inf : DistVal.succ .inf = .inf := rfl

/-- dmin of two fin values: the result is .fin of at most the minimum argument. -/
theorem DistVal.dmin_fin_fin_eq (a b : Nat) :
    DistVal.dmin (.fin a) (.fin b) = .fin (Nat.min a b) := rfl

/-- If dmin of two fin values = .fin m, then m <= a and m <= b. -/
theorem DistVal.dmin_fin_le {a b m : Nat}
    (h : DistVal.dmin (.fin a) (.fin b) = .fin m) : m ≤ a ∧ m ≤ b := by
  rw [DistVal.dmin_fin_fin_eq] at h; cases h
  exact ⟨Nat.min_le_left a b, Nat.min_le_right a b⟩

/-- If dmin (.fin a) x = .fin m, then m <= a. -/
theorem DistVal.dmin_fin_left_le {a : Nat} {x : DistVal} {m : Nat}
    (h : DistVal.dmin (.fin a) x = .fin m) : m ≤ a := by
  cases x with
  | inf => simp [DistVal.dmin] at h; omega
  | fin b => exact (DistVal.dmin_fin_le h).1

/- ------------------------------------------------------------------- -/
/- Topology lemmas                                                     -/

theorem neighbors1D_interior {n : Nat} (i : Fin n)
    (hpos : i.val > 0) (hlt : i.val + 1 < n) :
    neighbors1D i = [⟨i.val - 1, by omega⟩, ⟨i.val + 1, hlt⟩] := by
  simp [neighbors1D, leftNeighbor, rightNeighbor, hpos, hlt]

theorem neighbors1D_last {n : Nat} (i : Fin n)
    (hpos : i.val > 0) (hlast : ¬(i.val + 1 < n)) :
    neighbors1D i = [⟨i.val - 1, by omega⟩] := by
  simp [neighbors1D, leftNeighbor, rightNeighbor, hpos, hlast]

/- ------------------------------------------------------------------- -/
/- minDist lemmas                                                      -/

theorem minDist_singleton {n : Nat} (dist : Fin n → DistVal) (j : Fin n) :
    minDist dist [j] = dist j := rfl

theorem minDist_pair {n : Nat} (dist : Fin n → DistVal) (j k : Fin n) :
    minDist dist [j, k] = DistVal.dmin (dist j) (dist k) := rfl

/- ------------------------------------------------------------------- -/
/- Distance lower bound                                                -/

/-- Every cell's distance is at least its true shortest-path distance. -/
def distLowerBound {n : Nat} (s : RouteState n) : Prop :=
  ∀ i : Fin n, ∀ m : Nat, s.dist i = .fin m → m ≥ i.val

theorem distLowerBound_init (n : Nat) :
    ∀ s, (routeFFTS n).init s → distLowerBound s := by
  intro s ⟨hdist0, hdistNon0, _, _⟩
  intro i m hm
  by_cases hi : i.val = 0
  · rw [hdist0 i hi] at hm; cases hm; omega
  · rw [hdistNon0 i hi] at hm; cases hm

/-- Helper: for a pair of .fin neighbors, minDist = .fin m implies
    m >= minimum of their lower bounds. We state this directly with
    the Prop-valued lower bound to avoid Nat.min in conclusions. -/
private theorem minDist_pair_ge {n : Nat} (dist : Fin n → DistVal)
    (j k : Fin n) (bound : Nat)
    (hlb : ∀ i : Fin n, ∀ mv : Nat, dist i = .fin mv → mv ≥ i.val)
    (hjb : j.val ≥ bound) (hkb : k.val ≥ bound)
    (m : Nat) (hm : minDist dist [j, k] = .fin m) : m ≥ bound := by
  simp only [minDist] at hm
  cases hdj : dist j with
  | inf =>
    rw [hdj, DistVal.dmin_inf_left] at hm
    exact Nat.le_trans hkb (hlb k m hm)
  | fin mj =>
    cases hdk : dist k with
    | inf =>
      rw [hdj, hdk, DistVal.dmin_inf_right] at hm; cases hm
      exact Nat.le_trans hjb (hlb j m hdj)
    | fin mk =>
      rw [hdj, hdk, DistVal.dmin_fin_fin_eq] at hm
      cases hm
      have hmj_ge := hlb j mj hdj
      have hmk_ge := hlb k mk hdk
      simp [Nat.min_def]; split <;> omega

theorem distLowerBound_step (n : Nat) :
    ∀ s s', distLowerBound s → (routeFFTS n).next s s' → distLowerBound s' := by
  intro s s' hlb ⟨_, htarget, hothers⟩
  intro i m hm
  by_cases hiz : i.val = 0
  · rw [(htarget i hiz).1] at hm; cases hm; omega
  · have hipos : i.val > 0 := by omega
    have hstep_i := hothers i hiz
    rw [hstep_i.1] at hm
    cases hmd : minDist s.dist (neighbors1D i) with
    | inf => rw [hmd, DistVal.succ_inf] at hm; cases hm
    | fin md =>
      rw [hmd, DistVal.succ_fin] at hm; cases hm
      -- Need: md + 1 >= i.val, i.e., md >= i.val - 1
      suffices h : md ≥ i.val - 1 by omega
      by_cases hright : i.val + 1 < n
      · -- Interior: neighbors = [i-1, i+1], both have index >= i-1
        rw [neighbors1D_interior i hipos hright] at hmd
        exact minDist_pair_ge s.dist _ _ (i.val - 1) hlb (by simp) (by simp; omega) md hmd
      · -- Last: neighbors = [i-1]
        rw [neighbors1D_last i hipos hright] at hmd
        simp [minDist] at hmd
        have := hlb _ md hmd; simp at this; omega

theorem distLowerBound_inductive (n : Nat) :
    InductiveInvariant (routeFFTS n) distLowerBound :=
  ⟨distLowerBound_init n, distLowerBound_step n⟩

theorem distLowerBound_invariant (n : Nat) :
    Invariant (routeFFTS n) distLowerBound :=
  inductive_invariant_holds (routeFFTS n) distLowerBound (distLowerBound_inductive n)

theorem distLowerBound_at_k (n : Nat) :
    ∀ k s, ReachableInK (routeFFTS n) k s → distLowerBound s := by
  intro k s hrk
  exact distLowerBound_invariant n s (reachableInK_reachable (routeFFTS n) k s hrk)

/- ------------------------------------------------------------------- -/
/- Route convergence (Lemma 6)                                         -/

/-- ★ After k rounds of failure-free Bellman-Ford on a 1D line of n >= 1
    cells with target at cell 0, every cell i with i.val <= k has
    dist i = .fin i.val. (Lemma 6, Johnson-Mitra 2015)

    Proof by induction on k. The key insight for the step case: cell i's
    left neighbor (i-1) has converged by IH, and the right neighbor
    (i+1) has dist >= i+1 by the lower bound invariant, so the min
    over neighbors equals i-1 and dist' i = i. -/
theorem route_convergence (n : Nat) (_hn : n > 0) :
    ∀ k : Nat, ∀ s : RouteState n,
      ReachableInK (routeFFTS n) k s →
      ∀ i : Fin n, i.val ≤ k → s.dist i = .fin i.val := by
  intro k
  induction k with
  | zero =>
    intro s hrk i hle
    have hi : i.val = 0 := by omega
    match hrk with
    | .init _ hinit =>
      obtain ⟨hdist0, _, _, _⟩ := hinit
      rw [hdist0 i hi]; congr 1; omega
  | succ k ih =>
    intro s' hrk i hle
    match hrk with
    | .step _ s _ hrk_s hstep =>
      obtain ⟨_, htarget, hothers⟩ := hstep
      by_cases hiz : i.val = 0
      · rw [(htarget i hiz).1]; congr 1; omega
      · have hipos : i.val > 0 := by omega
        have hstep_i := hothers i (by omega : i.val ≠ 0)
        rw [hstep_i.1]
        suffices hmid : minDist s.dist (neighbors1D i) = .fin (i.val - 1) by
          rw [hmid, DistVal.succ_fin]; congr 1; omega
        -- Left neighbor converged by IH
        have hleft_dist : s.dist ⟨i.val - 1, by omega⟩ = .fin (i.val - 1) := by
          have h := ih s hrk_s ⟨i.val - 1, by omega⟩ (by simp; omega)
          simp at h; exact h
        -- Lower bound from inductive invariant
        have hlb := distLowerBound_at_k n k s hrk_s
        by_cases hright : i.val + 1 < n
        · -- Interior: neighbors = [i-1, i+1]
          rw [neighbors1D_interior i hipos hright, minDist_pair, hleft_dist]
          -- Goal: dmin (.fin (i.val-1)) (s.dist ⟨i+1,_⟩) = .fin (i.val-1)
          cases hdr : s.dist ⟨i.val + 1, hright⟩ with
          | inf =>
            -- dmin (.fin x) .inf = .fin x
            exact DistVal.dmin_inf_right _
          | fin m =>
            -- m >= i+1 by lower bound, so min(i-1, m) = i-1
            have hge : m ≥ i.val + 1 := by
              have := hlb ⟨i.val + 1, hright⟩ m hdr; simp at this; exact this
            rw [DistVal.dmin_fin_fin_eq]; congr 1; simp [Nat.min_def]; omega
        · -- Last: neighbors = [i-1]
          rw [neighbors1D_last i hipos hright, minDist_singleton, hleft_dist]

/- ------------------------------------------------------------------- -/
/- argminDist lemmas                                                   -/

/-- argminDist on a singleton with finite dist returns that element. -/
theorem argminDist_singleton_fin {n : Nat} (dist : Fin n → DistVal) (j : Fin n)
    (m : Nat) (hd : dist j = .fin m) :
    argminDist dist [j] = some j := by
  simp [argminDist, hd]

/-- argminDist on a pair [j, k] where dist j = .fin a and dist k = .fin b
    with a ≤ b returns some j (the first/left element). -/
theorem argminDist_pair_left_le {n : Nat} (dist : Fin n → DistVal) (j k : Fin n)
    (a b : Nat) (hdj : dist j = .fin a) (hdk : dist k = .fin b) (hab : a ≤ b) :
    argminDist dist [j, k] = some j := by
  simp [argminDist, hdk, hdj, DistVal.dle, hab]

/-- argminDist on a pair [j, k] where dist j = .fin a and dist k = .inf
    returns some j. -/
theorem argminDist_pair_left_inf {n : Nat} (dist : Fin n → DistVal) (j k : Fin n)
    (a : Nat) (hdj : dist j = .fin a) (hdk : dist k = .inf) :
    argminDist dist [j, k] = some j := by
  simp [argminDist, hdk, hdj]

/- ------------------------------------------------------------------- -/
/- Next-hop convergence (Corollary 7)                                  -/

/-- ★ After k rounds of failure-free Bellman-Ford on a 1D line of n >= 1
    cells with target at cell 0, every cell i with 0 < i ≤ k has its
    next-hop set to the left neighbor (cell i-1).

    Proof by k-induction. At step k+1, the step relation sets
    next' i = argminDist s.dist (neighbors1D i) where s is the step-k
    predecessor. By route_convergence on s, the left neighbor (i-1) has
    dist = fin(i-1), while the right neighbor (i+1) has dist >= fin(i+1)
    or inf by distLowerBound. Since i-1 < i+1, argminDist picks the
    left neighbor. -/
theorem next_convergence (n : Nat) (hn : n > 0) :
    ∀ k : Nat, ∀ s : RouteState n,
      ReachableInK (routeFFTS n) k s →
      ∀ i : Fin n, i.val > 0 → i.val ≤ k →
        s.next i = some ⟨i.val - 1, by omega⟩ := by
  intro k
  induction k with
  | zero =>
    -- Base case: i > 0 and i ≤ 0 is impossible
    intro s _hrk i hipos hle
    omega
  | succ k _ih =>
    intro s' hrk i hipos hle
    match hrk with
    | .step _ s _ hrk_s hstep =>
      obtain ⟨_, htarget, hothers⟩ := hstep
      -- Since i > 0, i is not the target
      have hiz : i.val ≠ 0 := by omega
      have hstep_i := hothers i hiz
      -- s'.next i = argminDist s.dist (neighbors1D i)
      rw [hstep_i.2]
      -- Left neighbor dist from route_convergence on the predecessor
      -- i - 1 ≤ k because i ≤ k + 1
      have hleft_dist : s.dist ⟨i.val - 1, by omega⟩ = .fin (i.val - 1) := by
        have h := route_convergence n hn k s hrk_s ⟨i.val - 1, by omega⟩ (by simp; omega)
        simp at h; exact h
      -- Lower bound on the predecessor state
      have hlb := distLowerBound_at_k n k s hrk_s
      by_cases hright : i.val + 1 < n
      · -- Interior: neighbors = [i-1, i+1]
        rw [neighbors1D_interior i hipos hright]
        cases hdr : s.dist ⟨i.val + 1, hright⟩ with
        | inf =>
          exact argminDist_pair_left_inf s.dist _ _ (i.val - 1) hleft_dist hdr
        | fin m =>
          have hge : m ≥ i.val + 1 := by
            have := hlb ⟨i.val + 1, hright⟩ m hdr; simp at this; exact this
          exact argminDist_pair_left_le s.dist _ _ (i.val - 1) m hleft_dist hdr (by omega)
      · -- Last cell: neighbors = [i-1]
        rw [neighbors1D_last i hipos hright]
        exact argminDist_singleton_fin s.dist _ (i.val - 1) hleft_dist

/- ------------------------------------------------------------------- -/
/- Distance is inf beyond wave front                                   -/

/-- argminDist on a singleton with inf dist returns none. -/
theorem argminDist_singleton_inf {n : Nat} (dist : Fin n → DistVal) (j : Fin n)
    (hd : dist j = .inf) :
    argminDist dist [j] = none := by
  simp [argminDist, hd]

/-- argminDist on a pair with both inf returns none. -/
theorem argminDist_pair_inf_inf {n : Nat} (dist : Fin n → DistVal) (j k : Fin n)
    (hdj : dist j = .inf) (hdk : dist k = .inf) :
    argminDist dist [j, k] = none := by
  simp [argminDist, hdk, hdj]

/-- ★ After k rounds, cells beyond the wave front have dist = inf.
    Combined with route_convergence, this fully characterizes the dist
    values: dist(i) = fin i for i ≤ k, and dist(i) = inf for i > k. -/
theorem dist_inf_beyond (n : Nat) (_hn : n > 0) :
    ∀ k : Nat, ∀ s : RouteState n,
      ReachableInK (routeFFTS n) k s →
      ∀ i : Fin n, i.val > k → s.dist i = .inf := by
  intro k
  induction k with
  | zero =>
    intro s hrk i hik
    match hrk with
    | .init _ hinit =>
      obtain ⟨_, hdistNon0, _, _⟩ := hinit
      exact hdistNon0 i (by omega)
  | succ k ih =>
    intro s' hrk i hik
    match hrk with
    | .step _ s _ hrk_s hstep =>
      obtain ⟨_, htarget, hothers⟩ := hstep
      have hiz : i.val ≠ 0 := by omega
      have hstep_i := hothers i hiz
      rw [hstep_i.1]
      -- Need: minDist s.dist (neighbors1D i) = .inf
      -- All neighbors of i have index > k or at most... Let's check.
      -- i > k+1, so i ≥ k+2. Left neighbor = i-1 ≥ k+1 > k. Right = i+1 > k.
      have hipos : i.val > 0 := by omega
      have hleft_inf : s.dist ⟨i.val - 1, by omega⟩ = .inf := by
        exact ih s hrk_s ⟨i.val - 1, by omega⟩ (by simp; omega)
      by_cases hright : i.val + 1 < n
      · rw [neighbors1D_interior i hipos hright, minDist_pair, hleft_inf]
        have hright_inf : s.dist ⟨i.val + 1, hright⟩ = .inf := by
          exact ih s hrk_s ⟨i.val + 1, hright⟩ (by simp; omega)
        rw [hright_inf]
        rfl
      · rw [neighbors1D_last i hipos hright, minDist_singleton, hleft_inf]
        rfl

/- ------------------------------------------------------------------- -/
/- Next-hop always points left or is none                              -/

/-- ★ In any k-step reachable state of routeFFTS, every cell's next-hop
    either points to its left neighbor or is none.
    This is the key structural property of 1D Bellman-Ford routing. -/
theorem next_left_or_none (n : Nat) (hn : n > 0) :
    ∀ k : Nat, ∀ s : RouteState n,
      ReachableInK (routeFFTS n) k s →
      ∀ i : Fin n, s.next i = none ∨
        (i.val > 0 ∧ s.next i = some ⟨i.val - 1, by omega⟩) := by
  intro k
  induction k with
  | zero =>
    intro s hrk i
    match hrk with
    | .init _ hinit =>
      obtain ⟨_, _, hnext, _⟩ := hinit
      left; exact hnext i
  | succ k _ih =>
    intro s' hrk i
    match hrk with
    | .step _ s _ hrk_s hstep =>
      obtain ⟨_, htarget, hothers⟩ := hstep
      by_cases hiz : i.val = 0
      · left; exact (htarget i hiz).2
      · have hipos : i.val > 0 := by omega
        have hstep_i := hothers i hiz
        -- s'.next i = argminDist s.dist (neighbors1D i)
        -- We show argminDist picks left or returns none
        have hlb := distLowerBound_at_k n k s hrk_s
        by_cases hconv : i.val - 1 ≤ k
        · -- Left neighbor has converged
          have hleft_dist : s.dist ⟨i.val - 1, by omega⟩ = .fin (i.val - 1) := by
            have h := route_convergence n hn k s hrk_s ⟨i.val - 1, by omega⟩ (by simp; omega)
            simp at h; exact h
          right
          constructor
          · exact hipos
          · rw [hstep_i.2]
            by_cases hright : i.val + 1 < n
            · rw [neighbors1D_interior i hipos hright]
              cases hdr : s.dist ⟨i.val + 1, hright⟩ with
              | inf => exact argminDist_pair_left_inf s.dist _ _ (i.val - 1) hleft_dist hdr
              | fin m =>
                have hge : m ≥ i.val + 1 := by
                  have := hlb ⟨i.val + 1, hright⟩ m hdr; simp at this; exact this
                exact argminDist_pair_left_le s.dist _ _ (i.val - 1) m hleft_dist hdr (by omega)
            · rw [neighbors1D_last i hipos hright]
              exact argminDist_singleton_fin s.dist _ (i.val - 1) hleft_dist
        · -- Left neighbor has NOT converged (i-1 > k), so i > k+1
          -- All neighbors have inf dist
          have hleft_inf : s.dist ⟨i.val - 1, by omega⟩ = .inf := by
            exact dist_inf_beyond n hn k s hrk_s ⟨i.val - 1, by omega⟩ (by simp; omega)
          left
          rw [hstep_i.2]
          by_cases hright : i.val + 1 < n
          · rw [neighbors1D_interior i hipos hright]
            have hright_inf : s.dist ⟨i.val + 1, hright⟩ = .inf := by
              exact dist_inf_beyond n hn k s hrk_s ⟨i.val + 1, hright⟩ (by simp; omega)
            exact argminDist_pair_inf_inf s.dist _ _ hleft_inf hright_inf
          · rw [neighbors1D_last i hipos hright]
            exact argminDist_singleton_inf s.dist _ hleft_inf

/-- ★ No mutual next-hops in routeFFTS: if next i = some j, then
    next j ≠ some i. This follows from next_left_or_none: all
    next-hops point left, so two cells cannot point at each other. -/
theorem noMutualNextHop_routeFFTS (n : Nat) (hn : n > 0) :
    ∀ k : Nat, ∀ s : RouteState n,
      ReachableInK (routeFFTS n) k s →
      ∀ i j : Fin n, s.next i = some j → s.next j ≠ some i := by
  intro k s hrk i j hnij hnji
  -- By next_left_or_none, next i = some j means j = i-1 and i > 0
  rcases next_left_or_none n hn k s hrk i with hnone | ⟨hipos, hleft⟩
  · -- next i = none contradicts next i = some j
    rw [hnone] at hnij; cases hnij
  · -- next i = some ⟨i-1,_⟩ = some j, so j.val = i.val - 1
    rw [hleft] at hnij
    have hjeq : j = ⟨i.val - 1, by omega⟩ := Option.some.inj hnij.symm
    -- By next_left_or_none, next j = some i means i = j-1 and j > 0
    rcases next_left_or_none n hn k s hrk j with hnone_j | ⟨_hjpos, hleft_j⟩
    · rw [hnone_j] at hnji; cases hnji
    · rw [hleft_j] at hnji
      have hieq : i = ⟨j.val - 1, by omega⟩ := Option.some.inj hnji.symm
      -- j.val = i.val - 1 and i.val = j.val - 1
      -- So i.val = (i.val - 1) - 1, contradiction for i.val > 0
      have hj_val : j.val = i.val - 1 := by
        subst hjeq; simp
      have hi_val : i.val = j.val - 1 := by
        have := congrArg Fin.val hieq; simp at this; exact this
      omega

end CellularFlows
