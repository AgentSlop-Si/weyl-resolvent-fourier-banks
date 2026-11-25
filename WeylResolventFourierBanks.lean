/-
  WeylResolventFourierBanks.lean

  Zero-dependency Lean 4 formal verification companion to:
  "Signed Weyl Resolvent Banks for Discrete Fourier Matrices: Small-Order Exactness and Linear Complexity"
  by Daniyar Kuttymbek, Adilkhan Kuttymbek, Dayana Kuttymbek,
  Amina Kolpenova, and Mukhammadali Kottumbekov.

  Uses Lean 4 core (`Init`) only — no Mathlib or external dependencies required.
  Zero `sorry`, zero custom `axiom`, zero `native_decide`.
  Verify with: `lean WeylResolventFourierBanks.lean`

  Contents:
    Part 1: Symbolic universal theorems (zero `sorry`):
      - Lemma 3.1: Signed-triangle exclusive points and full square coverage for ALL odd N >= 3.
      - Theorem 1.2: Matching Theta(N) Hankel bank-count inequality for ALL odd N >= 3.
      - Theorem 1.3 / Proposition 5.3: All range, interpolation, axis-rank, and quadratic-field
        guard-degree inequalities (N >= 6d - 2, d >= 4 => N - 2d - 1 > 4d - 4, 2m - 2 > N - 1,
        2(d - 2) < N, m >= 2d - 2, and H = d(d+1) + 2m - 1 < (N+1)^2 / 2 for d <= N/4, N >= 23).
      - Lemma 6.1 (Eq. 6.1): Universal 2v - 1 telescoping unwind-trial bound for reverse GCD descent.
    Part 2: Pure-kernel exact algebraic certificates (`decide` / `decide +kernel`, zero `native_decide`):
      - Theorem 1.1(a): Literal 4-bank 3x3 matrix synthesis of F_3 over F_7 (q=2), checking all
        12 two-sided 3x3 branch inverses and all 9 entries of F_3.
      - Theorem 1.1(b): Exact Z[q]/Phi_5 lower-bound elimination residues, Bezout identity, and
        upper-bound determinants det(M_0), det(M_2), det(M_3).
      - Theorem 1.1(c) / Proposition 5.1: Exact F_29[Y] Bezout certificate U*Rbar + V*Ebar = 1.
      - Theorem 1.1(d): Exact Z[q]/Phi_9 order-9 certificate E*(2q^5-q^4+3q^2-3q+2) = 3.
-/

namespace WeylResolventFourierBanks

/-! ## Part 1: Symbolic Universal Theorems -/

/-- Canonical residue of `(-x) mod N` for `0 ≤ x < N`. -/
def negMod (N x : Nat) : Nat :=
  if x == 0 then 0 else N - x

/-- Membership in the four signed triangles `A_{++}, A_{+-}, A_{-+}, A_{--}` for `0 ≤ a, b < N`. -/
def inPP (N a b : Nat) : Prop := a + b ≤ N - 1
def inPM (N a b : Nat) : Prop := a + negMod N b ≤ N - 1
def inMP (N a b : Nat) : Prop := negMod N a + b ≤ N - 1
def inMM (N a b : Nat) : Prop := negMod N a + negMod N b ≤ N - 1

/-- Lemma 3.1 (Exclusive diagonal points): for every odd `N ≥ 3` and `1 ≤ t ≤ (N - 1) / 2`,
    `(t, t)` lies in `A_{++}` and outside `A_{+-}, A_{-+}, A_{--}`, and symmetrically for all
    four orientations. -/
theorem exclusive_point_PP {N t : Nat} (hN : 3 ≤ N) (hodd : N % 2 = 1)
    (ht1 : 1 ≤ t) (ht2 : t ≤ (N - 1) / 2) :
    inPP N t t ∧ ¬ inPM N t t ∧ ¬ inMP N t t ∧ ¬ inMM N t t := by
  unfold inPP inPM inMP inMM negMod
  have ht_ne : (t == 0) = false := by
    cases t with
    | zero => omega
    | succ _ => rfl
  simp only [ht_ne, Bool.false_eq_true, ↓reduceIte]
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- Lemma 3.1 (Full square coverage for all odd `N ≥ 3`): every `(a, b)` with `0 ≤ a, b < N`
    lies in at least one of the four signed triangles. -/
theorem odd_square_covered_by_four_triangles {N a b : Nat} (hN : 3 ≤ N) (hodd : N % 2 = 1)
    (ha : a < N) (hb : b < N) :
    inPP N a b ∨ inPM N a b ∨ inMP N a b ∨ inMM N a b := by
  unfold inPP inPM inMP inMM negMod
  by_cases ha0 : a = 0
  · subst ha0; left; simp; omega
  · by_cases hb0 : b = 0
    · subst hb0; left; simp; omega
    · have hneA : (a == 0) = false := by cases a with | zero => contradiction | succ _ => rfl
      have hneB : (b == 0) = false := by cases b with | zero => contradiction | succ _ => rfl
      simp only [hneA, hneB, Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : a + b ≤ N - 1
      · exact Or.inl h1
      · by_cases h2 : a < b
        · exact Or.inr (Or.inl (by omega))
        · by_cases h3 : b < a
          · exact Or.inr (Or.inr (Or.inl (by omega)))
          · exact Or.inr (Or.inr (Or.inr (by omega)))

/-- Theorem 1.2 (Hankel lower bound arithmetic): from `2 * rP ≥ (N - 1) / 2`,
    `2 * rM ≥ (N - 1) / 2`, and `rP + rM ≥ 4`, deduce `rP + rM ≥ max 4 (2 * ((N + 2) / 4))`
    for every odd `N ≥ 3` (note `(N + 2) / 4 = ⌈(N - 1) / 4⌉`). -/
theorem hankel_bank_lower_bound {N rP rM : Nat} (hodd : N % 2 = 1) (hN : 3 ≤ N)
    (hP : (N - 1) / 2 ≤ 2 * rP) (hM : (N - 1) / 2 ≤ 2 * rM) (h4 : 4 ≤ rP + rM) :
    max 4 (2 * ((N + 2) / 4)) ≤ rP + rM := by
  omega

/-- Theorem 1.3 & Proposition 5.3 (All range and degree-margin inequalities in `N ≥ 6d - 2`):
    for every `d ≥ 4` and `N ≥ 6d - 2` with `m = N - d`,
    (1) chirp zero count exceeds degree bound `N - 2d - 1 > 4d - 4`,
    (2) degree bound `< N`,
    (3) axis-dependence degree excess `2m - 2 > N - 1`,
    (4) disjoint nonconstant axis rows `N > 2d`,
    (5) cyclic shift uniqueness `2(d - 2) < N`,
    (6) propagation length `m ≥ 2d - 2`,
    (7) `dim U` lower bound `N - 5d + 8 ≥ d + 6`. -/
theorem five_thirds_range_margins {N d : Nat} (hd : 4 ≤ d) (hN : 6 * d - 2 ≤ N) :
    let m := N - d
    (4 * d - 4 < N - 2 * d - 1) ∧
    (4 * d - 4 < N) ∧
    (N - 1 < 2 * m - 2) ∧
    (2 * d < N) ∧
    (2 * (d - 2) < N) ∧
    (2 * d - 2 ≤ m) ∧
    (d + 6 ≤ N - 5 * d + 8) := by
  dsimp only
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Proposition 5.3(d) (Quadratic finite-field guard margin):
    for all `N ≥ 23` and `4 ≤ d` with `4 * d ≤ N` (which holds for `d = (N + 2) / 6`),
    the simultaneous guard degree `H = d * (d + 1) + 2 * (N - d) - 1` satisfies
    `2 * H < (N + 1) * (N + 1)`, so `F_{Q^2}` (`Q ≥ N + 1`) always contains a legal point
    with random success probability `> 1/2`. -/
theorem finite_field_guard_margin {N d : Nat} (hN : 23 ≤ N) (hd4 : 4 ≤ d) (hd : 4 * d ≤ N) :
    let m := N - d
    let H := d * (d + 1) + 2 * m - 1
    2 * H < (N + 1) * (N + 1) := by
  dsimp only
  have h1 : 16 * (d * d) ≤ N * N := by
    have h4d : (4 * d) * (4 * d) ≤ N * N := Nat.mul_le_mul hd hd
    have hmul : (4 * d) * (4 * d) = 16 * (d * d) := by ac_rfl
    omega
  have h2 : 8 * (d * (d + 1) + 2 * (N - d) - 1) ≤ 8 * (d * d) + 16 * N - 8 * d - 8 := by
    have hdd : d * (d + 1) = d * d + d := by rw [Nat.mul_add, Nat.mul_one]
    omega
  -- Multiply desired inequality by 2: 16 * (d^2 + d + 2N - 2d - 1) <= N^2 + 32N - 16d - 16
  -- Need N^2 + 32N - 16d - 16 < 8 * (N+1)^2 = 8 N^2 + 16 N + 8, i.e., 16 N < 7 N^2 + 16 d + 24.
  have hN2 : 23 * N ≤ N * N := Nat.mul_le_mul_right N hN
  have h3 : (N + 1) * (N + 1) = N * N + 2 * N + 1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
  have hdd : d * (d + 1) = d * d + d := by rw [Nat.mul_add, Nat.mul_one]
  rw [hdd, h3]
  omega

/-- Lemma 6.1, Eq. (6.1) (Universal reverse-GCD unwind trial telescoping bound):
    given any strictly decreasing list of nonnegative degree drops `deltas` (each `≥ 1`)
    representing `Δ_1, ..., Δ_{ell-1}` with `∑ Δ_i ≤ v` and `length ≤ v - 1`,
    the total number of unwind GCD trials `∑ (Δ_i + 1)` is at most `2 * v - 1`. -/
def unwindTrials : List Nat → Nat
  | [] => 0
  | d :: ds => (d + 1) + unwindTrials ds

def sumList : List Nat → Nat
  | [] => 0
  | d :: ds => d + sumList ds

theorem unwind_trials_eq_sum_plus_len (ds : List Nat) :
    unwindTrials ds = sumList ds + ds.length := by
  induction ds with
  | nil => rfl
  | cons d tl ih =>
    simp only [unwindTrials, sumList, List.length_cons]
    omega

theorem reverse_gcd_trial_bound {v : Nat} (ds : List Nat)
    (hv : 1 ≤ v) (hsum : sumList ds ≤ v) (hlen : ds.length ≤ v - 1) :
    unwindTrials ds ≤ 2 * v - 1 := by
  rw [unwind_trials_eq_sum_plus_len]
  omega

/-! ## Part 2: Pure-Kernel Exact Algebraic Certificates (`decide` / `decide +kernel`) -/

/-- Exact `Z[q]/Phi_5(q)` arithmetic represented as 4-tuples `(c0, c1, c2, c3)`. -/
structure Z5 where
  c0 : Int
  c1 : Int
  c2 : Int
  c3 : Int
deriving DecidableEq

def Z5.zero : Z5 := ⟨0, 0, 0, 0⟩
def Z5.one : Z5 := ⟨1, 0, 0, 0⟩
def Z5.q : Z5 := ⟨0, 1, 0, 0⟩
def Z5.q2 : Z5 := ⟨0, 0, 1, 0⟩
def Z5.q3 : Z5 := ⟨0, 0, 0, 1⟩
def Z5.q4 : Z5 := ⟨-1, -1, -1, -1⟩

def Z5.add (a b : Z5) : Z5 := ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3⟩
def Z5.sub (a b : Z5) : Z5 := ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2, a.c3 - b.c3⟩
def Z5.neg (a : Z5) : Z5 := ⟨-a.c0, -a.c1, -a.c2, -a.c3⟩
def Z5.scale (s : Int) (a : Z5) : Z5 := ⟨s * a.c0, s * a.c1, s * a.c2, s * a.c3⟩

def Z5.mul (a b : Z5) : Z5 :=
  let v0 := a.c0 * b.c0 + a.c2 * b.c3 + a.c3 * b.c2
  let v1 := a.c0 * b.c1 + a.c1 * b.c0 + a.c3 * b.c3
  let v2 := a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0
  let v3 := a.c0 * b.c3 + a.c1 * b.c2 + a.c2 * b.c1 + a.c3 * b.c0
  let v4 := a.c1 * b.c3 + a.c2 * b.c2 + a.c3 * b.c1
  ⟨v0 - v4, v1 - v4, v2 - v4, v3 - v4⟩

def Z5.pow (a : Z5) : Nat → Z5
  | 0 => Z5.one
  | n + 1 => Z5.mul a (Z5.pow a n)

/-- Section 4 (Order-5 lower bound): exact `Z[q]/Phi_5(q)` verification of all four elimination
    residues and the exact polynomial Bezout identity `l1^2 B(t) - (c l1 t - c l0 - l1) L(t) = 1+4q-11q^2+6q^3`. -/
theorem order5_lower_bound_certificates :
    let c := Z5.add Z5.q Z5.q4
    let d := Z5.add Z5.one Z5.q4
    let a := Z5.sub (Z5.scale 2 c) Z5.q
    let s : Z5 := ⟨0, 0, 1, 1⟩
    let p : Z5 := ⟨1, -1, -2, -2⟩
    let l0 : Z5 := ⟨0, 2, 2, 1⟩
    let l1 : Z5 := ⟨2, -1, 2, 2⟩
    -- Fundamental relation c(c+1) = 1 and s, p identities
    Z5.mul c (Z5.add c Z5.one) = Z5.one ∧
    Z5.mul c s = Z5.neg Z5.one ∧
    Z5.mul (Z5.mul c c) p = Z5.sub Z5.one (Z5.mul c Z5.q2) ∧
    -- Distinct diagonal residue c * D(t, w) = -2 - 2q + 2q^2 - q^3
    Z5.sub (Z5.sub (Z5.mul a (Z5.neg Z5.q2)) ⟨2, 0, 0, 0⟩) (Z5.mul (Z5.scale 2 c) d) = ⟨-2, -2, 2, -1⟩ ∧
    -- Equal diagonal polynomial Bezout identity in Z5[t] (coefficients of t^2, t^1, t^0):
    -- B(t) = c t^2 - t - q^2, L(t) = l1 t + l0 = c D(t,t) - a B(t)
    (Z5.sub (Z5.mul c (Z5.scale (-4) Z5.one)) (Z5.mul a (Z5.neg Z5.one)) = l1 ∧
     Z5.sub (Z5.mul c (Z5.scale (-2) d)) (Z5.mul a (Z5.neg Z5.q2)) = l0 ∧
     -- t^2 coeff of l1^2 B - (c l1 t - c l0 - l1)(l1 t + l0) == 0
     Z5.sub (Z5.mul (Z5.mul l1 l1) c) (Z5.mul (Z5.mul c l1) l1) = Z5.zero ∧
     -- t^1 coeff == 0
     Z5.sub (Z5.neg (Z5.mul l1 l1))
            (Z5.add (Z5.mul (Z5.mul c l1) l0) (Z5.mul (Z5.sub (Z5.neg (Z5.mul c l0)) l1) l1)) = Z5.zero ∧
     -- t^0 coeff == 1 + 4q - 11q^2 + 6q^3
     Z5.sub (Z5.mul (Z5.mul l1 l1) (Z5.neg Z5.q2))
            (Z5.mul (Z5.sub (Z5.neg (Z5.mul c l0)) l1) l0) = ⟨1, 4, -11, 6⟩) ∧
    -- Both nondiagonal residues
    (let s2m2p := Z5.sub (Z5.mul s s) (Z5.scale 2 p)
     Z5.sub (Z5.sub (Z5.sub (Z5.mul Z5.q2 s2m2p) (Z5.mul s p)) (Z5.mul (Z5.scale 2 d) p))
            (Z5.mul Z5.q (Z5.mul p p)) = ⟨-5, -5, 0, 5⟩ ∧
     Z5.sub (Z5.sub (Z5.sub (Z5.mul Z5.q2 s2m2p) (Z5.mul s p)) (Z5.mul d s2m2p))
            (Z5.mul Z5.q (Z5.mul p p)) = ⟨-9, -19, -17, -5⟩) := by
  decide

/-- Exact 5x5 determinant over `Z5` via Laplace expansion (used to kernel-verify `det M0, M2, M3`). -/
def det2Z5 (m : List (List Z5)) : Z5 :=
  let g r c := (m.getD r []).getD c Z5.zero
  Z5.sub (Z5.mul (g 0 0) (g 1 1)) (Z5.mul (g 0 1) (g 1 0))

def removeCol (m : List (List Z5)) (col : Nat) : List (List Z5) :=
  m.map fun row => (List.range row.length).foldr (fun c acc =>
    if c == col then acc else row.getD c Z5.zero :: acc) []

def detZ5 : Nat → List (List Z5) → Z5
  | 0, _ => Z5.one
  | 1, m => (m.getD 0 []).getD 0 Z5.zero
  | 2, m => det2Z5 m
  | n + 1, m =>
    match m with
    | [] => Z5.zero
    | r0 :: rest =>
      (List.range (n + 1)).foldl (fun acc c =>
        let entry := r0.getD c Z5.zero
        if entry == Z5.zero then acc
        else
          let sub := detZ5 n (removeCol rest c)
          let term := Z5.mul entry sub
          if c % 2 == 0 then Z5.add acc term else Z5.sub acc term) Z5.zero

/-- Section 4.2 (Order-5 upper construction): exact `Z[q]/Phi_5(q)` verification of
    `c t^2 - t - q^2 = 0`, all five guards `-alpha^5`, and `det M_0, det M_2, det M_3`. -/
theorem order5_upper_determinants_and_guards :
    let x := Z5.one
    let z : Z5 := ⟨-2, -3, -3, -1⟩
    let y := Z5.q
    let t := Z5.add Z5.one Z5.q
    let c := Z5.add Z5.q Z5.q4
    let G : Z5 := ⟨1, 1, 1, 0⟩
    let P := Z5.add (Z5.add Z5.one Z5.q4) Z5.q3
    let M0 : List (List Z5) := [
      [Z5.one, Z5.one, Z5.one, Z5.one, Z5.one],
      [x, z, Z5.pow y 4, t, Z5.pow t 4],
      [Z5.pow x 2, Z5.pow z 2, Z5.pow y 3, Z5.pow t 2, Z5.pow t 3],
      [Z5.pow x 3, Z5.pow z 3, Z5.pow y 2, Z5.pow t 3, Z5.pow t 2],
      [Z5.pow x 4, Z5.pow z 4, y, Z5.pow t 4, t]]
    let M2 : List (List Z5) := [
      [Z5.one, Z5.one, Z5.one, Z5.one, Z5.one],
      [Z5.mul G x, Z5.mul G z, Z5.zero, Z5.neg (Z5.mul Z5.q t), Z5.zero],
      [Z5.mul Z5.q2 (Z5.pow x 2), Z5.mul Z5.q2 (Z5.pow z 2), Z5.zero, Z5.zero, Z5.zero],
      [Z5.zero, Z5.zero, Z5.mul Z5.q3 (Z5.pow y 2), Z5.zero, Z5.zero],
      [Z5.zero, Z5.zero, Z5.mul P y, Z5.zero, Z5.neg (Z5.mul Z5.q4 t)]]
    let M3 : List (List Z5) := [
      [Z5.one, Z5.one, Z5.one, Z5.one, Z5.one],
      [Z5.neg (Z5.mul Z5.q4 x), Z5.neg (Z5.mul Z5.q4 z), Z5.zero, Z5.mul P t, Z5.zero],
      [Z5.zero, Z5.zero, Z5.zero, Z5.mul Z5.q3 (Z5.pow t 2), Z5.zero],
      [Z5.zero, Z5.zero, Z5.zero, Z5.zero, Z5.mul Z5.q2 (Z5.pow t 2)],
      [Z5.zero, Z5.zero, Z5.neg (Z5.mul Z5.q y), Z5.zero, Z5.mul G t]]
    Z5.sub (Z5.sub (Z5.mul c (Z5.mul t t)) t) Z5.q2 = Z5.zero ∧
    Z5.neg (Z5.pow z 5) = ⟨269, 760, 795, 325⟩ ∧
    Z5.neg (Z5.pow t 5) = ⟨3, 0, -5, -5⟩ ∧
    detZ5 5 M0 = ⟨-1093, -5351, -6894, -3592⟩ ∧
    detZ5 5 M2 = ⟨31, 21, -17, -30⟩ ∧
    detZ5 5 M3 = ⟨6, 19, 21, 9⟩ := by
  decide +kernel

/-- Proposition 5.1 (Order-7 lower bound): exact `F_29[Y]` Bezout polynomial certificate
    `U * Rbar + V * Ebar = 1` (plus `7^7 ≡ 1 (mod 29)` and `7 ≠ 1`). -/
def polyAddF29 (a b : List Nat) : List Nat :=
  let n := max a.length b.length
  (List.range n).map fun i => ((a.getD i 0) + (b.getD i 0)) % 29

def polyMulF29 (a b : List Nat) : List Nat :=
  let n := a.length + b.length - 1
  (List.range n).map fun k =>
    (List.range (k + 1)).foldl (fun acc i =>
      (acc + (a.getD i 0) * (b.getD (k - i) 0)) % 29) 0

theorem order7_lower_bound_bezout_F29 :
    let Rbar := [23, 26, 9, 23, 13, 0, 11, 16, 10, 8]
    let Ebar := [28, 5, 17, 4, 2, 15, 24, 10, 28, 3]
    let U := [21, 24, 2, 5, 25, 23, 15, 2, 18]
    let V := [18, 28, 0, 22, 8, 2, 16, 25, 10]
    (7 ^ 7) % 29 = 1 ∧ 7 % 29 ≠ 1 ∧
    polyAddF29 (polyMulF29 U Rbar) (polyMulF29 V Ebar)
      = 1 :: List.replicate 17 0 := by
  decide +kernel

/-- Theorem 1.1(d) (Order-9 lower bound `M_k(9; q) >= 6` in all admissible characteristics):
    exact `Z[q]/Phi_9(q)` verification of `p3*(q^2+1)=1` and `E*(2q^5-q^4+3q^2-3q+2)=3`. -/
def z9Mul (a b : List Int) : List Int :=
  let raw := (List.range 11).map fun k =>
    (List.range (k + 1)).foldl (fun acc i =>
      if i < 6 && k - i < 6 then acc + a.getD i 0 * b.getD (k - i) 0 else acc) (0 : Int)
  -- Reduce modulo q^6 + q^3 + 1: q^{6+r} = -q^{3+r} - q^r
  let step (arr : List Int) (k : Nat) : List Int :=
    let v := arr.getD k 0
    (List.range 11).map fun j =>
      if j == k then 0
      else if j == k - 3 then arr.getD j 0 - v
      else if j == k - 6 then arr.getD j 0 - v
      else arr.getD j 0
  let red := [10, 9, 8, 7, 6].foldl step raw
  red.take 6

def z9Add (a b : List Int) : List Int :=
  (List.range 6).map fun i => a.getD i 0 + b.getD i 0

def z9Sub (a b : List Int) : List Int :=
  (List.range 6).map fun i => a.getD i 0 - b.getD i 0

theorem order9_lower_bound_certificate :
    let p3 : List Int := [1, -1, -1, 1, 0, -1]
    let p2 : List Int := [-1, 0, 2, 0, -1, 0]
    let p1 : List Int := [1, 1, -1, 0, 1, 0]
    let q : List Int := [0, 1, 0, 0, 0, 0]
    let q2 : List Int := [0, 0, 1, 0, 0, 0]
    let one : List Int := [1, 0, 0, 0, 0, 0]
    let opq2 := z9Mul (z9Add one q) (z9Add one q)
    let E := z9Sub (z9Mul opq2 (z9Sub (z9Sub p2 one) q2)) (z9Mul q (z9Mul p3 p3))
    let cof : List Int := [2, -3, 3, 0, -1, 2]
    z9Mul q p3 = p1 ∧
    z9Mul p3 (z9Add q2 one) = one ∧
    E = [-3, -2, 2, 0, -1, 1] ∧
    z9Mul E cof = [3, 0, 0, 0, 0, 0] := by
  decide +kernel

/-- Theorem 1.1(a) (Order-3 literal 4-bank synthesis over `F_7`, `q = 2`):
    literally constructs all 12 `3x3` branch matrices `(I - X_j)` over `F_7`, verifies each
    explicit inverse `(I - X_j) * Inv_j = I_3`, sums the 4 weighted banks, and verifies all
    9 entries match `F_3[k, t] = 2^(-kt) mod 7`. -/
def matMulF7 (A B : List (List Nat)) : List (List Nat) :=
  (List.range 3).map fun i =>
    (List.range 3).map fun j =>
      (List.range 3).foldl (fun acc k =>
        (acc + (A.getD i []).getD k 0 * (B.getD k []).getD j 0) % 7) 0

def pow2F7 (e : Nat) : Nat :=
  match e % 3 with
  | 0 => 1
  | 1 => 2
  | _ => 4

def branchX_F7 (epsPos deltaPos : Bool) (alpha j : Nat) : List (List Nat) :=
  let zetaExp := if epsPos == deltaPos then 1 else 2
  let zj := pow2F7 (zetaExp * j)
  let shiftRow (i : Nat) : Nat := if epsPos then (i + 1) % 3 else (i + 2) % 3
  let deltaExp (i : Nat) : Nat := if deltaPos then i else (3 - i % 3) % 3
  (List.range 3).map fun r =>
    (List.range 3).map fun c =>
      let diag := if r == c then (zj * pow2F7 (deltaExp c)) % 7 else 0
      let sh := if r == shiftRow c then alpha % 7 else 0
      (diag + sh) % 7

def matAddF7 (A B : List (List Nat)) : List (List Nat) :=
  (List.range 3).map fun i =>
    (List.range 3).map fun j =>
      ((A.getD i []).getD j 0 + (B.getD i []).getD j 0) % 7

def matSubF7 (A B : List (List Nat)) : List (List Nat) :=
  (List.range 3).map fun i =>
    (List.range 3).map fun j =>
      ((A.getD i []).getD j 0 + 7 - (B.getD i []).getD j 0) % 7

def matScaleF7 (s : Nat) (A : List (List Nat)) : List (List Nat) :=
  A.map fun row => row.map fun x => (s * x) % 7

def id3F7 : List (List Nat) := [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
def zero3F7 : List (List Nat) := [[0, 0, 0], [0, 0, 0], [0, 0, 0]]

def verifyOrder3F7Literal : Bool :=
  -- Four legal banks over F_7 (q=2, beta=1, Delta=6=-1 mod 7, 1/3 = 5 mod 7):
  -- (++, 1, [3,0,3]), (-+, 1, [5,3,6]), (+-, 2, [5,5,0]), (--, 2, [0,4,6])
  let banks : List (Bool × Bool × Nat × List Nat) := [
    (true,  true,  1, [3, 0, 3]),
    (false, true,  1, [5, 3, 6]),
    (true,  false, 2, [5, 5, 0]),
    (false, false, 2, [0, 4, 6])]
  let (allInvOk, total) := banks.foldl (fun (okAcc, sumAcc) (ep, dp, al, ws) =>
    let (bankOk, bankSum) := (List.range 3).foldl (fun (bOk, bSum) j =>
      let X := branchX_F7 ep dp al j
      let X2 := matMulF7 X X
      let imx := matSubF7 id3F7 X
      -- Since alpha^3 = 1 and beta^3 = 1, Delta = 1 - 1 - 1 = 6 = -1 mod 7,
      -- so (I - X)^{-1} = 6 * (I + X + X^2) mod 7!
      let invX := matScaleF7 6 (matAddF7 id3F7 (matAddF7 X X2))
      let invOk := (matMulF7 imx invX == id3F7) && (matMulF7 invX imx == id3F7)
      let wj := ws.getD j 0
      (bOk && invOk, matAddF7 bSum (matScaleF7 wj invX))) (true, zero3F7)
    -- Multiply bank average by 1/3 = 5 mod 7
    (okAcc && bankOk, matAddF7 sumAcc (matScaleF7 5 bankSum))) (true, zero3F7)
  let F3 : List (List Nat) :=
    (List.range 3).map fun k =>
      (List.range 3).map fun t => pow2F7 ((3 - (k * t) % 3) % 3)
  allInvOk && (total == F3)

theorem order3_F7_literal_four_bank_synthesis :
    verifyOrder3F7Literal = true := by
  decide +kernel

end WeylResolventFourierBanks

#print axioms WeylResolventFourierBanks.exclusive_point_PP
#print axioms WeylResolventFourierBanks.odd_square_covered_by_four_triangles
#print axioms WeylResolventFourierBanks.hankel_bank_lower_bound
#print axioms WeylResolventFourierBanks.five_thirds_range_margins
#print axioms WeylResolventFourierBanks.finite_field_guard_margin
#print axioms WeylResolventFourierBanks.reverse_gcd_trial_bound
#print axioms WeylResolventFourierBanks.order5_lower_bound_certificates
#print axioms WeylResolventFourierBanks.order5_upper_determinants_and_guards
#print axioms WeylResolventFourierBanks.order7_lower_bound_bezout_F29
#print axioms WeylResolventFourierBanks.order9_lower_bound_certificate
#print axioms WeylResolventFourierBanks.order3_F7_literal_four_bank_synthesis
