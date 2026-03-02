import Mathlib

open Polynomial AdjoinRoot

-- basic setup for the ring Z[sqrt7]

noncomputable def poly_seven : ℤ[X] := X^2 - 7

abbrev Z_sqrt7 := AdjoinRoot poly_seven

noncomputable def sqrt7 : Z_sqrt7 := root poly_seven

lemma sqrt7_sq : sqrt7 ^ 2 = (7 : Z_sqrt7) := by
  have h : AdjoinRoot.mk poly_seven poly_seven = 0 := AdjoinRoot.mk_self
  change AdjoinRoot.mk poly_seven (X ^ 2 - 7) = 0 at h
  rw [map_sub, map_pow] at h
  have hX : AdjoinRoot.mk poly_seven X = sqrt7 := rfl
  rw [hX] at h
  change sqrt7 ^ 2 - 7 = 0 at h
  exact sub_eq_zero.mp h

-- factorization in Z[sqrt7]

lemma rewrite_equation (x y : ℤ) (h : y ^ 2 = x ^ 3 + 7) : x^3 = y^2 - 7 := by
  rw [h]
  ring

lemma factorization_in_Z_sqrt7 (x y : ℤ) (h : y ^ 2 = x ^ 3 + 7) :
    (x : Z_sqrt7) ^ 3 = ((y : Z_sqrt7) - sqrt7) * ((y : Z_sqrt7) + sqrt7) := by
  have hxℤ : x ^ 3 = y ^ 2 - 7 := rewrite_equation x y h
  have hx_cast : (x : Z_sqrt7) ^ 3 = ((y ^ 2 - 7 : ℤ) : Z_sqrt7) := by
    simp only [← hxℤ]
    norm_cast
  have hx : (x : Z_sqrt7) ^ 3 = (y : Z_sqrt7) ^ 2 - 7 := by
    simpa [pow_two] using hx_cast
  have hprod : ((y : Z_sqrt7) - sqrt7) * ((y : Z_sqrt7) + sqrt7) = (y : Z_sqrt7) ^ 2 - 7 := by
    have : ((y : Z_sqrt7) - sqrt7) * ((y : Z_sqrt7) + sqrt7) = (y : Z_sqrt7) ^ 2 - sqrt7 ^ 2 := by ring
    rw [sqrt7_sq] at this
    simpa [pow_two] using this
  exact hx.trans hprod.symm

-- parity and coprimality lemmas
lemma x_even_then_cubemod8_zero (n : ℤ) (hn : Even n) : (n ^ 3 : ZMod 8) = 0 := by
  rcases hn with ⟨k, rfl⟩
  have h1 : k + k = 2 * k := by ring
  rw [h1]
  push_cast
  rw [mul_pow]
  have h2 : (2 : ZMod 8) ^ 3 = 0 := rfl
  rw [h2, zero_mul]

lemma squarenot7mod8 (n : ℤ) : (n ^ 2 : ZMod 8) ≠ 7 := by
  generalize (n : ZMod 8) = m
  revert m
  decide

-- A necessary step: x must be odd and y must be even
lemma x_is_odd (x y : ℤ) (h : y ^ 2 = x ^ 3 + 7) : Odd x := by
  rcases Int.even_or_odd x with h_even | h_odd
  · -- Case 1: x is even
    have h_mod : ((y ^ 2 : ℤ) : ZMod 8) = ((x ^ 3 + 7 : ℤ) : ZMod 8) := by rw [h]
    push_cast at h_mod
    have hx3 : (x ^ 3 : ZMod 8) = 0 := x_even_then_cubemod8_zero x h_even
    push_cast at hx3
    rw [hx3, zero_add] at h_mod
    have hy2 : (y ^ 2 : ZMod 8) ≠ 7 := squarenot7mod8 y
    push_cast at hy2
    exact False.elim (hy2 h_mod)
  · -- Case 2: x is odd
    exact h_odd

-- simple lemmas about eveness
lemma even_means_mod2zero (n : ℤ) : (Even n) ↔ (n : ZMod 2) = 0 := by
  constructor
  · rintro ⟨k, rfl⟩
    -- goal: (↑(k + k) : ZMod 2) = 0
    push_cast
    -- goal: (k : ZMod 2) + (k : ZMod 2) = 0
    have h : (2 : ZMod 2) = 0 := rfl
    have hstep : (k : ZMod 2) + (k : ZMod 2) = 2 * (k : ZMod 2) := by ring
    rw [hstep, h, zero_mul]
  · intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    -- h : (2 : ℤ) ∣ n
    obtain ⟨k, hk⟩ := h
    -- hk : n = 2 * k, need n = k + k
    exact ⟨k, by omega⟩

lemma even_of_even_sq (y : ℤ) (h : Even (y ^ 2)) : Even y := by
  have h_sq_zero : ((y ^ 2 : ℤ) : ZMod 2) = 0 := (even_means_mod2zero (y ^ 2)).mp h
  push_cast at h_sq_zero
  rcases Int.even_or_odd y with h_even | h_odd
  ·
    exact h_even
  ·
    have h_y_mod : (y : ZMod 2) = 1 := by
      rcases h_odd with ⟨k, rfl⟩
      have h_alg : k + k + 1 = 2 * k + 1 := by ring
      push_cast
      have h2 : (2 : ZMod 2) = 0 := rfl
      rw [h2, zero_mul, zero_add]
    rw [h_y_mod] at h_sq_zero
    have h_one_sq : (1 : ZMod 2) ^ 2 = 1 := rfl
    rw [h_one_sq] at h_sq_zero
    have h_one_neq_zero : (1 : ZMod 2) ≠ 0 := by decide
    exact False.elim (h_one_neq_zero h_sq_zero)

-- The main parity proof for y
lemma y_is_even (x y : ℤ) (h : y ^ 2 = x ^ 3 + 7) : Even y := by
-- first prove rhs is even, then use that to prove lhs is even, then apply the helper lemma
  have hx_odd : Odd x := x_is_odd x y h
  have h_mod : ((y ^ 2 : ℤ) : ZMod 2) = ((x ^ 3 + 7 : ℤ) : ZMod 2) := by rw [h]
  push_cast at h_mod
  have hx3 : (x ^ 3 : ZMod 2) = 1 := by
    rcases hx_odd with ⟨k, hk⟩
    rw [hk]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := rfl
    rw [h2, zero_mul, zero_add, one_pow]
  rw [hx3] at h_mod
  have h_rhs : (1 : ZMod 2) + 7 = 0 := rfl
  rw [h_rhs] at h_mod
  have hy2_even : Even (y ^ 2) := by
    rcases Int.even_or_odd (y ^ 2) with h_even | h_odd
    · exact h_even
    · have h_contra : ((y ^ 2 : ℤ) : ZMod 2) = 1 := by
        rcases h_odd with ⟨m, hm⟩
        rw [hm]
        push_cast
        have h2 : (2 : ZMod 2) = 0 := rfl
        rw [h2, zero_mul, zero_add]
      push_cast at h_contra
      rw [h_mod] at h_contra
      have h_zero_neq_one : (0 : ZMod 2) ≠ 1 := by decide
      exact False.elim (h_zero_neq_one h_contra)

  exact even_of_even_sq y hy2_even

-- Now we can prove coprimality using the fact that x is odd
lemma coprime_conjugates (x y : ℤ) (hx : Odd x) (h : y ^ 2 = x ^ 3 + 7) :
    IsCoprime ((y : Z_sqrt7) - sqrt7) ((y : Z_sqrt7) + sqrt7) := by
  sorry

-- proving ufd and the cube factorization of coprime elements

-- proof of ID
-- first prove x^2-7 is irreducible
lemma poly_seven_irreducible : Irreducible poly_seven := by
  sorry

-- then prove it is prime
lemma poly_seven_prime : Prime poly_seven := by
  sorry

-- finally, we can conclude it is an integral domain
noncomputable instance Z_sqrt7_isDomain : IsDomain Z_sqrt7 := by
  unfold Z_sqrt7 poly_seven
  have h_ne : (X ^ 2 - 7 : ℤ[X]) ≠ 0 := by
    sorry
  have h_prime_ideal : (Ideal.span {(X ^ 2 - 7 : ℤ[X])} : Ideal ℤ[X]).IsPrime :=
    (Ideal.span_singleton_prime h_ne).mpr poly_seven_prime
  exact Ideal.Quotient.isDomain _

-- Now the UFD instance will compile because IsDomain provides CancelCommMonoidWithZero
noncomputable instance Z_sqrt7_is_UFD : UniqueFactorizationMonoid Z_sqrt7 := sorry
-- If two coprime elements multiply to a cube, they are cubes *up to a unit*
lemma cube_factorization_of_coprime [UniqueFactorizationMonoid Z_sqrt7] {a b c : Z_sqrt7}
    (hcop : IsCoprime a b) (hprod : a * b = c ^ 3) :
    ∃ (u v : Z_sqrt7) (ua ub : Z_sqrt7ˣ), a = ua * u ^ 3 ∧ b = ub * v ^ 3 := by
  sorry

-- more calculations
-- basis representation of elements in Z[sqrt7]
-- A helper to extract unique integer coordinates
lemma exists_unique_int_coords (z : Z_sqrt7) :
    ∃ a b : ℤ, z = (a : Z_sqrt7) + (b : Z_sqrt7) * sqrt7 ∧
    (∀ c d : ℤ, z = (c : Z_sqrt7) + (d : Z_sqrt7) * sqrt7 → a = c ∧ b = d) := by
  sorry

-- we can equate coefficients
lemma int_coords_eq_iff (a b c d : ℤ) :
    (a : Z_sqrt7) + (b : Z_sqrt7) * sqrt7 = (c : Z_sqrt7) + (d : Z_sqrt7) * sqrt7 ↔ a = c ∧ b = d := by
  constructor
  · intro h
    -- Get unique coords for the element z = a + b*sqrt7
    obtain ⟨p, q, hpq, huniq⟩ := exists_unique_int_coords ((a : Z_sqrt7) + (b : Z_sqrt7) * sqrt7)
    -- By uniqueness, (a,b) gives the coords
    have hab : p = a ∧ q = b := huniq a b rfl
    -- By uniqueness, (c,d) also gives the coords (using h to rewrite)
    have hcd : p = c ∧ q = d := huniq c d h
    exact ⟨by omega, by omega⟩
  · rintro ⟨rfl, rfl⟩
    rfl

-- Define the fundamental unit 8 + 3√7
noncomputable def eps : Z_sqrt7 := 8 + 3 * sqrt7
noncomputable def eps_inv : Z_sqrt7 := 8 - 3 * sqrt7

-- We need a lemma stating that any unit in Z[sqrt7] is an integer power of eps (times ±1). HARD
-- Modulo cubes, the only unit multipliers we care about are 1, eps, and eps_inv.
lemma units_mod_cubes (u : Z_sqrt7ˣ) :
    ∃ (k : Z_sqrt7) (u_base : Z_sqrt7),
    (u : Z_sqrt7) = u_base * k ^ 3 ∧ (u_base = 1 ∨ u_base = eps ∨ u_base = eps_inv) := by
  sorry


-- Few Cube Expansion Lemmas
lemma cube_expand (a b : ℤ) :
    ((a : Z_sqrt7) + (b : Z_sqrt7) * sqrt7) ^ 3 =
    ((a ^ 3 + 21 * a * b ^ 2 : ℤ) : Z_sqrt7) + ((3 * a ^ 2 * b + 7 * b ^ 3 : ℤ) : Z_sqrt7) * sqrt7 := by
  push_cast
  calc ((a : Z_sqrt7) + (b : Z_sqrt7) * sqrt7) ^ 3
    _ = a^3 + 3*a^2*b*sqrt7 + 3*a*b^2*sqrt7^2 + b^3*sqrt7^2*sqrt7 := by ring
    _ = a^3 + 3*a^2*b*sqrt7 + 3*a*b^2*7 + b^3*7*sqrt7 := by rw [sqrt7_sq]
    _ = (a^3 + 21*a*b^2) + (3*a^2*b + 7*b^3)*sqrt7 := by ring

lemma eps_mul_cube_expand (a b : ℤ) :
    eps * ((a : Z_sqrt7) + (b : Z_sqrt7) * sqrt7) ^ 3 =
    ((8 * a ^ 3 + 63 * a ^ 2 * b + 168 * a * b ^ 2 + 147 * b ^ 3 : ℤ) : Z_sqrt7) +
    ((3 * a ^ 3 + 24 * a ^ 2 * b + 63 * a * b ^ 2 + 56 * b ^ 3 : ℤ) : Z_sqrt7) * sqrt7 := by
  -- Unfold eps and use our previous cube_expand lemma
  unfold eps
  rw [cube_expand]
  push_cast
  calc (8 + 3 * sqrt7) * (a ^ 3 + 21 * a * b ^ 2 + (3 * a ^ 2 * b + 7 * b ^ 3) * sqrt7)
    _ = 8 * (a ^ 3 + 21 * a * b ^ 2) + 8 * (3 * a ^ 2 * b + 7 * b ^ 3) * sqrt7 + 3 * (a ^ 3 + 21 * a * b ^ 2) * sqrt7 + 3 * (3 * a ^ 2 * b + 7 * b ^ 3) * sqrt7 ^ 2 := by ring
    _ = 8 * (a ^ 3 + 21 * a * b ^ 2) + 8 * (3 * a ^ 2 * b + 7 * b ^ 3) * sqrt7 + 3 * (a ^ 3 + 21 * a * b ^ 2) * sqrt7 + 3 * (3 * a ^ 2 * b + 7 * b ^ 3) * 7 := by rw [sqrt7_sq]
    _ = (8 * a ^ 3 + 63 * a ^ 2 * b + 168 * a * b ^ 2 + 147 * b ^ 3) + (3 * a ^ 3 + 24 * a ^ 2 * b + 63 * a * b ^ 2 + 56 * b ^ 3) * sqrt7 := by ring

lemma eps_inv_mul_cube_expand (a b : ℤ) :
    eps_inv * ((a : Z_sqrt7) + (b : Z_sqrt7) * sqrt7) ^ 3 =
    ((8 * a ^ 3 - 63 * a ^ 2 * b + 168 * a * b ^ 2 - 147 * b ^ 3 : ℤ) : Z_sqrt7) +
    ((-3 * a ^ 3 + 24 * a ^ 2 * b - 63 * a * b ^ 2 + 56 * b ^ 3 : ℤ) : Z_sqrt7) * sqrt7 := by
  -- Unfold eps_inv (8 - 3√7) and use our previous cube_expand lemma
  unfold eps_inv
  rw [cube_expand]
  push_cast

  calc (8 - 3 * sqrt7) * (a ^ 3 + 21 * a * b ^ 2 + (3 * a ^ 2 * b + 7 * b ^ 3) * sqrt7)
    _ = 8 * (a ^ 3 + 21 * a * b ^ 2) + 8 * (3 * a ^ 2 * b + 7 * b ^ 3) * sqrt7 - 3 * (a ^ 3 + 21 * a * b ^ 2) * sqrt7 - 3 * (3 * a ^ 2 * b + 7 * b ^ 3) * sqrt7 ^ 2 := by ring
    _ = 8 * (a ^ 3 + 21 * a * b ^ 2) + 8 * (3 * a ^ 2 * b + 7 * b ^ 3) * sqrt7 - 3 * (a ^ 3 + 21 * a * b ^ 2) * sqrt7 - 3 * (3 * a ^ 2 * b + 7 * b ^ 3) * 7 := by rw [sqrt7_sq]
    _ = (8 * a ^ 3 - 63 * a ^ 2 * b + 168 * a * b ^ 2 - 147 * b ^ 3) + (-3 * a ^ 3 + 24 * a ^ 2 * b - 63 * a * b ^ 2 + 56 * b ^ 3) * sqrt7 := by ring

-- Integer Multiplication Helper Lemma
lemma int_mul_eq_neg_one (x y : ℤ) (h : x * y = -1) : x = 1 ∨ x = -1 := by
  have h1 : x * (-y) = 1 := by
    calc x * (-y) = -(x * y) := by ring
    _ = -(-1) := by rw [h]
    _ = 1 := by ring
  exact Int.eq_one_or_neg_one_of_mul_eq_one h1

-- Case 1: Trivial unit multiplier leads to contradiction
lemma contradiction_case_1 (a b y : ℤ) :
    (y : Z_sqrt7) - sqrt7 ≠ 1 * ((a : Z_sqrt7) + (b : Z_sqrt7) * sqrt7) ^ 3 := by
  -- Assume the equation is true to derive a contradiction
  intro h_contra
  rw [one_mul] at h_contra
  rw [cube_expand] at h_contra

  -- Format the LHS to match `int_coords_eq_iff` (change `y - sqrt7` to `y + (-1)*sqrt7`)
  have h_lhs : (y : Z_sqrt7) - sqrt7 = (y : Z_sqrt7) + (-1 : ℤ) * sqrt7 := by
    push_cast
    ring
  rw [h_lhs] at h_contra

  -- Apply our iff lemma to equate the coefficients
  have h_eq := (int_coords_eq_iff y (-1) (a ^ 3 + 21 * a * b ^ 2) (3 * a ^ 2 * b + 7 * b ^ 3)).mp h_contra

  rcases h_eq with ⟨_, h_b⟩


  have h_factor : (3 * a ^ 2 * b + 7 * b ^ 3 : ℤ) = b * (3 * a ^ 2 + 7 * b ^ 2) := by ring
  rw [h_factor] at h_b


  have b_cases : b = 1 ∨ b = -1 := int_mul_eq_neg_one b (3 * a ^ 2 + 7 * b ^ 2) h_b.symm


  rcases b_cases with rfl | rfl
  · -- Case b = 1
    -- h_b becomes `-1 = 3a^2 + 7`.

    nlinarith
  · -- Case b = -1
    -- h_b becomes `-1 = -1 * (3a^2 + 7)`.

    nlinarith

-- Case 2: Fundamental unit multiplier leads to contradiction

-- some lemmas before we can prove the contradiction in this case
-- Modulo 9 simplification for the coefficient
lemma case_2_mod_9_simplification (a b : ℤ) :
    ((3 * a ^ 3 + 24 * a ^ 2 * b + 63 * a * b ^ 2 + 56 * b ^ 3 : ℤ) : ZMod 9) =
    3 * (a : ZMod 9) ^ 3 + 6 * (a : ZMod 9) ^ 2 * (b : ZMod 9) + 2 * (b : ZMod 9) ^ 3 := by
  push_cast
  -- Explicitly reduce modulo 9
  have h24 : (24 : ZMod 9) = 6 := rfl
  have h63 : (63 : ZMod 9) = 0 := rfl
  have h56 : (56 : ZMod 9) = 2 := rfl
  rw [h24, h63, h56]
  ring
-- 3 cases for mod3
lemma zmod3_cases (x : ZMod 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  revert x
  decide

-- main lemma mod9
lemma no_solution_mod_9 (A B : ZMod 9) :
    3 * A ^ 3 + 6 * A ^ 2 * B + 2 * B ^ 3 ≠ 8 := by
  revert A B
  decide


lemma contradiction_case_2 (a b y : ℤ) :
    (y : Z_sqrt7) - sqrt7 ≠ eps * ((a : Z_sqrt7) + (b : Z_sqrt7) * sqrt7) ^ 3 := by
  -- Assume the equation holds to derive a contradiction
  intro h_contra

  -- Expand the eps * cube expression
  rw [eps_mul_cube_expand] at h_contra

  -- Format LHS to isolate the `-1` coefficient for the sqrt7 term
  have h_lhs : (y : Z_sqrt7) - sqrt7 = (y : Z_sqrt7) + (-1 : ℤ) * sqrt7 := by
    push_cast
    ring
  rw [h_lhs] at h_contra

  -- Equate the coefficients using our iff lemma
  have h_eq := (int_coords_eq_iff y (-1)
    (8 * a ^ 3 + 63 * a ^ 2 * b + 168 * a * b ^ 2 + 147 * b ^ 3)
    (3 * a ^ 3 + 24 * a ^ 2 * b + 63 * a * b ^ 2 + 56 * b ^ 3)).mp h_contra

  -- Extract the sqrt7 coefficient equation: -1 = 3a^3 + 24a^2b + 63ab^2 + 56b^3
  rcases h_eq with ⟨_, h_b⟩

  -- Cast the exact integer equation to ZMod 9
  have h_mod9 : ((-1 : ℤ) : ZMod 9) = ((3 * a ^ 3 + 24 * a ^ 2 * b + 63 * a * b ^ 2 + 56 * b ^ 3 : ℤ) : ZMod 9) := by
    rw [h_b]

  -- The LHS (-1) trivially evaluates to 8 in ZMod 9
  have h_lhs_mod9 : ((-1 : ℤ) : ZMod 9) = 8 := rfl
  rw [h_lhs_mod9] at h_mod9

  -- Simplify the RHS coefficients using your helper lemma
  rw [case_2_mod_9_simplification] at h_mod9

  -- Flip the equation to match the signature of our universal lemma (LHS ≠ 8)
  have h_mod9_symm := h_mod9.symm

  -- Apply the main lemma we proved about no solutions mod 9 to get a contradiction
  exact no_solution_mod_9 (a : ZMod 9) (b : ZMod 9) h_mod9_symm

-- Case 3: Inverse fundamental unit multiplier leads to contradiction
-- we follow the same strategy as before

-- 2. Modulo 9 simplification for the coefficient (Case 3)
-- 2. Modulo 9 simplification for the coefficient (Case 3)
lemma case_3_mod_9_simplification (a b : ℤ) :
    ((-3 * a ^ 3 + 24 * a ^ 2 * b - 63 * a * b ^ 2 + 56 * b ^ 3 : ℤ) : ZMod 9) =
    6 * (a : ZMod 9) ^ 3 + 6 * (a : ZMod 9) ^ 2 * (b : ZMod 9) + 2 * (b : ZMod 9) ^ 3 := by

  -- Rewrite the polynomial in ℤ by explicitly factoring out 9
  have h_int : (-3 * a ^ 3 + 24 * a ^ 2 * b - 63 * a * b ^ 2 + 56 * b ^ 3 : ℤ) =
    (6 * a ^ 3 + 6 * a ^ 2 * b + 2 * b ^ 3) + 9 * (-a ^ 3 + 2 * a ^ 2 * b - 7 * a * b ^ 2 + 6 * b ^ 3) := by ring
  rw [h_int]
  push_cast
  have h9 : (9 : ZMod 9) = 0 := rfl
  rw [h9]
  ring
-- 3. Universal ZMod 9 contradiction lemma (Case 3)
lemma no_solution_case_3_mod_9 (A B : ZMod 9) :
    6 * A ^ 3 + 6 * A ^ 2 * B + 2 * B ^ 3 ≠ 8 := by
  -- Exhaustively tests all 81 combinations to guarantee this equation is impossible
  revert A B
  decide

lemma contradiction_case_3 (a b y : ℤ) :
    (y : Z_sqrt7) - sqrt7 ≠ eps_inv * ((a : Z_sqrt7) + (b : Z_sqrt7) * sqrt7) ^ 3 := by
  intro h_contra

  -- Expand the eps_inv * cube expression
  rw [eps_inv_mul_cube_expand] at h_contra


  have h_lhs : (y : Z_sqrt7) - sqrt7 = (y : Z_sqrt7) + (-1 : ℤ) * sqrt7 := by
    push_cast
    ring
  rw [h_lhs] at h_contra

  -- Equate the coefficients using our iff lemma
  have h_eq := (int_coords_eq_iff y (-1)
    (8 * a ^ 3 - 63 * a ^ 2 * b + 168 * a * b ^ 2 - 147 * b ^ 3)
    (-3 * a ^ 3 + 24 * a ^ 2 * b - 63 * a * b ^ 2 + 56 * b ^ 3)).mp h_contra

  -- Extract the sqrt7 coefficient equation
  rcases h_eq with ⟨_, h_b⟩

  -- Cast the exact integer equation to ZMod 9
  have h_mod9 : ((-1 : ℤ) : ZMod 9) = ((-3 * a ^ 3 + 24 * a ^ 2 * b - 63 * a * b ^ 2 + 56 * b ^ 3 : ℤ) : ZMod 9) := by
    rw [h_b]

  -- The LHS (-1) trivially evaluates to 8 in ZMod 9
  have h_lhs_mod9 : ((-1 : ℤ) : ZMod 9) = 8 := rfl
  rw [h_lhs_mod9] at h_mod9

  -- Simplify the RHS coefficients using the integer-factorization lemma you just wrote
  rw [case_3_mod_9_simplification] at h_mod9

  -- apply the main lemma we proved about no solutions mod 9 to get a contradiction
  have h_mod9_symm := h_mod9.symm
  exact no_solution_case_3_mod_9 (a : ZMod 9) (b : ZMod 9) h_mod9_symm


-- ==========================================
--  Main Theorem
-- ==========================================

theorem nosolution_for_given_elliptic_curve : ¬ ∃ (x y : ℤ), y ^ 2 = x ^ 3 + 7 := by
  intro ⟨x, y, h⟩
  have h_odd : Odd x := x_is_odd x y h
  have h_coprime := coprime_conjugates x y h_odd h
  have h_prod := factorization_in_Z_sqrt7 x y h

  -- Extract the factors up to a unit
  obtain ⟨u, v, ua, ub, ha, hb⟩ :=
    cube_factorization_of_coprime h_coprime (by simpa using h_prod.symm)

  -- Decompose the unit 'ua' into a base unit and a perfect cube 'k^3'
  obtain ⟨k, u_base, hua, h_base⟩ := units_mod_cubes ua

  -- Substitute our decomposed unit back into our factorization equation
  have ha_rewritten : (y : Z_sqrt7) - sqrt7 = u_base * (k * u) ^ 3 := by
    rw [hua] at ha
    -- ha is now: y - sqrt7 = (u_base * k^3) * u^3
    -- Group the cubes together: (k^3) * u^3 = (k * u)^3
    rw [mul_assoc, ← mul_pow] at ha
    exact ha

  -- Every element in Z_sqrt7 has integer coordinates. Get them for (k * u).
  obtain ⟨a, b, hab_eq, hab_unique⟩ := exists_unique_int_coords (k * u)

  -- Substitute a + b*sqrt7 in place of (k * u) using just the equality piece
  rw [hab_eq] at ha_rewritten
  -- Branch on our 3 possible base units (1, eps, or eps_inv)
  rcases h_base with rfl | rfl | rfl
  · -- Case 1: u_base = 1
    exact contradiction_case_1 a b y ha_rewritten
  · -- Case 2: u_base = eps
    exact contradiction_case_2 a b y ha_rewritten
  · -- Case 3: u_base = eps_inv
    exact contradiction_case_3 a b y ha_rewritten
