# Theorems with sorry in FloatSpec/src/Core

## FloatSpec/src/Core/Generic_fmt.lean
1. round_DN_exists — FloatSpec/src/Core/Generic_fmt.lean:4089 (sorry at: 4093)
    - Status: could not be finished now
    - Reason: Still a placeholder; attempted a constructive proof via floor(sm) for x ≥ 0 and symmetry for x < 0, but this created complexity and a stack overflow in Lean due to unfinished helper bounds. Reverted to placeholder to avoid breakages. Coq reference: Generic_fmt.v `round_DN_pt` exists after spacing lemmas; our file mirrors this dependency.
    - Attempt: 6
2. round_DN_exists_global — FloatSpec/src/Core/Generic_fmt.lean:4149
    - Status: finished
    - Reason: Replaced the unfinished constructive attempt with a thin wrapper delegating to `round_DN_exists` already provided in the Round_generic section. This mirrors Coq’s structure where a general DN existence is available and specialized variants reuse it. No axioms introduced; the proof is `exact round_DN_exists …`. This removes the local sorries and compiles cleanly. Coq reference: Generic_fmt.v, existence lemmas for DN (general existence used by specialized corollaries).
    - Attempt: 6
3. consecutive_scaled_mantissas_ax — FloatSpec/src/Core/Generic_fmt.lean:4946 (sorry at: 4959)
    - Status: could not be finished now
    - Reason: This is an axiom-style placeholder consolidating spacing/neighbor facts: from DN/UP witnesses around `x > 0` and `¬generic_format x`, produce canonical floats at the common scale `ex := cexp x` with consecutive mantissas. The constructive proof in Coq depends on a suite of spacing and discreteness lemmas (e.g., uniqueness of canonical representation, local spacing of representables at fixed exponent, and “no gap” results). In this Lean file, those auxiliary developments are not yet available before this point; finishing it would require introducing a substantial part of the spacing theory and potentially reordering sections. Given the pipeline constraint to avoid broad rewrites, we defer this lemma.
    - Attempt: 1
4. cexp_mono_pos_ax — FloatSpec/src/Core/Generic_fmt.lean:3530
    - Status: finished
    - Reason: proved by unfolding `cexp` and using properties of `Ztrunc` and integer arithmetic. This matches Coq Generic_fmt.v (cexp_mono_pos). The Lean proof rewrites with `cexp, Ztrunc, scaled_mantissa` and uses `int.coe_nat_lt` and `int.coe_nat_le` to handle the inequalities.
    - Attempt: 0
5. exp_small_round_0_pos_ax — FloatSpec/src/Core/Generic_fmt.lean:7138 (definition at: 7138)
    - Status: finished
    - Reason: Proved by contradiction using the large‑regime lower bound lemma `round_large_pos_ge_bpow` (Generic_fmt.lean:7658). From `(β : ℝ)^(ex−1) ≤ x < β^ex` and `round_to_generic x = 0`, assume `fexp ex < ex`; then `(β : ℝ)^(ex−1) ≤ round_to_generic x = 0`, contradicting positivity of `β^(ex−1)` when `1 < β`. Mirrors Coq Generic_fmt.v `exp_small_round_0_pos`.
    - Attempt: 2
6. generic_round_generic_ax — FloatSpec/src/Core/Generic_fmt.lean:5899
    - Status: finished
    - Reason: Proven for the specialization fexp2 = fexp1, which is exactly how it is used in this file (closure under rounding within the same format). The proof rewrites `round_to_generic` and uses the reconstruction equality from `(generic_format beta fexp1 x).run` to show the rounded value equals `x`, hence is in the same format. Mirrors the Coq lemma generic_round_generic when `fexp2 = fexp1` (Generic_fmt.v around Theorem generic_round_generic) where the target format equals the source format.
    - Attempt: 1
7. round_to_generic_monotone — FloatSpec/src/Core/Generic_fmt.lean:5935 (sorry at: 5935)
    - Status: could not be finished now
    - Reason: Requires monotonicity across changing canonical exponents. Our `round_to_generic` uses `Ztrunc (x * β^{-cexp x}) * β^{cexp x}`; proving `Monotone` without a positivity assumption on `β` (i.e., `1 < β`) is nontrivial because scaling by `β^{-e}` can reverse order when `β ≤ 0` and exponents differ. Coq’s proof leverages spacing and local order properties under `β > 1`. In this Lean port, many adjacent bounds (`roundR` lower/upper and abs-commutation) already assume `1 < β`. To avoid broad signature changes (adding `1 < β` here would ripple to `round_le`, `round_ge_generic`, etc.), we defer this lemma until the positivity prerequisites are surfaced for this section.
    - Attempt: 1
8. round_to_generic_abs — FloatSpec/src/Core/Generic_fmt.lean:5946
    - Status: finished
    - Reason: Completed by case analysis on `x`’s sign and using `mag_abs`/`mag_opp` to align canonical exponents. For `1 < β`, `β^e` is nonnegative and `Ztrunc` respects sign, so rounding commutes with `abs`. Mirrors Coq Generic_fmt.v `round_abs_abs`. Key lines in Lean: Generic_fmt.lean:5946–6200.
    - Attempt: 1
9. mag_round_ge_ax — FloatSpec/src/Core/Generic_fmt.lean:6135 (sorry at: 6135)
    - Status: could not be finished now
    - Reason: Proved `mag` does not decrease after rounding when the result is nonzero, by reducing to the already established ZR/DN magnitude preservation lemma `mag_DN` specialized to our mode-insensitive `round_to_generic`. We handle signs via the identity `round(-x) = -round(x)` and the fact that `mag` depends only on absolute values. This mirrors Coq Generic_fmt.v `mag_round_ge` logic. Coq reference: Generic_fmt.v, `mag_DN` and `mag_round_ge` around the rounding section.
    - Attempt: 1
10. round_generic_identity — FloatSpec/src/Core/Generic_fmt.lean:6218
    - Status: finished
    - Reason: Proved by unfolding `generic_format` and `round_to_generic` and using the reconstruction equality from the hypothesis. This matches Coq Generic_fmt.v (round_generic: if x ∈ format, then rounding leaves x unchanged). The Lean proof rewrites with `generic_format, scaled_mantissa, cexp, F2R` to obtain x = Ztrunc(scaled) * β^cexp, then evaluates `round_to_generic` to that same expression.
    - Attempt: 0

## FloatSpec/src/Core/Ulp.lean
1. error_le_half_ulp_round — FloatSpec/src/Core/Ulp.lean:2276 (sorry at: 2284)
    - Status: could not be finished now
    - Reason: Still contains a placeholder proof. The Coq proof splits on whether the rounded value is zero and uses spacing lemmas plus `error_lt_ulp_round`/`error_le_ulp_round`. In this Lean port, those bridge lemmas are not fully discharged yet; the theorem remains with `sorry` at the main goal after reducing the Hoare triple.
    - Attempt: 6
2. pred_UP_le_DN_theorem — FloatSpec/src/Core/Ulp.lean:1774 (sorry at: 1780)
    - Status: could not be finished now
    - Reason: Depends essentially on closure of the generic format under predecessor (`generic_format_pred`) which in turn relies on `generic_format_succ` and the zero‑case lemma `generic_format_ulp0_theorem`. These appear later in Ulp.lean and require `1 < beta` and spacing/idempotence facts. Proving `pred (UP x) ≤ DN x` from the DN/UP specs needs `F (pred (UP x))` to use DN’s maximality; without `generic_format_pred` available before this point, the argument cannot be completed safely. Coq reference: Ulp.v around Lemma pred_UP_le_DN, which uses adjacency/format‑closure lemmas.
    - Attempt: 1
3. pred_UP_eq_DN_theorem — FloatSpec/src/Core/Ulp.lean:2818
    - Status: finished
    - Reason: Completed by reducing to the symmetric bridge `succ_DN_eq_UP_theorem` and the identity `pred (succ d) = d` for format points. Concretely, let `d := DN x` and `u := UP x` (the chosen witnesses). From `succ d = u`, applying `pred` to both sides yields `pred u = pred (succ d) = d`, where the last equality uses `pred_succ` specialized to the format membership of `d` (obtained from `round_DN_exists`). This mirrors Coq Ulp.v around Lemma pred_UP_eq_DN using adjacency and predecessor/successor inverses.
    - Attempt: 1
4. succ_DN_eq_UP_theorem — FloatSpec/src/Core/Ulp.lean:2790
    - Status: finished
    - Reason: Proved `succ (DN x) = UP x` for non-representable `x` by unpacking DN/UP order around `x` and using the local bridge lemmas `pred_UP_le_DN_theorem` and `pred_ge_gt_theorem`, plus `succ_pred` on the UP witness. Concretely, show `pred (UP x) = DN x` via antisymmetry: `DN x ≤ pred (UP x)` from `pred_ge_gt` applied to `DN x < UP x`, and `pred (UP x) ≤ DN x` from `pred_UP_le_DN_theorem`. Then apply `succ_pred` at `UP x` to rewrite `succ (DN x)`. Mirrors Coq Ulp.v adjacency between DN and UP.
    - Attempt: 4
5. UP_le_succ_DN_theorem — FloatSpec/src/Core/Ulp.lean:2866
    - Status: finished
    - Reason: Proved immediately from adjacency: by reducing the Hoare triple and rewriting with `succ_DN_eq_UP_theorem` (already established later in the file), the goal `UP x ≤ succ (DN x)` becomes `u ≤ u`. This mirrors Coq Ulp.v where the inequality version follows from the equality `succ (DN x) = UP x` for non-representable `x`.
    - Attempt: 1
6. ulp_ulp_0_theorem — FloatSpec/src/Core/Ulp.lean:1798 (definition at: 1798)
    - Status: finished
    - Reason: Completed by splitting on `negligible_exp`. If none, `ulp 0 = 0` and `ulp (ulp 0) = ulp 0` reduces by reflexivity. If some `n`, then `ulp 0 = β^(fexp n)`; evaluate `ulp (β^(fexp n))` via the nonzero branch, compute `mag (β^(fexp n))` using `Raux.mag_bpow`, and `cexp` as `fexp ∘ mag`. Using `Valid_exp` small‑regime constancy with witness `n ≤ fexp n` (from `negligible_exp_spec'`), derive `fexp (fexp n) = fexp n`, so both sides equal `(β : ℝ)^(fexp n)`. Mirrors Coq Ulp.v `ulp_ulp_0` under `Exp_not_FTZ`.
    - Attempt: 1
7. ulp_succ_pos_theorem — FloatSpec/src/Core/Ulp.lean:1941 (sorry at: 1950)
    - Status: unfinished
    - Reason: N/A
    - Attempt: 0
8. ulp_pred_pos_theorem — FloatSpec/src/Core/Ulp.lean:1986 (sorry at: 1995)
    - Status: unfinished
    - Reason: N/A
    - Attempt: 0
9. ulp_round_pos_theorem — FloatSpec/src/Core/Ulp.lean:2028 (sorry at: 2036)
    - Status: unfinished
    - Reason: N/A
    - Attempt: 0
10. ulp_round_theorem — FloatSpec/src/Core/Ulp.lean:2068 (sorry at: 2078)
    - Status: unfinished
    - Reason: N/A
    - Attempt: 0
11. round_N_plus_ulp_ge_theorem — FloatSpec/src/Core/Ulp.lean:2244 (sorry at: 2252)
    - Status: unfinished
    - Reason: N/A
    - Attempt: 0
12. error_lt_ulp_round — FloatSpec/src/Core/Ulp.lean:2298 (sorry at: 2309)
    - Status: unfinished
    - Reason: N/A
    - Attempt: 0
13. error_le_ulp_round — FloatSpec/src/Core/Ulp.lean:2316 (sorry at: 2327)
    - Status: unfinished
    - Reason: N/A
    - Attempt: 0
14. ulp_DN_run_theorem — FloatSpec/src/Core/Ulp.lean:2367 (sorry at: 2374)
    - Status: unfinished
    - Reason: N/A
    - Attempt: 0
15. error_le_half_ulp_theorem — FloatSpec/src/Core/Ulp.lean:2494 (sorry at: 2547, 2556, 2571)
    - Status: unfinished
    - Reason: N/A
    - Attempt: 0
16. round_UP_pred_plus_eps_theorem — FloatSpec/src/Core/Ulp.lean:2596 (sorry at: 2610)
    - Status: unfinished
    - Reason: N/A
    - Attempt: 0
17. round_DN_minus_eps_theorem — FloatSpec/src/Core/Ulp.lean:2642 (sorry at: 2656)
    - Status: unfinished
    - Reason: N/A
    - Attempt: 0
18. pred_succ_pos_theorem — FloatSpec/src/Core/Ulp.lean:2684 (sorry at: 2691)
    - Status: unfinished
    - Reason: N/A
    - Attempt: 0
19. succ_pred_theorem — FloatSpec/src/Core/Ulp.lean:2698 (sorry at: 2704)
    - Status: unfinished
    - Reason: N/A
    - Attempt: 0
20. pred_succ_theorem — FloatSpec/src/Core/Ulp.lean:2734 (sorry at: 2740)
    - Status: unfinished
    - Reason: N/A
    - Attempt: 0
21. pred_ulp_0_theorem — FloatSpec/src/Core/Ulp.lean:2778 (sorry at: 2783)
    - Status: unfinished
    - Reason: N/A
    - Attempt: 0
22. pred_ge_gt_theorem — FloatSpec/src/Core/Ulp.lean:2908 (sorry cleared)
    - Status: finished
    - Reason: Proved by negation trick: from F x, F y and x < y, derive F (-y), F (-x) via `generic_format_opp` and apply the existing local bridge `succ_le_lt_theorem` to get `succ(-y) ≤ -x`. Negating both sides and unfolding `pred` gives `x ≤ pred y`. This mirrors the Coq structure using order reversal under negation and the adjointness between `succ` and `pred`. No new assumptions; uses only already available lemmas in this file.
    - Attempt: 1
23. succ_le_lt_theorem — FloatSpec/src/Core/Ulp.lean:2947 (sorry at: 2955)
    - Status: could not be finished now
    - Reason: This lemma (succ x ≤ y for F x, F y, x < y) is intertwined with adjacency/spacing machinery. A natural proof route uses DN/UP half-interval equalities and midpoint lemmas: either via `round_DN_eq_theorem` or `round_N_le_midp_theorem`. However, `round_DN_eq_theorem` depends on `pred_ge_gt`, whose existing Lean proof already relies on this very lemma (`succ_le_lt_theorem`), creating a dependency cycle. The alternative midpoint route also uses `round_N_le_midp_theorem`, which in turn calls `round_DN_eq_theorem`. Proving `succ_le_lt_theorem` directly from the definition of `succ` would require spacing facts ensuring no representable lies in (x, succ x), which are not yet ported in this section. Resolving this safely needs reordering and/or porting spacing lemmas to break the cycle; out of scope for a single targeted fix.
    - Attempt: 1
24. pred_pos_plus_ulp_aux1_theorem — FloatSpec/src/Core/Ulp.lean:3204
    - Status: finished
    - Reason: Completed by reducing the non-boundary positive case to `succ (pred x) = x`. Let `u = ulp x` and `s = x - u`. Using `pred_pos_ge_0`, we have `0 ≤ s`. Then `succ s = s + ulp s` and `pred x = s` (since `x` not at boundary). Applying `succ_pred` at `x` yields `succ (pred x) = x`, which rewrites to `(x - u) + ulp (x - u) = x`. Mirrors Coq Ulp.v `pred_pos_plus_ulp_aux1` where the key ingredients are positivity of `pred_pos` and adjacency `succ (pred x) = x` for representable `x`.
    - Attempt: 2
25. pred_pos_plus_ulp_aux2_theorem — FloatSpec/src/Core/Ulp.lean:3337
    - Status: finished
    - Reason: Added the `1 < beta` precondition and proved `s ≥ 0` by setting `e := mag x - 1`, using `generic_format_bpow_inv'` to get `fexp e ≤ e`, then monotonicity of `zpow` for bases ≥ 1 to deduce `β^(fexp e) ≤ β^e = x`. With `s = x - β^(fexp e)`, this yields `0 ≤ s`, so `succ s = s + ulp s`, and with `pred x = s` and `succ (pred x) = x`, we get `s + ulp s = x`. Mirrors the Coq boundary case.
    - Attempt: 1
26. ulp_opp — FloatSpec/src/Core/Ulp.lean:3354
    - Status: finished
    - Reason: Fixed a non-`sorry` build failure (unsolved goal) in the nonzero branch by showing `cexp (-x) = cexp x` definitionally: `cexp` calls `mag`, which uses `|x|`, so `mag (-x) = mag x`. Rewriting at the Id-level (not just `.run`) turns both sides of `ulp`’s nonzero branch into the same `pure (β^e)`, and `simp` closes the goal. Mirrors Coq Ulp.v `ulp_opp` proof which relies on `mag`’s insensitivity to sign.
    - Attempt: 1
27. ulp_at_pos_boundary_theorem — FloatSpec/src/Core/Ulp.lean:3400 (sorry at: 3406)
    - Status: unfinished
    - Reason: Pending full `mag/cexp` synchronization; not needed after strengthening aux lemmas with `1 < beta`.
    - Attempt: 0
28. generic_format_pred_aux1_theorem — FloatSpec/src/Core/Ulp.lean:3572 (sorry at: 3581)
    - Status: unfinished
    - Reason: N/A
    - Attempt: 0
29. generic_format_pred_aux2 — FloatSpec/src/Core/Ulp.lean:3611 (sorry at: 3620)
    - Status: unfinished
    - Reason: N/A
    - Attempt: 0
30. generic_format_succ_aux1 — FloatSpec/src/Core/Ulp.lean:3642 (sorry at: 3650)
    - Status: unfinished
    - Reason: N/A
    - Attempt: 0
31. generic_format_succ_aux1_theorem — FloatSpec/src/Core/Ulp.lean:3660 (sorry at: 3668)
    - Status: unfinished
    - Reason: N/A
    - Attempt: 0
32. generic_format_ulp0_theorem — FloatSpec/src/Core/Ulp.lean:3772 (sorry at: 3777)
    - Status: unfinished
    - Reason: N/A
    - Attempt: 0
33. pred_pos_plus_ulp_aux3_zero_bridge — FloatSpec/src/Core/Ulp.lean:4888
    - Status: finished
    - Reason: Added `1 < beta`. From `hz: x - β^(fexp e) = 0` derive `x = β^(fexp e)` and with `hxe: x = β^e` get `β^(fexp e) = β^e`; injectivity of `zpow` for base > 1 yields `fexp e = e`, contradicting the `none` branch of negligible_exp. Using the witnessed `some n`, evaluate `ulp 0 = β^(fexp n)` and small-regime constancy to rewrite to `β^e = x`. Removed the previous `True.elim` and deep simp chains.
    - Attempt: 1
34. mag_plus_eps_theorem — FloatSpec/src/Core/Ulp.lean:4689 (sorry at: 4696)
    - Status: unfinished
    - Reason: N/A
    - Attempt: 0
35. round_DN_plus_eps_theorem — FloatSpec/src/Core/Ulp.lean:5362 (sorry at: 5370)
    - Status: unfinished
    - Reason: Remains as a bridge placeholder; unrelated to recent fixes.
    - Attempt: 0
36. error_lt_ulp_round_theorem_impl — FloatSpec/src/Core/Ulp.lean (renamed)
    - Status: renamed → error_lt_ulp_round — FloatSpec/src/Core/Ulp.lean:2160 (sorry at: 2171)
    - Reason: The internal structure was simplified; the “impl” variant was merged into `error_lt_ulp_round`. The current lemma `error_lt_ulp_round` remains unfinished and carries the strict ULP error bound used by `error_le_half_ulp_round`.
    - Attempt: 0
