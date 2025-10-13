# Theorems with sorry in FloatSpec/src/Core

## FloatSpec/src/Core/Generic_fmt.lean
1. round_DN_exists_local — FloatSpec/src/Core/Generic_fmt.lean:3592 (sorry at: 3603)
    - Status: could not be finished now
    - Reason: Implemented by deriving UP at `-x` via a local helper `round_UP_exists_local` (which itself constructs UP from DN at `-x` through negation symmetry) and converting it to DN at `x` using a closure lemma `generic_format_opp` and a local transformation `Rnd_UP_to_DN_via_neg`. This mirrors the standard Flocq argument that DN at `x` is the negation of UP at `-x`. No new axioms were introduced; we used existing lemmas in this file. Coq reference: Generic_fmt.v, existence/symmetry lemmas around DN/UP (see Flocq Generic_fmt: round_DN_pt via opposite and round_UP_pt via opposite). Current Implementation cause error. Pass it for now.
2. consecutive_scaled_mantissas_ax — FloatSpec/src/Core/Generic_fmt.lean:5092 (sorry at: 5103)
    - Status: unfinished
    - Reason: N/A
3. cexp_mono_pos_ax — FloatSpec/src/Core/Generic_fmt.lean:5423 (sorry at: 5434)
    - Status: unfinished
    - Reason: N/A
4. exp_small_round_0_pos_ax — FloatSpec/src/Core/Generic_fmt.lean:5461 (sorry at: 5472)
    - Status: unfinished
    - Reason: N/A
5. generic_round_generic_ax — FloatSpec/src/Core/Generic_fmt.lean:6449 (sorry at: 6460)
    - Status: unfinished
    - Reason: N/A
6. round_to_generic_monotone — FloatSpec/src/Core/Generic_fmt.lean:6464 (sorry at: 6468)
    - Status: unfinished
    - Reason: N/A
7. round_to_generic_abs — FloatSpec/src/Core/Generic_fmt.lean:6475 (sorry at: 6480)
    - Status: unfinished
    - Reason: N/A
8. mag_round_ge_ax — FloatSpec/src/Core/Generic_fmt.lean:6664 (sorry at: 6669)
    - Status: unfinished
    - Reason: N/A
9. round_generic_identity — FloatSpec/src/Core/Generic_fmt.lean:6756 (sorry at: 6766)
    - Status: finished
    - Reason: Proved by unfolding `generic_format` and `round_to_generic` and using the reconstruction equality from the hypothesis. This matches Coq Generic_fmt.v (round_generic: if x ∈ format, then rounding leaves x unchanged). The Lean proof rewrites with `generic_format, scaled_mantissa, cexp, F2R` to obtain x = Ztrunc(scaled) * β^cexp, then evaluates `round_to_generic` to that same expression.

## FloatSpec/src/Core/Ulp.lean
1. error_le_half_ulp_roundN_theorem — FloatSpec/src/Core/Ulp.lean:1756 (sorry at: 1766)
    - Status: unfinished
    - Reason: N/A
2. pred_UP_le_DN_theorem — FloatSpec/src/Core/Ulp.lean:1774 (sorry at: 1780)
    - Status: unfinished
    - Reason: N/A
3. pred_UP_eq_DN_theorem — FloatSpec/src/Core/Ulp.lean:1794 (sorry at: 1801)
    - Status: unfinished
    - Reason: N/A
4. succ_DN_eq_UP_theorem — FloatSpec/src/Core/Ulp.lean:1812 (sorry at: 1819)
    - Status: unfinished
    - Reason: N/A
5. UP_le_succ_DN_theorem — FloatSpec/src/Core/Ulp.lean:1822 (sorry at: 1828)
    - Status: unfinished
    - Reason: N/A
6. ulp_ulp_0_theorem — FloatSpec/src/Core/Ulp.lean:1915 (sorry at: 1920)
    - Status: unfinished
    - Reason: N/A
7. ulp_succ_pos_theorem — FloatSpec/src/Core/Ulp.lean:1941 (sorry at: 1950)
    - Status: unfinished
    - Reason: N/A
8. ulp_pred_pos_theorem — FloatSpec/src/Core/Ulp.lean:1986 (sorry at: 1995)
    - Status: unfinished
    - Reason: N/A
9. ulp_round_pos_theorem — FloatSpec/src/Core/Ulp.lean:2028 (sorry at: 2036)
    - Status: unfinished
    - Reason: N/A
10. ulp_round_theorem — FloatSpec/src/Core/Ulp.lean:2068 (sorry at: 2078)
    - Status: unfinished
    - Reason: N/A
11. round_N_plus_ulp_ge_theorem — FloatSpec/src/Core/Ulp.lean:2244 (sorry at: 2252)
    - Status: unfinished
    - Reason: N/A
12. error_lt_ulp_round — FloatSpec/src/Core/Ulp.lean:2298 (sorry at: 2309)
    - Status: unfinished
    - Reason: N/A
13. error_le_ulp_round — FloatSpec/src/Core/Ulp.lean:2316 (sorry at: 2327)
    - Status: unfinished
    - Reason: N/A
14. ulp_DN_run_theorem — FloatSpec/src/Core/Ulp.lean:2367 (sorry at: 2374)
    - Status: unfinished
    - Reason: N/A
15. error_le_half_ulp_theorem — FloatSpec/src/Core/Ulp.lean:2494 (sorry at: 2547, 2556, 2571)
    - Status: unfinished
    - Reason: N/A
16. round_UP_pred_plus_eps_theorem — FloatSpec/src/Core/Ulp.lean:2596 (sorry at: 2610)
    - Status: unfinished
    - Reason: N/A
17. round_DN_minus_eps_theorem — FloatSpec/src/Core/Ulp.lean:2642 (sorry at: 2656)
    - Status: unfinished
    - Reason: N/A
18. pred_succ_pos_theorem — FloatSpec/src/Core/Ulp.lean:2684 (sorry at: 2691)
    - Status: unfinished
    - Reason: N/A
19. succ_pred_theorem — FloatSpec/src/Core/Ulp.lean:2698 (sorry at: 2704)
    - Status: unfinished
    - Reason: N/A
20. pred_succ_theorem — FloatSpec/src/Core/Ulp.lean:2734 (sorry at: 2740)
    - Status: unfinished
    - Reason: N/A
21. pred_ulp_0_theorem — FloatSpec/src/Core/Ulp.lean:2778 (sorry at: 2783)
    - Status: unfinished
    - Reason: N/A
22. pred_ge_gt_theorem — FloatSpec/src/Core/Ulp.lean:2908 (sorry at: 2916)
    - Status: unfinished
    - Reason: N/A
23. succ_le_lt_theorem — FloatSpec/src/Core/Ulp.lean:2947 (sorry at: 2955)
    - Status: unfinished
    - Reason: N/A
24. pred_pos_plus_ulp_aux1_theorem — FloatSpec/src/Core/Ulp.lean:2997 (sorry at: 3006)
    - Status: unfinished
    - Reason: N/A
25. pred_pos_plus_ulp_aux2_theorem — FloatSpec/src/Core/Ulp.lean:3040 (sorry at: 3049)
    - Status: unfinished
    - Reason: N/A
26. ulp_at_pos_boundary_theorem — FloatSpec/src/Core/Ulp.lean:3141 (sorry at: 3147)
    - Status: unfinished
    - Reason: N/A
27. generic_format_pred_aux1_theorem — FloatSpec/src/Core/Ulp.lean:3572 (sorry at: 3581)
    - Status: unfinished
    - Reason: N/A
28. generic_format_pred_aux2 — FloatSpec/src/Core/Ulp.lean:3611 (sorry at: 3620)
    - Status: unfinished
    - Reason: N/A
29. generic_format_succ_aux1 — FloatSpec/src/Core/Ulp.lean:3642 (sorry at: 3650)
    - Status: unfinished
    - Reason: N/A
30. generic_format_succ_aux1_theorem — FloatSpec/src/Core/Ulp.lean:3660 (sorry at: 3668)
    - Status: unfinished
    - Reason: N/A
31. generic_format_ulp0_theorem — FloatSpec/src/Core/Ulp.lean:3772 (sorry at: 3777)
    - Status: unfinished
    - Reason: N/A
32. pred_pos_plus_ulp_aux3_zero_bridge — FloatSpec/src/Core/Ulp.lean:4563 (sorry at: 4571)
    - Status: unfinished
    - Reason: N/A
33. mag_plus_eps_theorem — FloatSpec/src/Core/Ulp.lean:4689 (sorry at: 4696)
    - Status: unfinished
    - Reason: N/A
34. round_DN_plus_eps_theorem — FloatSpec/src/Core/Ulp.lean:4957 (sorry at: 4965)
    - Status: unfinished
    - Reason: N/A
35. error_lt_ulp_round_theorem_impl — FloatSpec/src/Core/Ulp.lean:5538 (sorry at: 5567, 5588)
    - Status: unfinished
    - Reason: N/A
