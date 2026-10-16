# JSP-000307 scope review

Catalog entry: `problems/catalog-0301-0400.md` (JSP-000307).
Wording: "Can three consecutive integers have strictly decreasing largest prime factors?"
Recorded status: Solved. Lean proof: No. No proof-contributor line.
Elapsed years: about 23 years since 1978.

This review does not change those catalog fields, and it does not add anything under `candidates/`.

## Scope distinction

Two different mathematical statements are in play.

**Literal existence.** The printed sentence is a yes/no question. An affirmative answer is the existence of one integer `n > 1` such that the largest prime factor satisfies `P(n) > P(n+1) > P(n+2)`. Erdős and Pomerance already knew examples in 1978 ("On the largest prime factors of n and n+1", Aequationes Math.), and they wrote that they could not prove there are infinitely many.

**Infinitude (the result the elapsed-years field points at).** About 23 years after 1978 is Antal Balog's 2001 paper "On triplets with descending largest prime factors" (Studia Sci. Math. Hungar.). The theorem is that `P(n-1) > P(n) > P(n+1)` for infinitely many `n`. Shifting the index, that is the same relation as `P(m) > P(m+1) > P(m+2)` for infinitely many `m`. A later elementary route (Sungjin Kim, using the Maynard–Tao theorem on admissible affine forms) proves the same infinitude statement. That route is a different proof of infinitude. It is still not a one-triple witness.

A Lean proof of one triple answers the literal sentence. It leaves Balog's infinitude theorem unproved. Setting **Lean proof** to Yes on the strength of one triple would record a formalization of the weaker reading as if it were the 2001 theorem.

## Finite check of 13, 14, 15

This is a check of the weaker reading. It is the 1978 example, and it is not Balog's 2001 theorem.

Computed by trial division:

| n | factorization | largest prime factor |
| --- | --- | --- |
| 13 | 13 | 13 |
| 14 | 2 · 7 | 7 |
| 15 | 3 · 5 | 5 |

`13 > 7 > 5`, so three consecutive integers can have strictly decreasing largest prime factors. The finite statement is true.

The same finite check, still not the 2001 theorem, confirms two other witnesses used in the pull requests below: `(14, 15, 16)` has largest prime factors `7 > 5 > 2` (`16 = 2^4`), and `(152, 153, 154)` has `19 > 17 > 11` (`152 = 2^3 · 19`, `153 = 3^2 · 17`, `154 = 2 · 7 · 11`).

## Reviewed pull requests

Search: open and closed pull requests on `TheJustinSunPrize/awards` matching `JSP-000307` (29 hits). The rows below are the ones whose Lean source was opened at the commit named in the pull request. Builds used Lean `v4.34.0` unless a row says otherwise. "Standard axioms" means `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`.

| PR | Claimed theorem | One finite triple only | Claims infinitude | Build in this review | `sorry` / `admit` / custom axioms | Statement matches infinitude | Verdict |
| --- | --- | --- | --- | --- | --- | --- | --- |
| [#5044](https://github.com/TheJustinSunPrize/awards/pull/5044) aznikline | `Jsp000307.jsp_000307`: `∃ n, 1 < n ∧ P(n) > P(n+1) > P(n+2)`, witness `n = 13`. Also `jsp_000307_family`: every prime `p ≡ 1 (mod 6)` with `(p+1)/2` prime gives one decreasing triple. Source: [aznikline/jsp-000307-lean@9c27196](https://github.com/aznikline/jsp-000307-lean/blob/9c27196f72c2359226ceb020244ebf6278be6a75/Jsp000307.lean). The same commit is named by [#2112](https://github.com/TheJustinSunPrize/awards/pull/2112), [#4862](https://github.com/TheJustinSunPrize/awards/pull/4862), and closed [#604](https://github.com/TheJustinSunPrize/awards/pull/604). | Yes. The family lemma is conditional on those primes. It does not prove infinitely many such primes. | No. The source comment says the infinitude theorem is outside the file. | `lake build` succeeded. Standard axioms on both theorems. | None in the file. | No | does not solve the infinitude statement |
| [#2112](https://github.com/TheJustinSunPrize/awards/pull/2112) aznikline | Same pinned file and theorem as #5044. | Yes | No | Same successful build as #5044. | None | No | does not solve the infinitude statement |
| [#4862](https://github.com/TheJustinSunPrize/awards/pull/4862) aznikline | Same pinned file and theorem as #5044 (one entry in a multi-problem pull request). | Yes | No | Same successful build as #5044. | None | No | does not solve the infinitude statement |
| [#4579](https://github.com/TheJustinSunPrize/awards/pull/4579) fengjie1981 | `Jsp000307.jsp000307`: existence of `n ≥ 14` whose largest prime factors are exactly `7`, `5`, and `2`. Witness `(14, 15, 16)`. Source: [fengjie1981/jsp000307-lean-proof@2ca2302](https://github.com/fengjie1981/jsp000307-lean-proof/blob/2ca2302fbde4784e619b8e2cd3a8f753a72f0f37/Jsp000307.lean). | Yes | No | `lake build` succeeded (Mathlib `ba22a898`). Standard axioms. | None in the file. | No | does not solve the infinitude statement |
| [#1084](https://github.com/TheJustinSunPrize/awards/pull/1084) qzxuwenlong | `jsp_307_answer`: existence of `a, p, q, r` with `p, q, r` prime, each the largest prime factor of `a`, `a+1`, `a+2`, and `p > q > r`. Witness `(14, 15, 16)` with `7 > 5 > 2`. Source: [qzxuwenlong/jsp-lean-solutions@2b75f75](https://github.com/qzxuwenlong/jsp-lean-solutions/blob/2b75f75ad5aec59de069f5ff34b9c7adbc599478/jsp307.lean). | Yes | No | `lean jsp307.lean` succeeded on Lean 4.34.0. The header mentions a wasm toolchain; the file is core Lean and compiled with the official toolchain. | No `sorry` or `admit`. `Prime` is a definition in the file, not an added axiom. | No | does not solve the infinitude statement |
| [#4705](https://github.com/TheJustinSunPrize/awards/pull/4705) kunjunsong-code | `jsp_000307`: `∃ n p1 p2 p3, IsLPF n p1 ∧ IsLPF (n+1) p2 ∧ IsLPF (n+2) p3 ∧ p1 > p2 ∧ p2 > p3`, witness `13, 13, 7, 5`. Source: [kunjunsong-code/jsp-000307-lean@f6c78e2](https://github.com/kunjunsong-code/jsp-000307-lean/blob/f6c78e20f6bc56a6b7c0e0f941b7e56cb978fb66/Jsp/JSP000307.lean). The pull request itself says this is existence and is not Erdős problem 372. | Yes | No | `lean JSP000307.lean` succeeded on Lean 4.34.0. `#print axioms` reported `[propext, Quot.sound]`. | No `sorry` or `admit`. `PrimeP` is a definition, not an added axiom. | No | does not solve the infinitude statement |
| [#3419](https://github.com/TheJustinSunPrize/awards/pull/3419) pokrc | `JSP000307.jsp000307`: `∃ n, maxPrimeFac n > maxPrimeFac (n+1) > maxPrimeFac (n+2)`, witness `152`. Source: [pokrc/jsp_claim@0d22f47](https://github.com/pokrc/jsp_claim/blob/0d22f47b936e39b4cbee801199c537bdef6f2fbb/JspClaim/JSP000307.lean). Closed [#1617](https://github.com/TheJustinSunPrize/awards/pull/1617) names an earlier commit of the same existential theorem. | Yes | No. The pull request text distinguishes this existence proof from Balog's infinitude theorem. | `lake build` of that file succeeded on Mathlib `v4.34.0`. Standard axioms. | None in the file. | No | does not solve the infinitude statement |
| [#4289](https://github.com/TheJustinSunPrize/awards/pull/4289) Omicron0314 | `LeanSyc.JSP000307.threeConsecutiveWithDecreasingP`: existence of `n` with `largestPrimeFactor` strictly decreasing, witness `13`. Source: [Omicron0314/lean_syc_proofs@31566b3](https://github.com/Omicron0314/lean_syc_proofs/blob/31566b39019e45598eedc3b7197311ea7ac1a202/LeanSyc/JSP000307.lean). This replaces closed [#36](https://github.com/TheJustinSunPrize/awards/pull/36), which contains the same theorem. | Yes | No | `lake build LeanSyc.JSP000307` succeeded. Standard axioms. | None in the file. | No | does not solve the infinitude statement |
| [#1946](https://github.com/TheJustinSunPrize/awards/pull/1946) qxf02151821 | `JSP307.solution`: existence of `n, a, b, c` with `a, b, c` the largest prime factors of `n, n+1, n+2` and `a > b > c`. Witness `(14, 15, 16)`. Source: [qxf02151821/jsp-lean-proofs@40319c3](https://github.com/qxf02151821/jsp-lean-proofs/blob/40319c3a46e998f129485d378ce155a1af5eeb91/JSP-000307/JSP307.lean). | Yes | No | `lean JSP307.lean` succeeded on Lean 4.34.0 (core library only). | No `sorry`, `admit`, or `axiom` declaration. `Prime` is a structure in the file. | No | does not solve the infinitude statement |
| [#4591](https://github.com/TheJustinSunPrize/awards/pull/4591) doge-th | `JSP000307.jsp_000307`: existence of primes `p1, p2, p3` with `n = 13`, each the largest prime factor of `n`, `n+1`, `n+2`, and `p1 > p2 > p3`. Source: [doge-th/jsp-lean-proofs@910d4cc](https://github.com/doge-th/jsp-lean-proofs/blob/910d4cc7836b10311fa1e33a9fdce2966726134a/proofs/JSP000307.lean). | Yes. The statement fixes `n = 13`. | No. The pull request says it exhibits `(13, 14, 15)` and does not restate the construction theorems. | Not lake-built here. The pin uses Lean `v4.35.0-rc1` and a different Mathlib revision. | No `sorry` or `admit` in the file. No custom axiom declaration. | No | does not solve the infinitude statement |
| [#496](https://github.com/TheJustinSunPrize/awards/pull/496) WhatIsTrending | `exists_three_consecutive_decreasing_lpf`: `∃ n, 1 < n ∧ lpf n > lpf (n+1) ∧ lpf (n+1) > lpf (n+2)`, with `def lpf n := if 1 < n then Nat.Prime.ofNat n else 1`. Witness intended to be `13`. | The text aims at one triple. | No | Failed. On Mathlib `v4.34.0`, `Nat.Prime.ofNat` is an unknown constant, so the definition does not typecheck. | The definition does not elaborate. No separate `axiom` command. | No. `lpf` is not the largest-prime-factor function. | statement mismatch |
| [#2580](https://github.com/TheJustinSunPrize/awards/pull/2580) dcdreamy-code (closed) | File `submissions/JSP-000307/Erdos307.lean` proves `Nat.Prime 13`, `14 = 2 * 7`, `15 = 3 * 5`, `13 > 7 ∧ 7 > 5`, and that `14` and `15` are the next two integers. | The arithmetic is about one triple, and it never states a largest-prime-factor theorem. | No | Not built. The file has no `sorry`. It also has no definition of largest prime factor. | No `sorry` or custom axiom. The gap is a missing statement. | No | statement mismatch |
| [#1684](https://github.com/TheJustinSunPrize/awards/pull/1684) xinkuangsi-spec | `Erdos372.erdos_372`: `Set.Infinite {n | P n > P (n+1) ∧ P (n+1) > P (n+2)}`, via Kim's reduction and an affine Maynard–Tao input. Source: [plby/lean-proofs@8822f7d](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos372.lean), dependency `BoundedGaps` from [frenzymath/FormalPantheon@ffbb65c](https://github.com/frenzymath/FormalPantheon/tree/ffbb65c21afc8a36ace67720f1b0df1c63d26bd1). | No. The target statement is infinitude. | Yes | Not lake-built. The development is the `Erdos372` modules, the `Erdos6` Maynard weight, and about 650 `BoundedGaps` Lean files on top of Mathlib. | A text scan of `Erdos372`, `Erdos6`, and the import closure of the `BoundedGaps` modules those files import found no `sorry` and no `axiom` declaration in that closure. `sorry` does occur in `Challenge.lean` stubs outside that closure. This was not a kernel check. | Yes, as infinitude. It is the Kim–Maynard–Tao route, and this review did not check it with `lake`. | could not build |
| [#3945](https://github.com/TheJustinSunPrize/awards/pull/3945) dcdreamy-code | Same pin and the same `Erdos372.lean` target as #1684. | No | Yes, by pointing at Erdős problem 372. | Same as #1684: not lake-built. | Same text scan as #1684. Not a kernel check. | Yes, as infinitude, unchecked here. | could not build |

No row has the verdict "actually proves infinitude". The two pull requests whose statement is infinitude were not built with `lake`, so this review does not treat them as a checked proof.

Several writeups name the 2001 author as Balasubramanian, Balzarotti, or Bárány. The paper cited by the elapsed-years field is Antal Balog's.

## Recommendation

Do not submit a Lean claim for JSP-000307 based only on one triple. Do not set **Lean proof** to Yes for a formalization of `(13, 14, 15)`, `(14, 15, 16)`, `(152, 153, 154)`, or a conditional family that assumes extra primes. Those developments can be correct proofs of existence, and several of them did build, and they still leave Balog's infinitude theorem unproved.

A claim that the infinitude statement is formalized needs a kernel-checked proof of infinitely many such `n`. This review did not produce that proof and did not `lake`-build the Maynard–Tao development linked from #1684 and #3945. The catalog numbers stay as they are: Solved, Lean proof No.
