# JSP-000301

Independent Lean 4 formalization of Solomon W. Golomb's 1970 counterexample to the catalog question JSP-000301:

if two consecutive positive integers are powerful, must at least one be a perfect square?

The answer formalized here is no, witnessed by `12167 = 23^3` and `12168 = 2^3 * 3^2 * 13^2`. The separate counting question in Erdős problem #365 is out of scope.

This project uses only core Lean. Closed arithmetic is checked with `decide` (kernel reduction). `native_decide` is not used.

## Build

```sh
lake build
```

The fully qualified theorem is `Jsp000301.jsp_000301`. `Jsp000301/Axioms.lean` runs `#print axioms` on it during the build.
