import QRHShort.Manuscript

/-!
Axiom audit of the two main theorems, run by `.github/workflows/build.yml`:

    cd build && lake env lean PrintAxioms.lean

The `example`s fail to compile unless the theorems have exactly the frozen
statement types; the `#print axioms` output must list only `propext`,
`Classical.choice` and `Quot.sound`.
-/

example : QRHShort.MainStatement := QRHShort.Manuscript.main
example : QRHShort.PrimeAPStatement := QRHShort.Manuscript.primes_ap

#print axioms QRHShort.Manuscript.main
#print axioms QRHShort.Manuscript.primes_ap
#print axioms QRHShort.hecke_continuation
