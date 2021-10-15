Coq proofs on transformation between mu-calculus and RA
=======================================================

Formal proofs on a transformation between
mu-calculus with freeze quatifier and register automata (RA).
The proofs were constructed using the [Coq](https://coq.inria.fr)
proof assistant.

- Pretty-printed definitions and statements of theorems are available
  in [automata.html](https://ytakata69.github.io/proof-mucal-ra/automata.html),
  [raToEqnsys.html](https://ytakata69.github.io/proof-mucal-ra/raToEqnsys.html),
  and other HTML files linked from them.
- To inspect the proofs, see the `.v` files in this repository.
  - `ltl.v`        - The definition of LTL formulas with freeze quantifier.
  - `eqnSys.v`     - The definition of equation systems on the LTL formulas.
  - `automata.v`   - The definition of the mu-calculus-to-RA transformation
                     and the proof of its correctness.
  - `raToEqnsys.v` - The definition of the RA-to-mu-calculus transformation
                     and the proof of its correctness.
