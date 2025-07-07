# FormalProofs: Formal Verification of Basic Logical Theorems in Coq

## Overview

This project, **FormalProofs**, presents the formalization and mechanized verification of fundamental theorems in **propositional** and **predicate logic** using the **Coq proof assistant**. The ability to express and verify logical statements formally is a key skill in areas such as formal methods, program verification, and AI safety.

The primary objective of this project is not only to prove well-known logical results, but to do so within a formal system that ensures the correctness of each proof down to the smallest inference step. This process highlights the distinction between **constructive logic** (intuitionistic) and **classical logic**, and how they are handled differently within Coq.

## Theorems Formalized and Verified

### Propositional Logic

The following foundational theorems are included:

1. **Modus Ponens**  
   If a proposition `P` is true and `P → Q` is true, then the proposition `Q` must also be true.  
   This is provable within constructive logic.

2. **Double Negation Introduction**  
   Demonstrates that if a proposition `P` holds, then its double negation `~~P` also holds.  
   This is valid constructively.

3. **De Morgan’s Law 1**: ¬(P ∧ Q) → ¬P ∨ ¬Q  
   This implication requires classical reasoning and cannot be proven constructively.

4. **De Morgan’s Law 2**: ¬(P ∨ Q) ↔ ¬P ∧ ¬Q  
   This equivalence can be established without classical axioms.

5. **Law of Excluded Middle**: P ∨ ¬P  
   This is a classical principle not provable within constructive logic, but usable via classical axioms.

### Predicate Logic

These theorems explore the interaction between quantifiers (`forall`, `exists`) and negation:

1. **Universal implies Existential**  
   If a property holds for all elements, it certainly holds for at least one.

2. **Existential implies Not Universal Negation**  
   If there exists an element satisfying a property, then it is false that the property fails for all elements.

3. **Negation of Existential implies Universal Negation**  
   If no element satisfies a property, then every element fails to satisfy it.

These predicate logic results are provable within Coq's constructive framework.

## Motivation and Significance

Mechanized proofs in Coq eliminate the possibility of human error in logical reasoning by enforcing rigor at every step. This kind of formal verification is increasingly important in:

- **Safety-critical systems** where correctness is essential (e.g., aerospace, healthcare software).
- **Cryptography and security protocols**.
- **Formal verification of machine learning models**.

Understanding the boundary between constructive and classical logic is also central to the development of sound systems in proof assistants, type theory, and programming language design.

## How to Use This Repository

1. Install Coq from https://coq.inria.fr/download, along with CoqIDE or VS Code + Coq extension.
2. Clone or download this repository.
3. Open the `formal_proofs.v` file in your Coq environment.
4. Step through each proof interactively to observe how theorems are constructed and verified.

## Future Work

Future directions could include:
- Formal verification of simple algorithms (e.g., sorting, arithmetic).
- Extending the project to first-order logic or program properties.
- Exploring automated proof strategies or decision procedures within Coq.

## License

Released under the MIT License.

## Acknowledgments

This project was developed to build foundational skills in formal reasoning, theorem proving, and the use of Coq for mechanized logic. All proofs were written and verified independently for educational purposes.
