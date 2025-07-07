# FormalProofs-coq

## Overview

**FormalProofs-coq** is an educational and verification project that demonstrates how to mechanize, verify, and partially automate basic logical theorems using the **Coq proof assistant**. The project is structured into two complementary parts:

1. **Manual Formal Proofs:** This section focuses on the formal verification of classical theorems from propositional and predicate logic.
2. **Simple Logic Evaluator:** This section introduces a small decision procedure that evaluates logical formulas represented as data structures.

The goal of this project is to showcase both the theoretical understanding and the practical application of formal methods through mechanized logic.

---

## Part 1: Manual Formal Proofs in Coq

This part contains interactive proofs of several foundational theorems from logic. These proofs are constructed step by step using Coq's tactics.

### Propositional Logic Theorems:

- **Law of Excluded Middle:** States that for any proposition $$P$, either $P$ or $\neg P$ holds. This requires classical reasoning.
- **Modus Ponens:** If $P$ is true and $P \Rightarrow Q$ is true, then $Q$ is true. This is provable constructively.
- **Double Negation Introduction:** If $P$ holds, then $\neg \neg P$ also holds. This is valid in constructive logic.
- **De Morgan's Laws:** Includes both constructive and classical versions of how negation interacts with conjunction and disjunction.

### Predicate Logic Theorems:

- **Universal Implies Existential:** If a property holds for every element, it certainly holds for some element.
- **Existential Implies Not Universal Negation:** If a property holds for at least one element, then it is false to say it holds for none.
- **Negation of Existential Implies Universal Negation:** If no element satisfies a property, then every element fails to satisfy it.

These theorems are proven using basic tactics such as \texttt{intros}, \texttt{apply}, \texttt{destruct}, and \texttt{exfalso} in Coq, ensuring correctness through mechanical verification.

---

## Part 2: Simple Logic Evaluator and Tautology Checking

To complement the manual proofs, this part introduces a minimal **logic evaluator** that can automatically compute the truth value of logical formulas:

1. **Inductive Definition of Logical Formulas:** Logical formulas are defined as an inductive type, representing constants (True, False), variables, and logical connectives (AND, OR, NOT, IMPLIES).

2. **Evaluation Function:** A recursive function computes the boolean result of any given formula under a specified environment (truth assignments to variables).

3. **Verified Tautology:** A small example formula, equivalent to Modus Ponens, is proven to always evaluate to true under any environment, demonstrating that it is a tautology.

This small decision procedure showcases how Coq can be used not just for interactive proofs but also for implementing and verifying logical computation.

---

## Why This Project Matters

This project provides hands-on experience in both:

- **Mechanized reasoning:** Writing, structuring, and verifying formal proofs in a proof assistant.
- **Automated reasoning:** Building a simple decision procedure that evaluates logical formulas systematically.

Such skills are essential in:

- **Formal software and hardware verification.**
- **Artificial Intelligence safety and trustworthiness.**
- **Design and verification of secure systems and protocols.**

This project highlights the importance of understanding both **constructive logic** (which aligns with computability) and **classical logic** (which relies on additional axioms).

---

## How to Use This Repository

1. Install **Coq** (https://coq.inria.fr/download) and either **CoqIDE** or **Visual Studio Code with Coq extension**.
2. Clone or download this repository.
3. Open the `formal_proofs.v` file.
4. Step through each proof and the evaluator interactively until completion (`Qed.`) to understand how each result is derived.

Optional: Capture screenshots of completed proofs for presentations or academic reports.

---

## Future Directions

To further develop this project:

- Extend the logic evaluator to handle more advanced logical constructs.
- Prove correctness of simple algorithms or data structures in Coq.
- Explore code extraction to OCaml or other functional programming languages for practical applications.

---

## Tools Used

- **Coq Proof Assistant**
- **Visual Studio Code with Coq extension**

---

## Repository Link

The complete project summary is available at:  
\url{[FormalLogic_Coq_Project_Summary.pdf](https://github.com/mufithamajeed/FormalProofs-Coq/blob/ce116c4c09568181551fad5e37cd743d24b95bdb/FormalProofs_Coq_Project_Summary.pdf)}

---

## Acknowledgments

This project was developed independently to strengthen my understanding of formal logic, theorem proving, and formal verification techniques using Coq.
