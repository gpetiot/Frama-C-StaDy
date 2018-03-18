# Methodology

The proposed methodology is composed of two steps. The first step looks for non-compliance. If none is detected, the second step looks for a subcontract weakness. These two steps have to be run separately for now (no automation).

Each of these steps is composed of two parts:
- a translation: producing an instrumented C program from an annotated C program. The ACSL annotations of the latter are translated in a semantically equivalent C code, such that test generation can be applied;
- a test generation: trying to cover all feasible execution paths of the program, exhibiting counterexamples if any, and reporting annotation violations. This step uses the [PathCrawler](https://frama-c.com/pathcrawler.html) test generator.
