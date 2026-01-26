# M782 Project: Progress and Preservation Proofs of System F

System F is the polymorphic simply-typed lambda calculus. Polymorphic, here, means that we are allowed to write lambda expressions over any type, e.g., $\Lambda\, A.\lambda\, x.x$ is the identity function over any type $A$.

In this project, we will prove the type-soundness theorem of System F using two lemmas: progress and preservation.

Progress is stated as follows: if $\Gamma \vdash e : \tau$, then $e$ is a value or $e \longmapsto e'$ for some $e'$. Effectively, this boils down to "a terms is either a value or takes a step to eventually becoming a value."

Preservation is stated as follows: if $\Gamma \vdash e : \tau$ and $e \longmapsto e'$, then $e : \tau$. This states that if $e$ is of type $\tau$ and $e$ steps, then the expression that $e$ steps to, namely $e'$, also has type $\tau$. So, terms do not change types in between steps.

## Weekly Progress

We will prove type-soundness in a piecemeal fashion: proving it for the entirety of System F at first would be disastrous. Instead, we will start with a very small language that includes only numbers and booleans. From there, we will add pairs, then sum types, then lambda expressions, and going from there until we reach the polymorphic STLC.

### Week 1: Proofs of a Language with Naturals and Booleans


### Week 2: Pairs


### Week 3: Sum Types


### Weeks 4-5: Functions/Lambda Expressions

