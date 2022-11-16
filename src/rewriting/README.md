
This directory contains an experimental version of the Abstract
Binding Trees library that relies on Agda's rewriting feature to
automate much of the reasoning (i.e. uses the `--rewriting` flag).
The main goal is for all the public-facing definitions to be in terms
of the σ-calculus of Abadi et. al. and to provide all the equations of
the σ-calculus as automatic rewrite rules. Because the σ-calculus is
confluent and strongly normalizing, this automation implements a
decision procedure for equality of substitutions.
