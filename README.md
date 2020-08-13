# SpeCS
SPARQL Query Containment Solver

SpeCS is a sound and complete SPARQL query containment solver.
The approach reduces the query containment problem to the satisfiability problem in FOL and therefore enables the usage of state of the art SMT solvers (SpeCS uses Z3 solver).
It covers the most common SPARQL language constructs (conjunctive and cyclic queries, union, filter, from clauses, blank nodes and projections, bind, subqueries, optional, graph, expressions within select clause, builtin functions, etc.) and reasoning under RDF SCHEMA entailment regime.
The containment problem can be considered in both standard and subsumption form.
Renaming of projection variables is also supported.
