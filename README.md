# SpeCS
SPARQL Query Containment Solver

SpeCS is a sound and complete SPARQL query containment solver.
The approach reduces the query containment problem to the satisfiability problem in FOL and therefore enables the usage of state of the art SMT solvers (SpeCS uses Z3 solver).
It covers the most common SPARQL language constructs (conjunctive and cyclic queries, union, filter, from clauses, blank nodes and projections, bind, subqueries, optional, graph, expressions within select clause, builtin functions, etc.) and reasoning under RDF SCHEMA entailment regime.
The containment problem can be considered in both standard and subsumption form.
Renaming of projection variables is also supported.

# Prerequisites
In order to compile SpeCS, the following tools have to be installed (check how to install them for your system):
- make
- g++
- flex
- bison

In order to execute SpeCS, Z3 solver has to be installed (https://github.com/Z3Prover/z3).

# Building
> cd src

> make

# Execution

> ./specs -file path_to_file_with_2_sparql_queries [-rename] [-qc]

> ./specs -superquery q1 -subquery q2 [-schema sc] [-rename] [-qc]

The option -rename allows renaming of projection variables that is forbidden by default.
The option -qc causes to chech the containment relation, instead of subsumption by default.
The output 'unsat' means that query containment is present, while 'sat' means the oposite.

# Test Examples
In folder tests, you can find test cases from QCBench (http://sparql-qc-bench.inrialpes.fr/).



