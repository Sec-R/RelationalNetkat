# Network Change Validation with Relational NetKAT (Artifact)

This artifact accompanies the POPL 2026 paper *Network Change Validation with Relational NetKAT*. 
It contains the complete OCaml implementation of Relational NetKAT (RN), as well as scripts and test data 
to reproduce all experiments and comparisons described in the paper.

## Claims and Benchmarks

The artifact supports the following evaluation claims:

- Relational NetKAT vs Rela (Section 5.2): performance on three benchmark scenarios
- Relational NetKAT vs Batfish (Section 5.3): forwarding change validation
- Relational NetKAT vs Batfish (Section 5.3): hybrid cloud network
- Relational NetKAT (Section 5.3): NAT and tunnel validation
- Relational NetKAT (Section 5.4): performance under different optimization
  - `R(0)` and `R(1)` for reachability pruning
  - `L(0)`, `L(32)`, `L(64)`,`Naive` for splitting algorithm
  - `Global` for global optimization
- Relational NetKAT (Section 5.5): performance under other optimization
  - `Hash` for the hash table memorization optimization
  - `Routing` for the efficient routing table optimization
  - `Explicit` for the explicit location encoding

All benchmarks and inputs are generated using the code included in this artifact.

## Installation

The implementation is written in OCaml 5.2.0 and depends on the following libraries and tools:

- [`mlbdd`](https://opam.ocaml.org/packages/mlbdd/)
- [`yojson`](https://opam.ocaml.org/packages/yojson/)
- [`ounit2`](https://opam.ocaml.org/packages/ounit2/)
- [`dune`](https://dune.build/install) 

To install these dependencies, run: `opam install mlbdd ounit2 yojson dune`.


Besides, our test uses code of Batfish and Rela. For installation of these toolkits, we have included the source code in our
files, but you can also download them directly from the github repo https://github.com/batfish/pybatfish and https://github.com/alibaba/rela/tree/main . 
To run these code and the view the diagram of our data, please install [`python3`](https://www.python.org/downloads/).

## Notes before Evaluation
1. It is common to have around 5-10% time difference each time you run our evaluation as our Rela benchmark randomly select nodes to be tested each time at evaluation.
This time variance may go to 20-30% in the benchmark `Hash`. But as the performance difference demonstrated in our paper is significantly larger
than 50%, and our most comparison claims are about whether such techniques make program timeout or not, these result should be able to verified
in our benchmark.


2. We observe that the `ounit2` library for ocaml testing have different default timeout time for different platform. Such as on ubuntu 22.04.2 it was 10 mins for each separate test case (not total time), while it is 60 mins
on Windows 10. You may automatically get timeouts on some benchmarks that runs over 10 mins, but you may consider that as a fact that our techniques
worked out as a method to resolve such timeout.


3. The benchmarks comparing Batfish vs. ours were ran on different platform due to the fact that batfish requires a docker subsystem to communicate.
But we the time ratio between batfish/ours and rela/ours should appear the same as demonstrated on paper.

# Evaluation Instructions

This artifact includes all the code needed to evaluate Relational NetKAT and compare it with Batfish and Rela. 
Below are instructions for running each set of experiments.

### Relational NetKAT

1. **Main Evaluation (RN Directory)**:  
   Navigate to the `RN/` directory and run: `dune runtest --no-buffer`, followed by `python3 draw.py`.
   
	This runs all benchmarks, including:
	- Comparison with Rela (200 randomly selected inputs)
	- Comparison with Batfish (including NAT and tunneling scenarios)

	The test may take over 20 minutes (in total) to complete.  
	Additionally, this directory includes unit tests for compiler correctness, which are unrelated to the paper's benchmarks but may be of interest. 
 
2. **Reachability Pruning (R(0) and R(1))**:  
	Navigate to the `R0/` and `R1/` directories and run: `dune runtest --no-buffer`, followed by `python3 draw.py`. 

	This runs tests on the `preserve` and `delete` scenarios.
	You expect to see a slightly faster (from 0.6x to 0.9x) performance compared to `RN/`'s performance on Rela dataset on `preserve` and `delete`.	
	The `change` scenario is commented out by default due to expected timeout. You may uncomment it in `test/test_RelationalNetkat.ml` to verify the timeout behavior.

3. **Splitting Algorithm (L(0) and L(32))**:  
	Navigate to the `L0/` and `L32/` directories and run: `dune runtest --no-buffer`, followed by `python3 draw.py`. 
	
	All tests should complete successfully. You expect to see a similar (from 0.95x to 1.05x) performance compared to `RN/`'s performance on Rela dataset.

4. **TIMEOUT Splitting Algorithm (L(64) and Naive)**:
	Navigate to the `L64/` and `Naive/` directories and run: `dune runtest --no-buffer`. 

	All tests are expected to timeout.

5. **Global Bisimulation Optimizations (Global)**:
	Navigate to the `Global/` directories and run: `dune runtest --no-buffer`, followed by `python3 draw.py`. 
	
	All tests should complete successfully.You expect to see a slightly slower (more than 2x) performance compared to `RN/`'s performance on Rela dataset.	


6. **Other Optimizations (Hash, Routing, Explicit)**:
	Navigate to the `Hash/` directories and run: `dune runtest --no-buffer`, followed by `python3 draw.py`. 

	Navigate to the `Routing/` directories and run: `dune runtest --no-buffer`. 

	Navigate to the `Explicit/` directories and run: `dune runtest --no-buffer`followed by `python3 draw.py`. 
	
	You may see some of the test case timeout due to some of the unoptimized version runs too slow. But TIMEOUT itself
	should stand for our claims that these optimizations make program faster.
	
	You expected to see much slower (more than 100x in `Hash/`, more than 5x in `Explicit/`) compared to `RN/`'s performance on Rela dataset,
	and a much slower (more than 50x in `Routing/`) to `RN/`'s performance on the first test in Batfish.



### Batfish

1. Navigate to the `Batfish/jupyter_notebooks` directory. One can see we attach a time measurement after each comparable test in the file
`Introduction to Forwarding Change Validation.ipynb` and `Analyzing public and hybrid cloud networks.ipynb`. One can verify we didn't change
  the rest of the code and data by downloading the Batfish repository:  https://github.com/batfish/pybatfish

2. Carefully follows the instruction at https://batfish.org/ or https://batfish.readthedocs.io/en/latest/index.html so that you are able to 
run the notebook in `Batfish/jupyter_notebooks` directory. This will require you to install another docker file to intialize the Batfish server.

3. Open and run the notebooks in Jupyter. Each query is instrumented with timing logic to match the test data reported in the paper.

### Rela

1. Navigate to the `Rela/` directory. One can see we add a `test.py` script to perform evaluation. One can verify we didn't change
  the rest of the code and data by downloading the Rela repository:  https://github.com/alibaba/rela

2. Type `python3 test.py`, this generates:
	- `rela_test_all.json` — the full test dataset (matches `RN/dataset/rela_test_all.json`), one can verify that the dataset we uses
	is exactly from Rela's repo.
	-  A peformance benchmark containing 2000 examples for the corresponding scenario, one expect to see around 60x faster performance compared
	to our `RN/` benchmark.
	
	
# Code documentation

## Relational NetKAT (RN)

This project provides an implementation of **Relational NetKAT** in the directory `RN/`,  a language for specifying and verifying relational properties between two network configurations.

It consists of two main OCaml files:


### RN.ml

This is the core implementation of the language. It defines:

- **Syntax**:
  - `field`, `pk`, `pred`, `pkr`: basic building blocks for packet and field manipulation
  - `NK`: NetKAT expressions
  - `Rel`: Relational NetKAT expressions

- **K and R Automata Construction**:
  - Implements derivatives-based automata for both NetKAT and relational NetKAT -- delta_k delta_r 
  - Defines how to symbolically compile atomics into BDDs  -- compile_pred_bdd, compile_pkr_bdd

- **Compilation Pipeline**:
  - Cross product -- delta_krx
  - Synchronization -- delta_kr
  - Reachability -- calculate_reachable_set
  - Splitting -- generate_all_transitions
  - Projection -- simplify_all_transitions
  - Determinization -- determinization
  - Bisimulation checking -- bisim


## Eval.ml

This file supports Batfish and Rela interfaces.

- **Batfish JSON Parsing**:
  - Loads and parses input/output format from Batfish -- parse_global_routing_table 

- **Rela JSON Parsing**:
  - Loads and parses input/output format from Rela -- parse_rela_global_routing_table, parse_rela_to_rel

	
# Reusability Guide

This artifact builds on top of the ocaml. This section describes how to reuse and adapt the artifact for your own language development.

### Assumptions

We assume you have already completed the steps outlined in the `Installation` section.

### Workflow

1. **Edit the Language Defintion**  
   Modify the language definition in the `RN.ml` and `RN.mli` file located at `RN/lib`. Detailedly, we have:

  - Types:
    - `field`: Represents a field in a packet.
    - `pk`: Represents a packet.
    - `pred`: Represents a predicate in NetKAT (e.g., `True`, `False`, `Test`, `And`, `Or`, `Neg`).
    - `pkr`: Represents a packet relation in NetKAT (e.g., `Id`, `Empty`, `Test`, `LeftAsgn`, `RightAsgn`, `Comp`, etc.).
    - `next_step`: Represents the next step in a transition (`E`, `X`, `Y`, `XY`).

  - Modules:
    - `NK`: Represents NetKAT expressions (e.g., `Pred`, `Pkr`, `Asgn`, `Union`, `Seq`, `Inter`, `Diff`, `Star`, `Dup`).
    - `SNK`: Represents sets of NetKAT expressions.
    - `Rel`: Represents relational expressions (e.g., `Left`, `Right`, `Binary`, `App`, `Id`, `Nil`, `OrR`, `SeqR`, `StarR`).
    - `SR`: Represents sets of relational expressions.
    - `NKOMap`: Represents a mapping from optional NetKAT expressions to BDDs.
    - `ROMap`: Represents a mapping from optional relational expressions to BDDs.
    - `NKROMap`: Represents a mapping from pairs of optional NetKAT and relational expressions to BDDs.
    - `NKROBMap`: Represents a mapping from pairs of optional NetKAT and relational expressions and BDDs to other values.
    - `BSet`: Represents a set of BDDs.
    - `NKROBSet`: Represents a set of pairs of optional NetKAT and relational expressions and BDDs.
    - `NKROBSMap`: Represents a mapping from sets of pairs of optional NetKAT and relational expressions and BDDs to other values.

  - Functions:
    - BDD Operations:
      - `bddvar`: Computes the BDD variable index for a given field and packet.
      - `generate_single_var`: Generates a BDD for a single variable.
      - `bdd_true` / `bdd_false`: Returns the BDD representing `true` or `false`.
      - `compile_pred_bdd`: Compiles a predicate into a BDD.
      - `produce_id`: Produces a BDD representing the identity relation.
      - `produce_assign`: Produces a BDD representing an assignment.
      - `rename_bdd`: Renames variables in a BDD.
      - `closure_bdd`: Computes the closure of a BDD.
      - `comp_bdd` / `comp_bdd_2` / `comp_bdd_4`: Composes BDDs for transitions.

    - Mapping and Set Operations:
      - `add_nko_mapping`, `add_ro_mapping`, `add_nkro_mapping`: Add mappings to BDDs.
      - `union_nko_mapping`, `union_ro_mapping`, `union_nkro_mapping`: Union mappings.
      - `apply_nko_mapping`, `apply_ro_mapping`, `apply_nkro_mapping`: Apply transformations to mappings.
      - `concatenate_nko_mapping`, `concatenate_ro_mapping`, `concatenate_nkro_mapping`: Concatenate mappings.

    - Delta and Transition Functions:
      - `delta_k`: Computes the delta transition for a NetKAT expression.
      - `delta_r`: Computes the delta transition for a relational expression.
      - `delta_krx`: Computes the delta transition with epsilon closure.
      - `delta_kr`: Computes the delta transition for a pair of NetKAT and relational expressions.

    - Determinization and Simplification:
      - `determinize_transition`: Determinizes a transition mapping.
      - `determinization`: Determinizes a NetKAT automaton.
      - `simplify_all_transition`: Simplifies all transitions for a NetKAT automaton.

    - Bisimulation:
      - `bisim`: Checks if two NetKAT automata are bisimilar.

    - String Conversion:
      - `pred_to_string`, `pkr_to_string`, `nk_to_string`, `rel_to_string`, `nkro_to_string`: Convert expressions to strings.

    - Utility Functions:
      - `generate_unused_pk`: Generates an unused packet index.
      - `generate_support`: Generates the support set for a packet.
      - `splitting_bdd`: Splits a BDD into a list of BDDs.
      - `is_final_nkro`, `is_final_nkrob`, `is_final_nkrobs`: Check if states are final.

    - Reordering Functions:
      - `re_ordering`: Reorders variables in a BDD.
      - `back_ordering`: Reverts the reordering of variables in a BDD.

    - Variable Branching:
      - `var_low_branch`, `var_high_branch`, `var_if`: Compute branches of a BDD for a given variable.

   

2. **Edit the Test Cases**   
   Modify the test in the `test_Relationalnetkat.ml` file located at `RN/test`. We provided more than 600 loC of test for correctness. Listed as:

   - var_test
   - compile_pred_test
   - compile_pkr_test
   - compile_delta_k_test
   - compile_delta_r_test
   - delta_krx_test
   - delta_kr_test
   - var_order_test
   - calculate_reachable_test
   - splitting_bdd_test
   - transition_test
   - determinization_transition_test
   - determinization_test
   - bisim_test
   
    One can follow the comments in this file to test the correctness of your own version.

	Other than correctness, one can play with `Rela` and `Batfish` to test the performance of their own version, please follow the test of:

   - rela_id_test
   - rela_delete_test
   - rela_change_test
   - change_validation_test
   - hybrid_validation_test 

 
3. **Explore the Impact of Changes**  
   You can experiment with language changes by typing `dune runtest`.
   
