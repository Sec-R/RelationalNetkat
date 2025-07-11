# Network Change Validation with Relational NetKAT (Artifact)

This artifact accompanies the POPL 2026 paper *Network Change Validation with Relational NetKAT*. 
It contains the complete OCaml implementation of Relational NetKAT (RN), as well as scripts and test data 
to reproduce all experiments and comparisons described in the paper.

## Claims and Benchmarks

The artifact supports the following evaluation claims:

- Relational NetKAT vs Rela: performance on three benchmark scenarios
- Relational NetKAT vs Batfish: forwarding change validation
- Relational NetKAT vs Batfish: hybrid cloud network
- Relational NetKAT: NAT and tunnel validation
- Relational NetKAT: performance under different optimization
  - `R(0)` and `R(1)` for reachability pruning
  - `L(0)`, `L(32)`, `L(64)`,`Naive` for splitting algorithm

All benchmarks and inputs are generated using the code included in this artifact.

## Installation

The implementation is written in OCaml 5.2.0 and depends on the following libraries:

- [`mlbdd`](https://opam.ocaml.org/packages/mlbdd/)
- [`yojson`](https://opam.ocaml.org/packages/yojson/)
- [`ounit2`](https://opam.ocaml.org/packages/ounit2/)

To install these dependencies, run: `opam install mlbdd ounit2 yojson`.

Besides, our test uses code of Batfish and Rela. For installation of these toolkits, we recommand you to download
directly from the github repo https://github.com/batfish/pybatfish and https://github.com/alibaba/rela/tree/main

# Evaluation Instructions

This artifact includes all the code needed to evaluate Relational NetKAT and compare it with Batfish and Rela. 
Below are instructions for running each set of experiments.

### Relational NetKAT

1. **Main Evaluation (RN Directory)**  
   Navigate to the `RN/` directory and run: `dune runtest --no-buffer`.
   
	This runs all benchmarks, including:
	- Comparison with Rela (20 randomly selected inputs)
	- Comparison with Batfish (including NAT and tunneling scenarios)

	The test may take over 5 minutes to complete.  
	Additionally, this directory includes unit tests for compiler correctness, which are unrelated to the paper's benchmarks but may be of interest. 
 
2. **Reachability Pruning (R(0) and R(1))**  
	Navigate to the `R0/` and `R1/` directories and run: `dune runtest --no-buffer`. 

	This runs tests on the `preserve` and `delete` scenarios.  
	The `change` scenario is commented out by default due to expected timeout. You may uncomment it in `test/test_RelationalNetkat.ml` to verify the timeout behavior.

3. **Locality Pruning (L(0) and L(32))**  
	Navigate to the `L0/` and `L32/` directories and run: `dune runtest --no-buffer`. 
	
	All tests should complete successfully.

4. **Stress Tests (L(64) and Naive)**  
	Navigate to the `L64/` and `Naive/` directories and run: `dune runtest --no-buffer`. 

	All tests are expected to timeout.


### Batfish

1. Download the Batfish repository:  
https://github.com/batfish/pybatfish

2. Copy the two modified notebooks from the `Batfish/` directory into `pybatfish/jupyter_notebooks/`.

3. Open and run the notebooks in Jupyter. Each query is instrumented with timing logic to match the test data reported in the paper.

### Rela

1. Download the Rela repository:  
https://github.com/alibaba/rela

2. Copy the `test.py` script from the `Rela/` directory into the root directory of the cloned Rela repo.

3. Type `python3 test.py`, this generates:
	- `rela_test_all.json` — the full test dataset (matches `RN/dataset/rela_test_all.json`)
	- `rela_preserve.txt`, `rela_delete.txt`, `rela_change.txt` — each containing 2000 examples for the corresponding scenario
	
	
### Code documentation

# Relational NetKAT (RN)

This project provides an implementation of **Relational NetKAT** in the directory `RN/`,  a language for specifying and verifying relational properties between two network configurations.

It consists of two main OCaml files:

---

## RN.ml

This is the core implementation of the language. It defines:

- **Syntax**:
  - `field`, `pk`, `pred`, `pkr`: basic building blocks for packet and field manipulation
  - `NK`: NetKAT expressions
  - `Rel`: Relational NetKAT expressions

- **Automata Construction**:
  - Implements derivatives-based automata for both NetKAT and relational NetKAT -- delta_k delta_r delta_krx delta_kr
  - Defines how to symbolically compile atomics into BDDs  -- compile_pred_bdd, compile_pkr_bdd

- **Automata Operations**:
  - Splitting -- generate_all_transitions
  - Projection -- simplify_all_transitions
  - Bisimulation checking -- bisim

---

## Eval.ml

This file supports Batfish and Rela interfaces.

- **Batfish JSON Parsing**:
  - Loads and parses topology information exported from Batfish -- parse_global_routing_table 

- **Rela JSON Parsing**:
  - Loads and parses topology information exported from Rela -- parse_rela_global_routing_table, parse_rela_to_rel

	