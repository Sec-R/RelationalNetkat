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


6. **Other Optimizations (Hash, Routing, Explicit)
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
	
	
### Code documentation

# Relational NetKAT (RN)

This project provides an implementation of **Relational NetKAT** in the directory `RN/`,  a language for specifying and verifying relational properties between two network configurations.

It consists of two main OCaml files:


## RN.ml

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

	