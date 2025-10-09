# Network Change Validation with Relational NetKAT (Artifact)

This artifact accompanies the POPL 2026 paper *Network Change Validation with Relational NetKAT*. 
It contains the complete OCaml implementation of Relational NetKAT (RN), as well as scripts and test data 
to reproduce all experiments and comparisons described in the paper.

## Claims and Benchmarks

This artifact supports the following evaluation claims from the paper:

### Section 5.2: Relational NetKAT vs. Rela
- Performance comparison across three benchmark scenarios

### Section 5.3: Relational NetKAT vs. Batfish
- Forwarding change validation
- Hybrid cloud network case study

### Section 5.3: Relational NetKAT Use Cases
- NAT validation
- Tunnel validation

### Section 5.4: Performance Under Splitting Algorithms
- `R(0)` and `R(1)`: Reachability pruning
- `L(0)`, `L(32)`, `L(64)`, `Naive`: Splitting algorithms
- `Global`: Global optimization

### Section 5.5: Other Optimizations
- `Hash`: Hash table memoization
- `Routing`: Efficient routing table encoding
- `Explicit`: Explicit vs. implicit location encoding

All benchmarks and inputs are generated using the included code.

## Installation

The implementation is written in **OCaml 5.2.0** and depends on the following libraries:

- [`mlbdd`](https://opam.ocaml.org/packages/mlbdd/)
- [`yojson`](https://opam.ocaml.org/packages/yojson/)
- [`ounit2`](https://opam.ocaml.org/packages/ounit2/)
- [`dune`](https://dune.build/install)

To install the OCaml dependencies, run: `opam install mlbdd ounit2 yojson dune`.

Besides, Our evaluation includes comparisons with [Batfish](https://github.com/batfish/pybatfish) and [Rela](https://github.com/alibaba/rela/tree/main).  
We have included the relevant source code for both in this artifact, but you may also download them directly from their respective GitHub repositories.

To run the scripts and generate visualization diagrams, please ensure that you have [`python3`](https://www.python.org/downloads/) installed.

## Notes Before Evaluation

1. **Timing Variance in Rela Benchmarks**  
   The Rela benchmarks randomly select test nodes each time they run, leading to natural time variability of about 5–10%.  
   In some cases, such as the `Hash` benchmark, this can reach 20–30%.  
   However, the performance gains we report in the paper are significantly larger (often 50% or more), and most of our comparisons focus on whether a technique results in a **timeout** or not.  
   Therefore, these variations do not affect the validity of the results.

2. **Platform-Specific Timeout Behavior**  
   The `ounit2` OCaml test framework uses platform-specific default timeouts per test case.  
   For example:
   - On **Ubuntu 22.04.2**, the timeout is **10 minutes** per test case.
   - On **Windows 10**, the timeout is **60 minutes** per test case.  
   
   Some benchmarks (especially without optimizations) may take longer than 10 minutes to complete.  
   If a test times out on one platform but not another, that itself is evidence of the optimization’s impact.

3. **Batfish Benchmarks Use a Different Platform**  
   Batfish requires a Docker subsystem for proper execution.  
   As such, our Batfish evaluations were conducted on a different platform from the other experiments.  
   Despite this, the **performance ratios** (e.g., Batfish vs. ours; Rela vs. ours) are consistent and reflect the trends shown in the paper.
   
# Evaluation Instructions

This artifact includes all code necessary to evaluate **Relational NetKAT** and reproduce comparisons with Batfish and Rela as described in the paper.

### 1. Main Evaluation (`RN/`)
Navigate to the `RN/` directory and run:
```bash
dune runtest --no-buffer
python3 draw.py
```

This executes:
- Performance comparison with Rela (200 randomly selected inputs)
- Comparison with Batfish (including NAT and tunneling)
- Timing breakdown for NAT and tunneling cases

**Note**: The full run may take over 20 minutes.  
This directory also includes compiler correctness unit tests, which are not part of the evaluation but may be useful.

---

### 2. Reachability Pruning (`R0/` and `R1/`)
Navigate to each directory and run:
```bash
dune runtest --no-buffer
python3 draw.py
```

These benchmarks evaluate pruning strategies for `preserve` and `delete` cases.  
You should observe a **slightly faster** runtime (0.6× to 0.9× speedup) relative to the `RN/` baseline on these cases.

The `change` scenario is commented out by default (due to expected timeout).  
You can uncomment it in `test/test_RelationalNetkat.ml` to verify the timeout behavior.

---

### 3. Splitting Algorithms (`L0/` and `L32/`)
Navigate to each directory and run:
```bash
dune runtest --no-buffer
python3 draw.py
```

These test our splitting heuristics. All benchmarks should complete successfully.  
You should observe **comparable performance** to `RN/` (within ±5%).

---

### 4. Timeout Splitting Cases (`L64/` and `Naive/`)
Navigate to each directory and run:
```bash
dune runtest --no-buffer
```

All tests are expected to **timeout**.  
This demonstrates that certain splitting strategies are too inefficient to be practical.

---

### 5. Global Bisimulation (`Global/`)
Navigate to the `Global/` directory and run:
```bash
dune runtest --no-buffer
python3 draw.py
```

All tests should complete, but will be over **2× slower** than `RN/`.  
This validates the advantage of our localized splitting approach.

---

### 6. Other Optimizations (`Hash/`, `Routing/`, `Explicit/`)
For each directory:

- In `Hash/`, run:
  ```bash
  dune runtest --no-buffer
  python3 draw.py
  ```

- In `Routing/`, run:
  ```bash
  dune runtest --no-buffer
  ```

- In `Explicit/`, run:
  ```bash
  dune runtest --no-buffer
  python3 draw.py
  ```

These tests validate additional optimizations:
- `Hash/`: Shows over **100× slower** than `RN/`.
- `Routing/`: Demonstrates **50× slower** in Batfish scenarios than `RN/` due to inefficient table organization.
- `Explicit/`: Encodes location information explicitly and is over **5× slower** than `RN/`.

Some test cases may timeout in unoptimized variants. This supports our claims about performance-critical optimizations.


### Batfish

1. Navigate to the `Batfish/jupyter_notebooks` directory. One can see we attach a time measurement after each comparable test in the file
`Introduction to Forwarding Change Validation.ipynb` and `Analyzing public and hybrid cloud networks.ipynb`. One can verify we didn't change
the rest of the code and data by downloading the Batfish repository:  https://github.com/batfish/pybatfish

2. Carefully follows the instruction at https://batfish.org/ or https://batfish.readthedocs.io/en/latest/index.html so that you are able to 
run the notebook in `Batfish/jupyter_notebooks` directory. This will require you to install another docker file to intialize the Batfish server.

3. Open and run the notebooks in Jupyter. Each query is instrumented with timing logic to match the test data reported in the paper.

4. All tests should complete, but will be over **1×-20x faster** than `RN/`.

### Rela

1. Navigate to the `Rela/` directory. One can see we add a `test.py` script to perform evaluation. One can verify we didn't change
the rest of the code and data by downloading the Rela repository:  https://github.com/alibaba/rela

2. Type `python3 test.py`, this generates:
	- `rela_test_all.json` — the full test dataset (matches `RN/dataset/rela_test_all.json`), one can verify that the dataset we uses
	is exactly from Rela's repo.
	-  A peformance benchmark containing 2000 examples for the corresponding scenario, one expect to see around 60x faster performance compared
	to our `RN/` benchmark.
	
3. All tests should complete, but will be over **50×-70x faster** than `RN/`.

	
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

This artifact builds on top of OCaml. This section describes how to reuse and adapt the artifact for your own language development or verification tools.

## Assumptions

Before proceeding, we assume:

- You have completed the steps in the **Installation** section.
- You are familiar with OCaml syntax and basic usage of `dune`.
- You understand the structure of the NetKAT-based relational language.

## Workflow

### 1. Edit the Language Definition

To modify or extend the language:

- Edit the core logic of Relational NetKAT in the following files:
  - `RN/lib/RN.ml`
  - `RN/lib/RN.mli`

These files define:
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
   Modify the test cases in the `test_RelationalNetkat.ml` file located at `RN/test`. We provide more than 600 lines of test code for correctness, including:

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

   Follow the comments in this file to test the correctness of your own version.

   For performance evaluation (e.g., with Rela and Batfish), test using:

   - rela_id_test
   - rela_delete_test
   - rela_change_test
   - change_validation_test
   - hybrid_validation_test

3. **Explore the Impact of Changes**  
   Run your modified implementation using:

   ```bash
   dune runtest
   ```

   This executes all test suites, including correctness checks and benchmarks.

   To visualize benchmark results, run:

   ```bash
   python3 draw.py
   ```

   from the appropriate directory (e.g., `RN/`, `Hash/`, etc.).

   This enables quick prototyping and thorough evaluation of any extensions or optimizations.
