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

1. The main verision is in the directory `RN/`, go to that directory and type `dune runtest` or `dune runtest --no-buffer`(recommanded).
   We have annotated our output so one will be able to see the test result of rela comparsion (on randomly selected 20 datas) 
   and batfish comparsion (integrate with it we show the NAT and tunneling). It is normal to have a long test time (>5min).
   
   Aside from these comparsion, we also integrate a lot of tests to ensure the correctness of our compiler. While it is related to
   none of the test data in the paper, one can also check it if interested.

2. For test on R0 and R1, go the the directory `R0/` and `R1/` and type `dune runtest --no-buffer`. One will see the test result on the senarios
   preserve and delete. We comment out the test change as it is going to timeout. One can verify such timeout by uncommenting that part
   in `test/test_RelationalNetkat.ml`  and type `dune runtest --no-buffer`.
   
3. For test on L0 and L32, go the the directory `L0/` and `L32/` and type `dune runtest --no-buffer`. One can expect seeing all of the result.

4. For test on L64 and Naive, go the the directory `L64/` and `Naive/` and type `dune runtest --no-buffer`. One should expect timeout on all of 
   the tests.


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
	
	
	