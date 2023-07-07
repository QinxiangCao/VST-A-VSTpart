## Build

Tested with Coq 8.12.2, OCaml 4.10.2, Menhir 20190924

1. Build patched [VST 2.5](https://github.com/QDelta/VST). Simply `make` in its directory.

   > Our modification of VST has two parts
   > - we prove some model level lemmas on preciseness of load/store (required to derive the conjunction rule)
   > - we define a stronger `semax` for VST-A, that removes bupd and restricts function specification being called to be precise

2. Build CompCert-A for the frontend. In its directory, run
   
   - `./configure x86_32-linux -clightgen -aclightgen -ignore-coq-version -no-runtime-lib`
   - `make`

3. Build SetsClass (https://bitbucket.org/qinxiang-SJTU/sets/src) for some examples. In its directory, run `make'.

4. In this directory, run `make config`, file `Makefile.config` will be generated, fill in there

   - `VSTDIR` is the path to (1)
   - `COMPCERTDIR` is the path to (1)/compcert
   - `COMPCERTADIR` is the path to (2)
   - `SETSDIR` is the path to (3)

5. Run `make`, the following will be built

   - the parsed results and proofs of test programs in `cprogs/`
   - the split function and its soundness proof in `csplit/`
   - the proof automation tactics in `floyd-seq/` (still working)


## Key Definitions & Lemmas of the stronger program logic

- `model_lemmas.v`: 
  - model level lemmas for precise read/write
    - `mapsto_join_andp_det`
    - `mapsto_join_andp_write_det`
  - `precise_funspec`: definition of precise function specification
  - two rewriting lemmas for function call (written in model level to make use of fash/unfash conveniently)
    - `func_at_unique_rewrite`:
      - rewrite `func_at` : `func_at (A P1 Q1) addr & func_at (A P2 Q2) addr |-- P1 x * (Q1 x -* R) <-> P2 x * (Q2 x -* R)`
    - `funspec_rewrite`:
      - rewrite state with subsumption: `gA gP gQ <: A P Q & P x * (Q x -* R) |-- EX x', gP x' * (gQ x' -* R)`
  
- `logic_lemmas.v`: 
  - transfer lemmas in `model_lemmas.v` to logic scope
  
- `strong.v`
  - definition of precise function specification in logic scope (identical to `model_lemmas.v`)
  - `semax`: our stronger program logic
  - inversion lemmas
  - `semax_noXXX_inv`: noreturn/nocontinue/nobreak lemmas
  - `semax_conj_rule`: conjunction rule
  - `aux_semax_extract_exists`
  - `semax_derives`: soundness w.r.t. VST's program logic
