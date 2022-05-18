## Build

using Coq 8.10

1. Install VST (`split` branch) from [https://github.com/ltzone/VST/tree/split], which is VST 2.5 with DeepEmbedded module opened (see commit 8de39a0). can be installed with `make -j`

2. Install CompCert-a dependency from [https://bitbucket.org/qinxiang-SJTU/compcert-clightgen-comment/src/nop_cmt/], first `./configure` and then `make`

3. run `make`, an CONFIGURE file will be generated, fill in there 
   - `RamifyCoq` can be left as empty, we do not depend on it for now
   - `VSTDIR` is the path to (1)
   - `COMPCERTDIR` is the path to (1)/compcert
   - `COMPCERTADIR` is the path to (2)

4. run `make` again, the following will be built
   - frontend, `aclightgen`
   - the parsed results of test progs in `cprogs/`
   - the split function and its soundness proof in `CSplit/`
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
  - `semax_aux`: our stronger program logic
  - inversion lemmas
  - `semax_aux_noXXX_inv`: noreturn/nocontinue/nobreak lemmas
  - `semax_aux_conj_rule`: conjunction rule
  - `aux_semax_extract_exists`
  - `semax_aux_derives`: soundness w.r.t. VST's program logic

## Rule based split algorithm

- `defs.v` `rule.v` `semantics.v`: definition of rules and semantics
- `soundness.v`: soundness w.r.t. `semax` program logic defined in `strong.v`



## AClightgen frontend:

Can make frontend alone
```
make -f Makefile.frontend 
```

Usage:
```
./aclightgen cprogs/sgn.c -normalize -A -V cprogs.sgn_def -V cprogs.sgn_prog -o cprogs/sgn_annot.v
```

> Still working on the frontend, so the current split result is not ideal.