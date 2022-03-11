## Build

using Coq 8.10

1. Install VST (`split` branch) from [https://github.com/ltzone/VST/tree/split], which is VST 2.5 with DeepEmbedded module opened (see commit 8de39a0).

2. CompCert-a dependency (not sure about version, see [https://jbox.sjtu.edu.cn/l/x1RXga])

3. Configure `Makefile.config`:

    ```
    VSTDIR= ...
    COMPCERTDIR= ...  (compcert-a dir)
    COQBIN= ...
    RAMIFYCOQDIR= ... (optional)
    ```

4. Make VST-A, `make` in the main directory (`make` may stop at RamifyCoq which is fine for this project)
   
5. Add `-Q ./vst-a/Split Split` to `_CoqProject`

6. `cd Split`,  Configure `CONFIGURE`

    ```
    VSTDIR= 
    COMPCERTDIR= (compcert in VST)
    COQBIN= 
    ```

7. in `Split`, `make`


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
- `soundness.v`: soundness w.r.t. `semax_aux` program logic defined in `strong.v`


## Dependent typed function based split algorithm

TBD