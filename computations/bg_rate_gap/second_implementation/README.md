# bg_rate_gap/second_implementation: second computation of the rate gaps Gamma_K

**Paper item:** Lemma `lem:bg-Gamma` (column Gamma_{k-1} of table `tab:bg-rate`, with its minimizing shapes).
Item C5 of the appendix on computations. Role: second implementation.

As for the first program (which lives in `../../bg_spider_comparison/conc.py`, see `../README.md`), the second
program for the rate gaps is kept together with the second program for the comparison with explicit spiders:
see `../../bg_spider_comparison/second_implementation/`, program `ind_gamma.py` (ball arithmetic, python-flint,
200 bits), its README and its `expected_output.txt`.

Run it there:

```sh
cd ../../bg_spider_comparison/second_implementation
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
python3 ind_gamma.py      # about 30 s
```

Result: the 22 values Gamma_K, K = 1..22, agree with table `tab:bg-rate` to the printed digits (the table rounds
down in the last digit), with the same minimizing shapes.
