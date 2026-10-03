#!/bin/sh
# Sequential kernel sweep: one module at a time (each needs 6-13 GB).
cd "$(dirname "$0")/.." || exit 1
LOG=BGUnique/sweep.log
for n in $(seq 150 491); do
  s=$(date +%s)
  if lake build BGUnique.Sweep.S_$n > BGUnique/sweep_last.out 2>&1; then
    echo "OK $n $(( $(date +%s) - s ))s" >> $LOG
  else
    echo "FAIL $n $(( $(date +%s) - s ))s" >> $LOG
    cp BGUnique/sweep_last.out BGUnique/sweep_fail_$n.out
  fi
done
echo DONE >> $LOG
