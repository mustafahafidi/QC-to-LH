# !/bin/bash
for i in $(cat cvc-vs-lhp/properties.txt); do
  echo $i
#   echo '(set-logic ALL_SUPPORTED)';
  (echo '(set-logic ALL)'; cat $i) > tmp/$(basename $i)
  # best options chosen based on VMCAI'15 companion website: http://lara.epfl.ch/~reynolds/VMCAI2015-ind/
  timeout 300s time cvc4  --lang=smt2.5 --quant-ind --quant-cf --conjecture-gen --conjecture-gen-per-round=3 --full-saturate-quant tmp/$(basename $i) >& out/$(basename $i) & 
done

# echo "waiting..."
# wait
# echo "done"

echo "building summary"
for i in $(find out/*.smt2); do
  echo $i >> summary.txt
  cat $i >> summary.txt
done

