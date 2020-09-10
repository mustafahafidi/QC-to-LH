#!/bin/bash
for i in $(cat properties.txt); do
  echo $i
  timeout 300s time zeno -m $i -I PropertiesZeno.hs
done

# # echo "waiting..."
# # wait
# # echo "done"

# echo "building summary"
# for i in $(find out/*.smt2); do
#   echo $i >> summary.txt
#   cat $i >> summary.txt
# done

