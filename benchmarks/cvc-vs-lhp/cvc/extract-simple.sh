#!/bin/bash

# while read l; do grep -E "$l" -A 2 summary.txt; done < lhpsat.txt
comm -23 <(sort cvc/cvcsat-all.txt ) <(sort ../lhp/lhpsat-simp.txt ) > /tmp/cvcsat-simp.txt
while read l; do grep -E "$l" -A 2 summary.txt; done < /tmp/cvcsat-simp.txt

# comm -23 <(sort cvcsat.txt ) <(sort lhpsat.txt )