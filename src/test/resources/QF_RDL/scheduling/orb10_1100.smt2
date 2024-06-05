(set-info :smt-lib-version 2.6)
(set-logic QF_RDL)
(set-info :source |
These benchmarks are used by the job-shop scheduling community and were
originaly from Andre Henning.  They were translated into CVC format by Bruno
Dutertre and Leonardo de Moura.  Contact demoura@csl.sri.com for more
information.

This benchmark was automatically translated into SMT-LIB format from
CVC format using CVC Lite
|)
(set-info :category "crafted")
(set-info :status sat)
(declare-fun cvclZero () Real)
(declare-fun Z () Real)
(declare-fun t_0_0 () Real)
(declare-fun t_0_1 () Real)
(declare-fun t_0_2 () Real)
(declare-fun t_0_3 () Real)
(declare-fun t_0_4 () Real)
(declare-fun t_0_5 () Real)
(declare-fun t_0_6 () Real)
(declare-fun t_0_7 () Real)
(declare-fun t_0_8 () Real)
(declare-fun t_0_9 () Real)
(declare-fun t_1_0 () Real)
(declare-fun t_1_1 () Real)
(declare-fun t_1_2 () Real)
(declare-fun t_1_3 () Real)
(declare-fun t_1_4 () Real)
(declare-fun t_1_5 () Real)
(declare-fun t_1_6 () Real)
(declare-fun t_1_7 () Real)
(declare-fun t_1_8 () Real)
(declare-fun t_1_9 () Real)
(declare-fun t_2_0 () Real)
(declare-fun t_2_1 () Real)
(declare-fun t_2_2 () Real)
(declare-fun t_2_3 () Real)
(declare-fun t_2_4 () Real)
(declare-fun t_2_5 () Real)
(declare-fun t_2_6 () Real)
(declare-fun t_2_7 () Real)
(declare-fun t_2_8 () Real)
(declare-fun t_2_9 () Real)
(declare-fun t_3_0 () Real)
(declare-fun t_3_1 () Real)
(declare-fun t_3_2 () Real)
(declare-fun t_3_3 () Real)
(declare-fun t_3_4 () Real)
(declare-fun t_3_5 () Real)
(declare-fun t_3_6 () Real)
(declare-fun t_3_7 () Real)
(declare-fun t_3_8 () Real)
(declare-fun t_3_9 () Real)
(declare-fun t_4_0 () Real)
(declare-fun t_4_1 () Real)
(declare-fun t_4_2 () Real)
(declare-fun t_4_3 () Real)
(declare-fun t_4_4 () Real)
(declare-fun t_4_5 () Real)
(declare-fun t_4_6 () Real)
(declare-fun t_4_7 () Real)
(declare-fun t_4_8 () Real)
(declare-fun t_4_9 () Real)
(declare-fun t_5_0 () Real)
(declare-fun t_5_1 () Real)
(declare-fun t_5_2 () Real)
(declare-fun t_5_3 () Real)
(declare-fun t_5_4 () Real)
(declare-fun t_5_5 () Real)
(declare-fun t_5_6 () Real)
(declare-fun t_5_7 () Real)
(declare-fun t_5_8 () Real)
(declare-fun t_5_9 () Real)
(declare-fun t_6_0 () Real)
(declare-fun t_6_1 () Real)
(declare-fun t_6_2 () Real)
(declare-fun t_6_3 () Real)
(declare-fun t_6_4 () Real)
(declare-fun t_6_5 () Real)
(declare-fun t_6_6 () Real)
(declare-fun t_6_7 () Real)
(declare-fun t_6_8 () Real)
(declare-fun t_6_9 () Real)
(declare-fun t_7_0 () Real)
(declare-fun t_7_1 () Real)
(declare-fun t_7_2 () Real)
(declare-fun t_7_3 () Real)
(declare-fun t_7_4 () Real)
(declare-fun t_7_5 () Real)
(declare-fun t_7_6 () Real)
(declare-fun t_7_7 () Real)
(declare-fun t_7_8 () Real)
(declare-fun t_7_9 () Real)
(declare-fun t_8_0 () Real)
(declare-fun t_8_1 () Real)
(declare-fun t_8_2 () Real)
(declare-fun t_8_3 () Real)
(declare-fun t_8_4 () Real)
(declare-fun t_8_5 () Real)
(declare-fun t_8_6 () Real)
(declare-fun t_8_7 () Real)
(declare-fun t_8_8 () Real)
(declare-fun t_8_9 () Real)
(declare-fun t_9_0 () Real)
(declare-fun t_9_1 () Real)
(declare-fun t_9_2 () Real)
(declare-fun t_9_3 () Real)
(declare-fun t_9_4 () Real)
(declare-fun t_9_5 () Real)
(declare-fun t_9_6 () Real)
(declare-fun t_9_7 () Real)
(declare-fun t_9_8 () Real)
(declare-fun t_9_9 () Real)
(assert (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (>= (- t_0_9 cvclZero) 0) (>= (- t_0_8 t_0_9) 66)) (>= (- t_0_0 t_0_8) 13)) (>= (- t_0_7 t_0_0) 93)) (>= (- t_0_6 t_0_7) 91)) (>= (- t_0_5 t_0_6) 14)) (>= (- t_0_3 t_0_5) 70)) (>= (- t_0_2 t_0_3) 99)) (>= (- t_0_4 t_0_2) 53)) (>= (- t_0_1 t_0_4) 86)) (>= (- Z t_0_1) 16)) (and (and (and (and (and (and (and (and (and (and (>= (- t_1_8 cvclZero) 0) (>= (- t_1_9 t_1_8) 34)) (>= (- t_1_0 t_1_9) 99)) (>= (- t_1_7 t_1_0) 62)) (>= (- t_1_5 t_1_7) 65)) (>= (- t_1_4 t_1_5) 62)) (>= (- t_1_6 t_1_4) 64)) (>= (- t_1_2 t_1_6) 21)) (>= (- t_1_3 t_1_2) 12)) (>= (- t_1_1 t_1_3) 9)) (>= (- Z t_1_1) 75))) (and (and (and (and (and (and (and (and (and (and (>= (- t_2_9 cvclZero) 0) (>= (- t_2_8 t_2_9) 12)) (>= (- t_2_7 t_2_8) 26)) (>= (- t_2_6 t_2_7) 64)) (>= (- t_2_4 t_2_6) 92)) (>= (- t_2_5 t_2_4) 67)) (>= (- t_2_3 t_2_5) 28)) (>= (- t_2_2 t_2_3) 66)) (>= (- t_2_1 t_2_2) 83)) (>= (- t_2_0 t_2_1) 38)) (>= (- Z t_2_0) 58))) (and (and (and (and (and (and (and (and (and (and (>= (- t_3_0 cvclZero) 0) (>= (- t_3_1 t_3_0) 77)) (>= (- t_3_3 t_3_1) 73)) (>= (- t_3_2 t_3_3) 82)) (>= (- t_3_6 t_3_2) 75)) (>= (- t_3_4 t_3_6) 84)) (>= (- t_3_5 t_3_4) 19)) (>= (- t_3_7 t_3_5) 18)) (>= (- t_3_8 t_3_7) 89)) (>= (- t_3_9 t_3_8) 8)) (>= (- Z t_3_9) 73))) (and (and (and (and (and (and (and (and (and (and (>= (- t_4_0 cvclZero) 0) (>= (- t_4_1 t_4_0) 34)) (>= (- t_4_7 t_4_1) 74)) (>= (- t_4_5 t_4_7) 48)) (>= (- t_4_4 t_4_5) 44)) (>= (- t_4_6 t_4_4) 92)) (>= (- t_4_3 t_4_6) 40)) (>= (- t_4_2 t_4_3) 60)) (>= (- t_4_8 t_4_2) 62)) (>= (- t_4_9 t_4_8) 22)) (>= (- Z t_4_9) 67))) (and (and (and (and (and (and (and (and (and (and (>= (- t_5_9 cvclZero) 0) (>= (- t_5_8 t_5_9) 8)) (>= (- t_5_3 t_5_8) 85)) (>= (- t_5_7 t_5_3) 58)) (>= (- t_5_5 t_5_7) 97)) (>= (- t_5_4 t_5_5) 92)) (>= (- t_5_6 t_5_4) 89)) (>= (- t_5_2 t_5_6) 75)) (>= (- t_5_1 t_5_2) 77)) (>= (- t_5_0 t_5_1) 95)) (>= (- Z t_5_0) 5))) (and (and (and (and (and (and (and (and (and (and (>= (- t_6_8 cvclZero) 0) (>= (- t_6_9 t_6_8) 52)) (>= (- t_6_6 t_6_9) 43)) (>= (- t_6_7 t_6_6) 5)) (>= (- t_6_5 t_6_7) 78)) (>= (- t_6_3 t_6_5) 12)) (>= (- t_6_4 t_6_3) 62)) (>= (- t_6_2 t_6_4) 21)) (>= (- t_6_1 t_6_2) 80)) (>= (- t_6_0 t_6_1) 60)) (>= (- Z t_6_0) 31))) (and (and (and (and (and (and (and (and (and (and (>= (- t_7_9 cvclZero) 0) (>= (- t_7_8 t_7_9) 81)) (>= (- t_7_7 t_7_8) 23)) (>= (- t_7_6 t_7_7) 23)) (>= (- t_7_4 t_7_6) 75)) (>= (- t_7_5 t_7_4) 78)) (>= (- t_7_3 t_7_5) 56)) (>= (- t_7_2 t_7_3) 51)) (>= (- t_7_1 t_7_2) 39)) (>= (- t_7_0 t_7_1) 53)) (>= (- Z t_7_0) 96))) (and (and (and (and (and (and (and (and (and (and (>= (- t_8_9 cvclZero) 0) (>= (- t_8_8 t_8_9) 79)) (>= (- t_8_2 t_8_8) 55)) (>= (- t_8_4 t_8_2) 88)) (>= (- t_8_5 t_8_4) 21)) (>= (- t_8_3 t_8_5) 83)) (>= (- t_8_6 t_8_3) 93)) (>= (- t_8_7 t_8_6) 47)) (>= (- t_8_0 t_8_7) 10)) (>= (- t_8_1 t_8_0) 63)) (>= (- Z t_8_1) 14))) (and (and (and (and (and (and (and (and (and (and (>= (- t_9_0 cvclZero) 0) (>= (- t_9_1 t_9_0) 43)) (>= (- t_9_2 t_9_1) 63)) (>= (- t_9_3 t_9_2) 83)) (>= (- t_9_4 t_9_3) 29)) (>= (- t_9_5 t_9_4) 52)) (>= (- t_9_6 t_9_5) 98)) (>= (- t_9_7 t_9_6) 54)) (>= (- t_9_8 t_9_7) 39)) (>= (- t_9_9 t_9_8) 33)) (>= (- Z t_9_9) 23))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and true (or (>= (- t_0_0 t_1_0) 62) (>= (- t_1_0 t_0_0) 93))) (or (>= (- t_0_0 t_2_0) 58) (>= (- t_2_0 t_0_0) 93))) (or (>= (- t_0_0 t_3_0) 77) (>= (- t_3_0 t_0_0) 93))) (or (>= (- t_0_0 t_4_0) 34) (>= (- t_4_0 t_0_0) 93))) (or (>= (- t_0_0 t_5_0) 5) (>= (- t_5_0 t_0_0) 93))) (or (>= (- t_0_0 t_6_0) 31) (>= (- t_6_0 t_0_0) 93))) (or (>= (- t_0_0 t_7_0) 96) (>= (- t_7_0 t_0_0) 93))) (or (>= (- t_0_0 t_8_0) 63) (>= (- t_8_0 t_0_0) 93))) (or (>= (- t_0_0 t_9_0) 43) (>= (- t_9_0 t_0_0) 93))) (or (>= (- t_1_0 t_2_0) 58) (>= (- t_2_0 t_1_0) 62))) (or (>= (- t_1_0 t_3_0) 77) (>= (- t_3_0 t_1_0) 62))) (or (>= (- t_1_0 t_4_0) 34) (>= (- t_4_0 t_1_0) 62))) (or (>= (- t_1_0 t_5_0) 5) (>= (- t_5_0 t_1_0) 62))) (or (>= (- t_1_0 t_6_0) 31) (>= (- t_6_0 t_1_0) 62))) (or (>= (- t_1_0 t_7_0) 96) (>= (- t_7_0 t_1_0) 62))) (or (>= (- t_1_0 t_8_0) 63) (>= (- t_8_0 t_1_0) 62))) (or (>= (- t_1_0 t_9_0) 43) (>= (- t_9_0 t_1_0) 62))) (or (>= (- t_2_0 t_3_0) 77) (>= (- t_3_0 t_2_0) 58))) (or (>= (- t_2_0 t_4_0) 34) (>= (- t_4_0 t_2_0) 58))) (or (>= (- t_2_0 t_5_0) 5) (>= (- t_5_0 t_2_0) 58))) (or (>= (- t_2_0 t_6_0) 31) (>= (- t_6_0 t_2_0) 58))) (or (>= (- t_2_0 t_7_0) 96) (>= (- t_7_0 t_2_0) 58))) (or (>= (- t_2_0 t_8_0) 63) (>= (- t_8_0 t_2_0) 58))) (or (>= (- t_2_0 t_9_0) 43) (>= (- t_9_0 t_2_0) 58))) (or (>= (- t_3_0 t_4_0) 34) (>= (- t_4_0 t_3_0) 77))) (or (>= (- t_3_0 t_5_0) 5) (>= (- t_5_0 t_3_0) 77))) (or (>= (- t_3_0 t_6_0) 31) (>= (- t_6_0 t_3_0) 77))) (or (>= (- t_3_0 t_7_0) 96) (>= (- t_7_0 t_3_0) 77))) (or (>= (- t_3_0 t_8_0) 63) (>= (- t_8_0 t_3_0) 77))) (or (>= (- t_3_0 t_9_0) 43) (>= (- t_9_0 t_3_0) 77))) (or (>= (- t_4_0 t_5_0) 5) (>= (- t_5_0 t_4_0) 34))) (or (>= (- t_4_0 t_6_0) 31) (>= (- t_6_0 t_4_0) 34))) (or (>= (- t_4_0 t_7_0) 96) (>= (- t_7_0 t_4_0) 34))) (or (>= (- t_4_0 t_8_0) 63) (>= (- t_8_0 t_4_0) 34))) (or (>= (- t_4_0 t_9_0) 43) (>= (- t_9_0 t_4_0) 34))) (or (>= (- t_5_0 t_6_0) 31) (>= (- t_6_0 t_5_0) 5))) (or (>= (- t_5_0 t_7_0) 96) (>= (- t_7_0 t_5_0) 5))) (or (>= (- t_5_0 t_8_0) 63) (>= (- t_8_0 t_5_0) 5))) (or (>= (- t_5_0 t_9_0) 43) (>= (- t_9_0 t_5_0) 5))) (or (>= (- t_6_0 t_7_0) 96) (>= (- t_7_0 t_6_0) 31))) (or (>= (- t_6_0 t_8_0) 63) (>= (- t_8_0 t_6_0) 31))) (or (>= (- t_6_0 t_9_0) 43) (>= (- t_9_0 t_6_0) 31))) (or (>= (- t_7_0 t_8_0) 63) (>= (- t_8_0 t_7_0) 96))) (or (>= (- t_7_0 t_9_0) 43) (>= (- t_9_0 t_7_0) 96))) (or (>= (- t_8_0 t_9_0) 43) (>= (- t_9_0 t_8_0) 63)))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and true (or (>= (- t_0_1 t_1_1) 75) (>= (- t_1_1 t_0_1) 16))) (or (>= (- t_0_1 t_2_1) 38) (>= (- t_2_1 t_0_1) 16))) (or (>= (- t_0_1 t_3_1) 73) (>= (- t_3_1 t_0_1) 16))) (or (>= (- t_0_1 t_4_1) 74) (>= (- t_4_1 t_0_1) 16))) (or (>= (- t_0_1 t_5_1) 95) (>= (- t_5_1 t_0_1) 16))) (or (>= (- t_0_1 t_6_1) 60) (>= (- t_6_1 t_0_1) 16))) (or (>= (- t_0_1 t_7_1) 53) (>= (- t_7_1 t_0_1) 16))) (or (>= (- t_0_1 t_8_1) 14) (>= (- t_8_1 t_0_1) 16))) (or (>= (- t_0_1 t_9_1) 63) (>= (- t_9_1 t_0_1) 16))) (or (>= (- t_1_1 t_2_1) 38) (>= (- t_2_1 t_1_1) 75))) (or (>= (- t_1_1 t_3_1) 73) (>= (- t_3_1 t_1_1) 75))) (or (>= (- t_1_1 t_4_1) 74) (>= (- t_4_1 t_1_1) 75))) (or (>= (- t_1_1 t_5_1) 95) (>= (- t_5_1 t_1_1) 75))) (or (>= (- t_1_1 t_6_1) 60) (>= (- t_6_1 t_1_1) 75))) (or (>= (- t_1_1 t_7_1) 53) (>= (- t_7_1 t_1_1) 75))) (or (>= (- t_1_1 t_8_1) 14) (>= (- t_8_1 t_1_1) 75))) (or (>= (- t_1_1 t_9_1) 63) (>= (- t_9_1 t_1_1) 75))) (or (>= (- t_2_1 t_3_1) 73) (>= (- t_3_1 t_2_1) 38))) (or (>= (- t_2_1 t_4_1) 74) (>= (- t_4_1 t_2_1) 38))) (or (>= (- t_2_1 t_5_1) 95) (>= (- t_5_1 t_2_1) 38))) (or (>= (- t_2_1 t_6_1) 60) (>= (- t_6_1 t_2_1) 38))) (or (>= (- t_2_1 t_7_1) 53) (>= (- t_7_1 t_2_1) 38))) (or (>= (- t_2_1 t_8_1) 14) (>= (- t_8_1 t_2_1) 38))) (or (>= (- t_2_1 t_9_1) 63) (>= (- t_9_1 t_2_1) 38))) (or (>= (- t_3_1 t_4_1) 74) (>= (- t_4_1 t_3_1) 73))) (or (>= (- t_3_1 t_5_1) 95) (>= (- t_5_1 t_3_1) 73))) (or (>= (- t_3_1 t_6_1) 60) (>= (- t_6_1 t_3_1) 73))) (or (>= (- t_3_1 t_7_1) 53) (>= (- t_7_1 t_3_1) 73))) (or (>= (- t_3_1 t_8_1) 14) (>= (- t_8_1 t_3_1) 73))) (or (>= (- t_3_1 t_9_1) 63) (>= (- t_9_1 t_3_1) 73))) (or (>= (- t_4_1 t_5_1) 95) (>= (- t_5_1 t_4_1) 74))) (or (>= (- t_4_1 t_6_1) 60) (>= (- t_6_1 t_4_1) 74))) (or (>= (- t_4_1 t_7_1) 53) (>= (- t_7_1 t_4_1) 74))) (or (>= (- t_4_1 t_8_1) 14) (>= (- t_8_1 t_4_1) 74))) (or (>= (- t_4_1 t_9_1) 63) (>= (- t_9_1 t_4_1) 74))) (or (>= (- t_5_1 t_6_1) 60) (>= (- t_6_1 t_5_1) 95))) (or (>= (- t_5_1 t_7_1) 53) (>= (- t_7_1 t_5_1) 95))) (or (>= (- t_5_1 t_8_1) 14) (>= (- t_8_1 t_5_1) 95))) (or (>= (- t_5_1 t_9_1) 63) (>= (- t_9_1 t_5_1) 95))) (or (>= (- t_6_1 t_7_1) 53) (>= (- t_7_1 t_6_1) 60))) (or (>= (- t_6_1 t_8_1) 14) (>= (- t_8_1 t_6_1) 60))) (or (>= (- t_6_1 t_9_1) 63) (>= (- t_9_1 t_6_1) 60))) (or (>= (- t_7_1 t_8_1) 14) (>= (- t_8_1 t_7_1) 53))) (or (>= (- t_7_1 t_9_1) 63) (>= (- t_9_1 t_7_1) 53))) (or (>= (- t_8_1 t_9_1) 63) (>= (- t_9_1 t_8_1) 14)))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and true (or (>= (- t_0_2 t_1_2) 12) (>= (- t_1_2 t_0_2) 53))) (or (>= (- t_0_2 t_2_2) 83) (>= (- t_2_2 t_0_2) 53))) (or (>= (- t_0_2 t_3_2) 75) (>= (- t_3_2 t_0_2) 53))) (or (>= (- t_0_2 t_4_2) 62) (>= (- t_4_2 t_0_2) 53))) (or (>= (- t_0_2 t_5_2) 77) (>= (- t_5_2 t_0_2) 53))) (or (>= (- t_0_2 t_6_2) 80) (>= (- t_6_2 t_0_2) 53))) (or (>= (- t_0_2 t_7_2) 39) (>= (- t_7_2 t_0_2) 53))) (or (>= (- t_0_2 t_8_2) 88) (>= (- t_8_2 t_0_2) 53))) (or (>= (- t_0_2 t_9_2) 83) (>= (- t_9_2 t_0_2) 53))) (or (>= (- t_1_2 t_2_2) 83) (>= (- t_2_2 t_1_2) 12))) (or (>= (- t_1_2 t_3_2) 75) (>= (- t_3_2 t_1_2) 12))) (or (>= (- t_1_2 t_4_2) 62) (>= (- t_4_2 t_1_2) 12))) (or (>= (- t_1_2 t_5_2) 77) (>= (- t_5_2 t_1_2) 12))) (or (>= (- t_1_2 t_6_2) 80) (>= (- t_6_2 t_1_2) 12))) (or (>= (- t_1_2 t_7_2) 39) (>= (- t_7_2 t_1_2) 12))) (or (>= (- t_1_2 t_8_2) 88) (>= (- t_8_2 t_1_2) 12))) (or (>= (- t_1_2 t_9_2) 83) (>= (- t_9_2 t_1_2) 12))) (or (>= (- t_2_2 t_3_2) 75) (>= (- t_3_2 t_2_2) 83))) (or (>= (- t_2_2 t_4_2) 62) (>= (- t_4_2 t_2_2) 83))) (or (>= (- t_2_2 t_5_2) 77) (>= (- t_5_2 t_2_2) 83))) (or (>= (- t_2_2 t_6_2) 80) (>= (- t_6_2 t_2_2) 83))) (or (>= (- t_2_2 t_7_2) 39) (>= (- t_7_2 t_2_2) 83))) (or (>= (- t_2_2 t_8_2) 88) (>= (- t_8_2 t_2_2) 83))) (or (>= (- t_2_2 t_9_2) 83) (>= (- t_9_2 t_2_2) 83))) (or (>= (- t_3_2 t_4_2) 62) (>= (- t_4_2 t_3_2) 75))) (or (>= (- t_3_2 t_5_2) 77) (>= (- t_5_2 t_3_2) 75))) (or (>= (- t_3_2 t_6_2) 80) (>= (- t_6_2 t_3_2) 75))) (or (>= (- t_3_2 t_7_2) 39) (>= (- t_7_2 t_3_2) 75))) (or (>= (- t_3_2 t_8_2) 88) (>= (- t_8_2 t_3_2) 75))) (or (>= (- t_3_2 t_9_2) 83) (>= (- t_9_2 t_3_2) 75))) (or (>= (- t_4_2 t_5_2) 77) (>= (- t_5_2 t_4_2) 62))) (or (>= (- t_4_2 t_6_2) 80) (>= (- t_6_2 t_4_2) 62))) (or (>= (- t_4_2 t_7_2) 39) (>= (- t_7_2 t_4_2) 62))) (or (>= (- t_4_2 t_8_2) 88) (>= (- t_8_2 t_4_2) 62))) (or (>= (- t_4_2 t_9_2) 83) (>= (- t_9_2 t_4_2) 62))) (or (>= (- t_5_2 t_6_2) 80) (>= (- t_6_2 t_5_2) 77))) (or (>= (- t_5_2 t_7_2) 39) (>= (- t_7_2 t_5_2) 77))) (or (>= (- t_5_2 t_8_2) 88) (>= (- t_8_2 t_5_2) 77))) (or (>= (- t_5_2 t_9_2) 83) (>= (- t_9_2 t_5_2) 77))) (or (>= (- t_6_2 t_7_2) 39) (>= (- t_7_2 t_6_2) 80))) (or (>= (- t_6_2 t_8_2) 88) (>= (- t_8_2 t_6_2) 80))) (or (>= (- t_6_2 t_9_2) 83) (>= (- t_9_2 t_6_2) 80))) (or (>= (- t_7_2 t_8_2) 88) (>= (- t_8_2 t_7_2) 39))) (or (>= (- t_7_2 t_9_2) 83) (>= (- t_9_2 t_7_2) 39))) (or (>= (- t_8_2 t_9_2) 83) (>= (- t_9_2 t_8_2) 88)))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and true (or (>= (- t_0_3 t_1_3) 9) (>= (- t_1_3 t_0_3) 99))) (or (>= (- t_0_3 t_2_3) 66) (>= (- t_2_3 t_0_3) 99))) (or (>= (- t_0_3 t_3_3) 82) (>= (- t_3_3 t_0_3) 99))) (or (>= (- t_0_3 t_4_3) 60) (>= (- t_4_3 t_0_3) 99))) (or (>= (- t_0_3 t_5_3) 58) (>= (- t_5_3 t_0_3) 99))) (or (>= (- t_0_3 t_6_3) 62) (>= (- t_6_3 t_0_3) 99))) (or (>= (- t_0_3 t_7_3) 51) (>= (- t_7_3 t_0_3) 99))) (or (>= (- t_0_3 t_8_3) 93) (>= (- t_8_3 t_0_3) 99))) (or (>= (- t_0_3 t_9_3) 29) (>= (- t_9_3 t_0_3) 99))) (or (>= (- t_1_3 t_2_3) 66) (>= (- t_2_3 t_1_3) 9))) (or (>= (- t_1_3 t_3_3) 82) (>= (- t_3_3 t_1_3) 9))) (or (>= (- t_1_3 t_4_3) 60) (>= (- t_4_3 t_1_3) 9))) (or (>= (- t_1_3 t_5_3) 58) (>= (- t_5_3 t_1_3) 9))) (or (>= (- t_1_3 t_6_3) 62) (>= (- t_6_3 t_1_3) 9))) (or (>= (- t_1_3 t_7_3) 51) (>= (- t_7_3 t_1_3) 9))) (or (>= (- t_1_3 t_8_3) 93) (>= (- t_8_3 t_1_3) 9))) (or (>= (- t_1_3 t_9_3) 29) (>= (- t_9_3 t_1_3) 9))) (or (>= (- t_2_3 t_3_3) 82) (>= (- t_3_3 t_2_3) 66))) (or (>= (- t_2_3 t_4_3) 60) (>= (- t_4_3 t_2_3) 66))) (or (>= (- t_2_3 t_5_3) 58) (>= (- t_5_3 t_2_3) 66))) (or (>= (- t_2_3 t_6_3) 62) (>= (- t_6_3 t_2_3) 66))) (or (>= (- t_2_3 t_7_3) 51) (>= (- t_7_3 t_2_3) 66))) (or (>= (- t_2_3 t_8_3) 93) (>= (- t_8_3 t_2_3) 66))) (or (>= (- t_2_3 t_9_3) 29) (>= (- t_9_3 t_2_3) 66))) (or (>= (- t_3_3 t_4_3) 60) (>= (- t_4_3 t_3_3) 82))) (or (>= (- t_3_3 t_5_3) 58) (>= (- t_5_3 t_3_3) 82))) (or (>= (- t_3_3 t_6_3) 62) (>= (- t_6_3 t_3_3) 82))) (or (>= (- t_3_3 t_7_3) 51) (>= (- t_7_3 t_3_3) 82))) (or (>= (- t_3_3 t_8_3) 93) (>= (- t_8_3 t_3_3) 82))) (or (>= (- t_3_3 t_9_3) 29) (>= (- t_9_3 t_3_3) 82))) (or (>= (- t_4_3 t_5_3) 58) (>= (- t_5_3 t_4_3) 60))) (or (>= (- t_4_3 t_6_3) 62) (>= (- t_6_3 t_4_3) 60))) (or (>= (- t_4_3 t_7_3) 51) (>= (- t_7_3 t_4_3) 60))) (or (>= (- t_4_3 t_8_3) 93) (>= (- t_8_3 t_4_3) 60))) (or (>= (- t_4_3 t_9_3) 29) (>= (- t_9_3 t_4_3) 60))) (or (>= (- t_5_3 t_6_3) 62) (>= (- t_6_3 t_5_3) 58))) (or (>= (- t_5_3 t_7_3) 51) (>= (- t_7_3 t_5_3) 58))) (or (>= (- t_5_3 t_8_3) 93) (>= (- t_8_3 t_5_3) 58))) (or (>= (- t_5_3 t_9_3) 29) (>= (- t_9_3 t_5_3) 58))) (or (>= (- t_6_3 t_7_3) 51) (>= (- t_7_3 t_6_3) 62))) (or (>= (- t_6_3 t_8_3) 93) (>= (- t_8_3 t_6_3) 62))) (or (>= (- t_6_3 t_9_3) 29) (>= (- t_9_3 t_6_3) 62))) (or (>= (- t_7_3 t_8_3) 93) (>= (- t_8_3 t_7_3) 51))) (or (>= (- t_7_3 t_9_3) 29) (>= (- t_9_3 t_7_3) 51))) (or (>= (- t_8_3 t_9_3) 29) (>= (- t_9_3 t_8_3) 93)))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and true (or (>= (- t_0_4 t_1_4) 64) (>= (- t_1_4 t_0_4) 86))) (or (>= (- t_0_4 t_2_4) 67) (>= (- t_2_4 t_0_4) 86))) (or (>= (- t_0_4 t_3_4) 19) (>= (- t_3_4 t_0_4) 86))) (or (>= (- t_0_4 t_4_4) 92) (>= (- t_4_4 t_0_4) 86))) (or (>= (- t_0_4 t_5_4) 89) (>= (- t_5_4 t_0_4) 86))) (or (>= (- t_0_4 t_6_4) 21) (>= (- t_6_4 t_0_4) 86))) (or (>= (- t_0_4 t_7_4) 78) (>= (- t_7_4 t_0_4) 86))) (or (>= (- t_0_4 t_8_4) 21) (>= (- t_8_4 t_0_4) 86))) (or (>= (- t_0_4 t_9_4) 52) (>= (- t_9_4 t_0_4) 86))) (or (>= (- t_1_4 t_2_4) 67) (>= (- t_2_4 t_1_4) 64))) (or (>= (- t_1_4 t_3_4) 19) (>= (- t_3_4 t_1_4) 64))) (or (>= (- t_1_4 t_4_4) 92) (>= (- t_4_4 t_1_4) 64))) (or (>= (- t_1_4 t_5_4) 89) (>= (- t_5_4 t_1_4) 64))) (or (>= (- t_1_4 t_6_4) 21) (>= (- t_6_4 t_1_4) 64))) (or (>= (- t_1_4 t_7_4) 78) (>= (- t_7_4 t_1_4) 64))) (or (>= (- t_1_4 t_8_4) 21) (>= (- t_8_4 t_1_4) 64))) (or (>= (- t_1_4 t_9_4) 52) (>= (- t_9_4 t_1_4) 64))) (or (>= (- t_2_4 t_3_4) 19) (>= (- t_3_4 t_2_4) 67))) (or (>= (- t_2_4 t_4_4) 92) (>= (- t_4_4 t_2_4) 67))) (or (>= (- t_2_4 t_5_4) 89) (>= (- t_5_4 t_2_4) 67))) (or (>= (- t_2_4 t_6_4) 21) (>= (- t_6_4 t_2_4) 67))) (or (>= (- t_2_4 t_7_4) 78) (>= (- t_7_4 t_2_4) 67))) (or (>= (- t_2_4 t_8_4) 21) (>= (- t_8_4 t_2_4) 67))) (or (>= (- t_2_4 t_9_4) 52) (>= (- t_9_4 t_2_4) 67))) (or (>= (- t_3_4 t_4_4) 92) (>= (- t_4_4 t_3_4) 19))) (or (>= (- t_3_4 t_5_4) 89) (>= (- t_5_4 t_3_4) 19))) (or (>= (- t_3_4 t_6_4) 21) (>= (- t_6_4 t_3_4) 19))) (or (>= (- t_3_4 t_7_4) 78) (>= (- t_7_4 t_3_4) 19))) (or (>= (- t_3_4 t_8_4) 21) (>= (- t_8_4 t_3_4) 19))) (or (>= (- t_3_4 t_9_4) 52) (>= (- t_9_4 t_3_4) 19))) (or (>= (- t_4_4 t_5_4) 89) (>= (- t_5_4 t_4_4) 92))) (or (>= (- t_4_4 t_6_4) 21) (>= (- t_6_4 t_4_4) 92))) (or (>= (- t_4_4 t_7_4) 78) (>= (- t_7_4 t_4_4) 92))) (or (>= (- t_4_4 t_8_4) 21) (>= (- t_8_4 t_4_4) 92))) (or (>= (- t_4_4 t_9_4) 52) (>= (- t_9_4 t_4_4) 92))) (or (>= (- t_5_4 t_6_4) 21) (>= (- t_6_4 t_5_4) 89))) (or (>= (- t_5_4 t_7_4) 78) (>= (- t_7_4 t_5_4) 89))) (or (>= (- t_5_4 t_8_4) 21) (>= (- t_8_4 t_5_4) 89))) (or (>= (- t_5_4 t_9_4) 52) (>= (- t_9_4 t_5_4) 89))) (or (>= (- t_6_4 t_7_4) 78) (>= (- t_7_4 t_6_4) 21))) (or (>= (- t_6_4 t_8_4) 21) (>= (- t_8_4 t_6_4) 21))) (or (>= (- t_6_4 t_9_4) 52) (>= (- t_9_4 t_6_4) 21))) (or (>= (- t_7_4 t_8_4) 21) (>= (- t_8_4 t_7_4) 78))) (or (>= (- t_7_4 t_9_4) 52) (>= (- t_9_4 t_7_4) 78))) (or (>= (- t_8_4 t_9_4) 52) (>= (- t_9_4 t_8_4) 21)))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and true (or (>= (- t_0_5 t_1_5) 62) (>= (- t_1_5 t_0_5) 70))) (or (>= (- t_0_5 t_2_5) 28) (>= (- t_2_5 t_0_5) 70))) (or (>= (- t_0_5 t_3_5) 18) (>= (- t_3_5 t_0_5) 70))) (or (>= (- t_0_5 t_4_5) 44) (>= (- t_4_5 t_0_5) 70))) (or (>= (- t_0_5 t_5_5) 92) (>= (- t_5_5 t_0_5) 70))) (or (>= (- t_0_5 t_6_5) 12) (>= (- t_6_5 t_0_5) 70))) (or (>= (- t_0_5 t_7_5) 56) (>= (- t_7_5 t_0_5) 70))) (or (>= (- t_0_5 t_8_5) 83) (>= (- t_8_5 t_0_5) 70))) (or (>= (- t_0_5 t_9_5) 98) (>= (- t_9_5 t_0_5) 70))) (or (>= (- t_1_5 t_2_5) 28) (>= (- t_2_5 t_1_5) 62))) (or (>= (- t_1_5 t_3_5) 18) (>= (- t_3_5 t_1_5) 62))) (or (>= (- t_1_5 t_4_5) 44) (>= (- t_4_5 t_1_5) 62))) (or (>= (- t_1_5 t_5_5) 92) (>= (- t_5_5 t_1_5) 62))) (or (>= (- t_1_5 t_6_5) 12) (>= (- t_6_5 t_1_5) 62))) (or (>= (- t_1_5 t_7_5) 56) (>= (- t_7_5 t_1_5) 62))) (or (>= (- t_1_5 t_8_5) 83) (>= (- t_8_5 t_1_5) 62))) (or (>= (- t_1_5 t_9_5) 98) (>= (- t_9_5 t_1_5) 62))) (or (>= (- t_2_5 t_3_5) 18) (>= (- t_3_5 t_2_5) 28))) (or (>= (- t_2_5 t_4_5) 44) (>= (- t_4_5 t_2_5) 28))) (or (>= (- t_2_5 t_5_5) 92) (>= (- t_5_5 t_2_5) 28))) (or (>= (- t_2_5 t_6_5) 12) (>= (- t_6_5 t_2_5) 28))) (or (>= (- t_2_5 t_7_5) 56) (>= (- t_7_5 t_2_5) 28))) (or (>= (- t_2_5 t_8_5) 83) (>= (- t_8_5 t_2_5) 28))) (or (>= (- t_2_5 t_9_5) 98) (>= (- t_9_5 t_2_5) 28))) (or (>= (- t_3_5 t_4_5) 44) (>= (- t_4_5 t_3_5) 18))) (or (>= (- t_3_5 t_5_5) 92) (>= (- t_5_5 t_3_5) 18))) (or (>= (- t_3_5 t_6_5) 12) (>= (- t_6_5 t_3_5) 18))) (or (>= (- t_3_5 t_7_5) 56) (>= (- t_7_5 t_3_5) 18))) (or (>= (- t_3_5 t_8_5) 83) (>= (- t_8_5 t_3_5) 18))) (or (>= (- t_3_5 t_9_5) 98) (>= (- t_9_5 t_3_5) 18))) (or (>= (- t_4_5 t_5_5) 92) (>= (- t_5_5 t_4_5) 44))) (or (>= (- t_4_5 t_6_5) 12) (>= (- t_6_5 t_4_5) 44))) (or (>= (- t_4_5 t_7_5) 56) (>= (- t_7_5 t_4_5) 44))) (or (>= (- t_4_5 t_8_5) 83) (>= (- t_8_5 t_4_5) 44))) (or (>= (- t_4_5 t_9_5) 98) (>= (- t_9_5 t_4_5) 44))) (or (>= (- t_5_5 t_6_5) 12) (>= (- t_6_5 t_5_5) 92))) (or (>= (- t_5_5 t_7_5) 56) (>= (- t_7_5 t_5_5) 92))) (or (>= (- t_5_5 t_8_5) 83) (>= (- t_8_5 t_5_5) 92))) (or (>= (- t_5_5 t_9_5) 98) (>= (- t_9_5 t_5_5) 92))) (or (>= (- t_6_5 t_7_5) 56) (>= (- t_7_5 t_6_5) 12))) (or (>= (- t_6_5 t_8_5) 83) (>= (- t_8_5 t_6_5) 12))) (or (>= (- t_6_5 t_9_5) 98) (>= (- t_9_5 t_6_5) 12))) (or (>= (- t_7_5 t_8_5) 83) (>= (- t_8_5 t_7_5) 56))) (or (>= (- t_7_5 t_9_5) 98) (>= (- t_9_5 t_7_5) 56))) (or (>= (- t_8_5 t_9_5) 98) (>= (- t_9_5 t_8_5) 83)))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and true (or (>= (- t_0_6 t_1_6) 21) (>= (- t_1_6 t_0_6) 14))) (or (>= (- t_0_6 t_2_6) 92) (>= (- t_2_6 t_0_6) 14))) (or (>= (- t_0_6 t_3_6) 84) (>= (- t_3_6 t_0_6) 14))) (or (>= (- t_0_6 t_4_6) 40) (>= (- t_4_6 t_0_6) 14))) (or (>= (- t_0_6 t_5_6) 75) (>= (- t_5_6 t_0_6) 14))) (or (>= (- t_0_6 t_6_6) 5) (>= (- t_6_6 t_0_6) 14))) (or (>= (- t_0_6 t_7_6) 75) (>= (- t_7_6 t_0_6) 14))) (or (>= (- t_0_6 t_8_6) 47) (>= (- t_8_6 t_0_6) 14))) (or (>= (- t_0_6 t_9_6) 54) (>= (- t_9_6 t_0_6) 14))) (or (>= (- t_1_6 t_2_6) 92) (>= (- t_2_6 t_1_6) 21))) (or (>= (- t_1_6 t_3_6) 84) (>= (- t_3_6 t_1_6) 21))) (or (>= (- t_1_6 t_4_6) 40) (>= (- t_4_6 t_1_6) 21))) (or (>= (- t_1_6 t_5_6) 75) (>= (- t_5_6 t_1_6) 21))) (or (>= (- t_1_6 t_6_6) 5) (>= (- t_6_6 t_1_6) 21))) (or (>= (- t_1_6 t_7_6) 75) (>= (- t_7_6 t_1_6) 21))) (or (>= (- t_1_6 t_8_6) 47) (>= (- t_8_6 t_1_6) 21))) (or (>= (- t_1_6 t_9_6) 54) (>= (- t_9_6 t_1_6) 21))) (or (>= (- t_2_6 t_3_6) 84) (>= (- t_3_6 t_2_6) 92))) (or (>= (- t_2_6 t_4_6) 40) (>= (- t_4_6 t_2_6) 92))) (or (>= (- t_2_6 t_5_6) 75) (>= (- t_5_6 t_2_6) 92))) (or (>= (- t_2_6 t_6_6) 5) (>= (- t_6_6 t_2_6) 92))) (or (>= (- t_2_6 t_7_6) 75) (>= (- t_7_6 t_2_6) 92))) (or (>= (- t_2_6 t_8_6) 47) (>= (- t_8_6 t_2_6) 92))) (or (>= (- t_2_6 t_9_6) 54) (>= (- t_9_6 t_2_6) 92))) (or (>= (- t_3_6 t_4_6) 40) (>= (- t_4_6 t_3_6) 84))) (or (>= (- t_3_6 t_5_6) 75) (>= (- t_5_6 t_3_6) 84))) (or (>= (- t_3_6 t_6_6) 5) (>= (- t_6_6 t_3_6) 84))) (or (>= (- t_3_6 t_7_6) 75) (>= (- t_7_6 t_3_6) 84))) (or (>= (- t_3_6 t_8_6) 47) (>= (- t_8_6 t_3_6) 84))) (or (>= (- t_3_6 t_9_6) 54) (>= (- t_9_6 t_3_6) 84))) (or (>= (- t_4_6 t_5_6) 75) (>= (- t_5_6 t_4_6) 40))) (or (>= (- t_4_6 t_6_6) 5) (>= (- t_6_6 t_4_6) 40))) (or (>= (- t_4_6 t_7_6) 75) (>= (- t_7_6 t_4_6) 40))) (or (>= (- t_4_6 t_8_6) 47) (>= (- t_8_6 t_4_6) 40))) (or (>= (- t_4_6 t_9_6) 54) (>= (- t_9_6 t_4_6) 40))) (or (>= (- t_5_6 t_6_6) 5) (>= (- t_6_6 t_5_6) 75))) (or (>= (- t_5_6 t_7_6) 75) (>= (- t_7_6 t_5_6) 75))) (or (>= (- t_5_6 t_8_6) 47) (>= (- t_8_6 t_5_6) 75))) (or (>= (- t_5_6 t_9_6) 54) (>= (- t_9_6 t_5_6) 75))) (or (>= (- t_6_6 t_7_6) 75) (>= (- t_7_6 t_6_6) 5))) (or (>= (- t_6_6 t_8_6) 47) (>= (- t_8_6 t_6_6) 5))) (or (>= (- t_6_6 t_9_6) 54) (>= (- t_9_6 t_6_6) 5))) (or (>= (- t_7_6 t_8_6) 47) (>= (- t_8_6 t_7_6) 75))) (or (>= (- t_7_6 t_9_6) 54) (>= (- t_9_6 t_7_6) 75))) (or (>= (- t_8_6 t_9_6) 54) (>= (- t_9_6 t_8_6) 47)))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and true (or (>= (- t_0_7 t_1_7) 65) (>= (- t_1_7 t_0_7) 91))) (or (>= (- t_0_7 t_2_7) 64) (>= (- t_2_7 t_0_7) 91))) (or (>= (- t_0_7 t_3_7) 89) (>= (- t_3_7 t_0_7) 91))) (or (>= (- t_0_7 t_4_7) 48) (>= (- t_4_7 t_0_7) 91))) (or (>= (- t_0_7 t_5_7) 97) (>= (- t_5_7 t_0_7) 91))) (or (>= (- t_0_7 t_6_7) 78) (>= (- t_6_7 t_0_7) 91))) (or (>= (- t_0_7 t_7_7) 23) (>= (- t_7_7 t_0_7) 91))) (or (>= (- t_0_7 t_8_7) 10) (>= (- t_8_7 t_0_7) 91))) (or (>= (- t_0_7 t_9_7) 39) (>= (- t_9_7 t_0_7) 91))) (or (>= (- t_1_7 t_2_7) 64) (>= (- t_2_7 t_1_7) 65))) (or (>= (- t_1_7 t_3_7) 89) (>= (- t_3_7 t_1_7) 65))) (or (>= (- t_1_7 t_4_7) 48) (>= (- t_4_7 t_1_7) 65))) (or (>= (- t_1_7 t_5_7) 97) (>= (- t_5_7 t_1_7) 65))) (or (>= (- t_1_7 t_6_7) 78) (>= (- t_6_7 t_1_7) 65))) (or (>= (- t_1_7 t_7_7) 23) (>= (- t_7_7 t_1_7) 65))) (or (>= (- t_1_7 t_8_7) 10) (>= (- t_8_7 t_1_7) 65))) (or (>= (- t_1_7 t_9_7) 39) (>= (- t_9_7 t_1_7) 65))) (or (>= (- t_2_7 t_3_7) 89) (>= (- t_3_7 t_2_7) 64))) (or (>= (- t_2_7 t_4_7) 48) (>= (- t_4_7 t_2_7) 64))) (or (>= (- t_2_7 t_5_7) 97) (>= (- t_5_7 t_2_7) 64))) (or (>= (- t_2_7 t_6_7) 78) (>= (- t_6_7 t_2_7) 64))) (or (>= (- t_2_7 t_7_7) 23) (>= (- t_7_7 t_2_7) 64))) (or (>= (- t_2_7 t_8_7) 10) (>= (- t_8_7 t_2_7) 64))) (or (>= (- t_2_7 t_9_7) 39) (>= (- t_9_7 t_2_7) 64))) (or (>= (- t_3_7 t_4_7) 48) (>= (- t_4_7 t_3_7) 89))) (or (>= (- t_3_7 t_5_7) 97) (>= (- t_5_7 t_3_7) 89))) (or (>= (- t_3_7 t_6_7) 78) (>= (- t_6_7 t_3_7) 89))) (or (>= (- t_3_7 t_7_7) 23) (>= (- t_7_7 t_3_7) 89))) (or (>= (- t_3_7 t_8_7) 10) (>= (- t_8_7 t_3_7) 89))) (or (>= (- t_3_7 t_9_7) 39) (>= (- t_9_7 t_3_7) 89))) (or (>= (- t_4_7 t_5_7) 97) (>= (- t_5_7 t_4_7) 48))) (or (>= (- t_4_7 t_6_7) 78) (>= (- t_6_7 t_4_7) 48))) (or (>= (- t_4_7 t_7_7) 23) (>= (- t_7_7 t_4_7) 48))) (or (>= (- t_4_7 t_8_7) 10) (>= (- t_8_7 t_4_7) 48))) (or (>= (- t_4_7 t_9_7) 39) (>= (- t_9_7 t_4_7) 48))) (or (>= (- t_5_7 t_6_7) 78) (>= (- t_6_7 t_5_7) 97))) (or (>= (- t_5_7 t_7_7) 23) (>= (- t_7_7 t_5_7) 97))) (or (>= (- t_5_7 t_8_7) 10) (>= (- t_8_7 t_5_7) 97))) (or (>= (- t_5_7 t_9_7) 39) (>= (- t_9_7 t_5_7) 97))) (or (>= (- t_6_7 t_7_7) 23) (>= (- t_7_7 t_6_7) 78))) (or (>= (- t_6_7 t_8_7) 10) (>= (- t_8_7 t_6_7) 78))) (or (>= (- t_6_7 t_9_7) 39) (>= (- t_9_7 t_6_7) 78))) (or (>= (- t_7_7 t_8_7) 10) (>= (- t_8_7 t_7_7) 23))) (or (>= (- t_7_7 t_9_7) 39) (>= (- t_9_7 t_7_7) 23))) (or (>= (- t_8_7 t_9_7) 39) (>= (- t_9_7 t_8_7) 10)))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and true (or (>= (- t_0_8 t_1_8) 34) (>= (- t_1_8 t_0_8) 13))) (or (>= (- t_0_8 t_2_8) 26) (>= (- t_2_8 t_0_8) 13))) (or (>= (- t_0_8 t_3_8) 8) (>= (- t_3_8 t_0_8) 13))) (or (>= (- t_0_8 t_4_8) 22) (>= (- t_4_8 t_0_8) 13))) (or (>= (- t_0_8 t_5_8) 85) (>= (- t_5_8 t_0_8) 13))) (or (>= (- t_0_8 t_6_8) 52) (>= (- t_6_8 t_0_8) 13))) (or (>= (- t_0_8 t_7_8) 23) (>= (- t_7_8 t_0_8) 13))) (or (>= (- t_0_8 t_8_8) 55) (>= (- t_8_8 t_0_8) 13))) (or (>= (- t_0_8 t_9_8) 33) (>= (- t_9_8 t_0_8) 13))) (or (>= (- t_1_8 t_2_8) 26) (>= (- t_2_8 t_1_8) 34))) (or (>= (- t_1_8 t_3_8) 8) (>= (- t_3_8 t_1_8) 34))) (or (>= (- t_1_8 t_4_8) 22) (>= (- t_4_8 t_1_8) 34))) (or (>= (- t_1_8 t_5_8) 85) (>= (- t_5_8 t_1_8) 34))) (or (>= (- t_1_8 t_6_8) 52) (>= (- t_6_8 t_1_8) 34))) (or (>= (- t_1_8 t_7_8) 23) (>= (- t_7_8 t_1_8) 34))) (or (>= (- t_1_8 t_8_8) 55) (>= (- t_8_8 t_1_8) 34))) (or (>= (- t_1_8 t_9_8) 33) (>= (- t_9_8 t_1_8) 34))) (or (>= (- t_2_8 t_3_8) 8) (>= (- t_3_8 t_2_8) 26))) (or (>= (- t_2_8 t_4_8) 22) (>= (- t_4_8 t_2_8) 26))) (or (>= (- t_2_8 t_5_8) 85) (>= (- t_5_8 t_2_8) 26))) (or (>= (- t_2_8 t_6_8) 52) (>= (- t_6_8 t_2_8) 26))) (or (>= (- t_2_8 t_7_8) 23) (>= (- t_7_8 t_2_8) 26))) (or (>= (- t_2_8 t_8_8) 55) (>= (- t_8_8 t_2_8) 26))) (or (>= (- t_2_8 t_9_8) 33) (>= (- t_9_8 t_2_8) 26))) (or (>= (- t_3_8 t_4_8) 22) (>= (- t_4_8 t_3_8) 8))) (or (>= (- t_3_8 t_5_8) 85) (>= (- t_5_8 t_3_8) 8))) (or (>= (- t_3_8 t_6_8) 52) (>= (- t_6_8 t_3_8) 8))) (or (>= (- t_3_8 t_7_8) 23) (>= (- t_7_8 t_3_8) 8))) (or (>= (- t_3_8 t_8_8) 55) (>= (- t_8_8 t_3_8) 8))) (or (>= (- t_3_8 t_9_8) 33) (>= (- t_9_8 t_3_8) 8))) (or (>= (- t_4_8 t_5_8) 85) (>= (- t_5_8 t_4_8) 22))) (or (>= (- t_4_8 t_6_8) 52) (>= (- t_6_8 t_4_8) 22))) (or (>= (- t_4_8 t_7_8) 23) (>= (- t_7_8 t_4_8) 22))) (or (>= (- t_4_8 t_8_8) 55) (>= (- t_8_8 t_4_8) 22))) (or (>= (- t_4_8 t_9_8) 33) (>= (- t_9_8 t_4_8) 22))) (or (>= (- t_5_8 t_6_8) 52) (>= (- t_6_8 t_5_8) 85))) (or (>= (- t_5_8 t_7_8) 23) (>= (- t_7_8 t_5_8) 85))) (or (>= (- t_5_8 t_8_8) 55) (>= (- t_8_8 t_5_8) 85))) (or (>= (- t_5_8 t_9_8) 33) (>= (- t_9_8 t_5_8) 85))) (or (>= (- t_6_8 t_7_8) 23) (>= (- t_7_8 t_6_8) 52))) (or (>= (- t_6_8 t_8_8) 55) (>= (- t_8_8 t_6_8) 52))) (or (>= (- t_6_8 t_9_8) 33) (>= (- t_9_8 t_6_8) 52))) (or (>= (- t_7_8 t_8_8) 55) (>= (- t_8_8 t_7_8) 23))) (or (>= (- t_7_8 t_9_8) 33) (>= (- t_9_8 t_7_8) 23))) (or (>= (- t_8_8 t_9_8) 33) (>= (- t_9_8 t_8_8) 55)))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and true (or (>= (- t_0_9 t_1_9) 99) (>= (- t_1_9 t_0_9) 66))) (or (>= (- t_0_9 t_2_9) 12) (>= (- t_2_9 t_0_9) 66))) (or (>= (- t_0_9 t_3_9) 73) (>= (- t_3_9 t_0_9) 66))) (or (>= (- t_0_9 t_4_9) 67) (>= (- t_4_9 t_0_9) 66))) (or (>= (- t_0_9 t_5_9) 8) (>= (- t_5_9 t_0_9) 66))) (or (>= (- t_0_9 t_6_9) 43) (>= (- t_6_9 t_0_9) 66))) (or (>= (- t_0_9 t_7_9) 81) (>= (- t_7_9 t_0_9) 66))) (or (>= (- t_0_9 t_8_9) 79) (>= (- t_8_9 t_0_9) 66))) (or (>= (- t_0_9 t_9_9) 23) (>= (- t_9_9 t_0_9) 66))) (or (>= (- t_1_9 t_2_9) 12) (>= (- t_2_9 t_1_9) 99))) (or (>= (- t_1_9 t_3_9) 73) (>= (- t_3_9 t_1_9) 99))) (or (>= (- t_1_9 t_4_9) 67) (>= (- t_4_9 t_1_9) 99))) (or (>= (- t_1_9 t_5_9) 8) (>= (- t_5_9 t_1_9) 99))) (or (>= (- t_1_9 t_6_9) 43) (>= (- t_6_9 t_1_9) 99))) (or (>= (- t_1_9 t_7_9) 81) (>= (- t_7_9 t_1_9) 99))) (or (>= (- t_1_9 t_8_9) 79) (>= (- t_8_9 t_1_9) 99))) (or (>= (- t_1_9 t_9_9) 23) (>= (- t_9_9 t_1_9) 99))) (or (>= (- t_2_9 t_3_9) 73) (>= (- t_3_9 t_2_9) 12))) (or (>= (- t_2_9 t_4_9) 67) (>= (- t_4_9 t_2_9) 12))) (or (>= (- t_2_9 t_5_9) 8) (>= (- t_5_9 t_2_9) 12))) (or (>= (- t_2_9 t_6_9) 43) (>= (- t_6_9 t_2_9) 12))) (or (>= (- t_2_9 t_7_9) 81) (>= (- t_7_9 t_2_9) 12))) (or (>= (- t_2_9 t_8_9) 79) (>= (- t_8_9 t_2_9) 12))) (or (>= (- t_2_9 t_9_9) 23) (>= (- t_9_9 t_2_9) 12))) (or (>= (- t_3_9 t_4_9) 67) (>= (- t_4_9 t_3_9) 73))) (or (>= (- t_3_9 t_5_9) 8) (>= (- t_5_9 t_3_9) 73))) (or (>= (- t_3_9 t_6_9) 43) (>= (- t_6_9 t_3_9) 73))) (or (>= (- t_3_9 t_7_9) 81) (>= (- t_7_9 t_3_9) 73))) (or (>= (- t_3_9 t_8_9) 79) (>= (- t_8_9 t_3_9) 73))) (or (>= (- t_3_9 t_9_9) 23) (>= (- t_9_9 t_3_9) 73))) (or (>= (- t_4_9 t_5_9) 8) (>= (- t_5_9 t_4_9) 67))) (or (>= (- t_4_9 t_6_9) 43) (>= (- t_6_9 t_4_9) 67))) (or (>= (- t_4_9 t_7_9) 81) (>= (- t_7_9 t_4_9) 67))) (or (>= (- t_4_9 t_8_9) 79) (>= (- t_8_9 t_4_9) 67))) (or (>= (- t_4_9 t_9_9) 23) (>= (- t_9_9 t_4_9) 67))) (or (>= (- t_5_9 t_6_9) 43) (>= (- t_6_9 t_5_9) 8))) (or (>= (- t_5_9 t_7_9) 81) (>= (- t_7_9 t_5_9) 8))) (or (>= (- t_5_9 t_8_9) 79) (>= (- t_8_9 t_5_9) 8))) (or (>= (- t_5_9 t_9_9) 23) (>= (- t_9_9 t_5_9) 8))) (or (>= (- t_6_9 t_7_9) 81) (>= (- t_7_9 t_6_9) 43))) (or (>= (- t_6_9 t_8_9) 79) (>= (- t_8_9 t_6_9) 43))) (or (>= (- t_6_9 t_9_9) 23) (>= (- t_9_9 t_6_9) 43))) (or (>= (- t_7_9 t_8_9) 79) (>= (- t_8_9 t_7_9) 81))) (or (>= (- t_7_9 t_9_9) 23) (>= (- t_9_9 t_7_9) 81))) (or (>= (- t_8_9 t_9_9) 23) (>= (- t_9_9 t_8_9) 79)))) (<= (- Z cvclZero) 1100)))
(check-sat)
(exit)
