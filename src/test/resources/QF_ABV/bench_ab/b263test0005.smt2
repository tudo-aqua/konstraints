(set-info :smt-lib-version 2.6)
(set-logic QF_ABV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun s () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun buf () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (= (select buf (_ bv0 32)) (_ bv0 8)))
(assert (= (select buf (_ bv1 32)) (_ bv0 8)))
(assert (= (select buf (_ bv2 32)) (_ bv0 8)))
(assert (= (select buf (_ bv3 32)) (_ bv0 8)))
(assert (= (select buf (_ bv4 32)) (_ bv0 8)))
(assert (= (select buf (_ bv5 32)) (_ bv0 8)))
(assert (= (select buf (_ bv6 32)) (_ bv0 8)))
(assert (= (select buf (_ bv7 32)) (_ bv0 8)))
(assert (= (select buf (_ bv8 32)) (_ bv0 8)))
(assert (= (select buf (_ bv9 32)) (_ bv0 8)))
(assert (= (select buf (_ bv10 32)) (_ bv0 8)))
(assert (= (select buf (_ bv11 32)) (_ bv0 8)))
(assert (= (select buf (_ bv12 32)) (_ bv0 8)))
(assert (= (select buf (_ bv13 32)) (_ bv0 8)))
(assert (= (select buf (_ bv14 32)) (_ bv0 8)))
(assert (= (select buf (_ bv15 32)) (_ bv0 8)))
(assert (= (select buf (_ bv16 32)) (_ bv0 8)))
(assert (= (select buf (_ bv17 32)) (_ bv0 8)))
(assert (= (select buf (_ bv18 32)) (_ bv0 8)))
(assert (= (select buf (_ bv19 32)) (_ bv0 8)))
(assert (= (select buf (_ bv20 32)) (_ bv0 8)))
(assert (= (select buf (_ bv21 32)) (_ bv0 8)))
(assert (= (select buf (_ bv22 32)) (_ bv0 8)))
(assert (= (select buf (_ bv23 32)) (_ bv0 8)))
(assert (= (select buf (_ bv24 32)) (_ bv0 8)))
(assert (= (select buf (_ bv25 32)) (_ bv0 8)))
(assert (= (select buf (_ bv26 32)) (_ bv0 8)))
(assert (= (select buf (_ bv27 32)) (_ bv0 8)))
(assert (= (select buf (_ bv28 32)) (_ bv0 8)))
(assert (= (select buf (_ bv29 32)) (_ bv0 8)))
(assert (= (select buf (_ bv30 32)) (_ bv0 8)))
(assert (= (select buf (_ bv31 32)) (_ bv0 8)))
(assert (= (select buf (_ bv32 32)) (_ bv1 8)))
(assert (= (select buf (_ bv33 32)) (_ bv0 8)))
(assert (= (select buf (_ bv34 32)) (_ bv0 8)))
(assert (= (select buf (_ bv35 32)) (_ bv0 8)))
(assert (= (select buf (_ bv36 32)) (_ bv0 8)))
(assert (= (select buf (_ bv37 32)) (_ bv0 8)))
(assert (= (select buf (_ bv38 32)) (_ bv0 8)))
(assert (= (select buf (_ bv39 32)) (_ bv0 8)))
(assert (= (select buf (_ bv40 32)) (_ bv0 8)))
(assert (= (select buf (_ bv41 32)) (_ bv0 8)))
(assert (= (select buf (_ bv42 32)) (_ bv0 8)))
(assert (= (select buf (_ bv43 32)) (_ bv0 8)))
(assert (= (select buf (_ bv44 32)) (_ bv0 8)))
(assert (= (select buf (_ bv45 32)) (_ bv0 8)))
(assert (= (select buf (_ bv46 32)) (_ bv0 8)))
(assert (= (select buf (_ bv47 32)) (_ bv0 8)))
(assert (= (select buf (_ bv48 32)) (_ bv0 8)))
(assert (= (select buf (_ bv49 32)) (_ bv0 8)))
(assert (= (select buf (_ bv50 32)) (_ bv0 8)))
(assert (= (select buf (_ bv51 32)) (_ bv0 8)))
(assert (= (select buf (_ bv52 32)) (_ bv0 8)))
(assert (= (select buf (_ bv53 32)) (_ bv0 8)))
(assert (= (select buf (_ bv54 32)) (_ bv0 8)))
(assert (= (select buf (_ bv55 32)) (_ bv0 8)))
(assert (= (select buf (_ bv56 32)) (_ bv0 8)))
(assert (= (select buf (_ bv57 32)) (_ bv0 8)))
(assert (= (select buf (_ bv58 32)) (_ bv0 8)))
(assert (= (select buf (_ bv59 32)) (_ bv0 8)))
(assert (= (select buf (_ bv60 32)) (_ bv0 8)))
(assert (= (select buf (_ bv61 32)) (_ bv0 8)))
(assert (= (select buf (_ bv62 32)) (_ bv0 8)))
(assert (= (select buf (_ bv63 32)) (_ bv0 8)))
(assert (= (select buf (_ bv64 32)) (_ bv0 8)))
(assert (= (select buf (_ bv65 32)) (_ bv0 8)))
(assert (= (select buf (_ bv66 32)) (_ bv0 8)))
(assert (= (select buf (_ bv67 32)) (_ bv0 8)))
(assert (= (select buf (_ bv68 32)) (_ bv0 8)))
(assert (= (select buf (_ bv69 32)) (_ bv0 8)))
(assert (= (select buf (_ bv70 32)) (_ bv0 8)))
(assert (= (select buf (_ bv71 32)) (_ bv0 8)))
(assert (= (select buf (_ bv72 32)) (_ bv0 8)))
(assert (= (select buf (_ bv73 32)) (_ bv0 8)))
(assert (= (select buf (_ bv74 32)) (_ bv0 8)))
(assert (= (select buf (_ bv75 32)) (_ bv0 8)))
(assert (= (select buf (_ bv76 32)) (_ bv0 8)))
(assert (= (select buf (_ bv77 32)) (_ bv0 8)))
(assert (= (select buf (_ bv78 32)) (_ bv0 8)))
(assert (= (select buf (_ bv79 32)) (_ bv0 8)))
(assert (= (select buf (_ bv80 32)) (_ bv0 8)))
(assert (= (select buf (_ bv81 32)) (_ bv0 8)))
(assert (= (select buf (_ bv82 32)) (_ bv0 8)))
(assert (= (select buf (_ bv83 32)) (_ bv0 8)))
(assert (= (select buf (_ bv84 32)) (_ bv0 8)))
(assert (= (select buf (_ bv85 32)) (_ bv0 8)))
(assert (= (select buf (_ bv86 32)) (_ bv0 8)))
(assert (= (select buf (_ bv87 32)) (_ bv0 8)))
(assert (= (select buf (_ bv88 32)) (_ bv0 8)))
(assert (= (select buf (_ bv89 32)) (_ bv0 8)))
(assert (= (select buf (_ bv90 32)) (_ bv0 8)))
(assert (= (select buf (_ bv91 32)) (_ bv0 8)))
(assert (= (select buf (_ bv92 32)) (_ bv0 8)))
(assert (= (select buf (_ bv93 32)) (_ bv0 8)))
(assert (= (select buf (_ bv94 32)) (_ bv0 8)))
(assert (= (select buf (_ bv95 32)) (_ bv0 8)))
(assert (= (select buf (_ bv96 32)) (_ bv0 8)))
(assert (= (select buf (_ bv97 32)) (_ bv0 8)))
(assert (= (select buf (_ bv98 32)) (_ bv0 8)))
(assert (= (select buf (_ bv99 32)) (_ bv0 8)))
(assert (= (select buf (_ bv100 32)) (_ bv0 8)))
(assert (= (select buf (_ bv101 32)) (_ bv0 8)))
(assert (= (select buf (_ bv102 32)) (_ bv0 8)))
(assert (= (select buf (_ bv103 32)) (_ bv0 8)))
(assert (= (select buf (_ bv104 32)) (_ bv0 8)))
(assert (= (select buf (_ bv105 32)) (_ bv0 8)))
(assert (= (select buf (_ bv106 32)) (_ bv0 8)))
(assert (= (select buf (_ bv107 32)) (_ bv0 8)))
(assert (= (select buf (_ bv108 32)) (_ bv0 8)))
(assert (= (select buf (_ bv109 32)) (_ bv0 8)))
(assert (= (select buf (_ bv110 32)) (_ bv0 8)))
(assert (= (select buf (_ bv111 32)) (_ bv0 8)))
(assert (= (select buf (_ bv112 32)) (_ bv0 8)))
(assert (= (select buf (_ bv113 32)) (_ bv0 8)))
(assert (= (select buf (_ bv114 32)) (_ bv0 8)))
(assert (= (select buf (_ bv115 32)) (_ bv0 8)))
(assert (= (select buf (_ bv116 32)) (_ bv0 8)))
(assert (= (select buf (_ bv117 32)) (_ bv0 8)))
(assert (= (select buf (_ bv118 32)) (_ bv0 8)))
(assert (= (select buf (_ bv119 32)) (_ bv0 8)))
(assert (= (select buf (_ bv120 32)) (_ bv0 8)))
(assert (= (select buf (_ bv121 32)) (_ bv0 8)))
(assert (= (select buf (_ bv122 32)) (_ bv0 8)))
(assert (= (select buf (_ bv123 32)) (_ bv0 8)))
(assert (= (select buf (_ bv124 32)) (_ bv0 8)))
(assert (= (select buf (_ bv125 32)) (_ bv0 8)))
(assert (= (select buf (_ bv126 32)) (_ bv0 8)))
(assert (= (select buf (_ bv127 32)) (_ bv0 8)))
(assert (= (select buf (_ bv128 32)) (_ bv0 8)))
(assert (= (select buf (_ bv129 32)) (_ bv0 8)))
(assert (= (select buf (_ bv130 32)) (_ bv0 8)))
(assert (= (select buf (_ bv131 32)) (_ bv0 8)))
(assert (= (select buf (_ bv132 32)) (_ bv0 8)))
(assert (= (select buf (_ bv133 32)) (_ bv0 8)))
(assert (= (select buf (_ bv134 32)) (_ bv0 8)))
(assert (= (select buf (_ bv135 32)) (_ bv0 8)))
(assert (= (select buf (_ bv136 32)) (_ bv0 8)))
(assert (= (select buf (_ bv137 32)) (_ bv0 8)))
(assert (= (select buf (_ bv138 32)) (_ bv0 8)))
(assert (= (select buf (_ bv139 32)) (_ bv0 8)))
(assert (= (select buf (_ bv140 32)) (_ bv0 8)))
(assert (= (select buf (_ bv141 32)) (_ bv0 8)))
(assert (= (select buf (_ bv142 32)) (_ bv0 8)))
(assert (= (select buf (_ bv143 32)) (_ bv0 8)))
(assert (= (select buf (_ bv144 32)) (_ bv0 8)))
(assert (= (select buf (_ bv145 32)) (_ bv0 8)))
(assert (= (select buf (_ bv146 32)) (_ bv0 8)))
(assert (= (select buf (_ bv147 32)) (_ bv0 8)))
(assert (= (select buf (_ bv148 32)) (_ bv0 8)))
(assert (= (select buf (_ bv149 32)) (_ bv0 8)))
(assert (= (select buf (_ bv150 32)) (_ bv0 8)))
(assert (= (select buf (_ bv151 32)) (_ bv0 8)))
(assert (= (select buf (_ bv152 32)) (_ bv0 8)))
(assert (= (select buf (_ bv153 32)) (_ bv0 8)))
(assert (= (select buf (_ bv154 32)) (_ bv0 8)))
(assert (= (select buf (_ bv155 32)) (_ bv0 8)))
(assert (= (select buf (_ bv156 32)) (_ bv0 8)))
(assert (= (select buf (_ bv157 32)) (_ bv0 8)))
(assert (= (select buf (_ bv158 32)) (_ bv0 8)))
(assert (= (select buf (_ bv159 32)) (_ bv0 8)))
(assert (= (select buf (_ bv160 32)) (_ bv0 8)))
(assert (= (select buf (_ bv161 32)) (_ bv0 8)))
(assert (= (select buf (_ bv162 32)) (_ bv0 8)))
(assert (= (select buf (_ bv163 32)) (_ bv0 8)))
(assert (= (select buf (_ bv164 32)) (_ bv0 8)))
(assert (= (select buf (_ bv165 32)) (_ bv0 8)))
(assert (= (select buf (_ bv166 32)) (_ bv0 8)))
(assert (= (select buf (_ bv167 32)) (_ bv0 8)))
(assert (= (select buf (_ bv168 32)) (_ bv0 8)))
(assert (= (select buf (_ bv169 32)) (_ bv0 8)))
(assert (= (select buf (_ bv170 32)) (_ bv0 8)))
(assert (= (select buf (_ bv171 32)) (_ bv0 8)))
(assert (= (select buf (_ bv172 32)) (_ bv0 8)))
(assert (= (select buf (_ bv173 32)) (_ bv0 8)))
(assert (= (select buf (_ bv174 32)) (_ bv0 8)))
(assert (= (select buf (_ bv175 32)) (_ bv0 8)))
(assert (= (select buf (_ bv176 32)) (_ bv0 8)))
(assert (= (select buf (_ bv177 32)) (_ bv0 8)))
(assert (= (select buf (_ bv178 32)) (_ bv0 8)))
(assert (= (select buf (_ bv179 32)) (_ bv0 8)))
(assert (= (select buf (_ bv180 32)) (_ bv0 8)))
(assert (= (select buf (_ bv181 32)) (_ bv0 8)))
(assert (= (select buf (_ bv182 32)) (_ bv0 8)))
(assert (= (select buf (_ bv183 32)) (_ bv0 8)))
(assert (= (select buf (_ bv184 32)) (_ bv0 8)))
(assert (= (select buf (_ bv185 32)) (_ bv0 8)))
(assert (= (select buf (_ bv186 32)) (_ bv0 8)))
(assert (= (select buf (_ bv187 32)) (_ bv0 8)))
(assert (= (select buf (_ bv188 32)) (_ bv0 8)))
(assert (= (select buf (_ bv189 32)) (_ bv0 8)))
(assert (= (select buf (_ bv190 32)) (_ bv0 8)))
(assert (= (select buf (_ bv191 32)) (_ bv0 8)))
(assert (= (select buf (_ bv192 32)) (_ bv0 8)))
(assert (= (select buf (_ bv193 32)) (_ bv0 8)))
(assert (= (select buf (_ bv194 32)) (_ bv0 8)))
(assert (= (select buf (_ bv195 32)) (_ bv0 8)))
(assert (= (select buf (_ bv196 32)) (_ bv0 8)))
(assert (= (select buf (_ bv197 32)) (_ bv0 8)))
(assert (= (select buf (_ bv198 32)) (_ bv0 8)))
(assert (= (select buf (_ bv199 32)) (_ bv0 8)))
(assert (= (select buf (_ bv200 32)) (_ bv0 8)))
(assert (= (select buf (_ bv201 32)) (_ bv0 8)))
(assert (= (select buf (_ bv202 32)) (_ bv0 8)))
(assert (= (select buf (_ bv203 32)) (_ bv0 8)))
(assert (= (select buf (_ bv204 32)) (_ bv0 8)))
(assert (= (select buf (_ bv205 32)) (_ bv0 8)))
(assert (= (select buf (_ bv206 32)) (_ bv0 8)))
(assert (= (select buf (_ bv207 32)) (_ bv0 8)))
(assert (= (select buf (_ bv208 32)) (_ bv0 8)))
(assert (= (select buf (_ bv209 32)) (_ bv0 8)))
(assert (= (select buf (_ bv210 32)) (_ bv0 8)))
(assert (= (select buf (_ bv211 32)) (_ bv0 8)))
(assert (= (select buf (_ bv212 32)) (_ bv0 8)))
(assert (= (select buf (_ bv213 32)) (_ bv0 8)))
(assert (= (select buf (_ bv214 32)) (_ bv0 8)))
(assert (= (select buf (_ bv215 32)) (_ bv0 8)))
(assert (= (select buf (_ bv216 32)) (_ bv0 8)))
(assert (= (select buf (_ bv217 32)) (_ bv0 8)))
(assert (= (select buf (_ bv218 32)) (_ bv0 8)))
(assert (= (select buf (_ bv219 32)) (_ bv0 8)))
(assert (= (select buf (_ bv220 32)) (_ bv0 8)))
(assert (= (select buf (_ bv221 32)) (_ bv0 8)))
(assert (= (select buf (_ bv222 32)) (_ bv0 8)))
(assert (= (select buf (_ bv223 32)) (_ bv0 8)))
(assert (= (select buf (_ bv224 32)) (_ bv0 8)))
(assert (= (select buf (_ bv225 32)) (_ bv0 8)))
(assert (= (select buf (_ bv226 32)) (_ bv0 8)))
(assert (= (select buf (_ bv227 32)) (_ bv0 8)))
(assert (= (select buf (_ bv228 32)) (_ bv0 8)))
(assert (= (select buf (_ bv229 32)) (_ bv0 8)))
(assert (= (select buf (_ bv230 32)) (_ bv0 8)))
(assert (= (select buf (_ bv231 32)) (_ bv0 8)))
(assert (= (select buf (_ bv232 32)) (_ bv0 8)))
(assert (= (select buf (_ bv233 32)) (_ bv0 8)))
(assert (= (select buf (_ bv234 32)) (_ bv0 8)))
(assert (= (select buf (_ bv235 32)) (_ bv0 8)))
(assert (= (select buf (_ bv236 32)) (_ bv0 8)))
(assert (= (select buf (_ bv237 32)) (_ bv0 8)))
(assert (= (select buf (_ bv238 32)) (_ bv0 8)))
(assert (= (select buf (_ bv239 32)) (_ bv0 8)))
(assert (= (select buf (_ bv240 32)) (_ bv0 8)))
(assert (= (select buf (_ bv241 32)) (_ bv0 8)))
(assert (= (select buf (_ bv242 32)) (_ bv0 8)))
(assert (= (select buf (_ bv243 32)) (_ bv0 8)))
(assert (= (select buf (_ bv244 32)) (_ bv0 8)))
(assert (= (select buf (_ bv245 32)) (_ bv0 8)))
(assert (= (select buf (_ bv246 32)) (_ bv0 8)))
(assert (= (select buf (_ bv247 32)) (_ bv0 8)))
(assert (= (select buf (_ bv248 32)) (_ bv0 8)))
(assert (= (select buf (_ bv249 32)) (_ bv0 8)))
(assert (= (select buf (_ bv250 32)) (_ bv0 8)))
(assert (= (select buf (_ bv251 32)) (_ bv0 8)))
(assert (= (select buf (_ bv252 32)) (_ bv0 8)))
(assert (= (select buf (_ bv253 32)) (_ bv0 8)))
(assert (= (select buf (_ bv254 32)) (_ bv0 8)))
(assert (= (select buf (_ bv255 32)) (_ bv0 8)))
(assert (not (not (= (select buf (concat (_ bv0 24) (select s (_ bv0 32)))) (_ bv0 8)))))
(assert (not (= (select (store buf (_ bv32 32) (_ bv1 8)) (concat (_ bv0 24) (select s (_ bv1 32)))) (_ bv0 8))))
(check-sat)
(exit)
