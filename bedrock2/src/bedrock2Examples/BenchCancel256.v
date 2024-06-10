Require Import coqutil.Map.Interface.
Require Import bedrock2.Map.SeparationLogic.
Local Open Scope list_scope. Local Open Scope sep_scope.

(* https://arxiv.org/pdf/1305.6543.pdf figure 4 *)
(* https://github.com/gmalecha/bedrock-mirror-shard/blob/ea7e5ad56a1d6392468b6823e0457dd44524bca7/benchmarks/MicroBenchCancel.v#L45-L65 *)

Parameters
  (mem : map.map nat nat) (mem_ok : map.ok mem)
  (ptsto : nat -> nat -> mem -> Prop).
Existing Instance mem_ok.

Fixpoint chain (ls : list nat) : list (mem -> Prop) :=
  match ls with
    | nil => nil
    | a :: b =>
      match b with
        | nil => nil
        | c :: d => ptsto a c :: chain b
      end
  end.

Definition chainr (ls : list nat) : mem -> Prop :=
  List.fold_right sep (emp True) (chain ls).

Definition chainl (ls : list nat) : mem -> Prop :=
  List.fold_left sep (chain ls) (emp True).

Fixpoint list_to (now : nat) (n : nat) : list nat :=
  match n with
    | 0 => nil
    | S n => (S n) :: list_to now n
  end.


Definition n1 := 1.
Definition n2 := 2.
Definition n3 := 3.
Definition n4 := 4.
Definition n5 := 5.
Definition n6 := 6.
Definition n7 := 7.
Definition n8 := 8.
Definition n9 := 9.
Definition n10 := 10.
Definition n11 := 11.
Definition n12 := 12.
Definition n13 := 13.
Definition n14 := 14.
Definition n15 := 15.
Definition n16 := 16.
Definition n17 := 17.
Definition n18 := 18.
Definition n19 := 19.
Definition n20 := 20.
Definition n21 := 21.
Definition n22 := 22.
Definition n23 := 23.
Definition n24 := 24.
Definition n25 := 25.
Definition n26 := 26.
Definition n27 := 27.
Definition n28 := 28.
Definition n29 := 29.
Definition n30 := 30.
Definition n31 := 31.
Definition n32 := 32.
Definition n33 := 33.
Definition n34 := 34.
Definition n35 := 35.
Definition n36 := 36.
Definition n37 := 37.
Definition n38 := 38.
Definition n39 := 39.
Definition n40 := 40.
Definition n41 := 41.
Definition n42 := 42.
Definition n43 := 43.
Definition n44 := 44.
Definition n45 := 45.
Definition n46 := 46.
Definition n47 := 47.
Definition n48 := 48.
Definition n49 := 49.
Definition n50 := 50.
Definition n51 := 51.
Definition n52 := 52.
Definition n53 := 53.
Definition n54 := 54.
Definition n55 := 55.
Definition n56 := 56.
Definition n57 := 57.
Definition n58 := 58.
Definition n59 := 59.
Definition n60 := 60.
Definition n61 := 61.
Definition n62 := 62.
Definition n63 := 63.
Definition n64 := 64.
Definition n65 := 65.
Definition n66 := 66.
Definition n67 := 67.
Definition n68 := 68.
Definition n69 := 69.
Definition n70 := 70.
Definition n71 := 71.
Definition n72 := 72.
Definition n73 := 73.
Definition n74 := 74.
Definition n75 := 75.
Definition n76 := 76.
Definition n77 := 77.
Definition n78 := 78.
Definition n79 := 79.
Definition n80 := 80.
Definition n81 := 81.
Definition n82 := 82.
Definition n83 := 83.
Definition n84 := 84.
Definition n85 := 85.
Definition n86 := 86.
Definition n87 := 87.
Definition n88 := 88.
Definition n89 := 89.
Definition n90 := 90.
Definition n91 := 91.
Definition n92 := 92.
Definition n93 := 93.
Definition n94 := 94.
Definition n95 := 95.
Definition n96 := 96.
Definition n97 := 97.
Definition n98 := 98.
Definition n99 := 99.
Definition n100 := 100.
Definition n101 := 101.
Definition n102 := 102.
Definition n103 := 103.
Definition n104 := 104.
Definition n105 := 105.
Definition n106 := 106.
Definition n107 := 107.
Definition n108 := 108.
Definition n109 := 109.
Definition n110 := 110.
Definition n111 := 111.
Definition n112 := 112.
Definition n113 := 113.
Definition n114 := 114.
Definition n115 := 115.
Definition n116 := 116.
Definition n117 := 117.
Definition n118 := 118.
Definition n119 := 119.
Definition n120 := 120.
Definition n121 := 121.
Definition n122 := 122.
Definition n123 := 123.
Definition n124 := 124.
Definition n125 := 125.
Definition n126 := 126.
Definition n127 := 127.
Definition n128 := 128.
Definition n129 := 129.
Definition n130 := 130.
Definition n131 := 131.
Definition n132 := 132.
Definition n133 := 133.
Definition n134 := 134.
Definition n135 := 135.
Definition n136 := 136.
Definition n137 := 137.
Definition n138 := 138.
Definition n139 := 139.
Definition n140 := 140.
Definition n141 := 141.
Definition n142 := 142.
Definition n143 := 143.
Definition n144 := 144.
Definition n145 := 145.
Definition n146 := 146.
Definition n147 := 147.
Definition n148 := 148.
Definition n149 := 149.
Definition n150 := 150.
Definition n151 := 151.
Definition n152 := 152.
Definition n153 := 153.
Definition n154 := 154.
Definition n155 := 155.
Definition n156 := 156.
Definition n157 := 157.
Definition n158 := 158.
Definition n159 := 159.
Definition n160 := 160.
Definition n161 := 161.
Definition n162 := 162.
Definition n163 := 163.
Definition n164 := 164.
Definition n165 := 165.
Definition n166 := 166.
Definition n167 := 167.
Definition n168 := 168.
Definition n169 := 169.
Definition n170 := 170.
Definition n171 := 171.
Definition n172 := 172.
Definition n173 := 173.
Definition n174 := 174.
Definition n175 := 175.
Definition n176 := 176.
Definition n177 := 177.
Definition n178 := 178.
Definition n179 := 179.
Definition n180 := 180.
Definition n181 := 181.
Definition n182 := 182.
Definition n183 := 183.
Definition n184 := 184.
Definition n185 := 185.
Definition n186 := 186.
Definition n187 := 187.
Definition n188 := 188.
Definition n189 := 189.
Definition n190 := 190.
Definition n191 := 191.
Definition n192 := 192.
Definition n193 := 193.
Definition n194 := 194.
Definition n195 := 195.
Definition n196 := 196.
Definition n197 := 197.
Definition n198 := 198.
Definition n199 := 199.
Definition n200 := 200.
Definition n201 := 201.
Definition n202 := 202.
Definition n203 := 203.
Definition n204 := 204.
Definition n205 := 205.
Definition n206 := 206.
Definition n207 := 207.
Definition n208 := 208.
Definition n209 := 209.
Definition n210 := 210.
Definition n211 := 211.
Definition n212 := 212.
Definition n213 := 213.
Definition n214 := 214.
Definition n215 := 215.
Definition n216 := 216.
Definition n217 := 217.
Definition n218 := 218.
Definition n219 := 219.
Definition n220 := 220.
Definition n221 := 221.
Definition n222 := 222.
Definition n223 := 223.
Definition n224 := 224.
Definition n225 := 225.
Definition n226 := 226.
Definition n227 := 227.
Definition n228 := 228.
Definition n229 := 229.
Definition n230 := 230.
Definition n231 := 231.
Definition n232 := 232.
Definition n233 := 233.
Definition n234 := 234.
Definition n235 := 235.
Definition n236 := 236.
Definition n237 := 237.
Definition n238 := 238.
Definition n239 := 239.
Definition n240 := 240.
Definition n241 := 241.
Definition n242 := 242.
Definition n243 := 243.
Definition n244 := 244.
Definition n245 := 245.
Definition n246 := 246.
Definition n247 := 247.
Definition n248 := 248.
Definition n249 := 249.
Definition n250 := 250.
Definition n251 := 251.
Definition n252 := 252.
Definition n253 := 253.
Definition n254 := 254.
Definition n255 := 255.
Definition n256 := 256.
Definition n257 := 257.

(* Goal Lift1Prop.iff1 (chainl (list_to 0 257)) (chainr (list_to 0 257)). cbv -[Lift1Prop.iff1 sep emp]. change x with nx... *)
Goal (Lift1Prop.iff1 (emp True ⋆ ptsto n257 n256 ⋆ ptsto n256 n255 ⋆ ptsto n255 n254 ⋆ ptsto n254 n253 ⋆ ptsto n253 n252 ⋆ ptsto n252 n251 ⋆ ptsto n251 n250 ⋆ ptsto n250 n249 ⋆ ptsto n249 n248 ⋆ ptsto n248 n247 ⋆ ptsto n247 n246 ⋆ ptsto n246 n245 ⋆ ptsto n245 n244 ⋆ ptsto n244 n243 ⋆ ptsto n243 n242 ⋆ ptsto n242 n241 ⋆ ptsto n241 n240 ⋆ ptsto n240 n239 ⋆ ptsto n239 n238 ⋆ ptsto n238 n237 ⋆ ptsto n237 n236 ⋆ ptsto n236 n235 ⋆ ptsto n235 n234 ⋆ ptsto n234 n233 ⋆ ptsto n233 n232 ⋆ ptsto n232 n231 ⋆ ptsto n231 n230 ⋆ ptsto n230 n229 ⋆ ptsto n229 n228 ⋆ ptsto n228 n227 ⋆ ptsto n227 n226 ⋆ ptsto n226 n225 ⋆ ptsto n225 n224 ⋆ ptsto n224 n223 ⋆ ptsto n223 n222 ⋆ ptsto n222 n221 ⋆ ptsto n221 n220 ⋆ ptsto n220 n219 ⋆ ptsto n219 n218 ⋆ ptsto n218 n217 ⋆ ptsto n217 n216 ⋆ ptsto n216 n215 ⋆ ptsto n215 n214 ⋆ ptsto n214 n213 ⋆ ptsto n213 n212 ⋆ ptsto n212 n211 ⋆ ptsto n211 n210 ⋆ ptsto n210 n209 ⋆ ptsto n209 n208 ⋆ ptsto n208 n207 ⋆ ptsto n207 n206 ⋆ ptsto n206 n205 ⋆ ptsto n205 n204 ⋆ ptsto n204 n203 ⋆ ptsto n203 n202 ⋆ ptsto n202 n201 ⋆ ptsto n201 n200 ⋆ ptsto n200 n199 ⋆ ptsto n199 n198 ⋆ ptsto n198 n197 ⋆ ptsto n197 n196 ⋆ ptsto n196 n195 ⋆ ptsto n195 n194 ⋆ ptsto n194 n193 ⋆ ptsto n193 n192 ⋆ ptsto n192 n191 ⋆ ptsto n191 n190 ⋆ ptsto n190 n189 ⋆ ptsto n189 n188 ⋆ ptsto n188 n187 ⋆ ptsto n187 n186 ⋆ ptsto n186 n185 ⋆ ptsto n185 n184 ⋆ ptsto n184 n183 ⋆ ptsto n183 n182 ⋆ ptsto n182 n181 ⋆ ptsto n181 n180 ⋆ ptsto n180 n179 ⋆ ptsto n179 n178 ⋆ ptsto n178 n177 ⋆ ptsto n177 n176 ⋆ ptsto n176 n175 ⋆ ptsto n175 n174 ⋆ ptsto n174 n173 ⋆ ptsto n173 n172 ⋆ ptsto n172 n171 ⋆ ptsto n171 n170 ⋆ ptsto n170 n169 ⋆ ptsto n169 n168 ⋆ ptsto n168 n167 ⋆ ptsto n167 n166 ⋆ ptsto n166 n165 ⋆ ptsto n165 n164 ⋆ ptsto n164 n163 ⋆ ptsto n163 n162 ⋆ ptsto n162 n161 ⋆ ptsto n161 n160 ⋆ ptsto n160 n159 ⋆ ptsto n159 n158 ⋆ ptsto n158 n157 ⋆ ptsto n157 n156 ⋆ ptsto n156 n155 ⋆ ptsto n155 n154 ⋆ ptsto n154 n153 ⋆ ptsto n153 n152 ⋆ ptsto n152 n151 ⋆ ptsto n151 n150 ⋆ ptsto n150 n149 ⋆ ptsto n149 n148 ⋆ ptsto n148 n147 ⋆ ptsto n147 n146 ⋆ ptsto n146 n145 ⋆ ptsto n145 n144 ⋆ ptsto n144 n143 ⋆ ptsto n143 n142 ⋆ ptsto n142 n141 ⋆ ptsto n141 n140 ⋆ ptsto n140 n139 ⋆ ptsto n139 n138 ⋆ ptsto n138 n137 ⋆ ptsto n137 n136 ⋆ ptsto n136 n135 ⋆ ptsto n135 n134 ⋆ ptsto n134 n133 ⋆ ptsto n133 n132 ⋆ ptsto n132 n131 ⋆ ptsto n131 n130 ⋆ ptsto n130 n129 ⋆ ptsto n129 n128 ⋆ ptsto n128 n127 ⋆ ptsto n127 n126 ⋆ ptsto n126 n125 ⋆ ptsto n125 n124 ⋆ ptsto n124 n123 ⋆ ptsto n123 n122 ⋆ ptsto n122 n121 ⋆ ptsto n121 n120 ⋆ ptsto n120 n119 ⋆ ptsto n119 n118 ⋆ ptsto n118 n117 ⋆ ptsto n117 n116 ⋆ ptsto n116 n115 ⋆ ptsto n115 n114 ⋆ ptsto n114 n113 ⋆ ptsto n113 n112 ⋆ ptsto n112 n111 ⋆ ptsto n111 n110 ⋆ ptsto n110 n109 ⋆ ptsto n109 n108 ⋆ ptsto n108 n107 ⋆ ptsto n107 n106 ⋆ ptsto n106 n105 ⋆ ptsto n105 n104 ⋆ ptsto n104 n103 ⋆ ptsto n103 n102 ⋆ ptsto n102 n101 ⋆ ptsto n101 n100 ⋆ ptsto n100 n99 ⋆ ptsto n99 n98 ⋆ ptsto n98 n97 ⋆ ptsto n97 n96 ⋆ ptsto n96 n95 ⋆ ptsto n95 n94 ⋆ ptsto n94 n93 ⋆ ptsto n93 n92 ⋆ ptsto n92 n91 ⋆ ptsto n91 n90 ⋆ ptsto n90 n89 ⋆ ptsto n89 n88 ⋆ ptsto n88 n87 ⋆ ptsto n87 n86 ⋆ ptsto n86 n85 ⋆ ptsto n85 n84 ⋆ ptsto n84 n83 ⋆ ptsto n83 n82 ⋆ ptsto n82 n81 ⋆ ptsto n81 n80 ⋆ ptsto n80 n79 ⋆ ptsto n79 n78 ⋆ ptsto n78 n77 ⋆ ptsto n77 n76 ⋆ ptsto n76 n75 ⋆ ptsto n75 n74 ⋆ ptsto n74 n73 ⋆ ptsto n73 n72 ⋆ ptsto n72 n71 ⋆ ptsto n71 n70 ⋆ ptsto n70 n69 ⋆ ptsto n69 n68 ⋆ ptsto n68 n67 ⋆ ptsto n67 n66 ⋆ ptsto n66 n65 ⋆ ptsto n65 n64 ⋆ ptsto n64 n63 ⋆ ptsto n63 n62 ⋆ ptsto n62 n61 ⋆ ptsto n61 n60 ⋆ ptsto n60 n59 ⋆ ptsto n59 n58 ⋆ ptsto n58 n57 ⋆ ptsto n57 n56 ⋆ ptsto n56 n55 ⋆ ptsto n55 n54 ⋆ ptsto n54 n53 ⋆ ptsto n53 n52 ⋆ ptsto n52 n51 ⋆ ptsto n51 n50 ⋆ ptsto n50 n49 ⋆ ptsto n49 n48 ⋆ ptsto n48 n47 ⋆ ptsto n47 n46 ⋆ ptsto n46 n45 ⋆ ptsto n45 n44 ⋆ ptsto n44 n43 ⋆ ptsto n43 n42 ⋆ ptsto n42 n41 ⋆ ptsto n41 n40 ⋆ ptsto n40 n39 ⋆ ptsto n39 n38 ⋆ ptsto n38 n37 ⋆ ptsto n37 n36 ⋆ ptsto n36 n35 ⋆ ptsto n35 n34 ⋆ ptsto n34 n33 ⋆ ptsto n33 n32 ⋆ ptsto n32 n31 ⋆ ptsto n31 n30 ⋆ ptsto n30 n29 ⋆ ptsto n29 n28 ⋆ ptsto n28 n27 ⋆ ptsto n27 n26 ⋆ ptsto n26 n25 ⋆ ptsto n25 n24 ⋆ ptsto n24 n23 ⋆ ptsto n23 n22 ⋆ ptsto n22 n21 ⋆ ptsto n21 n20 ⋆ ptsto n20 n19 ⋆ ptsto n19 n18 ⋆ ptsto n18 n17 ⋆ ptsto n17 n16 ⋆ ptsto n16 n15 ⋆ ptsto n15 n14 ⋆ ptsto n14 n13 ⋆ ptsto n13 n12 ⋆ ptsto n12 n11 ⋆ ptsto n11 n10 ⋆ ptsto n10 n9 ⋆ ptsto n9 n8 ⋆ ptsto n8 n7 ⋆ ptsto n7 n6 ⋆ ptsto n6 n5 ⋆ ptsto n5 n4 ⋆ ptsto n4 n3 ⋆ ptsto n3 n2 ⋆ ptsto n2 n1) (ptsto n257 n256 ⋆ (ptsto n256 n255 ⋆ (ptsto n255 n254 ⋆ (ptsto n254 n253 ⋆ (ptsto n253 n252 ⋆ (ptsto n252 n251 ⋆ (ptsto n251 n250 ⋆ (ptsto n250 n249 ⋆ (ptsto n249 n248 ⋆ (ptsto n248 n247 ⋆ (ptsto n247 n246 ⋆ (ptsto n246 n245 ⋆ (ptsto n245 n244 ⋆ (ptsto n244 n243 ⋆ (ptsto n243 n242 ⋆ (ptsto n242 n241 ⋆ (ptsto n241 n240 ⋆ (ptsto n240 n239 ⋆ (ptsto n239 n238 ⋆ (ptsto n238 n237 ⋆ (ptsto n237 n236 ⋆ (ptsto n236 n235 ⋆ (ptsto n235 n234 ⋆ (ptsto n234 n233 ⋆ (ptsto n233 n232 ⋆ (ptsto n232 n231 ⋆ (ptsto n231 n230 ⋆ (ptsto n230 n229 ⋆ (ptsto n229 n228 ⋆ (ptsto n228 n227 ⋆ (ptsto n227 n226 ⋆ (ptsto n226 n225 ⋆ (ptsto n225 n224 ⋆ (ptsto n224 n223 ⋆ (ptsto n223 n222 ⋆ (ptsto n222 n221 ⋆ (ptsto n221 n220 ⋆ (ptsto n220 n219 ⋆ (ptsto n219 n218 ⋆ (ptsto n218 n217 ⋆ (ptsto n217 n216 ⋆ (ptsto n216 n215 ⋆ (ptsto n215 n214 ⋆ (ptsto n214 n213 ⋆ (ptsto n213 n212 ⋆ (ptsto n212 n211 ⋆ (ptsto n211 n210 ⋆ (ptsto n210 n209 ⋆ (ptsto n209 n208 ⋆ (ptsto n208 n207 ⋆ (ptsto n207 n206 ⋆ (ptsto n206 n205 ⋆ (ptsto n205 n204 ⋆ (ptsto n204 n203 ⋆ (ptsto n203 n202 ⋆ (ptsto n202 n201 ⋆ (ptsto n201 n200 ⋆ (ptsto n200 n199 ⋆ (ptsto n199 n198 ⋆ (ptsto n198 n197 ⋆ (ptsto n197 n196 ⋆ (ptsto n196 n195 ⋆ (ptsto n195 n194 ⋆ (ptsto n194 n193 ⋆ (ptsto n193 n192 ⋆ (ptsto n192 n191 ⋆ (ptsto n191 n190 ⋆ (ptsto n190 n189 ⋆ (ptsto n189 n188 ⋆ (ptsto n188 n187 ⋆ (ptsto n187 n186 ⋆ (ptsto n186 n185 ⋆ (ptsto n185 n184 ⋆ (ptsto n184 n183 ⋆ (ptsto n183 n182 ⋆ (ptsto n182 n181 ⋆ (ptsto n181 n180 ⋆ (ptsto n180 n179 ⋆ (ptsto n179 n178 ⋆ (ptsto n178 n177 ⋆ (ptsto n177 n176 ⋆ (ptsto n176 n175 ⋆ (ptsto n175 n174 ⋆ (ptsto n174 n173 ⋆ (ptsto n173 n172 ⋆ (ptsto n172 n171 ⋆ (ptsto n171 n170 ⋆ (ptsto n170 n169 ⋆ (ptsto n169 n168 ⋆ (ptsto n168 n167 ⋆ (ptsto n167 n166 ⋆ (ptsto n166 n165 ⋆ (ptsto n165 n164 ⋆ (ptsto n164 n163 ⋆ (ptsto n163 n162 ⋆ (ptsto n162 n161 ⋆ (ptsto n161 n160 ⋆ (ptsto n160 n159 ⋆ (ptsto n159 n158 ⋆ (ptsto n158 n157 ⋆ (ptsto n157 n156 ⋆ (ptsto n156 n155 ⋆ (ptsto n155 n154 ⋆ (ptsto n154 n153 ⋆ (ptsto n153 n152 ⋆ (ptsto n152 n151 ⋆ (ptsto n151 n150 ⋆ (ptsto n150 n149 ⋆ (ptsto n149 n148 ⋆ (ptsto n148 n147 ⋆ (ptsto n147 n146 ⋆ (ptsto n146 n145 ⋆ (ptsto n145 n144 ⋆ (ptsto n144 n143 ⋆ (ptsto n143 n142 ⋆ (ptsto n142 n141 ⋆ (ptsto n141 n140 ⋆ (ptsto n140 n139 ⋆ (ptsto n139 n138 ⋆ (ptsto n138 n137 ⋆ (ptsto n137 n136 ⋆ (ptsto n136 n135 ⋆ (ptsto n135 n134 ⋆ (ptsto n134 n133 ⋆ (ptsto n133 n132 ⋆ (ptsto n132 n131 ⋆ (ptsto n131 n130 ⋆ (ptsto n130 n129 ⋆ (ptsto n129 n128 ⋆ (ptsto n128 n127 ⋆ (ptsto n127 n126 ⋆ (ptsto n126 n125 ⋆ (ptsto n125 n124 ⋆ (ptsto n124 n123 ⋆ (ptsto n123 n122 ⋆ (ptsto n122 n121 ⋆ (ptsto n121 n120 ⋆ (ptsto n120 n119 ⋆ (ptsto n119 n118 ⋆ (ptsto n118 n117 ⋆ (ptsto n117 n116 ⋆ (ptsto n116 n115 ⋆ (ptsto n115 n114 ⋆ (ptsto n114 n113 ⋆ (ptsto n113 n112 ⋆ (ptsto n112 n111 ⋆ (ptsto n111 n110 ⋆ (ptsto n110 n109 ⋆ (ptsto n109 n108 ⋆ (ptsto n108 n107 ⋆ (ptsto n107 n106 ⋆ (ptsto n106 n105 ⋆ (ptsto n105 n104 ⋆ (ptsto n104 n103 ⋆ (ptsto n103 n102 ⋆ (ptsto n102 n101 ⋆ (ptsto n101 n100 ⋆ (ptsto n100 n99 ⋆ (ptsto n99 n98 ⋆ (ptsto n98 n97 ⋆ (ptsto n97 n96 ⋆ (ptsto n96 n95 ⋆ (ptsto n95 n94 ⋆ (ptsto n94 n93 ⋆ (ptsto n93 n92 ⋆ (ptsto n92 n91 ⋆ (ptsto n91 n90 ⋆ (ptsto n90 n89 ⋆ (ptsto n89 n88 ⋆ (ptsto n88 n87 ⋆ (ptsto n87 n86 ⋆ (ptsto n86 n85 ⋆ (ptsto n85 n84 ⋆ (ptsto n84 n83 ⋆ (ptsto n83 n82 ⋆ (ptsto n82 n81 ⋆ (ptsto n81 n80 ⋆ (ptsto n80 n79 ⋆ (ptsto n79 n78 ⋆ (ptsto n78 n77 ⋆ (ptsto n77 n76 ⋆ (ptsto n76 n75 ⋆ (ptsto n75 n74 ⋆ (ptsto n74 n73 ⋆ (ptsto n73 n72 ⋆ (ptsto n72 n71 ⋆ (ptsto n71 n70 ⋆ (ptsto n70 n69 ⋆ (ptsto n69 n68 ⋆ (ptsto n68 n67 ⋆ (ptsto n67 n66 ⋆ (ptsto n66 n65 ⋆ (ptsto n65 n64 ⋆ (ptsto n64 n63 ⋆ (ptsto n63 n62 ⋆ (ptsto n62 n61 ⋆ (ptsto n61 n60 ⋆ (ptsto n60 n59 ⋆ (ptsto n59 n58 ⋆ (ptsto n58 n57 ⋆ (ptsto n57 n56 ⋆ (ptsto n56 n55 ⋆ (ptsto n55 n54 ⋆ (ptsto n54 n53 ⋆ (ptsto n53 n52 ⋆ (ptsto n52 n51 ⋆ (ptsto n51 n50 ⋆ (ptsto n50 n49 ⋆ (ptsto n49 n48 ⋆ (ptsto n48 n47 ⋆ (ptsto n47 n46 ⋆ (ptsto n46 n45 ⋆ (ptsto n45 n44 ⋆ (ptsto n44 n43 ⋆ (ptsto n43 n42 ⋆ (ptsto n42 n41 ⋆ (ptsto n41 n40 ⋆ (ptsto n40 n39 ⋆ (ptsto n39 n38 ⋆ (ptsto n38 n37 ⋆ (ptsto n37 n36 ⋆ (ptsto n36 n35 ⋆ (ptsto n35 n34 ⋆ (ptsto n34 n33 ⋆ (ptsto n33 n32 ⋆ (ptsto n32 n31 ⋆ (ptsto n31 n30 ⋆ (ptsto n30 n29 ⋆ (ptsto n29 n28 ⋆ (ptsto n28 n27 ⋆ (ptsto n27 n26 ⋆ (ptsto n26 n25 ⋆ (ptsto n25 n24 ⋆ (ptsto n24 n23 ⋆ (ptsto n23 n22 ⋆ (ptsto n22 n21 ⋆ (ptsto n21 n20 ⋆ (ptsto n20 n19 ⋆ (ptsto n19 n18 ⋆ (ptsto n18 n17 ⋆ (ptsto n17 n16 ⋆ (ptsto n16 n15 ⋆ (ptsto n15 n14 ⋆ (ptsto n14 n13 ⋆ (ptsto n13 n12 ⋆ (ptsto n12 n11 ⋆ (ptsto n11 n10 ⋆ (ptsto n10 n9 ⋆ (ptsto n9 n8 ⋆ (ptsto n8 n7 ⋆ (ptsto n7 n6 ⋆ (ptsto n6 n5 ⋆ (ptsto n5 n4 ⋆ (ptsto n4 n3 ⋆ (ptsto n3 n2 ⋆ (ptsto n2 n1 ⋆ emp True))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Proof.
  Time reify_goal. (* 0.1s *)
  (* Time abstract cancel_seps. (* 1.838 *) *)
  (* Set Ltac Profiling. *)
  Time cancel_seps. (* 0.42s *)
  (* Show Ltac Profile CutOff 0. *)
  (*
total time:      0.584s
 tactic                                   local  total   calls       max 
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─cancel_seps ---------------------------   1.9% 100.0%       1    0.584s
 ├─cancel_step -------------------------  10.9%  97.5%     258    0.023s
 │ ├─cancel_seps_at_indices ------------  70.1%  70.1%    1028    0.022s
 │ │ ├─cbv[firstn skipn app hd tl] -----  34.9%  34.9%     257    0.022s
 │ │ └─simple refine (uconstr) ---------  28.5%  28.5%     257    0.019s
 │ ├─ltac_list_ops.find_constr_eq ------  10.5%  11.0%       0    0.001s
 │ │ ├─exact (uconstr) -----------------   1.0%   1.0%     257    0.000s
 │ │ └─constr_eq -----------------------   0.9%   0.9%     513    0.000s
 │ ├─ltac_list_ops.index_and_element_of    2.4%   2.4%       0    0.000s
 │ ├─exact (uconstr) -------------------   2.0%   2.0%     257    0.000s
 │ ├─assert_fails ----------------------   0.6%   0.9%     257    0.000s
 │ │└tac -------------------------------   0.2%   0.2%     257    0.000s
 │ └─has_evar --------------------------   0.1%   0.1%       0    0.000s
 ├─cancel_done -------------------------   0.0%   0.6%       1    0.004s
 │ ├─ecancel_done ----------------------   0.1%   0.6%       1    0.004s
 │ │ ├─syntactic_unify._syntactic_exact_   0.0%   0.5%       1    0.003s
 │ │ │ ├─syntactic_unify._syntactic_unif   0.5%   0.5%      17    0.003s
   *)
Time Qed. (* 3.25s *)
