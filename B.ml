open Printf 
open Scanf

(*--------------------------Leitura de dados---------------------------- *)
let n = scanf " %d" (fun n -> n)                    (* Número de estados *)

let card_so = scanf " %d" (fun card_so -> card_so)  (* Cardinalidade de estados iniciais *)  
let rec leitura_so so card_so =                     (* Leitura dos estados iniciais*)
   if card_so = 0 then
    so
  else
    let x = scanf " %d" (fun x -> x) in
    let so = so@[(x,0)] in
   leitura_so so (card_so-1)
let so = leitura_so [] card_so 

let card_f = scanf " %d" (fun card_f -> card_f)     (* Cardinalidade de estados finais *)
let rec leitura_f f card_f =                        (* Leitura dos estados finais *)     
  if card_f = 0 then
   f
 else
   let x = scanf " %d" (fun x -> x) in
   let f = f@[x] in
  leitura_f f (card_f-1)
let f = leitura_f [] card_f 

let card_trans = scanf " %d" (fun card_trans -> card_trans) (* Número de transições *)

let rec armazenar_transicoes transicoes card_trans = (* Armazenar Transições *)
    if card_trans > 0 then
        let a1,a2,a3= scanf " %d %c %d " (fun a1 a2 a3 -> a1,a2,a3) in 
        let x = (a1,a2,a3) in 
        let transicoes = transicoes @ [x] in 
        armazenar_transicoes transicoes (card_trans-1) 
else transicoes
let transicoes = armazenar_transicoes transicoes card_trans