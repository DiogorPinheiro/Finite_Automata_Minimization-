open Printf 
open Scanf
open Array

(*--------------------------Leitura de dados---------------------------- *)
let n = scanf " %d" (fun n -> n)                    (* Número de estados *)

let card_so = scanf " %d" (fun card_so -> card_so)  (* Cardinalidade de estados iniciais *)  
let rec leitura_so so card_so =                     (* Leitura dos estados iniciais*)
   if card_so = 0 then
    so
  else
    let x = scanf " %d" (fun x -> x) in
    let so = so@[(x)] in
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
let transicoes = []

let rec armazenar_transicoes transicoes card_trans = (* Armazenar Transições *)
    if card_trans > 0 then
        let a1,a2,a3= scanf " %d %c %d " (fun a1 a2 a3 -> a1,a2,a3) in 
        let x = (a1,a2,a3) in 
        let transicoes = transicoes @ [x] in 
        armazenar_transicoes transicoes (card_trans-1) 
else transicoes
let transicoes = armazenar_transicoes transicoes card_trans

(* -------------------------- Valores iniciais nas tabelas ---------------------------*)

let tabela_transicoes = Array.make_matrix 2 n 0       (* Tabela de transições com 2 colunas (a,b) e n linhas *)
let tabela_particoes = Array.make_matrix 1 n 0        (* Tabela de particoes com 1 coluna e n linhas *)
let tabela_check = Array.make_matrix n n 0            (* Tabela onde se vai verificar pares de transições *)

let rec colocar_tab_trans tabela transicoes =         (* Colocar transicoes na tabela*)
    match transicoes with
    | [] -> tabela
    | (a1,a2,a3)::resto ->
        if a2='a' then
          let () = tabela.(0).(a1-1) <- a3 in colocar_tab_trans tabela resto     
        else
          let () = tabela.(1).(a1-1) <- a3 in colocar_tab_trans tabela resto      
let tabela_transicoes = colocar_tab_trans tabela_transicoes transicoes

let nenhumdestino tabela =
  for i=0 to 1 do
      for j=0 to (n-1) do
        if tabela.(i).(j)=0 then tabela.(i).(j)<-(-1)
      done
  done
let () = nenhumdestino tabela_transicoes

let () =                                              (* Colocar na tabela posições que não serão verificadas *)
    for x=0 to (n-1) do
      for y=0 to (n-1) do
        if x<=y then 
          let () = tabela_check.(x).(y) <- (-1) in ()
      done
    done

(*---------------------------------Funções de Verificação-------------------------------- *)
let rec final x f =                   (* Ver se é estado final *)
  match f with
  | []-> false
  | t::resto -> if x=(t-1) then true else final x resto 


let contar_estados tabela =         (* Contar ceĺulas verificadas na tabela das partições *)
  let cont = ref 0 in
  let () = 
    for x=0 to (n-1) do
      for y=0 to (n-1) do
        if tabela.(x).(y) = 1 then (cont:=(!cont+1)) else (cont := (!cont +0))
      done 
    done in
  !cont

let rec ver_transicao inicial letra transicao=    (* Descobrir qual será a transição, dando estado de partida e caracter *)
  match transicao with
  |[] -> (-1)
  |(a1,a2,a3)::resto-> if (((a1-1) = inicial) && (a2 =letra)) then a3 else ver_transicao inicial letra resto

(*let () = printf "%d\n" (ver_transicao 5 'a' transicoes)*)

let isVerificada tabela i j =                 (* Ver se corresponde a uma célula verificada *)
  if (tabela.(i-1).(j-1)=1) then true else false


let getposicaoprimeiro x tabela =     (* Obter posição do primeiro elemento da tabela que tem a partição igual ao valor x *)
    let pos = ref 0 in
    let () =
      for i=(n-1) downto 0 do
          if tabela.(0).(i)=x then pos := i
      done in
    !pos
  
let correspondencia x letra transicoes particoes =
  let valor = ref 0 in
  let pos= ref 0 in
  if letra = ('b') then pos:= 1 ;
    let () =
      for i=0 to (n-1) do
          if i=x then
            let holder = transicoes.(!pos).(i) in
            if holder<>(-1) then
              if (valor=valor) then valor := particoes.(0).(holder-1) else ()
            else
              valor:=(-1)
      done in          
  (!valor) 

(*------------------------------------Verificações------------------------------------------- *)
let verificar_finais tabela f =   (* Verificar pares em que um é estado final e o outro não *)
  for i = 0 to (n-1) do
    for j = 0 to (n-1) do
      if tabela.(i).(j)<>(-1) then
        if ( ((final i f) =true) && ( (final j f) =false)  || ((final i f) =false) && ( (final j f) =true) ) then
          tabela.(i).(j) <- 1 
    done
  done
let () = verificar_finais tabela_check f

let variacoes tabela transicao = (* Verificar resto dos pares *)
  let () =
    let mudancas = ref 0 in
    let mudancas_anteriores = ref 1 in 
    while (!mudancas<>(!mudancas_anteriores)) do
        if (mudancas<>mudancas_anteriores) then mudancas_anteriores:=(!mudancas) else ();
        if (mudancas<>mudancas_anteriores) then mudancas:=0 else ();
        for i=0 to (n-1) do
            for j=0 to (n-1) do
              if tabela.(i).(j)=0 then
                let first = (ver_transicao j 'a' transicao) in (* y *)
                let second = (ver_transicao i 'a' transicao) in (* x *)
                let firstb = (ver_transicao j 'b' transicao) in (* y *)
                let secondb = (ver_transicao i 'b' transicao) in (* x *)
                if ((isVerificada tabela second first) || (isVerificada tabela secondb firstb)) then
                  let () = tabela.(i).(j) <- 1 in
                  if (mudancas=mudancas) then mudancas := (!mudancas + 1) else ()                 
            done ;
        done 
      done in ()

let () = variacoes tabela_check transicoes
(*--------------------------------- Partições ------------------------------------------------ *)
let tabela_particoes_aux = Array.make_matrix 1 n 0  (* Tabela de partições auxiliares*)

let particoes_iniciais tabela particoes =     (* Obter conjuntos de partições*)
  let contador = ref 1 in
  let () = 
  for i=0 to (n-1) do
    for j=0 to (n-1) do
        if tabela.(i).(j) = 0 then 
          if ((particoes.(0).(i)=0) && (particoes.(0).(j)<>0)) then
            particoes.(0).(i)<-particoes.(0).(j)
          else if ((particoes.(0).(i)<>0) && (particoes.(0).(j)=0)) then
            particoes.(0).(j)<-particoes.(0).(i)
          else if ((particoes.(0).(i)<>0) && (particoes.(0).(j)<>0)) then
          particoes.(0).(j)<-particoes.(0).(i)
          else 
            let () = particoes.(0).(i)<-(!contador) in
            let () = particoes.(0).(j)<-(!contador) in
            if (contador=contador) then contador := (!contador + 1) else () 
    done
  done in
  (!contador)
let posicaomaxima = particoes_iniciais tabela_check tabela_particoes_aux


let particoes_restantes tabela particao auxiliar=        (* Obter partições que estão sozinhas*)
  let contador = ref 1 in
  let () = 
  for i=0 to (n-1) do
    for j=0 to (n-1) do
      if particao.(0).(i)=0 then
        if auxiliar.(0).(i)=0 then
          let () = particao.(0).(i) <- (!contador) in
          if (contador=contador) then contador := (!contador + 1) else () 
        else
          let pos = (getposicaoprimeiro (auxiliar.(0).(i)) auxiliar) in
          if pos=i then
            let () = particao.(0).(i) <- (!contador) in
            if (contador=contador) then contador := (!contador + 1) else ()
          else
            particao.(0).(i) <- particao.(0).(pos);
      if particao.(0).(j)=0 then
        if auxiliar.(0).(j)=0 then
          let () = particao.(0).(j) <- (!contador) in
          if (contador=contador) then contador := (!contador + 1) else () 
        else
          let pos = (getposicaoprimeiro (auxiliar.(0).(j)) auxiliar) in
          if pos=j then
            let () = particao.(0).(j) <- (!contador) in
            if (contador=contador) then contador := (!contador + 1) else ()
          else
            particao.(0).(j) <- particao.(0).(pos)
    done    
  done in
  (!contador-1)
let numeroparticoes = particoes_restantes tabela_check tabela_particoes tabela_particoes_aux

(*---------------------------------Novos Estados---------------------------------------------- *)
let novatabela_transicoes = Array.make_matrix 2 numeroparticoes 0
(*let () = printf "Particao = %d\n" tabela_particoes.(0).(2)
let () = printf "corresponde = %d\n" (correspondencia 2 'a' tabela_transicoes tabela_particoes)*)

let contrucao_tabela nova particoes transicoes =
  let pos = ref 0 in
  let cont = ref 1 in
  for i=0 to (n-1) do
    if particoes.(0).(i)=(!cont) then
      let () = nova.(0).(!pos) <- (correspondencia i 'a' transicoes particoes) in
      let () = nova.(1).(!pos) <- (correspondencia i 'b' transicoes particoes) in
      if (cont=cont) then cont := (!cont + 1) else ();
      if (pos=pos) then pos := (!pos + 1) else ()
  done
let () = contrucao_tabela novatabela_transicoes tabela_particoes tabela_transicoes

(*---------------------------------Output-----------------------------------------------------*)
let () = printf "%d\n" (numeroparticoes)

let () = printf "%d\n" (List.fold_left (fun acc _ -> acc + 1) 0 so)

let rec print_estados estado =
  match estado with
  | []->printf "\n"
  | v1::resto -> let () = printf "%d " v1 in print_estados resto 
let () = print_estados so 

(*Cardinalidade Estados finais*)
let card_novosestados tabela f numero =
  let cont = ref 1 in
  let num = ref 0 in
  let () = 
    while (!cont<>(numero+1)) do
      let cont_ant=(!cont) in
      for i=0 to (n-1) do
        if (tabela.(0).(i)=(!cont)) then
          if (final i f) then
          let () = printf "" in
            if (cont=cont) then cont := (!cont + 1) else () ;
            if (num=num) then num := (!num + 1) else ()
      done;
      if cont_ant=(!cont) then
        let () = if (cont=cont) then cont := (!cont + 1) in () 
    done in
  (!num)
let () = printf "%d\n" (card_novosestados tabela_particoes f numeroparticoes)
(*Estados finais*)
let printestadosfinais tabela f numero =
  let cont = ref 1 in
  while (!cont<>(numero+1)) do
      let cont_ant=(!cont) in
      for i=0 to (n-1) do
        if (tabela.(0).(i)=(!cont)) then
          if (final i f) then
          let () = printf "%d" (!cont) in
            if (cont=cont) then cont := (!cont + 1) else () ; 
      done;
      if cont_ant=(!cont) then
        let () = if (cont=cont) then cont := (!cont + 1) in () 
  done
let () = printestadosfinais tabela_particoes f numeroparticoes
let () = printf "\n" 
 
(*NºTransições*)
let numerotransicoes tabela =
  let num = ref 0 in
  let () =
    for i=0 to (numeroparticoes-1) do
      for j=0 to 1 do
          if tabela.(j).(i)<>(-1) then num:=(!num +1)
      done
    done in
  (!num)
let () = printf "%d\n" (numerotransicoes novatabela_transicoes)
(*Transições*)
let printtransicoes tabela =
  let letraa=('a') in
  let letrab=('b') in
  for i=0 to (numeroparticoes-1) do
      for j=0 to 1 do
          if tabela.(j).(i)<>(-1) then printf "%d %c %d\n" (i+1) (if j=0 then letraa else letrab) (tabela.(j).(i))
      done
    done 
let () = printtransicoes novatabela_transicoes

(*---------------------------------Auxiliares------------------------------------------------- *)
(*
let rec print_transicoes lista =
  match lista with
  | [] -> printf "\n"
  | (a1,a2,a3)::resto -> let () = printf "(%d, %c, %d)\n" a1 a2 a3 in print_transicoes resto
let () = print_transicoes transicoes 
*)
(*
let print_tabelacheck tabela =
  for i=0 to (n-1) do
    for j=0 to (n-1) do
      let () = printf "%d " tabela.(i).(j) in ()
    done;
    let () = printf "\n" in ()
  done;;
let () = print_tabelacheck tabela_check
*)
(* Funcões de leitura adicionais (para testes) *)
(*
let print_tabela tabela =
  for i = 0 to (numeroparticoes-1) do
    for j = 0 to 1 do
      let () = printf "%d " tabela.(j).(i) in ()
    done;
    let () = printf "\n" in ()
  done
let () = print_tabela novatabela_transicoes *)
(*
let print_particoes tabela =
  for i=0 to (n-1) do
    let () = printf "%d \n" tabela.(0).(i) in ()
  done
let () = print_particoes tabela_particoes *)
