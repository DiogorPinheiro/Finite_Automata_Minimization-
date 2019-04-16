open Printf 
open Scanf
open Array

(*--------------------------Leitura de dados---------------------------- *)
let n = scanf " %d" (fun n -> n)                    (* Número de estados *)

let so = scanf " %d" (fun card_so -> card_so)  (* Cardinalidade de estados iniciais *)  

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

let carac = []                                            (* Inicializar lista de caracteres *)

let rec isCarac carac c=                                  (* Ver se caracter já está na lista *)                    
  match carac with
  | []->false
  | v1::resto -> if v1=c then true else isCarac resto c

let rec caracteres transicoes carac =                     (* Obter caracteres através das transições *)
  match transicoes with
  |[]->carac
  |(a1,a2,a3)::resto-> if (isCarac carac a2 ) then caracteres resto carac else let carac = carac@[a2] in caracteres resto carac
  let carac = caracteres transicoes carac

let numcarac = (List.fold_left (fun acc _ -> acc + 1) 0 carac)  (* Nºcaracteres na lista *)
(*let () = printf "Caracter = %c\n" (List.nth carac 1)*)
let rec find x lst =                                    (* Descobrir posicao do caracter na lista*)
  match lst with
  | [] -> raise (Failure "Not Found")
  | h :: t -> if x = h then 0 else 1 + find x t

let tabela_transicoes = Array.make_matrix numcarac n 0       (* Tabela de transições com nºcolunas correspondentes ao nºcaracteres e n linhas *)
let tabela_particoes = Array.make_matrix 1 n 0        (* Tabela de particoes com 1 coluna e n linhas *)
let tabela_check = Array.make_matrix n n 0            (* Tabela onde se vai verificar pares de transições *)

let rec colocar_tab_trans tabela transicoes carac =         (* Colocar transicoes na tabela*)
    match transicoes with
    | [] -> tabela
    | (a1,a2,a3)::resto ->
          let () = tabela.((find a2 carac)).(a1-1) <- a3 in colocar_tab_trans tabela resto carac          
let tabela_transicoes = colocar_tab_trans tabela_transicoes transicoes carac

let nenhumdestino tabela numcarac =
  for i=0 to (numcarac-1) do
      for j=0 to (n-1) do
        if tabela.(i).(j)=0 then tabela.(i).(j)<-(-1)
      done
  done
let () = nenhumdestino tabela_transicoes numcarac

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
  
let correspondencia x letra transicoes particoes carac=
  let valor = ref 0 in
  let pos = (find letra carac) in
    let () =
      for i=0 to (n-1) do
          if i=x then
            let holder = transicoes.(pos).(i) in
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

let variacoes tabela transicao carac numcarac = (* Verificar resto dos pares *)
  let () =
    let mudancas = ref 0 in
    let mudancas_anteriores = ref 1 in 
    while (!mudancas<>(!mudancas_anteriores)) do
        if (mudancas<>mudancas_anteriores) then mudancas_anteriores:=(!mudancas) else ();
        if (mudancas<>mudancas_anteriores) then mudancas:=0 else ();
        for i=0 to (n-1) do
            for j=0 to (n-1) do
             
              if tabela.(i).(j)=0 then
              
                for k=0 to (numcarac-1) do
                  let first = (ver_transicao j (List.nth carac k) transicao) in (* y *)
                  let second = (ver_transicao i (List.nth carac k) transicao) in (* x *) 
                  if ((isVerificada tabela second first) || (isVerificada tabela first second)) then
                    let () = tabela.(i).(j) <- 1 in
                    if (mudancas=mudancas) then mudancas := (!mudancas + 1) else ()  
                done              
            done ;
        done 
      done in ()

let () = variacoes tabela_check transicoes carac numcarac
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
let novatabela_transicoes = Array.make_matrix numcarac numeroparticoes 0
(*let () = printf "Particao = %d\n" tabela_particoes.(0).(2)
let () = printf "corresponde = %d\n" (correspondencia 2 'a' tabela_transicoes tabela_particoes)*)

let contrucao_tabela nova particoes transicoes carac numcarac =
  let pos = ref 0 in
  let cont = ref 1 in
  for i=0 to (n-1) do
    if particoes.(0).(i)=(!cont) then begin
      for j=0 to (numcarac -1) do
        nova.(j).(!pos) <- (correspondencia i (List.nth carac j) transicoes particoes carac) 
      done;
      if (cont=cont) then cont := (!cont + 1) else ();
      if (pos=pos) then pos := (!pos + 1) else ()
    end
  done
let () = contrucao_tabela novatabela_transicoes tabela_particoes tabela_transicoes carac numcarac

(*---------------------------------Output-----------------------------------------------------*)
let () = printf "%d\n" (numeroparticoes)

let () = printf "%d\n" (tabela_particoes.(0).(so-1))

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
let card_novos = card_novosestados tabela_particoes f numeroparticoes
let () = printf "%d\n" card_novos
(*Estados finais*)
let printestadosfinais tabela f numero card_f=
  let cont = ref 1 in
  let total = ref 0 in
  while (!cont<>(numero+1)) do
      let cont_ant=(!cont) in
      for i=0 to (n-1) do
        if (tabela.(0).(i)=(!cont)) then
          if (final i f) then
            if (!total = (card_f-1)) then
              let () = printf "%d\n" (!cont) in
              if (cont=cont) then cont := (!cont + 1) else () ; 
            else
              let () = printf "%d " (!cont) in
              if (total=total) then total := (!total + 1) else () ; 
              if (cont=cont) then cont := (!cont + 1) else () ; 
      done;
      if cont_ant=(!cont) then
        let () = if (cont=cont) then cont := (!cont + 1) in () 
  done
let () = printestadosfinais tabela_particoes f numeroparticoes card_novos

 
(*NºTransições*)
let numerotransicoes tabela numcarac=
  let num = ref 0 in
  let () =
    for i=0 to (numeroparticoes-1) do
      for j=0 to (numcarac-1) do
          if tabela.(j).(i)<>(-1) then num:=(!num +1)
      done
    done in
  (!num)
let () = printf "%d\n" (numerotransicoes novatabela_transicoes numcarac)
(*Transições*)
let printtransicoes tabela num=
  for i=0 to (numeroparticoes-1) do
      for j=0 to (num-1) do
          if tabela.(j).(i)<>(-1) then printf "%d %c %d\n" (i+1) (List.nth carac j) (tabela.(j).(i))
      done
    done 
let () = printtransicoes novatabela_transicoes numcarac


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
let print_tabela tabela num=
  for i = 0 to (numeroparticoes-1) do
    for j = 0 to (num-1) do
      let () = printf "%d " tabela.(j).(i) in ()
    done;
    let () = printf "\n" in ()
  done
let () = print_tabela novatabela_transicoes numcarac*)
(*
let print_particoes tabela =
  for i=0 to (n-1) do
    let () = printf "%d \n" tabela.(0).(i) in ()
  done
let () = print_particoes tabela_particoes 
*)
(*let rec print carac =
    match carac with
    |[]->printf "\n"
    |a1::resto-> let () = printf "%c" a1 in print resto
let () = print carac *)