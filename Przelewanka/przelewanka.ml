(* PRZELEWANKA *)
(* Autor: Wojciech Przytuła  *)
(* Reviewer: Hubert Badocha *)


(** Wyjątek rzucany w przypadku znalezienia rozwiązania,
  * z liczbą kroków doń prowadzących *)
exception Znalezione of int


(* hashtablica do przechowywania sprawdzonych już stanów *)
let stany = Hashtbl.create 4048


(* kolejka na stany do BFSa *)
let queue = Queue.create()


(** czy_sprawdzany : int array -> bool 
  * zwraca true jesli [stan] byl juz sprawdzany i false wpp *)
let czy_sprawdzany stan =
  Hashtbl.mem stany stan
    
    
(** wrzuc : int -> int array -> unit 
  * wrzuca parę ([stan], [kroki]) (gdzie kroki to liczba kroków
  * konieczna do osiągnięcia stanu) na kolejkę oraz dodaje [stan] 
  * do hashtablicy *)
let wrzuc kroki stan =
  Hashtbl.add stany stan ();
  Queue.push (stan, kroki) queue
    

(** porownaj : int array -> int array -> bool
  * zwraca true jesli [stan] jest taki sam
  * jak pożądany - [cel] i false wpp *)
let porownaj cel stan = cel = stan


(** procesuj : int array -> int array -> int -> unit 
  * dla danego [stanu] sprawdza czy był już rozpatrywany;
  * jeśli nie, to sprawdza jego zgodnosc ze stanem pożądanym:
  * jeśli jest zgodny, to rzuca [Znalezione] wraz z liczbą
  * kroków koniecznych do jego osiągnięcia;
  * wpp wola [wrzuc] po [nowym_stanie] *)
let procesuj cel stan kroki =
    if not (czy_sprawdzany stan) then
      if porownaj cel stan then raise (Znalezione kroki)
      else wrzuc kroki stan


(** dolej : int array -> int array -> int -> int array 
  * przyjmuje [pojemnosci], [stan] oraz [nr] i zwraca
  * kopię [stanu] jako [nowy_stan] różną tak, że szklanka
  * o numerze [nr] jest pełna *)
let dolej pojemnosci stan nr =
  let nowy_stan = Array.copy stan in
  nowy_stan.(nr) <- pojemnosci.(nr);
  nowy_stan
  

(** dolewaj : int array -> int array -> int array -> int -> unit
  * wykonuje [dolej] dla każdej szklanki w [stan], a następnie
  * dla każdego otrzymanego [nowego_stanu] woła [procesuj] *)
let dolewaj cel pojemnosci stan kroki =
  for i = 0 to Array.length stan - 1 do
    if stan.(i) <> pojemnosci.(i) then
    let nowy_stan = dolej pojemnosci stan i in
    procesuj cel nowy_stan kroki
  done
  
  
(** wylej : int array -> int -> int array
  * przyjmuje [stan] oraz [nr] i zwraca
  * kopię [stanu] jako [nowy_stan] różną tak, że szklanka
  * o numerze [nr] jest pusta *)
let wylej stan nr =
  let nowy_stan = Array.copy stan in
  nowy_stan.(nr) <- 0;
  nowy_stan
  
  
(** wylewaj : int array -> int array -> int array -> int -> unit
  * wykonuje [wylej] dla każdej szklanki w [stan], a następnie
  * dla każdego otrzymanego [nowego_stanu] woła [procesuj] *) 
let wylewaj cel stan kroki =
  for i = 0 to Array.length stan - 1 do
    if stan.(i) <> 0 then
    let nowy_stan = wylej stan i in
    procesuj cel nowy_stan kroki
  done


(** przelej : int array -> int array -> int -> int -> unit
  * zwraca kopię [stanu] jako [nowy_stan] różną tak, że jesli
  * w szklance [nr_z] jest nie więcej wody niż pozostałego miejsca
  * w szklance [nr_do], to szklanka [nr_do] ma dolaną całą wodę ze
  * szklanki [nr_z] a szklanka [nr_z] jest pusta; wpp szklanka [nr_do]
  * jest pełna, a szklanka [nr_z] ma o tyle mniej wody, o ile przybyło
  * do szklanki [nr_do] *)
let przelej pojemnosci stan nr_z nr_do =
  assert (nr_z <> nr_do);
  let nowy_stan = Array.copy stan in
  let limit_do = pojemnosci.(nr_do) 
  and zawartosc_do = nowy_stan.(nr_do)
  and zawartosc_z = nowy_stan.(nr_z) in 
  let dostepne = limit_do - zawartosc_do in
  if dostepne >= zawartosc_z then
    begin
      nowy_stan.(nr_z) <- 0;
      nowy_stan.(nr_do) <- zawartosc_do + zawartosc_z
    end
  else
    begin
      nowy_stan.(nr_z) <- zawartosc_z - dostepne;
      nowy_stan.(nr_do) <- limit_do
    end;
  nowy_stan

  
(** przelewaj : int array -> int array -> int array -> int -> unit
  * wykonuje [przelej] dla każdej pary szklanek w [stan]
  * (z uwzględnieniem kolejności szklanek), a następnie
  * dla każdego otrzymanego [nowego_stanu] woła [procesuj] *) 
let przelewaj cel pojemnosci stan kroki =
  let n = Array.length stan in
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do 
      if i <> j && stan.(i) <> 0 && stan.(j) <> pojemnosci.(j) then
      begin
        let nowy_stan = przelej pojemnosci stan i j in
        procesuj cel nowy_stan kroki
      end
    done
  done  


(** bfs : int array -> int array -> unit
  * przechodzi BFSem po wszystkich możliwych stanach;
  * jeżeli jednak znalezione zostanie rozwiązanie, to przerywa się
  * i zwraca liczbę kroków potrzebnych do jego uzyskania *)
let bfs cel pojemnosci =
  try while not (Queue.is_empty queue) do
    let badany, kroki = Queue.pop queue in
    dolewaj cel pojemnosci badany (kroki + 1);
    wylewaj cel badany (kroki + 1);
    przelewaj cel pojemnosci badany (kroki + 1)
    done; -1
  with (Znalezione kroki) -> kroki
    
    
(** nwd : int -> int -> int
  * zwraca największy wspólny dzielnik dwóch liczb *)
let rec nwd a b =
  if b = 0 then a else
  let r = a mod b in 
  nwd b r
    
    
(** mozliwy : int array -> int array -> bool
  * zwraca false jeśli jest wykluczone osiągnięcie pożądanego stanu
  * przy zadanej konfiguracji lub true wpp *)
let mozliwy pojemnosci cel =
  let n = Array.length cel in
  let rec ma_ekstremalny i =
    if i = n then false
    else if cel.(i) = pojemnosci.(i) || cel.(i) = 0 then true
    else ma_ekstremalny (i + 1) in
  let nwd_pojem = Array.fold_left nwd 0 pojemnosci in
  if nwd_pojem = 0 then true else
  let dziela_sie () = Array.fold_left 
                      (fun czy_wszystkie ilosc ->
                            czy_wszystkie && ilosc mod nwd_pojem = 0)
                      true cel in
  ma_ekstremalny 0 && dziela_sie ()
  

(* przelewanka : (int * int) array -> int *)
let przelewanka szklanki =
  Hashtbl.clear stany;
  Queue.clear queue;
  let n = Array.length szklanki in
  if n = 0 then 0 else
  let pojemnosci = Array.init n (fun n -> fst szklanki.(n)) in
  let cel = Array.init n (fun n -> snd szklanki.(n)) in
  if not (mozliwy pojemnosci cel) then -1 else
  let wyjsciowy = Array.make n 0 in
  if porownaj cel wyjsciowy then 0 else
  begin
    Queue.push (wyjsciowy, 0) queue;
    bfs cel pojemnosci
  end



(** Testy: pochodzą ze wspólnej puli *

assert (przelewanka [| (10,2); (1,1) |] = 5);;
assert (przelewanka [| (0,0); (2,2); (2,2); (2,2); (0,0); (0,0); (1,0);
  (0,0); (1,0) |] = (3));;
assert (przelewanka [| (1,1); (2,1); (3,0); (4,2) |] = (3));;
assert (przelewanka [| (0,0); (2,2); (1,0); (1,1); (1,0); (2,2); (1,0);
  (0,0); (0,0) |] = (3));;
assert (przelewanka [| (11,11); (11,1) |] = (-1));;
assert (przelewanka [| (1,1); (0,0); (2,2); (0,0); (2,0); (0,0); (0,0);
  (1,0); (2,0); (1,0) |] = (2));;
assert (przelewanka [| (5,2); (0,0); (0,0); (2,0); (3,2) |] = (4));;
assert (przelewanka [| (1,1); (0,0); (4,4); (4,0); (4,4) |] = (3));;
assert (przelewanka [| (9,9); (13,12) |] = (10));;
assert (przelewanka [| (2,2); (1,0); (2,2); (0,0); (1,0); (0,0); (1,1);
  (1,0); (0,0) |] = (3));;
assert (przelewanka [| (5,2); (3,1); (0,0); (4,1); (0,0); (1,0) |] = (5));;
assert (przelewanka [| (310,76); (139,91) |] = (-1));;
assert (przelewanka [| (48,9); (12,0); (1,1); (65,64) |] = (10));;
assert (przelewanka [| (7,5); (3,3); (9,4); (10,4); (6,3); (5,3) |] =
  (8));;
assert (przelewanka [| (100000,50000); (1,1) |] = (100000));;
assert (przelewanka [| (0,0); (0,0); (0,0); (300000,151515);
  (1,0); (0,0) |] = (296971));;
assert (przelewanka [| (11,2); (11,10); (4,0); (10,8); (21,16) |] = (12));;
assert (przelewanka [| (50,1); (7,3); (78,64) |] = (-1));;
assert (przelewanka [| (85,23); (524,210) |] = (-1));;
assert (przelewanka [| (557,349); (73,49) |] = (-1));;
assert (przelewanka [| (62,3); (38,7) |] = (-1));;
assert (przelewanka [| (15,15); (6,3); (42,32); (33,20) |] = (-1));;
assert (przelewanka [| (39,12); (35,34); (21,7); (2,1) |] = (-1));;
assert (przelewanka [| (1,0); (2,1); (2,1); (0,0); (2,0); (0,0); (0,0);
  (0,0); (1,1); (0,0); (1,0) |] = (4));;
assert (przelewanka [| (2,0); (2,2); (2,1); (6,6); (0,0) |] = (-1));;
assert (przelewanka [| (2,0); (1,1); (1,1); (1,1); (0,0); (1,0); (3,2);
  (0,0) |] = (4));;
assert (przelewanka [| (1,1); (2,2); (4,1); (0,0); (1,0); (2,1) |] = (5));;
assert (przelewanka [| (1,0); (3,1); (2,2); (1,1); (1,0); (1,0) |] = (3));;
assert (przelewanka [| (20,7); (12,11) |] = (-1));;
assert (przelewanka [| (0,0); (21,21) |] = (1));;
assert (przelewanka [| (13,8); (11,11) |] = (14));;
assert (przelewanka [| (1,1); (3,2); (6,5) |] = (5));;
assert (przelewanka [| (4,4); (7,6); (2,2) |] = (6));;
assert (przelewanka [| (3,2); (3,3); (1,1); (2,0) |] = (3));;
assert (przelewanka [| (0,0); (2,0); (0,0); (2,0); (3,2); (2,1); (1,0) |] =
  (3));;
*)
